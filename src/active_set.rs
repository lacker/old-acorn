use std::cmp::Ordering;
use std::collections::HashSet;

use crate::fingerprint::FingerprintTree;
use crate::literal_set::LiteralSet;
use crate::term::{Clause, Literal, Term};
use crate::unifier::{Scope, Unifier};

// The ActiveSet stores a bunch of clauses that are indexed for various efficient lookups.
// The goal is that, given a new clause, it is efficient to determine what can be concluded
// given that clause and one clause from the active set.
// "Efficient" is relative - this still may take time roughly linear to the size of the active set.
pub struct ActiveSet {
    // A vector for indexed reference
    clauses: Vec<Clause>,

    // A HashSet for checking what complete clauses we already know
    clause_set: HashSet<Clause>,

    // A LiteralSet for checking specific literals we already know, including generalization
    literal_set: LiteralSet,

    resolution_targets: FingerprintTree<ResolutionTarget>,

    // The only information we need on a paramodulation target is the clause index, because
    // we use the entire paramodulator, not a subterm.
    paramodulation_targets: FingerprintTree<ParamodulationTarget>,
}

// A ResolutionTarget is a way of specifying one particular term that is "eligible for resolution".
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ResolutionTarget {
    // Which clause the resolution target is in.
    // For now, we assume the resolution target is the first term in the first literal of the clause.
    // For resolution, the literal can be either positive or negative.
    clause_index: usize,

    // We resolve against subterms. This is the path from the root term to the subterm to resolve against.
    // An empty path means resolve against the root.
    path: Vec<usize>,
}

// A ParamodulationTarget is a way of specifying one particular term that is
// "eligible for paramodulation".
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ParamodulationTarget {
    // Which clause the paramodulation target is in.
    // We assume it must be the first literal.
    clause_index: usize,

    // "forwards" paramodulation is when we use s = t to rewrite s to t.
    // "backwards" paramodulation is when we use s = t to rewrite t to s.
    forwards: bool,
}

// The ways a new clause can be generated.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ProofStep {
    ActivateParamodulator(usize),
    ActivateResolver(usize),
    EqualityFactoring,
    EqualityResolution,
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet {
            clauses: vec![],
            clause_set: HashSet::new(),
            literal_set: LiteralSet::new(),
            resolution_targets: FingerprintTree::new(),
            paramodulation_targets: FingerprintTree::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    // Get an iterator of (path, subterm) for all allowable resolution targets of a term.
    fn resolution_subterms(term: &Term) -> impl Iterator<Item = (Vec<usize>, &Term)> {
        term.subterms()
            .into_iter()
            .filter(|(_, t)| !t.atomic_variable().is_some())
    }

    fn get_resolution_term(&self, target: &ResolutionTarget) -> &Term {
        let clause = &self.clauses[target.clause_index];
        let mut term = &clause.literals[0].left;
        for i in &target.path {
            term = &term.args[*i];
        }
        term
    }

    // Get an iterator of (forward?, s, t) for all s -> t paramodulations allowed for this literal.
    fn paramodulation_terms(literal: &Literal) -> impl Iterator<Item = (bool, &Term, &Term)> {
        if !literal.positive {
            return vec![].into_iter();
        }
        let order = literal.left.kbo(&literal.right);
        match order {
            Ordering::Greater => {
                // s > t, so we only do forwards
                vec![(true, &literal.left, &literal.right)].into_iter()
            }
            Ordering::Equal => {
                // s = t, so we do both directions
                vec![
                    (true, &literal.left, &literal.right),
                    (false, &literal.right, &literal.left),
                ]
                .into_iter()
            }
            Ordering::Less => {
                panic!("Backwards literal: {:?}", literal);
            }
        }
    }

    // Look for superposition inferences using a paramodulator which is not yet in the
    // active set.
    // At a high level, this is when we have just learned that s = t in some circumstances,
    // and we are looking for all the conclusions we can infer by rewriting s -> t
    // in existing formulas.
    //
    // Specifically, this function handles the case when
    //
    //   s = t | S  (pm_clause)
    //
    // is the clause that is being activated, and we are searching for any clauses that can fit the
    //
    //   u ?= v | R
    //
    // in the superposition formula.
    pub fn activate_paramodulator(&self, pm_clause: &Clause) -> Vec<(Clause, ProofStep)> {
        let mut result = vec![];

        let pm_literal = &pm_clause.literals[0];
        for (_, s, t) in Self::paramodulation_terms(pm_literal) {
            // Look for resolution targets that match pm_left
            let targets = self.resolution_targets.get(s);
            for target in targets {
                let u_subterm = self.get_resolution_term(target);
                let mut unifier = Unifier::new();
                // s/t must be in "left" scope and u/v must be in "right" scope
                if !unifier.unify(Scope::Left, s, Scope::Right, u_subterm) {
                    continue;
                }

                // The clauses do actually unify. Combine them according to the superposition rule.
                let resolution_clause = &self.clauses[target.clause_index];
                let new_clause = unifier.superpose(t, pm_clause, &target.path, resolution_clause);

                result.push((
                    new_clause,
                    ProofStep::ActivateParamodulator(target.clause_index),
                ));
            }
        }

        result
    }

    // Look for superposition inferences using a resolver which is not yet in the active set.
    // At a high level, this is when we have just learned the relation u ?= v, and we are
    // looking for all the ways we can alter it in a no-less-simple way
    // (while possibly adding conditions).
    //
    // Specifically, this function handles the case when
    //
    //   u ?= v | R   (res_clause)
    //
    // is the clause that is being activated, and we are searching for any clauses that can fit the
    //
    //   s = t | S
    //
    // in the superposition formula.
    pub fn activate_resolver(&self, res_clause: &Clause) -> Vec<(Clause, ProofStep)> {
        let mut result = vec![];
        let res_literal = &res_clause.literals[0];
        let u = &res_literal.left;
        let u_subterms = u.subterms();

        for (path, u_subterm) in u_subterms {
            if res_literal.positive && path.is_empty() {
                // We already handle the u = s case in activate_paramodulator.
                continue;
            }

            // Look for paramodulation targets that match u_subterm
            let targets = self.paramodulation_targets.get(u_subterm);
            for target in targets {
                let pm_clause = &self.clauses[target.clause_index];
                let pm_literal = &pm_clause.literals[0];
                let (s, t) = if target.forwards {
                    (&pm_literal.left, &pm_literal.right)
                } else {
                    (&pm_literal.right, &pm_literal.left)
                };

                // s/t must be in "left" scope and u/v must be in "right" scope
                let mut unifier = Unifier::new();
                if !unifier.unify(Scope::Left, s, Scope::Right, u_subterm) {
                    continue;
                }

                // The clauses do actually unify. Combine them according to the superposition rule.
                let new_clause = unifier.superpose(t, pm_clause, &path, res_clause);

                result.push((new_clause, ProofStep::ActivateResolver(target.clause_index)));
            }
        }

        result
    }

    // Tries to do inference using the equality resolution (ER) rule.
    // This assumes the first literal in the clause is the one being resolved.
    // Specifically, when the first literal is of the form
    //   u != v
    // then if we can unify u and v, we can eliminate this literal from the clause.
    pub fn equality_resolution(clause: &Clause) -> Option<Clause> {
        if clause.literals.is_empty() {
            return None;
        }
        let first = &clause.literals[0];
        if first.positive {
            return None;
        }

        // The variables are in the same scope, which we will call "left".
        let mut unifier = Unifier::new();
        if !unifier.unify(Scope::Left, &first.left, Scope::Left, &first.right) {
            return None;
        }

        // We can do equality resolution
        let literals = clause
            .literals
            .iter()
            .skip(1)
            .map(|literal| unifier.apply_to_literal(Scope::Left, literal))
            .collect();
        let answer = Clause::new(literals);
        if answer.is_tautology() {
            None
        } else {
            Some(answer)
        }
    }

    // Tries to do inference using the equality factoring (EF) rule.
    //
    // Given:
    //   s = t | u = v | R
    // if we can unify s and u, we can rewrite it to:
    //   t != v | u = v | R
    //
    // "s = t" must be the first clause, but "u = v" can be any of them.
    pub fn equality_factoring(clause: &Clause) -> Vec<Clause> {
        let mut answer = vec![];
        let pm_literal = &clause.literals[0];
        for (_, s, t) in ActiveSet::paramodulation_terms(pm_literal) {
            for i in 1..clause.literals.len() {
                // Try paramodulating into the literal at index i
                let literal = &clause.literals[i];
                if !literal.positive {
                    continue;
                }
                // This literal can go in either direction.
                for (u, v) in [
                    (&literal.left, &literal.right),
                    (&literal.right, &literal.left),
                ] {
                    // The variables are in the same scope, which we will call "left".
                    let mut unifier = Unifier::new();
                    if !unifier.unify(Scope::Left, s, Scope::Left, u) {
                        continue;
                    }
                    let mut literals = vec![];
                    literals.push(Literal::not_equals(
                        unifier.apply(Scope::Left, t),
                        unifier.apply(Scope::Left, v),
                    ));
                    literals.push(unifier.apply_to_literal(Scope::Left, literal));
                    for j in 1..clause.literals.len() {
                        if j != i {
                            literals.push(clause.literals[j].clone());
                        }
                    }
                    let new_clause = Clause::new(literals);
                    answer.push(new_clause);
                }
            }
        }
        answer
    }

    pub fn get_clause(&self, index: usize) -> &Clause {
        &self.clauses[index]
    }

    pub fn contains(&self, clause: &Clause) -> bool {
        self.clause_set.contains(clause)
    }

    // Simplifies the clause based on both structural rules and the active set.
    // If the result is redundant given what's already known, return None.
    // If the result is an impossibility, return an empty clause.
    pub fn simplify(&self, clause: Clause) -> Option<Clause> {
        if clause.is_tautology() {
            return None;
        }
        if self.contains(&clause) {
            return None;
        }
        let mut literals = vec![];
        for literal in clause.literals {
            match self.literal_set.lookup(&literal) {
                Some((true, _)) => {
                    // This literal is already known to be true.
                    // Thus, the whole clause is a tautology.
                    return None;
                }
                Some((false, _)) => {
                    // This literal is already known to be false.
                    // Thus, we can just omit it from the disjunction.
                    continue;
                }
                None => {
                    literals.push(literal);
                }
            }
        }
        let clause = Clause::new(literals);
        if self.contains(&clause) {
            return None;
        }
        Some(clause)
    }

    pub fn insert(&mut self, clause: Clause) {
        // Add resolution targets for the new clause.
        let clause_index = self.clauses.len();
        let leftmost_literal = &clause.literals[0];
        let leftmost_term = &leftmost_literal.left;
        for (path, subterm) in ActiveSet::resolution_subterms(leftmost_term) {
            self.resolution_targets.insert(
                subterm,
                ResolutionTarget {
                    clause_index,
                    path: path.clone(),
                },
            );
        }

        // Add paramodulation targets for the new clause.
        for (forwards, from, _) in ActiveSet::paramodulation_terms(leftmost_literal) {
            self.paramodulation_targets.insert(
                from,
                ParamodulationTarget {
                    clause_index,
                    forwards,
                },
            );
        }

        self.clause_set.insert(clause.clone());

        if clause.literals.len() == 1 {
            self.literal_set.insert(clause.literals[0].clone());
        }

        self.clauses.push(clause);
    }

    // Generate all the inferences that can be made from a given clause, plus some existing clause.
    // This does not simplify.
    // Returns pairs describing how this clause was proved.
    pub fn generate(&mut self, clause: &Clause) -> Vec<(Clause, ProofStep)> {
        let mut generated_clauses = vec![];
        generated_clauses.extend(self.activate_paramodulator(&clause));
        generated_clauses.extend(self.activate_resolver(&clause));
        if let Some(new_clause) = ActiveSet::equality_resolution(&clause) {
            generated_clauses.push((new_clause, ProofStep::EqualityResolution));
        }
        for clause in ActiveSet::equality_factoring(&clause) {
            generated_clauses.push((clause, ProofStep::EqualityFactoring));
        }
        generated_clauses
    }
}

#[cfg(test)]
mod tests {
    use crate::term::Literal;

    use super::*;

    #[test]
    fn test_activate_paramodulator() {
        // Create an active set that knows a0(a3) = a2
        let res_left = Term::parse("a0(a3)");
        let res_right = Term::parse("a2");
        let mut set = ActiveSet::new();
        set.insert(Clause::new(vec![Literal::equals(res_left, res_right)]));

        // We should be able to use a1 = a3 to paramodulate into a0(a3) = a2
        let pm_left = Term::parse("a1");
        let pm_right = Term::parse("a3");
        let pm_clause = Clause::new(vec![Literal::equals(pm_left.clone(), pm_right.clone())]);
        let result = set.activate_paramodulator(&pm_clause);

        assert_eq!(result.len(), 1);
        let expected = Clause::new(vec![Literal::equals(
            Term::parse("a0(a1)"),
            Term::parse("a2"),
        )]);
        assert_eq!(result[0].0, expected);
    }

    #[test]
    fn test_activate_resolver() {
        // Create an active set that knows a1 = a3
        let pm_left = Term::parse("a1");
        let pm_right = Term::parse("a3");
        let mut set = ActiveSet::new();
        set.insert(Clause::new(vec![Literal::equals(pm_left, pm_right)]));

        // We should be able to use a0(a3) = a2 as a resolver to get a0(a1) = a2
        let res_left = Term::parse("a0(a3)");
        let res_right = Term::parse("a2");
        let res_clause = Clause::new(vec![Literal::equals(res_left, res_right)]);
        let result = set.activate_resolver(&res_clause);

        assert_eq!(result.len(), 1);
        let expected = Clause::new(vec![Literal::equals(
            Term::parse("a0(a1)"),
            Term::parse("a2"),
        )]);
        assert_eq!(result[0].0, expected);
    }

    #[test]
    fn test_equality_resolution() {
        let old_clause = Clause::new(vec![
            Literal::not_equals(Term::parse("x0"), Term::parse("a0")),
            Literal::equals(Term::parse("x0"), Term::parse("a1")),
        ]);
        let new_clause = ActiveSet::equality_resolution(&old_clause).unwrap();
        assert!(new_clause.literals.len() == 1);
        assert_eq!(format!("{}", new_clause), "a1 = a0".to_string())
    }

    #[test]
    fn test_equality_factoring() {
        let old_clause = Clause::new(vec![
            Literal::equals(Term::parse("x0"), Term::parse("a0")),
            Literal::equals(Term::parse("x1"), Term::parse("a0")),
        ]);
        let new_clauses = ActiveSet::equality_factoring(&old_clause);
        for c in &new_clauses {
            if format!("{}", c) == "a0 = x0".to_string() {
                return;
            }
        }
        panic!("Did not find expected clause");
    }
}
