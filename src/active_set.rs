use std::cmp::Ordering;
use std::collections::HashSet;

use crate::clause::Clause;
use crate::clause_info::{ClauseInfo, ClauseType, ProofRule, ProofStep};
use crate::fingerprint::FingerprintTree;
use crate::literal::Literal;
use crate::literal_set::LiteralSet;
use crate::specializer::Specializer;
use crate::term::Term;
use crate::unifier::{Scope, Unifier};

// The ActiveSet stores a bunch of clauses that are indexed for various efficient lookups.
// The goal is that, given a new clause, it is efficient to determine what can be concluded
// given that clause and one clause from the active set.
// "Efficient" is relative - this still may take time roughly linear to the size of the active set.
pub struct ActiveSet {
    // A vector for indexed reference
    clause_info: Vec<ClauseInfo>,

    // A HashSet for checking what complete clauses we already know
    clause_set: HashSet<Clause>,

    // A LiteralSet for checking specific literals we already know, including generalization
    literal_set: LiteralSet,

    resolution_targets: FingerprintTree<ResolutionTarget>,

    // The only information we need on a paramodulation target is the clause index, because
    // we use the entire paramodulator, not a subterm.
    paramodulation_targets: FingerprintTree<ParamodulationTarget>,

    // The rewrite rules we use.
    // A clause can only be a rewrite if it's a single foo = bar literal, and foo > bar by the KBO.
    // So we only need to store the clause index of the rewrite rule.
    rewrite_rules: FingerprintTree<usize>,
}

// A ResolutionTarget is a way of specifying one particular term that is "eligible for resolution".
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ResolutionTarget {
    // Which clause the resolution target is in.
    // For resolution, the literal can be either positive or negative.
    clause_index: usize,

    // Which literal within the clause the resolution target is in.
    // We assume the resolution target is the first term in the literal. (Is that okay?)
    literal_index: usize,

    // "forwards" resolution is when we rewrite u in a literal u ?= v.
    // "backwards" resolution is when we rewrite u in a literal v ?= u.
    // You could call this "left" but it's nice to be parallel to the paramodulation target.
    forwards: bool,

    // We resolve against subterms. This is the path from the root term to the subterm to
    // resolve against.
    // An empty path means resolve against the root.
    path: Vec<usize>,
}

// A ParamodulationTarget is a way of specifying one particular term that is
// "eligible for paramodulation".
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ParamodulationTarget {
    // Which clause the paramodulation target is in.
    clause_index: usize,

    // Which literal within the clause the paramodulation target is in.
    literal_index: usize,

    // "forwards" paramodulation is when we use s = t to rewrite s to t.
    // "backwards" paramodulation is when we use s = t to rewrite t to s.
    forwards: bool,
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet {
            clause_info: vec![],
            clause_set: HashSet::new(),
            literal_set: LiteralSet::new(),
            resolution_targets: FingerprintTree::new(),
            paramodulation_targets: FingerprintTree::new(),
            rewrite_rules: FingerprintTree::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.clause_info.len()
    }

    fn get_resolution_term(&self, target: &ResolutionTarget) -> &Term {
        let clause = self.get_clause(target.clause_index);
        let literal = &clause.literals[target.literal_index];
        let mut term = if target.forwards {
            &literal.left
        } else {
            &literal.right
        };
        for i in &target.path {
            term = &term.args[*i];
        }
        term
    }

    // Get an iterator of (forward?, s, t) for all (s, t) pairs where there could be a s > t rewrite.
    // Basically, if our literal is s = t, and s > t in the KBO ordering, only allow (s, t).
    // Otherwise, also allow (t, s).
    fn quasiordered_term_pairs(literal: &Literal) -> Vec<(bool, &Term, &Term)> {
        let order = literal.left.kbo(&literal.right);
        match order {
            Ordering::Greater => {
                // s > t, so we only do forwards
                vec![(true, &literal.left, &literal.right)]
            }
            Ordering::Equal => {
                // s = t, so we do both directions
                vec![
                    (true, &literal.left, &literal.right),
                    (false, &literal.right, &literal.left),
                ]
            }
            Ordering::Less => {
                panic!("Backwards literal: {:?}", literal);
            }
        }
    }

    // Get an iterator of (forward?, s, t) for all s -> t paramodulations allowed for this literal.
    fn paramodulation_terms(literal: &Literal) -> Vec<(bool, &Term, &Term)> {
        if !literal.positive {
            return vec![];
        }
        ActiveSet::quasiordered_term_pairs(literal)
    }

    // Considers an inference that rewrites s -> t, based on pm_clause, in a known fact.
    // Returns whether this inference is allowed.
    // We are more restrictive on fact-fact inference than goal-based inference
    // because we have many more facts, thus we want to limit non-goal-related inference.
    fn allow_fact_combining(&self, pm_clause: &Clause, s: &Term, t: &Term) -> bool {
        if pm_clause.len() > 1 {
            return false;
        }

        s.kbo(t) == Ordering::Greater
    }

    // Tries to do superposition, but uses heuristics to not do the inference sometimes.
    //
    // The pm clause is:
    //   s = t | S
    // The res clause is:
    //   u ?= v | R
    //
    // fact_fact is whether both clause are factual, in which case we are more restrictive.
    fn maybe_superpose(
        &self,
        s: &Term,
        t: &Term,
        pm_clause: &Clause,
        pm_literal_index: usize,
        u_subterm: &Term,
        u_subterm_path: &[usize],
        res_clause: &Clause,
        res_literal_index: usize,
        res_forwards: bool,
        fact_fact: bool,
    ) -> Option<Clause> {
        let mut unifier = Unifier::new();
        // s/t are in "left" scope and u/v are in "right" scope regardless of whether they are
        // the actual left or right of their normalized literals.
        if !unifier.unify(Scope::Left, s, Scope::Right, u_subterm) {
            return None;
        }
        let new_clause = unifier.superpose(
            t,
            pm_clause,
            pm_literal_index,
            u_subterm_path,
            res_clause,
            res_literal_index,
            res_forwards,
        );

        let eliminated_clauses = pm_clause.len() + res_clause.len() - new_clause.len();
        assert!(eliminated_clauses > 0);

        // Restrict single elimination.
        if pm_clause.len() > 1 && res_clause.len() > 1 && eliminated_clauses == 1 {
            return None;
        }

        if fact_fact && eliminated_clauses == 1 {
            // Heuristic limit for fact-fact inference.
            if new_clause.atom_count() > 12 {
                return None;
            }
        }

        Some(new_clause)
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
    // Returns the clauses we generated along with the index of the clause we used to generate them.
    pub fn activate_paramodulator(
        &self,
        pm_clause: &Clause,
        clause_type: ClauseType,
    ) -> Vec<(Clause, usize)> {
        let pm_literal = &pm_clause.literals[0];
        if !pm_literal.positive {
            return vec![];
        }
        let mut result = vec![];
        for (_, s, t) in ActiveSet::paramodulation_terms(pm_literal) {
            if clause_type == ClauseType::Fact && !self.allow_fact_combining(pm_clause, s, t) {
                continue;
            }

            // Look for resolution targets that match pm_left
            let targets = self.resolution_targets.get_unifying(s);
            for target in targets {
                let u_subterm = self.get_resolution_term(target);

                if let Some(new_clause) = self.maybe_superpose(
                    s,
                    t,
                    pm_clause,
                    0,
                    u_subterm,
                    &target.path,
                    self.get_clause(target.clause_index),
                    target.literal_index,
                    target.forwards,
                    clause_type == ClauseType::Fact,
                ) {
                    result.push((new_clause, target.clause_index));
                }
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
    // Returns the clauses we generated along with the index of the clause we used to generate them.
    pub fn activate_resolver(
        &self,
        res_clause: &Clause,
        clause_type: ClauseType,
    ) -> Vec<(Clause, usize)> {
        let mut result = vec![];
        let res_literal = &res_clause.literals[0];

        for (res_forwards, u, _) in ActiveSet::quasiordered_term_pairs(res_literal) {
            let u_subterms = u.non_variable_subterms();

            for (path, u_subterm) in u_subterms {
                if res_literal.positive && path.is_empty() {
                    // We already handle the u = s case in activate_paramodulator.
                    continue;
                }

                // Look for paramodulation targets that match u_subterm
                let targets = self.paramodulation_targets.get_unifying(u_subterm);
                for target in targets {
                    let pm_clause = self.get_clause(target.clause_index);
                    let pm_literal = &pm_clause.literals[target.literal_index];
                    let (s, t) = if target.forwards {
                        (&pm_literal.left, &pm_literal.right)
                    } else {
                        (&pm_literal.right, &pm_literal.left)
                    };
                    if clause_type == ClauseType::Fact
                        && !self.allow_fact_combining(pm_clause, s, t)
                    {
                        continue;
                    }

                    if let Some(new_clause) = self.maybe_superpose(
                        s,
                        t,
                        pm_clause,
                        target.literal_index,
                        u_subterm,
                        &path,
                        res_clause,
                        0,
                        res_forwards,
                        clause_type == ClauseType::Fact,
                    ) {
                        result.push((new_clause, target.clause_index));
                    }
                }
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
        &self.clause_info[index].clause
    }

    pub fn get_proof_step(&self, index: usize) -> &ProofStep {
        &self.clause_info[index].proof_step
    }

    pub fn contains(&self, clause: &Clause) -> bool {
        self.clause_set.contains(clause)
    }

    // Rewrites subterms as well.
    // Only returns a new term if there is something to rewrite.
    fn rewrite_once(&self, term: &Term) -> Option<Term> {
        // Check if some args can be rewritten
        let rewritten_args: Vec<_> = term.args.iter().map(|arg| self.rewrite_once(arg)).collect();
        if rewritten_args.iter().any(|arg| arg.is_some()) {
            let mut new_args = vec![];
            for (original, rewritten) in term.args.iter().zip(rewritten_args) {
                if let Some(rewritten) = rewritten {
                    new_args.push(rewritten);
                } else {
                    new_args.push(original.clone());
                }
            }
            let new_term = term.replace_args(new_args);
            return Some(new_term);
        }

        // Check if we can rewrite this term at the root
        let clause_indexes = self.rewrite_rules.get_generalizing(&term);
        for i in clause_indexes {
            let clause = self.get_clause(*i);
            let rule = &clause.literals[0];
            let mut s = Specializer::new();

            if s.match_terms(&rule.left, term) {
                let new_term = s.specialize(&rule.right);
                return Some(new_term);
            }
        }

        None
    }

    // Rewrites up to limit times.
    fn rewrite_term_limited(&self, term: &Term, limit: u32) -> Option<Term> {
        if limit == 0 {
            panic!("error: ran out of rewrite stack");
        }
        if let Some(new_term) = self.rewrite_once(term) {
            self.rewrite_term_limited(&new_term, limit - 1)
                .or(Some(new_term))
        } else {
            None
        }
    }

    pub fn rewrite_term(&self, term: &Term) -> Option<Term> {
        self.rewrite_term_limited(term, 10)
    }

    fn rewrite_term_or_clone(&self, term: &Term) -> Term {
        if let Some(term) = self.rewrite_term(term) {
            term
        } else {
            term.clone()
        }
    }

    pub fn rewrite_literal(&self, literal: &Literal) -> Literal {
        let left = self.rewrite_term_or_clone(&literal.left);
        let right = self.rewrite_term_or_clone(&literal.right);
        Literal::new(literal.positive, left, right)
    }

    fn evaluate_literal(&mut self, literal: &Literal) -> Option<bool> {
        if literal.left == literal.right {
            return Some(literal.positive);
        }
        let answer: Option<bool> = match self.literal_set.lookup(&literal) {
            Some((positive, _)) => Some(positive),
            None => None,
        };
        answer
    }

    // Simplifies the clause based on both structural rules and the active set.
    // If the result is redundant given what's already known, return None.
    // If the result is an impossibility, return an empty clause.
    pub fn simplify(&mut self, clause: &Clause, clause_type: ClauseType) -> Option<Clause> {
        if clause.is_tautology() {
            return None;
        }
        if self.contains(&clause) {
            return None;
        }

        // Filter out any literals that are known to be true
        let mut rewritten_literals = vec![];
        for literal in &clause.literals {
            let rewritten_literal = self.rewrite_literal(literal);
            match self.evaluate_literal(&rewritten_literal) {
                Some(true) => {
                    // This literal is already known to be true.
                    // Thus, the whole clause is a tautology.
                    return None;
                }
                Some(false) => {
                    // This literal is already known to be false.
                    // Thus, we can just omit it from the disjunction.
                    continue;
                }
                None => {
                    if clause_type == ClauseType::NegatedGoal {
                        // Don't automatically simplify the goal.
                        rewritten_literals.push(literal.clone());
                    } else {
                        rewritten_literals.push(rewritten_literal);
                    }
                }
            }
        }
        let clause = Clause::new(rewritten_literals);
        if clause.is_tautology() {
            return None;
        }
        if self.contains(&clause) {
            return None;
        }
        Some(clause)
    }

    // Add all the resolution targets for a given literal.
    fn add_resolution_targets(
        &mut self,
        clause_index: usize,
        literal_index: usize,
        literal: &Literal,
    ) {
        for (path, subterm) in literal.left.non_variable_subterms() {
            self.resolution_targets.insert(
                subterm,
                ResolutionTarget {
                    clause_index,
                    literal_index,
                    forwards: true,
                    path,
                },
            );
        }
        for (path, subterm) in literal.right.non_variable_subterms() {
            self.resolution_targets.insert(
                subterm,
                ResolutionTarget {
                    clause_index,
                    literal_index,
                    forwards: false,
                    path,
                },
            );
        }
    }

    // Adds a clause so that it becomes available for resolution and paramodulation.
    // If select_all is set, then every literal can be used as a target for paramodulation.
    // Otherwise, only the first one can be.
    fn insert(&mut self, info: ClauseInfo) {
        let clause = &info.clause;
        let clause_index = self.clause_info.len();
        let leftmost_literal = &clause.literals[0];

        // Add resolution targets for the new clause.
        if info.clause_type == ClauseType::Fact {
            // Use any literal for resolution
            for (i, literal) in clause.literals.iter().enumerate() {
                self.add_resolution_targets(clause_index, i, literal);
            }
        } else {
            // Use only the leftmost literal for resolution.
            self.add_resolution_targets(clause_index, 0, leftmost_literal);
        }

        // Add paramodulation targets for the new clause.
        if info.clause_type == ClauseType::Fact {
            // Use any literal for paramodulation
            for (i, literal) in clause.literals.iter().enumerate() {
                for (forwards, from, _) in ActiveSet::paramodulation_terms(literal) {
                    self.paramodulation_targets.insert(
                        from,
                        ParamodulationTarget {
                            clause_index,
                            literal_index: i,
                            forwards,
                        },
                    );
                }
            }
        } else {
            // Use only the leftmost literal for paramodulation.
            for (forwards, from, _) in ActiveSet::paramodulation_terms(leftmost_literal) {
                self.paramodulation_targets.insert(
                    from,
                    ParamodulationTarget {
                        clause_index,
                        literal_index: 0,
                        forwards,
                    },
                );
            }
        }

        if clause.is_rewrite_rule() {
            let rewrite_literal = &clause.literals[0];
            self.rewrite_rules
                .insert(&rewrite_literal.left, clause_index);
        }

        self.clause_set.insert(clause.clone());

        if clause.literals.len() == 1 {
            self.literal_set.insert(clause.literals[0].clone());
        }

        self.clause_info.push(info);
    }

    // Generate all the inferences that can be made from a given clause, plus some existing clause.
    // The generated clauses are simplified, but we will simplify them again at activation time.
    // After generation, adds this clause to the active set.
    // Returns pairs describing how the generated clauses were proved.
    pub fn generate(&mut self, info: ClauseInfo) -> Vec<(Clause, ProofStep)> {
        let mut generated_clauses = vec![];
        let activated = Some(self.clause_info.len());

        // First calculate proof size for clauses dependent only on this one
        let activated_size = info.proof_step.proof_size;

        // We always allow ER/EF. Since they reduce the number of literals in a clause,
        // they won't lead to infinite loops on the fact library.
        if let Some(new_clause) = ActiveSet::equality_resolution(&info.clause) {
            generated_clauses.push((
                new_clause,
                ProofStep {
                    rule: ProofRule::EqualityResolution,
                    activated,
                    existing: None,
                    proof_size: activated_size + 1,
                },
            ));
        }
        for clause in ActiveSet::equality_factoring(&info.clause) {
            generated_clauses.push((
                clause,
                ProofStep {
                    rule: ProofRule::EqualityFactoring,
                    activated,
                    existing: None,
                    proof_size: activated_size + 1,
                },
            ));
        }

        for (new_clause, i) in self.activate_paramodulator(&info.clause, info.clause_type) {
            let existing_size = self.get_proof_step(i).proof_size;
            generated_clauses.push((
                new_clause,
                ProofStep {
                    rule: ProofRule::ActivatingParamodulator,
                    activated,
                    existing: Some(i),
                    proof_size: activated_size + existing_size + 1,
                },
            ))
        }
        for (new_clause, i) in self.activate_resolver(&info.clause, info.clause_type) {
            let existing_size = self.get_proof_step(i).proof_size;
            generated_clauses.push((
                new_clause,
                ProofStep {
                    rule: ProofRule::ActivatingResolver,
                    activated,
                    existing: Some(i),
                    proof_size: activated_size + existing_size + 1,
                },
            ))
        }

        // Simplify the generated clauses
        let mut simp_clauses = vec![];
        for (clause, step) in generated_clauses {
            if info.clause_type == ClauseType::Fact && step.proof_size > 2 {
                // Limit fact-fact inference
                continue;
            }
            if let Some(clause) = self.simplify(&clause, info.clause_type) {
                simp_clauses.push((clause, step));
            }
        }
        self.insert(info);

        simp_clauses
    }

    pub fn iter_clauses(&self) -> impl Iterator<Item = &Clause> {
        self.clause_info.iter().map(|info| &info.clause)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_activate_paramodulator() {
        // Create an active set that knows c0(c3) = c2
        let mut set = ActiveSet::new();
        let info = ClauseInfo::mock("c0(c3) = c2");
        set.insert(info);

        // We should be able to use c1 = c3 to paramodulate into c0(c3) = c2
        let pm_left = Term::parse("c1");
        let pm_right = Term::parse("c3");
        let pm_clause = Clause::new(vec![Literal::equals(pm_left.clone(), pm_right.clone())]);
        let result = set.activate_paramodulator(&pm_clause, ClauseType::Other);

        assert_eq!(result.len(), 1);
        let expected = Clause::new(vec![Literal::equals(
            Term::parse("c0(c1)"),
            Term::parse("c2"),
        )]);
        assert_eq!(result[0].0, expected);
    }

    #[test]
    fn test_activate_resolver() {
        // Create an active set that knows c1 = c3
        let mut set = ActiveSet::new();
        let info = ClauseInfo::mock("c1 = c3");
        set.insert(info);

        // We should be able to use c0(c3) = c2 as a resolver to get c0(c1) = c2
        let res_left = Term::parse("c0(c3)");
        let res_right = Term::parse("c2");
        let res_clause = Clause::new(vec![Literal::equals(res_left, res_right)]);
        let result = set.activate_resolver(&res_clause, ClauseType::Other);

        assert_eq!(result.len(), 1);
        let expected = Clause::new(vec![Literal::equals(
            Term::parse("c0(c1)"),
            Term::parse("c2"),
        )]);
        assert_eq!(result[0].0, expected);
    }

    #[test]
    fn test_equality_resolution() {
        let old_clause = Clause::new(vec![
            Literal::not_equals(Term::parse("x0"), Term::parse("c0")),
            Literal::equals(Term::parse("x0"), Term::parse("c1")),
        ]);
        let new_clause = ActiveSet::equality_resolution(&old_clause).unwrap();
        assert!(new_clause.literals.len() == 1);
        assert_eq!(format!("{}", new_clause), "c1 = c0".to_string());
    }

    #[test]
    fn test_mutually_recursive_equality_resolution() {
        // This is a bug we ran into. It shouldn't work
        let unresolvable_clause = Clause::parse("c0(x0, c0(x1, c1(x2))) != c0(c0(x2, x1), x0)");
        assert!(ActiveSet::equality_resolution(&unresolvable_clause).is_none());
    }

    #[test]
    fn test_select_all_literals_for_paramodulation() {
        let mut set = ActiveSet::new();
        let mut info = ClauseInfo::mock("c1 != c0(x0) | c2 = c3");
        info.clause_type = ClauseType::Fact;
        set.insert(info);
        let resolver = Clause::parse("c2 != c3");
        let result = set.activate_resolver(&resolver, ClauseType::Other);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].0.to_string(), "c1 != c0(x0)".to_string());
    }

    #[test]
    fn test_equality_factoring() {
        let old_clause = Clause::new(vec![
            Literal::equals(Term::parse("x0"), Term::parse("c0")),
            Literal::equals(Term::parse("x1"), Term::parse("c0")),
        ]);
        let new_clauses = ActiveSet::equality_factoring(&old_clause);
        for c in &new_clauses {
            if format!("{}", c) == "c0 = x0".to_string() {
                return;
            }
        }
        panic!("Did not find expected clause");
    }

    #[test]
    fn test_matching_entire_literal() {
        let mut set = ActiveSet::new();
        let mut info = ClauseInfo::mock("!c2(c0(c0(x0))) | c1(x0) != x0");
        info.clause_type = ClauseType::Fact;
        set.insert(info);
        let mut info = ClauseInfo::mock("c1(s1) = s1");
        info.clause_type = ClauseType::NegatedGoal;
        let new_clauses = set.generate(info);
        assert_eq!(new_clauses.len(), 1);
        assert_eq!(new_clauses[0].0.to_string(), "!c2(c0(c0(s1)))".to_string());
    }
}
