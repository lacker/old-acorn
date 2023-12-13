use std::cmp::Ordering;
use std::collections::HashSet;

use crate::clause::Clause;
use crate::fingerprint::FingerprintTree;
use crate::literal::Literal;
use crate::literal_set::LiteralSet;
use crate::proof_step::{ProofStep, Rule, Truthiness};
use crate::rewrite_tree::RewriteTree;
use crate::term::Term;
use crate::unifier::{Scope, Unifier};

// The ActiveSet stores a bunch of clauses that are indexed for various efficient lookups.
// The goal is that, given a new clause, it is efficient to determine what can be concluded
// given that clause and one clause from the active set.
// "Efficient" is relative - this still may take time roughly linear to the size of the active set.
pub struct ActiveSet {
    // A vector for indexed reference
    steps: Vec<ProofStep>,

    // A HashSet for checking what complete clauses we already know
    clause_set: HashSet<Clause>,

    // A LiteralSet for checking specific literals we already know, including generalization
    literal_set: LiteralSet,

    resolution_targets: FingerprintTree<ResolutionTarget>,

    paramodulation_targets: FingerprintTree<ParamodulationTarget>,

    // Represents each rewrite rule as an index into steps.
    // A clause can only be a rewrite if it's a single foo = bar literal, and foo > bar by the KBO.
    // So we only need to store the clause index of the rewrite rule.
    rewrite_tree: RewriteTree,

    // How many ProofSteps have been generated (not activated) during this proof.
    num_generated: usize,
}

// A ResolutionTarget represents one a subterm within an active clause.
// So, in foo(bar(x)) = baz, bar(x) could be a resolution target.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ResolutionTarget {
    // Which proof step the resolution target is in.
    // For resolution, the literal can be either positive or negative.
    step_index: usize,

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

// A ParamodulationTarget represents one side of a literal within an active clause.
// So, in foo(bar(x)) = baz, bar(x) could *not* be a paramodulation target.
// Only the whole foo(bar(x)).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ParamodulationTarget {
    // Which proof step the paramodulation target is in.
    step_index: usize,

    // Which literal within the clause the paramodulation target is in.
    literal_index: usize,

    // "forwards" paramodulation is when we use s = t to rewrite s to t.
    // "backwards" paramodulation is when we use s = t to rewrite t to s.
    forwards: bool,
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet {
            steps: vec![],
            clause_set: HashSet::new(),
            literal_set: LiteralSet::new(),
            resolution_targets: FingerprintTree::new(),
            paramodulation_targets: FingerprintTree::new(),
            rewrite_tree: RewriteTree::new(),
            num_generated: 0,
        }
    }

    // Get a number representing the order in which a clause was generated.
    pub fn next_generation_ordinal(&mut self) -> usize {
        let ordinal = self.num_generated;
        self.num_generated += 1;
        ordinal
    }

    pub fn len(&self) -> usize {
        self.steps.len()
    }

    fn get_resolution_term(&self, target: &ResolutionTarget) -> &Term {
        let clause = self.get_clause(target.step_index);
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
        if fact_fact && !pm_clause.is_rewrite_rule() {
            // Heuristic restriction of fact-fact inference.
            return None;
        }

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

        let eliminated_literals = pm_clause.len() + res_clause.len() - new_clause.len();
        assert!(eliminated_literals > 0);

        // Heuristic restriction of superpositions that lengthen clauses.
        if pm_clause.len() > 1 && res_clause.len() > 1 && eliminated_literals == 1 {
            return None;
        }

        if fact_fact && eliminated_literals == 1 {
            // Heuristic restriction of fact-fact inference.
            if new_clause.atom_count() > 12 {
                return None;
            }
        }

        Some(new_clause)
    }

    // Look for superposition inferences using a paramodulator which is not yet in the
    // active set.in total, we activated
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
    pub fn activate_paramodulator(&self, pm_step: &ProofStep) -> Vec<(Clause, usize)> {
        let mut results = vec![];
        for (i, pm_literal) in pm_step.clause.literals.iter().enumerate() {
            if !pm_literal.positive {
                continue;
            }
            for (_, s, t) in ActiveSet::paramodulation_terms(pm_literal) {
                // Look for resolution targets that match pm_left
                let targets = self.resolution_targets.get_unifying(s);
                for target in targets {
                    let u_subterm = self.get_resolution_term(target);
                    let res_step = self.get_step(target.step_index);
                    let fact_fact = pm_step.truthiness == Truthiness::Factual
                        && res_step.truthiness == Truthiness::Factual;
                    if let Some(new_clause) = self.maybe_superpose(
                        s,
                        t,
                        &pm_step.clause,
                        i,
                        u_subterm,
                        &target.path,
                        &res_step.clause,
                        target.literal_index,
                        target.forwards,
                        fact_fact,
                    ) {
                        results.push((new_clause, target.step_index));
                    }
                }
            }
        }
        results
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
    pub fn activate_resolver(&self, res_step: &ProofStep) -> Vec<(Clause, usize)> {
        let mut results = vec![];
        for (i, res_literal) in res_step.clause.literals.iter().enumerate() {
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
                        let pm_step = self.get_step(target.step_index);
                        let pm_literal = &pm_step.clause.literals[target.literal_index];
                        let (s, t) = if target.forwards {
                            (&pm_literal.left, &pm_literal.right)
                        } else {
                            (&pm_literal.right, &pm_literal.left)
                        };
                        let fact_fact = pm_step.truthiness == Truthiness::Factual
                            && res_step.truthiness == Truthiness::Factual;
                        if let Some(new_clause) = self.maybe_superpose(
                            s,
                            t,
                            &pm_step.clause,
                            target.literal_index,
                            u_subterm,
                            &path,
                            &res_step.clause,
                            i,
                            res_forwards,
                            fact_fact,
                        ) {
                            results.push((new_clause, target.step_index));
                        }
                    }
                }
            }
        }

        results
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
                            literals
                                .push(unifier.apply_to_literal(Scope::Left, &clause.literals[j]));
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
        &self.steps[index].clause
    }

    pub fn get_step(&self, index: usize) -> &ProofStep {
        &self.steps[index]
    }

    pub fn contains(&self, clause: &Clause) -> bool {
        self.clause_set.contains(clause)
    }

    // Rewrites this literal, appending a list of the rewrite rules used.
    fn rewrite_literal(&self, literal: &Literal, rules: &mut Vec<usize>) -> Literal {
        let left = self.rewrite_tree.rewrite_or_clone(&literal.left, rules);
        let right = self.rewrite_tree.rewrite_or_clone(&literal.right, rules);
        Literal::new(literal.positive, left, right)
    }

    // Returns (value, id of clause) when this literal's value is known due to some existing clause.
    // No id is returned if this literal is "expr = expr".
    fn evaluate_literal(&self, literal: &Literal) -> Option<(bool, Option<usize>)> {
        if literal.left == literal.right {
            return Some((literal.positive, None));
        }
        match self.literal_set.lookup(&literal) {
            Some((positive, _, id)) => Some((positive, Some(id))),
            None => None,
        }
    }

    // Simplifies the clause based on both structural rules and the active set.
    // If the result is redundant given what's already known, return None.
    // If the result is an impossibility, return an empty clause.
    pub fn simplify(&self, step: ProofStep) -> Option<ProofStep> {
        if step.clause.is_tautology() {
            return None;
        }
        if self.contains(&step.clause) {
            return None;
        }

        // Filter out any literals that are known to be true
        let mut new_rewrites = vec![];
        let mut rewritten_literals = vec![];
        for literal in &step.clause.literals {
            let rewritten_literal = self.rewrite_literal(literal, &mut new_rewrites);
            match self.evaluate_literal(&rewritten_literal) {
                Some((true, _)) => {
                    // This literal is already known to be true.
                    // Thus, the whole clause is a tautology.
                    return None;
                }
                Some((false, id)) => {
                    // This literal is already known to be false.
                    // Thus, we can just omit it from the disjunction.
                    if let Some(id) = id {
                        new_rewrites.push(id);
                    }
                    continue;
                }
                None => {
                    if step.is_negated_goal() {
                        // Don't automatically simplify the goal.
                        rewritten_literals.push(literal.clone());
                    } else {
                        rewritten_literals.push(rewritten_literal);
                    }
                }
            }
        }

        if new_rewrites.is_empty() {
            // This proof step hasn't changed.
            return Some(step);
        }

        let simplified_clause = Clause::new(rewritten_literals);
        if simplified_clause.is_tautology() {
            return None;
        }
        if self.contains(&simplified_clause) {
            return None;
        }
        let mut new_truthiness = step.truthiness;
        for i in &new_rewrites {
            let rewrite_step = self.get_step(*i);
            new_truthiness = new_truthiness.combine(rewrite_step.truthiness);
        }
        Some(step.rewrite(simplified_clause, new_rewrites, new_truthiness))
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
                    step_index: clause_index,
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
                    step_index: clause_index,
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
    fn insert(&mut self, step: ProofStep, id: usize) {
        let clause = &step.clause;
        let step_index = self.steps.len();
        let leftmost_literal = &clause.literals[0];

        // Add resolution targets for the new clause.
        if step.truthiness == Truthiness::Factual {
            // Use any literal for resolution
            for (i, literal) in clause.literals.iter().enumerate() {
                self.add_resolution_targets(step_index, i, literal);
            }
        } else {
            // Use only the leftmost literal for resolution.
            // NOTE: these resolution targets don't end up being used!
            self.add_resolution_targets(step_index, 0, leftmost_literal);
        }

        // Add paramodulation targets for the new clause.
        if step.truthiness == Truthiness::Factual {
            // Use any literal for paramodulation
            for (i, literal) in clause.literals.iter().enumerate() {
                for (forwards, from, _) in ActiveSet::paramodulation_terms(literal) {
                    self.paramodulation_targets.insert(
                        from,
                        ParamodulationTarget {
                            step_index,
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
                        step_index,
                        literal_index: 0,
                        forwards,
                    },
                );
            }
        }

        if clause.is_rewrite_rule() && step.truthiness == Truthiness::Factual {
            self.rewrite_tree
                .add_rule(step_index, &leftmost_literal.left, &leftmost_literal.right);
        }

        self.clause_set.insert(clause.clone());

        if clause.literals.len() == 1 {
            self.literal_set.insert(clause.literals[0].clone(), id);
        }

        self.steps.push(step);
    }

    // Generate all the inferences that can be made from a given clause, plus some existing clause.
    // Does not simplify.
    // After generation, adds this clause to the active set.
    // Returns pairs describing how the generated clauses were proved.
    pub fn generate(&mut self, activated_step: ProofStep) -> Vec<ProofStep> {
        let mut generated_steps = vec![];
        let activated_id = self.steps.len();

        // We always allow ER/EF. Since they reduce (total literals + positive literals) in a clause,
        // they won't lead to infinite loops on the fact library.
        if let Some(new_clause) = ActiveSet::equality_resolution(&activated_step.clause) {
            generated_steps.push(ProofStep::new_direct(
                &activated_step,
                Rule::EqualityResolution(activated_id),
                new_clause,
                self.next_generation_ordinal(),
            ));
        }
        for clause in ActiveSet::equality_factoring(&activated_step.clause) {
            generated_steps.push(ProofStep::new_direct(
                &activated_step,
                Rule::EqualityFactoring(activated_id),
                clause,
                self.next_generation_ordinal(),
            ));
        }

        for (new_clause, resolver_id) in self.activate_paramodulator(&activated_step) {
            let generation_ordinal = self.next_generation_ordinal();
            generated_steps.push(ProofStep::new_superposition(
                activated_id,
                &activated_step,
                resolver_id,
                self.get_step(resolver_id),
                new_clause,
                generation_ordinal,
            ));
        }
        for (new_clause, paramodulator_id) in self.activate_resolver(&activated_step) {
            let generation_ordinal = self.next_generation_ordinal();
            generated_steps.push(ProofStep::new_superposition(
                paramodulator_id,
                self.get_step(paramodulator_id),
                activated_id,
                &activated_step,
                new_clause,
                generation_ordinal,
            ));
        }

        self.insert(activated_step, activated_id);
        generated_steps
    }

    pub fn iter_clauses(&self) -> impl Iterator<Item = &Clause> {
        self.steps.iter().map(|step| &step.clause)
    }

    // Find the index of all clauses used to prove the provided step.
    pub fn find_upstream(&self, step: &ProofStep) -> Vec<usize> {
        let mut pending = Vec::<usize>::new();
        let mut seen = HashSet::new();
        for i in step.dependencies() {
            pending.push(*i);
        }
        while !pending.is_empty() {
            let i = pending.pop().unwrap();
            if seen.contains(&i) {
                continue;
            }
            seen.insert(i);
            for j in self.get_step(i).dependencies() {
                pending.push(*j);
            }
        }

        // Print out the clauses in order.
        let mut indices = seen.into_iter().collect::<Vec<_>>();
        indices.sort();
        indices
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_activate_paramodulator() {
        // Create an active set that knows c0(c3) = c2
        let mut set = ActiveSet::new();
        let step = ProofStep::mock("c0(c3) = c2");
        set.insert(step, 0);

        // We should be able to use c1 = c3 to paramodulate into c0(c3) = c2
        let pm_step = ProofStep::mock("c1 = c3");
        let result = set.activate_paramodulator(&pm_step);

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
        let step = ProofStep::mock("c1 = c3");
        set.insert(step, 0);

        // We should be able to use c0(c3) = c2 as a resolver to get c0(c1) = c2
        let res_step = ProofStep::mock("c0(c3) = c2");
        let result = set.activate_resolver(&res_step);

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
        let mut step = ProofStep::mock("c1 != c0(x0) | c2 = c3");
        step.truthiness = Truthiness::Factual;
        set.insert(step, 0);
        let mut res_step = ProofStep::mock("c2 != c3");
        res_step.truthiness = Truthiness::Hypothetical;
        let result = set.activate_resolver(&res_step);
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
        let mut step = ProofStep::mock("!c2(c0(c0(x0))) | c1(x0) != x0");
        step.truthiness = Truthiness::Factual;
        set.insert(step, 0);
        let mut step = ProofStep::mock("c1(c3) = c3");
        step.truthiness = Truthiness::Hypothetical;
        let new_clauses = set.generate(step);
        assert_eq!(new_clauses.len(), 1);
        assert_eq!(
            new_clauses[0].clause.to_string(),
            "!c2(c0(c0(c3)))".to_string()
        );
    }

    #[test]
    fn test_equality_factoring_variable_numbering() {
        // This is a bug we ran into
        let mut set = ActiveSet::new();

        // Nonreflexive rule of less-than
        let mut step = ProofStep::mock("!c1(x0, x0)");
        step.truthiness = Truthiness::Factual;
        set.insert(step, 1);

        // Trichotomy
        let clause = Clause::parse("c1(x0, x1) | c1(x1, x0) | x0 = x1");
        let output = ActiveSet::equality_factoring(&clause);
        assert_eq!(output[0].to_string(), "c1(x0, x0) | x0 = x0");
    }
}
