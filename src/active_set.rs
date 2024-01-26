use std::collections::HashSet;

use crate::clause::Clause;
use crate::fingerprint::FingerprintTree;
use crate::literal::Literal;
use crate::literal_set::LiteralSet;
use crate::proof_step::{ProofStep, Rule, Truthiness};
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

    rewrite_targets: FingerprintTree<RewriteTarget>,

    paramodulation_targets: FingerprintTree<ParamodulationTarget>,

    positive_res_targets: FingerprintTree<ResolutionTarget>,

    negative_res_targets: FingerprintTree<ResolutionTarget>,
}

// A ResolutionTarget represents a literal that could be resolved against.
struct ResolutionTarget {
    // Which proof step the resolution target is in.
    step_index: usize,

    // Which literal within the clause the resolution target is in.
    literal_index: usize,

    // Whether we index starting with the left term of the literal.
    // (As opposed to the right term.)
    left: bool,
}

// A RewriteTarget represents one a subterm within an active clause.
// So, in foo(bar(x)) = baz, bar(x) could be a rewrite target.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct RewriteTarget {
    // Which proof step the rewrite target is in.
    // The literal can be either positive or negative.
    step_index: usize,

    // Which literal within the clause the rewrite target is in.
    // TODO: remove
    literal_index: usize,

    // Whether we are rewriting the left term of the literal.
    // (As opposed to the right one.)
    left: bool,

    // We rewrite subterms. This is the path from the root term to the subterm.
    // An empty path means rewrite at the root.
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
            rewrite_targets: FingerprintTree::new(),
            paramodulation_targets: FingerprintTree::new(),
            positive_res_targets: FingerprintTree::new(),
            negative_res_targets: FingerprintTree::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.steps.len()
    }

    fn get_resolution_term(&self, target: &RewriteTarget) -> &Term {
        let clause = self.get_clause(target.step_index);
        let literal = &clause.literals[target.literal_index];
        let mut term = if target.left {
            &literal.left
        } else {
            &literal.right
        };
        for i in &target.path {
            term = &term.args[*i];
        }
        term
    }

    // Get an iterator of (forward?, s, t) for all s -> t paramodulations allowed for this literal.
    fn paramodulation_terms(literal: &Literal) -> Vec<(bool, &Term, &Term)> {
        if !literal.positive {
            return vec![];
        }
        literal.both_term_pairs()
    }

    // Tries to do a superposition from two clauses, but may fail to unify.
    //
    // The pm clause is:
    //   s = t | S
    // The res clause is:
    //   u ?= v | R
    fn try_superposition(
        s: &Term,
        t: &Term,
        pm_clause: &Clause,
        u_subterm: &Term,
        u_subterm_path: &[usize],
        res_clause: &Clause,
        res_forwards: bool,
    ) -> Option<Clause> {
        if pm_clause.len() > 1 || res_clause.len() > 1 {
            // Only allow superposition on short clauses.
            return None;
        }

        // This prevents the "sub-unification" case, where we become interested in a term by
        // unifying it with a subterm of another term.
        if !u_subterm_path.is_empty() && u_subterm.has_any_variable() {
            return None;
        }

        let mut unifier = Unifier::new();
        // s/t are in "left" scope and u/v are in "right" scope regardless of whether they are
        // the actual left or right of their normalized literals.
        if !unifier.unify(Scope::Left, s, Scope::Right, u_subterm) {
            return None;
        }

        // This constraint makes superposition only handle the "rewrite" case.
        if !unifier.right_reversible() {
            return None;
        }

        let literal =
            unifier.superpose_literals(t, u_subterm_path, &res_clause.literals[0], res_forwards);
        return Some(Clause::new(vec![literal]));
    }

    // Finds all resolutions that can be done with a given proof step.
    // The "new clause" is the one that is being activated, and the "old clause" is the existing one.
    pub fn find_resolutions(&self, new_step_id: usize, new_step: &ProofStep) -> Vec<ProofStep> {
        let mut results = vec![];
        for (i, new_literal) in new_step.clause.literals.iter().enumerate() {
            let target_map = if new_literal.positive {
                &self.negative_res_targets
            } else {
                &self.positive_res_targets
            };

            let targets = target_map.get_unifying(&new_literal.left);
            for target in targets {
                let old_step = self.get_step(target.step_index);
                let flipped = !target.left;

                if new_step.truthiness == Truthiness::Factual
                    && old_step.truthiness == Truthiness::Factual
                {
                    // No global-global resolution
                    continue;
                }

                let step = if new_literal.positive {
                    self.try_resolution(
                        new_step_id,
                        new_step,
                        i,
                        target.step_index,
                        old_step,
                        target.literal_index,
                        flipped,
                    )
                } else {
                    self.try_resolution(
                        target.step_index,
                        old_step,
                        target.literal_index,
                        new_step_id,
                        new_step,
                        i,
                        flipped,
                    )
                };

                if let Some(step) = step {
                    results.push(step);
                }
            }
        }
        results
    }

    // Tries to do a resolution from two clauses. This works when two literals can be unified
    // in such a way that they contradict each other.
    //
    // There are two ways that A = B and C != D can contradict.
    // When u(A) = u(C) and u(B) = u(D), that is "not flipped".
    // When u(A) = u(D) and u(B) = u(C), that is "flipped".
    //
    // To do resolution, one of the literals must be positive, and the other must be negative.
    fn try_resolution(
        &self,
        pos_id: usize,
        pos_step: &ProofStep,
        pos_index: usize,
        neg_id: usize,
        neg_step: &ProofStep,
        neg_index: usize,
        flipped: bool,
    ) -> Option<ProofStep> {
        let pos_clause = &pos_step.clause;
        let neg_clause = &neg_step.clause;

        // TODO: do this check outside try_resolution.
        if neg_clause.literals[neg_index].positive {
            return None;
        }

        // We want to only use reductive operations that are reductive because all the literals
        // in the shorter clause are either non-variable dupes or the one that is being canceled.
        // Let's be sure those are the only ones we are using.
        let (short_clause, short_index, long_clause, long_index) =
            if pos_clause.len() < neg_clause.len() {
                (pos_clause, pos_index, neg_clause, neg_index)
            } else {
                (neg_clause, neg_index, pos_clause, pos_index)
            };
        for (i, literal) in short_clause.literals.iter().enumerate() {
            if i == short_index {
                continue;
            }
            if literal.has_any_variable() {
                return None;
            }
            if long_clause.literals.contains(literal) {
                continue;
            }
            return None;
        }

        let mut unifier = Unifier::new();

        // The short clause is "left" scope and the long clause is "right" scope.
        // This is different from the "left" and "right" of the literals - unfortunately
        // "left" and "right" are a bit overloaded here.
        let short_a = &short_clause.literals[short_index].left;
        let short_b = &short_clause.literals[short_index].right;
        let (long_a, long_b) = if flipped {
            (
                &long_clause.literals[long_index].right,
                &long_clause.literals[long_index].left,
            )
        } else {
            (
                &long_clause.literals[long_index].left,
                &long_clause.literals[long_index].right,
            )
        };
        if !unifier.unify(Scope::Left, short_a, Scope::Right, long_a) {
            return None;
        }
        if !unifier.unify(Scope::Left, short_b, Scope::Right, long_b) {
            return None;
        }

        let mut literals = vec![];
        for (i, literal) in long_clause.literals.iter().enumerate() {
            if i == long_index {
                continue;
            }
            literals.push(unifier.apply_to_literal(Scope::Right, literal));
        }

        // Gather the output data
        let clause = Clause::new(literals);
        let step = ProofStep::new_resolution(pos_id, pos_step, neg_id, neg_step, clause);
        Some(step)
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
    pub fn activate_paramodulator(&self, pm_id: usize, pm_step: &ProofStep) -> Vec<ProofStep> {
        let mut results = vec![];
        for (i, pm_literal) in pm_step.clause.literals.iter().enumerate() {
            if !pm_literal.positive {
                continue;
            }
            for (pm_forwards, s, t) in ActiveSet::paramodulation_terms(pm_literal) {
                if s.is_true() {
                    // I don't think we should paramodulate into "true"
                    continue;
                }

                // Look for resolution targets that match s
                let targets = self.rewrite_targets.get_unifying(s);
                for target in targets {
                    let u_subterm = self.get_resolution_term(target);
                    let res_step = self.get_step(target.step_index);
                    if pm_step.truthiness == Truthiness::Factual
                        && res_step.truthiness == Truthiness::Factual
                    {
                        // No global-global superposition
                        continue;
                    }
                    if let Some(new_clause) = ActiveSet::try_superposition(
                        s,
                        t,
                        &pm_step.clause,
                        u_subterm,
                        &target.path,
                        &res_step.clause,
                        target.left,
                    ) {
                        results.push(ProofStep::new_superposition(
                            pm_id,
                            &pm_step,
                            target.step_index,
                            self.get_step(target.step_index),
                            new_clause,
                        ));
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
    pub fn activate_resolver(&self, res_id: usize, res_step: &ProofStep) -> Vec<ProofStep> {
        let mut results = vec![];
        for (i, res_literal) in res_step.clause.literals.iter().enumerate() {
            for (res_forwards, u, _) in res_literal.both_term_pairs() {
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
                        if pm_step.truthiness == Truthiness::Factual
                            && res_step.truthiness == Truthiness::Factual
                        {
                            // No global-global superposition
                            continue;
                        }
                        let pm_literal = &pm_step.clause.literals[target.literal_index];
                        let (s, t) = if target.forwards {
                            (&pm_literal.left, &pm_literal.right)
                        } else {
                            (&pm_literal.right, &pm_literal.left)
                        };
                        if s.is_true() {
                            // I don't think we should paramodulate into "true"
                            continue;
                        }
                        if let Some(new_clause) = ActiveSet::try_superposition(
                            s,
                            t,
                            &pm_step.clause,
                            u_subterm,
                            &path,
                            &res_step.clause,
                            res_forwards,
                        ) {
                            results.push(ProofStep::new_superposition(
                                target.step_index,
                                &pm_step,
                                res_id,
                                &res_step,
                                new_clause,
                            ));
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

        // We only do the first due to tradition.
        // Logically it seems like maybe we should allow others.
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

    // Tries to do inference using the function elimination (FE) rule.
    // Note that I just made up this rule, it isn't part of standard superposition.
    // It's pretty simple, though.
    // When f(a, b, d) != f(a, c, d), that implies that b != c.
    // We can run this operation on any negative literal in the clause.
    pub fn function_elimination(clause: &Clause) -> Vec<Clause> {
        let mut answer = vec![];

        for (i, target) in clause.literals.iter().enumerate() {
            // Check if we can eliminate the functions from the ith literal.
            if target.positive {
                // Negative literals come before positive ones so we're done
                break;
            }
            if target.left.head != target.right.head {
                continue;
            }
            if target.left.num_args() != target.right.num_args() {
                continue;
            }

            // We can do function elimination when precisely one of the arguments is different.
            let mut different_index = None;
            for (j, arg) in target.left.args.iter().enumerate() {
                if arg != &target.right.args[j] {
                    if different_index.is_some() {
                        different_index = None;
                        break;
                    }
                    different_index = Some(j);
                }
            }

            if let Some(j) = different_index {
                // Looks like we can eliminate the functions from this literal
                let mut literals = clause.literals.clone();
                literals[i] =
                    Literal::not_equals(target.left.args[j].clone(), target.right.args[j].clone());
                answer.push(Clause::new(literals))
            }
        }

        answer
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
        let mut new_rules = vec![];
        let mut filtered_literals = vec![];
        for literal in &step.clause.literals {
            match self.evaluate_literal(&literal) {
                Some((true, _)) => {
                    // This literal is already known to be true.
                    // Thus, the whole clause is a tautology.
                    return None;
                }
                Some((false, id)) => {
                    // This literal is already known to be false.
                    // Thus, we can just omit it from the disjunction.
                    if let Some(id) = id {
                        new_rules.push(id);
                    }
                    continue;
                }
                None => {
                    filtered_literals.push(literal.clone());
                }
            }
        }

        if new_rules.is_empty() {
            // This proof step hasn't changed.
            return Some(step);
        }

        let simplified_clause = Clause::new(filtered_literals);
        if simplified_clause.is_tautology() {
            return None;
        }
        if self.contains(&simplified_clause) {
            return None;
        }
        let mut new_truthiness = step.truthiness;
        for i in &new_rules {
            let rewrite_step = self.get_step(*i);
            new_truthiness = new_truthiness.combine(rewrite_step.truthiness);
        }
        Some(step.simplify(simplified_clause, new_rules, new_truthiness))
    }

    // Add all the rewrite targets for a given literal.
    fn add_rewrite_targets(&mut self, step_index: usize, literal_index: usize, literal: &Literal) {
        for (forwards, from, _) in literal.both_term_pairs() {
            for (path, subterm) in from.non_variable_subterms() {
                self.rewrite_targets.insert(
                    subterm,
                    RewriteTarget {
                        step_index,
                        literal_index,
                        left: forwards,
                        path,
                    },
                );
            }
        }
    }

    fn add_resolution_targets(
        &mut self,
        step_index: usize,
        literal_index: usize,
        literal: &Literal,
    ) {
        let tree = if literal.positive {
            &mut self.positive_res_targets
        } else {
            &mut self.negative_res_targets
        };
        tree.insert(
            &literal.left,
            ResolutionTarget {
                step_index,
                literal_index,
                left: true,
            },
        );
        tree.insert(
            &literal.right,
            ResolutionTarget {
                step_index,
                literal_index,
                left: false,
            },
        );
    }

    // Adds a clause so that it becomes available for resolution and paramodulation.
    // There's nothing heuristic here any more.
    fn insert(&mut self, step: ProofStep, id: usize) {
        let clause = &step.clause;
        let step_index = self.steps.len();

        // Add resolution targets for the new clause.
        // Use any literal for resolution.
        for (i, literal) in clause.literals.iter().enumerate() {
            self.add_rewrite_targets(step_index, i, literal);
            self.add_resolution_targets(step_index, i, literal);
        }

        // Add paramodulation targets for the new clause.
        // Use any literal for paramodulation.
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

        if let Some(new_clause) = ActiveSet::equality_resolution(&activated_step.clause) {
            generated_steps.push(ProofStep::new_direct(
                &activated_step,
                Rule::EqualityResolution(activated_id),
                new_clause,
            ));
        }

        for clause in ActiveSet::equality_factoring(&activated_step.clause) {
            generated_steps.push(ProofStep::new_direct(
                &activated_step,
                Rule::EqualityFactoring(activated_id),
                clause,
            ));
        }

        for clause in ActiveSet::function_elimination(&activated_step.clause) {
            generated_steps.push(ProofStep::new_direct(
                &activated_step,
                Rule::FunctionElimination(activated_id),
                clause,
            ));
        }

        for step in self.activate_paramodulator(activated_id, &activated_step) {
            generated_steps.push(step);
        }

        for step in self.activate_resolver(activated_id, &activated_step) {
            generated_steps.push(step);
        }

        for step in self.find_resolutions(activated_id, &activated_step) {
            generated_steps.push(step);
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
        let mut step = ProofStep::mock("c0(c3) = c2");
        step.truthiness = Truthiness::Hypothetical;
        set.insert(step, 0);

        // We should be able to use c1 = c3 to paramodulate into c0(c3) = c2
        let pm_step = ProofStep::mock("c1 = c3");
        let result = set.activate_paramodulator(0, &pm_step);

        assert_eq!(result.len(), 1);
        let expected = Clause::new(vec![Literal::equals(
            Term::parse("c0(c1)"),
            Term::parse("c2"),
        )]);
        assert_eq!(result[0].clause, expected);
    }

    #[test]
    fn test_activate_resolver() {
        // Create an active set that knows c1 = c3
        let mut set = ActiveSet::new();
        let step = ProofStep::mock("c1 = c3");
        set.insert(step, 0);

        // We should be able to use c0(c3) = c2 as a resolver to get c0(c1) = c2
        let mut res_step = ProofStep::mock("c0(c3) = c2");
        res_step.truthiness = Truthiness::Hypothetical;
        let result = set.activate_resolver(0, &res_step);

        assert_eq!(result.len(), 1);
        let expected = Clause::new(vec![Literal::equals(
            Term::parse("c0(c1)"),
            Term::parse("c2"),
        )]);
        assert_eq!(result[0].clause, expected);
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
    fn test_equality_factoring_basic() {
        let old_clause = Clause::new(vec![
            Literal::equals(Term::parse("x0"), Term::parse("c0")),
            Literal::equals(Term::parse("x1"), Term::parse("c0")),
        ]);
        let new_clauses = ActiveSet::equality_factoring(&old_clause);
        let expected = Clause::parse("c0 = x0");
        for c in &new_clauses {
            if *c == expected {
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
        step.truthiness = Truthiness::Counterfactual;
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
