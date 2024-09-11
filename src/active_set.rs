use std::collections::{HashMap, HashSet};

use crate::clause::Clause;
use crate::fingerprint::FingerprintUnifier;
use crate::literal::Literal;
use crate::pattern_tree::LiteralSet;
use crate::proof_step::{ProofStep, Rule, Truthiness};
use crate::rewrite_tree::{Rewrite, RewriteTree};
use crate::term::Term;
use crate::term_graph::{TermGraph, TermId};
use crate::unifier::{Scope, Unifier};

// The ActiveSet stores a bunch of clauses that are indexed for various efficient lookups.
// The goal is that, given a new clause, it is efficient to determine what can be concluded
// given that clause and one clause from the active set.
// "Efficient" is relative - this still may take time roughly linear to the size of the active set.
#[derive(Clone)]
pub struct ActiveSet {
    // A vector for indexed reference
    steps: Vec<ProofStep>,

    // The long clauses (ie more than one literal) that we have proven.
    long_clauses: HashSet<Clause>,

    // The short clauses (ie just one literal) that we have proven.
    literal_set: LiteralSet,

    // An index of all the positive literals that we can do resolution with.
    positive_res_targets: FingerprintUnifier<ResolutionTarget>,

    // An index of all the negative literals that we can do resolution with.
    negative_res_targets: FingerprintUnifier<ResolutionTarget>,

    // A graph that encodes equalities and inequalities between terms.
    pub graph: TermGraph,

    // Information about every subterm that appears in an activated concrete literal,
    // except "true".
    subterms: Vec<SubtermInfo>,

    // An index to find the id of a subterm for an exact match.
    subterm_map: HashMap<Term, usize>,

    // An index to find the id of subterms for a pattern match.
    subterm_unifier: FingerprintUnifier<usize>,

    // A data structure to do the mechanical rewriting of subterms.
    rewrite_tree: RewriteTree,
}

// A ResolutionTarget represents a literal that we could do resolution with.
#[derive(Clone)]
struct ResolutionTarget {
    // Which proof step the resolution target is in.
    step_index: usize,

    // Which literal within the clause the resolution target is in.
    literal_index: usize,

    // Whether we index starting with the left term of the literal.
    // (As opposed to the right term.)
    left: bool,
}

// Information about a subterm that appears in an activated concrete literal.
#[derive(Clone)]
struct SubtermInfo {
    // The subterm itself
    term: Term,

    // Where the subterm occurs, in activated concrete literals.
    locations: Vec<SubtermLocation>,

    // The possible terms that this subterm can be rewritten to.
    // Note that this contains duplicates.
    // We do use duplicates to prevent factual-factual rewrites, but it is displeasing.
    rewrites: Vec<Rewrite>,

    // The depth of the subterm is the maximum depth of a clause that needs to be activated
    // to use this subterm.
    depth: u32,
}

// A SubtermLocation describes somewhere that the subterm exists among the activated clauses.
// Subterm locations always refer to concrete single-literal clauses.
#[derive(Clone)]
struct SubtermLocation {
    // Which proof step the subterm is in.
    // The literal can be either positive or negative.
    target_id: usize,

    // Whether the subterm is in the left term of the literal.
    // (As opposed to the right one.)
    left: bool,

    // This is the path from the root term to the subterm.
    // An empty path means the root, so the whole term is the relevant subterm.
    path: Vec<usize>,
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet {
            steps: vec![],
            long_clauses: HashSet::new(),
            literal_set: LiteralSet::new(),
            positive_res_targets: FingerprintUnifier::new(),
            negative_res_targets: FingerprintUnifier::new(),
            graph: TermGraph::new(),
            subterms: vec![],
            subterm_map: HashMap::new(),
            subterm_unifier: FingerprintUnifier::new(),
            rewrite_tree: RewriteTree::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.steps.len()
    }

    fn is_known_long_clause(&self, clause: &Clause) -> bool {
        clause.literals.len() > 1 && self.long_clauses.contains(clause)
    }

    // Finds all resolutions that can be done with a given proof step.
    // The "new clause" is the one that is being activated, and the "old clause" is the existing one.
    pub fn find_resolutions(&self, new_step: &ProofStep, output: &mut Vec<ProofStep>) {
        let new_step_id = self.next_id();
        for (i, new_literal) in new_step.clause.literals.iter().enumerate() {
            let target_map = if new_literal.positive {
                &self.negative_res_targets
            } else {
                &self.positive_res_targets
            };

            let targets = target_map.find_unifying(&new_literal.left);
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
                    output.push(step);
                }
            }
        }
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
        assert!(pos_clause.literals[pos_index].positive);

        let neg_clause = &neg_step.clause;
        assert!(!neg_clause.literals[neg_index].positive);

        // We want to only do resolution when the shorter clause can be entirely eliminated.
        // Thus, we check that all the literals in the shorter clause are either duplicates of
        // literals in the longer clause, or being canceled in the resolution.
        let (short_id, short_step, short_index, long_id, long_step, long_index) =
            if pos_clause.len() < neg_clause.len() {
                (pos_id, pos_step, pos_index, neg_id, neg_step, neg_index)
            } else {
                (neg_id, neg_step, neg_index, pos_id, pos_step, pos_index)
            };
        let short_clause = &short_step.clause;

        // Experimental.
        // TODO: if we can really skip out here, we might be able to make our data structures
        // more efficient elsewhere.
        if short_clause.len() > 1 {
            return None;
        }

        let long_clause = &long_step.clause;
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
        let step = ProofStep::new_resolution(long_id, long_step, short_id, short_step, clause);
        Some(step)
    }

    // Look for ways to rewrite a literal that is not yet in the active set.
    // The literal must be concrete.
    // The naming convention is that we use the pattern s->t to rewrite u in u ?= v.
    pub fn activate_rewrite_target(
        &mut self,
        target_id: usize,
        target_step: &ProofStep,
        output: &mut Vec<ProofStep>,
    ) {
        assert!(target_step.clause.len() == 1);
        let target_literal = &target_step.clause.literals[0];

        for (target_left, u, _) in target_literal.both_term_pairs() {
            let u_subterms = u.rewritable_subterms();

            for (path, u_subterm) in u_subterms {
                let u_subterm_id = if let Some(id) = self.subterm_map.get(&u_subterm) {
                    // We already have data for this subterm.
                    *id
                } else {
                    // We've never seen this subterm before.
                    // We need to find all the possible rewrites for it.
                    let rewrites = self.rewrite_tree.get_rewrites(u_subterm, 0);

                    // Add these rewrites to the term graph
                    let id1 = self.graph.insert_term(&u_subterm);
                    for rewrite in &rewrites {
                        let id2 = self.graph.insert_term(&rewrite.term);
                        self.add_to_term_graph(
                            rewrite.pattern_id,
                            Some(target_step.depth),
                            id1,
                            id2,
                            true,
                        );
                    }

                    // Populate the subterm info.
                    let id = self.subterms.len();
                    self.subterms.push(SubtermInfo {
                        term: u_subterm.clone(),
                        locations: vec![],
                        rewrites,
                        depth: target_step.depth,
                    });
                    self.subterm_map.insert(u_subterm.clone(), id);
                    self.subterm_unifier.insert(u_subterm, id);
                    id
                };

                // Apply all the ways to rewrite u_subterm.
                for rewrite in &self.subterms[u_subterm_id].rewrites {
                    if target_id == rewrite.pattern_id {
                        // Don't rewrite a literal with itself
                        continue;
                    }

                    let pattern_step = self.get_step(rewrite.pattern_id);
                    if target_step.truthiness == Truthiness::Factual
                        && pattern_step.truthiness == Truthiness::Factual
                    {
                        // No global-global rewriting
                        continue;
                    }

                    let ps = ProofStep::new_rewrite(
                        rewrite.pattern_id,
                        &pattern_step,
                        target_id,
                        target_step,
                        target_left,
                        &path,
                        &rewrite.term,
                    );
                    output.push(ps);
                }

                // Record the location of this subterm.
                self.subterms[u_subterm_id].locations.push(SubtermLocation {
                    target_id,
                    left: target_left,
                    path,
                });
            }
        }
    }

    // When we have a new rewrite pattern, find everything that we can rewrite with it.
    // The naming convention is that we use the pattern s->t to rewrite u in u ?= v.
    pub fn activate_rewrite_pattern(
        &mut self,
        pattern_id: usize,
        pattern_step: &ProofStep,
        output: &mut Vec<ProofStep>,
    ) {
        assert!(pattern_step.clause.len() == 1);
        let pattern_literal = &pattern_step.clause.literals[0];
        assert!(pattern_literal.positive);

        for (forwards, s, t) in pattern_literal.both_term_pairs() {
            if s.is_true() {
                // Don't rewrite from "true"
                continue;
            }

            // Look for existing subterms that match s
            let subterm_ids: Vec<usize> = self
                .subterm_unifier
                .find_unifying(s)
                .iter()
                .map(|&x| *x)
                .collect();

            for subterm_id in subterm_ids {
                let subterm_info = &self.subterms[subterm_id];
                let subterm = &subterm_info.term;

                let mut unifier = Unifier::new();
                if !unifier.unify(Scope::Left, s, Scope::Right, subterm) {
                    continue;
                }
                let new_subterm = unifier.apply(Scope::Left, t);

                for location in &subterm_info.locations {
                    if location.target_id == pattern_id {
                        // Don't rewrite a literal with itself
                        continue;
                    }
                    let target_id = location.target_id;
                    let target_step = self.get_step(target_id);

                    if pattern_step.truthiness == Truthiness::Factual
                        && target_step.truthiness == Truthiness::Factual
                    {
                        // No global-global rewriting
                        continue;
                    }

                    let ps = ProofStep::new_rewrite(
                        pattern_id,
                        pattern_step,
                        target_id,
                        target_step,
                        location.left,
                        &location.path,
                        &new_subterm,
                    );
                    output.push(ps);
                }

                // Add this rewrite to the term graph.
                let id1 = self.graph.insert_term(&subterm);
                let id2 = self.graph.insert_term(&new_subterm);
                self.add_to_term_graph(pattern_id, Some(subterm_info.depth), id1, id2, true);

                self.subterms[subterm_id].rewrites.push(Rewrite {
                    pattern_id,
                    forwards,
                    term: new_subterm,
                });
            }
        }
    }

    // Tries to do inference using the equality resolution (ER) rule.
    // Specifically, when one first literal is of the form
    //   u != v
    // then if we can unify u and v, we can eliminate this literal from the clause.
    pub fn equality_resolution(clause: &Clause) -> Vec<Clause> {
        let mut answer = vec![];

        for i in 0..clause.literals.len() {
            // See if we can eliminate the ith literal.
            let literal = &clause.literals[i];
            if literal.positive {
                // Negative literals come before positive ones so we're done
                break;
            }

            // The variables are in the same scope, which we will call "left".
            let mut unifier = Unifier::new();
            if !unifier.unify(Scope::Left, &literal.left, Scope::Left, &literal.right) {
                continue;
            }

            // We can do equality resolution
            let mut new_literals = vec![];
            for (j, lit) in clause.literals.iter().enumerate() {
                if j != i {
                    new_literals.push(unifier.apply_to_literal(Scope::Left, lit));
                }
            }

            let new_clause = Clause::new(new_literals);
            if !new_clause.is_tautology() {
                answer.push(new_clause);
            }
        }

        answer
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
    //
    // I find this rule to be unintuitive, extracting an inequality from only equalities.
    //
    // TODO: This "first clause" constraint seems incomplete or mistaken.
    pub fn equality_factoring(clause: &Clause) -> Vec<Clause> {
        let mut answer = vec![];
        let st_literal = &clause.literals[0];
        if !st_literal.positive {
            return answer;
        }
        for (_, s, t) in st_literal.both_term_pairs() {
            for i in 1..clause.literals.len() {
                let uv_literal = &clause.literals[i];
                if !uv_literal.positive {
                    continue;
                }

                for (_, u, v) in uv_literal.both_term_pairs() {
                    // The variables are all in the same scope, which we will call "left".
                    let mut unifier = Unifier::new();
                    if !unifier.unify(Scope::Left, s, Scope::Left, u) {
                        continue;
                    }
                    let mut literals = vec![];
                    literals.push(Literal::not_equals(
                        unifier.apply(Scope::Left, t),
                        unifier.apply(Scope::Left, v),
                    ));
                    literals.push(unifier.apply_to_literal(Scope::Left, uv_literal));
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

    pub fn has_step(&self, index: usize) -> bool {
        index < self.steps.len()
    }

    pub fn get_step(&self, index: usize) -> &ProofStep {
        &self.steps[index]
    }

    // Iterate over all active proof steps.
    pub fn iter_steps(&self) -> impl Iterator<Item = (usize, &ProofStep)> {
        self.steps.iter().enumerate()
    }

    // Iterate over all proof steps that depend on this id.
    pub fn find_consequences(&self, id: usize) -> impl Iterator<Item = (usize, &ProofStep)> {
        self.steps
            .iter()
            .enumerate()
            .filter(move |(_, step)| step.depends_on_active(id))
    }

    // Returns (value, id of clause) when this literal's value is known due to some existing clause.
    // No id is returned if this literal is "expr = expr".
    fn evaluate_literal(&self, literal: &Literal) -> Option<(bool, Option<usize>)> {
        literal.validate_type();
        if literal.left == literal.right {
            return Some((literal.positive, None));
        }
        match self.literal_set.find_generalization(&literal) {
            Some((positive, id)) => Some((positive, Some(id))),
            None => None,
        }
    }

    // Simplifies the clause based on both structural rules and the active set.
    // If the result is redundant given what's already known, return None.
    // Specializations are allowed, though, even if they're redundant.
    // If the result is an impossibility, return an empty clause.
    pub fn simplify(&self, mut step: ProofStep) -> Option<ProofStep> {
        if step.clause.is_tautology() {
            return None;
        }

        if self.is_known_long_clause(&step.clause) {
            return None;
        }

        // Filter out any literals that are known to be true
        let mut new_rules = vec![];
        let initial_num_literals = step.clause.literals.len();
        let mut output_literals = vec![];
        for literal in std::mem::take(&mut step.clause.literals) {
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
                        new_rules.push((id, self.get_step(id)));
                    }
                    continue;
                }
                None => {
                    output_literals.push(literal);
                }
            }
        }

        if output_literals.len() == initial_num_literals {
            // This proof step hasn't changed.
            step.clause.literals = output_literals;
            return Some(step);
        }

        let simplified_clause = Clause::new(output_literals);
        if simplified_clause.is_tautology() {
            return None;
        }
        if self.is_known_long_clause(&simplified_clause) {
            return None;
        }
        Some(ProofStep::new_simplified(
            step,
            &new_rules,
            simplified_clause,
        ))
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

    // Indexes a clause so that it becomes available for future proof step generation.
    // Return its id.
    fn insert(&mut self, step: ProofStep) -> usize {
        let step_index = self.next_id();
        let clause = &step.clause;

        // Add resolution targets for the new clause.
        for (i, literal) in clause.literals.iter().enumerate() {
            self.add_resolution_targets(step_index, i, literal);
        }

        // Store long clauses here. Short clauses will be kept in the literal set.
        if clause.literals.len() > 1 {
            self.long_clauses.insert(clause.clone());
        }

        self.steps.push(step);
        step_index
    }

    pub fn next_id(&self) -> usize {
        self.steps.len()
    }

    fn add_to_term_graph(
        &mut self,
        pattern_id: usize,
        inspiration_depth: Option<u32>,
        term1: TermId,
        term2: TermId,
        equal: bool,
    ) {
        if equal {
            self.graph
                .set_terms_equal(term1, term2, pattern_id, inspiration_depth);
        } else {
            assert!(inspiration_depth.is_none());
            self.graph.set_terms_not_equal(term1, term2, pattern_id);
        }
    }

    // Inference that is specific to literals.
    fn activate_literal(&mut self, activated_step: &ProofStep, output: &mut Vec<ProofStep>) {
        let activated_id = self.next_id();
        assert_eq!(activated_step.clause.len(), 1);
        let literal = &activated_step.clause.literals[0];

        // Using the literal as a rewrite target.
        if !literal.has_any_variable() {
            // Add this to the term graph.
            let left = self.graph.insert_term(&literal.left);
            let right = self.graph.insert_term(&literal.right);

            self.add_to_term_graph(activated_id, None, left, right, literal.positive);

            // The activated step could be rewritten immediately.
            self.activate_rewrite_target(activated_id, &activated_step, output);
        }

        // Using the literal as a rewrite pattern.
        if literal.positive && !activated_step.rule.is_rewrite() {
            // The activated step could be used as a rewrite pattern immediately.
            self.activate_rewrite_pattern(activated_id, &activated_step, output);

            // Index it so that it can be used as a rewrite pattern in the future.
            self.rewrite_tree.insert_literal(activated_id, literal);
        }

        self.literal_set.insert(&literal, activated_id);
    }

    // Generate all the inferences that can be made from a given clause, plus some existing clause.
    // This function does not simplify the inferences, or use the inferences to simplify anything else.
    // The prover will do all forms of simplification separately.
    // After generation, this clause is added to the active set.
    // Returns the id of the new clause, and pairs describing how the generated clauses were proved.
    pub fn activate(&mut self, activated_step: ProofStep) -> (usize, Vec<ProofStep>) {
        let mut output = vec![];
        let activated_id = self.next_id();

        // Unification-based inferences don't need to be done on specialization, because
        // they can operate directly on the general form.
        for new_clause in ActiveSet::equality_resolution(&activated_step.clause) {
            output.push(ProofStep::new_direct(
                &activated_step,
                Rule::EqualityResolution(activated_id),
                new_clause,
            ));
        }

        for clause in ActiveSet::equality_factoring(&activated_step.clause) {
            output.push(ProofStep::new_direct(
                &activated_step,
                Rule::EqualityFactoring(activated_id),
                clause,
            ));
        }

        for clause in ActiveSet::function_elimination(&activated_step.clause) {
            output.push(ProofStep::new_direct(
                &activated_step,
                Rule::FunctionElimination(activated_id),
                clause,
            ));
        }

        self.find_resolutions(&activated_step, &mut output);

        if activated_step.clause.len() == 1 {
            self.activate_literal(&activated_step, &mut output);
        }

        self.insert(activated_step);
        (activated_id, output)
    }

    pub fn iter_clauses(&self) -> impl Iterator<Item = &Clause> {
        self.steps.iter().map(|step| &step.clause)
    }

    // Find the index of all clauses used to prove the provided step.
    pub fn find_upstream(&self, step: &ProofStep, output: &mut HashSet<usize>) {
        let mut pending = vec![];
        for i in step.active_dependencies() {
            pending.push(i);
        }
        while !pending.is_empty() {
            let i = pending.pop().unwrap();
            if output.contains(&i) {
                continue;
            }
            output.insert(i);
            for j in self.get_step(i).active_dependencies() {
                pending.push(j);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_activate_rewrite_pattern() {
        // Create an active set that knows c0(c3) = c2
        let mut set = ActiveSet::new();
        let mut step = ProofStep::mock("c0(c3) = c2");
        step.truthiness = Truthiness::Hypothetical;
        set.activate(step);

        // We should be able replace c1 with c3 in "c0(c3) = c2"
        let pattern_step = ProofStep::mock("c1 = c3");
        let mut result = vec![];
        set.activate_rewrite_pattern(1, &pattern_step, &mut result);

        assert_eq!(result.len(), 1);
        let expected = Clause::new(vec![Literal::equals(
            Term::parse("c0(c1)"),
            Term::parse("c2"),
        )]);
        assert_eq!(result[0].clause, expected);
    }

    #[test]
    fn test_activate_rewrite_target() {
        // Create an active set that knows c1 = c3
        let mut set = ActiveSet::new();
        let step = ProofStep::mock("c1 = c3");
        set.activate(step);

        // We want to use c0(c3) = c2 to get c0(c1) = c2.
        let mut target_step = ProofStep::mock("c0(c3) = c2");
        target_step.truthiness = Truthiness::Hypothetical;
        let mut result = vec![];
        set.activate_rewrite_target(1, &target_step, &mut result);
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_equality_resolution() {
        let old_clause = Clause::new(vec![
            Literal::not_equals(Term::parse("x0"), Term::parse("c0")),
            Literal::equals(Term::parse("x0"), Term::parse("c1")),
        ]);
        let clauses = ActiveSet::equality_resolution(&old_clause);
        assert_eq!(clauses.len(), 1);
        assert!(clauses[0].len() == 1);
        assert_eq!(format!("{}", clauses[0]), "c1 = c0".to_string());
    }

    #[test]
    fn test_mutually_recursive_equality_resolution() {
        // This is a bug we ran into. It shouldn't work
        let clause = Clause::parse("c0(x0, c0(x1, c1(x2))) != c0(c0(x2, x1), x0)");
        assert!(ActiveSet::equality_resolution(&clause).is_empty());
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
        let mut step = ProofStep::mock("not c2(c0(c0(x0))) or c1(x0) != x0");
        step.truthiness = Truthiness::Factual;
        set.activate(step);
        let mut step = ProofStep::mock("c1(c3) = c3");
        step.truthiness = Truthiness::Counterfactual;
        let (_, new_clauses) = set.activate(step);
        assert_eq!(new_clauses.len(), 1);
        assert_eq!(
            new_clauses[0].clause.to_string(),
            "not c2(c0(c0(c3)))".to_string()
        );
    }

    #[test]
    fn test_equality_factoring_variable_numbering() {
        // This is a bug we ran into
        let mut set = ActiveSet::new();

        // Nonreflexive rule of less-than
        let step = ProofStep::mock("not c1(x0, x0)");
        set.activate(step);

        // Trichotomy
        let clause = Clause::parse("c1(x0, x1) or c1(x1, x0) or x0 = x1");
        let output = ActiveSet::equality_factoring(&clause);
        assert_eq!(output[0].to_string(), "c1(x0, x0) or x0 = x0");
    }

    #[test]
    fn test_self_referential_resolution() {
        // This is a bug we ran into. These things should not unify
        let mut set = ActiveSet::new();
        set.activate(ProofStep::mock("g2(x0, x0) = g0"));
        let mut step = ProofStep::mock("g2(g2(g1(c0, x0), x0), g2(x1, x1)) != g0");
        step.truthiness = Truthiness::Counterfactual;
        let mut results = vec![];
        set.find_resolutions(&step, &mut results);
        assert_eq!(results.len(), 0);
    }
}
