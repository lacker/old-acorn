use std::collections::HashSet;

use crate::clause::Clause;
use crate::fingerprint::FingerprintTree;
use crate::literal::Literal;
use crate::pattern_tree::LiteralSet;
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

    // The long clauses (ie more than one literal) that we already know
    long_clauses: HashSet<Clause>,

    // For checking specific literals we already know, including generalization
    literal_tree: LiteralSet,

    // An index of all the subterms that can be rewritten.
    rewrite_targets: FingerprintTree<RewriteTarget>,

    // An index of all the ways to rewrite subterms.
    rewrite_patterns: RewriteTree,

    // An index of all the positive literals that we can do resolution with.
    positive_res_targets: FingerprintTree<ResolutionTarget>,

    // An index of all the negative literals that we can do resolution with.
    negative_res_targets: FingerprintTree<ResolutionTarget>,
}

// A ResolutionTarget represents a literal that we could do resolution with.
struct ResolutionTarget {
    // Which proof step the resolution target is in.
    step_index: usize,

    // Which literal within the clause the resolution target is in.
    literal_index: usize,

    // Whether we index starting with the left term of the literal.
    // (As opposed to the right term.)
    left: bool,
}

// A RewriteTarget represents a subterm within an active clause, that could be rewritten.
// So, in foo(bar(x)) = baz, bar(x) could be a rewrite target.
// We only rewrite within single literals.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct RewriteTarget {
    // Which proof step the rewrite target is in.
    // The literal can be either positive or negative.
    step_index: usize,

    // Whether we are rewriting the left term of the literal.
    // (As opposed to the right one.)
    left: bool,

    // We rewrite subterms. This is the path from the root term to the subterm.
    // An empty path means rewrite at the root.
    path: Vec<usize>,
}

// TODO: remove
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct OldRewritePattern {
    // Which proof step to use as a rewrite pattern.
    step_index: usize,

    // "forwards" rewriting is when we use s = t to rewrite s to t.
    // "backwards" rewriting is when we use s = t to rewrite t to s.
    forwards: bool,
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet {
            steps: vec![],
            long_clauses: HashSet::new(),
            literal_tree: LiteralSet::new(),
            rewrite_targets: FingerprintTree::new(),
            rewrite_patterns: RewriteTree::new(),
            positive_res_targets: FingerprintTree::new(),
            negative_res_targets: FingerprintTree::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.steps.len()
    }

    fn is_known_long_clause(&self, clause: &Clause) -> bool {
        clause.literals.len() > 1 && self.long_clauses.contains(clause)
    }

    fn get_subterm(&self, target: &RewriteTarget) -> &Term {
        let clause = self.get_clause(target.step_index);
        let literal = &clause.literals[0];
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

    // A helper to print a clause that may not yet be inserted.
    fn clause_str(&self, index: usize, extra: Option<(usize, &ProofStep)>) -> String {
        if let Some((id, step)) = extra {
            if id == index {
                return format!("clause {}: {}", id, step.clause);
            }
        }
        format!("clause {}: {}", index, self.get_clause(index))
    }

    // Not as nice as the Prover's print_proof_step, because it uses ids instead of nice names for
    // values, but useful for debugging.
    // You can pass an "extra" step that does not yet exist.
    pub fn print_proof_step(&self, step: &ProofStep, extra: Option<(usize, &ProofStep)>) {
        println!("proof step:");
        println!("  output: {}", step.clause);
        match &step.rule {
            Rule::Assumption => {
                println!("  rule: assumption");
            }
            Rule::EqualityResolution(id) => {
                println!("  rule: equality resolution from {}", id);
                println!("  clause {}: {}", id, self.clause_str(*id, extra));
            }
            Rule::EqualityFactoring(id) => {
                println!("  rule: equality factoring from {}", id);
                println!("  clause {}: {}", id, self.clause_str(*id, extra));
            }
            Rule::FunctionElimination(id) => {
                println!("  rule: function elimination from {}", id);
                println!("  clause {}: {}", id, self.clause_str(*id, extra));
            }
            Rule::Rewrite(info) => {
                println!(
                    "  rule: rewrite with target {}, pattern {}",
                    info.target_id, info.pattern_id
                );
                println!(
                    "  target clause {}: {}",
                    info.target_id,
                    self.clause_str(info.target_id, extra)
                );
                println!(
                    "  pattern clause {}: {}",
                    info.pattern_id,
                    self.clause_str(info.pattern_id, extra)
                );
            }
            Rule::Resolution(info) => {
                println!(
                    "  rule: resolution with positive {}, negative {}",
                    info.positive_id, info.negative_id
                );
                println!(
                    "  positive clause {}: {}",
                    info.positive_id,
                    self.clause_str(info.positive_id, extra)
                );
                println!(
                    "  negative clause {}: {}",
                    info.negative_id,
                    self.clause_str(info.negative_id, extra)
                );
            }
        }
    }

    // Tries to do a rewrite, but may fail or decline.
    // The "indexing" type stuff happens outside this function.
    //
    // We are using the equality "pattern" to rewrite "target".
    // pattern_forwards is the rewrite direction, ie forwards is using "s = t" to rewrite s -> t.
    // target_left tells us whether we are rewriting the left or right of the target literal.
    // subterm is the subterm of the target literal that we are rewriting.
    // path is the subpath at which subterm exists in the target term.
    //
    // Returns None if the rewrite doesn't work, either mechanically or heuristically.
    fn try_rewrite(
        pattern_id: usize,
        pattern_step: &ProofStep,
        pattern_forwards: bool,
        target_id: usize,
        target_step: &ProofStep,
        target_left: bool,
        subterm: &Term,
        path: &[usize],
    ) -> Option<ProofStep> {
        if pattern_step.truthiness == Truthiness::Factual
            && target_step.truthiness == Truthiness::Factual
        {
            // No global-global rewriting
            return None;
        }
        let pattern_literal = &pattern_step.clause.literals[0];
        let (s, t) = if pattern_forwards {
            (&pattern_literal.left, &pattern_literal.right)
        } else {
            (&pattern_literal.right, &pattern_literal.left)
        };
        let target_literal = &target_step.clause.literals[0];

        let mut unifier = Unifier::new();
        // s/t are in "left" scope and u/v are in "right" scope regardless of whether they are
        // the actual left or right of their normalized literals.
        if !unifier.unify(Scope::Left, s, Scope::Right, subterm) {
            return None;
        }

        // This constraint makes superposition only handle the "rewrite" case.
        if !unifier.right_reversible() {
            return None;
        }

        let literal = unifier.superpose_literals(t, path, &target_literal, target_left);
        let new_clause = Clause::new(vec![literal]);
        Some(ProofStep::new_rewrite(
            pattern_id,
            pattern_step,
            target_id,
            target_step,
            new_clause,
            path.is_empty(),
        ))
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
        assert!(pos_clause.literals[pos_index].positive);

        let neg_clause = &neg_step.clause;
        assert!(!neg_clause.literals[neg_index].positive);

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

    // When we have a new rewrite pattern, find everything that we can rewrite with it.
    pub fn activate_rewrite_pattern(
        &self,
        pattern_id: usize,
        pattern_step: &ProofStep,
    ) -> Vec<ProofStep> {
        let mut results = vec![];
        assert!(pattern_step.clause.len() == 1);
        let pattern_literal = &pattern_step.clause.literals[0];
        assert!(pattern_literal.positive);

        for (pattern_forwards, s, _) in pattern_literal.both_term_pairs() {
            if s.is_true() {
                // Don't rewrite from "true"
                continue;
            }

            // Look for resolution targets that match s
            let targets = self.rewrite_targets.get_unifying(s);
            for target in targets {
                let subterm = self.get_subterm(target);
                if let Some(ps) = ActiveSet::try_rewrite(
                    pattern_id,
                    pattern_step,
                    pattern_forwards,
                    target.step_index,
                    self.get_step(target.step_index),
                    target.left,
                    subterm,
                    &target.path,
                ) {
                    results.push(ps);
                }
            }
        }
        results
    }

    // Look for ways to rewrite a literal that is not yet in the active set.
    pub fn activate_rewrite_target(
        &self,
        target_id: usize,
        target_step: &ProofStep,
    ) -> Vec<ProofStep> {
        let mut results = vec![];
        assert!(target_step.clause.len() == 1);
        let target_literal = &target_step.clause.literals[0];
        let next_var = target_literal.least_unused_variable();
        for (_, u, v) in target_literal.both_term_pairs() {
            let u_subterms = u.rewritable_subterms();

            for (path, u_subterm) in u_subterms {
                if target_literal.positive && path.is_empty() {
                    // The "transitive equality" case.
                    // We know a = b and we are activating b = c.
                    // This will be caught twice, because b = c could be either pattern or target.
                    // So, we don't bother catching it here.
                    continue;
                }

                // Look for ways to rewrite u_subterm.
                // No global-global rewriting
                let allow_factual = target_step.truthiness != Truthiness::Factual;
                let rewrites =
                    self.rewrite_patterns
                        .get_rewrites(u_subterm, allow_factual, next_var);
                for (step_index, _, new_subterm) in rewrites {
                    let pattern_step = self.get_step(step_index);
                    let new_u = u.replace_at_path(&path, new_subterm);
                    let new_literal = Literal::new(target_literal.positive, new_u, v.clone());
                    new_literal.validate_type();
                    let new_clause = Clause::new(vec![new_literal]);
                    let ps = ProofStep::new_rewrite(
                        step_index,
                        pattern_step,
                        target_id,
                        target_step,
                        new_clause,
                        path.is_empty(),
                    );
                    results.push(ps);
                }
            }
        }

        results
    }

    // Tries to do inference using the equality resolution (ER) rule.
    // This assumes we are operating on the first literal.
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

    // Iterate over all proof steps that depend on this id.
    pub fn find_consequences<'a>(
        &'a self,
        id: usize,
    ) -> impl Iterator<Item = (usize, &'a ProofStep)> {
        self.steps
            .iter()
            .enumerate()
            .filter(move |(_, step)| step.depends_on(id))
    }

    // Returns (value, id of clause) when this literal's value is known due to some existing clause.
    // No id is returned if this literal is "expr = expr".
    fn evaluate_literal(&self, literal: &Literal) -> Option<(bool, Option<usize>)> {
        literal.validate_type();
        if literal.left == literal.right {
            return Some((literal.positive, None));
        }
        match self.literal_tree.find_generalization(&literal) {
            Some((positive, id)) => Some((positive, Some(id))),
            None => None,
        }
    }

    // Simplifies the clause based on both structural rules and the active set.
    // If the result is redundant given what's already known, return None.
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
                        new_rules.push(id);
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
        let mut new_truthiness = step.truthiness;
        for i in &new_rules {
            let rewrite_step = self.get_step(*i);
            new_truthiness = new_truthiness.combine(rewrite_step.truthiness);
        }
        Some(step.simplify(simplified_clause, new_rules, new_truthiness))
    }

    // Add all the rewrite targets for a given literal.
    fn add_rewrite_targets(&mut self, step_index: usize, literal: &Literal) {
        for (forwards, from, _) in literal.both_term_pairs() {
            for (path, subterm) in from.rewritable_subterms() {
                self.rewrite_targets.insert(
                    subterm,
                    RewriteTarget {
                        step_index,
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

    // Indexes a clause so that it becomes available for future proof step generation.
    fn insert(&mut self, step: ProofStep, id: usize) {
        let clause = &step.clause;
        let step_index = self.steps.len();

        // Add resolution targets for the new clause.
        // Any literal can be used for resolution.
        for (i, literal) in clause.literals.iter().enumerate() {
            self.add_resolution_targets(step_index, i, literal);
        }

        // Add rewrite targets for the new clause.
        // Only single-literal clauses can be used for rewriting.
        if clause.literals.len() == 1 {
            let literal = &clause.literals[0];

            self.add_rewrite_targets(step_index, literal);

            // When a literal is created via rewrite, we don't need to add it as a rewrite pattern.
            // At some point we might want to do it anyway.
            // Ie, if we prove that a = b after five steps of rewrites, we might want to use that
            // to simplify everything, without going through the intermediate steps.
            // But, for now, we just don't do it.
            if literal.positive && !step.rule.is_rewrite() {
                self.rewrite_patterns.insert_literal(
                    step_index,
                    step.truthiness == Truthiness::Factual,
                    literal,
                );
            }

            self.literal_tree.insert(&clause.literals[0], id);
        } else {
            self.long_clauses.insert(clause.clone());
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

        if activated_step.clause.len() == 1 {
            if activated_step.clause.literals[0].positive {
                // The activated step could be used as a rewrite pattern.
                for step in self.activate_rewrite_pattern(activated_id, &activated_step) {
                    generated_steps.push(step);
                }
            }

            // The activated step could be rewritten itself.
            for step in self.activate_rewrite_target(activated_id, &activated_step) {
                generated_steps.push(step);
            }
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
    fn test_activate_rewrite_pattern() {
        // Create an active set that knows c0(c3) = c2
        let mut set = ActiveSet::new();
        let mut step = ProofStep::mock("c0(c3) = c2");
        step.truthiness = Truthiness::Hypothetical;
        set.insert(step, 0);

        // We should be able replace c1 with c3 in "c0(c3) = c2"
        let pattern_step = ProofStep::mock("c1 = c3");
        let result = set.activate_rewrite_pattern(0, &pattern_step);

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
        set.insert(step, 0);

        // We should be able to rewrite c0(c3) = c2 to get c0(c1) = c2
        let mut target_step = ProofStep::mock("c0(c3) = c2");
        target_step.truthiness = Truthiness::Hypothetical;
        let result = set.activate_rewrite_target(0, &target_step);

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
        let clause = Clause::parse("c0(x0, c0(x1, c1(x2))) != c0(c0(x2, x1), x0)");
        assert!(ActiveSet::equality_resolution(&clause).is_none());
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
