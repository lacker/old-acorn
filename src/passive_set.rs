use std::collections::BTreeSet;

use crate::clause::Clause;
use crate::fingerprint::FingerprintSpecializer;
use crate::literal::Literal;
use crate::policy::{ManualPolicy, Score};
use crate::proof_step::ProofStep;
use crate::specializer::Specializer;
use crate::term::Term;

// The PassiveSet stores a bunch of clauses.
// A clause in the passive set can be activated, and it can be simplified, but to do
// anything more complicated it needs to be activated first.
pub struct PassiveSet {
    // Stores clauses in the passive set, along with their score.
    // We never shrink this vector, we just replace its entries with None.
    // The index into clauses acts like an id, but that id doesn't mean anything outside of the
    // PassiveSet.
    clauses: Vec<Option<(ProofStep, Score)>>,

    // Stores (score, clause id).
    // The queue lets us pick the highest-scoring clause to activate next.
    queue: BTreeSet<(Score, usize)>,

    // Stores (clause id, literal index) for each literal in each passive clause.
    // We currently don't clean this up by removing old clause ids, so when we retrieve from
    // it we need to check that the clause is still in the passive set.
    literals: FingerprintSpecializer<(usize, usize)>,
}

// Whether (left1, right2) can be specialized to get (left2, right2).
// Only tries this direction.
// Terms do not have to have variables normalized.
fn pair_specializes(left1: &Term, right1: &Term, left2: &Term, right2: &Term) -> bool {
    let mut s = Specializer::new();
    s.match_terms(left1, left2) && s.match_terms(right1, right2)
}

// Tries both directions
fn pair_specializes_either_way(left: &Term, right: &Term, literal: &Literal) -> bool {
    if left.term_type != literal.left.term_type {
        return false;
    }
    if pair_specializes(left, right, &literal.left, &literal.right) {
        return true;
    }
    pair_specializes(left, right, &literal.right, &literal.left)
}

// Makes a new clause by simplifying a bunch of literals with respect to a given literal.
// left and right do not have to have variables normalized.
// We already know literals[index] is a specialization of the given literal.
// Returns None if the clause is tautologically implied by the literal we are simplifying with.
fn make_simplified(
    left: &Term,
    right: &Term,
    positive: bool,
    index: usize,
    literals: Vec<Literal>,
) -> Option<Clause> {
    if literals[index].positive == positive {
        return None;
    }
    let mut new_literals = vec![];
    for (i, literal) in literals.into_iter().enumerate() {
        if i == index {
            continue;
        }
        if pair_specializes_either_way(left, right, &literal) {
            if literal.positive == positive {
                // The whole clause is implied by the literal we are simplifying with.
                return None;
            }
            // This specific literal is unsatisfiable.
            continue;
        }
        new_literals.push(literal);
    }
    Some(Clause::new(new_literals))
}

impl PassiveSet {
    pub fn new() -> PassiveSet {
        PassiveSet {
            clauses: vec![],
            queue: BTreeSet::new(),
            literals: FingerprintSpecializer::new(),
        }
    }

    pub fn push(&mut self, step: ProofStep) {
        let policy = ManualPolicy::new();
        let score = policy.score(
            &step.clause,
            step.truthiness,
            &step.rule,
            step.proof_size,
            step.depth(),
        );
        let id = self.clauses.len();
        for (i, literal) in step.clause.literals.iter().enumerate() {
            self.literals.insert(literal, (id, i));
        }
        self.clauses.push(Some((step, score)));
        self.queue.insert((score, id));
    }

    pub fn pop(&mut self) -> Option<ProofStep> {
        // Remove the largest entry from queue
        let (_, id) = self.queue.pop_last()?;
        match self.clauses[id].take() {
            Some((step, _)) => Some(step),
            None => panic!("Queue and clauses are out of sync"),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    // Whether we have more basic clauses to process.
    pub fn has_basic(&self) -> bool {
        match self.queue.last() {
            None => false,
            Some((score, _)) => score.basic,
        }
    }

    // Checks just the left->right direction for simplification.
    fn simplify_one_direction(
        &mut self,
        activated_id: usize,
        activated_step: &ProofStep,
        left: &Term,
        right: &Term,
        positive: bool,
    ) {
        let mut new_steps = vec![];
        for &(clause_id, literal_index) in self.literals.find_specializing(left, right) {
            let step = match &self.clauses[clause_id] {
                Some((step, _)) => step,
                None => {
                    // The clause was already removed, so this is a dead reference.
                    // Maybe we could more actively clean these up.
                    continue;
                }
            };

            let literal = &step.clause.literals[literal_index];
            let literal_positive = literal.positive;

            // We've only checked fingerprints. We need to check if they actually match.
            if !pair_specializes(left, right, &literal.left, &literal.right) {
                continue;
            }

            if step.rule.is_assumption() && positive == literal_positive {
                // This assumption is redundant, implied by an existing clause.
                // But, let's keep it, because we might use it for rewrite inspiration.
                continue;
            }

            // It matches. So we're definitely removing the existing clause.
            let (mut step, score) = self.clauses[clause_id].take().unwrap();
            self.queue.remove(&(score, clause_id));

            if positive == literal_positive {
                // The whole passive clause is implied by the activated clause.
                // So it's just redundant. We can forget about it.
                continue;
            }
            let new_clause = match make_simplified(
                left,
                right,
                positive,
                literal_index,
                std::mem::take(&mut step.clause.literals),
            ) {
                Some(clause) => clause,
                None => continue,
            };
            let new_truthiness = activated_step.truthiness.combine(step.truthiness);
            new_steps.push(step.new_simplified(new_clause, vec![activated_id], new_truthiness));
        }
        for step in new_steps {
            self.push(step);
        }
    }

    // Called when we activate a new true literal.
    // Simplifies the passive set by removing literals that are now known to be true.
    // Checks both directions.
    pub fn simplify(&mut self, activated_id: usize, step: &ProofStep) {
        assert!(step.clause.literals.len() == 1);
        let literal = &step.clause.literals[0];
        self.simplify_one_direction(
            activated_id,
            &step,
            &literal.left,
            &literal.right,
            literal.positive,
        );
        if !literal.strict_kbo() {
            let (right, left) = literal.normalized_reversed();
            self.simplify_one_direction(activated_id, &step, &right, &left, literal.positive);
        }
    }

    // The number of clauses remaining in the passive set.
    pub fn len(&self) -> usize {
        self.queue.len()
    }

    // Iterates over the steps from highest-scoring to lowest-scoring.
    pub fn iter_steps(&self) -> impl Iterator<Item = &ProofStep> {
        self.queue
            .iter()
            .rev()
            .map(|(_, id)| match &self.clauses[*id] {
                Some((step, _)) => step,
                None => panic!("Queue and clauses are out of sync"),
            })
    }

    // Finds the proof steps that are consequences of the given clause.
    // Sorts from best to worst, which is highest to lowest for ProofSteps.
    pub fn find_consequences<'a>(&'a self, id: usize) -> Vec<&'a ProofStep> {
        self.iter_steps()
            .filter(|step| step.depends_on_active(id))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_passive_set_simplification() {
        let mut passive_set = PassiveSet::new();
        passive_set.push(ProofStep::mock("c0(c1) or c0(c2)"));
        // This should match *both* the literals in our existing clause
        passive_set.simplify(3, &ProofStep::mock("not c0(x0)"));
        let step = passive_set.pop().unwrap();
        assert_eq!(step.clause.to_string(), "<empty>");
    }
}
