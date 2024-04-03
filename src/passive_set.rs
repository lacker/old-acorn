use std::collections::BinaryHeap;

use crate::proof_step::ProofStep;

// The PassiveSet stores a bunch of clauses.
// It does not assist in generating new clauses.
// So the PassiveSet is faster than the ActiveSet, but less powerful.
// The main operations of the passive set are adding new clauses, and
// picking the "most promising" clause to add to the active set.
// This is not stable, but it is deterministic.
pub struct PassiveSet {
    clauses: BinaryHeap<ProofStep>,
}

impl PassiveSet {
    pub fn new() -> PassiveSet {
        PassiveSet {
            clauses: BinaryHeap::new(),
        }
    }

    pub fn push(&mut self, step: ProofStep) {
        self.clauses.push(step);
    }

    pub fn pop(&mut self) -> Option<ProofStep> {
        self.clauses.pop()
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    // Finds the proof steps that are consequences of the given clause.
    // Sorts from best to worst, which is highest to lowest for ProofSteps.
    pub fn find_consequences<'a>(&'a self, id: usize) -> Vec<&'a ProofStep> {
        let mut answer = vec![];
        for step in &self.clauses {
            if step.depends_on(id) {
                answer.push(step);
            }
        }
        answer.sort();
        answer.reverse();
        answer
    }

    // Sort "highest" to "lowest" which is best to worst
    pub fn all_steps(&self) -> Vec<ProofStep> {
        let mut steps: Vec<ProofStep> = self.clauses.iter().cloned().collect();
        steps.sort();
        steps.reverse();
        steps
    }
}
