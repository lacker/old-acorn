use std::collections::BinaryHeap;

use crate::clause::Clause;
use crate::proof_step::{ProofStep, Truthiness};

// The PassiveSet stores a bunch of clauses.
// It does not assist in generating new clauses.
// So the PassiveSet is faster than the ActiveSet, but less powerful.
// The main operations of the passive set are adding new clauses, and
// picking the "most promising" clause to add to the active set.
pub struct PassiveSet {
    clauses: BinaryHeap<ProofStep>,
}

impl PassiveSet {
    pub fn new() -> PassiveSet {
        PassiveSet {
            clauses: BinaryHeap::new(),
        }
    }

    pub fn push(&mut self, info: ProofStep) {
        self.clauses.push(info);
    }

    pub fn pop(&mut self) -> Option<ProofStep> {
        self.clauses.pop()
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn iter_clauses(&self) -> impl Iterator<Item = &Clause> {
        self.clauses.iter().map(|pc| &pc.output)
    }

    // Sort "highest" to "lowest" which is best to worst
    pub fn all_clause_info(&self) -> Vec<ProofStep> {
        let mut infos: Vec<ProofStep> = self.clauses.iter().cloned().collect();
        infos.sort();
        infos.reverse();
        infos
    }

    pub fn next_clause_type(&self) -> Option<Truthiness> {
        self.clauses.peek().map(|pc| pc.truthiness)
    }
}
