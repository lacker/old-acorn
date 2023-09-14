use std::collections::BinaryHeap;

use crate::clause::Clause;
use crate::proof::{ClauseInfo, ClauseType};

// The PassiveSet stores a bunch of clauses.
// It does not assist in generating new clauses.
// So the PassiveSet is faster than the ActiveSet, but less powerful.
// The main operations of the passive set are adding new clauses, and
// picking the "most promising" clause to add to the active set.
pub struct PassiveSet {
    clauses: BinaryHeap<ClauseInfo>,
}

impl PassiveSet {
    pub fn new() -> PassiveSet {
        PassiveSet {
            clauses: BinaryHeap::new(),
        }
    }

    pub fn push(&mut self, info: ClauseInfo) {
        self.clauses.push(info);
    }

    pub fn pop(&mut self) -> Option<ClauseInfo> {
        self.clauses.pop()
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn iter_clauses(&self) -> impl Iterator<Item = &Clause> {
        self.clauses.iter().map(|pc| &pc.clause)
    }

    pub fn next_clause_type(&self) -> Option<ClauseType> {
        self.clauses.peek().map(|pc| pc.clause_type)
    }
}
