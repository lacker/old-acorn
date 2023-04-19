use std::cmp::Ordering;
use std::collections::BinaryHeap;

use crate::term::Clause;

// The PassiveSet stores a bunch of clauses.
// It does not assist in generating new clauses.
// So the PassiveSet is faster than the ActiveSet, but less powerful.
// The main operations of the passive set are adding new clauses, and
// picking the "most promising" clause to add to the active set.
pub struct PassiveSet {
    clauses: BinaryHeap<PrioritizedClause>,
    num_adds: usize,
}

#[derive(Debug, Eq, PartialEq)]
struct PrioritizedClause {
    clause: Clause,
    weights: (u32, u32),
    index: usize,
}

impl Ord for PrioritizedClause {
    // Higher comparisons get popped off the heap first.
    // So we want lower weights, tiebreaking by the clauses we
    // saw first.
    fn cmp(&self, other: &PrioritizedClause) -> Ordering {
        other
            .weights
            .cmp(&self.weights)
            .then_with(|| other.index.cmp(&self.index))
    }
}

impl PartialOrd for PrioritizedClause {
    fn partial_cmp(&self, other: &PrioritizedClause) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PassiveSet {
    pub fn new() -> PassiveSet {
        PassiveSet {
            clauses: BinaryHeap::new(),
            num_adds: 0,
        }
    }

    pub fn add(&mut self, clause: Clause) {
        let weights = clause.multi_weight();
        let index = self.num_adds;
        self.clauses.push(PrioritizedClause {
            clause,
            weights,
            index,
        });
        self.num_adds += 1;
    }

    pub fn pop(&mut self) -> Option<Clause> {
        self.clauses.pop().map(|pc| pc.clause)
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }
}
