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
    atom_count: u32,
    index: usize,
}

impl Ord for PrioritizedClause {
    fn cmp(&self, other: &PrioritizedClause) -> Ordering {
        let smart_priority = false;
        if smart_priority {
            // Shortest-first, then first-in-first-out
            other
                .atom_count
                .cmp(&self.atom_count)
                .then_with(|| other.index.cmp(&self.index))
        } else {
            // This is just "first in first out"
            other.index.cmp(&self.index)
        }
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
        let atom_count = clause.atom_count();
        self.clauses.push(PrioritizedClause {
            clause,
            atom_count,
            index: self.num_adds,
        });
        self.num_adds += 1;
    }

    pub fn pop(&mut self) -> Option<Clause> {
        self.clauses.pop().map(|pc| pc.clause)
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn map(&self, f: &mut impl FnMut(&Clause)) {
        for pc in &self.clauses {
            f(&pc.clause);
        }
    }
}
