use std::collections::BinaryHeap;

use crate::clause::Clause;
use crate::proof::{ClauseInfo, ClauseType, ProofStep};

// The PassiveSet stores a bunch of clauses.
// It does not assist in generating new clauses.
// So the PassiveSet is faster than the ActiveSet, but less powerful.
// The main operations of the passive set are adding new clauses, and
// picking the "most promising" clause to add to the active set.
pub struct PassiveSet {
    clauses: BinaryHeap<ClauseInfo>,
    num_adds: usize,
}

impl PassiveSet {
    pub fn new() -> PassiveSet {
        PassiveSet {
            clauses: BinaryHeap::new(),
            num_adds: 0,
        }
    }

    pub fn add(&mut self, clause: Clause, clause_type: ClauseType, proof_step: ProofStep) {
        let atom_count = clause.atom_count();
        self.clauses.push(ClauseInfo {
            clause,
            clause_type,
            proof_step,
            atom_count,
            generation_order: self.num_adds,
        });
        self.num_adds += 1;
    }

    pub fn add_fact(&mut self, clause: Clause) {
        self.add(clause, ClauseType::Fact, ProofStep::assumption());
        self.num_adds += 1;
    }

    pub fn add_negated_goal(&mut self, clause: Clause) {
        self.add(clause, ClauseType::NegatedGoal, ProofStep::assumption());
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
