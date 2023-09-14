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

    fn add_helper(
        &mut self,
        clause: Clause,
        clause_type: ClauseType,
        proof_step: ProofStep,
        weight: u32,
    ) {
        self.clauses.push(ClauseInfo {
            clause,
            clause_type,
            proof_step,
            atom_count: weight,
            passive_order: self.num_adds,
        });
        self.num_adds += 1;
    }

    pub fn add_fact(&mut self, clause: Clause) {
        self.add_helper(clause, ClauseType::Fact, ProofStep::assumption(), 0);
        self.num_adds += 1;
    }

    pub fn add_negated_goal(&mut self, clause: Clause) {
        self.add_helper(clause, ClauseType::NegatedGoal, ProofStep::assumption(), 0);
    }

    pub fn add(&mut self, clause: Clause, clause_type: ClauseType, proof_step: ProofStep) {
        let weight = clause.atom_count();
        self.add_helper(clause, clause_type, proof_step, weight);
    }

    pub fn pop(&mut self) -> Option<(Clause, ClauseType, ProofStep)> {
        self.clauses
            .pop()
            .map(|pc| (pc.clause, pc.clause_type, pc.proof_step))
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
