use std::cmp::Ordering;
use std::collections::BinaryHeap;

use crate::active_set::ProofStep;
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
pub enum ClauseType {
    Fact,
    NegatedGoal,
    Other,
}

impl ClauseType {
    // Highest priority should be processed first
    fn priority(&self) -> u8 {
        match self {
            ClauseType::Fact => 2,
            ClauseType::NegatedGoal => 1,
            ClauseType::Other => 0,
        }
    }
}

impl Ord for ClauseType {
    fn cmp(&self, other: &ClauseType) -> Ordering {
        self.priority().cmp(&other.priority())
    }
}

impl PartialOrd for ClauseType {
    fn partial_cmp(&self, other: &ClauseType) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Eq, PartialEq)]
struct PrioritizedClause {
    clause: Clause,
    clause_type: ClauseType,
    proof_step: ProofStep,
    weight: u32,
    index: usize,
}

impl Ord for PrioritizedClause {
    // This is a "max heap", so we want the most important clause to compare as the largest.
    fn cmp(&self, other: &PrioritizedClause) -> Ordering {
        // First type, then weight, then index (fifo)
        self.clause_type.cmp(&other.clause_type).then_with(|| {
            other
                .weight
                .cmp(&self.weight)
                .then_with(|| other.index.cmp(&self.index))
        })
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

    fn add_helper(
        &mut self,
        clause: Clause,
        clause_type: ClauseType,
        proof_step: ProofStep,
        weight: u32,
    ) {
        self.clauses.push(PrioritizedClause {
            clause,
            clause_type,
            proof_step,
            weight,
            index: self.num_adds,
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

    // Add an intermediate calculation, that is neither fact nor direct goal
    pub fn add(&mut self, clause: Clause, proof_step: ProofStep) {
        let weight = clause.atom_count();
        self.add_helper(clause, ClauseType::Other, proof_step, weight);
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
}
