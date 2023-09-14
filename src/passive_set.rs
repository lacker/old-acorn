use std::cmp::Ordering;
use std::collections::BinaryHeap;

use crate::active_set::ProofStep;
use crate::clause::Clause;
use crate::proof::ClauseType;

// The PassiveSet stores a bunch of clauses.
// It does not assist in generating new clauses.
// So the PassiveSet is faster than the ActiveSet, but less powerful.
// The main operations of the passive set are adding new clauses, and
// picking the "most promising" clause to add to the active set.
pub struct PassiveSet {
    clauses: BinaryHeap<ClauseInfo>,
    num_adds: usize,
}

// The ClauseInfo contains a bunch of heuristic information about the clause.
#[derive(Debug, Eq, PartialEq)]
struct ClauseInfo {
    clause: Clause,
    clause_type: ClauseType,
    proof_step: ProofStep,
    atom_count: u32,

    // When the clause was inserted into the passive set.
    // This will never be equal for any two clauses, so we can use it as a tiebreaker.
    passive_order: usize,
}

impl Ord for ClauseInfo {
    // The heuristic used to decide which clause is the most promising.
    // The passive set is a "max heap", so we want the best clause to compare as the largest.
    fn cmp(&self, other: &ClauseInfo) -> Ordering {
        // Do facts, then negated goal, then others
        let by_type = self.clause_type.cmp(&other.clause_type);
        if by_type != Ordering::Equal {
            return by_type;
        }

        // Prefer clauses with fewer atoms
        let by_atom_count = other.atom_count.cmp(&self.atom_count);
        if by_atom_count != Ordering::Equal {
            return by_atom_count;
        }

        // Prefer clauses that were added earlier
        other.passive_order.cmp(&self.passive_order)
    }
}

impl PartialOrd for ClauseInfo {
    fn partial_cmp(&self, other: &ClauseInfo) -> Option<Ordering> {
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
