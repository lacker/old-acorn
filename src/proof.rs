// This file contains the data structures that make up a proof, along with heuristics of how it is found.

use std::cmp::Ordering;

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
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

// The rules that can generate new clauses.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ProofRule {
    Assumption,
    Definition,
    ActivatingParamodulator,
    ActivatingResolver,
    EqualityFactoring,
    EqualityResolution,
}

// The ProofStep records how one clause was generated from other clauses.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct ProofStep {
    pub rule: ProofRule,

    // The clause index in the active set that was activated to generate this clause.
    pub activated: Option<usize>,

    // The index of the already-activated clause in the active set we used, if there was any.
    pub existing: Option<usize>,
}

impl ProofStep {
    pub fn assumption() -> ProofStep {
        ProofStep {
            rule: ProofRule::Assumption,
            activated: None,
            existing: None,
        }
    }

    pub fn definition() -> ProofStep {
        ProofStep {
            rule: ProofRule::Definition,
            activated: None,
            existing: None,
        }
    }

    pub fn indices(&self) -> impl Iterator<Item = &usize> {
        self.activated.iter().chain(self.existing.iter())
    }

    pub fn is_assumption(&self) -> bool {
        match self.rule {
            ProofRule::Assumption => true,
            _ => false,
        }
    }
}
