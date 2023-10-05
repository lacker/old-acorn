// This file contains the data structures that make up a proof, along with heuristics of how it is found.

use std::{cmp::Ordering, fmt};

use crate::clause::Clause;

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

    // The number of proof steps that this proof step depends on.
    // The size includes this proof step itself, but does not count assumptions and definitions.
    // So the size for any assumption or definition is zero.
    // This does not deduplicate among different branches, so it may be an overestimate.
    pub proof_size: u32,
}

impl ProofStep {
    pub fn assumption() -> ProofStep {
        ProofStep {
            rule: ProofRule::Assumption,
            activated: None,
            existing: None,
            proof_size: 0,
        }
    }

    pub fn definition() -> ProofStep {
        ProofStep {
            rule: ProofRule::Definition,
            activated: None,
            existing: None,
            proof_size: 0,
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

// The ClauseInfo contains a bunch of heuristic information about the clause.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ClauseInfo {
    pub clause: Clause,
    pub clause_type: ClauseType,

    // How this clause was generated.
    pub proof_step: ProofStep,

    // Cached for simplicity
    pub atom_count: u32,

    // When the clause was generated.
    pub generation_order: usize,
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

        if self.clause_type == ClauseType::Other {
            // Prefer clauses with fewer atoms
            let by_atom_count = other.atom_count.cmp(&self.atom_count);
            if by_atom_count != Ordering::Equal {
                return by_atom_count;
            }
        }

        // Prefer clauses that were added earlier
        other.generation_order.cmp(&self.generation_order)
    }
}

impl PartialOrd for ClauseInfo {
    fn partial_cmp(&self, other: &ClauseInfo) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for ClauseInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} atoms, {} proof size",
            self.atom_count, self.proof_step.proof_size
        )
    }
}

impl ClauseInfo {
    // Construct a ClauseInfo with fake heuristic data for testing
    pub fn mock(s: &str) -> ClauseInfo {
        let clause = Clause::parse(s);
        let atom_count = clause.atom_count();
        ClauseInfo {
            clause,
            clause_type: ClauseType::Other,
            proof_step: ProofStep::assumption(),
            atom_count,
            generation_order: 0,
        }
    }
}
