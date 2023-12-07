// ClauseInfo contains information about a Clause that we use for both heuristically guiding proof
// search and satisfying human curiosity.

use std::{cmp::Ordering, fmt};

use crate::clause::Clause;

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ClauseType {
    // The facts include both the normalized facts the prover was initialized with, and any
    // deduction that comes from other facts.
    // In general, facts should be true. If not, there's an inconsistency.
    Fact,

    // The negated goal clauses come directly from the negated goal.
    // Our strategy is to add the negated goal then find a contradiction.
    // Typically, a negated goal is false. If not, it could either be an unprovable goal,
    // or a goal that has been normalized into multiple contradictory clauses.
    NegatedGoal,

    // Impure clauses is anything generated from other clauses that aren't all facts.
    // An impure clause might be true or it might be false.
    Impure,
}

impl ClauseType {
    // Highest priority should be processed first
    fn priority(&self) -> u8 {
        match self {
            ClauseType::Fact => 2,
            ClauseType::NegatedGoal => 1,
            ClauseType::Impure => 0,
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    pub rule: ProofRule,

    // The clause index in the active set that was activated to generate this clause.
    pub activated: Option<usize>,

    // The index of the already-activated clause in the active set we used, if there was any.
    pub existing: Option<usize>,

    // The clauses that we used for rewrites.
    pub rewrites: Vec<usize>,

    // The number of proof steps that this proof step depends on.
    // The size includes this proof step itself, but does not count assumptions and definitions.
    // So the size for any assumption or definition is zero.
    // This does not deduplicate among different branches, so it may be an overestimate.
    // This also ignores rewrites, which may or may not be the ideal behavior.
    pub proof_size: u32,
}

impl ProofStep {
    pub fn assumption() -> ProofStep {
        ProofStep {
            rule: ProofRule::Assumption,
            activated: None,
            existing: None,
            rewrites: vec![],
            proof_size: 0,
        }
    }

    pub fn definition() -> ProofStep {
        ProofStep {
            rule: ProofRule::Definition,
            activated: None,
            existing: None,
            rewrites: vec![],
            proof_size: 0,
        }
    }

    pub fn indices(&self) -> impl Iterator<Item = &usize> {
        self.activated
            .iter()
            .chain(self.existing.iter())
            .chain(self.rewrites.iter())
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

    // The order in which this ClauseInfo was created.
    // This is different from the order in which the ClauseInfo was activated.
    pub generation_ordinal: usize,
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

        if self.clause_type == ClauseType::Impure {
            // Use the simplicity heuristic
            let by_simplicity = other.simplicity().cmp(&self.simplicity());
            if by_simplicity != Ordering::Equal {
                return by_simplicity;
            }
        }

        // Prefer clauses that were added earlier
        other.generation_ordinal.cmp(&self.generation_ordinal)
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
    pub fn new(
        clause: Clause,
        clause_type: ClauseType,
        proof_step: ProofStep,
        generation_ordinal: usize,
    ) -> ClauseInfo {
        let atom_count = clause.atom_count();
        ClauseInfo {
            clause,
            clause_type,
            proof_step,
            atom_count,
            generation_ordinal,
        }
    }

    // Construct a ClauseInfo for one of the facts from the initial set of facts.
    pub fn new_initial_fact(clause: Clause, generation_ordinal: usize) -> ClauseInfo {
        ClauseInfo::new(
            clause,
            ClauseType::Fact,
            ProofStep::assumption(),
            generation_ordinal,
        )
    }

    // Construct a ClauseInfo for the negated goal that we are trying to prove.
    pub fn new_negated_goal(clause: Clause, generation_ordinal: usize) -> ClauseInfo {
        ClauseInfo::new(
            clause,
            ClauseType::NegatedGoal,
            ProofStep::assumption(),
            generation_ordinal,
        )
    }

    // Construct a ClauseInfo with fake heuristic data for testing
    pub fn mock(s: &str) -> ClauseInfo {
        let clause = Clause::parse(s);

        ClauseInfo::new(clause, ClauseType::Impure, ProofStep::assumption(), 0)
    }

    // A heuristic for how simple this clause is.
    // The lower the simplicity, the more likely we are to select it.
    fn simplicity(&self) -> u32 {
        self.atom_count + self.proof_step.proof_size
    }

    pub fn proof_size(&self) -> u32 {
        self.proof_step.proof_size
    }

    // The ids of the other clauses that this clause depends on.
    pub fn dependencies(&self) -> impl Iterator<Item = &usize> {
        self.proof_step.indices()
    }

    // Whether this is the last step of the proof
    pub fn finishes_proof(&self) -> bool {
        self.clause.is_impossible()
    }

    // A heuristic for whether this clause is so bad, it should be rejected immediately.
    pub fn heuristic_reject(&self) -> bool {
        self.clause_type == ClauseType::Fact && self.proof_size() > 2
    }
}
