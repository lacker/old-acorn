use ordered_float::OrderedFloat;

use crate::clause::Clause;
use crate::policy::ManualPolicy;
use crate::proof_step::{Rule, Truthiness};

// Each proof step has a score, which encapsulates all heuristic judgments about
// the proof step.
// The better the score, the more we want to activate this proof step.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct Score {
    // Contradictions are the most important thing
    contradiction: bool,

    // Whether this step can be used during verification.
    // Verification steps should always be activated before non-verification steps.
    // Otherwise, we might discover a proof using non-verification steps, and then be
    // unsure whether the proof is simple enough to pass verification or not.
    usable_for_verification: bool,

    // Higher scores are preferred.
    score: OrderedFloat<f32>,
}

impl Score {
    // The logic here is logic that we want to use regardless of the policy.
    pub fn new(
        policy: &ManualPolicy,
        clause: &Clause,
        truthiness: Truthiness,
        rule: &Rule,
        proof_size: u32,
        depth: u32,
    ) -> Score {
        if clause.is_impossible() {
            return Score {
                contradiction: true,
                usable_for_verification: true,
                score: OrderedFloat(0.0),
            };
        }
        let usable_for_verification = depth < 2;
        let score = policy.old_score(clause, truthiness, rule, proof_size, depth);
        Score {
            contradiction: false,
            usable_for_verification,
            score: OrderedFloat(score),
        }
    }

    pub fn is_usable_for_verification(&self) -> bool {
        self.usable_for_verification
    }
}
