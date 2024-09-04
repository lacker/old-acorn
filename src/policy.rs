use crate::clause::Clause;
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
    pub usable_for_verification: bool,

    // Higher scores are preferred, using subsequent heuristics for tiebreaks.
    heuristic1: i32,
    heuristic2: i32,
    heuristic3: i32,
}

// We want the definition of "usable for verification" to be the same for different policies.
fn usable_for_verification(depth: u32) -> bool {
    depth < 2
}

pub struct ManualPolicy {}

impl ManualPolicy {
    pub fn new() -> ManualPolicy {
        ManualPolicy {}
    }

    // The first heuristic is the negative depth.
    // It's bounded at -MAX_DEPTH so after that we don't use depth for scoring any more.
    //
    // The second heuristic of the score is an ordering by the type
    //
    //   Global facts, both explicit and deductions
    //   The negated goal
    //   Explicit hypotheses
    //   Local deductions
    //
    // The third element of the score is a combination of a bunch of stuff, roughly to discourage
    // complexity.
    pub fn score(
        &self,
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
                heuristic1: 0,
                heuristic2: 0,
                heuristic3: 0,
            };
        }

        // The first heuristic is 0 for zero depth, -1 for depth 1, -2 for anything deeper.
        let heuristic1 = match depth {
            0 => 0,
            1 => -1,
            _ => -2,
        };

        // The second heuristic is based on truthiness.
        // Higher = more important.
        let heuristic2 = match truthiness {
            Truthiness::Counterfactual => {
                if rule.is_negated_goal() {
                    3
                } else {
                    1
                }
            }
            Truthiness::Hypothetical => {
                if let Rule::Assumption(_) = rule {
                    2
                } else {
                    1
                }
            }
            Truthiness::Factual => 4,
        };

        // The third heuristic is a hodgepodge.
        let mut heuristic3 = 0;
        heuristic3 -= clause.atom_count() as i32;
        heuristic3 -= 2 * proof_size as i32;
        if truthiness == Truthiness::Hypothetical {
            heuristic3 -= 3;
        }

        Score {
            contradiction: false,
            usable_for_verification: usable_for_verification(depth),
            heuristic1,
            heuristic2,
            heuristic3,
        }
    }
}
