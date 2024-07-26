use crate::proof_step::{ProofStep, Rule, Truthiness};

// Each proof step has a score, which encapsulates all heuristic judgments about
// the proof step.
// The better the score, the more we want to activate this proof step.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct Score {
    // Contradictions are the most important thing
    contradiction: bool,

    // Higher scores are preferred, using subsequent heuristics for tiebreaks.
    heuristic1: i32,
    heuristic2: i32,
    heuristic3: i32,

    // Whether this is a basic step. Basic steps can be stated without proof.
    pub basic: bool,
}

// Don't bother differentiating depth for score purposes after this point.
// Basic proofs ignore everything at max depth (and below).
const MAX_DEPTH: i32 = 3;

impl Score {
    // A scoring algorithm developed by hand.
    //
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
    pub fn manual(step: &ProofStep) -> Score {
        let contradiction = step.clause.is_impossible();

        let heuristic1 = -(step.depth as i32).max(-MAX_DEPTH);

        // Higher = more important, for the deterministic tier.
        let heuristic2 = match step.truthiness {
            Truthiness::Counterfactual => {
                if step.is_negated_goal() {
                    3
                } else {
                    1
                }
            }
            Truthiness::Hypothetical => {
                if let Rule::Assumption(_) = step.rule {
                    2
                } else {
                    1
                }
            }
            Truthiness::Factual => 4,
        };

        let mut heuristic3 = 0;
        heuristic3 -= step.clause.atom_count() as i32;
        heuristic3 -= 2 * step.proof_size as i32;
        if step.truthiness == Truthiness::Hypothetical {
            heuristic3 -= 3;
        }

        let basic = if contradiction {
            true
        } else {
            heuristic1 > -MAX_DEPTH
        };

        Score {
            contradiction,
            heuristic1,
            heuristic2,
            heuristic3,
            basic,
        }
    }
}
