use ordered_float::OrderedFloat;

use crate::features::Features;
use crate::scorer::Scorer;

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
    pub fn new(scorer: &dyn Scorer, features: &Features) -> Score {
        if features.is_contradiction {
            return Score {
                contradiction: true,
                usable_for_verification: true,
                score: OrderedFloat(0.0),
            };
        }
        let usable_for_verification = features.depth < 2;
        let score = scorer.score(features).unwrap();
        Score {
            contradiction: false,
            usable_for_verification,
            score: OrderedFloat(score),
        }
    }

    // Do a whole batch of scoring at once.
    pub fn batch(scorer: &dyn Scorer, features: &[Features]) -> Vec<Score> {
        let floats = scorer.score_batch(features).unwrap();
        features
            .iter()
            .zip(floats.iter())
            .map(|(f, &s)| Score {
                contradiction: f.is_contradiction,
                usable_for_verification: f.depth < 2 || f.is_contradiction,
                score: OrderedFloat(s),
            })
            .collect()
    }

    pub fn is_usable_for_verification(&self) -> bool {
        self.usable_for_verification
    }
}
