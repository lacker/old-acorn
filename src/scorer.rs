use std::error::Error;

use crate::features::Features;
use crate::ort_model::OrtModel;

pub trait Scorer {
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>>;

    fn batch_score(&self, features: &[Features]) -> Result<Vec<f32>, Box<dyn Error>> {
        Ok(features.iter().map(|f| self.score(f).unwrap()).collect())
    }
}

const EXPERIMENT: bool = false;

pub fn default_scorer() -> Box<dyn Scorer + Send + Sync> {
    if EXPERIMENT {
        Box::new(OrtModel::load(true).unwrap())
    } else {
        Box::new(HandcraftedScorer)
    }
}

// Developed before I had any other framework for policies.
pub struct HandcraftedScorer;

impl Scorer for HandcraftedScorer {
    // The first heuristic is like negative depth.
    // It's bounded at -2 so after that we don't use depth for scoring any more.
    //
    // The second heuristic is an ordering by the type
    //
    //   Global facts, both explicit and deductions
    //   The negated goal
    //   Explicit hypotheses
    //   Local deductions
    //
    // The third heuristic is a combination of a bunch of stuff, roughly to discourage
    // complexity.
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>> {
        // The first heuristic is 0 for zero depth, -1 for depth 1, -2 for anything deeper.
        let heuristic1 = match features.depth {
            0 => 0,
            1 => -1,
            _ => -2,
        };

        // The second heuristic is based on truthiness.
        // Higher = more important.
        let heuristic2 = if features.is_counterfactual {
            if features.is_negated_goal {
                3
            } else {
                1
            }
        } else if features.is_hypothetical {
            if features.is_assumption {
                2
            } else {
                1
            }
        } else {
            4
        };

        // The third heuristic is a hodgepodge.
        let mut heuristic3 = 0;
        heuristic3 -= features.atom_count;
        heuristic3 -= 2 * features.proof_size;
        if features.is_hypothetical {
            heuristic3 -= 3;
        }

        // Essentially lexicographical
        let score =
            1000000.0 * (heuristic1 as f32) + 100000.0 * (heuristic2 as f32) + heuristic3 as f32;
        Ok(score)
    }
}

pub struct DepthFirstScorer;

impl Scorer for DepthFirstScorer {
    // Always scoring zero will make it do depth-first search.
    fn score(&self, _features: &Features) -> Result<f32, Box<dyn Error>> {
        Ok(0.0)
    }
}

#[cfg(test)]
mod tests {
    use crate::burn_model::BurnModel;
    use crate::proof_step::ProofStep;

    use super::*;

    #[test]
    fn test_loading_models() {
        let step = ProofStep::mock("c0(c3) = c2");
        let features = Features::new(&step);

        // First ort
        let ort_model = OrtModel::load(true).unwrap();
        let ort_score = ort_model.score(&features).unwrap();
        assert!(ort_score.is_finite());

        // Then burn
        let burn_model = BurnModel::load().unwrap();
        let burn_score = burn_model.score(&features).unwrap();
        assert!(burn_score.is_finite());

        // Then check they match
        assert!((ort_score - burn_score).abs() < 1e-6);
    }
}
