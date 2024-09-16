use std::error::Error;
use std::path::PathBuf;

use ndarray::{Axis, IxDyn};
use ort::{GraphOptimizationLevel, Session};

use crate::features::Features;
use crate::scorer::Scorer;

// The ScoringModel loads a model that was trained in Python and uses it to score feature vectors.
pub struct ScoringModel {
    // The ONNX model.
    session: Session,
}

// We just support one hard-coded model.
const FILENAME: &str = "model-2024-09-13-09:55:03.onnx";

impl ScoringModel {
    pub fn load() -> Result<Self, ort::Error> {
        let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        d.push("files");
        d.push(FILENAME);
        let session = Session::builder()?
            .with_optimization_level(GraphOptimizationLevel::Level3)?
            .commit_from_file(d)?;

        Ok(ScoringModel { session })
    }
}

impl Scorer for ScoringModel {
    // This assumes that the model is calculating a probability of the positive class,
    // where the positive class is a step that was actually taken in a proof.
    // There's a lot of unwrapping - it would be nice to handle errors more gracefully.
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>> {
        let array = features.to_array().insert_axis(Axis(0));
        let inputs = ort::inputs![array]?;
        let outputs = self.session.run(inputs)?;
        let extracted = outputs[0].try_extract_tensor::<f32>()?;
        let ix = IxDyn(&[0, 0]);
        if let Some(score) = extracted.get(ix) {
            Ok(*score)
        } else {
            Err("No score at [0, 0]. Maybe the model is the wrong shape?".into())
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::proof_step::ProofStep;

    use super::*;

    #[test]
    fn test_onnx_scoring() {
        let model = ScoringModel::load().unwrap();
        let step = ProofStep::mock("c0(c3) = c2");
        let features = Features::new(&step);
        let score = model.score(&features).unwrap();
        assert!(score.is_finite());
    }
}
