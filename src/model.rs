use std::path::PathBuf;

use ndarray::Array1;
use ort::{Error, GraphOptimizationLevel, Session};

use crate::features::Features;
use crate::scorer::Scorer;

// The Model loads a model that was trained in Python and uses it to score feature vectors.
pub struct Model {
    // The ONNX .
    session: Session,
}

// We just support one hard-coded model.
const FILENAME: &str = "model-2024-09-13-09:55:03.onnx";

impl Model {
    pub fn load() -> Result<Self, Error> {
        let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        d.push("files");
        d.push(FILENAME);
        let session = Session::builder()?
            .with_optimization_level(GraphOptimizationLevel::Level3)?
            .commit_from_file(d)?;

        Ok(Model { session })
    }
}

impl Scorer for Model {
    fn score(&self, features: &Features) -> f32 {
        let arr: Array1<f32> = Array1::from_vec(vec![0.0, 0.0]);
        let inputs = ort::inputs![arr];

        todo!();
    }
}

#[cfg(test)]
mod tests {
    use crate::proof_step::ProofStep;

    use super::*;

    #[test]
    fn test_onnx_scoring() {
        let model = Model::load().unwrap();
        let step = ProofStep::mock("c0(c3) = c2");
        let features = Features::new(&step);
        let score = model.score(&features);
        assert!(score.is_finite());
    }
}
