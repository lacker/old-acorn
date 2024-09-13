use crate::features::Features;
use crate::scorer::Scorer;

// The Model loads a model that was trained in Python and uses it to score feature vectors.
pub struct Model;

// We just support one hard-coded model.
const FILENAME: &str = "model-2024-09-13-09:55:03.onnx";

impl Model {
    pub fn new() -> Self {
        todo!();
    }
}

impl Scorer for Model {
    fn score(&self, features: &Features) -> f32 {
        todo!();
    }
}

#[cfg(test)]
mod tests {
    use crate::proof_step::ProofStep;

    use super::*;

    #[test]
    fn test_onnx_scoring() {
        let model = Model::new();
        let step = ProofStep::mock("c0(c3) = c2");
        let features = Features::new(&step);
        let score = model.score(&features);
        assert!(score.is_finite());
    }
}
