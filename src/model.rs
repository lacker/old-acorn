use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Once;

use ndarray::{Axis, IxDyn};
use ort::{CPUExecutionProvider, GraphOptimizationLevel, Session};

use crate::features::Features;
use crate::scorer::Scorer;

// The ScoringModel loads a model that was trained in Python and uses it to score feature vectors.
pub struct ScoringModel {
    // The ONNX model.
    session: Session,
}

static ORT_INIT: Once = Once::new();

impl ScoringModel {
    // Loads a model from a specific file.
    pub fn load_file(p: impl AsRef<Path>) -> Result<Self, Box<dyn Error>> {
        ORT_INIT.call_once(|| {
            ort::init()
                .with_execution_providers([CPUExecutionProvider::default()
                    .build()
                    .error_on_failure()])
                .commit()
                .unwrap();
        });

        let session = Session::builder()?
            .with_optimization_level(GraphOptimizationLevel::Disable)?
            .commit_from_file(p)?;
        Ok(ScoringModel { session })
    }

    // Loads the most recent model.
    pub fn load(verbose: bool) -> Result<Self, Box<dyn Error>> {
        let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        d.push("files");

        // Naming is by timestamp, so the largest is the most recent
        let filename = match fs::read_dir(d.clone())?
            .filter_map(|entry| entry.ok())
            .filter_map(|entry| {
                let path = entry.path();
                if let Some(filename) = path.file_name()?.to_str() {
                    if filename.starts_with("model-") && filename.ends_with(".onnx") {
                        return Some(filename.to_string());
                    }
                }
                None
            })
            .max()
        {
            Some(filename) => filename,
            None => return Err("No model files found".into()),
        };

        if verbose {
            println!("Loading model from {}", filename);
        }

        ScoringModel::load_file(d.join(filename))
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
        let model = ScoringModel::load(true).unwrap();
        let step = ProofStep::mock("c0(c3) = c2");
        let features = Features::new(&step);
        let score = model.score(&features).unwrap();
        assert!(score.is_finite());
    }
}
