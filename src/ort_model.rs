use std::error::Error;
use std::path::Path;
use std::sync::Once;

use ndarray::{Axis, IxDyn};
use ort::{CPUExecutionProvider, GraphOptimizationLevel, Session};

use crate::common;
use crate::features::Features;
use crate::scorer::Scorer;

// The OrtModel uses ort to load an onnx model and uses it to score feature vectors.
pub struct OrtModel {
    // The ONNX model.
    session: Session,
}

static ORT_INIT: Once = Once::new();

impl OrtModel {
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
            .with_optimization_level(GraphOptimizationLevel::Level3)?
            .commit_from_file(p)?;
        Ok(OrtModel { session })
    }

    // Loads the most recent model.
    pub fn load(verbose: bool) -> Result<Self, Box<dyn Error>> {
        let filename = common::most_recent_onnx_model()?;
        if verbose {
            println!("Loading model from {}", filename.display());
        }
        OrtModel::load_file(filename)
    }
}

impl Scorer for OrtModel {
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

    fn batch_score(&self, features: &[Features]) -> Result<Vec<f32>, Box<dyn Error>> {
        Ok(features.iter().map(|f| self.score(f).unwrap()).collect())
    }
}
