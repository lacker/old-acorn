use crate::features::Features;
use crate::scorer::Scorer;

pub struct Model;

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
