// Include the generated burn model code.
// Beware that we have to avoid stepping on its names, which we don't know.
include!("../files/burn/model.rs");

use std::error::Error;

use burn::backend::ndarray::NdArrayDevice;
use burn::backend::NdArray;

use crate::features::Features;
use crate::scorer::Scorer;

// Aliases that choose our backend and device.
// B for Backend because the autogenerated file took Backend.
type B = NdArray;
type Device = NdArrayDevice;

// The BurnModel uses burn to load an onnx model and uses it to score feature vectors.
pub struct BurnModel {
    device: Device,
    model: Model<B>,
}

impl BurnModel {
    // The filename is figured out at compile time, so we don't have to do it here
    pub fn load() -> Result<Self, Box<dyn Error>> {
        let device = Device::default();
        let model = Model::<B>::from_embedded(&device);
        Ok(BurnModel { device, model })
    }
}

impl Scorer for BurnModel {
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>> {
        let floats = [features.to_floats()];
        let inputs = Tensor::<B, 2>::from_floats(floats, &self.device);
        let outputs = self.model.forward(inputs);
        let score = outputs.into_scalar();
        Ok(score)
    }
}
