// Include the generated burn model code.
// Beware that we have to avoid stepping on its names, which we don't know.
include!("../files/burn/model.rs");

use std::error::Error;

use burn::backend::ndarray::NdArrayDevice;
use burn::backend::NdArray;

use crate::common;
use crate::features::Features;
use crate::scorer::Scorer;

// Aliases that choose our backend and device.
type BackendAlias = NdArray;
type DeviceAlias = NdArrayDevice;

// The BurnModel uses burn to load an onnx model and uses it to score feature vectors.
pub struct BurnModel {
    device: DeviceAlias,
    model: Model<BackendAlias>,
}

impl BurnModel {
    // The filename is figured out at compile time, so we don't have to do it here
    pub fn load() -> Result<Self, Box<dyn Error>> {
        let device = DeviceAlias::default();
        let weights_file = common::files_dir().join("burn").join("model.mpk");
        let model = Model::<BackendAlias>::from_file(&weights_file.to_str().unwrap(), &device);
        Ok(BurnModel { device, model })
    }
}

impl Scorer for BurnModel {
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>> {
        todo!();
    }
}
