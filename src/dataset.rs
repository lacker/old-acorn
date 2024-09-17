use std::fs::File;

use chrono::Local;
use ndarray::Array1;
use ndarray_npy::NpzWriter;

use crate::common;
use crate::features::Features;

// Data tracked from a build to use for training
pub struct Dataset {
    pub features: Vec<Features>,
    pub labels: Vec<bool>,
}

impl Dataset {
    pub fn new() -> Self {
        Dataset {
            features: vec![],
            labels: vec![],
        }
    }

    pub fn add(&mut self, features: Features, label: bool) {
        self.features.push(features);
        self.labels.push(label);
    }

    // This doesn't mess with the filename, but it would make sense to add npz.
    pub fn save_with_name(
        &self,
        relative_filename: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // Always save to the logs directory
        let mut d = common::files_dir();
        d.push("datasets");
        d.push(relative_filename);
        let file = File::create(d)?;
        let mut npz = NpzWriter::new(file);
        let features = Features::to_array2(&self.features);
        let labels = Array1::from(self.labels.clone());
        npz.add_array("features", &features)?;
        npz.add_array("labels", &labels)?;
        npz.finish()?;
        Ok(())
    }

    // Pick a default name and die on errors.
    pub fn save(&self) {
        let now = Local::now();
        let filename = now.format("dataset-%Y-%m-%d-%H:%M:%S.npz").to_string();
        println!(
            "Saving dataset with {} items to {}",
            self.features.len(),
            filename
        );
        self.save_with_name(&filename).unwrap();
    }
}
