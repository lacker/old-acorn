use crate::features::Features;

// Data tracked from a build to use for training a
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
}
