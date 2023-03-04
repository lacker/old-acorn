#![allow(dead_code)]
use crate::acorn_type::FunctionType;

pub struct Skolemizer {
    // Types of the skolem functions produced
    types: Vec<FunctionType>,
}

impl Skolemizer {
    pub fn new() -> Skolemizer {
        Skolemizer { types: vec![] }
    }

    // The input should already have negations moved inwards.
    pub fn skolemize(&mut self, value: AcornValue) -> AcornValue {
        panic!("TODO")
    }
}
