#![allow(dead_code)]
use crate::acorn_type::{AcornType, FunctionType};
use crate::acorn_value::AcornValue;

pub struct Skolemizer {
    // Types of the skolem functions produced
    types: Vec<FunctionType>,
}

impl Skolemizer {
    pub fn new() -> Skolemizer {
        Skolemizer { types: vec![] }
    }

    // The input should already have negations moved inwards.
    // The stack must be entirely universal quantifiers.
    pub fn skolemize(&mut self, stack: &Vec<AcornType>, value: AcornValue) -> AcornValue {
        match value {
            AcornValue::Lambda(_, _) => panic!("cannot skolemize a lambda"),
            _ => panic!("TODO"),
        }
    }
}
