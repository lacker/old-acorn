use crate::acorn_value::AcornValue;
use crate::proof_step::Truthiness;
use crate::proposition::{Proposition, Source};

// A fact is a proposition that we already know to be true.
#[derive(Debug)]
pub struct Fact {
    pub value: AcornValue,
    pub source: Source,
    pub truthiness: Truthiness,
}

impl Fact {
    pub fn new(proposition: Proposition, truthiness: Truthiness) -> Fact {
        Fact {
            value: proposition.value,
            source: proposition.source,
            truthiness,
        }
    }

    pub fn local(&self) -> bool {
        self.truthiness != Truthiness::Factual
    }
}
