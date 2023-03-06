use crate::acorn_value::{AcornValue, Clause};
use crate::skolemizer::Skolemizer;

// The Engine handles normalizing propositions and proving them.
pub struct Engine {
    pub skolemizer: Skolemizer,

    pub clauses: Vec<Clause>,
}

impl Engine {
    pub fn new() -> Engine {
        Engine {
            skolemizer: Skolemizer::new(),
            clauses: vec![],
        }
    }

    // Normalizes the value and adds it to our clause list.
    pub fn add_value(&mut self, value: AcornValue) {
        let neg_in = value.move_negation_inwards(false);
        let skolemized = self.skolemizer.skolemize(&vec![], neg_in);
        panic!("TODO")
    }
}
