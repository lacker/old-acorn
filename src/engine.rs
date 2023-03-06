use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, Clause};
use crate::normalizer::Normalizer;

// The Engine handles normalizing propositions and proving them.
pub struct Engine {
    pub normalizer: Normalizer,

    pub clauses: Vec<Clause>,
}

impl Engine {
    pub fn new() -> Engine {
        Engine {
            normalizer: Normalizer::new(),
            clauses: vec![],
        }
    }

    // Normalizes the proposition and adds it to our clause list.
    pub fn add_proposition(&mut self, proposition: AcornValue) {
        assert_eq!(proposition.get_type(), AcornType::Bool);

        let expanded = proposition.expand_lambdas(0);
        let neg_in = expanded.move_negation_inwards(false);
        let skolemized = self.normalizer.skolemize(&vec![], neg_in);
        panic!("TODO")
    }
}
