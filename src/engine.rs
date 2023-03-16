use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::normalizer::Normalizer;
use crate::term::Clause;

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

        let new_clauses = self.normalizer.normalize(proposition);
        for clause in new_clauses {
            println!("adding clause: {:?}", clause);
            self.clauses.push(clause);
        }
    }
}
