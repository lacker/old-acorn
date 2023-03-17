use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::normalizer::Normalizer;
use crate::term::{Clause, Literal, Term};

pub struct Prover {
    pub normalizer: Normalizer,

    pub clauses: Vec<Clause>,
}

pub enum Compare {
    Equal,
    NotEqual,
    Unknown,
}

impl Prover {
    pub fn new() -> Prover {
        Prover {
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

    // Checks whether we already know whether these two terms are equal.
    // This only does exact comparisons, so if we already know x = y,
    // this won't find that f(x) = f(y).
    pub fn exact_compare(&self, term1: &Term, term2: &Term) -> Compare {
        for clause in &self.clauses {
            if clause.literals.len() != 1 {
                continue;
            }
            match &clause.literals[0] {
                Literal::NotEquals(left, right) => {
                    //
                }
                Literal::Equals(left, right) => {
                    //
                }
                _ => continue,
            }
        }
        panic!("TODO")
    }
}
