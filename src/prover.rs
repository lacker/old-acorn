use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::normalizer::Normalizer;
use crate::term::{Clause, Literal, Substitution, Term};

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
            let (left, right, answer) = match &clause.literals[0] {
                Literal::NotEquals(left, right) => (left, right, Compare::NotEqual),
                Literal::Equals(left, right) => (left, right, Compare::Equal),
                _ => continue,
            };

            // Check if (left, right) specializes to (term1, term2)
            let mut sub = Substitution::new();
            if sub.identify_terms(left, term1) && sub.identify_terms(right, term2) {
                return answer;
            }

            // Check if (left, right) specializes to (term2, term1)
            sub = Substitution::new();
            if sub.identify_terms(left, term2) && sub.identify_terms(right, term1) {
                return answer;
            }
        }
        Compare::Unknown
    }
}
