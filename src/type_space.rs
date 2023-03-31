use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, FunctionApplication};
use crate::atom::{Atom, TypedAtom};
use crate::term::{Literal, Term};

pub type TypeId = u16;

// A TypeSpace lets us represent types uniquely as TypeIds.
// Zero always means "any", which we don't give to specific atoms, but we use for matching or
// for testing.
pub struct TypeSpace {
    types: Vec<AcornType>,
}

impl TypeSpace {
    pub fn new() -> TypeSpace {
        TypeSpace {
            types: vec![AcornType::Any],
        }
    }

    // Returns the id for the new type.
    pub fn add_type(&mut self, acorn_type: AcornType) -> TypeId {
        for (i, t) in self.types.iter().enumerate() {
            if t == &acorn_type {
                return i as TypeId;
            }
        }
        self.types.push(acorn_type);
        (self.types.len() - 1).try_into().unwrap()
    }

    // Constructs a new term from an atom
    pub fn term_from_atom(&mut self, atom: TypedAtom) -> Term {
        Term {
            itype: self.add_type(atom.acorn_type),
            head: atom.atom,
            args: vec![],
        }
    }

    // Constructs a new term from a function application
    // Function applications that are nested like f(x)(y) are flattened to f(x, y)
    pub fn term_from_application(&mut self, application: FunctionApplication) -> Term {
        let itype = self.add_type(application.return_type());
        let func_term = self.term_from_value(*application.function);
        let head = func_term.head;
        let mut args = func_term.args;
        for arg in application.args {
            args.push(self.term_from_value(arg));
        }
        Term { itype, head, args }
    }

    // Constructs a new term from an AcornValue
    pub fn term_from_value(&mut self, value: AcornValue) -> Term {
        match value {
            AcornValue::Atom(atom) => self.term_from_atom(atom),
            AcornValue::Application(application) => self.term_from_application(application),
            _ => panic!("cannot convert value to term: {:?}", value),
        }
    }

    // Panics if this value cannot be converted to a literal.
    // Swaps left and right if needed, to sort.
    // Normalizes literals to <larger> = <smaller>, because that's the logical direction
    // to do rewrite-type lookups, on the larger literal first.
    pub fn literal_from_value(&mut self, value: AcornValue) -> Literal {
        match value {
            AcornValue::Atom(atom) => Literal::Positive(self.term_from_atom(atom)),
            AcornValue::Application(app) => Literal::Positive(self.term_from_application(app)),
            AcornValue::Equals(left, right) => {
                let left_term = self.term_from_value(*left);
                let right_term = self.term_from_value(*right);
                if left_term >= right_term {
                    Literal::Equals(left_term, right_term)
                } else {
                    Literal::Equals(right_term, left_term)
                }
            }
            AcornValue::NotEquals(left, right) => {
                let left_term = self.term_from_value(*left);
                let right_term = self.term_from_value(*right);
                if left_term >= right_term {
                    Literal::NotEquals(left_term, right_term)
                } else {
                    Literal::NotEquals(right_term, left_term)
                }
            }
            AcornValue::Not(subvalue) => Literal::Negative(self.term_from_value(*subvalue)),
            _ => panic!("cannot convert {:?} to a literal", value),
        }
    }

    // Converts a value to Clausal Normal Form.
    // Everything below "and" and "or" nodes must be literals.
    // Skips any tautologies.
    // Appends all results found.
    pub fn into_cnf(&mut self, value: AcornValue, results: &mut Vec<Vec<Literal>>) {
        match value {
            AcornValue::And(left, right) => {
                self.into_cnf(*left, results);
                self.into_cnf(*right, results);
            }
            AcornValue::Or(left, right) => {
                let mut left_results = Vec::new();
                self.into_cnf(*left, &mut left_results);
                let mut right_results = Vec::new();
                self.into_cnf(*right, &mut right_results);
                for left_result in left_results {
                    for right_result in &right_results {
                        let mut combined = left_result.clone();
                        combined.extend(right_result.clone());
                        results.push(combined);
                    }
                }
            }
            _ => {
                let literal = self.literal_from_value(value);
                if !literal.is_tautology() {
                    results.push(vec![literal]);
                }
            }
        }
    }

    // For testing, make a boolean reference
    pub fn bref(&mut self, index: usize) -> Term {
        self.term_from_atom(TypedAtom {
            atom: Atom::Reference(index),
            acorn_type: AcornType::Bool,
        })
    }

    // For testing, make a function application with this head, return type bool
    pub fn bfn(&mut self, head: Atom, args: Vec<Term>) -> Term {
        Term {
            itype: self.add_type(AcornType::Bool),
            head,
            args,
        }
    }
}
