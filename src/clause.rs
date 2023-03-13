use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, FunctionApplication};
use crate::atom::TypedAtom;

// Clauses and their parts, like Literals and Terms.

// If args is not empty, then atom should be treated as a function.
// Otherwise, the term is just the atom.
// This is more general than typical first-order logic terms, because the
// function can be quantified.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct Term {
    pub atom: TypedAtom,
    pub args: Vec<Term>,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.args.is_empty() {
            write!(f, "{}", self.atom)
        } else {
            write!(f, "{}(", self.atom)?;
            for (i, arg) in self.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ")")
        }
    }
}

impl Term {
    pub fn from_atom(atom: TypedAtom) -> Term {
        Term {
            atom,
            args: Vec::new(),
        }
    }

    pub fn from_application(app: FunctionApplication) -> Term {
        let atom = match *app.function {
            AcornValue::Atom(atom) => atom,
            _ => panic!("cannot convert {:?} to a term", app.function),
        };
        Term {
            atom: atom,
            args: app.args.into_iter().map(|x| Term::from_value(x)).collect(),
        }
    }

    // Panics if this value cannot be converted to a term.
    pub fn from_value(value: AcornValue) -> Term {
        match value {
            AcornValue::Atom(atom) => Term::from_atom(atom),
            AcornValue::Application(app) => Term::from_application(app),
            _ => panic!("cannot convert {:?} to a term", value),
        }
    }
}

// Literals are always boolean-valued.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum Literal {
    Positive(Term),
    Negative(Term),
    Equals(Term, Term),
    NotEquals(Term, Term),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Literal::Positive(term) => write!(f, "{}", term),
            Literal::Negative(term) => write!(f, "!{}", term),
            Literal::Equals(left, right) => write!(f, "{} = {}", left, right),
            Literal::NotEquals(left, right) => write!(f, "{} != {}", left, right),
        }
    }
}

impl Literal {
    // Panics if this value cannot be converted to a literal.
    // Swaps left and right if needed, to sort.
    pub fn from_value(value: AcornValue) -> Literal {
        match value {
            AcornValue::Atom(atom) => Literal::Positive(Term::from_atom(atom)),
            AcornValue::Application(app) => Literal::Positive(Term::from_application(app)),
            AcornValue::Equals(left, right) => {
                let left_term = Term::from_value(*left);
                let right_term = Term::from_value(*right);
                if left_term <= right_term {
                    Literal::Equals(left_term, right_term)
                } else {
                    Literal::Equals(right_term, left_term)
                }
            }
            AcornValue::NotEquals(left, right) => {
                let left_term = Term::from_value(*left);
                let right_term = Term::from_value(*right);
                if left_term <= right_term {
                    Literal::NotEquals(left_term, right_term)
                } else {
                    Literal::NotEquals(right_term, left_term)
                }
            }
            AcornValue::Not(subvalue) => Literal::Negative(Term::from_value(*subvalue)),
            _ => panic!("cannot convert {:?} to a literal", value),
        }
    }

    // Everything below "and" and "or" nodes must be literals.
    // Appends all results found.
    pub fn into_cnf(value: AcornValue, results: &mut Vec<Vec<Literal>>) {
        match value {
            AcornValue::And(left, right) => {
                Literal::into_cnf(*left, results);
                Literal::into_cnf(*right, results);
            }
            AcornValue::Or(left, right) => {
                let mut left_results = Vec::new();
                Literal::into_cnf(*left, &mut left_results);
                let mut right_results = Vec::new();
                Literal::into_cnf(*right, &mut right_results);
                for left_result in left_results {
                    for right_result in &right_results {
                        let mut combined = left_result.clone();
                        combined.extend(right_result.clone());
                        results.push(combined);
                    }
                }
            }
            _ => {
                results.push(vec![Literal::from_value(value)]);
            }
        }
    }
}

// A clause is a disjunction (an "or") of literals, universally quantified over some variables.
// We include the types of the universal variables it is quantified over.
// It cannot contain existential quantifiers.
#[derive(Debug)]
pub struct Clause {
    pub universal: Vec<AcornType>,
    pub literals: Vec<Literal>,
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.universal.is_empty() {
            return write!(f, "<empty>");
        }
        for (i, literal) in self.literals.iter().enumerate() {
            if i > 0 {
                write!(f, " | ")?;
            }
            write!(f, "{}", literal)?;
        }
        Ok(())
    }
}
