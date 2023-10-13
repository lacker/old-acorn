use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, FunctionApplication};
use crate::atom::{Atom, AtomId, TypedAtom};
use crate::clause::Clause;
use crate::term::{Literal, Term};

pub type TypeId = u16;

pub const ANY: TypeId = 0;
pub const BOOL: TypeId = 1;

// A TypeSpace lets us represent types uniquely as TypeIds.
// Zero always means "any", which we don't give to specific atoms, but we use for matching or
// for testing.
pub struct TypeSpace {
    types: Vec<AcornType>,
}

pub enum Error {
    Normalization(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Normalization(msg) => write!(f, "Normalization error: {}", msg),
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

impl TypeSpace {
    pub fn new() -> TypeSpace {
        TypeSpace {
            types: vec![AcornType::Any, AcornType::Bool],
        }
    }

    // Returns the id for the new type.
    pub fn add_type(&mut self, acorn_type: AcornType) -> TypeId {
        for (i, t) in self.types.iter().enumerate() {
            if t == &acorn_type {
                return i as TypeId;
            }
        }
        if !acorn_type.is_normalized() {
            panic!("Type {} is not normalized", acorn_type);
        }
        self.types.push(acorn_type);
        (self.types.len() - 1) as TypeId
    }

    pub fn get_type(&self, type_id: TypeId) -> &AcornType {
        &self.types[type_id as usize]
    }

    // Panics if the term has an invalid type id, or one that does not match its type.
    // Checks all type ids in the term, recursively.
    pub fn check_term(&self, term: &Term) {
        // The head has type (A -> B) when the term has type B, so the term's type should
        // have been constructed first.
        assert!(term.term_type <= term.head_type);

        // Make sure the type you get when applying the head to its arguments is the
        // same as the term type
        let mut calculated_type = self.get_type(term.head_type).clone();
        for arg in &term.args {
            calculated_type = calculated_type.apply(self.get_type(arg.term_type));
        }
        assert_eq!(calculated_type, *self.get_type(term.term_type));

        // Recurse
        for arg in &term.args {
            self.check_term(arg);
        }
    }

    pub fn check_literal(&self, literal: &Literal) {
        self.check_term(&literal.left);
        self.check_term(&literal.right);
    }

    pub fn check_clause(&self, clause: &Clause) {
        for literal in &clause.literals {
            self.check_literal(literal);
        }
    }

    // Constructs a new term from an atom
    pub fn term_from_atom(&mut self, atom: &TypedAtom) -> Term {
        let type_id = self.add_type(atom.acorn_type.clone());
        Term {
            term_type: type_id,
            head_type: type_id,
            head: atom.atom,
            args: vec![],
        }
    }

    // Constructs a new term from a function application
    // Function applications that are nested like f(x)(y) are flattened to f(x, y)
    pub fn term_from_application(&mut self, application: &FunctionApplication) -> Result<Term> {
        let term_type = self.add_type(application.return_type());
        let func_term = self.term_from_value(&application.function)?;
        let head = func_term.head;
        let head_type = func_term.head_type;
        let mut args = func_term.args;
        for arg in &application.args {
            args.push(self.term_from_value(arg)?);
        }
        Ok(Term {
            term_type,
            head_type,
            head,
            args,
        })
    }

    // Constructs a new term from an AcornValue
    // Returns None if it's inconvertible
    pub fn term_from_value(&mut self, value: &AcornValue) -> Result<Term> {
        match value {
            AcornValue::Atom(atom) => Ok(self.term_from_atom(atom)),
            AcornValue::Application(application) => Ok(self.term_from_application(application)?),
            _ => Err(Error::Normalization(format!(
                "Cannot convert {} to term",
                value
            ))),
        }
    }

    // Panics if this value cannot be converted to a literal.
    // Swaps left and right if needed, to sort.
    // Normalizes literals to <larger> = <smaller>, because that's the logical direction
    // to do rewrite-type lookups, on the larger literal first.
    pub fn literal_from_value(&mut self, value: &AcornValue) -> Result<Literal> {
        match value {
            AcornValue::Atom(atom) => Ok(Literal::positive(self.term_from_atom(atom))),
            AcornValue::Application(app) => Ok(Literal::positive(self.term_from_application(app)?)),
            AcornValue::Equals(left, right) => {
                let left_term = self.term_from_value(&*left)?;
                let right_term = self.term_from_value(&*right)?;
                Ok(Literal::equals(left_term, right_term))
            }
            AcornValue::NotEquals(left, right) => {
                let left_term = self.term_from_value(&*left)?;
                let right_term = self.term_from_value(&*right)?;
                Ok(Literal::not_equals(left_term, right_term))
            }
            AcornValue::Not(subvalue) => Ok(Literal::negative(self.term_from_value(subvalue)?)),
            _ => Err(Error::Normalization(format!(
                "Cannot convert {} to literal",
                value
            ))),
        }
    }

    // Converts a value to Clausal Normal Form.
    // Everything below "and" and "or" nodes must be literals.
    // Skips any tautologies.
    // Appends all results found.
    pub fn into_cnf(&mut self, value: &AcornValue, results: &mut Vec<Vec<Literal>>) -> Result<()> {
        match value {
            AcornValue::And(left, right) => {
                self.into_cnf(left, results)?;
                self.into_cnf(right, results)
            }
            AcornValue::Or(left, right) => {
                let mut left_results = Vec::new();
                self.into_cnf(left, &mut left_results)?;
                let mut right_results = Vec::new();
                self.into_cnf(right, &mut right_results)?;
                for left_result in left_results {
                    for right_result in &right_results {
                        let mut combined = left_result.clone();
                        combined.extend(right_result.clone());
                        results.push(combined);
                    }
                }
                Ok(())
            }
            _ => {
                let literal = self.literal_from_value(&value)?;
                if !literal.is_tautology() {
                    results.push(vec![literal]);
                }
                Ok(())
            }
        }
    }

    // For testing, make a boolean reference
    pub fn bref(&mut self, index: AtomId) -> Term {
        self.term_from_atom(&TypedAtom {
            atom: Atom::Variable(index),
            acorn_type: AcornType::Bool,
        })
    }

    // For testing, make a function application with this head, return type bool
    pub fn bfn(&mut self, head: Atom, args: Vec<Term>) -> Term {
        Term {
            term_type: BOOL,
            head_type: 0,
            head,
            args,
        }
    }
}
