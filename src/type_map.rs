use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, FunctionApplication};
use crate::atom::{Atom, AtomId, TypedAtom};
use crate::clause::Clause;
use crate::literal::Literal;
use crate::term::Term;

pub type TypeId = u16;

pub const EMPTY: TypeId = 0;
pub const BOOL: TypeId = 1;

#[derive(Hash, Debug, Eq, PartialEq, Clone)]
pub struct MonomorphKey {
    pub polymorph: AtomId,
    pub parameters: Vec<AcornType>,
}

// The Acorn language allows a rich variety of types, where each value has an AcornType, and where
// functions can be polymorphic.
// The low-level prover only understands simple typing, where each value has a TypeId, and there
// is no polymorphism.
// The TypeMap is a mapping between the two.
pub struct TypeMap {
    types: Vec<AcornType>,

    // One entry for each monomorphization
    monomorph_map: HashMap<MonomorphKey, AtomId>,

    // For each monomorphization, store how it was created and its type.
    pub monomorph_info: Vec<(MonomorphKey, TypeId)>,
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

impl TypeMap {
    pub fn new() -> TypeMap {
        TypeMap {
            types: vec![AcornType::Empty, AcornType::Bool],
            monomorph_info: vec![],
            monomorph_map: HashMap::new(),
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
            AcornValue::Variable(i, var_type) => {
                let type_id = self.add_type(var_type.clone());
                Ok(Term {
                    term_type: type_id,
                    head_type: type_id,
                    head: Atom::Variable(*i),
                    args: vec![],
                })
            }
            AcornValue::Application(application) => Ok(self.term_from_application(application)?),
            AcornValue::Monomorph(c, _, parameters) => {
                let key = MonomorphKey {
                    polymorph: *c,
                    parameters: parameters.clone(),
                };
                let (monomorph_id, type_id) =
                    if let Some(monomorph_id) = self.monomorph_map.get(&key) {
                        let (_, type_id) = self.monomorph_info[*monomorph_id as usize];
                        (*monomorph_id, type_id)
                    } else {
                        // Construct an atom and appropriate entries for this monomorph
                        let type_id = self.add_type(value.get_type());
                        let monomorph_id = self.monomorph_info.len() as AtomId;
                        self.monomorph_info.push((key.clone(), type_id));
                        self.monomorph_map.insert(key, monomorph_id);
                        (monomorph_id, type_id)
                    };

                Ok(Term {
                    term_type: type_id,
                    head_type: type_id,
                    head: Atom::Monomorph(monomorph_id),
                    args: vec![],
                })
            }
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
            AcornValue::Variable(i, var_type) => {
                let type_id = self.add_type(var_type.clone());
                Ok(Literal::positive(Term {
                    term_type: type_id,
                    head_type: type_id,
                    head: Atom::Variable(*i),
                    args: vec![],
                }))
            }
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
}
