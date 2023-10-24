use std::collections::HashMap;

use crate::acorn_type::AcornType;

use crate::atom::{Atom, AtomId};
use crate::clause::Clause;
use crate::literal::Literal;
use crate::namespace::NamespaceId;
use crate::term::Term;

pub type TypeId = u16;

pub const EMPTY: TypeId = 0;
pub const BOOL: TypeId = 1;

#[derive(Hash, Debug, Eq, PartialEq, Clone)]
pub struct MonomorphKey {
    pub namespace: NamespaceId,
    pub name: String,
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

    pub fn term_from_monomorph(
        &mut self,
        namespace: NamespaceId,
        name: &str,
        parameters: &Vec<AcornType>,
        monomorph_type: AcornType,
    ) -> Term {
        let key = MonomorphKey {
            namespace,
            name: name.to_string(),
            parameters: parameters.clone(),
        };
        let (monomorph_id, type_id) = if let Some(monomorph_id) = self.monomorph_map.get(&key) {
            let (_, type_id) = self.monomorph_info[*monomorph_id as usize];
            (*monomorph_id, type_id)
        } else {
            // Construct an atom and appropriate entries for this monomorph
            let type_id = self.add_type(monomorph_type);
            let monomorph_id = self.monomorph_info.len() as AtomId;
            self.monomorph_info.push((key.clone(), type_id));
            self.monomorph_map.insert(key, monomorph_id);
            (monomorph_id, type_id)
        };

        Term {
            term_type: type_id,
            head_type: type_id,
            head: Atom::Monomorph(monomorph_id),
            args: vec![],
        }
    }

    pub fn get_monomorph_info(&self, id: AtomId) -> (NamespaceId, &str, &Vec<AcornType>) {
        let (key, _) = &self.monomorph_info[id as usize];
        (key.namespace, &key.name, &key.parameters)
    }
}
