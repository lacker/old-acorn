use std::collections::HashMap;

use crate::atom::{Atom, AtomId};
use crate::module::ModuleId;

// The ConstantKey identifies a constant in the Acorn language.
#[derive(Hash, Debug, Eq, PartialEq, Clone)]
pub struct ConstantKey {
    pub module: ModuleId,
    pub name: String,
}

// In the Acorn language a constant is uniquely identified by its module id and name.
// The low-level prover, on the other hand, just wants each constant to have a
// numerical id.
// The ConstantMap is a mapping between the two.
pub struct ConstantMap {
    // For global constant i in the prover, global_constants[i] is the corresponding ConstantKey.
    // The AtomId -> ConstantKey lookup direction.
    global_constants: Vec<Option<ConstantKey>>,

    // For lobal constant i in the prover, local_constants[i] is the corresponding ConstantKey.
    // The AtomId -> ConstantKey lookup direction.
    local_constants: Vec<Option<ConstantKey>>,

    // Inverse map of constants.
    // The ConstantKey -> AtomId lookup direction.
    keymap: HashMap<ConstantKey, Atom>,
}

impl ConstantMap {
    pub fn new() -> ConstantMap {
        ConstantMap {
            global_constants: vec![],
            local_constants: vec![],
            keymap: HashMap::new(),
        }
    }

    // Assigns an id to this (module, name) pair if it doesn't already have one.
    pub fn add_constant(&mut self, module: ModuleId, name: &str) -> Atom {
        let key = ConstantKey {
            module,
            name: name.to_string(),
        };
        if let Some(&atom) = self.keymap.get(&key) {
            return atom;
        }
        let atom_id = self.global_constants.len() as AtomId;
        self.global_constants.push(Some(key.clone()));
        let atom = Atom::GlobalConstant(atom_id);
        self.keymap.insert(key, atom);
        atom
    }

    // Get information about a global constant.
    pub fn get_global_info(&self, atom_id: AtomId) -> (ModuleId, &str) {
        let key = &self.global_constants[atom_id as usize].as_ref().unwrap();
        (key.module, &key.name)
    }

    // Get information about a local constant.
    pub fn get_local_info(&self, atom_id: AtomId) -> (ModuleId, &str) {
        let key = &self.local_constants[atom_id as usize].as_ref().unwrap();
        (key.module, &key.name)
    }
}
