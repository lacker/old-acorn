use std::collections::HashMap;

use crate::atom::{Atom, AtomId};
use crate::module::{ModuleId, SKOLEM};

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
#[derive(Clone)]
pub struct ConstantMap {
    // For global constant i in the prover, global_constants[i] is the corresponding ConstantKey.
    // The AtomId -> ConstantKey lookup direction.
    global_constants: Vec<Option<ConstantKey>>,

    // For lobal constant i in the prover, local_constants[i] is the corresponding ConstantKey.
    // The AtomId -> ConstantKey lookup direction.
    local_constants: Vec<Option<ConstantKey>>,

    // Inverse map of constants.
    // The ConstantKey -> AtomId lookup direction.
    // Multiple ConstantKey can map to the same AtomId, when two constants alias to the same thing.
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
    pub fn add_constant(&mut self, module: ModuleId, name: &str, local: bool) -> Atom {
        if module == SKOLEM {
            panic!("skolem constants should not be stored in the ConstantMap");
        }
        let key = ConstantKey {
            module,
            name: name.to_string(),
        };
        if let Some(&atom) = self.keymap.get(&key) {
            return atom;
        }
        let atom = if local {
            let atom_id = self.local_constants.len() as AtomId;
            self.local_constants.push(Some(key.clone()));
            Atom::LocalConstant(atom_id)
        } else {
            let atom_id = self.global_constants.len() as AtomId;
            self.global_constants.push(Some(key.clone()));
            Atom::GlobalConstant(atom_id)
        };
        self.keymap.insert(key, atom);
        atom
    }

    pub fn has_constant(&self, module: ModuleId, name: &str) -> bool {
        let key = ConstantKey {
            module,
            name: name.to_string(),
        };
        self.keymap.contains_key(&key)
    }

    // Make the new module/name an alias to whatever the old one refers to.
    pub fn add_alias(
        &mut self,
        new_module: ModuleId,
        new_name: &str,
        old_module: ModuleId,
        old_name: &str,
    ) {
        assert!(!self.has_constant(new_module, new_name));
        assert!(self.has_constant(old_module, old_name));
        let new_key = ConstantKey {
            module: new_module,
            name: new_name.to_string(),
        };
        let old_key = ConstantKey {
            module: old_module,
            name: old_name.to_string(),
        };
        let atom = self.keymap[&old_key];
        self.keymap.insert(new_key, atom);
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
