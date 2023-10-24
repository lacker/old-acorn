use std::collections::HashMap;

use crate::acorn_type::NamespaceId;
use crate::atom::AtomId;

// The ConstantKey identifies a constant in the Acorn language.
#[derive(Hash, Debug, Eq, PartialEq, Clone)]
struct ConstantKey {
    namespace: NamespaceId,
    name: String,
}

// In the Acorn language a constant is specified by its namespace and name.
// The low-level prover, on the other hand, just wants each constant to have a
// numerical id.
// The ConstantMap is a mapping between the two.
pub struct ConstantMap {
    // For c_i in the prover, constants[i] is the corresponding ConstantKey.
    // The AtomId -> ConstantKey lookup direction.
    constants: Vec<Option<ConstantKey>>,

    // Inverse map of constants.
    // The ConstantKey -> AtomId lookup direction.
    keymap: HashMap<ConstantKey, AtomId>,
}

impl ConstantMap {
    pub fn new() -> ConstantMap {
        ConstantMap {
            constants: vec![],
            keymap: HashMap::new(),
        }
    }

    // The version where the environment already knew what AtomId the constant should get.
    pub fn old_add_constant(&mut self, namespace: NamespaceId, id: AtomId, name: &str) {
        let key = ConstantKey {
            namespace,
            name: name.to_string(),
        };
        if self.constants.len() <= id as usize {
            self.constants.resize(id as usize + 1, None);
        }
        self.constants[id as usize] = Some(key.clone());
        self.keymap.insert(key, id);
    }

    // Assigns an id to this (namespace, name) pair if it doesn't already have one.
    pub fn new_add_constant(&mut self, namespace: NamespaceId, name: &str) -> AtomId {
        let key = ConstantKey {
            namespace,
            name: name.to_string(),
        };
        if let Some(&atom_id) = self.keymap.get(&key) {
            return atom_id;
        }
        let atom_id = self.constants.len() as AtomId;
        self.constants.push(Some(key.clone()));
        self.keymap.insert(key, atom_id);
        atom_id
    }

    pub fn get_info(&self, atom_id: AtomId) -> (NamespaceId, &str) {
        let key = &self.constants[atom_id as usize].as_ref().unwrap();
        (key.namespace, &key.name)
    }
}
