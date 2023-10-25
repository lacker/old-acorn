use std::collections::HashMap;

use crate::environment::Environment;
use crate::namespace::{NamespaceId, FIRST_NORMAL};

// The Project is responsible for loading different files and assigning them namespace ids.
pub struct Project {
    // The root directory of the project
    root: String,

    // envs[namespace] is the environment for that namespace
    envs: Vec<Option<Environment>>,

    // namespaces maps from a file specified in Acorn (like "foo.bar") to the namespace id
    namespaces: HashMap<String, NamespaceId>,
}

impl Project {
    fn new(root: String) -> Project {
        let mut envs = vec![];
        while envs.len() < FIRST_NORMAL as usize {
            envs.push(None);
        }
        Project {
            root,
            envs,
            namespaces: HashMap::new(),
        }
    }
}
