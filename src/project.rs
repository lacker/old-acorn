use std::collections::HashMap;
use std::io;
use std::path::PathBuf;

use crate::environment::Environment;
use crate::namespace::{NamespaceId, FIRST_NORMAL};
use crate::token::{self, Token};

// The Project is responsible for importing different files and assigning them namespace ids.
pub struct Project {
    // The root directory of the project
    // Can be None for stub projects where every import fails.
    root: Option<PathBuf>,

    // modules[namespace] can be:
    //   None, if it's a non-loadable namespace (ie below FIRST_NORMAL)
    //   Ok(env) where env is the environment for that namespace
    //   Err(error) if there was an error in the code of the module
    modules: Vec<Option<Result<Environment, token::Error>>>,

    // namespaces maps from a file specified in Acorn (like "foo.bar") to the namespace id
    namespaces: HashMap<String, NamespaceId>,
}

// An error found while importing a module.
// Not an error in the code of the module itself.
#[derive(Debug)]
pub struct LoadError(pub String);

impl From<io::Error> for LoadError {
    fn from(error: io::Error) -> Self {
        LoadError(format!("{}", error))
    }
}

impl Project {
    pub fn stub() -> Project {
        Project {
            root: None,
            modules: vec![],
            namespaces: HashMap::new(),
        }
    }

    fn new(root: &str) -> Project {
        let root = if root.starts_with('/') {
            PathBuf::from(root)
        } else {
            let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            d.push(root);
            d
        };
        let mut envs = vec![];
        while envs.len() < FIRST_NORMAL as usize {
            envs.push(None);
        }
        Project {
            root: Some(root),
            modules: envs,
            namespaces: HashMap::new(),
        }
    }

    // Returns None if no such module has been loaded.
    pub fn get_env(&self, namespace: NamespaceId) -> Option<Result<&Environment, &token::Error>> {
        self.modules.get(namespace as usize).and_then(|x| match x {
            None => None,
            Some(Ok(env)) => Some(Ok(env)),
            Some(Err(err)) => Some(Err(err)),
        })
    }

    // Loads a module from cache if possible, or else from the filesystem.
    // Module names are a .-separated list where each one must be [a-z_].
    // Each component maps to a subdirectory, except the last one, which maps to a .ac file.
    // load returns an error if the module-loading process itself has an error.
    // For example, we might have an invalid name, or the file might not exist.
    // If there is an error in the file, that will be reported by the Module.
    pub fn load(&mut self, module_name: &str) -> Result<NamespaceId, LoadError> {
        if let Some(namespace) = self.namespaces.get(module_name) {
            return Ok(*namespace);
        }

        let mut filename = match self.root {
            None => return Err(LoadError("cannot import in stub projects".to_string())),
            Some(ref root) => root.clone(),
        };
        let parts: Vec<&str> = module_name.split('.').collect();

        for (i, part) in parts.iter().enumerate() {
            if !part.chars().all(|c| c.is_ascii_lowercase() || c == '_') {
                return Err(LoadError(format!("invalid module name: {}", module_name)));
            }

            let component = if i + 1 == parts.len() {
                format!("{}.ac", part)
            } else {
                part.to_string()
            };
            filename.push(component);
        }

        let text = match std::fs::read_to_string(&filename) {
            Ok(text) => text,
            Err(e) => {
                return Err(LoadError(format!(
                    "error loading {}: {}",
                    filename.to_string_lossy(),
                    e
                )))
            }
        };
        let namespace = self.modules.len() as NamespaceId;
        let mut env = Environment::new(namespace);
        let tokens = Token::scan(&text);
        let module = if let Err(e) = env.add_tokens(self, tokens) {
            Err(e)
        } else {
            Ok(env)
        };
        self.modules.push(Some(module));
        self.namespaces.insert(module_name.to_string(), namespace);
        Ok(namespace)
    }

    // Loads a file from the filesystem and just panics if that file is not there.
    pub fn force_load(root: &str, module_name: &str) -> Result<Environment, token::Error> {
        let mut project = Project::new(root);

        // Here we ignore any LoadError
        let namespace = project.load(module_name).unwrap();

        std::mem::take(&mut project.modules[namespace as usize]).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_import_ok() {
        Project::force_load("test", "import_ok").unwrap();
    }

    #[test]
    fn test_import_nonexistent() {
        let result = Project::force_load("test", "import_nonexistent");
        assert!(result.is_err());
    }

    #[test]
    fn test_nonexistent_property() {
        let result = Project::force_load("test", "nonexistent_property");
        assert!(result.is_err());
    }
}
