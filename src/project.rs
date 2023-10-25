use std::collections::HashMap;
use std::io;
use std::path::PathBuf;

use crate::environment::Environment;
use crate::namespace::{NamespaceId, FIRST_NORMAL};
use crate::token::{self, Token};

// The Project is responsible for importing different files and assigning them namespace ids.
pub struct Project {
    // The root directory of the project
    root: PathBuf,

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
pub struct LoadError(String);

impl From<io::Error> for LoadError {
    fn from(error: io::Error) -> Self {
        LoadError(format!("{}", error))
    }
}

impl Project {
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
            root,
            modules: envs,
            namespaces: HashMap::new(),
        }
    }

    // Returns None if no such module has been loaded.
    pub fn get_module(
        &self,
        namespace: NamespaceId,
    ) -> Option<Result<&Environment, &token::Error>> {
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

        let mut filename = self.root.clone();
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

        let text = std::fs::read_to_string(&filename)?;
        let namespace = self.modules.len() as NamespaceId;
        let mut env = Environment::new(namespace);
        let tokens = Token::scan(&text);
        let module = if let Err(e) = env.add_tokens(tokens) {
            Err(e)
        } else {
            Ok(env)
        };
        self.modules.push(Some(module));
        self.namespaces.insert(module_name.to_string(), namespace);
        Ok(namespace)
    }

    fn take_env(&mut self, namespace: NamespaceId) -> Environment {
        let module = std::mem::take(&mut self.modules[namespace as usize]);
        match module {
            None => panic!("module not loaded"),
            Some(Ok(env)) => env,
            Some(Err(err)) => panic!("module had error: {}", err),
        }
    }

    fn force_load(root: &str, module_name: &str) -> Environment {
        let mut project = Project::new(root);
        let namespace = project.load(module_name).unwrap();
        project.take_env(namespace)
    }

    pub fn load_math(module_name: &str) -> Environment {
        Project::force_load("math", module_name)
    }

    pub fn load_test(module_name: &str) -> Environment {
        Project::force_load("test", module_name)
    }
}
