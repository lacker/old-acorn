use std::collections::HashMap;
use std::io;
use std::path::PathBuf;

use crate::binding_map::BindingMap;
use crate::environment::Environment;
use crate::namespace::{NamespaceId, FIRST_NORMAL};
use crate::token::{self, Token};

// The Project is responsible for importing different files and assigning them namespace ids.
pub struct Project {
    // The root directory of the project
    // Set to "/mock" for mock projects.
    root: PathBuf,

    // Whether we permit loading files from the filesystem
    use_filesystem: bool,

    // Anything in here is used in preference to the real filesystem
    // Maps (filename, contents).
    mock_files: HashMap<String, String>,

    // modules[namespace] can be:
    //   None, if it's a non-loadable namespace (ie below FIRST_NORMAL)
    //   None, when we are in the middle of loading the module
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
    // A Project where files are imported from the real filesystem.
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
            use_filesystem: true,
            mock_files: HashMap::new(),
            modules: envs,
            namespaces: HashMap::new(),
        }
    }

    // A Project where nothing can be imported.
    pub fn new_mock() -> Project {
        let mut p = Project::new("/mock");
        p.use_filesystem = false;
        p
    }

    // Used for mocking
    pub fn add(&mut self, filename: &str, content: &str) {
        assert!(!self.use_filesystem);
        self.mock_files
            .insert(filename.to_string(), content.to_string());
    }

    // Returns the bindings for a namespace, None if we don't have them, or an error if
    // there was an error importing the other module.
    pub fn get_bindings(
        &self,
        namespace: NamespaceId,
    ) -> Option<Result<&BindingMap, &token::Error>> {
        let module = self.modules.get(namespace as usize)?;
        let result = module.as_ref()?;
        Some(match result {
            Ok(env) => Ok(&env.bindings),
            Err(e) => Err(e),
        })
    }

    fn read_file(&self, path: &PathBuf) -> Result<String, LoadError> {
        let s = match path.to_str() {
            Some(s) => s,
            None => return Err(LoadError(format!("invalid path: {:?}", path))),
        };
        if self.use_filesystem {
            std::fs::read_to_string(&path)
                .map_err(|e| LoadError(format!("error loading {}: {}", s, e)))
        } else {
            if let Some(content) = self.mock_files.get(s) {
                Ok(content.clone())
            } else {
                Err(LoadError(format!("no mocked file for: {}", s)))
            }
        }
    }

    // Loads a module from cache if possible, or else from the filesystem.
    // Module names are a .-separated list where each one must be [a-z_].
    // Each component maps to a subdirectory, except the last one, which maps to a .ac file.
    // load returns an error if the module-loading process itself has an error.
    // For example, we might have an invalid name, the file might not exist, or this
    // might be a circular import.
    // If there is an error in the file, that will be reported by get_bindings.
    pub fn load(&mut self, module_name: &str) -> Result<NamespaceId, LoadError> {
        if let Some(namespace) = self.namespaces.get(module_name) {
            if *namespace < FIRST_NORMAL {
                panic!("namespace {} should not be loadable", namespace);
            }
            if self.modules[*namespace as usize].is_none() {
                return Err(LoadError(format!("circular import of {}", module_name)));
            }
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

        let text = self.read_file(&filename)?;
        let namespace = self.modules.len() as NamespaceId;
        self.modules.push(None);
        let mut env = Environment::new(namespace);
        let tokens = Token::scan(&text);
        let module = if let Err(e) = env.add_tokens(self, tokens) {
            Err(e)
        } else {
            Ok(env)
        };
        self.modules[namespace as usize] = Some(module);
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

    #[cfg(test)]
    fn expect_load_ok(&mut self, module_name: &str) {
        let namespace = self.load(module_name).expect("load failed");
        self.get_bindings(namespace)
            .expect("no bindings found")
            .expect("module had an error");
    }

    // This expects there to be an error during loading itself.
    #[cfg(test)]
    fn expect_load_err(&mut self, module_name: &str) {
        assert!(self.load(module_name).is_err());
    }

    // This expects the module to load, but for there to be an error in the loaded module.
    #[cfg(test)]
    fn expect_module_err(&mut self, module_name: &str) {
        let namespace = self.load(module_name).expect("load failed");
        let result = self
            .modules
            .get(namespace as usize)
            .unwrap()
            .as_ref()
            .unwrap();
        assert!(result.is_err());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FOO_AC: &str = r#"
    // Imported by other tests
    type Foo: axiom
    let foo: Foo = axiom
    define fooify(x: Foo) -> Foo = foo
    "#;

    #[test]
    fn test_basic_import() {
        let mut p = Project::new_mock();
        p.add("/mock/foo.ac", FOO_AC);
        p.add("/mock/main.ac", "import foo");
        p.expect_load_ok("main");
    }

    #[test]
    fn test_direct_import_nonexistent() {
        let mut p = Project::new_mock();
        p.expect_load_err("main");
    }

    #[test]
    fn test_indirect_import_nonexistent() {
        let mut p = Project::new_mock();
        p.add("/mock/main.ac", "import nonexistent");
        p.expect_module_err("main");
    }

    #[test]
    fn test_nonexistent_property() {
        let mut p = Project::new_mock();
        p.add("/mock/foo.ac", FOO_AC);
        p.add(
            "/mock/main.ac",
            r#"
            import foo
            let bar: foo.nonexistent = axiom
        "#,
        );
        p.expect_module_err("main");
    }

    #[test]
    fn test_circular_imports() {
        let mut p = Project::new_mock();
        p.add("/mock/a.ac", "import b");
        p.add("/mock/b.ac", "import c");
        p.add("/mock/c.ac", "import a");
        p.expect_load_err("a");
    }
}
