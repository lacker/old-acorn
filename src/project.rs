use std::collections::{HashMap, HashSet};
use std::io;
use std::path::PathBuf;

use crate::acorn_value::AcornValue;
use crate::environment::Environment;
use crate::namespace::{NamespaceId, FIRST_NORMAL};
use crate::token::{self, Token};

// The Module represents a module that can be in different states of being loaded.
pub enum Module {
    // There is no such module, not even a namespace id for it
    None,

    // The module is in the process of being loaded.
    // Modules that fail on circular import will be in this state forever.
    Loading,

    // The module has been loaded, but there is an error in its code
    Error(token::Error),

    // The module has been loaded successfully and we have its environment
    Ok(Environment),
}

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

    // modules[namespace] is the Module for the given namespace id
    modules: Vec<Module>,

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
    pub fn new(root: &str) -> Project {
        let root = if root.starts_with('/') {
            PathBuf::from(root)
        } else {
            let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            d.push(root);
            d
        };
        let mut modules = vec![];
        while modules.len() < FIRST_NORMAL as usize {
            modules.push(Module::None);
        }
        Project {
            root,
            use_filesystem: true,
            mock_files: HashMap::new(),
            modules,
            namespaces: HashMap::new(),
        }
    }

    // A Project where nothing can be imported.
    pub fn new_mock() -> Project {
        let mut p = Project::new("/mock");
        p.use_filesystem = false;
        p
    }

    // A Project that only contains a single, already-existing Environment.
    pub fn shim(env: Environment) -> Project {
        let mut p = Project::new_mock();
        assert_eq!(env.namespace, p.modules.len() as NamespaceId);
        p.modules.push(Module::Ok(env));
        p
    }

    // Used for mocking
    pub fn add(&mut self, filename: &str, content: &str) {
        assert!(!self.use_filesystem);
        self.mock_files
            .insert(filename.to_string(), content.to_string());
    }

    pub fn get_module(&self, namespace: NamespaceId) -> &Module {
        self.modules
            .get(namespace as usize)
            .unwrap_or(&Module::None)
    }

    pub fn get_env(&self, namespace: NamespaceId) -> Option<&Environment> {
        if let Module::Ok(env) = self.get_module(namespace) {
            Some(env)
        } else {
            None
        }
    }

    pub fn errors(&self) -> Vec<(NamespaceId, &token::Error)> {
        let mut errors = vec![];
        for (namespace, module) in self.modules.iter().enumerate() {
            if let Module::Error(e) = module {
                errors.push((namespace as NamespaceId, e));
            }
        }
        errors
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
    // If there is an error in the file, the load will return a namespace id, but the module
    // for this namespace id will have an error.
    pub fn load(&mut self, module_name: &str) -> Result<NamespaceId, LoadError> {
        if let Some(namespace) = self.namespaces.get(module_name) {
            if *namespace < FIRST_NORMAL {
                panic!("namespace {} should not be loadable", namespace);
            }
            if let Module::Loading = self.get_module(*namespace) {
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

        // Give this module a namespace id before parsing it, so that we can catch
        // circular imports.
        let namespace = self.modules.len() as NamespaceId;
        self.modules.push(Module::Loading);
        self.namespaces.insert(module_name.to_string(), namespace);

        let mut env = Environment::new(namespace);
        let tokens = Token::scan(&text);
        let module = if let Err(e) = env.add_tokens(self, tokens) {
            Module::Error(e)
        } else {
            Module::Ok(env)
        };
        self.modules[namespace as usize] = module;

        Ok(namespace)
    }

    // All dependencies, including chains of direct depedencies.
    // Ie, if A imports B and B imports C, then A depends on B and C.
    // Does not count this namespace itself.
    // Includes modules with errors, but doesn't follow their dependencies.
    // Sorts in ascending order.
    pub fn all_dependencies(&self, original_namespace: NamespaceId) -> Vec<NamespaceId> {
        let mut seen = HashSet::new();
        let mut todo = vec![original_namespace];
        while !todo.is_empty() {
            let namespace = todo.pop().unwrap();
            if seen.contains(&namespace) {
                continue;
            }
            seen.insert(namespace);
            if let Module::Ok(env) = self.get_module(namespace) {
                for dep in env.bindings.direct_dependencies() {
                    todo.push(dep);
                }
            }
        }
        seen.remove(&original_namespace);
        let mut answer: Vec<_> = seen.into_iter().collect();
        answer.sort();
        answer
    }

    // Replaces each theorem with its definition.
    pub fn inline_theorems(&self, value: &AcornValue) -> AcornValue {
        value.replace_constants_with_values(0, &|namespace, name| {
            if let Module::Ok(env) = self.get_module(namespace) {
                if env.bindings.is_theorem(name) {
                    return env.bindings.get_definition(name).clone();
                }
            }
            None
        })
    }

    // Expects the module to load successfully and for there to be no errors in the loaded module.
    #[cfg(test)]
    fn expect_ok(&mut self, module_name: &str) {
        let namespace = self.load(module_name).expect("load failed");
        if let Module::Ok(_) = self.get_module(namespace) {
            // Success
        } else {
            panic!("module had an error");
        }
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
        if let Module::Error(_) = self.get_module(namespace) {
            // What we expected
        } else {
            panic!("expected error");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FOO_AC: &str = r#"
    // Imported by other tests
    type Foo: axiom
    type AlsoFoo: Foo
    type NotFoo: axiom
    let foo: Foo = axiom
    define fooify(x: Foo) -> Foo = foo
    "#;

    #[test]
    fn test_basic_import() {
        let mut p = Project::new_mock();
        p.add("/mock/foo.ac", FOO_AC);
        p.add("/mock/main.ac", "import foo");
        p.expect_ok("main");
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
        p.expect_ok("a");
        // The error should show up in c.ac, not in a.ac
        assert!(p.errors().len() > 0);
    }

    #[test]
    fn test_self_import() {
        let mut p = Project::new_mock();
        p.add("/mock/a.ac", "import a");
        p.expect_module_err("a");
    }

    #[test]
    fn test_import_from_subdir() {
        let mut p = Project::new_mock();
        p.add("/mock/stuff/foo.ac", FOO_AC);
        p.add("/mock/main.ac", "import stuff.foo");
        p.expect_ok("main");
    }

    #[test]
    fn test_good_imported_types() {
        let mut p = Project::new_mock();
        p.add("/mock/foo.ac", FOO_AC);
        p.add(
            "/mock/main.ac",
            r#"
            import foo
            type MyFoo: foo.AlsoFoo
            let x: foo.Foo = axiom
            let y: MyFoo = axiom
            let z: bool = (x = y)
        "#,
        );
        p.expect_ok("main");
    }

    #[test]
    fn test_bad_imported_types() {
        let mut p = Project::new_mock();
        p.add("/mock/foo.ac", FOO_AC);
        p.add(
            "/mock/main.ac",
            r#"
            import foo
            type MyFoo: foo.NotFoo
            let x: foo.Foo = axiom
            let y: MyFoo = axiom
            let z: bool = (x = y)
        "#,
        );
        p.expect_module_err("main");
    }

    #[test]
    fn test_imported_constants() {
        let mut p = Project::new_mock();
        p.add("/mock/foo.ac", FOO_AC);
        p.add(
            "/mock/main.ac",
            r#"
            import foo
            let x: foo.Foo = axiom
            let y: foo.Foo = foo.foo
            let z: bool = (x = y)
        "#,
        );
        p.expect_ok("main");
    }
}
