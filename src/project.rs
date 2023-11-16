use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::{fmt, io};

use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Range, Url};

use crate::environment::Environment;
use crate::namespace::{NamespaceId, FIRST_NORMAL};
use crate::prover::{Outcome, Prover};
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

    // Anything in here is used in preference to the real filesystem.
    // This can store either test data that doesn't exist on the filesystem at all, or
    // work in progress that hasn't been saved yet, via an IDE.
    // Maps (filename, contents).
    file_content: HashMap<PathBuf, String>,

    // modules[namespace] is the Module for the given namespace id
    modules: Vec<Module>,

    // namespaces maps from a module name specified in Acorn (like "foo.bar") to the namespace id
    namespaces: HashMap<String, NamespaceId>,

    // Used as a flag to stop a build in progress.
    build_stopped: Arc<AtomicBool>,
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

impl fmt::Display for LoadError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// An error that can be reported to the user.
pub enum UserError {
    // This sort of error can be attached to a specific place in a document.
    // Document, range in document, message.
    Local(Url, Range, String),

    // This sort of error cannot be attached to anything.
    Global(String),
}

// Loading errors are global errors.
impl From<LoadError> for UserError {
    fn from(e: LoadError) -> UserError {
        UserError::Global(e.to_string())
    }
}

impl fmt::Display for UserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UserError::Local(_, _, message) => write!(f, "{}", message),
            UserError::Global(message) => write!(f, "{}", message),
        }
    }
}

// The build process generates a number of build events
pub struct BuildEvent {
    // Current progress is done / total.
    // This is across all modules.
    pub progress: Option<(i32, i32)>,

    // Human-readable
    pub log_message: Option<String>,

    // Whenever we run into a problem, report the module name, plus the diagnostic itself.
    pub diagnostic: Option<(String, Diagnostic)>,
}

fn new_modules() -> Vec<Module> {
    let mut modules = vec![];
    while modules.len() < FIRST_NORMAL as usize {
        modules.push(Module::None);
    }
    modules
}

fn check_valid_module_part(s: &str, error_name: &str) -> Result<(), LoadError> {
    if s.is_empty() || !s.chars().all(|c| c.is_ascii_lowercase() || c == '_') {
        Err(LoadError(format!("invalid module name: {}", error_name)))
    } else {
        Ok(())
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
        Project {
            root,
            use_filesystem: true,
            file_content: HashMap::new(),
            modules: new_modules(),
            namespaces: HashMap::new(),
            build_stopped: Arc::new(AtomicBool::new(false)),
        }
    }

    // A Project where nothing can be imported.
    pub fn new_mock() -> Project {
        let mut p = Project::new("/mock");
        p.use_filesystem = false;
        p
    }

    // Dropping existing modules lets you update the project for new data.
    // TODO: do this incrementally instead of dropping everything.
    pub fn drop_modules(&mut self) {
        self.modules = new_modules();
        self.namespaces = HashMap::new();
    }

    // You only need read access to an RwLock<Project> to stop the build.
    // When the build is stopped, threads that didn't stop the build themselves should
    // finish any long-running process with an "interrupted" behavior, and give up their
    // locks on the project.
    pub fn stop_build(&self) {
        self.build_stopped
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }

    // You need to have write access to a RwLock<Project> to re-allow the build.
    //
    // To change the project, acquire a read lock, stop the build, acquire a write lock, mess
    // around with the project state however you wanted, then re-allow the build.
    //
    // This asymmetry ensures that when we quickly stop and re-allow the build, any build in
    // progress will in fact stop.
    pub fn allow_build(&mut self) {
        self.build_stopped = Arc::new(AtomicBool::new(false));
    }

    pub fn set_file_content(&mut self, path: PathBuf, content: &str) {
        self.file_content.insert(path, content.to_string());
    }

    pub fn build(&self, handler: &mut impl FnMut(BuildEvent)) {
        // Build in alphabetical order for consistency
        let mut namespaces: Vec<(&String, &NamespaceId)> = self.namespaces.iter().collect();
        namespaces.sort();

        // On the first pass we just look for errors.
        // If there are errors, we won't even try to do proving.
        // But, we will still go through and look for any other errors.
        let mut module_errors = false;
        let mut total: i32 = 0;
        for (name, namespace) in &namespaces {
            let module = self.get_module(**namespace);
            match module {
                Module::Ok(env) => {
                    total += env.goal_paths().len() as i32;
                }
                Module::Error(e) => {
                    let diagnostic = Diagnostic {
                        range: e.token.range(),
                        severity: Some(DiagnosticSeverity::ERROR),
                        message: e.to_string(),
                        ..Diagnostic::default()
                    };
                    handler(BuildEvent {
                        progress: None,
                        log_message: None,
                        diagnostic: Some((name.to_string(), diagnostic)),
                    });
                    module_errors = true;
                }
                Module::None => {
                    // I'm not sure in what situations this might happen.
                    handler(BuildEvent {
                        progress: None,
                        log_message: Some(format!("error: module {} is not loaded", name)),
                        diagnostic: None,
                    });
                    module_errors = true;
                }
                Module::Loading => {
                    // Happens if there's a circular import. A more localized error should
                    // show up elsewhere, so let's just log.
                    handler(BuildEvent {
                        progress: None,
                        log_message: Some(format!("error: module {} stuck in loading", name)),
                        diagnostic: None,
                    });
                    module_errors = true;
                }
            }
        }

        if module_errors {
            return;
        }

        // On the second pass we do the actual proving.
        let mut done: i32 = 0;
        for (name, namespace) in &namespaces {
            let env = self.get_env(**namespace).unwrap();
            let paths = env.goal_paths();
            for path in paths {
                let goal_context = env.get_goal_context(&self, &path);
                let mut prover = Prover::new(&self, &goal_context, false, None);
                prover.stop_flags.push(self.build_stopped.clone());
                let outcome = prover.search_for_contradiction(5000, 5.0);

                done += 1;
                let description = match outcome {
                    Outcome::Success => "",
                    Outcome::Exhausted => " is unprovable",
                    Outcome::Inconsistent => " - prover found an inconsistency",
                    Outcome::Unknown => " timed out",
                    Outcome::Interrupted => {
                        done = total;
                        " was interrupted"
                    }
                };
                let (diagnostic, log_message) = if outcome == Outcome::Success {
                    (None, None)
                } else {
                    let message = format!("{} {}", goal_context.name, description);
                    let diagnostic = Diagnostic {
                        range: goal_context.range,
                        severity: Some(DiagnosticSeverity::WARNING),
                        message: message.clone(),
                        ..Diagnostic::default()
                    };
                    (Some((name.to_string(), diagnostic)), Some(message))
                };

                handler(BuildEvent {
                    progress: Some((done, total)),
                    log_message,
                    diagnostic,
                });

                if outcome == Outcome::Interrupted {
                    return;
                }
            }
        }
    }

    // Set the file content. This has priority over the actual filesystem.
    #[cfg(test)]
    pub fn mock(&mut self, filename: &str, content: &str) {
        assert!(!self.use_filesystem);
        self.set_file_content(PathBuf::from(filename), content);
    }

    pub fn get_module(&self, namespace: NamespaceId) -> &Module {
        self.modules
            .get(namespace as usize)
            .unwrap_or(&Module::None)
    }

    pub fn get_module_by_name(&self, module_name: &str) -> &Module {
        if let Some(namespace) = self.namespaces.get(module_name) {
            self.get_module(*namespace)
        } else {
            &Module::None
        }
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
        if let Some(content) = self.file_content.get(path) {
            return Ok(content.clone());
        }
        if self.use_filesystem {
            std::fs::read_to_string(&path)
                .map_err(|e| LoadError(format!("error loading {}: {}", path.display(), e)))
        } else {
            Err(LoadError(format!("no mocked file for: {}", path.display())))
        }
    }

    pub fn module_name_from_path(&self, path: &Path) -> Result<String, LoadError> {
        let relative = path.strip_prefix(&self.root).map_err(|_| {
            LoadError(format!(
                "path {} is not in the project root {}",
                path.display(),
                self.root.display()
            ))
        })?;
        let components: Vec<_> = relative
            .components()
            .map(|comp| comp.as_os_str().to_string_lossy())
            .collect();
        let mut answer = String::new();
        for (i, component) in components.iter().enumerate() {
            let part = if i + 1 == components.len() {
                if !component.ends_with(".ac") {
                    return Err(LoadError(format!(
                        "path {} does not end with .ac",
                        path.display()
                    )));
                }
                component[..component.len() - 3].to_string()
            } else {
                component.to_string()
            };
            if i > 0 {
                answer.push('.');
            }
            answer.push_str(&part);
            check_valid_module_part(&part, &answer)?;
        }

        Ok(answer)
    }

    pub fn path_from_module_name(&self, module_name: &str) -> Result<PathBuf, LoadError> {
        let mut path = self.root.clone();
        let parts: Vec<&str> = module_name.split('.').collect();

        for (i, part) in parts.iter().enumerate() {
            check_valid_module_part(part, module_name)?;

            let component = if i + 1 == parts.len() {
                format!("{}.ac", part)
            } else {
                part.to_string()
            };
            path.push(component);
        }
        Ok(path)
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

        let path = self.path_from_module_name(module_name)?;
        let text = self.read_file(&path)?;

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
        let mut pending = vec![original_namespace];
        while !pending.is_empty() {
            let namespace = pending.pop().unwrap();
            if seen.contains(&namespace) {
                continue;
            }
            seen.insert(namespace);
            if let Module::Ok(env) = self.get_module(namespace) {
                for dep in env.bindings.direct_dependencies() {
                    pending.push(dep);
                }
            }
        }
        seen.remove(&original_namespace);
        let mut answer: Vec<_> = seen.into_iter().collect();
        answer.sort();
        answer
    }

    // Gets the current environment corresponding to a file url.
    pub fn get_url_env<'a>(&'a self, url: &Url) -> Result<&'a Environment, UserError> {
        let path = url
            .to_file_path()
            .map_err(|_| UserError::Global(format!("could not convert url to path: {}", url)))?;
        let module_name = self.module_name_from_path(&path)?;
        match self.get_module_by_name(&module_name) {
            Module::Ok(env) => Ok(env),
            Module::None => Err(UserError::Global(format!(
                "module {} not loaded",
                module_name
            ))),
            Module::Loading => Err(UserError::Global(format!(
                "module {} is still loading",
                module_name
            ))),
            Module::Error(e) => Err(UserError::Local(
                url.clone(),
                e.token.range(),
                e.to_string(),
            )),
        }
    }

    // Updates the contents of a file corresponding to a file url.
    pub fn update_url_content<'a>(
        &'a mut self,
        url: &Url,
        content: &str,
    ) -> Result<NamespaceId, UserError> {
        let path = url
            .to_file_path()
            .map_err(|_| UserError::Global(format!("could not convert url to path: {}", url)))?;
        let module_name = self.module_name_from_path(&path)?;

        // TODO: Ideally we would be able to refresh only one module, rather than dropping all of
        // them whenever one of them changes.
        self.drop_modules();

        self.set_file_content(path, content);
        Ok(self.load(&module_name)?)
    }

    // pub fn build(&self, )

    // Expects the module to load successfully and for there to be no errors in the loaded module.
    #[cfg(test)]
    pub fn expect_ok(&mut self, module_name: &str) -> NamespaceId {
        let namespace = self.load(module_name).expect("load failed");
        if let Module::Ok(_) = self.get_module(namespace) {
            // Success
            namespace
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
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock("/mock/main.ac", "import foo");
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
        p.mock("/mock/main.ac", "import nonexistent");
        p.expect_module_err("main");
    }

    #[test]
    fn test_nonexistent_property() {
        let mut p = Project::new_mock();
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock(
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
        p.mock("/mock/a.ac", "import b");
        p.mock("/mock/b.ac", "import c");
        p.mock("/mock/c.ac", "import a");
        p.expect_ok("a");
        // The error should show up in c.ac, not in a.ac
        assert!(p.errors().len() > 0);
    }

    #[test]
    fn test_self_import() {
        let mut p = Project::new_mock();
        p.mock("/mock/a.ac", "import a");
        p.expect_module_err("a");
    }

    #[test]
    fn test_import_from_subdir() {
        let mut p = Project::new_mock();
        p.mock("/mock/stuff/foo.ac", FOO_AC);
        p.mock("/mock/main.ac", "import stuff.foo");
        p.expect_ok("main");
    }

    #[test]
    fn test_good_imported_types() {
        let mut p = Project::new_mock();
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock(
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
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock(
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
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock(
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
