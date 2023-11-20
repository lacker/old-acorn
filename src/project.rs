use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::{fmt, io};

use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity};

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

    // For "open" files, we use the content we are storing rather than the content on disk.
    // This can store either test data that doesn't exist on the filesystem at all, or
    // work in progress whose state is "owned" by an IDE via the language server protocol.
    // Maps filename -> contents.
    pub open_files: HashMap<PathBuf, String>,

    // modules[namespace] is the Module for the given namespace id
    modules: Vec<Module>,

    // namespaces maps from a module name specified in Acorn (like "foo.bar") to the namespace id
    namespaces: HashMap<String, NamespaceId>,

    // The module names that we want to build.
    targets: HashSet<String>,

    // Used as a flag to stop a build in progress.
    pub build_stopped: Arc<AtomicBool>,
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

// The build process generates a number of build events
#[derive(Debug)]
pub struct BuildEvent {
    // Current progress is done / total.
    // This is across all modules.
    pub progress: Option<(i32, i32)>,

    // Human-readable
    pub log_message: Option<String>,

    // Whenever we run into a problem, report the module name, plus the diagnostic itself.
    // If we prove everything in a module without any problems, report a None diagnostic.
    pub diagnostic: Option<(String, Option<Diagnostic>)>,
}

impl BuildEvent {
    fn default() -> BuildEvent {
        BuildEvent {
            progress: None,
            log_message: None,
            diagnostic: None,
        }
    }
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
            open_files: HashMap::new(),
            modules: new_modules(),
            namespaces: HashMap::new(),
            targets: HashSet::new(),
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
    fn drop_modules(&mut self) {
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

    // Returns whether it loaded okay.
    // Either way, it's still added as a target.
    pub fn add_target(&mut self, module_name: &str) -> bool {
        let answer = self.load(module_name).is_ok();
        self.targets.insert(module_name.to_string());
        answer
    }

    pub fn add_target_file(&mut self, path: &Path) -> bool {
        let module_name = self.module_name_from_path(path).unwrap();
        self.add_target(&module_name)
    }

    // Whether the provided content matches what we already have for an open file.
    pub fn matches_open_file(&self, path: &PathBuf, content: &str) -> bool {
        if let Some(existing) = self.open_files.get(path) {
            existing == content
        } else {
            false
        }
    }

    // Updating a file makes us treat it as "open". When a file is open, we use the
    // content in memory for it, rather than the content on disk.
    // Updated files are also added as build targets.
    pub fn update_file(&mut self, path: PathBuf, content: &str) {
        if self.matches_open_file(&path, content) {
            // No need to do anything
            return;
        }
        // TODO: handle files that are opened outside of the project
        let module_name = self.module_name_from_path(&path).unwrap();
        let mut reload_modules = vec![module_name];
        if self.open_files.contains_key(&path) {
            // We're changing the value of an existing file. This could invalidate
            // current modules.
            // For now, we just drop everything and reload the targets.
            // TODO: figure out precisely which ones are invalidated.
            self.drop_modules();
            for target in &self.targets {
                reload_modules.push(target.clone());
            }
        }
        self.open_files.insert(path, content.to_string());
        for module_name in &reload_modules {
            self.add_target(module_name);
        }
    }

    // Builds all open modules, and calls the event handler on any build events.
    //
    // There are two ways a build can go wrong.
    // An error is a human problem, like a syntax error or a type error.
    // A warning indicates that the prover could not prove something.
    // This may or may not be a human problem.
    //
    // Returns whether the build was entirely good, no errors or warnings.
    pub fn build(&self, handler: &mut impl FnMut(BuildEvent)) -> bool {
        // Build in alphabetical order by module name for consistency.
        let mut targets = self.targets.iter().collect::<Vec<_>>();
        targets.sort();

        handler(BuildEvent {
            log_message: Some(format!("building targets: {:?}", targets)),
            ..BuildEvent::default()
        });

        // On the first pass we just look for errors.
        // If there are errors, we won't even try to do proving.
        // But, we will still go through and look for any other errors.
        let mut module_errors = false;
        let mut total: i32 = 0;
        let mut envs = vec![];
        for target in &targets {
            let module = self.get_module_by_name(target);
            match module {
                Module::Ok(env) => {
                    total += env.goal_paths().len() as i32;
                    envs.push(env);
                }
                Module::Error(e) => {
                    let diagnostic = Diagnostic {
                        range: e.token.range(),
                        severity: Some(DiagnosticSeverity::ERROR),
                        message: e.to_string(),
                        ..Diagnostic::default()
                    };
                    handler(BuildEvent {
                        diagnostic: Some((target.to_string(), Some(diagnostic))),
                        ..BuildEvent::default()
                    });
                    module_errors = true;
                }
                Module::None => {
                    // Targets are supposed to be loaded already.
                    handler(BuildEvent {
                        log_message: Some(format!("error: module {} is not loaded", target)),
                        ..BuildEvent::default()
                    });
                    module_errors = true;
                }
                Module::Loading => {
                    // Happens if there's a circular import. A more localized error should
                    // show up elsewhere, so let's just log.
                    handler(BuildEvent {
                        log_message: Some(format!("error: module {} stuck in loading", target)),
                        ..BuildEvent::default()
                    });
                }
            }
        }

        if module_errors {
            return false;
        }

        handler(BuildEvent {
            progress: Some((0, total)),
            ..BuildEvent::default()
        });

        // On the second pass we do the actual proving.
        let mut build_warnings: bool = false;
        let mut done: i32 = 0;
        for (target, env) in targets.iter().zip(envs) {
            let mut target_warnings = false;
            let paths = env.goal_paths();
            for path in paths.iter() {
                let goal_context = env.get_goal_context(&self, &path);
                let mut prover = Prover::new(&self, &goal_context, false, None);
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
                    Outcome::Error => " had an error",
                };

                let (diagnostic, log_message) = if outcome != Outcome::Success {
                    // This is a failure
                    target_warnings = true;
                    let message = format!("{}{}", goal_context.name, description);
                    let diagnostic = Diagnostic {
                        range: goal_context.range,
                        severity: Some(DiagnosticSeverity::WARNING),
                        message: message.clone(),
                        ..Diagnostic::default()
                    };
                    build_warnings = true;
                    (Some((target.to_string(), Some(diagnostic))), Some(message))
                } else {
                    (None, None)
                };

                handler(BuildEvent {
                    progress: Some((done, total)),
                    log_message,
                    diagnostic,
                });

                if outcome == Outcome::Interrupted {
                    return false;
                }
            }
            if !target_warnings {
                // Report a None diagnostic to indicate that this file is okay
                handler(BuildEvent {
                    diagnostic: Some((target.to_string(), None)),
                    ..BuildEvent::default()
                });
            }
        }
        !build_warnings
    }

    // Set the file content. This has priority over the actual filesystem.
    #[cfg(test)]
    pub fn mock(&mut self, filename: &str, content: &str) {
        assert!(!self.use_filesystem);
        self.update_file(PathBuf::from(filename), content);
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

    pub fn get_env_by_name(&self, module_name: &str) -> Option<&Environment> {
        if let Some(namespace) = self.namespaces.get(module_name) {
            self.get_env(*namespace)
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

    fn read_file(&mut self, path: &PathBuf) -> Result<String, LoadError> {
        if let Some(content) = self.open_files.get(path) {
            return Ok(content.clone());
        }
        if !self.use_filesystem {
            return Err(LoadError(format!("no mocked file for: {}", path.display())));
        }
        match std::fs::read_to_string(&path) {
            Ok(s) => Ok(s),
            Err(e) => Err(LoadError(format!(
                "error loading {}: {}",
                path.display(),
                e
            ))),
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
    // If "open" is passed, then we cache this file's content in open files.
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
        p.expect_module_err("a");
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

    #[tokio::test]
    async fn test_building_project() {
        let mut p = Project::new_mock();
        p.mock("/mock/foo.ac", FOO_AC);
        p.mock(
            "/mock/main.ac",
            r#"
            import foo
            let new_foo: foo.Foo = axiom
            theorem goal: foo.fooify(new_foo) = foo.foo
        "#,
        );
        p.load("foo").expect("loading foo failed");
        p.load("main").expect("loading main failed");
        p.add_target("foo");
        p.add_target("main");
        let mut events = vec![];
        assert!(p.build(&mut |event| {
            events.push(event);
        }));

        // Testing this is annoying because I keep changing it for UI purposes.
        assert!(events.len() > 0);
    }
}
