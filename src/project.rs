use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::{fmt, io};

use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity};
use walkdir::WalkDir;

use crate::binding_map::BindingMap;
use crate::environment::Environment;
use crate::module::{Module, ModuleId, FIRST_NORMAL};
use crate::prover::{Outcome, Prover};
use crate::token::{self, Token};

// The Project is responsible for importing different files and assigning them module ids.
pub struct Project {
    // The root directory of the project
    // Set to "/mock" for mock projects.
    root: PathBuf,

    // Whether we permit loading files from the filesystem
    use_filesystem: bool,

    // For "open" files, we use the content we are storing rather than the content on disk.
    // This can store either test data that doesn't exist on the filesystem at all, or
    // work in progress whose state is "owned" by an IDE via the language server protocol.
    //
    // Maps filename -> (contents, version number).
    // The version number can mean whatever the caller wants it to mean.
    // From vscode, it'll be the vscode version number.
    pub open_files: HashMap<PathBuf, (String, i32)>,

    // modules[module_id] is the Module for the given module id
    modules: Vec<Module>,

    // module_map maps from a module name specified in Acorn to its id
    module_map: HashMap<String, ModuleId>,

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
            module_map: HashMap::new(),
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
        self.module_map = HashMap::new();
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
        let answer = self.load_module(module_name).is_ok();
        self.targets.insert(module_name.to_string());
        answer
    }

    pub fn add_target_file(&mut self, path: &Path) -> bool {
        let module_name = self.module_name_from_path(path).unwrap();
        self.add_target(&module_name)
    }

    // Adds a target for all files in this directory.
    pub fn add_all_targets(&mut self) {
        if !self.use_filesystem {
            panic!("cannot add all targets without filesystem access")
        }
        for entry in WalkDir::new(&self.root).into_iter().filter_map(|e| e.ok()) {
            if entry.file_type().is_file() {
                let path = entry.path();
                if path.extension() == Some(std::ffi::OsStr::new("ac")) {
                    self.add_target_file(path);
                }
            }
        }
    }

    // Whether the provided content matches what we already have for an open file.
    pub fn matches_open_file(&self, path: &PathBuf, content: &str) -> bool {
        if let Some((existing, _)) = self.open_files.get(path) {
            existing == content
        } else {
            false
        }
    }

    // Returns None if we don't have this file at all.
    pub fn get_version(&self, path: &PathBuf) -> Option<i32> {
        self.open_files.get(path).map(|(_, version)| *version)
    }

    // Updating a file makes us treat it as "open". When a file is open, we use the
    // content in memory for it, rather than the content on disk.
    // Updated files are also added as build targets.
    pub fn update_file(&mut self, path: PathBuf, content: &str, version: i32) {
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
        self.open_files.insert(path, (content.to_string(), version));
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
                let outcome = prover.medium_search();

                done += 1;
                let mut exit_early = false;
                let description = match outcome {
                    Outcome::Success => "",
                    Outcome::Exhausted => " is unprovable",
                    Outcome::Inconsistent => " - prover found an inconsistency",
                    Outcome::Unknown => " timed out",
                    Outcome::Interrupted => {
                        exit_early = true;
                        " was interrupted"
                    }
                    Outcome::Error => {
                        exit_early = true;
                        " had an error"
                    }
                };

                let (diagnostic, log_message) = if outcome != Outcome::Success {
                    // This is a failure
                    let severity = Some(if exit_early {
                        DiagnosticSeverity::ERROR
                    } else {
                        DiagnosticSeverity::WARNING
                    });
                    target_warnings = true;
                    let mut message = format!("{}{}", goal_context.name, description);
                    if let Some(e) = prover.error {
                        message.push_str(&format!(": {}", e));
                    }
                    let diagnostic = Diagnostic {
                        range: goal_context.range,
                        severity,
                        message: message.clone(),
                        ..Diagnostic::default()
                    };
                    build_warnings = true;
                    (Some((target.to_string(), Some(diagnostic))), Some(message))
                } else {
                    (None, None)
                };

                if exit_early {
                    handler(BuildEvent {
                        progress: Some((total, total)),
                        log_message,
                        diagnostic,
                    });
                    return false;
                }

                handler(BuildEvent {
                    progress: Some((done, total)),
                    log_message,
                    diagnostic,
                });
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
        self.update_file(PathBuf::from(filename), content, 0);
    }

    pub fn get_module(&self, module_id: ModuleId) -> &Module {
        self.modules
            .get(module_id as usize)
            .unwrap_or(&Module::None)
    }

    pub fn get_module_by_name(&self, module_name: &str) -> &Module {
        if let Some(module) = self.module_map.get(module_name) {
            self.get_module(*module)
        } else {
            &Module::None
        }
    }

    pub fn get_env(&self, module_id: ModuleId) -> Option<&Environment> {
        if let Module::Ok(env) = self.get_module(module_id) {
            Some(env)
        } else {
            None
        }
    }

    pub fn get_env_by_name(&self, module_name: &str) -> Option<&Environment> {
        if let Some(module_id) = self.module_map.get(module_name) {
            self.get_env(*module_id)
        } else {
            None
        }
    }

    pub fn errors(&self) -> Vec<(ModuleId, &token::Error)> {
        let mut errors = vec![];
        for (module_id, module) in self.modules.iter().enumerate() {
            if let Module::Error(e) = module {
                errors.push((module_id as ModuleId, e));
            }
        }
        errors
    }

    fn read_file(&mut self, path: &PathBuf) -> Result<String, LoadError> {
        if let Some((content, _)) = self.open_files.get(path) {
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

    // Returns a load error if the path doesn't correspond to a module.
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
    // If there is an error in the file, the load will return a module id, but the module
    // for the id will have an error.
    // If "open" is passed, then we cache this file's content in open files.
    pub fn load_module(&mut self, module_name: &str) -> Result<ModuleId, LoadError> {
        if let Some(module_id) = self.module_map.get(module_name) {
            if *module_id < FIRST_NORMAL {
                panic!("module {} should not be loadable", module_id);
            }
            if let Module::Loading = self.get_module(*module_id) {
                return Err(LoadError(format!("circular import of {}", module_name)));
            }
            return Ok(*module_id);
        }

        let path = self.path_from_module_name(module_name)?;
        let text = self.read_file(&path)?;

        // Give this module an id before parsing it, so that we can catch circular imports.
        let module_id = self.modules.len() as ModuleId;
        self.modules.push(Module::Loading);
        self.module_map.insert(module_name.to_string(), module_id);

        let mut env = Environment::new(module_id);
        let tokens = Token::scan(&text);
        let module = if let Err(e) = env.add_tokens(self, tokens) {
            Module::Error(e)
        } else {
            Module::Ok(env)
        };
        self.modules[module_id as usize] = module;

        Ok(module_id)
    }

    // Appends all dependencies, including chains of direct dependencies.
    // Ie, if A imports B and B imports C, then A depends on B and C.
    // The order will be the "pop order", so that each module is added only
    // after all of its dependencies are added.
    pub fn all_dependencies(&self, original_module_id: ModuleId) -> Vec<ModuleId> {
        let mut answer = vec![];
        let mut seen = HashSet::new();
        self.append_dependencies(&mut seen, &mut answer, original_module_id);
        answer
    }

    // Helper function for all_dependencies.
    // Returns "false" if we have already seen this dependency.
    // Does not append module_id itself. If we want it, add that in last.
    fn append_dependencies(
        &self,
        seen: &mut HashSet<ModuleId>,
        output: &mut Vec<ModuleId>,
        module_id: ModuleId,
    ) -> bool {
        if !seen.insert(module_id) {
            return false;
        }
        if let Module::Ok(env) = self.get_module(module_id) {
            for dep in env.bindings.direct_dependencies() {
                if self.append_dependencies(seen, output, dep) {
                    output.push(dep);
                }
            }
        }
        true
    }

    pub fn get_bindings(&self, module_id: ModuleId) -> Option<&BindingMap> {
        if let Module::Ok(env) = self.get_module(module_id) {
            Some(&env.bindings)
        } else {
            None
        }
    }

    // Expects the module to load successfully and for there to be no errors in the loaded module.
    #[cfg(test)]
    pub fn expect_ok(&mut self, module_name: &str) -> ModuleId {
        let module_id = self.load_module(module_name).expect("load failed");
        match self.get_module(module_id) {
            Module::Ok(_) => module_id,
            Module::Error(e) => panic!("error in {}: {}", module_name, e),
            _ => panic!("logic error"),
        }
    }

    // This expects there to be an error during loading itself.
    #[cfg(test)]
    fn expect_load_err(&mut self, module_name: &str) {
        assert!(self.load_module(module_name).is_err());
    }

    // This expects the module to load, but for there to be an error in the loaded module.
    #[cfg(test)]
    fn expect_module_err(&mut self, module_name: &str) {
        let module_id = self.load_module(module_name).expect("load failed");
        if let Module::Error(_) = self.get_module(module_id) {
            // What we expected
        } else {
            panic!("expected error");
        }
    }

    // Checks that the given expression can be parsed and turned back into code.
    #[cfg(test)]
    fn check_code_into(&mut self, module_name: &str, input: &str, expected: &str) {
        use crate::expression::Expression;

        let module_id = self.expect_ok(module_name);
        let expression = Expression::expect_value(input);
        let env = self.get_env(module_id).expect("no env");
        let value = env
            .bindings
            .evaluate_value(self, &expression, None)
            .expect("could not evaluate");
        let output = env
            .bindings
            .value_to_code(&value)
            .expect("could not convert to code");

        if output != expected {
            panic!(
                "\nconverted:\n  {}\nto value:\n  {}\nand back to:\n  {}\nbut expected:\n  {}\n",
                input, value, output, expected
            );
        }
    }

    #[cfg(test)]
    fn check_code(&mut self, module_name: &str, code: &str) {
        self.check_code_into(module_name, code, code);
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

    #[test]
    fn test_code_generation() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            type MyType: axiom
            let t: MyType = axiom
        "#,
        );
        p.check_code("main", "t");
        p.check_code("main", "forall(x0: MyType) { x0 = t }");
    }

    #[test]
    fn test_code_for_imported_things() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            let thing1: bool = axiom
            let thing2: bool = axiom
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import stuff
            let st1: bool = stuff.thing1
        "#,
        );
        p.check_code_into("main", "stuff.thing1", "st1");
        p.check_code("main", "st1");
        p.check_code("main", "stuff.thing2");
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
        p.load_module("foo").expect("loading foo failed");
        p.load_module("main").expect("loading main failed");
        p.add_target("foo");
        p.add_target("main");
        let mut events = vec![];
        assert!(p.build(&mut |event| {
            events.push(event);
        }));

        // Testing this is annoying because I keep changing it for UI purposes.
        assert!(events.len() > 0);
    }

    #[test]
    fn test_imported_member_functions() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/boolpair.ac",
            r#"
            struct BoolPair {
                first: bool
                second: bool
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import boolpair
            type BoolPair: boolpair.BoolPair
            let first: BoolPair -> bool = BoolPair.first
        "#,
        );
        p.expect_ok("main");
        p.check_code("main", "first");
        p.check_code_into("main", "BoolPair.first", "first");
        p.check_code_into("main", "boolpair.BoolPair.first", "first");

        p.check_code("main", "BoolPair.second");
        p.check_code_into("main", "boolpair.BoolPair.second", "BoolPair.second");
    }

    #[test]
    fn test_struct_aliasing() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            struct Foo {
                member: bool
            }
            type Bar: Foo
        "#,
        );
        p.expect_ok("stuff");
        p.check_code_into("stuff", "Bar.member", "Foo.member");
    }
}
