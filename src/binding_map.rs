use std::collections::{BTreeMap, HashMap, HashSet};

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp, FunctionApplication};
use crate::atom::AtomId;
use crate::code_gen_error::CodeGenError;
use crate::expression::{Declaration, Expression, Terminator};
use crate::module::{ModuleId, FIRST_NORMAL};
use crate::project::Project;
use crate::token::{self, Error, Token, TokenIter, TokenType};

// A representation of the variables on the stack.
pub struct Stack {
    // Maps the name of the variable to their depth and their type.
    vars: HashMap<String, (AtomId, AcornType)>,
}

impl Stack {
    pub fn new() -> Self {
        Stack {
            vars: HashMap::new(),
        }
    }

    pub fn names(&self) -> Vec<&str> {
        let mut answer: Vec<&str> = vec![""; self.vars.len()];
        for (name, (i, _)) in &self.vars {
            answer[*i as usize] = name;
        }
        answer
    }

    fn insert(&mut self, name: String, acorn_type: AcornType) -> AtomId {
        let i = self.vars.len() as AtomId;
        self.vars.insert(name, (i, acorn_type));
        i
    }

    fn remove(&mut self, name: &str) {
        self.vars.remove(name);
    }

    pub fn remove_all(&mut self, names: &[String]) {
        for name in names {
            self.remove(name);
        }
    }

    // Returns the depth and type of the variable with this name.
    fn get(&self, name: &str) -> Option<&(AtomId, AcornType)> {
        self.vars.get(name)
    }
}

// In order to convert an Expression to an AcornValue, we need to convert the string representation
// of types, variable names, and constant names into numeric identifiers, detect name collisions,
// and typecheck everything.
// The BindingMap handles this. It does not handle Statements, just Expressions.
// It does not have to be efficient enough to run in the inner loop of the prover.
#[derive(Clone)]
pub struct BindingMap {
    // The module all these names are in.
    module: ModuleId,

    // Maps the name of a type to the type object.
    type_names: HashMap<String, AcornType>,

    // Maps the type object to the name of a type.
    reverse_type_names: HashMap<AcornType, String>,

    // Maps an identifier name to its type.
    // Has entries for both defined constants and aliases.
    identifier_types: HashMap<String, AcornType>,

    // Maps the name of a constant defined in this scope to information about it.
    // Doesn't handle variables defined on the stack, only ones that will be in scope for the
    // entirety of this environment.
    // Includes "<datatype>.<constant>" for members.
    constants: HashMap<String, ConstantInfo>,

    // The canonical identifier of a constant is the first place it is defined.
    // There may be other names in this environment that refer to the same thing.
    // When we create an AcornValue, we want to use the canonical name.
    // The alias -> canonical name mapping is stored here.
    alias_to_canonical: HashMap<String, (ModuleId, String)>,

    // Whenever a name from some other scope has a local alias in this one,
    // if we're generating code, we prefer to use the local name.
    // Thus, preferred_names maps the canonical identifier to a local alias.
    canonical_to_alias: HashMap<(ModuleId, String), String>,

    // Names that refer to other modules.
    // For example after "import foo", "foo" refers to a module.
    modules: BTreeMap<String, ModuleId>,

    // The local name for imported modules.
    reverse_modules: HashMap<ModuleId, String>,

    // The default data type to use for numeric literals.
    default: Option<(ModuleId, String)>,

    // Whether this constant is the name of a theorem in this context.
    // Inside the block containing the proof of a theorem, the name is not considered to
    // be a theorem.
    theorems: HashSet<String>,
}

#[derive(Clone)]
struct ConstantInfo {
    // The names of the type parameters this constant was defined with, if any.
    // These type parameters can be used in the definition.
    params: Vec<String>,

    // The definition of this constant, if it has one.
    definition: Option<AcornValue>,
}

// Return an error if the types don't match.
// This doesn't do full polymorphic typechecking, but it will fail if there's no
// way that the types can match, for example if a function expects T -> Nat and
// the value provided is Nat.
// actual_type should be non-generic here.
// expected_type can be generic.
pub fn check_type<'a>(
    error_token: &Token,
    expected_type: Option<&AcornType>,
    actual_type: &AcornType,
) -> token::Result<()> {
    if let Some(e) = expected_type {
        if e != actual_type {
            return Err(Error::new(
                error_token,
                &format!("expected type {}, but got {}", e, actual_type),
            ));
        }
    }
    Ok(())
}

// A name can refer to any of these things.
enum NamedEntity {
    Value(AcornValue),
    Type(AcornType),
    Module(ModuleId),
}

impl NamedEntity {
    fn expect_value(
        self,
        expected_type: Option<&AcornType>,
        token: &Token,
    ) -> token::Result<AcornValue> {
        match self {
            NamedEntity::Value(value) => {
                check_type(token, expected_type, &value.get_type())?;
                Ok(value)
            }
            NamedEntity::Type(_) => Err(Error::new(
                token,
                "name refers to a type but we expected a value",
            )),
            NamedEntity::Module(_) => Err(Error::new(
                token,
                "name refers to a module but we expected a value",
            )),
        }
    }

    fn expect_type(self, token: &Token) -> token::Result<AcornType> {
        match self {
            NamedEntity::Value(_) => Err(Error::new(
                token,
                "name refers to a value but we expected a type",
            )),
            NamedEntity::Type(t) => Ok(t),
            NamedEntity::Module(_) => Err(Error::new(
                token,
                "name refers to a module but we expected a type",
            )),
        }
    }
}

impl BindingMap {
    pub fn new(module: ModuleId) -> Self {
        assert!(module >= FIRST_NORMAL);
        let mut answer = BindingMap {
            module,
            type_names: HashMap::new(),
            reverse_type_names: HashMap::new(),
            identifier_types: HashMap::new(),
            constants: HashMap::new(),
            alias_to_canonical: HashMap::new(),
            canonical_to_alias: HashMap::new(),
            modules: BTreeMap::new(),
            reverse_modules: HashMap::new(),
            default: None,
            theorems: HashSet::new(),
        };
        answer.add_type_alias("Bool", AcornType::Bool);
        answer
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Simple helper functions.
    ////////////////////////////////////////////////////////////////////////////////

    pub fn name_in_use(&self, name: &str) -> bool {
        self.type_names.contains_key(name)
            || self.identifier_types.contains_key(name)
            || self.modules.contains_key(name)
    }

    fn insert_type_name(&mut self, name: String, acorn_type: AcornType) {
        if self.name_in_use(&name) {
            panic!("type name {} already bound", name);
        }
        // There can be multiple names for a type.
        // If we already have a name for the reverse lookup, we don't overwrite it.
        if !self.reverse_type_names.contains_key(&acorn_type) {
            self.reverse_type_names
                .insert(acorn_type.clone(), name.clone());
        }
        self.type_names.insert(name, acorn_type);
    }

    // Adds a new data type to the binding map.
    // Panics if the name is already bound.
    pub fn add_data_type(&mut self, name: &str) -> AcornType {
        if self.name_in_use(name) {
            panic!("type name {} already bound", name);
        }
        let data_type = AcornType::Data(self.module, name.to_string());
        self.insert_type_name(name.to_string(), data_type.clone());
        data_type
    }

    // Adds a new type name that's an alias for an existing type
    pub fn add_type_alias(&mut self, name: &str, acorn_type: AcornType) {
        if self.name_in_use(name) {
            panic!("type alias {} already bound", name);
        }
        if let AcornType::Data(module, type_name) = &acorn_type {
            self.canonical_to_alias
                .entry((*module, type_name.clone()))
                .or_insert(name.to_string());
        }
        self.insert_type_name(name.to_string(), acorn_type);
    }

    // Returns an AcornValue representing this name, if there is one.
    // Returns None if this name does not refer to a constant.
    pub fn get_constant_value(&self, name: &str) -> Option<AcornValue> {
        let constant_type = self.identifier_types.get(name)?.clone();

        // Aliases
        if let Some((canonical_module, canonical_name)) = self.alias_to_canonical.get(name) {
            return Some(AcornValue::Constant(
                *canonical_module,
                canonical_name.clone(),
                constant_type,
                vec![],
            ));
        }

        // Constants defined here
        Some(AcornValue::Constant(
            self.module,
            name.to_string(),
            constant_type,
            self.constants.get(name)?.params.clone(),
        ))
    }

    // Gets the type for an identifier, not for a type name.
    // E.g. if let x: Nat = 0, then get_type("x") will give you Nat.
    pub fn get_type_for_identifier(&self, identifier: &str) -> Option<&AcornType> {
        self.identifier_types.get(identifier)
    }

    pub fn get_params(&self, identifier: &str) -> Vec<String> {
        match self.constants.get(identifier) {
            Some(info) => info.params.clone(),
            None => vec![],
        }
    }

    // Gets the type for a type name, not for an identifier.
    pub fn get_type_for_name(&self, type_name: &str) -> Option<&AcornType> {
        self.type_names.get(type_name)
    }

    pub fn has_type_name(&self, type_name: &str) -> bool {
        self.type_names.contains_key(type_name)
    }

    pub fn has_identifier(&self, identifier: &str) -> bool {
        self.identifier_types.contains_key(identifier)
    }

    // Returns the defined value, if there is a defined value.
    // If there isn't, returns None.
    pub fn get_definition(&self, name: &str) -> Option<&AcornValue> {
        self.constants.get(name)?.definition.as_ref()
    }

    // All other modules that we directly depend on, besides this one.
    // Sorted by the name of the import, so that the order will be consistent.
    pub fn direct_dependencies(&self) -> Vec<ModuleId> {
        self.modules.values().copied().collect()
    }

    pub fn set_default(&mut self, module: ModuleId, type_name: String) {
        self.default = Some((module, type_name));
    }

    // Adds a constant.
    // Returns whether this is a new constant - if it's just an alias, returns false.
    // This can also add members, by providing a name like "Foo.bar".
    pub fn add_constant(
        &mut self,
        name: &str,
        params: Vec<String>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
    ) -> bool {
        if self.name_in_use(name) {
            panic!("constant name {} already bound", name);
        }
        self.identifier_types
            .insert(name.to_string(), constant_type);

        // Check if we are aliasing some other constant.
        if let Some(AcornValue::Constant(module, external_name, _, _)) = &definition {
            let canonical = (*module, external_name.clone());
            if *module != self.module {
                // Prefer this alias locally to using the qualified, canonical name
                self.canonical_to_alias
                    .entry(canonical.clone())
                    .or_insert(name.to_string());
            }
            self.alias_to_canonical.insert(name.to_string(), canonical);
            return false;
        }

        // We're defining a new constant.
        let info = ConstantInfo { params, definition };
        self.constants.insert(name.to_string(), info);
        true
    }

    pub fn is_constant(&self, name: &str) -> bool {
        self.constants.contains_key(name)
    }

    pub fn mark_as_theorem(&mut self, name: &str) {
        self.theorems.insert(name.to_string());
    }

    pub fn is_theorem(&self, name: &str) -> bool {
        self.theorems.contains(name)
    }

    // Data types that come from type parameters get removed when they go out of scope.
    pub fn remove_data_type(&mut self, name: &str) {
        match self.type_names.remove(name) {
            Some(t) => {
                self.reverse_type_names.remove(&t);
            }
            None => panic!("removing data type {} which is already not present", name),
        }
    }

    pub fn add_module(&mut self, name: &str, module: ModuleId) {
        if self.name_in_use(name) {
            panic!("module name {} already bound", name);
        }
        self.modules.insert(name.to_string(), module);
        self.reverse_modules.insert(module, name.to_string());
    }

    pub fn is_module(&self, name: &str) -> bool {
        self.modules.contains_key(name)
    }

    // Whether this value is calling a theorem on some arguments.
    pub fn is_citation(&self, project: &Project, claim: &AcornValue) -> bool {
        match claim.is_named_function_call() {
            Some((module_id, name)) => {
                if module_id == self.module {
                    self.is_theorem(&name)
                } else {
                    let bindings = project.get_bindings(module_id).unwrap();
                    bindings.is_theorem(&name)
                }
            }
            None => false,
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for parsing Expressions and similar structures
    ////////////////////////////////////////////////////////////////////////////////

    // Evaluates an expression that represents a type.
    pub fn evaluate_type(
        &self,
        project: &Project,
        expression: &Expression,
    ) -> token::Result<AcornType> {
        match expression {
            Expression::Singleton(token) => {
                if token.token_type == TokenType::Axiom {
                    return Err(Error::new(
                        token,
                        "axiomatic types can only be created at the top level",
                    ));
                }
                if let Some(acorn_type) = self.type_names.get(token.text()) {
                    Ok(acorn_type.clone())
                } else {
                    Err(Error::new(token, "expected type name"))
                }
            }
            Expression::Unary(token, _) => Err(Error::new(
                token,
                "unexpected unary operator in type expression",
            )),
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow => {
                    let arg_exprs = left.flatten_list(true)?;
                    let mut arg_types = vec![];
                    for arg_expr in arg_exprs {
                        arg_types.push(self.evaluate_type(project, arg_expr)?);
                    }
                    let return_type = self.evaluate_type(project, right)?;
                    Ok(AcornType::new_functional(arg_types, return_type))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_entity(&mut Stack::new(), project, expression)?;
                    entity.expect_type(token)
                }
                _ => Err(Error::new(
                    token,
                    "unexpected binary operator in type expression",
                )),
            },
            Expression::Apply(left, _) => Err(Error::new(
                left.token(),
                "unexpected function application in type expression",
            )),
            Expression::Grouping(_, e, _) => self.evaluate_type(project, e),
            Expression::Binder(token, _, _, _) | Expression::IfThenElse(token, _, _, _, _) => {
                Err(Error::new(token, "unexpected token in type expression"))
            }
        }
    }

    // Evaluates a list of types.
    pub fn evaluate_type_list(
        &self,
        project: &Project,
        expression: &Expression,
        output: &mut Vec<AcornType>,
    ) -> token::Result<()> {
        match expression {
            Expression::Grouping(_, e, _) => self.evaluate_type_list(project, e, output),
            Expression::Binary(left, token, right) if token.token_type == TokenType::Comma => {
                self.evaluate_type_list(project, left, output)?;
                self.evaluate_type_list(project, right, output)
            }
            e => {
                output.push(self.evaluate_type(project, e)?);
                Ok(())
            }
        }
    }

    // Evaluates a variable declaration in this context.
    // expect_self is whether we expect this to be a "self" declaration.
    pub fn evaluate_declaration(
        &self,
        project: &Project,
        declaration: &Declaration,
    ) -> token::Result<(String, AcornType)> {
        match declaration {
            Declaration::Typed(name_token, type_expr) => {
                let acorn_type = self.evaluate_type(project, &type_expr)?;
                return Ok((name_token.to_string(), acorn_type));
            }
            Declaration::SelfToken(name_token) => {
                return Err(Error::new(
                    &name_token,
                    "cannot use 'self' as an argument here",
                ));
            }
        };
    }

    // Parses a list of named argument declarations and adds them to the stack.
    // class_name should be provided if these are the arguments of a new member function.
    pub fn bind_args<'a, I>(
        &self,
        stack: &mut Stack,
        project: &Project,
        declarations: I,
        class_name: Option<&str>,
    ) -> token::Result<(Vec<String>, Vec<AcornType>)>
    where
        I: IntoIterator<Item = &'a Declaration>,
    {
        let mut names = Vec::new();
        let mut types = Vec::new();
        for (i, declaration) in declarations.into_iter().enumerate() {
            if class_name.is_some() && i == 0 {
                match declaration {
                    Declaration::SelfToken(_) => {
                        names.push("self".to_string());
                        types.push(AcornType::Data(
                            self.module,
                            class_name.unwrap().to_string(),
                        ));
                        continue;
                    }
                    _ => {
                        return Err(Error::new(
                            declaration.token(),
                            "first argument of a member function must be 'self'",
                        ));
                    }
                }
            }
            let (name, acorn_type) = self.evaluate_declaration(project, declaration)?;
            if self.name_in_use(&name) {
                return Err(Error::new(
                    declaration.token(),
                    "cannot redeclare a name in an argument list",
                ));
            }
            if names.contains(&name) {
                return Err(Error::new(
                    declaration.token(),
                    "cannot declare a name twice in one argument list",
                ));
            }
            names.push(name);
            types.push(acorn_type);
        }
        for (name, acorn_type) in names.iter().zip(types.iter()) {
            stack.insert(name.to_string(), acorn_type.clone());
        }
        Ok((names, types))
    }

    // This function evaluates numbers when we already know what type they are.
    // token is the token to report errors with.
    // s is the string to parse.
    fn evaluate_number_with_type(
        &self,
        token: &Token,
        project: &Project,
        module: ModuleId,
        type_name: &str,
        s: &str,
    ) -> token::Result<AcornValue> {
        if let Some(value) = self.evaluate_class_variable(project, module, type_name, s) {
            return Ok(value);
        }

        if s.len() == 1 {
            return Err(Error::new(
                token,
                &format!("digit {}.{} is not defined", type_name, s),
            ));
        }

        let last_str = &s[s.len() - 1..];
        let last_num =
            self.evaluate_number_with_type(token, project, module, type_name, last_str)?;
        let initial_str = &s[..s.len() - 1];
        let initial_num =
            self.evaluate_number_with_type(token, project, module, type_name, initial_str)?;
        let read_fn = match self.evaluate_class_variable(project, module, type_name, "read") {
            Some(f) => f,
            None => {
                return Err(Error::new(
                    token,
                    &format!(
                        "{}.read must be defined to read numeric literals",
                        type_name
                    ),
                ))
            }
        };
        let value = AcornValue::new_apply(read_fn, vec![initial_num, last_num]);
        Ok(value)
    }

    // Evaluates a name scoped by a type name, like MyClass.foo
    fn evaluate_class_variable(
        &self,
        project: &Project,
        module: ModuleId,
        type_name: &str,
        var_name: &str,
    ) -> Option<AcornValue> {
        let bindings = if module == self.module {
            &self
        } else {
            project.get_bindings(module).unwrap()
        };
        let constant_name = format!("{}.{}", type_name, var_name);
        bindings.get_constant_value(&constant_name)
    }

    // Evaluates an expression that is supposed to describe a value, with an empty stack.
    pub fn evaluate_value(
        &self,
        project: &Project,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> token::Result<AcornValue> {
        self.evaluate_value_with_stack(&mut Stack::new(), project, expression, expected_type)
    }

    // Evaluates a variable attached to an instance like foo.bar.
    // token is used for reporting errors but may not correspond to anything in particular.
    fn evaluate_instance_variable(
        &self,
        token: &Token,
        project: &Project,
        instance: AcornValue,
        name: &str,
    ) -> token::Result<AcornValue> {
        let base_type = instance.get_type();
        if let AcornType::Data(module, type_name) = base_type {
            let bindings = if module == self.module {
                &self
            } else {
                project.get_bindings(module).unwrap()
            };
            let constant_name = format!("{}.{}", type_name, name);
            let function = match bindings.get_constant_value(&constant_name) {
                Some(value) => value,
                None => {
                    return Err(Error::new(
                        token,
                        &format!("unknown instance variable '{}'", constant_name),
                    ))
                }
            };
            // We need to typecheck that the apply is okay
            match function.get_type() {
                AcornType::Function(function_type) => {
                    check_type(
                        token,
                        Some(&function_type.arg_types[0]),
                        &instance.get_type(),
                    )?;
                }
                _ => {
                    return Err(Error::new(token, "expected member to be a function"));
                }
            };
            Ok(AcornValue::new_apply(function, vec![instance]))
        } else {
            Err(Error::new(
                token,
                &format!("objects of type {:?} have no members", base_type),
            ))
        }
    }

    // Evaluates a single name, which may be namespaced to another named entity.
    // In this situation, we don't know what sort of thing we expect the name to represent.
    // We have the entity described by a chain of names, and we're adding one more name to the chain.
    fn evaluate_name(
        &self,
        name_token: &Token,
        project: &Project,
        stack: &Stack,
        namespace: Option<NamedEntity>,
    ) -> token::Result<NamedEntity> {
        let name = name_token.text();
        match namespace {
            Some(NamedEntity::Value(instance)) => {
                let value = self.evaluate_instance_variable(name_token, project, instance, name)?;
                Ok(NamedEntity::Value(value))
            }
            Some(NamedEntity::Type(t)) => {
                if let AcornType::Data(module, type_name) = t {
                    if name_token.token_type == TokenType::Numeral {
                        let value = self.evaluate_number_with_type(
                            name_token,
                            project,
                            module,
                            &type_name,
                            name_token.text(),
                        )?;
                        return Ok(NamedEntity::Value(value));
                    }
                    match self.evaluate_class_variable(project, module, &type_name, name) {
                        Some(value) => Ok(NamedEntity::Value(value)),
                        None => Err(Error::new(
                            name_token,
                            &format!("{} has no member named '{}'", type_name, name),
                        )),
                    }
                } else {
                    Err(Error::new(name_token, "expected a data type"))
                }
            }
            Some(NamedEntity::Module(module)) => {
                if let Some(bindings) = project.get_bindings(module) {
                    bindings.evaluate_name(name_token, project, stack, None)
                } else {
                    Err(Error::new(name_token, "could not load bindings for module"))
                }
            }
            None => {
                match name_token.token_type {
                    TokenType::Identifier => {
                        if self.is_module(name) {
                            match self.modules.get(name) {
                                Some(module) => Ok(NamedEntity::Module(*module)),
                                None => Err(Error::new(name_token, "unknown module")),
                            }
                        } else if self.has_type_name(name) {
                            match self.get_type_for_name(name) {
                                Some(t) => Ok(NamedEntity::Type(t.clone())),
                                None => Err(Error::new(name_token, "unknown type")),
                            }
                        } else if let Some((i, t)) = stack.get(name) {
                            // This is a stack variable
                            Ok(NamedEntity::Value(AcornValue::Variable(*i, t.clone())))
                        } else if let Some(value) = self.get_constant_value(name) {
                            Ok(NamedEntity::Value(value))
                        } else {
                            Err(Error::new(
                                name_token,
                                &format!("unknown identifier '{}'", name),
                            ))
                        }
                    }
                    TokenType::Numeral => {
                        let (module, type_name) = match &self.default {
                            Some((module, type_name)) => (module, type_name),
                            None => {
                                return Err(Error::new(
                                    name_token,
                                    "you must set a default type for numeric literals",
                                ));
                            }
                        };
                        let value = self.evaluate_number_with_type(
                            name_token,
                            project,
                            *module,
                            type_name,
                            name_token.text(),
                        )?;
                        Ok(NamedEntity::Value(value))
                    }
                    TokenType::SelfToken => {
                        if let Some((i, t)) = stack.get(name) {
                            // This is a stack variable
                            Ok(NamedEntity::Value(AcornValue::Variable(*i, t.clone())))
                        } else {
                            Err(Error::new(name_token, "unexpected location for 'self'"))
                        }
                    }
                    t => Err(Error::new(name_token, &format!("unexpected {:?} token", t))),
                }
            }
        }
    }

    // Evaluates a single dot operator.
    fn evaluate_dot_expression(
        &self,
        stack: &mut Stack,
        project: &Project,
        left: &Expression,
        right: &Expression,
    ) -> token::Result<NamedEntity> {
        let right_token = match right {
            Expression::Singleton(token) => token,
            _ => {
                return Err(Error::new(
                    right.token(),
                    "expected an identifier after a dot",
                ))
            }
        };
        let left_entity = self.evaluate_entity(stack, project, left)?;

        self.evaluate_name(right_token, project, stack, Some(left_entity))
    }

    // Evaluates an expression that could represent any sort of named entity.
    // It could be a type, a value, or a module.
    fn evaluate_entity(
        &self,
        stack: &mut Stack,
        project: &Project,
        expression: &Expression,
    ) -> token::Result<NamedEntity> {
        // Handle a plain old name
        if let Expression::Singleton(token) = expression {
            return self.evaluate_name(token, project, stack, None);
        }

        if let Expression::Binary(left, token, right) = expression {
            if token.token_type == TokenType::Dot {
                return self.evaluate_dot_expression(stack, project, left, right);
            }
        }

        // If it isn't a name or a dot, it must be a value.
        let value = self.evaluate_value_with_stack(stack, project, expression, None)?;
        Ok(NamedEntity::Value(value))
    }

    // Evaluates an infix operator.
    // name is the special alphanumeric name that corresponds to the operator, like "+" expands to "add".
    fn evaluate_infix(
        &self,
        stack: &mut Stack,
        project: &Project,
        left: &Expression,
        token: &Token,
        right: &Expression,
        name: &str,
        expected_type: Option<&AcornType>,
    ) -> token::Result<AcornValue> {
        let left_value = self.evaluate_value_with_stack(stack, project, left, None)?;
        let right_value = self.evaluate_value_with_stack(stack, project, right, None)?;

        // Get the partial application to the left
        let partial = self.evaluate_instance_variable(token, project, left_value, name)?;
        let mut fa = match partial {
            AcornValue::Application(fa) => fa,
            _ => {
                return Err(Error::new(
                    token,
                    &format!(
                        "the '{}' operator requires a method named '{}'",
                        token, name
                    ),
                ))
            }
        };
        match fa.function.get_type() {
            AcornType::Function(f) => {
                if f.arg_types.len() != 2 {
                    return Err(Error::new(
                        token,
                        &format!("expected a binary function for '{}' method", name),
                    ));
                }
                check_type(token, Some(&f.arg_types[1]), &right_value.get_type())?;
            }
            _ => {
                return Err(Error::new(
                    token,
                    &format!("unexpected type for '{}' method", name),
                ))
            }
        };

        fa.args.push(right_value);
        let value = AcornValue::new_apply(*fa.function, fa.args);
        check_type(token, expected_type, &value.get_type())?;
        Ok(value)
    }

    // Imports a name from another module.
    // The name could either be a type or a value.
    pub fn import_name(
        &mut self,
        project: &Project,
        module: ModuleId,
        name_token: &Token,
    ) -> token::Result<()> {
        if self.name_in_use(&name_token.text()) {
            return Err(Error::new(
                name_token,
                &format!("name {} already bound in this module", name_token.text()),
            ));
        }
        let bindings = match project.get_bindings(module) {
            Some(b) => b,
            None => {
                return Err(Error::new(
                    name_token,
                    &format!("could not load bindings for imported module"),
                ))
            }
        };
        let entity = bindings.evaluate_name(name_token, project, &Stack::new(), None)?;
        match entity {
            NamedEntity::Value(value) => {
                if self.add_constant(&name_token.text(), vec![], value.get_type(), Some(value)) {
                    return Err(Error::new(name_token, "alias failed mysteriously"));
                }
                Ok(())
            }
            NamedEntity::Type(acorn_type) => {
                self.add_type_alias(&name_token.text(), acorn_type);
                Ok(())
            }
            NamedEntity::Module(_) => {
                Err(Error::new(name_token, "cannot import modules indirectly"))
            }
        }
    }

    // Evaluates an expression that describes a value, with a stack given as context.
    // A value expression could be either a value or an argument list.
    // Returns the value along with its type.
    pub fn evaluate_value_with_stack(
        &self,
        stack: &mut Stack,
        project: &Project,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> token::Result<AcornValue> {
        match expression {
            Expression::Singleton(token) => match token.token_type {
                TokenType::Axiom => panic!("axiomatic values should be handled elsewhere"),
                TokenType::ForAll | TokenType::Exists | TokenType::Function => {
                    return Err(Error::new(
                        token,
                        "binder keywords cannot be used as values",
                    ));
                }
                TokenType::True | TokenType::False => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    Ok(AcornValue::Bool(token.token_type == TokenType::True))
                }
                TokenType::Identifier | TokenType::Numeral | TokenType::SelfToken => {
                    let entity = self.evaluate_name(token, project, stack, None)?;
                    Ok(entity.expect_value(expected_type, token)?)
                }
                token_type => Err(Error::new(
                    token,
                    &format!("identifier expression has token type {:?}", token_type),
                )),
            },
            Expression::Unary(token, expr) => match token.token_type {
                TokenType::Not => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    let value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        expr,
                        Some(&AcornType::Bool),
                    )?;
                    Ok(AcornValue::Not(Box::new(value)))
                }
                _ => Err(Error::new(
                    token,
                    "unexpected unary operator in value expression",
                )),
            },
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        left,
                        Some(&AcornType::Bool),
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&AcornType::Bool),
                    )?;

                    Ok(AcornValue::Binary(
                        BinaryOp::Implies,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::Equals => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(stack, project, left, None)?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&left_value.get_type()),
                    )?;
                    Ok(AcornValue::Binary(
                        BinaryOp::Equals,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::NotEquals => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(stack, project, left, None)?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&left_value.get_type()),
                    )?;
                    Ok(AcornValue::Binary(
                        BinaryOp::NotEquals,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::And => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        left,
                        Some(&AcornType::Bool),
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&AcornType::Bool),
                    )?;
                    Ok(AcornValue::Binary(
                        BinaryOp::And,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::Or => {
                    check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        left,
                        Some(&AcornType::Bool),
                    )?;
                    let right_value = self.evaluate_value_with_stack(
                        stack,
                        project,
                        right,
                        Some(&AcornType::Bool),
                    )?;
                    Ok(AcornValue::Binary(
                        BinaryOp::Or,
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::Dot => {
                    let entity = self.evaluate_dot_expression(stack, project, left, right)?;
                    Ok(entity.expect_value(expected_type, token)?)
                }
                token_type => match token_type.to_magic_method_name() {
                    Some(name) => {
                        self.evaluate_infix(stack, project, left, token, right, name, expected_type)
                    }
                    None => Err(Error::new(
                        token,
                        "unhandled binary operator in value expression",
                    )),
                },
            },
            Expression::Apply(function_expr, args_expr) => {
                let function =
                    self.evaluate_value_with_stack(stack, project, function_expr, None)?;
                let function_type = function.get_type();

                let function_type = match function_type {
                    AcornType::Function(f) => f,
                    _ => {
                        return Err(Error::new(function_expr.token(), "expected a function"));
                    }
                };

                let arg_exprs = args_expr.flatten_list(false)?;

                if function_type.arg_types.len() < arg_exprs.len() {
                    return Err(Error::new(
                        args_expr.token(),
                        &format!(
                            "expected <= {} arguments, but got {}",
                            function_type.arg_types.len(),
                            arg_exprs.len()
                        ),
                    ));
                }

                let mut args = vec![];
                let mut mapping = HashMap::new();
                for (i, arg_expr) in arg_exprs.iter().enumerate() {
                    let arg_type = &function_type.arg_types[i];
                    let arg_value =
                        self.evaluate_value_with_stack(stack, project, arg_expr, None)?;
                    if !arg_type.match_specialized(&arg_value.get_type(), &mut mapping) {
                        return Err(Error::new(
                            arg_expr.token(),
                            &format!(
                                "expected type {}, but got {}",
                                arg_type,
                                arg_value.get_type()
                            ),
                        ));
                    }
                    args.push(arg_value);
                }
                let applied_type = function_type.applied_type(arg_exprs.len());

                // For non-polymorphic functions we are done
                if mapping.is_empty() {
                    check_type(function_expr.token(), expected_type, &applied_type)?;
                    return Ok(AcornValue::new_apply(function, args));
                }

                // Templated functions have to just be constants
                let (c_module, c_name, c_type, c_params) =
                    if let AcornValue::Constant(c_module, c_name, c_type, c_params) = function {
                        (c_module, c_name, c_type, c_params)
                    } else {
                        return Err(Error::new(
                            function_expr.token(),
                            "a non-constant function cannot be a template",
                        ));
                    };

                let mut params = vec![];
                for param_name in &c_params {
                    match mapping.get(param_name) {
                        Some(t) => params.push((param_name.clone(), t.clone())),
                        None => {
                            return Err(Error::new(
                                function_expr.token(),
                                &format!("parameter {} could not be inferred", param_name),
                            ))
                        }
                    }
                }

                if expected_type.is_some() {
                    // Check the applied type
                    let specialized_type = applied_type.specialize(&params);
                    check_type(function_expr.token(), expected_type, &specialized_type)?;
                }

                let specialized = AcornValue::Specialized(c_module, c_name, c_type, params);
                Ok(AcornValue::Application(FunctionApplication {
                    function: Box::new(specialized),
                    args,
                }))
            }
            Expression::Grouping(_, e, _) => {
                self.evaluate_value_with_stack(stack, project, e, expected_type)
            }
            Expression::Binder(token, args, body, _) => {
                if args.len() < 1 {
                    return Err(Error::new(token, "binders must have at least one argument"));
                }
                let (arg_names, arg_types) = self.bind_args(stack, project, args, None)?;
                let body_type = match token.token_type {
                    TokenType::ForAll => Some(&AcornType::Bool),
                    TokenType::Exists => Some(&AcornType::Bool),
                    _ => None,
                };
                let ret_val = match self.evaluate_value_with_stack(stack, project, body, body_type)
                {
                    Ok(value) => match token.token_type {
                        TokenType::ForAll => Ok(AcornValue::ForAll(arg_types, Box::new(value))),
                        TokenType::Exists => Ok(AcornValue::Exists(arg_types, Box::new(value))),
                        TokenType::Function => Ok(AcornValue::Lambda(arg_types, Box::new(value))),
                        _ => Err(Error::new(token, "expected a binder identifier token")),
                    },
                    Err(e) => Err(e),
                };
                stack.remove_all(&arg_names);
                if ret_val.is_ok()
                    && token.token_type == TokenType::Function
                    && expected_type.is_some()
                {
                    // We could check this before creating the value rather than afterwards.
                    // It seems theoretically faster but I'm not sure if there's any reason to.
                    check_type(token, expected_type, &ret_val.as_ref().unwrap().get_type())?;
                }
                ret_val
            }
            Expression::IfThenElse(_, cond_exp, if_exp, else_exp, _) => {
                let cond = self.evaluate_value_with_stack(
                    stack,
                    project,
                    cond_exp,
                    Some(&AcornType::Bool),
                )?;
                let if_value =
                    self.evaluate_value_with_stack(stack, project, if_exp, expected_type)?;
                let else_value = self.evaluate_value_with_stack(
                    stack,
                    project,
                    else_exp,
                    Some(&if_value.get_type()),
                )?;
                Ok(AcornValue::IfThenElse(
                    Box::new(cond),
                    Box::new(if_value),
                    Box::new(else_value),
                ))
            }
        }
    }

    // Evaluate an expression that is scoped inside a bunch of variable declarations.
    // type_params is a list of tokens for the parametrized types in this value.
    // arg_exprs is a list of "<varname>: <typename>" expressions for the arguments.
    // value_type_expr is an optional expression for the type of the value.
    //   (None means expect a boolean value.)
    // value_expr is the expression for the value itself.
    //
    // This function mutates the binding map but sets it back to its original state when finished.
    //
    // Returns a tuple with:
    //   a list of type parameter names
    //   a list of argument names
    //   a list of argument types
    //   an optional unbound value. (None means axiom.)
    //   the value type
    //
    // Both the argument types and the value can be polymorphic, with the ith type parameter
    // represented as AcornType::Generic(i).
    // class_name should be provided if this is the definition of a member function.
    //
    // The return value is "unbound" in the sense that it has variable atoms that are not
    // bound within any lambda, exists, or forall value.
    pub fn evaluate_subvalue(
        &mut self,
        project: &Project,
        type_param_tokens: &[Token],
        args: &[Declaration],
        value_type_expr: Option<&Expression>,
        value_expr: &Expression,
        class_name: Option<&str>,
    ) -> token::Result<(
        Vec<String>,
        Vec<String>,
        Vec<AcornType>,
        Option<AcornValue>,
        AcornType,
    )> {
        // "Specific" types are types that can refer to these parameters bound as opaque types.
        // "Generic" types are types where those have been replaced with AcornType::Generic types.

        // Bind all the type parameters and arguments
        let mut type_param_names: Vec<String> = vec![];
        for token in type_param_tokens {
            if self.type_names.contains_key(token.text()) {
                return Err(Error::new(
                    token,
                    "cannot redeclare a type in a generic type list",
                ));
            }
            self.add_data_type(token.text());
            type_param_names.push(token.text().to_string());
        }
        let mut stack = Stack::new();
        let (arg_names, specific_arg_types) =
            self.bind_args(&mut stack, project, args, class_name)?;

        // Check for possible errors in the specification.
        // Each type has to be used by some argument so that we know how to
        // monomorphize the template.
        for (i, type_param_name) in type_param_names.iter().enumerate() {
            if !specific_arg_types
                .iter()
                .any(|a| a.refers_to(self.module, &type_param_name))
            {
                return Err(Error::new(
                    &type_param_tokens[i],
                    &format!(
                        "type parameter {} is not used in the function arguments",
                        type_param_names[i]
                    ),
                ));
            }
        }

        // Evaluate the inner value using our modified bindings
        let specific_value_type = match value_type_expr {
            Some(e) => self.evaluate_type(project, e)?,
            None => AcornType::Bool,
        };
        let generic_value = if value_expr.token().token_type == TokenType::Axiom {
            None
        } else {
            let specific_value = self.evaluate_value_with_stack(
                &mut stack,
                project,
                value_expr,
                Some(&specific_value_type),
            )?;
            let generic_value = specific_value.parametrize(self.module, &type_param_names);
            Some(generic_value)
        };

        // Parametrize everything before returning it
        let generic_value_type = specific_value_type.parametrize(self.module, &type_param_names);
        let generic_arg_types = specific_arg_types
            .into_iter()
            .map(|t| t.parametrize(self.module, &type_param_names))
            .collect();

        // Reset the bindings
        for name in type_param_names.iter().rev() {
            self.remove_data_type(&name);
        }

        Ok((
            type_param_names,
            arg_names,
            generic_arg_types,
            generic_value,
            generic_value_type,
        ))
    }

    // Finds the names of all constants that are in this module but unknown to this binding map.
    // Does not deduplicate
    pub fn find_unknown_local_constants(
        &self,
        value: &AcornValue,
        answer: &mut HashMap<String, AcornType>,
    ) {
        match value {
            AcornValue::Variable(_, _) | AcornValue::Bool(_) => {}
            AcornValue::Constant(module, name, t, _)
            | AcornValue::Specialized(module, name, t, _) => {
                if *module == self.module && !self.constants.contains_key(name) {
                    answer.insert(name.to_string(), t.clone());
                }
            }
            AcornValue::Application(app) => {
                self.find_unknown_local_constants(&app.function, answer);
                for arg in &app.args {
                    self.find_unknown_local_constants(arg, answer);
                }
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => {
                self.find_unknown_local_constants(value, answer);
            }
            AcornValue::Binary(_, left, right) => {
                self.find_unknown_local_constants(left, answer);
                self.find_unknown_local_constants(right, answer);
            }
            AcornValue::IfThenElse(cond, then_value, else_value) => {
                self.find_unknown_local_constants(cond, answer);
                self.find_unknown_local_constants(then_value, answer);
                self.find_unknown_local_constants(else_value, answer);
            }
            AcornValue::Not(value) => {
                self.find_unknown_local_constants(value, answer);
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for going the other way, to create expressions and code strings from values and types.
    ////////////////////////////////////////////////////////////////////////////////

    // Returns an error if this type can't be encoded. For example, it could be a type that
    // is not obviously accessible from this scope.
    fn type_to_expr(&self, acorn_type: &AcornType) -> Result<Expression, CodeGenError> {
        if let AcornType::Function(ft) = acorn_type {
            let mut args = vec![];
            for arg_type in &ft.arg_types {
                args.push(self.type_to_expr(arg_type)?);
            }
            let lhs = if args.len() == 1 {
                args.pop().unwrap()
            } else {
                Expression::generate_grouping(args)
            };
            let rhs = self.type_to_expr(&ft.return_type)?;
            return Ok(Expression::Binary(
                Box::new(lhs),
                TokenType::RightArrow.generate(),
                Box::new(rhs),
            ));
        }

        match self.reverse_type_names.get(acorn_type) {
            Some(name) => Ok(Expression::generate_identifier(name)),
            None => Err(CodeGenError::unnamed_type(acorn_type)),
        }
    }

    // We use variables named x0, x1, x2, etc when new temporary variables are needed.
    // Find the next one that's available.
    fn next_x_var(&self, next_x: &mut u32) -> String {
        loop {
            let name = format!("x{}", next_x);
            *next_x += 1;
            if !self.name_in_use(&name) {
                return name;
            }
        }
    }

    // We use variables named k0, k1, k2, etc when new constant names are needed.
    // Find the next one that's available.
    fn next_k_var(&self, next_k: &mut u32) -> String {
        loop {
            let name = format!("k{}", next_k);
            *next_k += 1;
            if !self.name_in_use(&name) {
                return name;
            }
        }
    }

    // If this value cannot be expressed in a single chunk of code, returns an error.
    // For example, it might refer to a constant that is not in scope.
    // Takes a next_k parameter so that it can be used sequentially in the middle of
    // a bunch of code generation.
    pub fn value_to_code(&self, value: &AcornValue) -> Result<String, CodeGenError> {
        let mut var_names = vec![];
        let mut next_x = 0;
        let mut next_k = 0;
        let expr = self.value_to_expr(value, &mut var_names, &mut next_x, &mut next_k)?;
        Ok(expr.to_string())
    }

    // Given a module and a name, find an expression that refers to the name.
    // Note that:
    //   module, the canonical module of the entity we are trying to express
    // is different from
    //   self.module, the module we are trying to express the name in
    fn name_to_expr(&self, module: ModuleId, name: &str) -> Result<Expression, CodeGenError> {
        let mut parts = name.split('.').collect::<Vec<_>>();

        // Handle numeric literals
        if parts.len() == 2 && parts[1].chars().all(|ch| ch.is_ascii_digit()) {
            let numeral = TokenType::Numeral.new_token(parts[1]);

            // If it's the default type, we don't need to scope it
            if let Some((default_module, default_type_name)) = &self.default {
                if *default_module == module && default_type_name == parts[0] {
                    return Ok(Expression::Singleton(numeral));
                }
            }

            // Otherwise, we need to scope it by the type
            let numeric_type = self.name_to_expr(module, parts[0])?;
            return Ok(Expression::Binary(
                Box::new(numeric_type),
                TokenType::Dot.generate(),
                Box::new(Expression::Singleton(numeral)),
            ));
        }

        if parts.len() > 2 {
            return Err(CodeGenError::UnhandledValue("unexpected dots".to_string()));
        }

        // Handle local constants
        if module == self.module {
            // TODO: this generates an identifier token with a dot, which is wrong
            return Ok(Expression::generate_identifier(name));
        }

        // Check if there's a local alias for this constant.
        let key = (module, name.to_string());
        if let Some(alias) = self.canonical_to_alias.get(&key) {
            return Ok(Expression::generate_identifier(alias));
        }

        // If it's a member function, check if there's a local alias for its struct.
        if parts.len() == 2 {
            let data_type = AcornType::Data(module, parts[0].to_string());
            if let Some(type_alias) = self.reverse_type_names.get(&data_type) {
                let lhs = Expression::generate_identifier(type_alias);
                let rhs = Expression::generate_identifier(parts[1]);
                return Ok(Expression::Binary(
                    Box::new(lhs),
                    TokenType::Dot.generate(),
                    Box::new(rhs),
                ));
            }
        }

        // Refer to this constant using its module
        match self.reverse_modules.get(&module) {
            Some(module_name) => {
                parts.insert(0, module_name);
                Ok(Expression::generate_identifier_chain(&parts))
            }
            None => Err(CodeGenError::UnimportedModule(module)),
        }
    }

    // If use_x is true we use x-variables; otherwise we use k-variables.
    fn generate_quantifier_expr(
        &self,
        token_type: TokenType,
        quants: &Vec<AcornType>,
        value: &AcornValue,
        var_names: &mut Vec<String>,
        use_x: bool,
        next_x: &mut u32,
        next_k: &mut u32,
    ) -> Result<Expression, CodeGenError> {
        let initial_var_names_len = var_names.len();
        let mut decls = vec![];
        for arg_type in quants {
            let var_name = if use_x {
                self.next_x_var(next_x)
            } else {
                self.next_k_var(next_k)
            };
            let name_token = TokenType::Identifier.new_token(&var_name);
            var_names.push(var_name);
            let type_expr = self.type_to_expr(arg_type)?;
            let var_name = Declaration::Typed(name_token, type_expr);
            let decl = var_name;
            decls.push(decl);
        }
        let subresult = self.value_to_expr(value, var_names, next_x, next_k)?;
        var_names.truncate(initial_var_names_len);
        Ok(Expression::Binder(
            token_type.generate(),
            decls,
            Box::new(subresult),
            TokenType::RightBrace.generate(),
        ))
    }

    // Convert an AcornValue to an Expression.
    fn value_to_expr(
        &self,
        value: &AcornValue,
        var_names: &mut Vec<String>,
        next_x: &mut u32,
        next_k: &mut u32,
    ) -> Result<Expression, CodeGenError> {
        match value {
            AcornValue::Variable(i, _) => {
                Ok(Expression::generate_identifier(&var_names[*i as usize]))
            }
            AcornValue::Constant(module, name, _, _) => self.name_to_expr(*module, name),
            AcornValue::Application(fa) => {
                let mut args = vec![];
                for arg in &fa.args {
                    args.push(self.value_to_expr(arg, var_names, next_x, next_k)?);
                }

                if let Some(name) = fa.function.is_member(&fa.args[0].get_type()) {
                    if args.len() == 2 {
                        // Infix operators
                        if let Some(op) = TokenType::from_magic_method_name(&name) {
                            let right = args.pop().unwrap();
                            let left = args.pop().unwrap();
                            return Ok(Expression::generate_binary(left, op, right));
                        }

                        // Long numeric literals
                        if name == "read" && args[0].is_number() {
                            if let Some(digit) = args[1].to_digit() {
                                let left = args.remove(0);
                                return Ok(Expression::generate_number(left, digit));
                            }
                        }
                    }

                    // General member functions
                    let instance = args.remove(0);
                    let bound = Expression::generate_binary(
                        instance,
                        TokenType::Dot,
                        Expression::generate_identifier(&name),
                    );
                    if args.len() == 0 {
                        // Like foo.bar
                        return Ok(bound);
                    } else {
                        // Like foo.bar(baz, qux)
                        let applied = Expression::Apply(
                            Box::new(bound),
                            Box::new(Expression::generate_grouping(args)),
                        );
                        return Ok(applied);
                    }
                }

                let f = self.value_to_expr(&fa.function, var_names, next_x, next_k)?;
                let grouped_args = Expression::generate_grouping(args);
                Ok(Expression::Apply(Box::new(f), Box::new(grouped_args)))
            }
            AcornValue::Binary(op, left, right) => {
                let left = self.value_to_expr(left, var_names, next_x, next_k)?;
                let right = self.value_to_expr(right, var_names, next_x, next_k)?;
                let token = op.token_type().generate();
                Ok(Expression::Binary(Box::new(left), token, Box::new(right)))
            }
            AcornValue::Not(x) => {
                let x = self.value_to_expr(x, var_names, next_x, next_k)?;
                Ok(Expression::Unary(TokenType::Not.generate(), Box::new(x)))
            }
            AcornValue::ForAll(quants, value) => self.generate_quantifier_expr(
                TokenType::ForAll,
                quants,
                value,
                var_names,
                true,
                next_x,
                next_k,
            ),
            AcornValue::Exists(quants, value) => self.generate_quantifier_expr(
                TokenType::Exists,
                quants,
                value,
                var_names,
                false,
                next_x,
                next_k,
            ),
            AcornValue::Lambda(quants, value) => self.generate_quantifier_expr(
                TokenType::Function,
                quants,
                value,
                var_names,
                true,
                next_x,
                next_k,
            ),
            AcornValue::Bool(b) => {
                let token = if *b {
                    TokenType::True.generate()
                } else {
                    TokenType::False.generate()
                };
                Ok(Expression::Singleton(token))
            }
            AcornValue::Specialized(module, name, _, _) => {
                // Here we are assuming that the context will be enough to disambiguate
                // the type of the templated name.
                // I'm not sure if this is a good assumption.
                self.name_to_expr(*module, name)
            }
            AcornValue::IfThenElse(condition, if_value, else_value) => {
                let condition = self.value_to_expr(condition, var_names, next_x, next_k)?;
                let if_value = self.value_to_expr(if_value, var_names, next_x, next_k)?;
                let else_value = self.value_to_expr(else_value, var_names, next_x, next_k)?;
                Ok(Expression::IfThenElse(
                    TokenType::If.generate(),
                    Box::new(condition),
                    Box::new(if_value),
                    Box::new(else_value),
                    TokenType::RightBrace.generate(),
                ))
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for testing.
    ////////////////////////////////////////////////////////////////////////////////

    fn str_to_type(&mut self, input: &str) -> AcornType {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let (expression, _) =
            Expression::parse_type(&mut tokens, Terminator::Is(TokenType::NewLine)).unwrap();
        match self.evaluate_type(&Project::new_mock(), &expression) {
            Ok(t) => t,
            Err(error) => panic!("Error evaluating type expression: {}", error),
        }
    }

    pub fn assert_type_ok(&mut self, input_code: &str) {
        let acorn_type = self.str_to_type(input_code);
        let type_expr = self.type_to_expr(&acorn_type).unwrap();
        let reconstructed_code = type_expr.to_string();
        let reevaluated_type = self.str_to_type(&reconstructed_code);
        assert_eq!(acorn_type, reevaluated_type);
    }

    pub fn assert_type_bad(&mut self, input: &str) {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let expression =
            match Expression::parse_type(&mut tokens, Terminator::Is(TokenType::NewLine)) {
                Ok((expression, _)) => expression,
                Err(_) => {
                    // We expect a bad type so this is fine
                    return;
                }
            };
        assert!(self
            .evaluate_type(&Project::new_mock(), &expression)
            .is_err());
    }

    // Check that the given name actually does have this type in the environment.
    pub fn expect_type(&self, name: &str, type_string: &str) {
        let env_type = match self.identifier_types.get(name) {
            Some(t) => t,
            None => panic!("{} not found", name),
        };
        assert_eq!(env_type.to_string(), type_string);
    }

    // Check that this code, when converted to a value and back to code, is the same.
    pub fn expect_good_code(&self, input_code: &str) {
        let project = Project::new_mock();
        let expression = Expression::expect_value(input_code);
        let value = self
            .evaluate_value(&project, &expression, None)
            .expect("evaluate_value failed");
        let output_code = self.value_to_code(&value).expect("value_to_code failed");
        assert_eq!(input_code, output_code);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_env_types() {
        let mut b = BindingMap::new(FIRST_NORMAL);
        b.assert_type_ok("Bool");
        b.assert_type_ok("Bool -> Bool");
        b.assert_type_ok("Bool -> (Bool -> Bool)");
        b.assert_type_ok("(Bool -> Bool) -> (Bool -> Bool)");
        b.assert_type_ok("(Bool, Bool) -> Bool");
        b.assert_type_bad("Bool, Bool -> Bool");
        b.assert_type_bad("(Bool, Bool)");
    }
}
