use std::collections::{BTreeMap, HashMap};

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp, FunctionApplication};
use crate::atom::AtomId;
use crate::code_gen_error::CodeGenError;
use crate::expression::Expression;
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
    identifier_types: HashMap<String, AcornType>,

    // Maps the name of a constant to information about it.
    // Doesn't handle variables defined on the stack, only ones that will be in scope for the
    // entirety of this environment.
    // Includes "<datatype>.<constant>" for members.
    constants: HashMap<String, ConstantInfo>,

    // For constants in other modules that have a local name in this environment, we map
    // their canonical identifier to their local name.
    aliased_constants: HashMap<(ModuleId, String), String>,

    // Names that refer to other modules.
    // For example after "import foo", "foo" refers to a module.
    modules: BTreeMap<String, ModuleId>,

    // The local name for imported modules.
    reverse_modules: HashMap<ModuleId, String>,
}

#[derive(Clone)]
struct ConstantInfo {
    // The names of the type parameters this constant was defined with, if any.
    // These type parameters can be used in the definition.
    params: Vec<String>,

    // The definition of this constant, if it has one.
    definition: Option<AcornValue>,

    // Whether this constant is the name of a theorem in this context.
    // Inside the block containing the proof of a theorem, a theorem is just treated like a function, so
    // this flag will be set to false.
    theorem: bool,
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
            aliased_constants: HashMap::new(),
            modules: BTreeMap::new(),
            reverse_modules: HashMap::new(),
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

    pub fn is_type(&self, name: &str) -> bool {
        self.type_names.contains_key(name)
    }

    // Adds a new type name that's an alias for an existing type
    pub fn add_type_alias(&mut self, name: &str, acorn_type: AcornType) {
        if self.name_in_use(name) {
            panic!("type alias {} already bound", name);
        }
        self.insert_type_name(name.to_string(), acorn_type);
    }

    // Returns an AcornValue representing this name, if there is one.
    // Returns None if this name does not refer to a constant.
    pub fn get_constant_value(&self, name: &str) -> Option<AcornValue> {
        let info = self.constants.get(name)?;
        Some(AcornValue::Constant(
            self.module,
            name.to_string(),
            self.identifier_types[name].clone(),
            info.params.clone(),
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

    #[cfg(test)]
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

    // This can also add members, by providing a name like "Foo.bar".
    // It would be nice to not use string manipulation for this behavior.
    pub fn add_constant(
        &mut self,
        name: &str,
        params: Vec<String>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
    ) {
        if self.name_in_use(name) {
            panic!("constant name {} already bound", name);
        }

        // Check if we are aliasing a constant from another module.
        if let Some(AcornValue::Constant(module, external_name, _, _)) = &definition {
            if *module != self.module {
                let key = (*module, external_name.clone());
                self.aliased_constants
                    .entry(key)
                    .or_insert(name.to_string());
            }
        }

        let info = ConstantInfo {
            params,
            definition,
            theorem: false,
        };
        self.identifier_types
            .insert(name.to_string(), constant_type);
        self.constants.insert(name.to_string(), info);
    }

    pub fn is_constant(&self, name: &str) -> bool {
        self.constants.contains_key(name)
    }

    pub fn mark_as_theorem(&mut self, name: &str) {
        if !self.constants.contains_key(name) {
            panic!("cannot mark as theorem the unknown constant {}", name);
        }
        self.constants.get_mut(name).unwrap().theorem = true;
    }

    pub fn is_theorem(&self, name: &str) -> bool {
        match self.constants.get(name) {
            Some(info) => info.theorem,
            None => false,
        }
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
            Expression::Identifier(token) => {
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

    // Parses a declaration.
    // Must be in the form of "<name> : <type expression>"
    // For example, "x: Nat" or "f: Nat -> bool".
    // expect_self is whether we expect this variable to be named "self" based on its position.
    pub fn parse_declaration(
        &self,
        project: &Project,
        declaration: &Expression,
        expect_self: bool,
    ) -> token::Result<(String, AcornType)> {
        match declaration {
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::Colon => {
                    if left.token().token_type != TokenType::Identifier {
                        return Err(Error::new(
                            left.token(),
                            "expected an identifier in this declaration",
                        ));
                    }
                    let name = left.token().text().to_string();
                    if !Token::is_valid_variable_name(&name) {
                        return Err(Error::new(left.token(), "invalid variable name"));
                    }
                    if expect_self && name != "self" {
                        return Err(Error::new(
                            declaration.token(),
                            "expected 'self' as the first argument",
                        ));
                    }
                    if !expect_self && name == "self" {
                        return Err(Error::new(
                            declaration.token(),
                            "cannot use 'self' as an argument name here",
                        ));
                    }
                    let acorn_type = self.evaluate_type(project, right)?;
                    Ok((name, acorn_type))
                }
                _ => Err(Error::new(token, "expected a colon in this declaration")),
            },
            _ => Err(Error::new(declaration.token(), "expected a declaration")),
        }
    }

    // Parses a list of named argument declarations and adds them to the stack.
    pub fn bind_args<'a, I>(
        &self,
        stack: &mut Stack,
        project: &Project,
        declarations: I,
        is_member_function: bool,
    ) -> token::Result<(Vec<String>, Vec<AcornType>)>
    where
        I: IntoIterator<Item = &'a Expression>,
    {
        let mut names = Vec::new();
        let mut types = Vec::new();
        for (i, declaration) in declarations.into_iter().enumerate() {
            let expect_self = is_member_function && i == 0;
            let (name, acorn_type) = self.parse_declaration(project, declaration, expect_self)?;
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

    // Evaluates an expression that is supposed to describe a value, with an empty stack.
    pub fn evaluate_value(
        &self,
        project: &Project,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> token::Result<AcornValue> {
        self.evaluate_value_with_stack(&mut Stack::new(), project, expression, expected_type)
    }

    // Evaluates a single name, which may be namespaced to another named entity.
    // In this situation, we don't know what sort of thing we expect the name to represent.
    // We have the entity described by a chain of names, and we're adding one more name to the chain.
    fn evaluate_name(
        &self,
        token: &Token,
        project: &Project,
        stack: &Stack,
        namespace: Option<NamedEntity>,
        name: &str,
    ) -> token::Result<NamedEntity> {
        match namespace {
            Some(NamedEntity::Value(left_value)) => {
                // This is <object>.<name> so we need to find the type of the object on the left.
                let left_type = left_value.get_type();
                if let AcornType::Data(module, type_name) = left_type {
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
                                &format!("unknown member '{}'", constant_name),
                            ))
                        }
                    };
                    // We need to typecheck that the apply is okay
                    match function.get_type() {
                        AcornType::Function(function_type) => {
                            check_type(
                                token,
                                Some(&function_type.arg_types[0]),
                                &left_value.get_type(),
                            )?;
                        }
                        _ => {
                            return Err(Error::new(token, "expected member to be a function"));
                        }
                    };
                    let applied_value = AcornValue::new_apply(function, vec![left_value]);

                    Ok(NamedEntity::Value(applied_value))
                } else {
                    Err(Error::new(token, "type has no members"))
                }
            }
            Some(NamedEntity::Type(t)) => {
                if let AcornType::Data(module, type_name) = t {
                    let bindings = if module == self.module {
                        &self
                    } else {
                        project.get_bindings(module).unwrap()
                    };
                    let constant_name = format!("{}.{}", type_name, name);
                    match bindings.get_constant_value(&constant_name) {
                        Some(value) => Ok(NamedEntity::Value(value)),
                        None => Err(Error::new(
                            token,
                            &format!("unknown member '{}'", constant_name),
                        )),
                    }
                } else {
                    Err(Error::new(token, "expected a data type"))
                }
            }
            Some(NamedEntity::Module(module)) => {
                if let Some(bindings) = project.get_bindings(module) {
                    bindings.evaluate_name(token, project, stack, None, name)
                } else {
                    Err(Error::new(token, "could not load bindings for module"))
                }
            }
            None => {
                if self.is_module(name) {
                    match self.modules.get(name) {
                        Some(module) => Ok(NamedEntity::Module(*module)),
                        None => Err(Error::new(token, "unknown module")),
                    }
                } else if self.is_type(name) {
                    match self.get_type_for_name(name) {
                        Some(t) => Ok(NamedEntity::Type(t.clone())),
                        None => Err(Error::new(token, "unknown type")),
                    }
                } else if let Some((i, t)) = stack.get(name) {
                    // This is a stack variable
                    Ok(NamedEntity::Value(AcornValue::Variable(*i, t.clone())))
                } else if let Some(value) = self.get_constant_value(name) {
                    Ok(NamedEntity::Value(value))
                } else {
                    Err(Error::new(token, &format!("unknown identifier '{}'", name)))
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
            Expression::Identifier(token) => token,
            _ => {
                return Err(Error::new(
                    right.token(),
                    "expected an identifier after a dot",
                ))
            }
        };
        let left_entity = self.evaluate_entity(stack, project, left)?;

        self.evaluate_name(
            right_token,
            project,
            stack,
            Some(left_entity),
            right_token.text(),
        )
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
        if let Expression::Identifier(token) = expression {
            return self.evaluate_name(token, project, stack, None, token.text());
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
        let left_entity = NamedEntity::Value(left_value);
        let right_value = self.evaluate_value_with_stack(stack, project, right, None)?;

        // Get the partial application to the left
        let partial = self.evaluate_name(token, project, stack, Some(left_entity), name)?;
        let mut fa = match partial {
            NamedEntity::Value(AcornValue::Application(fa)) => fa,
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
            Expression::Identifier(token) => match token.token_type {
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

                TokenType::Identifier => {
                    let entity = self.evaluate_name(token, project, stack, None, token.text())?;
                    Ok(entity.expect_value(expected_type, token)?)
                }
                _ => Err(Error::new(
                    token,
                    "unexpected identifier in value expression",
                )),
            },
            Expression::Unary(token, expr) => match token.token_type {
                TokenType::Exclam => {
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
                TokenType::Ampersand => {
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
                TokenType::Pipe => {
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
                token_type => match token_type.infix_magic_function_name() {
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
            Expression::Binder(token, args_expr, body, _) => {
                let binder_args = args_expr.flatten_list(false)?;
                if binder_args.len() < 1 {
                    return Err(Error::new(
                        args_expr.token(),
                        "binders must have at least one argument",
                    ));
                }
                let (arg_names, arg_types) = self.bind_args(stack, project, binder_args, false)?;
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
    // The return value is "unbound" in the sense that it has variable atoms that are not
    // bound within any lambda, exists, or forall value.
    pub fn evaluate_subvalue(
        &mut self,
        project: &Project,
        type_param_tokens: &[Token],
        arg_exprs: &[Expression],
        value_type_expr: Option<&Expression>,
        value_expr: &Expression,
        is_member_function: bool,
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
            self.bind_args(&mut stack, project, arg_exprs, is_member_function)?;

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

    fn type_to_code(&self, acorn_type: &AcornType) -> Result<String, CodeGenError> {
        let expr = self.type_to_expr(acorn_type)?;
        Ok(expr.to_string())
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
    pub fn value_to_code(
        &self,
        value: &AcornValue,
        next_k: &mut u32,
    ) -> Result<String, CodeGenError> {
        let mut var_names = vec![];
        let mut next_x = 0;
        self.value_to_code_helper(value, &mut var_names, &mut next_x, next_k)
    }

    // Given a module and a name, find an expression that refers to the name.
    fn name_to_expr(&self, module: ModuleId, name: &str) -> Result<Expression, CodeGenError> {
        if module == self.module {
            return Ok(Expression::generate_identifier(name));
        }

        // Check if there's a local alias for this constant.
        let key = (module, name.to_string());
        if let Some(alias) = self.aliased_constants.get(&key) {
            return Ok(Expression::generate_identifier(alias));
        }

        // If it's a member function, check if there's a local alias for its struct.
        let parts = name.split('.').collect::<Vec<_>>();
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
                let lhs = Expression::generate_identifier(module_name);
                let rhs = Expression::generate_identifier(name);
                Ok(Expression::Binary(
                    Box::new(lhs),
                    TokenType::Dot.generate(),
                    Box::new(rhs),
                ))
            }
            None => Err(CodeGenError::UnimportedModule(module)),
        }
    }

    // Given a module and a name, find a way for us to describe the name with our bindings.
    fn name_to_code(&self, module: ModuleId, name: &str) -> Result<String, CodeGenError> {
        let expr = self.name_to_expr(module, name)?;
        Ok(expr.to_string())
    }

    pub fn value_to_expr_helper(
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
                let f = self.value_to_expr_helper(&fa.function, var_names, next_x, next_k)?;
                let mut args = vec![];
                for arg in &fa.args {
                    args.push(self.value_to_expr_helper(arg, var_names, next_x, next_k)?);
                }
                let grouped_args = Expression::generate_grouping(args);
                Ok(Expression::Apply(Box::new(f), Box::new(grouped_args)))
            }
            AcornValue::Binary(op, left, right) => {
                let left = self.value_to_expr_helper(left, var_names, next_x, next_k)?;
                let right = self.value_to_expr_helper(right, var_names, next_x, next_k)?;
                let token = op.token_type().generate();
                Ok(Expression::Binary(Box::new(left), token, Box::new(right)))
            }
            AcornValue::Not(x) => {
                let x = self.value_to_expr_helper(x, var_names, next_x, next_k)?;
                Ok(Expression::Unary(TokenType::Exclam.generate(), Box::new(x)))
            }
            // Currently, I don't think these code paths are ever hit.
            AcornValue::IfThenElse(..) => Err(CodeGenError::unhandled_value("if-then-else")),
            AcornValue::Lambda(..) => Err(CodeGenError::unhandled_value("lambda")),
            _ => todo!("XXX"),
        }
    }

    // Helper that handles temporary variable naming.
    // var_names are the names of the variables that we have already named.
    // next_x and next_k are the next names to give out.
    fn value_to_code_helper(
        &self,
        value: &AcornValue,
        var_names: &mut Vec<String>,
        next_x: &mut u32,
        next_k: &mut u32,
    ) -> Result<String, CodeGenError> {
        match value {
            AcornValue::Variable(i, _) => Ok(var_names[*i as usize].clone()),
            AcornValue::Constant(module, name, _, _) => self.name_to_code(*module, name),
            AcornValue::Application(fa) => {
                let f = self.value_to_code_helper(&fa.function, var_names, next_x, next_k)?;
                let mut args = vec![];
                for arg in &fa.args {
                    args.push(self.value_to_code_helper(arg, var_names, next_x, next_k)?);
                }
                Ok(format!("{}({})", f, args.join(", ")))
            }
            AcornValue::Binary(op, left, right) => {
                let left = self.value_to_code_helper(left, var_names, next_x, next_k)?;
                let right = self.value_to_code_helper(right, var_names, next_x, next_k)?;
                Ok(format!("{} {} {}", left, op, right))
            }
            AcornValue::Not(x) => {
                let x = self.value_to_code_helper(x, var_names, next_x, next_k)?;
                Ok(format!("!{}", x))
            }
            AcornValue::ForAll(quants, value) => {
                let initial_var_names_len = var_names.len();
                let mut args = vec![];
                for arg_type in quants {
                    let var_name = self.next_x_var(next_x);
                    let type_name = self.type_to_code(arg_type)?;
                    args.push(format!("{}: {}", var_name, type_name));
                    var_names.push(var_name);
                }
                let subresult = self.value_to_code_helper(value, var_names, next_x, next_k);
                var_names.truncate(initial_var_names_len);
                Ok(format!("forall({}) {{ {} }}", args.join(", "), subresult?))
            }
            AcornValue::Exists(quants, value) => {
                let initial_var_names_len = var_names.len();
                let mut args = vec![];
                for arg_type in quants {
                    let var_name = self.next_k_var(next_k);
                    let type_name = self.type_to_code(arg_type)?;
                    args.push(format!("{}: {}", var_name, type_name));
                    var_names.push(var_name);
                }
                let subresult = self.value_to_code_helper(value, var_names, next_x, next_k);
                var_names.truncate(initial_var_names_len);
                Ok(format!("exists({}) {{ {} }}", args.join(", "), subresult?))
            }
            AcornValue::Bool(b) => {
                if *b {
                    Ok("true".to_string())
                } else {
                    Ok("false".to_string())
                }
            }
            AcornValue::Specialized(module, name, _, _) => {
                // Here we are assuming that the context will be enough to disambiguate
                // the type of the templated name.
                // At some point this assumption will probably fail.
                self.name_to_code(*module, name)
            }

            // Currently, I don't think these code paths are ever hit.
            AcornValue::IfThenElse(..) => Err(CodeGenError::unhandled_value("if-then-else")),
            AcornValue::Lambda(..) => Err(CodeGenError::unhandled_value("lambda")),
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for testing.
    ////////////////////////////////////////////////////////////////////////////////

    fn str_to_type(&mut self, input: &str) -> AcornType {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let (expression, _) =
            Expression::parse(&mut tokens, false, |t| t == TokenType::NewLine).unwrap();
        match self.evaluate_type(&Project::new_mock(), &expression) {
            Ok(t) => t,
            Err(error) => panic!("Error evaluating type expression: {}", error),
        }
    }

    pub fn assert_type_ok(&mut self, input: &str) {
        let acorn_type = self.str_to_type(input);
        let reconstructed = self.type_to_code(&acorn_type).unwrap();
        let reevaluated = self.str_to_type(&reconstructed);
        assert_eq!(acorn_type, reevaluated);
    }

    pub fn assert_type_bad(&mut self, input: &str) {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let expression = match Expression::parse(&mut tokens, false, |t| t == TokenType::NewLine) {
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
        let value = self.evaluate_value(&project, &expression, None).unwrap();
        let mut next_k = 0;
        let output_code = self.value_to_code(&value, &mut next_k).unwrap();
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
