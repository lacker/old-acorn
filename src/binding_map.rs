use std::collections::HashMap;

use crate::acorn_type::{AcornType, FunctionType};
use crate::acorn_value::{AcornValue, FunctionApplication};
use crate::atom::{Atom, AtomId};
use crate::expression::Expression;
use crate::namespace::{NamespaceId, FIRST_NORMAL};
use crate::token::{Error, Result, Token, TokenIter, TokenType};

// In order to convert an Expression to an AcornValue, we need to convert the string representation
// of types, variable names, and constant names into numeric identifiers, detect name collisions,
// and typecheck everything.
// The BindingMap handles this. It does not handle Statements, just Expressions.
// It does not have to be efficient enough to run in the inner loop of the prover.
#[derive(Clone)]
pub struct BindingMap {
    // The namespace all these names are in.
    namespace: NamespaceId,

    // Maps the name of a type to the type object.
    type_names: HashMap<String, AcornType>,

    // Maps an identifier name to its type.
    identifier_types: HashMap<String, AcornType>,

    // Maps the name of a constant to information about it.
    // Doesn't handle variables defined on the stack, only ones that will be in scope for the
    // entirety of this environment.
    constants: HashMap<String, ConstantInfo>,

    // Reverse lookup for the information in constants.
    // constant_names[i] is the name of Atom::Constant(i).
    // constants[constant_names[i]] = (i, _)
    constant_names: Vec<String>,

    // For variables defined on the stack, we keep track of their depth from the top.
    stack: HashMap<String, AtomId>,
}

#[derive(Clone)]
struct ConstantInfo {
    // The id of this constant, used for constructing its atom or for the index in constant_names.
    id: AtomId,

    // The definition of this constant, if it has one.
    definition: Option<AcornValue>,
}

impl BindingMap {
    pub fn new(namespace: NamespaceId) -> Self {
        assert!(namespace >= FIRST_NORMAL);
        BindingMap {
            namespace,
            constant_names: Vec::new(),
            type_names: HashMap::from([("bool".to_string(), AcornType::Bool)]),
            identifier_types: HashMap::new(),
            constants: HashMap::new(),
            stack: HashMap::new(),
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Simple helper functions.
    ////////////////////////////////////////////////////////////////////////////////

    // The names of all the stack variables, in order.
    pub fn stack_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = vec![""; self.stack.len()];
        for (name, i) in &self.stack {
            names[*i as usize] = name;
        }
        names
    }

    // Adds a new data type to the binding map.
    // Panics if the name is already a typename.
    pub fn add_data_type(&mut self, name: &str) -> AcornType {
        let data_type = AcornType::Data(self.namespace, name.to_string());
        if let Some(_) = self.type_names.insert(name.to_string(), data_type.clone()) {
            panic!("type name {} already exists", name);
        }
        data_type
    }

    // Adds a new type name that's an alias for an existing type
    pub fn add_type_alias(&mut self, name: &str, acorn_type: AcornType) {
        if let Some(_) = self.type_names.insert(name.to_string(), acorn_type) {
            panic!("type name {} already exists", name);
        }
    }

    // Returns None if this name does not refer to a constant.
    pub fn get_constant_id(&self, name: &str) -> Option<AtomId> {
        let info = self.constants.get(name)?;
        Some(info.id)
    }

    // Returns an AcornValue representing this name, if there is one.
    // Returns None if this name does not refer to a constant.
    pub fn get_constant_value(&self, name: &str) -> Option<AcornValue> {
        let info = self.constants.get(name)?;
        Some(AcornValue::Constant(
            self.namespace,
            info.id,
            name.to_string(),
            self.identifier_types[name].clone(),
        ))
    }

    pub fn get_constant_name(&self, id: AtomId) -> &str {
        &self.constant_names[id as usize]
    }

    // Gets the type for an identifier, not for a type name.
    // E.g. if let x: Nat = 0, then get_type("x") will give you Nat.
    pub fn get_type(&self, identifier: &str) -> Option<&AcornType> {
        self.identifier_types.get(identifier)
    }

    pub fn get_type_for_name(&self, type_name: &str) -> Option<&AcornType> {
        self.type_names.get(type_name)
    }

    pub fn has_type_name(&self, type_name: &str) -> bool {
        self.type_names.contains_key(type_name)
    }

    pub fn has_identifier(&self, identifier: &str) -> bool {
        self.identifier_types.contains_key(identifier)
    }

    pub fn num_constants(&self) -> AtomId {
        self.constant_names.len() as AtomId
    }

    // This creates an atomic value for the next constant, but does not bind it to the name.
    pub fn next_constant_atom(&self, name: &str, acorn_type: &AcornType) -> AcornValue {
        let c_id = self.num_constants();
        AcornValue::Constant(self.namespace, c_id, name.to_string(), acorn_type.clone())
    }

    // Returns the defined value, if there is a defined value.
    // If there isn't, returns None.
    pub fn get_definition(&self, name: &str) -> Option<&AcornValue> {
        self.constants.get(name)?.definition.as_ref()
    }

    pub fn get_definition_for_id(&self, id: AtomId) -> Option<&AcornValue> {
        let name = &self.constant_names[id as usize];
        self.get_definition(name)
    }

    pub fn add_constant(
        &mut self,
        name: &str,
        constant_type: AcornType,
        definition: Option<AcornValue>,
    ) -> AtomId {
        if self.identifier_types.contains_key(name) {
            panic!("name {} already bound to a type", name);
        }
        if self.constants.contains_key(name) {
            panic!("name {} already bound to a value", name);
        }

        let id = self.constant_names.len() as AtomId;
        let info = ConstantInfo { id, definition };
        self.identifier_types
            .insert(name.to_string(), constant_type);
        self.constants.insert(name.to_string(), info);
        self.constant_names.push(name.to_string());
        id
    }

    // Data types that come from type parameters get removed when they go out of scope.
    pub fn remove_data_type(&mut self, name: &str) {
        if !self.type_names.contains_key(name) {
            panic!("removing data type {} which is already not present", name);
        }
        self.type_names.remove(name);
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for parsing Expressions and similar structures
    ////////////////////////////////////////////////////////////////////////////////

    // Return an error if the types don't match.
    // This doesn't do full polymorphic typechecking, but it will fail if there's no
    // way that the types can match, for example if a function expects T -> Nat and
    // the value provided is Nat.
    // actual_type should be non-generic here.
    // expected_type can be generic.
    pub fn check_type<'a>(
        &self,
        error_token: &Token,
        expected_type: Option<&AcornType>,
        actual_type: &AcornType,
    ) -> Result<()> {
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

    // Evaluates an expression that represents a type.
    pub fn evaluate_type(&self, expression: &Expression) -> Result<AcornType> {
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
                        arg_types.push(self.evaluate_type(arg_expr)?);
                    }
                    let return_type = self.evaluate_type(right)?;
                    let function_type = FunctionType {
                        arg_types,
                        return_type: Box::new(return_type),
                    };
                    Ok(AcornType::Function(function_type))
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
            Expression::Grouping(_, e, _) => self.evaluate_type(e),
            Expression::Macro(token, _, _, _) => {
                Err(Error::new(token, "unexpected macro in type expression"))
            }
        }
    }

    // Parses a declaration.
    // Must be in the form of "<name> : <type expression>"
    // For example, "x: Nat" or "f: Nat -> bool".
    pub fn parse_declaration(&self, declaration: &Expression) -> Result<(String, AcornType)> {
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
                    let acorn_type = self.evaluate_type(right)?;
                    Ok((name, acorn_type))
                }
                _ => Err(Error::new(token, "expected a colon in this declaration")),
            },
            _ => Err(Error::new(declaration.token(), "expected a declaration")),
        }
    }

    // Parses a list of named argument declarations and adds them to the stack.
    pub fn bind_args<'a, I>(&mut self, declarations: I) -> Result<(Vec<String>, Vec<AcornType>)>
    where
        I: IntoIterator<Item = &'a Expression>,
    {
        let mut names = Vec::new();
        let mut types = Vec::new();
        for declaration in declarations {
            let (name, acorn_type) = self.parse_declaration(declaration)?;
            if self.identifier_types.contains_key(&name) {
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
            self.stack
                .insert(name.to_string(), self.stack.len() as AtomId);
            self.identifier_types
                .insert(name.to_string(), acorn_type.clone());
        }
        Ok((names, types))
    }

    // There should be a call to unbind_args for every call to bind_args.
    pub fn unbind_args(&mut self, names: &[String]) {
        for name in names {
            self.stack.remove(name);
            self.identifier_types.remove(name);
        }
    }

    // A value expression could be either a value or an argument list.
    // We mutate the environment to account for the stack, so self has to be mut.
    // It might be better to use some fancier data structure.
    // Returns the value along with its type.
    pub fn evaluate_value(
        &mut self,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> Result<AcornValue> {
        match expression {
            Expression::Identifier(token) => {
                if token.token_type == TokenType::Axiom {
                    panic!("axiomatic values should be handled elsewhere");
                }

                if token.token_type.is_macro() {
                    return Err(Error::new(token, "macros cannot be used as values"));
                }

                // Check the type for this identifier
                let return_type = match self.identifier_types.get(token.text()) {
                    Some(t) => {
                        self.check_type(token, expected_type, t)?;
                        t.clone()
                    }
                    None => {
                        return Err(Error::new(
                            token,
                            &format!("the name {} is unbound", token.text()),
                        ));
                    }
                };

                // Figure out the value for this identifier
                if let Some(acorn_value) = self.get_constant_value(token.text()) {
                    Ok(acorn_value)
                } else if let Some(stack_index) = self.stack.get(token.text()) {
                    Ok(AcornValue::Variable(*stack_index, return_type.clone()))
                } else {
                    Err(Error::new(
                        token,
                        "interpreter bug: name is bound but it has no value and is not on the stack",
                    ))
                }
            }
            Expression::Unary(token, expr) => match token.token_type {
                TokenType::Exclam => {
                    self.check_type(token, expected_type, &AcornType::Bool)?;
                    let value = self.evaluate_value(expr, Some(&AcornType::Bool))?;
                    Ok(AcornValue::Not(Box::new(value)))
                }
                _ => Err(Error::new(
                    token,
                    "unexpected unary operator in value expression",
                )),
            },
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow => {
                    self.check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value(left, Some(&AcornType::Bool))?;
                    let right_value = self.evaluate_value(right, Some(&AcornType::Bool))?;
                    Ok(AcornValue::Implies(
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::Equals => {
                    self.check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value(left, None)?;
                    let right_value = self.evaluate_value(right, Some(&left_value.get_type()))?;
                    Ok(AcornValue::Equals(
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::NotEquals => {
                    self.check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value(left, None)?;
                    let right_value = self.evaluate_value(right, Some(&left_value.get_type()))?;
                    Ok(AcornValue::NotEquals(
                        Box::new(left_value),
                        Box::new(right_value),
                    ))
                }
                TokenType::Ampersand => {
                    self.check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value(left, Some(&AcornType::Bool))?;
                    let right_value = self.evaluate_value(right, Some(&AcornType::Bool))?;
                    Ok(AcornValue::And(Box::new(left_value), Box::new(right_value)))
                }
                TokenType::Pipe => {
                    self.check_type(token, expected_type, &AcornType::Bool)?;
                    let left_value = self.evaluate_value(left, Some(&AcornType::Bool))?;
                    let right_value = self.evaluate_value(right, Some(&AcornType::Bool))?;
                    Ok(AcornValue::Or(Box::new(left_value), Box::new(right_value)))
                }
                TokenType::Dot => {
                    let name = expression.concatenate_dots()?;
                    if let Some(acorn_value) = self.get_constant_value(&name) {
                        Ok(acorn_value)
                    } else {
                        return Err(Error::new(token, &format!("the name {} is unbound", name)));
                    }
                }
                _ => Err(Error::new(
                    token,
                    "unhandled binary operator in value expression",
                )),
            },
            Expression::Apply(function_expr, args_expr) => {
                let function = self.evaluate_value(function_expr, None)?;
                let function_type = function.get_type();

                let function_type = match function_type {
                    AcornType::Function(f) => f,
                    _ => {
                        return Err(Error::new(function_expr.token(), "expected a function"));
                    }
                };

                let arg_exprs = args_expr.flatten_list(false)?;

                if function_type.arg_types.len() != arg_exprs.len() {
                    return Err(Error::new(
                        args_expr.token(),
                        &format!(
                            "expected {} arguments, but got {}",
                            function_type.arg_types.len(),
                            arg_exprs.len()
                        ),
                    ));
                }

                let mut args = vec![];
                let mut template_types = vec![];
                for (i, arg_expr) in arg_exprs.iter().enumerate() {
                    let arg_type = &function_type.arg_types[i];
                    let arg_value = self.evaluate_value(arg_expr, None)?;
                    if !arg_type.match_monomorph(&arg_value.get_type(), &mut template_types) {
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

                if template_types.is_empty() {
                    self.check_type(
                        function_expr.token(),
                        expected_type,
                        &*function_type.return_type,
                    )?;
                    return Ok(AcornValue::Application(FunctionApplication {
                        function: Box::new(function),
                        args,
                    }));
                }

                // Templated functions have to just be constants
                let (c_namespace, c_id, c_name, c_type) =
                    if let AcornValue::Constant(c_namespace, c_id, c_name, c_type) = function {
                        (c_namespace, c_id, c_name, c_type)
                    } else {
                        return Err(Error::new(
                            function_expr.token(),
                            "a non-constant function cannot be a template",
                        ));
                    };

                // Check to make sure all of the template types were inferred
                let mut inst_types = vec![];
                for t in template_types {
                    match t {
                        Some(t) => inst_types.push(t),
                        None => {
                            return Err(Error::new(
                                function_expr.token(),
                                "cannot infer types for this generic function application",
                            ));
                        }
                    }
                }

                if expected_type.is_some() {
                    // Check the return type
                    let return_type = function_type.return_type.monomorphize(&inst_types);
                    self.check_type(function_expr.token(), expected_type, &return_type)?;
                }

                let monomorph =
                    AcornValue::Monomorph(c_namespace, c_id, c_name, c_type, inst_types);
                Ok(AcornValue::Application(FunctionApplication {
                    function: Box::new(monomorph),
                    args,
                }))
            }
            Expression::Grouping(_, e, _) => self.evaluate_value(e, expected_type),
            Expression::Macro(token, args_expr, body, _) => {
                let macro_args = args_expr.flatten_list(false)?;
                if macro_args.len() < 1 {
                    return Err(Error::new(
                        args_expr.token(),
                        "macros must have at least one argument",
                    ));
                }
                let (arg_names, arg_types) = self.bind_args(macro_args)?;
                let expected_type = match token.token_type {
                    TokenType::ForAll => Some(&AcornType::Bool),
                    TokenType::Exists => Some(&AcornType::Bool),
                    _ => None,
                };
                let ret_val = match self.evaluate_value(body, expected_type) {
                    Ok(value) => match token.token_type {
                        TokenType::ForAll => Ok(AcornValue::ForAll(arg_types, Box::new(value))),
                        TokenType::Exists => Ok(AcornValue::Exists(arg_types, Box::new(value))),
                        TokenType::Function => Ok(AcornValue::Lambda(arg_types, Box::new(value))),
                        _ => Err(Error::new(token, "expected a macro identifier token")),
                    },
                    Err(e) => Err(e),
                };
                self.unbind_args(&arg_names);
                ret_val
            }
        }
    }

    // Evaluate an expression that is scoped within braces.
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
        type_param_tokens: &[Token],
        arg_exprs: &[Expression],
        value_type_expr: Option<&Expression>,
        value_expr: &Expression,
    ) -> Result<(
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
        let (arg_names, specific_arg_types) = self.bind_args(arg_exprs)?;

        // Check for possible errors in the specification.
        // Each type has to be used by some argument so that we know how to
        // monomorphize the template.
        for (i, type_param_name) in type_param_names.iter().enumerate() {
            if !specific_arg_types
                .iter()
                .any(|a| a.refers_to(self.namespace, &type_param_name))
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
            Some(e) => self.evaluate_type(e)?,
            None => AcornType::Bool,
        };
        let generic_value = if value_expr.token().token_type == TokenType::Axiom {
            None
        } else {
            let specific_value = self.evaluate_value(value_expr, Some(&specific_value_type))?;
            let generic_value = self.genericize(&type_param_names, specific_value);
            Some(generic_value)
        };

        // Genericize everything before returning it
        let generic_value_type = self.genericize_type(&type_param_names, specific_value_type);
        let generic_arg_types = specific_arg_types
            .into_iter()
            .map(|t| self.genericize_type(&type_param_names, t))
            .collect();

        // Reset the bindings
        self.unbind_args(&arg_names);
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

    // type_params contains a list of types that should look like opaque data types to us.
    // genericize converts this value to a polymorphic one, by replacing any types in
    // this list with AcornType::Generic values.
    // Do this before unbind_type_params.
    pub fn genericize(&self, type_params: &[String], value: AcornValue) -> AcornValue {
        let mut value = value;
        for (generic_type, name) in type_params.iter().enumerate() {
            value = value.genericize(self.namespace, name, generic_type);
        }
        value
    }

    fn genericize_type(&self, type_params: &[String], specific_type: AcornType) -> AcornType {
        let mut answer = specific_type;
        for (generic_type, name) in type_params.iter().enumerate() {
            answer = answer.genericize(self.namespace, name, generic_type);
        }
        answer
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for converting things to displayable strings.
    ////////////////////////////////////////////////////////////////////////////////

    pub fn atom_str(&self, atom: &Atom) -> String {
        match atom {
            Atom::True => "true".to_string(),
            Atom::Constant(i) => {
                if *i as usize >= self.constant_names.len() {
                    panic!(
                        "atom is c{} but we have only {} constants",
                        i,
                        self.constant_names.len()
                    );
                }
                self.constant_names[*i as usize].to_string()
            }
            Atom::Skolem(i) => format!("s{}", i),
            Atom::Monomorph(i) => format!("m{}", i),
            Atom::Synthetic(i) => format!("p{}", i),
            Atom::Variable(i) => format!("x{}", i),
        }
    }

    fn macro_str_stacked(
        &self,
        macro_name: &str,
        types: &Vec<AcornType>,
        value: &AcornValue,
        stack_size: usize,
    ) -> String {
        let parts: Vec<_> = types
            .iter()
            .enumerate()
            .map(|(i, t)| format!("x{}: {}", i + stack_size, t))
            .collect();
        let value_str = self.value_str_stacked(value, stack_size + types.len());
        format!("{}({}) {{ {} }}", macro_name, parts.join(", "), value_str)
    }

    fn value_str_stacked(&self, value: &AcornValue, stack_size: usize) -> String {
        match value {
            AcornValue::Atom(a) => self.atom_str(&a.atom),
            AcornValue::Variable(i, _) => format!("x{}", i),
            AcornValue::Constant(_, _, name, _) => name.to_string(),
            AcornValue::Application(app) => {
                let fn_name = self.value_str_stacked(&app.function, stack_size);
                let args: Vec<_> = app
                    .args
                    .iter()
                    .map(|a| self.value_str_stacked(a, stack_size))
                    .collect();
                format!("{}({})", fn_name, args.join(", "))
            }
            AcornValue::Implies(left, right) => format!(
                "({} -> {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::Equals(left, right) => format!(
                "({} = {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::NotEquals(left, right) => format!(
                "({} != {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::And(left, right) => format!(
                "({} & {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::Or(left, right) => format!(
                "({} | {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::ForAll(types, values) => {
                self.macro_str_stacked("forall", types, values, stack_size)
            }
            AcornValue::Exists(types, values) => {
                self.macro_str_stacked("exists", types, values, stack_size)
            }
            AcornValue::Not(subvalue) => {
                format!("!{}", self.value_str_stacked(subvalue, stack_size))
            }
            AcornValue::Lambda(types, values) => {
                self.macro_str_stacked("lambda", types, values, stack_size)
            }
            AcornValue::Monomorph(_, _, name, _, types) => {
                format!("{}<{}>", name, AcornType::types_to_str(&types))
            }
        }
    }

    pub fn value_str(&self, value: &AcornValue) -> String {
        self.value_str_stacked(value, 0)
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for testing.
    ////////////////////////////////////////////////////////////////////////////////

    pub fn assert_type_ok(&mut self, input: &str) {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let (expression, _) =
            Expression::parse(&mut tokens, false, |t| t == TokenType::NewLine).unwrap();
        match self.evaluate_type(&expression) {
            Ok(_) => {}
            Err(error) => panic!("Error evaluating type expression: {}", error),
        }
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
        assert!(self.evaluate_type(&expression).is_err());
    }

    // Check that the given name actually does have this type in the environment.
    pub fn expect_type(&self, name: &str, type_string: &str) {
        let env_type = match self.identifier_types.get(name) {
            Some(t) => t,
            None => panic!("{} not found", name),
        };
        assert_eq!(env_type.to_string(), type_string);
    }

    // Checks that the given constant id matches the given name
    pub fn expect_constant(&self, id: usize, name: &str) {
        let constant = match self.constant_names.get(id) {
            Some(c) => c,
            None => panic!("constant {} not found", id),
        };
        assert_eq!(constant, name);
        let info = match self.constants.get(name) {
            Some(info) => info,
            None => panic!(
                "inconsistency: c{} evalutes to {}, for which we have no info",
                id, name
            ),
        };
        assert_eq!(info.id, id as AtomId);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_env_types() {
        let mut b = BindingMap::new(FIRST_NORMAL);
        b.assert_type_ok("bool");
        b.assert_type_ok("bool -> bool");
        b.assert_type_ok("bool -> (bool -> bool)");
        b.assert_type_ok("(bool -> bool) -> (bool -> bool)");
        b.assert_type_ok("(bool, bool) -> bool");
        b.assert_type_bad("bool, bool -> bool");
        b.assert_type_bad("(bool, bool)");
    }
}
