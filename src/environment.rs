use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::{AcornType, FunctionType};
use crate::acorn_value::{AcornValue, FunctionApplication};
use crate::atom::{Atom, TypedAtom};
use crate::expression::Expression;
use crate::statement::Statement;
use crate::token::{Error, Result, Token, TokenType};

// The Environment takes in a bunch of statements that make sense on their own,
// and combines them while doing typechecking and similar validation.
// It is not responsible for proving anything, or for logically manipulating
// proofs or values.
// It does not have to be efficient enough to run in the inner loop of the prover.
// It does keep track of names, with the goal of being able to show nice debug information
// for its values and types.
pub struct Environment {
    // The names of the axiomatic types that have been defined in this scope
    // The axiomatic types can be stored as ids that are indices into this vector.
    axiomatic_types: Vec<String>,

    // How many axiomatic values have been defined by name in this scope
    axiomatic_values: Vec<String>,

    // Maps the name of a type to the type object.
    typenames: HashMap<String, AcornType>,

    // Maps an identifier name to its type.
    types: HashMap<String, AcornType>,

    // Maps a name to its value.
    // Doesn't handle variables defined on the stack, only ones in the top level environment.
    values: HashMap<String, AcornValue>,

    // For variables defined on the stack, we keep track of their depth from the top.
    stack: HashMap<String, usize>,

    // All named theorems, in order.
    theorems: Vec<String>,
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment {{\n")?;
        for (name, acorn_type) in &self.typenames {
            write!(f, "  type {}: {}\n", name, self.type_str(acorn_type))?;
        }
        for (name, acorn_type) in &self.types {
            write!(f, "  let {}: {}\n", name, self.type_str(acorn_type))?;
        }
        write!(f, "}}")
    }
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            axiomatic_types: Vec::new(),
            axiomatic_values: Vec::new(),
            typenames: HashMap::from([("bool".to_string(), AcornType::Bool)]),
            types: HashMap::new(),
            values: HashMap::new(),
            stack: HashMap::new(),
            theorems: Vec::new(),
        }
    }

    fn add_axiomatic_type(&mut self, name: &str) {
        let axiomatic_type = AcornType::Axiomatic(self.axiomatic_types.len());
        self.axiomatic_types.push(name.to_string());
        self.typenames.insert(name.to_string(), axiomatic_type);
    }

    // This creates the next axiomatic value, but does not bind it to any name.
    fn next_axiomatic_value(&self, acorn_type: &AcornType) -> AcornValue {
        let atom = Atom::Axiomatic(self.axiomatic_values.len());
        AcornValue::Atom(TypedAtom {
            atom,
            acorn_type: acorn_type.clone(),
        })
    }

    fn push_stack_variable(&mut self, name: &str, acorn_type: AcornType) {
        self.stack.insert(name.to_string(), self.stack.len());
        self.types.insert(name.to_string(), acorn_type);
    }

    fn pop_stack_variable(&mut self, name: &str) {
        self.stack.remove(name);
        self.types.remove(name);
    }

    // This can be a new axiomatic value that is being bound for the first time,
    // in which case we track the name
    fn bind_name(&mut self, name: &str, value: AcornValue) {
        if self.types.contains_key(name) {
            panic!("name {} already bound to a type", name);
        }
        if self.values.contains_key(name) {
            panic!("name {} already bound to a value", name);
        }

        if let Some(i) = value.axiom_index() {
            if i == self.axiomatic_values.len() {
                self.axiomatic_values.push(name.to_string());
            } else if i > self.axiomatic_values.len() {
                panic!("axiom index {} unexpectedly high", i);
            }
        }
        self.types.insert(name.to_string(), value.get_type());
        self.values.insert(name.to_string(), value);
    }

    pub fn get_value(&self, name: &str) -> Option<&AcornValue> {
        self.values.get(name)
    }

    // Iterates through (name, value) pairs for all theorems in this environment.
    pub fn iter_theorems(&self) -> impl Iterator<Item = (&String, &AcornValue)> {
        self.theorems
            .iter()
            .map(move |name| (name, self.values.get(name).unwrap()))
    }

    pub fn type_list_str(&self, types: &[AcornType]) -> String {
        let mut s = "(".to_string();
        for (i, acorn_type) in types.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            s.push_str(&self.type_str(acorn_type));
        }
        s.push_str(")");
        s
    }

    pub fn type_str(&self, acorn_type: &AcornType) -> String {
        match acorn_type {
            AcornType::Bool => "bool".to_string(),
            AcornType::Axiomatic(i) => self.axiomatic_types[*i].to_string(),
            AcornType::Function(function_type) => {
                let s = if function_type.arg_types.len() > 1 {
                    self.type_list_str(&function_type.arg_types)
                } else {
                    self.type_str(&function_type.arg_types[0])
                };
                format!("{} -> {}", s, self.type_str(&function_type.return_type))
            }
            AcornType::ArgList(types) => self.type_list_str(types),
            AcornType::Macro => "macro".to_string(),
        }
    }

    fn atom_str(&self, atom: &Atom) -> String {
        match atom {
            Atom::Axiomatic(i) => self.axiomatic_values[*i].to_string(),
            Atom::Skolem(i) => format!("skolem{}", i),
            Atom::Reference(i) => format!("x{}", i),
        }
    }

    fn macro_str_stacked(
        &self,
        macro_name: &str,
        types: &Vec<AcornType>,
        value: &AcornValue,
        stack_size: usize,
    ) -> String {
        let mut parts: Vec<_> = types
            .iter()
            .enumerate()
            .map(|(i, t)| format!("x{}: {}", i + stack_size, self.type_str(t)))
            .collect();
        parts.push(self.value_str_stacked(value, stack_size + types.len()));
        format!("{}({})", macro_name, parts.join(", "))
    }

    fn value_str_stacked(&self, value: &AcornValue, stack_size: usize) -> String {
        match value {
            AcornValue::Atom(a) => self.atom_str(&a.atom),
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
            _ => format!("unhandled({:?})", value),
        }
    }

    pub fn value_str(&self, value: &AcornValue) -> String {
        self.value_str_stacked(value, 0)
    }

    fn check_type<'a>(
        &self,
        token: &Token<'a>,
        expected_type: Option<&AcornType>,
        actual_type: &AcornType,
    ) -> Result<'a, ()> {
        match expected_type {
            Some(e) => {
                if e != actual_type {
                    Err(Error::new(
                        token,
                        &format!(
                            "Expected type {}, but got {}",
                            self.type_str(e),
                            self.type_str(actual_type)
                        ),
                    ))
                } else {
                    Ok(())
                }
            }
            None => Ok(()),
        }
    }

    // Parses a list of named argument declarations and adds them to the stack.
    fn bind_args(
        &mut self,
        declarations: Vec<&Expression>,
    ) -> Result<(Vec<String>, Vec<AcornType>)> {
        let mut names = Vec::new();
        let mut types = Vec::new();
        for declaration in declarations {
            let (name, acorn_type) = self.parse_declaration(declaration)?;
            if self.types.contains_key(&name) {
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
            self.push_stack_variable(name, acorn_type.clone());
        }
        Ok((names, types))
    }

    // There should be a call to unbind_args for every call to bind_args.
    fn unbind_args(&mut self, names: Vec<String>) {
        for name in names {
            self.pop_stack_variable(&name);
        }
    }

    // Evaluates an expression that we expect to be indicating either a type or an arg list
    pub fn evaluate_partial_type_expression(&self, expression: &Expression) -> Result<AcornType> {
        match expression {
            Expression::Identifier(token) => {
                if token.token_type == TokenType::Axiom {
                    return Err(Error::new(
                        token,
                        "axiomatic types can only be created at the top level",
                    ));
                }
                if let Some(acorn_type) = self.typenames.get(token.text) {
                    Ok(acorn_type.clone())
                } else {
                    Err(Error::new(token, "expected type name"))
                }
            }
            Expression::Unary(token, _) => Err(Error::new(
                token,
                "unexpected unary operator in type expression",
            )),
            Expression::Binary(token, left, right) => match token.token_type {
                TokenType::RightArrow => {
                    let left_type = self.evaluate_partial_type_expression(left)?;
                    let right_type = self.evaluate_partial_type_expression(right)?;
                    let function_type = FunctionType {
                        arg_types: left_type.into_vec(),
                        return_type: Box::new(right_type),
                    };
                    Ok(AcornType::Function(function_type))
                }
                TokenType::Comma => {
                    // Flatten the types on either side, assumed to be arg lists
                    let mut args = self.evaluate_partial_type_expression(left)?.into_vec();
                    args.extend(self.evaluate_partial_type_expression(right)?.into_vec());
                    Ok(AcornType::ArgList(args))
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
            Expression::Grouping(e) => self.evaluate_partial_type_expression(e),
        }
    }

    // Evaluates an expression that indicates a complete type, not an arg list
    pub fn evaluate_type_expression(&self, expression: &Expression) -> Result<AcornType> {
        let acorn_type = self.evaluate_partial_type_expression(expression)?;
        if let AcornType::ArgList(_) = acorn_type {
            Err(Error::new(
                expression.token(),
                "expected a complete type, not arg list",
            ))
        } else {
            Ok(acorn_type)
        }
    }

    // A value expression could be either a value or an argument list.
    // We mutate the environment to account for the stack, so self has to be mut.
    // It might be better to use some fancier data structure.
    // Returns the value along with its type.
    pub fn evaluate_value_expression(
        &mut self,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> Result<AcornValue> {
        match expression {
            Expression::Identifier(token) => {
                if token.token_type == TokenType::Axiom {
                    return match expected_type {
                        Some(AcornType::ArgList(_)) => Err(Error::new(
                            token,
                            "axiomatic objects cannot be argument lists",
                        )),
                        Some(t) => Ok(self.next_axiomatic_value(&t)),
                        None => Err(Error::new(
                            token,
                            "axiomatic objects can only be created with known types",
                        )),
                    };
                }

                if token.token_type == TokenType::ForAll {
                    return Ok(AcornValue::ForAllMacro);
                }

                if token.token_type == TokenType::Exists {
                    return Ok(AcornValue::ExistsMacro);
                }

                // Check the type for this identifier
                let return_type = match self.types.get(token.text) {
                    Some(t) => {
                        self.check_type(token, expected_type, t)?;
                        t.clone()
                    }
                    None => {
                        return Err(Error::new(token, "name appears to be unbound"));
                    }
                };

                // Figure out the value for this identifier
                if let Some(acorn_value) = self.values.get(token.text) {
                    // We need to shift any stack variables that this value uses,
                    // so that they don't squash existing ones.
                    Ok(acorn_value.clone().insert_stack(0, self.stack.len()))
                } else if let Some(stack_index) = self.stack.get(token.text) {
                    let atom = Atom::Reference(*stack_index);
                    let typed_atom = TypedAtom {
                        atom,
                        acorn_type: return_type.clone(),
                    };
                    Ok(AcornValue::Atom(typed_atom))
                } else {
                    Err(Error::new(
                        token,
                        "name is bound but we can't find its type. this is an interpreter bug",
                    ))
                }
            }
            Expression::Unary(token, expr) => match token.token_type {
                TokenType::Exclam => {
                    self.check_type(token, expected_type, &AcornType::Bool)?;
                    let value = self.evaluate_value_expression(expr, Some(&AcornType::Bool))?;
                    Ok(AcornValue::Not(Box::new(value)))
                }
                _ => Err(Error::new(
                    token,
                    "unexpected unary operator in value expression",
                )),
            },
            Expression::Binary(token, left, right) => {
                match token.token_type {
                    TokenType::Comma => {
                        // Flatten the values on either side, assumed to be arg lists
                        let left_args = self.evaluate_value_expression(left, None)?;
                        let left_type = left_args.get_type();
                        let right_args = self.evaluate_value_expression(right, None)?;
                        let right_type = right_args.get_type();
                        let mut args = left_args.into_vec();
                        args.extend(right_args.into_vec());
                        let mut types = left_type.into_vec();
                        types.extend(right_type.into_vec());
                        Ok(AcornValue::ArgList(args))
                    }
                    TokenType::RightArrow => {
                        let left_value =
                            self.evaluate_value_expression(left, Some(&AcornType::Bool))?;
                        let right_value =
                            self.evaluate_value_expression(right, Some(&AcornType::Bool))?;
                        Ok(AcornValue::Implies(
                            Box::new(left_value),
                            Box::new(right_value),
                        ))
                    }
                    TokenType::Equals => {
                        let left_value = self.evaluate_value_expression(left, None)?;
                        let right_value =
                            self.evaluate_value_expression(right, Some(&left_value.get_type()))?;
                        Ok(AcornValue::Equals(
                            Box::new(left_value),
                            Box::new(right_value),
                        ))
                    }
                    TokenType::NotEquals => {
                        let left_value = self.evaluate_value_expression(left, None)?;

                        let right_value =
                            self.evaluate_value_expression(right, Some(&left_value.get_type()))?;
                        Ok(AcornValue::NotEquals(
                            Box::new(left_value),
                            Box::new(right_value),
                        ))
                    }
                    TokenType::Ampersand => {
                        let left_value =
                            self.evaluate_value_expression(left, Some(&AcornType::Bool))?;
                        let right_value =
                            self.evaluate_value_expression(right, Some(&AcornType::Bool))?;
                        Ok(AcornValue::And(Box::new(left_value), Box::new(right_value)))
                    }
                    TokenType::Pipe => {
                        let left_value =
                            self.evaluate_value_expression(left, Some(&AcornType::Bool))?;
                        let right_value =
                            self.evaluate_value_expression(right, Some(&AcornType::Bool))?;
                        Ok(AcornValue::Or(Box::new(left_value), Box::new(right_value)))
                    }
                    _ => Err(Error::new(
                        token,
                        "unhandled binary operator in value expression",
                    )),
                }
            }
            Expression::Apply(function_expr, args_expr) => {
                let function = self.evaluate_value_expression(function_expr, None)?;
                let function_type = function.get_type();

                if function_type == AcornType::Macro {
                    let mut macro_args = args_expr.flatten_arg_list();
                    if macro_args.len() < 2 {
                        return Err(Error::new(
                            args_expr.token(),
                            "quantifier macros must have at least two arguments",
                        ));
                    }
                    let body = macro_args.pop().unwrap();
                    let (arg_names, arg_types) = self.bind_args(macro_args)?;

                    let ret_val = match self.evaluate_value_expression(body, Some(&AcornType::Bool))
                    {
                        Ok(value) => match function {
                            AcornValue::ForAllMacro => {
                                Ok(AcornValue::ForAll(arg_types, Box::new(value)))
                            }
                            AcornValue::ExistsMacro => {
                                Ok(AcornValue::Exists(arg_types, Box::new(value)))
                            }
                            _ => Err(Error::new(function_expr.token(), "expected a macro")),
                        },
                        Err(e) => Err(e),
                    };
                    self.unbind_args(arg_names);
                    return ret_val;
                }

                let function_type = match function_type {
                    AcornType::Function(f) => f,
                    _ => {
                        return Err(Error::new(function_expr.token(), "expected a function"));
                    }
                };
                self.check_type(
                    function_expr.token(),
                    expected_type,
                    &*function_type.return_type,
                )?;

                let args = self.evaluate_value_expression(args_expr, None)?;
                let args_type = args.get_type();

                self.check_type(
                    args_expr.token(),
                    Some(&AcornType::ArgList(function_type.arg_types)),
                    &args_type.into_arg_list(),
                )?;

                Ok(AcornValue::Application(FunctionApplication {
                    function: Box::new(function),
                    args: args.into_vec(),
                }))
            }
            Expression::Grouping(e) => self.evaluate_value_expression(e, expected_type),
        }
    }

    // Parses the "x: Nat" sort of declaration.
    fn parse_declaration(&self, declaration: &Expression) -> Result<(String, AcornType)> {
        match declaration {
            Expression::Binary(token, left, right) => match token.token_type {
                TokenType::Colon => {
                    if left.token().token_type != TokenType::Identifier {
                        return Err(Error::new(
                            left.token(),
                            "expected an identifier in this declaration",
                        ));
                    }
                    let name = left.token().text.to_string();
                    let acorn_type = self.evaluate_type_expression(right)?;
                    Ok((name, acorn_type))
                }
                _ => Err(Error::new(token, "expected a colon in this declaration")),
            },
            _ => Err(Error::new(declaration.token(), "expected a declaration")),
        }
    }

    // Handle function definitions with named arguments.
    // "declaration" is something like:
    //   add(a: Nat, b:Nat) -> Nat
    // "body" is something like:
    //   a + b
    // This doesn't bind the function name into the environment, but it does mutate the environment
    // to use the stack.
    // Returns the name of the function and the value of the function.
    fn define_function(
        &mut self,
        declaration: &Expression,
        body: &Expression,
    ) -> Result<(String, AcornValue)> {
        let (fn_appl, ret_type) = match declaration {
            Expression::Binary(token, left, right) => match token.token_type {
                TokenType::RightArrow => {
                    let ret_type = self.evaluate_type_expression(right)?;
                    (&**left, ret_type)
                }
                _ => return Err(Error::new(token, "expected a right arrow here")),
            },
            _ => {
                return Err(Error::new(
                    declaration.token(),
                    "expected a function declaration",
                ))
            }
        };

        let (fn_name, arg_list) = match fn_appl {
            Expression::Apply(ident, arg_list) => {
                if ident.token().token_type != TokenType::Identifier {
                    return Err(Error::new(
                        ident.token(),
                        "expected an identifier in this function declaration",
                    ));
                }
                let name = ident.token().text.to_string();
                if self.types.contains_key(&name) {
                    return Err(Error::new(
                        ident.token(),
                        "function name already defined in this scope",
                    ));
                }
                (name, &**arg_list)
            }
            _ => {
                return Err(Error::new(
                    fn_appl.token(),
                    "expected a function declaration",
                ))
            }
        };

        let (arg_names, arg_types) = self.bind_args(arg_list.flatten_arg_list())?;

        let ret_val = if body.token().token_type == TokenType::Axiom {
            let new_axiom_type = AcornType::Function(FunctionType {
                arg_types: arg_types.clone(),
                return_type: Box::new(ret_type.clone()),
            });
            let fn_value = self.next_axiomatic_value(&new_axiom_type);
            Ok((fn_name, fn_value))
        } else {
            match self.evaluate_value_expression(body, Some(&ret_type)) {
                Ok(value) => {
                    let fn_value = AcornValue::Lambda(arg_types, Box::new(value));
                    Ok((fn_name, fn_value))
                }
                Err(e) => Err(e),
            }
        };

        self.unbind_args(arg_names);

        ret_val
    }

    pub fn add_statement(&mut self, statement: &Statement) -> Result<()> {
        match statement {
            Statement::Type(ts) => {
                if self.typenames.contains_key(&ts.name.to_string()) {
                    return Err(Error::new(
                        &ts.type_expr.token(),
                        "type name already defined in this scope",
                    ));
                }
                if ts.type_expr.token().token_type == TokenType::Axiom {
                    self.add_axiomatic_type(ts.name);
                } else {
                    let acorn_type = self.evaluate_type_expression(&ts.type_expr)?;
                    self.typenames.insert(ts.name.to_string(), acorn_type);
                };
                Ok(())
            }
            Statement::Definition(ds) => match ds.declaration.token().token_type {
                TokenType::Colon => {
                    let (name, acorn_type) = self.parse_declaration(&ds.declaration)?;
                    if self.types.contains_key(&name) {
                        return Err(Error::new(
                            ds.declaration.token(),
                            "variable name already defined in this scope",
                        ));
                    }
                    let acorn_value = if let Some(value_expr) = &ds.value {
                        self.evaluate_value_expression(value_expr, Some(&acorn_type))?
                    } else {
                        panic!("TODO: handle definitions without values");
                    };
                    self.bind_name(&name, acorn_value);
                    Ok(())
                }
                TokenType::RightArrow => {
                    let value = match &ds.value {
                        Some(v) => v,
                        None => {
                            return Err(Error::new(
                                ds.declaration.token(),
                                "expected a value in this definition",
                            ));
                        }
                    };
                    let (name, acorn_value) = self.define_function(&ds.declaration, value)?;
                    self.bind_name(&name, acorn_value);
                    Ok(())
                }
                _ => Err(Error::new(
                    ds.declaration.token(),
                    "unexpected top-level token in declaration",
                )),
            },
            Statement::Theorem(ts) => {
                // A theorem has two parts. It's a list of arguments that are being universally
                // quantified, and a boolean expression representing a claim of things that are true.
                // The value of the theorem is a ForAll expression representing its claim.
                let (arg_names, arg_types) = self.bind_args(ts.args.iter().collect())?;

                // Handle the claim
                let ret_val =
                    match self.evaluate_value_expression(&ts.claim, Some(&AcornType::Bool)) {
                        Ok(claim_value) => {
                            let theorem_value =
                                AcornValue::ForAll(arg_types.clone(), Box::new(claim_value));
                            self.bind_name(&ts.name, theorem_value);
                            self.theorems.push(ts.name.to_string());
                            Ok(())
                        }
                        Err(e) => Err(e),
                    };

                self.unbind_args(arg_names);

                ret_val
            }
            _ => panic!("TODO"),
        }
    }

    // Adds a possibly multi-line statement to the environment
    pub fn add(&mut self, input: &str) {
        let tokens = Token::scan(input).unwrap();
        let mut tokens = tokens.into_iter().peekable();
        while let Some(statement) = Statement::parse(&mut tokens).unwrap() {
            if let Err(e) = self.add_statement(&statement) {
                panic!("\nerror adding statement:\n{}\n{}", statement, e);
            }
        }
    }

    #[cfg(test)]
    fn assert_type_ok(&mut self, input: &str) {
        let tokens = Token::scan(input).unwrap();
        let mut tokens = tokens.into_iter();
        let (expression, _) =
            Expression::parse(&mut tokens, false, |t| t == TokenType::NewLine).unwrap();
        match self.evaluate_type_expression(&expression) {
            Ok(_) => {}
            Err(error) => panic!("Error evaluating type expression: {}", error),
        }
    }

    #[cfg(test)]
    fn assert_type_bad(&mut self, input: &str) {
        let tokens = Token::scan(input).unwrap();
        let mut tokens = tokens.into_iter();
        let expression = match Expression::parse(&mut tokens, false, |t| t == TokenType::NewLine) {
            Ok((expression, _)) => expression,
            Err(_) => {
                // We expect a bad type so this is fine
                return;
            }
        };
        assert!(self.evaluate_type_expression(&expression).is_err());
    }

    // Expects the given line to be bad
    #[cfg(test)]
    fn bad(&mut self, input: &str) {
        let statement = Statement::parse_str(input).unwrap();
        assert!(
            self.add_statement(&statement).is_err(),
            "expected error in: {}",
            input
        );
    }

    // Check that the given name actually does have this type in the environment.
    #[cfg(test)]
    fn typecheck(&mut self, name: &str, type_string: &str) {
        let env_type = match self.types.get(name) {
            Some(t) => t,
            None => panic!("{} not found in environment", name),
        };
        assert_eq!(self.type_str(env_type), type_string);
    }

    // Check that the given name has this normalized value in the environment
    #[cfg(test)]
    fn valuecheck(&mut self, name: &str, value_string: &str) {
        let env_value = match self.values.get(name) {
            Some(t) => t,
            None => panic!("{} not found in environment", name),
        };
        assert_eq!(self.value_str(env_value), value_string);
    }

    // Check the name of the given axiomatic value
    #[cfg(test)]
    pub fn axiomcheck(&mut self, id: usize, name: &str) {
        let axiom = match self.axiomatic_values.get(id) {
            Some(axiom) => axiom,
            None => panic!("axiom {} not found in environment", id),
        };
        assert_eq!(axiom, name);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_env_types() {
        let mut env = Environment::new();
        env.assert_type_ok("bool");
        env.assert_type_ok("bool -> bool");
        env.assert_type_ok("bool -> (bool -> bool)");
        env.assert_type_ok("(bool -> bool) -> (bool -> bool)");
        env.assert_type_ok("(bool, bool) -> bool");

        env.assert_type_bad("bool, bool -> bool");
        env.assert_type_bad("(bool, bool)");
    }

    #[test]
    fn test_fn_equality() {
        let mut env = Environment::new();
        env.add("define idb1(x: bool) -> bool = x");
        env.typecheck("idb1", "bool -> bool");
        env.add("define idb2(y: bool) -> bool = y");
        env.typecheck("idb2", "bool -> bool");
        assert_eq!(env.values["idb1"], env.values["idb2"]);

        env.add("type Nat: axiom");
        env.add("define idn1(x: Nat) -> Nat = x");
        env.typecheck("idn1", "Nat -> Nat");
        assert_ne!(env.values["idb1"], env.values["idn1"]);
    }

    #[test]
    fn test_forall_equality() {
        let mut env = Environment::new();
        env.add("define bsym1: bool = forall(x: bool, x = x)");
        env.typecheck("bsym1", "bool");
        env.add("define bsym2: bool = forall(y: bool, y = y)");
        env.typecheck("bsym2", "bool");
        assert_eq!(env.values["bsym1"], env.values["bsym2"]);

        env.add("type Nat: axiom");
        env.add("define nsym1: bool = forall(x: Nat, x = x)");
        env.typecheck("nsym1", "bool");
        assert_ne!(env.values["bsym1"], env.values["nsym1"]);
    }

    #[test]
    fn test_exists_equality() {
        let mut env = Environment::new();
        env.add("define bex1: bool = exists(x: bool, x = x)");
        env.add("define bex2: bool = exists(y: bool, y = y)");
        assert_eq!(env.values["bex1"], env.values["bex2"]);

        env.add("type Nat: axiom");
        env.add("define nex1: bool = exists(x: Nat, x = x)");
        assert_ne!(env.values["bex1"], env.values["nex1"]);
    }

    #[test]
    fn test_arg_binding() {
        let mut env = Environment::new();
        env.bad("define qux(x: bool, x: bool) -> bool = x");
        assert!(env.types.get("x").is_none());
        env.add("define qux(x: bool, y: bool) -> bool = x");
        env.typecheck("qux", "(bool, bool) -> bool");

        env.bad("theorem foo(x: bool, x: bool): x");
        assert!(env.types.get("x").is_none());
        env.add("theorem foo(x: bool, y: bool): x");
        env.typecheck("foo", "bool");

        env.bad("define bar: bool = forall(x: bool, x: bool, x = x)");
        assert!(env.types.get("x").is_none());
        env.add("define bar: bool = forall(x: bool, y: bool, x = x)");

        env.bad("define baz: bool = exists(x: bool, x: bool, x = x)");
        assert!(env.types.get("x").is_none());
        env.add("define baz: bool = exists(x: bool, y: bool, x = x)");
    }

    #[test]
    fn test_argless_theorem() {
        let mut env = Environment::new();
        env.add("define b: bool = axiom");
        env.add("theorem foo: b | !b");
        env.valuecheck("foo", "(b | !b)");
    }

    #[test]
    fn test_nested_binding() {
        let mut env = Environment::new();
        env.add("define p: bool = forall(b: bool, b | !b)");
        env.add("define q: bool = forall(b: bool, p)");
        env.valuecheck("q", "forall(x0: bool, forall(x1: bool, (x1 | !x1)))");
    }

    #[test]
    fn test_axiomatic_values_distinct() {
        let mut env = Environment::new();
        env.add("define x: bool = axiom");
        env.add("define y: bool = axiom");
        assert_ne!(env.values["x"], env.values["y"]);
    }

    #[test]
    fn test_nat_ac_piecewise() {
        let mut env = Environment::new();
        env.add("type Nat: axiom");

        env.bad("type Borf: Gorf");
        env.bad("type Nat: axiom");

        env.add("define 0: Nat = axiom");
        env.valuecheck("0", "0");

        env.bad("define Nat: 0 = axiom");
        env.bad("define axiom: Nat = 0");
        env.bad("define foo: bool = (axiom = axiom)");
        env.bad("define foo: bool = 0");

        env.add("define Suc: Nat -> Nat = axiom");
        env.valuecheck("Suc", "Suc");
        env.add("define 1: Nat = Suc(0)");
        env.valuecheck("1", "Suc(0)");

        env.bad("define 1: Nat = Suc(1)");
        env.bad("define 1: Nat = Borf");

        env.add("axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y");
        env.typecheck("suc_injective", "bool");
        env.valuecheck(
            "suc_injective",
            "forall(x0: Nat, x1: Nat, ((Suc(x0) = Suc(x1)) -> (x0 = x1)))",
        );

        env.bad("axiom bad_types(x: Nat, y: Nat): x -> y");

        // We don't want failed typechecks to leave the environment in a bad state
        assert!(!env.types.contains_key("x"));

        env.bad("define foo: bool = Suc(0)");
        env.bad("define foo: Nat = Suc(0 = 0)");
        env.bad("define foo: Nat = Suc(0, 0)");

        env.add("axiom suc_neq_zero(x: Nat): Suc(x) != 0");
        env.valuecheck("suc_neq_zero", "forall(x0: Nat, (Suc(x0) != 0))");

        assert!(env.typenames.contains_key("Nat"));
        assert!(!env.types.contains_key("Nat"));

        assert!(!env.typenames.contains_key("0"));
        assert!(env.types.contains_key("0"));

        assert!(!env.typenames.contains_key("1"));
        assert!(env.types.contains_key("1"));

        assert!(!env.typenames.contains_key("Suc"));
        assert!(env.types.contains_key("Suc"));

        assert!(!env.typenames.contains_key("foo"));
        assert!(!env.types.contains_key("foo"));

        env.add(
            "axiom induction(f: Nat -> bool, n: Nat):
            f(0) & forall(k: Nat, f(k) -> f(Suc(k))) -> f(n)",
        );
        env.valuecheck("induction", "forall(x0: Nat -> bool, x1: Nat, ((x0(0) & forall(x2: Nat, (x0(x2) -> x0(Suc(x2))))) -> x0(x1)))");

        env.bad("theorem foo(x: Nat): 0");
        env.bad("theorem foo(x: Nat): forall(0, 0)");
        env.bad("theorem foo(x: Nat): forall(y: Nat, 0)");

        env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom");
        env.typecheck("recursion", "(Nat -> Nat, Nat, Nat) -> Nat");

        env.bad("theorem foo(x: Nat): forall(0: Nat, 0 = 0)");

        env.add("axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a");
        env.add(
            "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat):
            recursion(f, a, Suc(n)) = f(recursion(f, a, n))",
        );

        env.add("define add(a: Nat, b: Nat) -> Nat = recursion(Suc, a, b)");
        env.typecheck("add", "(Nat, Nat) -> Nat");

        env.add("theorem add_zero_right(a: Nat): add(a, 0) = a");
        env.add("theorem add_zero_left(a: Nat): add(0, a) = a");
        env.add("theorem add_suc_right(a: Nat, b: Nat): add(a, Suc(b)) = Suc(add(a, b))");
        env.add("theorem add_suc_left(a: Nat, b: Nat): add(Suc(a), b) = Suc(add(a, b))");
        env.add("theorem add_comm(a: Nat, b: Nat): add(a, b) = add(b, a)");
        env.add("theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c))");
        env.add("theorem not_suc_eq_zero(x: Nat): !(Suc(x) = 0)");
    }

    #[test]
    fn test_nat_ac_together() {
        let mut env = Environment::new();
        env.add(
            r#"
// The axioms of Peano arithmetic.
        
type Nat: axiom

define 0: Nat = axiom

define Suc: Nat -> Nat = axiom
define 1: Nat = Suc(0)

axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y

axiom suc_neq_zero(x: Nat): Suc(x) != 0

axiom induction(f: Nat -> bool): f(0) & forall(k: Nat, f(k) -> f(Suc(k))) -> forall(n: Nat, f(n))

// Ideally a and f would be templated rather than just Nat.
define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom
axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a
axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat): recursion(f, a, Suc(n)) = f(recursion(f, a, n))

define add(a: Nat, b: Nat) -> Nat = recursion(Suc, a, b)

// Now let's have some theorems.

theorem add_zero_right(a: Nat): add(a, 0) = a

theorem add_zero_left(a: Nat): add(0, a) = a

theorem add_suc_right(a: Nat, b: Nat): add(a, Suc(b)) = Suc(add(a, b))

theorem add_suc_left(a: Nat, b: Nat): add(Suc(a), b) = Suc(add(a, b))

theorem add_comm(a: Nat, b: Nat): add(a, b) = add(b, a)

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c))
"#,
        );
    }
}
