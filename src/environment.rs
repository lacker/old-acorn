use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::{AcornType, FunctionType};
use crate::acorn_value::{AcornValue, FunctionApplication};
use crate::expression::Expression;
use crate::statement::Statement;
use crate::token::{Error, Result, Token, TokenType};

pub struct Environment {
    // How many axiomatic types have been defined in this scope
    axiomatic_type_count: usize,

    // How many axiomatic values have been defined in this scope
    axiomatic_value_count: usize,

    // Maps the name of a type to the type object.
    typenames: HashMap<String, AcornType>,

    // Maps an identifier name to its type.
    types: HashMap<String, AcornType>,

    // Maps the name of a constant to its value.
    constants: HashMap<String, AcornValue>,

    // For variables defined on the stack, we keep track of their depth from the top.
    stack: HashMap<String, usize>,
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment {{\n")?;
        for (name, acorn_type) in &self.typenames {
            write!(f, "  type {}: {}\n", name, acorn_type)?;
        }
        for (name, acorn_type) in &self.types {
            write!(f, "  let {}: {}\n", name, acorn_type)?;
        }
        write!(f, "}}")
    }
}

fn check_type<'a>(
    token: &Token<'a>,
    expected_type: Option<&AcornType>,
    actual_type: &AcornType,
) -> Result<'a, ()> {
    match expected_type {
        Some(e) => {
            if e != actual_type {
                Err(Error::new(
                    token,
                    &format!("Expected type {}, but got {}", e, actual_type),
                ))
            } else {
                Ok(())
            }
        }
        None => Ok(()),
    }
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            axiomatic_type_count: 0,
            axiomatic_value_count: 0,
            typenames: HashMap::from([("bool".to_string(), AcornType::Bool)]),
            types: HashMap::new(),
            constants: HashMap::new(),
            stack: HashMap::new(),
        }
    }

    pub fn new_axiomatic_type(&mut self) -> AcornType {
        let axiomatic_type = AcornType::Axiomatic(self.axiomatic_type_count);
        self.axiomatic_type_count += 1;
        axiomatic_type
    }

    pub fn new_axiomatic_value(&mut self) -> AcornValue {
        let axiomatic_value = AcornValue::Axiomatic(self.axiomatic_value_count);
        self.axiomatic_value_count += 1;
        axiomatic_value
    }

    fn push_stack_variable(&mut self, name: &str, acorn_type: AcornType) {
        self.stack.insert(name.to_string(), self.stack.len());
        self.types.insert(name.to_string(), acorn_type);
    }

    fn pop_stack_variable(&mut self, name: &str) {
        self.stack.remove(name);
        self.types.remove(name);
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
                        args: left_type.into_vec(),
                        value: Box::new(right_type),
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
    // Returns the value along with its type.
    pub fn evaluate_value_expression(
        &mut self,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> Result<(AcornValue, AcornType)> {
        match expression {
            Expression::Identifier(token) => {
                if token.token_type == TokenType::Axiom {
                    return match expected_type {
                        Some(AcornType::ArgList(_)) => Err(Error::new(
                            token,
                            "axiomatic objects cannot be argument lists",
                        )),
                        Some(t) => Ok((self.new_axiomatic_value(), t.clone())),
                        None => Err(Error::new(
                            token,
                            "axiomatic objects can only be created with known types",
                        )),
                    };
                }

                if token.token_type == TokenType::ForAll {
                    return Ok((AcornValue::ForAllMacro, AcornType::Macro));
                }

                if token.token_type == TokenType::Exists {
                    return Ok((AcornValue::ExistsMacro, AcornType::Macro));
                }

                // Check the type for this identifier
                let return_type = match self.types.get(token.text) {
                    Some(t) => {
                        check_type(token, expected_type, t)?;
                        t.clone()
                    }
                    None => {
                        return Err(Error::new(token, "name appears to be unbound"));
                    }
                };

                // Figure out the value for this identifier
                if let Some(acorn_value) = self.constants.get(token.text) {
                    Ok((acorn_value.clone(), return_type))
                } else if let Some(stack_depth) = self.stack.get(token.text) {
                    let binding_depth = self.stack.len() - stack_depth - 1;
                    Ok((AcornValue::Binding(binding_depth), return_type))
                } else {
                    Err(Error::new(
                        token,
                        "name is bound but we can't find its type. this is an interpreter bug",
                    ))
                }
            }
            Expression::Unary(token, _) => Err(Error::new(
                token,
                "TODO: handle unary operator in value expression",
            )),
            Expression::Binary(token, left, right) => {
                match token.token_type {
                    TokenType::Comma => {
                        // Flatten the values on either side, assumed to be arg lists
                        let (left_args, left_types) = self.evaluate_value_expression(left, None)?;
                        let (right_args, right_types) =
                            self.evaluate_value_expression(right, None)?;
                        let mut args = left_args.into_vec();
                        args.extend(right_args.into_vec());
                        let mut types = left_types.into_vec();
                        types.extend(right_types.into_vec());
                        Ok((AcornValue::ArgList(args), AcornType::ArgList(types)))
                    }
                    TokenType::RightArrow => {
                        let (left_value, _) =
                            self.evaluate_value_expression(left, Some(&AcornType::Bool))?;
                        let (right_value, _) =
                            self.evaluate_value_expression(right, Some(&AcornType::Bool))?;
                        Ok((
                            AcornValue::Implies(Box::new(left_value), Box::new(right_value)),
                            AcornType::Bool,
                        ))
                    }
                    TokenType::Equals => {
                        let (left_value, left_type) = self.evaluate_value_expression(left, None)?;
                        let (right_value, _) =
                            self.evaluate_value_expression(right, Some(&left_type))?;
                        Ok((
                            AcornValue::Equals(Box::new(left_value), Box::new(right_value)),
                            AcornType::Bool,
                        ))
                    }
                    TokenType::NotEquals => {
                        let (left_value, left_type) = self.evaluate_value_expression(left, None)?;
                        let (right_value, _) =
                            self.evaluate_value_expression(right, Some(&left_type))?;
                        Ok((
                            AcornValue::NotEquals(Box::new(left_value), Box::new(right_value)),
                            AcornType::Bool,
                        ))
                    }
                    TokenType::Ampersand => {
                        let (left_value, _) =
                            self.evaluate_value_expression(left, Some(&AcornType::Bool))?;
                        let (right_value, _) =
                            self.evaluate_value_expression(right, Some(&AcornType::Bool))?;
                        Ok((
                            AcornValue::And(Box::new(left_value), Box::new(right_value)),
                            AcornType::Bool,
                        ))
                    }
                    TokenType::Pipe => {
                        let (left_value, _) =
                            self.evaluate_value_expression(left, Some(&AcornType::Bool))?;
                        let (right_value, _) =
                            self.evaluate_value_expression(right, Some(&AcornType::Bool))?;
                        Ok((
                            AcornValue::Or(Box::new(left_value), Box::new(right_value)),
                            AcornType::Bool,
                        ))
                    }
                    _ => Err(Error::new(
                        token,
                        "unhandled binary operator in value expression",
                    )),
                }
            }
            Expression::Apply(function_expr, args_expr) => {
                let (function, function_type) =
                    self.evaluate_value_expression(function_expr, None)?;

                if function_type == AcornType::Macro {
                    let (declaration, condition_expr) = args_expr.split_two_args()?;
                    let (name, acorn_type) = self.parse_declaration(declaration)?;
                    if self.types.contains_key(&name) {
                        return Err(Error::new(
                            declaration.token(),
                            "cannot redeclare a name in a macro",
                        ));
                    }
                    self.push_stack_variable(&name, acorn_type.clone());
                    let ret_val = match self
                        .evaluate_value_expression(condition_expr, Some(&AcornType::Bool))
                    {
                        Ok((value, _)) => match function {
                            AcornValue::ForAllMacro => {
                                Ok((AcornValue::ForAll(Box::new(value)), AcornType::Bool))
                            }
                            AcornValue::ExistsMacro => {
                                Ok((AcornValue::Exists(Box::new(value)), AcornType::Bool))
                            }
                            _ => Err(Error::new(function_expr.token(), "expected a macro")),
                        },
                        Err(e) => Err(e),
                    };
                    self.pop_stack_variable(&name);
                    return ret_val;
                }

                let function_type = match function_type {
                    AcornType::Function(f) => f,
                    _ => {
                        return Err(Error::new(function_expr.token(), "expected a function"));
                    }
                };
                check_type(function_expr.token(), expected_type, &*function_type.value)?;

                let (args, args_type) = self.evaluate_value_expression(args_expr, None)?;

                check_type(
                    args_expr.token(),
                    Some(&AcornType::ArgList(function_type.args)),
                    &args_type.into_arg_list(),
                )?;

                Ok((
                    AcornValue::Application(FunctionApplication {
                        function: Box::new(function),
                        args: args.into_vec(),
                    }),
                    *function_type.value,
                ))
            }
            Expression::Grouping(e) => self.evaluate_value_expression(e, expected_type),
        }
    }

    // Parses the "x: Nat" sort of declaration.
    fn parse_declaration(&mut self, declaration: &Expression) -> Result<(String, AcornType)> {
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

    // Parses a list of named arguments like "(x: Nat, f: Nat -> Nat)".
    fn parse_named_args(&mut self, arg_list: &Expression) -> Result<Vec<(String, AcornType)>> {
        let exprs = arg_list.flatten_arg_list();
        let mut declarations = Vec::new();
        for expr in exprs {
            let (name, acorn_type) = self.parse_declaration(expr)?;
            declarations.push((name, acorn_type));
        }
        Ok(declarations)
    }

    fn define_function(
        &mut self,
        declaration: &Expression,
        value: &Expression,
    ) -> Result<(String, AcornValue, AcornType)> {
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

        let named_args = self.parse_named_args(&arg_list)?;
        let named_args_len = named_args.len();
        for (name, arg_type) in &named_args {
            if self.types.contains_key(name) {
                return Err(Error::new(
                    declaration.token(),
                    &format!("argument name already defined in this scope: {}", name),
                ));
            }
            self.push_stack_variable(&name, arg_type.clone());
        }

        let ret_val = match self.evaluate_value_expression(value, Some(&ret_type)) {
            Ok((value, _)) => {
                let fn_value = AcornValue::Lambda(named_args_len, Box::new(value));
                let fn_type = AcornType::Function(FunctionType {
                    args: named_args.iter().map(|(_, t)| t.clone()).collect(),
                    value: Box::new(ret_type),
                });
                Ok((fn_name, fn_value, fn_type))
            }
            Err(e) => Err(e),
        };

        for (name, _) in &named_args {
            self.pop_stack_variable(&name);
        }

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
                let acorn_type = if ts.type_expr.token().token_type == TokenType::Axiom {
                    self.new_axiomatic_type()
                } else {
                    self.evaluate_type_expression(&ts.type_expr)?
                };
                self.typenames.insert(ts.name.to_string(), acorn_type);
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
                    if let Some(value_expr) = &ds.value {
                        let (acorn_value, _) =
                            self.evaluate_value_expression(value_expr, Some(&acorn_type))?;
                        self.constants.insert(name.clone(), acorn_value);
                    }
                    self.types.insert(name, acorn_type);
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
                    let (name, acorn_value, acorn_type) =
                        self.define_function(&ds.declaration, value)?;
                    self.constants.insert(name.clone(), acorn_value);
                    self.types.insert(name, acorn_type);
                    Ok(())
                }
                _ => Err(Error::new(
                    ds.declaration.token(),
                    "unexpected top-level token in declaration",
                )),
            },
            Statement::Theorem(ts) => {
                // A theorem is two things. It's a function from a list of arguments to a boolean,
                // and it's implying that the function always returns true.
                // Here we are typechecking the function, but not proving it's always true.
                let mut names = Vec::new();
                let mut types = Vec::new();
                for arg in &ts.args {
                    let (name, acorn_type) = self.parse_declaration(arg)?;
                    if self.types.contains_key(&name) {
                        return Err(Error::new(
                            arg.token(),
                            "variable name already defined in this scope",
                        ));
                    }
                    self.push_stack_variable(&name, acorn_type.clone());
                    names.push(name);
                    types.push(acorn_type);
                }

                // Handle the claim
                let ret_val = match self
                    .evaluate_value_expression(&ts.claim, Some(&AcornType::Bool))
                {
                    Ok((claim_value, _)) => {
                        let theorem_value = AcornValue::Lambda(names.len(), Box::new(claim_value));
                        let theorem_type = AcornType::Function(FunctionType {
                            args: types,
                            value: Box::new(AcornType::Bool),
                        });
                        self.types.insert(ts.name.to_string(), theorem_type);
                        self.constants.insert(ts.name.to_string(), theorem_value);
                        Ok(())
                    }
                    Err(e) => Err(e),
                };

                // Reset the stack
                for name in names {
                    self.pop_stack_variable(&name);
                }

                ret_val
            }
            _ => panic!("TODO"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        expression::parse_expression,
        token::{scan, TokenType},
    };

    use super::*;

    fn check_type(env: &mut Environment, input: &str) {
        let tokens = scan(input).unwrap();
        let mut tokens = tokens.into_iter();
        let (expression, _) =
            parse_expression(&mut tokens, false, |t| t == TokenType::NewLine).unwrap();
        match env.evaluate_type_expression(&expression) {
            Ok(_) => {}
            Err(error) => panic!("Error evaluating type expression: {}", error),
        }
    }

    fn check_bad_type(env: &mut Environment, input: &str) {
        let tokens = scan(input).unwrap();
        let mut tokens = tokens.into_iter();
        let expression = match parse_expression(&mut tokens, false, |t| t == TokenType::NewLine) {
            Ok((expression, _)) => expression,
            Err(_) => {
                // We expect a bad type so this is fine
                return;
            }
        };
        assert!(env.evaluate_type_expression(&expression).is_err());
    }

    #[test]
    fn test_env_types() {
        let mut env = Environment::new();
        check_type(&mut env, "bool");
        check_type(&mut env, "bool -> bool");
        check_type(&mut env, "bool -> (bool -> bool)");
        check_type(&mut env, "(bool -> bool) -> (bool -> bool)");
        check_type(&mut env, "(bool, bool) -> bool");

        check_bad_type(&mut env, "bool, bool -> bool");
        check_bad_type(&mut env, "(bool, bool)");
    }

    fn add(env: &mut Environment, input: &str) {
        let statement = Statement::parse_str(input).unwrap();
        if let Err(r) = env.add_statement(&statement) {
            panic!("Error adding statement:\n\n{}", r);
        }
    }

    fn bad(env: &mut Environment, input: &str) {
        let statement = Statement::parse_str(input).unwrap();
        assert!(
            env.add_statement(&statement).is_err(),
            "expected error in: {}",
            input
        );
    }

    #[test]
    fn test_nat_ac() {
        let mut env = Environment::new();
        add(&mut env, "type Nat: axiom");

        bad(&mut env, "type Borf: Gorf");
        bad(&mut env, "type Nat: axiom");

        add(&mut env, "define 0: Nat = axiom");

        bad(&mut env, "define Nat: 0 = axiom");
        bad(&mut env, "define axiom: Nat = 0");
        bad(&mut env, "define foo: bool = (axiom = axiom)");
        bad(&mut env, "define foo: bool = 0");

        add(&mut env, "define Suc: Nat -> Nat = axiom");
        add(&mut env, "define 1: Nat = Suc(0)");

        bad(&mut env, "define 1: Nat = Suc(1)");
        bad(&mut env, "define 1: Nat = Borf");

        add(
            &mut env,
            "axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y",
        );

        bad(&mut env, "axiom bad_types(x: Nat, y: Nat): x -> y");

        // We don't want failed typechecks to leave the environment in a bad state
        assert!(!env.types.contains_key("x"));

        bad(&mut env, "define foo: bool = Suc(0)");
        bad(&mut env, "define foo: Nat = Suc(0 = 0)");
        bad(&mut env, "define foo: Nat = Suc(0, 0)");

        add(&mut env, "axiom suc_neq_zero(x: Nat): Suc(x) != 0");

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

        add(&mut env,
        "axiom induction(f: Nat -> bool, n: Nat): f(0) & forall(k: Nat, f(k) -> f(Suc(k))) -> f(n)");

        bad(&mut env, "theorem foo(x: Nat): 0");
        bad(&mut env, "theorem foo(x: Nat): forall(0, 0)");
        bad(&mut env, "theorem foo(x: Nat): forall(y: Nat, 0)");

        add(
            &mut env,
            "define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom",
        );

        bad(&mut env, "theorem foo(x: Nat): forall(0: Nat, 0 = 0)");
    }
}
