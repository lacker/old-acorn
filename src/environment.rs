use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::{AcornType, FunctionType};
use crate::acorn_value::{AcornValue, FunctionApplication};
use crate::expression::Expression;
use crate::statement::Statement;
use crate::token::{Error, Result, TokenType};

pub struct Environment {
    // How many axiomatic types have been defined in this scope
    axiomatic_type_count: usize,

    // How many axiomatic values have been defined in this scope
    axiomatic_value_count: usize,

    // Types that are named in this scope
    named_types: HashMap<String, AcornType>,

    // Variables that have names and types.
    // Includes both variables defined on the stack and variables defined in a larger scope.
    declarations: HashMap<String, AcornType>,

    // Declared variables that also have values.
    values: HashMap<String, AcornValue>,

    // For variables on the stack, we keep track of their depth from the top.
    stack: HashMap<String, usize>,
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment {{\n")?;
        for (name, acorn_type) in &self.named_types {
            write!(f, "  typedef {}: {}\n", name, acorn_type)?;
        }
        for (name, acorn_type) in &self.declarations {
            write!(f, "  let {}: {}\n", name, acorn_type)?;
        }
        write!(f, "}}")
    }
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            axiomatic_type_count: 0,
            axiomatic_value_count: 0,
            named_types: HashMap::from([("bool".to_string(), AcornType::Bool)]),
            declarations: HashMap::new(),
            values: HashMap::new(),
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
        self.declarations.insert(name.to_string(), acorn_type);
    }

    fn pop_stack_variable(&mut self, name: &str) {
        self.stack.remove(name);
        self.declarations.remove(name);
    }

    // Evaluates an expression that we expect to be indicating either a type or an arg list
    pub fn evaluate_partial_type_expression(
        &mut self,
        expression: &Expression,
    ) -> Result<AcornType> {
        match expression {
            Expression::Identifier(token) => {
                if token.token_type == TokenType::Axiom {
                    return Ok(self.new_axiomatic_type());
                }
                if let Some(acorn_type) = self.named_types.get(token.text) {
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
                        args: left_type.into_arg_list(),
                        value: Box::new(right_type),
                    };
                    Ok(AcornType::Function(function_type))
                }
                TokenType::Comma => {
                    // Flatten the types on either side, assumed to be arg lists
                    let mut args = self.evaluate_partial_type_expression(left)?.into_arg_list();
                    args.extend(
                        self.evaluate_partial_type_expression(right)?
                            .into_arg_list(),
                    );
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
    pub fn evaluate_type_expression(&mut self, expression: &Expression) -> Result<AcornType> {
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

    // Could be either a value or an argument list
    pub fn evaluate_value_expression(&mut self, expression: &Expression) -> Result<AcornValue> {
        match expression {
            Expression::Identifier(token) => {
                if token.token_type == TokenType::Axiom {
                    return Ok(self.new_axiomatic_value());
                }
                if let Some(acorn_value) = self.values.get(token.text) {
                    Ok(acorn_value.clone())
                } else if let Some(stack_depth) = self.stack.get(token.text) {
                    let binding_depth = self.stack.len() - stack_depth - 1;
                    Ok(AcornValue::Binding(binding_depth))
                } else {
                    Err(Error::new(token, "name appears to be unbound"))
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
                        let mut args = self.evaluate_value_expression(left)?.into_arg_list();
                        args.extend(self.evaluate_value_expression(right)?.into_arg_list());
                        Ok(AcornValue::ArgList(args))
                    }
                    TokenType::RightArrow => {
                        let left_value = self.evaluate_value_expression(left)?;
                        let right_value = self.evaluate_value_expression(right)?;
                        Ok(AcornValue::Implies(
                            Box::new(left_value),
                            Box::new(right_value),
                        ))
                    }
                    TokenType::Equals => {
                        let left_value = self.evaluate_value_expression(left)?;
                        let right_value = self.evaluate_value_expression(right)?;
                        Ok(AcornValue::Equals(
                            Box::new(left_value),
                            Box::new(right_value),
                        ))
                    }
                    _ => Err(Error::new(
                        token,
                        "unhandled binary operator in value expression",
                    )),
                }
            }
            Expression::Apply(function_expr, args_expr) => {
                let function = Box::new(self.evaluate_value_expression(function_expr)?);
                let args = self.evaluate_value_expression(args_expr)?.into_arg_list();
                Ok(AcornValue::Application(FunctionApplication {
                    function,
                    args,
                }))
            }
            Expression::Grouping(e) => self.evaluate_value_expression(e),
        }
    }

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

    pub fn add_statement(&mut self, statement: &Statement) -> Result<()> {
        match statement {
            Statement::Type(ts) => {
                if self.named_types.contains_key(&ts.name.to_string()) {
                    return Err(Error::new(
                        &ts.type_expr.token(),
                        "type name already defined in this scope",
                    ));
                }
                let acorn_type = self.evaluate_type_expression(&ts.type_expr)?;
                self.named_types.insert(ts.name.to_string(), acorn_type);
                Ok(())
            }
            Statement::Definition(ds) => {
                let (name, acorn_type) = self.parse_declaration(&ds.declaration)?;
                if self.declarations.contains_key(&name) {
                    return Err(Error::new(
                        ds.declaration.token(),
                        "variable name already defined in this scope",
                    ));
                }
                if let Some(value_expr) = &ds.value {
                    let acorn_value = self.evaluate_value_expression(value_expr)?;
                    self.values.insert(name.clone(), acorn_value);
                }
                self.declarations.insert(name, acorn_type);
                Ok(())
            }
            Statement::Theorem(ts) => {
                // A theorem is two things. It's a function from a list of arguments to a boolean,
                // and it's implying that the function always returns true.
                // Here we are typechecking the function, but not proving it's always true.
                let mut names = Vec::new();
                let mut types = Vec::new();
                for arg in &ts.args {
                    let (name, acorn_type) = self.parse_declaration(arg)?;
                    if self.declarations.contains_key(&name) {
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
                let claim_value = self.evaluate_value_expression(&ts.claim)?;
                // TODO: validate that the claim is a boolean
                let theorem_value = AcornValue::Lambda(names.len(), Box::new(claim_value));
                let theorem_type = AcornType::Function(FunctionType {
                    args: types,
                    value: Box::new(AcornType::Bool),
                });
                self.declarations.insert(ts.name.to_string(), theorem_type);
                self.values.insert(ts.name.to_string(), theorem_value);

                // Reset the stack
                for name in names {
                    self.pop_stack_variable(&name);
                }
                Ok(())
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

    fn add_statement(env: &mut Environment, input: &str) {
        let statement = Statement::parse_str(input).unwrap();
        env.add_statement(&statement).unwrap();
    }

    fn bad_statement(env: &mut Environment, input: &str) {
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
        add_statement(&mut env, "type Nat: axiom");
        bad_statement(&mut env, "type Borf: Gorf");
        bad_statement(&mut env, "type Nat: axiom");

        add_statement(&mut env, "define 0: Nat = axiom");
        bad_statement(&mut env, "define Nat: 0 = axiom");
        bad_statement(&mut env, "define axiom: Nat = 0");

        add_statement(&mut env, "define Suc: Nat -> Nat = axiom");
        add_statement(&mut env, "define 1: Nat = Suc(0)");
        bad_statement(&mut env, "define 1: Nat = Suc(1)");
        bad_statement(&mut env, "define 1: Nat = Borf");

        add_statement(
            &mut env,
            "axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y",
        );
        bad_statement(&mut env, "axiom bad_types(x: Nat, y: Nat): x -> y");
    }
}
