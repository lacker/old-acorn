use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::{AcornFunctionType, AcornType};
use crate::acorn_value::AcornValue;
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

    // Variables that have names and types
    declarations: HashMap<String, AcornType>,

    // Declared variables that also have values.
    values: HashMap<String, AcornValue>,
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
                    let function_type = AcornFunctionType {
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

    pub fn evaluate_value_expression(&mut self, expression: &Expression) -> Result<AcornValue> {
        match expression {
            Expression::Identifier(token) => {
                if token.token_type == TokenType::Axiom {
                    return Ok(self.new_axiomatic_value());
                }
                if let Some(acorn_value) = self.values.get(token.text) {
                    Ok(acorn_value.clone())
                } else {
                    Err(Error::new(token, "expected value name"))
                }
            }
            Expression::Unary(token, _) => Err(Error::new(
                token,
                "TODO: handle unary operator in value expression",
            )),
            Expression::Binary(token, _, _) => Err(Error::new(
                token,
                "TODO: handle binary operators in value expression",
            )),
            Expression::Apply(left, _) => Err(Error::new(
                left.token(),
                "TODO: handle function application in value expression",
            )),
            _ => Err(Error::new(
                expression.token(),
                "TODO: handle fallthrough case in value expression",
            )),
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
            Statement::Definition(ds) => match &ds.declaration {
                Expression::Binary(token, left, right) => match token.token_type {
                    TokenType::Colon => {
                        if left.token().token_type != TokenType::Identifier {
                            return Err(Error::new(
                                left.token(),
                                "expected an identifier in this declaration",
                            ));
                        }
                        let name = left.token().text.to_string();
                        if self.declarations.contains_key(&name) {
                            return Err(Error::new(
                                token,
                                "variable name already defined in this scope",
                            ));
                        }
                        let acorn_type = self.evaluate_type_expression(right)?;
                        if let Some(value_expr) = &ds.value {
                            let acorn_value = self.evaluate_value_expression(value_expr)?;
                            self.values.insert(name.clone(), acorn_value);
                        }
                        self.declarations.insert(name, acorn_type);
                        Ok(())
                    }
                    TokenType::RightArrow => {
                        panic!("TODO: handle function definitions")
                    }
                    _ => Err(Error::new(token, "invalid binary declaration")),
                },
                _ => Err(Error::new(
                    &ds.declaration.token(),
                    "invalid nonbinary declaration",
                )),
            },
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
    }
}
