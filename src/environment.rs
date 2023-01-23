use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::{AcornFunctionType, AcornType};
use crate::expression::Expression;
use crate::token::{Error, Result, TokenType};

pub struct Environment {
    // Types that are named in this scope
    named_types: HashMap<String, AcornType>,

    // Variables that have names and types but not values
    declarations: HashMap<String, AcornType>,
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
            named_types: HashMap::from([("bool".to_string(), AcornType::Bool)]),
            declarations: HashMap::new(),
        }
    }

    // Evaluates an expression that we expect to be indicating either a type or an arg list
    pub fn evaluate_partial_type_expression(&self, expression: &Expression) -> Result<AcornType> {
        match expression {
            Expression::Identifier(token) => {
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
}

#[cfg(test)]
mod tests {
    use crate::{
        expression::parse_expression,
        token::{scan, TokenType},
    };

    use super::*;

    fn check_type(env: &Environment, input: &str) {
        let tokens = scan(input).unwrap();
        let mut tokens = tokens.into_iter();
        let (expression, _) =
            parse_expression(&mut tokens, false, |t| t == TokenType::NewLine).unwrap();
        match env.evaluate_type_expression(&expression) {
            Ok(_) => {}
            Err(error) => panic!("Error evaluating type expression: {}", error),
        }
    }

    fn check_bad_type(env: &Environment, input: &str) {
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
        let env = Environment::new();
        check_type(&env, "bool");
        check_type(&env, "bool -> bool");
        check_type(&env, "bool -> (bool -> bool)");
        check_type(&env, "(bool -> bool) -> (bool -> bool)");
        check_type(&env, "(bool, bool) -> bool");

        check_bad_type(&env, "bool, bool -> bool");
        check_bad_type(&env, "(bool, bool)");
    }
}
