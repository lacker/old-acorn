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

    // Evaluates an expression that we expect to be indicating a type
    pub fn evaluate_type_expression(&self, expression: &Expression) -> Result<AcornType> {
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
            Expression::Binary(token, left, right) => {
                if token.token_type != TokenType::RightArrow {
                    return Err(Error::new(
                        token,
                        "unexpected binary operator in type expression",
                    ));
                }
                let left_type = self.evaluate_type_expression(left)?;
                let right_type = self.evaluate_type_expression(right)?;
                let function_type = AcornFunctionType {
                    args: vec![left_type],
                    value: Box::new(right_type),
                };
                Ok(AcornType::Function(function_type))
            }
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

    fn expect_valid_type(env: &Environment, input: &str) {
        let tokens = scan(input).unwrap();
        let mut tokens = tokens.into_iter();
        let (expression, _) = parse_expression(&mut tokens, |t| t == TokenType::NewLine).unwrap();
        assert!(env.evaluate_type_expression(&expression).is_ok());
    }

    #[test]
    fn test_environment() {
        let env = Environment::new();
        expect_valid_type(&env, "bool");
        expect_valid_type(&env, "bool -> bool");
        expect_valid_type(&env, "bool -> (bool -> bool)");
        expect_valid_type(&env, "(bool -> bool) -> (bool -> bool)");
    }
}
