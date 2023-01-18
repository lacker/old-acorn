use std::collections::HashMap;

use crate::acorn_type::AcornType;
use crate::expression::Expression;
use crate::token::{Error, Result};

pub struct Environment {
    declarations: HashMap<String, AcornType>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            declarations: HashMap::from([
                ("bool".to_string(), AcornType::Bool),
                ("nat".to_string(), AcornType::Nat),
                ("int".to_string(), AcornType::Int),
            ]),
        }
    }

    pub fn declare(&mut self, name: &str, acorn_type: AcornType) {
        self.declarations.insert(name.to_string(), acorn_type);
    }

    pub fn lookup(&self, name: &str) -> Option<&AcornType> {
        self.declarations.get(name)
    }

    pub fn typecheck(&self, expression: &Expression) -> Result<AcornType> {
        match expression {
            Expression::Identifier(token) => {
                if let Some(acorn_type) = self.lookup(token.text) {
                    Ok(acorn_type.clone())
                } else {
                    Err(Error::new(token, "undeclared identifier"))
                }
            }
            _ => {
                panic!("TODO: implement")
            }
        }
    }
}
