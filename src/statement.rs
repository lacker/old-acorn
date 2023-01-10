use std::fmt;

use crate::expression::{parse_expression, Expression};
use crate::token::Token;

// Acorn is a statement-based language. There are several types.
pub enum Statement<'a> {
    // For example:
    //   let a: int = x + 2
    // The first token is the variable name "a", the second is the type "int",
    // and the expression is the "x + 2".
    Let(&'a str, &'a str, Option<Expression<'a>>),
}

impl fmt::Display for Statement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Let(name, type_name, value) => {
                write!(f, "let {}: {}", name, type_name)?;
                if let Some(value) = value {
                    write!(f, " = {}", value)?;
                }
                Ok(())
            }
        }
    }
}

// Parses a single statement from the provided tokens.
//
pub fn parse_statement<'a>(
    tokens: &mut impl Iterator<Item = &'a Token>,
    terminator: Option<&Token>,
) -> Option<Statement<'a>> {
    loop {
        match tokens.next() {
            Some(Token::NewLine) => continue,
            Some(Token::Let) => {
                let name = if let Some(Token::Identifier(name)) = tokens.next() {
                    name
                } else {
                    panic!("expected identifier after let");
                };
                if let Some(Token::Colon) = tokens.next() {
                } else {
                    panic!("expected colon after let identifier");
                }
                let type_name = if let Some(Token::Identifier(type_name)) = tokens.next() {
                    type_name
                } else {
                    panic!("expected identifier after let colon");
                };
                let value = match tokens.next() {
                    Some(Token::Equals) => Some(parse_expression(tokens, &Token::NewLine)),
                    Some(Token::NewLine) => None,
                    Some(token) => panic!("unexpected token after let type: {}", token),
                    None => panic!("unexpected end of input after let type"),
                };
                return Some(Statement::Let(name, type_name, value));
            }
            t => {
                if t == terminator {
                    return None;
                }
                panic!("unexpected token instead of a statement: {:?}", t)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::token::scan;

    use super::*;

    fn expect_optimal(input: &str) {
        let tokens = scan(input);
        let mut tokens = tokens.iter();
        let stmt = parse_statement(&mut tokens, None);
        let output = stmt.unwrap().to_string();
        assert_eq!(input, output);
    }

    #[test]
    fn test_statement_parsing() {
        expect_optimal("let p: bool");
        expect_optimal("let a: int = x + 2");
    }
}
