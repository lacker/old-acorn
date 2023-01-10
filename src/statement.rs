use std::fmt;

use crate::expression::{parse_expression, Expression};
use crate::token::Token;

// For example, in:
//   let a: int = x + 2
// The first token is the variable name "a", the second is the type "int",
// and the expression is the "x + 2".
pub struct LetStatement<'a> {
    name: &'a str,
    type_name: &'a str,
    value: Option<Expression<'a>>,
}

// There are two keywords for theorems.
// "axiom" indicates theorems that are axiomatic.
// "theorem" is used for the vast majority of normal theorems.
// For example, in:
//   axiom foo(p, q): p -> (q -> p)
// axiomatic would be "true", the name is "foo", the args are p, q, and the claim is "p -> (q -> p)".
pub struct TheoremStatement<'a> {
    axiomatic: bool,
    name: &'a str,
    args: Vec<Expression<'a>>,
    claim: Expression<'a>,
}

// Def statements are the keyword "def" followed by an expression with an equals.
// For example, in:
//   def (p | q) = !p -> q
// the left expression is "p | q" and the right expression is "!p -> q".
pub struct DefStatement<'a> {
    left: Expression<'a>,
    right: Expression<'a>,
}

// Acorn is a statement-based language. There are several types.
pub enum Statement<'a> {
    Let(LetStatement<'a>),
    Theorem(TheoremStatement<'a>),
    Def(DefStatement<'a>),
}

impl fmt::Display for Statement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Let(ls) => {
                write!(f, "let {}: {}", ls.name, ls.type_name)?;
                if let Some(value) = &ls.value {
                    write!(f, " = {}", value)?;
                }
                Ok(())
            }

            Statement::Theorem(ts) => {
                if ts.axiomatic {
                    write!(f, "axiom")?;
                } else {
                    write!(f, "theorem")?;
                }
                write!(f, " {}", ts.name)?;
                if ts.args.len() > 0 {
                    write!(f, "(")?;
                    for (i, arg) in ts.args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, ")")?;
                }
                write!(f, ": {}", ts.claim)
            }

            Statement::Def(ds) => {
                write!(f, "def {} = {}", ds.left, ds.right)
            }
        }
    }
}

fn parse_theorem_statement<'a>(
    tokens: &mut impl Iterator<Item = &'a Token>,
    axiomatic: bool,
) -> TheoremStatement<'a> {
    let name = if let Some(Token::Identifier(name)) = tokens.next() {
        name
    } else {
        panic!("expected identifier after theorem");
    };
    let mut args = Vec::new();
    match tokens.next() {
        Some(Token::LeftParen) => {
            // Parse an arguments list
            loop {
                let (exp, terminator) =
                    parse_expression(tokens, |t| t == &Token::Comma || t == &Token::RightParen);
                args.push(exp);
                if terminator == &Token::RightParen {
                    if let Some(Token::Colon) = tokens.next() {
                        break;
                    } else {
                        panic!("expected colon after theorem arguments");
                    }
                }
            }
        }
        Some(Token::Colon) => {}
        t => panic!("unexpected token after theorem name: {:?}", t),
    }
    let (claim, _) = parse_expression(tokens, |t| t == &Token::NewLine);
    TheoremStatement {
        axiomatic,
        name,
        args,
        claim,
    }
}

// Parses a single statement from the provided tokens.
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
                    Some(Token::Equals) => {
                        let (exp, _) = parse_expression(tokens, |t| t == &Token::NewLine);
                        Some(exp)
                    }
                    Some(Token::NewLine) => None,
                    Some(token) => panic!("unexpected token after let type: {}", token),
                    None => panic!("unexpected end of input after let type"),
                };
                return Some(Statement::Let(LetStatement {
                    name,
                    type_name,
                    value,
                }));
            }
            Some(Token::Axiom) => {
                return Some(Statement::Theorem(parse_theorem_statement(tokens, true)));
            }
            Some(Token::Theorem) => {
                return Some(Statement::Theorem(parse_theorem_statement(tokens, false)));
            }
            Some(Token::Def) => {
                let (exp, _) = parse_expression(tokens, |t| t == &Token::NewLine);
                if let Expression::Binary(op, left, right) = exp {
                    if op == &Token::Equals {
                        return Some(Statement::Def(DefStatement {
                            left: *left,
                            right: *right,
                        }));
                    }
                }
                panic!("expected equals expression after def");
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
        expect_optimal("axiom simplification: p -> (q -> p)");
        expect_optimal("axiom distribution: (p -> (q -> r)) -> ((p -> q) -> (p -> r))");
        expect_optimal("axiom contraposition: (!p -> !q) -> (q -> p)");
        expect_optimal("axiom modus_ponens(p, p -> q): q");
        expect_optimal("theorem and_comm: p & q <-> q & p");
        expect_optimal("theorem and_assoc: (p & q) & r <-> p & (q & r)");
        expect_optimal("theorem or_comm: p | q <-> q | p");
        expect_optimal("theorem or_assoc: (p | q) | r <-> p | (q | r)");
    }
}
