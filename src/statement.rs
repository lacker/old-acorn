use crate::expression::{parse_expression, Expression};
use crate::token::Token;

use std::fmt;
use std::iter::Peekable;

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
    body: Vec<Statement<'a>>,
}

// Acorn is a statement-based language. There are several types.
// Some have their own struct. For the others:
//
// Def statements are the keyword "def" followed by an expression with an equals.
// For example, in:
//   def (p | q) = !p -> q
// the equality is the whole "(p | q) = !p -> q",
//
// Prop statements are just an expression. We're implicitly asserting that it is true and provable.
//
// "EndBlock" is maybe not really a statement; it indicates a } ending a block with
// a bunch of statements.
pub enum Statement<'a> {
    Let(LetStatement<'a>),
    Theorem(TheoremStatement<'a>),
    Def(Expression<'a>),
    Prop(Expression<'a>),
    EndBlock,
}

impl fmt::Display for Statement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_helper(f, 0)
    }
}

const INDENT_WIDTH: u8 = 4;

impl Statement<'_> {
    fn fmt_helper(&self, f: &mut fmt::Formatter<'_>, indent: u8) -> fmt::Result {
        for _ in 0..indent {
            write!(f, " ")?;
        }
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
                write!(f, ": {}", ts.claim)?;
                if ts.body.len() > 0 {
                    write!(f, " {{\n")?;
                    for s in &ts.body {
                        s.fmt_helper(f, indent + INDENT_WIDTH)?;
                        write!(f, "\n")?;
                    }
                    for _ in 0..indent {
                        write!(f, " ")?;
                    }
                    write!(f, "}}")?;
                }
                Ok(())
            }

            Statement::Def(ds) => {
                write!(f, "def {}", ds)
            }

            Statement::Prop(ps) => {
                write!(f, "{}", ps)
            }

            Statement::EndBlock => {
                write!(f, "}}")
            }
        }
    }
}

fn parse_block<'a, I>(tokens: &mut Peekable<I>) -> Vec<Statement<'a>>
where
    I: Iterator<Item = Token<'a>>,
{
    let mut body = Vec::new();
    loop {
        match parse_statement(tokens) {
            Some(Statement::EndBlock) => break,
            Some(s) => body.push(s),
            None => panic!("unexpected end of file in block body"),
        }
    }
    body
}

fn parse_theorem_statement<'a, I>(tokens: &mut Peekable<I>, axiomatic: bool) -> TheoremStatement<'a>
where
    I: Iterator<Item = Token<'a>>,
{
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
                    parse_expression(tokens, |t| t == Token::Comma || t == Token::RightParen);
                args.push(exp);
                if terminator == Token::RightParen {
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
    let (claim, terminator) =
        parse_expression(tokens, |t| t == Token::NewLine || t == Token::LeftBrace);
    let body = if terminator == Token::LeftBrace {
        parse_block(tokens)
    } else {
        Vec::new()
    };
    TheoremStatement {
        axiomatic,
        name,
        args,
        claim,
        body,
    }
}

// Tries to parse a single statement from the provided tokens.
// A statement should end with a newline, which is consumed.
// The iterator may also end, in which case this returns None.
pub fn parse_statement<'a, I>(tokens: &mut Peekable<I>) -> Option<Statement<'a>>
where
    I: Iterator<Item = Token<'a>>,
{
    loop {
        match tokens.peek() {
            Some(Token::NewLine) => {
                tokens.next();
                continue;
            }
            Some(Token::Let) => {
                tokens.next();
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
                        let (exp, _) = parse_expression(tokens, |t| t == Token::NewLine);
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
                tokens.next();
                return Some(Statement::Theorem(parse_theorem_statement(tokens, true)));
            }
            Some(Token::Theorem) => {
                tokens.next();
                return Some(Statement::Theorem(parse_theorem_statement(tokens, false)));
            }
            Some(Token::Def) => {
                tokens.next();
                let (exp, _) = parse_expression(tokens, |t| t == Token::NewLine);
                if let Expression::Binary(op, _, _) = exp {
                    if op == Token::Equals {
                        return Some(Statement::Def(exp));
                    }
                }
                panic!("expected equals expression after def");
            }
            Some(Token::RightBrace) => {
                tokens.next();
                if let Some(Token::NewLine) = tokens.next() {
                    return Some(Statement::EndBlock);
                }
                panic!("expected newline after end of block");
            }
            None => return None,
            _ => {
                let (exp, _) = parse_expression(tokens, |t| t == Token::NewLine);
                return Some(Statement::Prop(exp));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::scan;
    use indoc::indoc;

    fn expect_optimal(input: &str) {
        let tokens = scan(input);
        let mut tokens = tokens.into_iter().peekable();
        let stmt = parse_statement(&mut tokens);
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
        expect_optimal("def (p | q) = (!p -> q)");
        expect_optimal("def (p & q) = !(p -> !q)");
        expect_optimal("def (p <-> q) = ((p -> q) & (q -> p))");
        expect_optimal("p -> p");
    }

    #[test]
    fn test_block_parsing() {
        expect_optimal(indoc! {"
            theorem foo: bar {
                baz
            }"})
    }
}
