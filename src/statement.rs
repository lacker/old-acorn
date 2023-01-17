use crate::expression::{parse_expression, Expression};
use crate::token::{self, expect_token, expect_type, Error, Result, Token, TokenType};

use std::fmt;
use std::iter::Peekable;

// For example, in:
//   let a: int = x + 2
// The first token is the variable name "a", the second is the type "int",
// and the expression is the "x + 2".
pub struct LetStatement<'a> {
    name: &'a str,
    type_name: Option<&'a str>,
    value: Option<Expression<'a>>,
}

impl fmt::Display for LetStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "let {}", self.name)?;
        if let Some(type_name) = &self.type_name {
            write!(f, ": {}", type_name)?;
        }
        if let Some(value) = &self.value {
            write!(f, " = {}", value)?;
        }
        Ok(())
    }
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

// Prop statements are an expression, with an optional block.
// We're implicitly asserting that it is true and provable.
pub struct PropStatement<'a> {
    claim: Expression<'a>,
    body: Vec<Statement<'a>>,
}

// Acorn is a statement-based language. There are several types.
// Some have their own struct. For the others:
//
// Def statements are the keyword "def" followed by an expression with an equals.
// For example, in:
//   def (p | q) = !p -> q
// the equality is the whole "(p | q) = !p -> q".
//
// "EndBlock" is maybe not really a statement; it indicates a } ending a block with
// a bunch of statements.
pub enum Statement<'a> {
    Let(LetStatement<'a>),
    Theorem(TheoremStatement<'a>),
    Def(Expression<'a>),
    Prop(PropStatement<'a>),
    EndBlock,
}

const INDENT_WIDTH: u8 = 4;

// Writes out a block, starting with the space before the open-brace, indenting the rest.
fn write_block(f: &mut fmt::Formatter, statements: &[Statement], indent: u8) -> fmt::Result {
    write!(f, " {{\n")?;
    for s in statements {
        s.fmt_helper(f, indent + INDENT_WIDTH)?;
        write!(f, "\n")?;
    }
    for _ in 0..indent {
        write!(f, " ")?;
    }
    write!(f, "}}")
}

impl fmt::Display for Statement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_helper(f, 0)
    }
}

impl Statement<'_> {
    fn fmt_helper(&self, f: &mut fmt::Formatter<'_>, indent: u8) -> fmt::Result {
        for _ in 0..indent {
            write!(f, " ")?;
        }
        match self {
            Statement::Let(ls) => write!(f, "{}", ls),

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
                    write_block(f, &ts.body, indent)?;
                }
                Ok(())
            }

            Statement::Def(ds) => {
                write!(f, "def {}", ds)
            }

            Statement::Prop(ps) => {
                write!(f, "{}", ps.claim)?;
                if ps.body.len() > 0 {
                    write_block(f, &ps.body, indent)?;
                }
                Ok(())
            }

            Statement::EndBlock => {
                write!(f, "}}")
            }
        }
    }
}

// Parses a block (a list of statements) where the left brace has already been consumed.
fn parse_block<'a, I>(tokens: &mut Peekable<I>) -> Result<Vec<Statement<'a>>>
where
    I: Iterator<Item = Token<'a>>,
{
    let mut body = Vec::new();
    loop {
        match parse_statement(tokens)? {
            Some(Statement::EndBlock) => break,
            Some(s) => body.push(s),
            None => return Err(token::Error::EOF),
        }
    }
    Ok(body)
}

// Parses a theorem where the keyword identifier (axiom or theorem) has already been consumed.
// "axiomatic" is whether this is an axiom.
fn parse_theorem_statement<'a, I>(
    tokens: &mut Peekable<I>,
    axiomatic: bool,
) -> Result<TheoremStatement<'a>>
where
    I: Iterator<Item = Token<'a>>,
{
    let token = expect_type(tokens, TokenType::Identifier)?;
    let name = token.text;
    let mut args = Vec::new();
    let token = expect_token(tokens)?;
    match token.token_type {
        TokenType::LeftParen => {
            // Parse an arguments list
            loop {
                let (exp, terminator) = parse_expression(tokens, |t| {
                    t == TokenType::Comma || t == TokenType::RightParen
                })?;
                args.push(exp);
                if terminator.token_type == TokenType::RightParen {
                    expect_type(tokens, TokenType::Colon)?;
                    break;
                }
            }
        }
        TokenType::Colon => {}
        _ => {
            return Err(Error::new(
                &token,
                &format!(
                    "unexpected token after {} keyword",
                    if axiomatic { "axiom" } else { "theorem" }
                ),
            ))
        }
    }
    let (claim, terminator) = parse_expression(tokens, |t| {
        t == TokenType::NewLine || t == TokenType::LeftBrace
    })?;
    let body = if terminator.token_type == TokenType::LeftBrace {
        parse_block(tokens)?
    } else {
        Vec::new()
    };
    Ok(TheoremStatement {
        axiomatic,
        name,
        args,
        claim,
        body,
    })
}

// Parses a let statement where the "let" keyword has already been consumed.
fn parse_let_statement<'a, I>(tokens: &mut Peekable<I>) -> Result<LetStatement<'a>>
where
    I: Iterator<Item = Token<'a>>,
{
    let name = expect_type(tokens, TokenType::Identifier)?.text;
    let type_name = if let Some(type_token) = tokens.peek() {
        match type_token.token_type {
            TokenType::Colon => {
                tokens.next();
                Some(expect_type(tokens, TokenType::Identifier)?.text)
            }
            TokenType::Equals => None,
            _ => {
                return Err(Error::new(
                    &type_token,
                    "unexpected token after let keyword",
                ))
            }
        }
    } else {
        return Err(token::Error::EOF);
    };
    let token = expect_token(tokens)?;
    let value = match token.token_type {
        TokenType::Equals => {
            let (exp, _) = parse_expression(tokens, |t| t == TokenType::NewLine)?;
            Some(exp)
        }
        TokenType::NewLine => None,
        _ => {
            return Err(Error::new(&token, "unexpected token after let keyword"));
        }
    };
    Ok(LetStatement {
        name,
        type_name,
        value,
    })
}

// Tries to parse a single statement from the provided tokens.
// A statement should end with a newline, which is consumed.
// The iterator may also end, in which case this returns None.
pub fn parse_statement<'a, I>(tokens: &mut Peekable<I>) -> Result<Option<Statement<'a>>>
where
    I: Iterator<Item = Token<'a>>,
{
    loop {
        if let Some(token) = tokens.peek() {
            match token.token_type {
                TokenType::NewLine => {
                    tokens.next();
                    continue;
                }
                TokenType::Let => {
                    tokens.next();
                    return Ok(Some(Statement::Let(parse_let_statement(tokens)?)));
                }
                TokenType::Axiom => {
                    tokens.next();
                    return Ok(Some(Statement::Theorem(parse_theorem_statement(
                        tokens, true,
                    )?)));
                }
                TokenType::Theorem => {
                    tokens.next();
                    return Ok(Some(Statement::Theorem(parse_theorem_statement(
                        tokens, false,
                    )?)));
                }
                TokenType::Def => {
                    tokens.next();
                    let (exp, _) = parse_expression(tokens, |t| t == TokenType::NewLine)?;
                    if let Expression::Binary(op, _, _) = exp {
                        if op.token_type == TokenType::Equals {
                            return Ok(Some(Statement::Def(exp)));
                        }
                    }
                    return Err(Error::new(
                        exp.token(),
                        "expected equals expression after def",
                    ));
                }
                TokenType::RightBrace => {
                    tokens.next();
                    expect_type(tokens, TokenType::NewLine)?;
                    return Ok(Some(Statement::EndBlock));
                }
                _ => {
                    let (claim, terminator) = parse_expression(tokens, |t| {
                        t == TokenType::NewLine || t == TokenType::LeftBrace
                    })?;
                    let body = if terminator.token_type == TokenType::LeftBrace {
                        parse_block(tokens)?
                    } else {
                        Vec::new()
                    };
                    return Ok(Some(Statement::Prop(PropStatement { claim, body })));
                }
            }
        } else {
            return Ok(None);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::scan;
    use indoc::indoc;

    fn expect_optimal(input: &str) {
        let tokens = scan(input).unwrap();
        let mut tokens = tokens.into_iter().peekable();
        let stmt = parse_statement(&mut tokens).unwrap();
        let output = stmt.unwrap().to_string();
        assert_eq!(input, output);
    }

    // Expects an error parsing the input into a statement, but not a lex error
    fn expect_error(input: &str) {
        let tokens = scan(input).unwrap();
        let mut tokens = tokens.into_iter().peekable();
        assert!(parse_statement(&mut tokens).is_err());
    }

    #[test]
    fn test_statement_parsing() {
        expect_optimal("let p: bool");
        expect_optimal("let a: int = x + 2");
        expect_optimal("let a = x + 2");
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
            }"});
        expect_optimal(indoc! {"
            foo {
                bar
            }"});
    }

    #[test]
    fn test_statement_errors() {
        expect_error("+ + +");
        expect_error("let p: bool =");
        expect_error("let p: bool = (");
        expect_error("let p: bool = (x + 2");
        expect_error("let p: bool = x + 2)");
    }
}
