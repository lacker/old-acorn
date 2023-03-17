use crate::expression::Expression;
use crate::token::{Error, Result, Token, TokenType};

use std::fmt;
use std::iter::Peekable;

// For example, in:
//   let a: int = x + 2
// The declaration is "a: int" and the expression is the "x + 2".
//
// The declaration can also be a function form, like in
//   define foo(a: int, b: int) -> int = a + a + b
// where the declaration is "foo(a: int, b: int) -> int".
//
// "let" indicates a private definition, and "define" indicates a public definition.
pub struct DefinitionStatement<'a> {
    pub declaration: Expression<'a>,
    pub value: Option<Expression<'a>>,
    pub public: bool,
}

impl fmt::Display for DefinitionStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let keyword = if self.public { "define" } else { "let" };
        write!(f, "{} {}", keyword, self.declaration)?;
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
    pub axiomatic: bool,
    pub name: &'a str,
    pub args: Vec<Expression<'a>>,
    pub claim: Expression<'a>,
    pub body: Vec<Statement<'a>>,
}

// Prop statements are an expression, with an optional block.
// We're implicitly asserting that it is true and provable.
// It's like an unnamed theorem.
pub struct PropStatement<'a> {
    claim: Expression<'a>,
    body: Vec<Statement<'a>>,
}

// Type statements associate a name with a type expression
pub struct TypeStatement<'a> {
    pub name: &'a str,
    pub type_expr: Expression<'a>,
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
    Definition(DefinitionStatement<'a>),
    Theorem(TheoremStatement<'a>),
    Prop(PropStatement<'a>),
    Type(TypeStatement<'a>),
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

// Parses a block (a list of statements) where the left brace has already been consumed.
fn parse_block<'a, I>(tokens: &mut Peekable<I>) -> Result<Vec<Statement<'a>>>
where
    I: Iterator<Item = Token<'a>>,
{
    let mut body = Vec::new();
    loop {
        match Statement::parse(tokens)? {
            Some(Statement::EndBlock) => break,
            Some(s) => body.push(s),
            None => return Err(Error::EOF),
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
    let token = Token::expect_type(tokens, TokenType::Identifier)?;
    let name = token.text;
    let mut args = Vec::new();
    let token = Token::expect_token(tokens)?;
    match token.token_type {
        TokenType::LeftParen => {
            // Parse an arguments list
            loop {
                let (exp, terminator) = Expression::parse(tokens, false, |t| {
                    t == TokenType::Comma || t == TokenType::RightParen
                })?;
                args.push(exp);
                if terminator.token_type == TokenType::RightParen {
                    Token::expect_type(tokens, TokenType::Colon)?;
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
    Token::skip_newlines(tokens);
    let (claim, terminator) = Expression::parse(tokens, true, |t| {
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

// Parses a let statement where the "let" or "define" keyword has already been consumed.
fn parse_definition_statement<'a, I>(
    tokens: &mut Peekable<I>,
    public: bool,
) -> Result<DefinitionStatement<'a>>
where
    I: Iterator<Item = Token<'a>>,
{
    let (declaration, terminator) = Expression::parse(tokens, false, |t| {
        t == TokenType::NewLine || t == TokenType::Equals
    })?;

    if terminator.token_type == TokenType::NewLine {
        // This is a declaration, with no value
        Ok(DefinitionStatement {
            public,
            declaration,
            value: None,
        })
    } else {
        // This is a definition, with both a declaration and a value
        let (value, _) = Expression::parse(tokens, true, |t| t == TokenType::NewLine)?;
        Ok(DefinitionStatement {
            public,
            declaration,
            value: Some(value),
        })
    }
}

// Parses a type statement where the "type" keyword has already been consumed.
fn parse_type_statement<'a, I>(tokens: &mut Peekable<I>) -> Result<TypeStatement<'a>>
where
    I: Iterator<Item = Token<'a>>,
{
    let name = Token::expect_type(tokens, TokenType::Identifier)?.text;
    Token::expect_type(tokens, TokenType::Colon)?;
    Token::skip_newlines(tokens);
    let (type_expr, _) = Expression::parse(tokens, false, |t| t == TokenType::NewLine)?;
    Ok(TypeStatement { name, type_expr })
}

impl Statement<'_> {
    fn fmt_helper(&self, f: &mut fmt::Formatter<'_>, indent: u8) -> fmt::Result {
        for _ in 0..indent {
            write!(f, " ")?;
        }
        match self {
            Statement::Definition(ds) => write!(f, "{}", ds),

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

            Statement::Prop(ps) => {
                write!(f, "{}", ps.claim)?;
                if ps.body.len() > 0 {
                    write_block(f, &ps.body, indent)?;
                }
                Ok(())
            }

            Statement::Type(ts) => {
                write!(f, "type {}: {}", ts.name, ts.type_expr)
            }

            Statement::EndBlock => {
                write!(f, "}}")
            }
        }
    }

    // Tries to parse a single statement from the provided tokens.
    // A statement should end with a newline, which is consumed.
    // The iterator may also end, in which case this returns None.
    pub fn parse<'a, I>(tokens: &mut Peekable<I>) -> Result<Option<Statement<'a>>>
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
                        return Ok(Some(Statement::Definition(parse_definition_statement(
                            tokens, false,
                        )?)));
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
                    TokenType::Define => {
                        tokens.next();
                        return Ok(Some(Statement::Definition(parse_definition_statement(
                            tokens, true,
                        )?)));
                    }
                    TokenType::Type => {
                        tokens.next();
                        return Ok(Some(Statement::Type(parse_type_statement(tokens)?)));
                    }
                    TokenType::RightBrace => {
                        tokens.next();
                        Token::expect_type(tokens, TokenType::NewLine)?;
                        return Ok(Some(Statement::EndBlock));
                    }
                    _ => {
                        let (claim, terminator) = Expression::parse(tokens, true, |t| {
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

    // Helper for tests; don't use in production code
    pub fn parse_str(input: &str) -> Result<Statement> {
        let tokens = Token::scan(input)?;
        let mut tokens = tokens.into_iter().peekable();
        match Statement::parse(&mut tokens)? {
            Some(statement) => Ok(statement),
            None => panic!("expected statement, got EOF"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use indoc::indoc;

    fn ok(input: &str) {
        let statement = Statement::parse_str(input).unwrap();
        assert_eq!(input, statement.to_string());
    }

    // Expects an error parsing the input into a statement, but not a lex error
    fn fail(input: &str) {
        assert!(Statement::parse_str(input).is_err());
    }

    #[test]
    fn test_definition_statements() {
        ok("let p: bool");
        ok("let a: int = x + 2");
        ok("let a = x + 2");
        ok("let f: int -> bool");
        ok("let f: int -> int = x -> x + 1");
        ok("let g: (int, int) -> int");
        ok("let g: (int, int, int) -> bool");
        ok("define or(p: bool, q: bool) -> bool = (!p -> q)");
        ok("define and(p: bool, q: bool) -> bool = !(p -> !q)");
        ok("define iff(p: bool, q: bool) -> bool = (p -> q) & (q -> p)");
    }

    #[test]
    fn test_theorem_statements() {
        ok("axiom simplification: p -> (q -> p)");
        ok("axiom distribution: (p -> (q -> r)) -> ((p -> q) -> (p -> r))");
        ok("axiom contraposition: (!p -> !q) -> (q -> p)");
        ok("axiom modus_ponens(p, p -> q): q");
        ok("theorem and_comm: p & q <-> q & p");
        ok("theorem and_assoc: (p & q) & r <-> p & (q & r)");
        ok("theorem or_comm: p | q <-> q | p");
        ok("theorem or_assoc: (p | q) | r <-> p | (q | r)");
        ok("theorem suc_gt_zero(x: nat): Suc(x) > 0");
    }

    #[test]
    fn test_prop_statements() {
        ok("p -> p");
    }

    #[test]
    fn test_nat_ac_statements() {
        ok("type Nat: axiom");
        ok("define 0: Nat = axiom");
        ok("define Suc: Nat -> Nat = axiom");
        ok("define 1: Nat = Suc(0)");
        ok("axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y");
        ok("axiom suc_neq_zero(x: Nat): Suc(x) != 0");
        ok("axiom induction(f: Nat -> bool, n: Nat): f(0) & forall(k: Nat, f(k) -> f(Suc(k))) -> f(n)");
        ok("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom");
        ok("axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a");
        ok("axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat): recursion(f, a, Suc(n)) = f(recursion(f, a, n))");
        ok("define add(x: Nat, y: Nat) -> Nat = recursion(Suc, x, y)");
        ok("theorem add_zero_right(a: Nat): add(a, 0) = a");
        ok("theorem add_zero_left(a: Nat): add(0, a) = a");
        ok("theorem add_suc_right(a: Nat, b: Nat): add(a, Suc(b)) = Suc(add(a, b))");
        ok("theorem add_suc_left(a: Nat, b: Nat): add(Suc(a), b) = Suc(add(a, b))");
        ok("theorem add_comm(a: Nat, b: Nat): add(a, b) = add(b, a)");
        ok("theorem add_assoc(a: Nat, b: Nat, c: Nat): add(a, add(b, c)) = add(add(a, b), c)");
    }

    #[test]
    fn test_multiline_at_colon() {
        Statement::parse_str("type Nat:\n  axiom").unwrap();
        Statement::parse_str("theorem foo(b: bool):\nb | !b").unwrap();
    }

    #[test]
    fn test_block_parsing() {
        ok(indoc! {"
            theorem foo: bar {
                baz
            }"});
        ok(indoc! {"
            foo {
                bar
            }"});
    }

    #[test]
    fn test_statement_errors() {
        fail("+ + +");
        fail("let p: bool =");
        fail("let p: bool = (");
        fail("let p: bool = (x + 2");
        fail("let p: bool = x + 2)");
    }

    #[test]
    fn test_only_declarations_in_signatures() {
        fail("theorem foo(x: int, x > 0): x + 1 > 0");
    }
}
