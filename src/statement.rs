use crate::expression::Expression;
use crate::token::{Error, Result, Token, TokenIter, TokenType};

use std::fmt;

// For example, in:
//   let a: int = x + 2
// The declaration is "a: int" and the expression is the "x + 2".
//
// The declaration can also be a function form, like in
//   define foo(a: int, b: int) -> int = a + a + b
// where the declaration is "foo(a: int, b: int) -> int".
//
// "let" indicates a private definition, and "define" indicates a public definition.
pub struct DefinitionStatement {
    pub declaration: Expression,
    pub value: Option<Expression>,
    pub public: bool,
}

impl fmt::Display for DefinitionStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let keyword = if self.public { "define" } else { "let" };
        write!(f, "{} {}", keyword, self.declaration)?;
        if let Some(value) = &self.value {
            write!(f, " = {}", value)?;
        }
        Ok(())
    }
}

// There are two keywords for theorems.
// The "axiom" keyword indicates theorems that are axiomatic.
// The "theorem" keyword is used for the vast majority of normal theorems.
// For example, in:
//   axiom foo(p, q): p -> (q -> p)
// axiomatic would be "true", the name is "foo", the args are p, q, and the claim is "p -> (q -> p)".
pub struct TheoremStatement {
    pub axiomatic: bool,
    pub name: String,
    pub args: Vec<Expression>,
    pub claim: Expression,
    pub body: Vec<Statement>,
}

// Prop statements are a boolean expression.
// We're implicitly asserting that it is true and provable.
// It's like an anonymous theorem.
pub struct PropStatement {
    pub claim: Expression,
}

// Type statements associate a name with a type expression
pub struct TypeStatement {
    pub name: String,
    pub type_expr: Expression,
}

// ForAll statements create a new block in which new variables are introduced.
pub struct ForAllStatement {
    pub quantifiers: Vec<Expression>,
    pub body: Vec<Statement>,

    // Just for error reporting
    pub token: Token,
}

// If statements create a new block that introduces no variables but has an implicit condition.
pub struct IfStatement {
    pub condition: Expression,
    pub body: Vec<Statement>,

    // Just for error reporting
    pub token: Token,
}

// Exists statements introduce new variables to the outside block.
pub struct ExistsStatement {
    pub quantifiers: Vec<Expression>,
    pub claim: Expression,

    // Just for error reporting
    pub token: Token,
}

// Acorn is a statement-based language. There are several types.
// Each type has its own struct.
pub enum Statement {
    Definition(DefinitionStatement),
    Theorem(TheoremStatement),
    Prop(PropStatement),
    Type(TypeStatement),
    ForAll(ForAllStatement),
    If(IfStatement),
    Exists(ExistsStatement),
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

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_helper(f, 0)
    }
}

// Parses a block (a list of statements) where the left brace has already been consumed.
// Consumes the final right brace.
fn parse_block(tokens: &mut TokenIter) -> Result<Vec<Statement>> {
    let mut body = Vec::new();
    loop {
        match Statement::parse(tokens, true)? {
            (Some(s), end_block) => {
                body.push(s);
                if end_block {
                    break;
                }
            }
            (None, end_block) => {
                if end_block {
                    break;
                }
                return Err(Error::EOF);
            }
        }
    }
    Ok(body)
}

// Parse a parenthesized list of arguments, after which we expect the given terminator token.
fn parse_args(tokens: &mut TokenIter, terminator: TokenType) -> Result<Vec<Expression>> {
    let mut args = Vec::new();
    let token = Token::expect_token(tokens)?;
    if token.token_type == terminator {
        return Ok(args);
    }
    if token.token_type != TokenType::LeftParen {
        return Err(Error::new(&token, "expected an argument list"));
    }
    // Parse an arguments list
    loop {
        let (exp, t) = Expression::parse(tokens, false, |t| {
            t == TokenType::Comma || t == TokenType::RightParen
        })?;
        args.push(exp);
        if t.token_type == TokenType::RightParen {
            Token::expect_type(tokens, terminator)?;
            break;
        }
    }
    Ok(args)
}

// Parses a theorem where the keyword identifier (axiom or theorem) has already been consumed.
// "axiomatic" is whether this is an axiom.
fn parse_theorem_statement(tokens: &mut TokenIter, axiomatic: bool) -> Result<TheoremStatement> {
    let token = Token::expect_type(tokens, TokenType::Identifier)?;
    let name = token.text().to_string();
    let args = parse_args(tokens, TokenType::Colon)?;
    Token::skip_newlines(tokens);
    let (claim, terminator) = Expression::parse(tokens, true, |t| {
        t == TokenType::NewLine || t == TokenType::By
    })?;
    let body = if terminator.token_type == TokenType::By {
        Token::expect_type(tokens, TokenType::LeftBrace)?;
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
fn parse_definition_statement(tokens: &mut TokenIter, public: bool) -> Result<DefinitionStatement> {
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
fn parse_type_statement(tokens: &mut TokenIter) -> Result<TypeStatement> {
    let name = Token::expect_type(tokens, TokenType::Identifier)?
        .text()
        .to_string();
    Token::expect_type(tokens, TokenType::Colon)?;
    Token::skip_newlines(tokens);
    let (type_expr, _) = Expression::parse(tokens, false, |t| t == TokenType::NewLine)?;
    Ok(TypeStatement { name, type_expr })
}

// Parses a forall statement where the "forall" keyword has already been consumed.
fn parse_forall_statement(tokens: &mut TokenIter) -> Result<ForAllStatement> {
    let token = tokens.peek().unwrap().clone();
    let quantifiers = parse_args(tokens, TokenType::LeftBrace)?;
    let body = parse_block(tokens)?;
    Ok(ForAllStatement {
        quantifiers,
        body,
        token,
    })
}

// Parses an if statement where the "if" keyword has already been consumed.
fn parse_if_statement(tokens: &mut TokenIter) -> Result<IfStatement> {
    let token = tokens.peek().unwrap().clone();
    let (condition, _) = Expression::parse(tokens, true, |t| t == TokenType::LeftBrace)?;
    let body = parse_block(tokens)?;
    Ok(IfStatement {
        condition,
        body,
        token,
    })
}

// Parses an exists statement where the "exists" keyword has already been consumed.
fn parse_exists_statement(tokens: &mut TokenIter) -> Result<ExistsStatement> {
    let token = tokens.peek().unwrap().clone();
    let quantifiers = parse_args(tokens, TokenType::LeftBrace)?;
    let (condition, _) = Expression::parse(tokens, true, |t| t == TokenType::RightBrace)?;
    Ok(ExistsStatement {
        quantifiers,
        claim: condition,
        token,
    })
}

fn write_args(f: &mut fmt::Formatter, args: &[Expression]) -> fmt::Result {
    if args.len() == 0 {
        return Ok(());
    }
    write!(f, "(")?;
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}", arg)?;
    }
    write!(f, ")")?;
    Ok(())
}

impl Statement {
    fn fmt_helper(&self, f: &mut fmt::Formatter, indent: u8) -> fmt::Result {
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
                write_args(f, &ts.args)?;
                write!(f, ": {}", ts.claim)?;
                if ts.body.len() > 0 {
                    write!(f, " by")?;
                    write_block(f, &ts.body, indent)?;
                }
                Ok(())
            }

            Statement::Prop(ps) => {
                write!(f, "{}", ps.claim)?;
                Ok(())
            }

            Statement::Type(ts) => {
                write!(f, "type {}: {}", ts.name, ts.type_expr)
            }

            Statement::ForAll(fas) => {
                write!(f, "forall")?;
                write_args(f, &fas.quantifiers)?;
                write_block(f, &fas.body, indent)
            }

            Statement::If(is) => {
                write!(f, "if {}", is.condition)?;
                write_block(f, &is.body, indent)
            }

            Statement::Exists(es) => {
                write!(f, "exists")?;
                write_args(f, &es.quantifiers)?;
                write!(f, " {{ {} }}", es.claim)
            }
        }
    }

    // Tries to parse a single statement from the provided tokens.
    // A statement can always end with a newline, which is consumed.
    // If in_block is true, a prop statement can also end with a right brace.
    // The iterator may also end, in which case this returns None.
    // Returns statement as well as a flag for whether the current block or file ended.
    pub fn parse(tokens: &mut TokenIter, in_block: bool) -> Result<(Option<Statement>, bool)> {
        loop {
            if let Some(token) = tokens.peek() {
                match token.token_type {
                    TokenType::NewLine => {
                        tokens.next();
                        continue;
                    }
                    TokenType::Let => {
                        tokens.next();
                        let s = Statement::Definition(parse_definition_statement(tokens, false)?);
                        return Ok((Some(s), false));
                    }
                    TokenType::Axiom => {
                        tokens.next();
                        let s = Statement::Theorem(parse_theorem_statement(tokens, true)?);
                        return Ok((Some(s), false));
                    }
                    TokenType::Theorem => {
                        tokens.next();
                        let s = Statement::Theorem(parse_theorem_statement(tokens, false)?);
                        return Ok((Some(s), false));
                    }
                    TokenType::Define => {
                        tokens.next();
                        let s = Statement::Definition(parse_definition_statement(tokens, true)?);
                        return Ok((Some(s), false));
                    }
                    TokenType::Type => {
                        tokens.next();
                        let s = Statement::Type(parse_type_statement(tokens)?);
                        return Ok((Some(s), false));
                    }
                    TokenType::RightBrace => {
                        if !in_block {
                            return Err(Error::new(token, "unmatched right brace at top level"));
                        }
                        tokens.next();
                        Token::expect_type(tokens, TokenType::NewLine)?;

                        return Ok((None, true));
                    }
                    TokenType::ForAll => {
                        tokens.next();
                        let s = Statement::ForAll(parse_forall_statement(tokens)?);
                        return Ok((Some(s), false));
                    }
                    TokenType::If => {
                        tokens.next();
                        let s = Statement::If(parse_if_statement(tokens)?);
                        return Ok((Some(s), false));
                    }
                    TokenType::Exists => {
                        tokens.next();
                        let s = Statement::Exists(parse_exists_statement(tokens)?);
                        return Ok((Some(s), false));
                    }
                    _ => {
                        let (claim, token) = Expression::parse(tokens, true, |t| {
                            t == TokenType::NewLine || t == TokenType::RightBrace
                        })?;
                        let block_ended = token.token_type == TokenType::RightBrace;
                        if block_ended && !in_block {
                            return Err(Error::new(
                                &token,
                                "unmatched right brace after expression",
                            ));
                        }
                        let s = Statement::Prop(PropStatement { claim });
                        return Ok((Some(s), block_ended));
                    }
                }
            } else {
                return Ok((None, true));
            }
        }
    }

    // Helper for tests; don't use in production code
    pub fn parse_str(input: &str) -> Result<Statement> {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        match Statement::parse(&mut tokens, false)? {
            (Some(statement), _) => Ok(statement),
            _ => panic!("expected statement, got EOF"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use indoc::indoc;

    fn should_parse(input: &str) -> Statement {
        match Statement::parse_str(input) {
            Ok(statement) => statement,
            Err(e) => panic!("failed to parse {}: {}", input, e),
        }
    }

    fn ok(input: &str) {
        let statement = should_parse(input);
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
    fn test_forall_statements() {
        ok(indoc! {"
            forall(x: Nat) {
                f(x) -> f(Suc(x))
            }"});
    }

    #[test]
    fn test_forall_value_in_statement() {
        ok("let p: bool = forall(b: bool) { b | !b }");
    }

    #[test]
    fn test_nat_ac_statements() {
        ok("type Nat: axiom");
        ok("define 0: Nat = axiom");
        ok("define Suc: Nat -> Nat = axiom");
        ok("define 1: Nat = Suc(0)");
        ok("axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y");
        ok("axiom suc_neq_zero(x: Nat): Suc(x) != 0");
        ok("axiom induction(f: Nat -> bool, n: Nat): f(0) & forall(k: Nat) { f(k) -> f(Suc(k)) } -> f(n)");
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
            theorem foo: bar by {
                baz
            }"});
        fail(indoc! {"
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

    #[test]
    fn test_single_line_forall() {
        should_parse("forall(x: Nat) { f(x) -> f(Suc(x)) }");
    }
}
