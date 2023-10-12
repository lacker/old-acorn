use tower_lsp::lsp_types::Range;

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
// "let" indicates a constant definition, and "define" indicates a function definition.
pub struct OldDefinitionStatement {
    pub declaration: Expression,
    pub value: Option<Expression>,
    pub public: bool,
}

impl fmt::Display for OldDefinitionStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let keyword = if self.public { "define" } else { "let" };
        write!(f, "{} {}", keyword, self.declaration)?;
        if let Some(value) = &self.value {
            write!(f, " = {}", value)?;
        }
        Ok(())
    }
}

// Let statements introduce new named constants. For example:
//   let a: int = x + 2
pub struct LetStatement {
    pub name: String,
    pub type_expr: Expression,
    pub value: Expression,
}

// Define statements introduce new named functions. For example:
//   define foo(a: int, b: int) -> int = a + a + b
pub struct DefineStatement {
    pub name: String,
    pub generic_types: Vec<Token>,

    // A list of the named arg types, like "a: int" and "b: int".
    pub args: Vec<Expression>,

    // The specified return type of the function, like "int"
    pub return_type: Expression,

    // The body of the function, like "a + a + b"
    pub return_value: Expression,
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
    pub generic_types: Vec<Token>,
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
}

// Struct statements define a new type
pub struct StructStatement {
    pub name: String,

    pub name_token: Token,

    // Each field contains a field name-token and a type expression
    pub fields: Vec<(Token, Expression)>,
}

// Acorn is a statement-based language. There are several types.
// Each type has its own struct.
pub struct Statement {
    pub first_token: Token,
    pub last_token: Token,
    pub statement: StatementInfo,
}

// Information about a statement that is specific to the type of statement it is
pub enum StatementInfo {
    OldDefinition(OldDefinitionStatement),
    Let(LetStatement),
    Define(DefineStatement),
    Theorem(TheoremStatement),
    Prop(PropStatement),
    Type(TypeStatement),
    ForAll(ForAllStatement),
    If(IfStatement),
    Exists(ExistsStatement),
    Struct(StructStatement),
}

const ONE_INDENT: &str = "    ";

fn add_indent(indentation: &str) -> String {
    format!("{}{}", indentation, ONE_INDENT)
}

// Writes out a block, starting with the space before the open-brace, indenting the rest.
fn write_block(f: &mut fmt::Formatter, statements: &[Statement], indentation: &str) -> fmt::Result {
    write!(f, " {{\n")?;
    let new_indentation = add_indent(indentation);
    for s in statements {
        s.fmt_helper(f, &new_indentation)?;
        write!(f, "\n")?;
    }
    write!(f, "{}}}", indentation)
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_helper(f, "")
    }
}

// Parses a block (a list of statements) where the left brace has already been consumed.
// Returns the statements along with the token for the final right brace.
fn parse_block(tokens: &mut TokenIter) -> Result<(Vec<Statement>, Token)> {
    let mut body = Vec::new();
    loop {
        match Statement::parse(tokens, true)? {
            (Some(s), maybe_right_brace) => {
                body.push(s);
                if let Some(brace) = maybe_right_brace {
                    return Ok((body, brace));
                }
            }
            (None, Some(brace)) => {
                return Ok((body, brace));
            }
            (None, None) => {
                return Err(tokens.error("expected statement but got EOF"));
            }
        }
    }
}

// Parse some arguments.
// The first element is an optional template. For example, the <T> in:
// <T>(a: T, f: T -> T)
// The second element is an optional parenthesized list of arguments.
// Finally we have the terminator token.
fn parse_args(
    tokens: &mut TokenIter,
    terminator: TokenType,
) -> Result<(Vec<Token>, Vec<Expression>)> {
    let mut token = Token::expect_token(tokens)?;
    if token.token_type == terminator {
        return Ok((vec![], vec![]));
    }
    let mut generic_types = vec![];
    if token.token_type == TokenType::LessThan {
        loop {
            let token = Token::expect_type(tokens, TokenType::Identifier)?;
            generic_types.push(token);
            let token = Token::expect_token(tokens)?;
            match token.token_type {
                TokenType::GreaterThan => {
                    break;
                }
                TokenType::Comma => {
                    continue;
                }
                _ => {
                    return Err(Error::new(
                        &token,
                        "expected '>' or ',' in template type list",
                    ));
                }
            }
        }
        token = Token::expect_token(tokens)?;
    }
    if token.token_type != TokenType::LeftParen {
        return Err(Error::new(&token, "expected an argument list"));
    }
    // Parse the arguments list
    let mut args = Vec::new();
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
    Ok((generic_types, args))
}

// Parses a theorem where the keyword identifier (axiom or theorem) has already been found.
// "axiomatic" is whether this is an axiom.
fn parse_theorem_statement(
    keyword: Token,
    tokens: &mut TokenIter,
    axiomatic: bool,
) -> Result<Statement> {
    let token = Token::expect_type(tokens, TokenType::Identifier)?;
    let name = token.text().to_string();
    let (generic_types, args) = parse_args(tokens, TokenType::Colon)?;
    Token::skip_newlines(tokens);
    let (claim, terminator) = Expression::parse(tokens, true, |t| {
        t == TokenType::NewLine || t == TokenType::By
    })?;
    let (body, last_token) = if terminator.token_type == TokenType::By {
        Token::expect_type(tokens, TokenType::LeftBrace)?;
        parse_block(tokens)?
    } else {
        (Vec::new(), terminator)
    };
    let ts = TheoremStatement {
        axiomatic,
        name,
        generic_types,
        args,
        claim,
        body,
    };
    let statement = Statement {
        first_token: keyword,
        last_token: last_token,
        statement: StatementInfo::Theorem(ts),
    };
    Ok(statement)
}

// Parses a let statement where the "let" or "define" keyword has already been found.
fn parse_old_definition_statement(
    keyword: Token,
    tokens: &mut TokenIter,
    public: bool,
) -> Result<Statement> {
    let (declaration, terminator) = Expression::parse(tokens, false, |t| {
        t == TokenType::NewLine || t == TokenType::Equals
    })?;

    let (ds, last_token) = if terminator.token_type == TokenType::NewLine {
        // This is a declaration, with no value
        let last_token = declaration.last_token().clone();
        (
            OldDefinitionStatement {
                public,
                declaration,
                value: None,
            },
            last_token,
        )
    } else {
        // This is a definition, with both a declaration and a value
        let (value, _) = Expression::parse(tokens, true, |t| t == TokenType::NewLine)?;
        let last_token = value.last_token().clone();
        (
            OldDefinitionStatement {
                public,
                declaration,
                value: Some(value),
            },
            last_token,
        )
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::OldDefinition(ds),
    };
    Ok(statement)
}

// Parses a let statement where the "let" keyword has already been found.
fn parse_let_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let name = Token::expect_type(tokens, TokenType::Identifier)?
        .text()
        .to_string();
    Token::expect_type(tokens, TokenType::Colon)?;
    let (type_expr, _) = Expression::parse(tokens, false, |t| t == TokenType::Equals)?;
    let (value, last_token) = Expression::parse(tokens, true, |t| t == TokenType::NewLine)?;
    let ls = LetStatement {
        name,
        type_expr,
        value,
    };
    Ok(Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Let(ls),
    })
}

// Parses a define statement where the "define" keyword has already been found.
fn parse_define_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let name = Token::expect_type(tokens, TokenType::Identifier)?
        .text()
        .to_string();
    let (generic_types, args) = parse_args(tokens, TokenType::RightArrow)?;
    let (return_type, _) = Expression::parse(tokens, false, |t| t == TokenType::Equals)?;
    let (return_value, last_token) = Expression::parse(tokens, true, |t| t == TokenType::NewLine)?;
    let ds = DefineStatement {
        name,
        generic_types,
        args,
        return_type,
        return_value,
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Define(ds),
    };
    Ok(statement)
}

// Parses a type statement where the "type" keyword has already been found.
fn parse_type_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let name = Token::expect_type(tokens, TokenType::Identifier)?
        .text()
        .to_string();
    Token::expect_type(tokens, TokenType::Colon)?;
    Token::skip_newlines(tokens);
    let (type_expr, _) = Expression::parse(tokens, false, |t| t == TokenType::NewLine)?;
    let last_token = type_expr.last_token().clone();
    let ts = TypeStatement { name, type_expr };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Type(ts),
    };
    Ok(statement)
}

// Parses a forall statement where the "forall" keyword has already been found.
fn parse_forall_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let (_, quantifiers) = parse_args(tokens, TokenType::LeftBrace)?;
    let (body, last_token) = parse_block(tokens)?;
    let fas = ForAllStatement { quantifiers, body };
    let statement = Statement {
        first_token: keyword,
        last_token: last_token,
        statement: StatementInfo::ForAll(fas),
    };
    Ok(statement)
}

// Parses an if statement where the "if" keyword has already been found.
fn parse_if_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let token = tokens.peek().unwrap().clone();
    let (condition, _) = Expression::parse(tokens, true, |t| t == TokenType::LeftBrace)?;
    let (body, last_token) = parse_block(tokens)?;
    let is = IfStatement {
        condition,
        body,
        token,
    };
    let statement = Statement {
        first_token: keyword,
        last_token: last_token,
        statement: StatementInfo::If(is),
    };
    Ok(statement)
}

// Parses an exists statement where the "exists" keyword has already been found.
fn parse_exists_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let (_, quantifiers) = parse_args(tokens, TokenType::LeftBrace)?;
    let (condition, last_token) = Expression::parse(tokens, true, |t| t == TokenType::RightBrace)?;
    let es = ExistsStatement {
        quantifiers,
        claim: condition,
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Exists(es),
    };
    Ok(statement)
}

// Parses a struct statement where the "struct" keyword has already been found.
fn parse_struct_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let name_token = Token::expect_type(tokens, TokenType::Identifier)?;
    let name = name_token.text().to_string();
    Token::expect_type(tokens, TokenType::LeftBrace)?;
    let mut fields = Vec::new();
    loop {
        let token = Token::expect_token(tokens)?;
        match token.token_type {
            TokenType::NewLine => {
                continue;
            }
            TokenType::RightBrace => {
                if fields.len() == 0 {
                    return Err(Error::new(&token, "structs must have at least one field"));
                }
                return Ok(Statement {
                    first_token: keyword,
                    last_token: token,
                    statement: StatementInfo::Struct(StructStatement {
                        name,
                        name_token,
                        fields,
                    }),
                });
            }
            TokenType::Identifier => {
                Token::expect_type(tokens, TokenType::Colon)?;
                let (type_expr, _) = Expression::parse(tokens, false, |t| {
                    t == TokenType::NewLine || t == TokenType::RightBrace
                })?;
                fields.push((token, type_expr));
            }
            _ => {
                return Err(Error::new(&token, "expected field name"));
            }
        }
    }
}

fn write_generic_types(f: &mut fmt::Formatter, generic_types: &[Token]) -> fmt::Result {
    if generic_types.len() == 0 {
        return Ok(());
    }
    write!(f, "<")?;
    for (i, generic_type) in generic_types.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}", generic_type)?;
    }
    write!(f, ">")?;
    Ok(())
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
    fn fmt_helper(&self, f: &mut fmt::Formatter, indentation: &str) -> fmt::Result {
        write!(f, "{}", indentation)?;
        match &self.statement {
            StatementInfo::OldDefinition(ds) => write!(f, "{}", ds),

            StatementInfo::Let(ls) => {
                write!(f, "let {}: {} = {}", ls.name, ls.type_expr, ls.value)
            }

            StatementInfo::Define(ds) => {
                write!(f, "define {}", ds.name)?;
                write_generic_types(f, &ds.generic_types)?;
                write_args(f, &ds.args)?;
                write!(f, " -> {} = {}", ds.return_type, ds.return_value)
            }

            StatementInfo::Theorem(ts) => {
                if ts.axiomatic {
                    write!(f, "axiom")?;
                } else {
                    write!(f, "theorem")?;
                }
                write!(f, " {}", ts.name)?;
                write_generic_types(f, &ts.generic_types)?;
                write_args(f, &ts.args)?;
                write!(f, ": {}", ts.claim)?;
                if ts.body.len() > 0 {
                    write!(f, " by")?;
                    write_block(f, &ts.body, indentation)?;
                }
                Ok(())
            }

            StatementInfo::Prop(ps) => {
                write!(f, "{}", ps.claim)?;
                Ok(())
            }

            StatementInfo::Type(ts) => {
                write!(f, "type {}: {}", ts.name, ts.type_expr)
            }

            StatementInfo::ForAll(fas) => {
                write!(f, "forall")?;
                write_args(f, &fas.quantifiers)?;
                write_block(f, &fas.body, indentation)
            }

            StatementInfo::If(is) => {
                write!(f, "if {}", is.condition)?;
                write_block(f, &is.body, indentation)
            }

            StatementInfo::Exists(es) => {
                let new_indentation = add_indent(indentation);
                write!(f, "exists")?;
                write_args(f, &es.quantifiers)?;
                write!(
                    f,
                    " {{\n{}{}\n{}}}",
                    &new_indentation, es.claim, indentation
                )
            }

            StatementInfo::Struct(ss) => {
                let new_indentation = add_indent(indentation);
                write!(f, "struct {} {{\n", ss.name)?;
                for (name, type_expr) in &ss.fields {
                    write!(f, "{}{}: {}\n", new_indentation, name, type_expr)?;
                }
                write!(f, "{}}}", indentation)
            }
        }
    }

    // Tries to parse a single statement from the provided tokens.
    // A statement can always end with a newline, which is consumed.
    // If in_block is true, a prop statement can also end with a right brace.
    // Returns statement, as well as the right brace token, if the current block ended.
    pub fn parse(
        tokens: &mut TokenIter,
        in_block: bool,
    ) -> Result<(Option<Statement>, Option<Token>)> {
        loop {
            if let Some(token) = tokens.peek() {
                match token.token_type {
                    TokenType::NewLine => {
                        tokens.next();
                        continue;
                    }
                    TokenType::Let => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_let_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Axiom => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_theorem_statement(keyword, tokens, true)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Theorem => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_theorem_statement(keyword, tokens, false)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Define => {
                        let keyword = tokens.next().unwrap();
                        let s = if false {
                            parse_define_statement(keyword, tokens)?
                        } else {
                            parse_old_definition_statement(keyword, tokens, true)?
                        };
                        return Ok((Some(s), None));
                    }
                    TokenType::Type => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_type_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::RightBrace => {
                        if !in_block {
                            return Err(Error::new(token, "unmatched right brace at top level"));
                        }
                        let brace = tokens.next().unwrap();
                        Token::expect_type(tokens, TokenType::NewLine)?;

                        return Ok((None, Some(brace)));
                    }
                    TokenType::ForAll => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_forall_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::If => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_if_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Exists => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_exists_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Struct => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_struct_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    _ => {
                        let first_token = tokens.peek().unwrap().clone();
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
                        let brace = if block_ended { Some(token) } else { None };
                        let last_token = claim.last_token().clone();
                        let se = StatementInfo::Prop(PropStatement { claim });
                        let s = Statement {
                            first_token,
                            last_token,
                            statement: se,
                        };
                        return Ok((Some(s), brace));
                    }
                }
            } else {
                return Ok((None, None));
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

    pub fn range(&self) -> Range {
        Range {
            start: self.first_token.start_pos(),
            end: self.last_token.end_pos(),
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
        ok("let a: int = x + 2");
        ok("let f: int -> bool = compose(g, h)");
        ok("let f: int -> int = x -> x + 1");
        ok("let g: (int, int, int) -> bool = swap(h)");
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
        ok("let 0: Nat = axiom");
        ok("let Suc: Nat -> Nat = axiom");
        ok("let 1: Nat = Suc(0)");
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

    #[test]
    fn test_exists_statement() {
        ok(indoc! {"
        exists(x: Nat) {
            x > 0
        }"});
    }

    #[test]
    fn test_single_line_exists_statement() {
        should_parse("exists(x: Nat) { x > 0 }");
    }

    #[test]
    fn test_if_statement() {
        ok(indoc! {"
        if x > 1 {
            x > 0
        }"});
    }

    #[test]
    fn test_struct_statement() {
        ok(indoc! {"
        struct NatPair {
            first: Nat
            second: Nat
        }"});
    }

    #[test]
    fn test_no_empty_structs() {
        fail("struct Foo {}");
    }

    #[test]
    fn test_templated_theorem() {
        ok("axiom recursion_base<T>(f: T -> T, a: T): recursion(f, a, 0) = a");
    }

    // #[test]
    // fn test_templated_definition() {
    //     ok("define recursion<T>(f: T -> T, a: T, n: Nat) -> Nat = axiom");
    // }
}
