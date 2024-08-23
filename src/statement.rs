use tower_lsp::lsp_types::Range;

use crate::expression::{Declaration, Expression, Terminator};
use crate::token::{Error, Result, Token, TokenIter, TokenType};

use std::fmt;

pub struct Body {
    pub left_brace: Token,
    pub statements: Vec<Statement>,
    pub right_brace: Token,
}

// Let statements introduce new named constants. For example:
//   let a: int = x + 2
// The name token can either be an identifier or a number.
pub struct LetStatement {
    pub name: String,
    pub name_token: Token,
    pub type_expr: Expression,
    pub value: Expression,
}

// Define statements introduce new named functions. For example:
//   define foo(a: int, b: int) -> int = a + a + b
pub struct DefineStatement {
    pub name: String,
    pub name_token: Token,

    // For templated definitions
    pub type_params: Vec<Token>,

    // A list of the named arg types, like "a: int" and "b: int".
    pub args: Vec<Declaration>,

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
    pub type_params: Vec<Token>,
    pub args: Vec<Declaration>,
    pub claim: Expression,
    pub claim_right_brace: Token,
    pub body: Option<Body>,
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
    pub quantifiers: Vec<Declaration>,
    pub body: Body,
}

// If statements create a new block that introduces no variables but has an implicit condition.
// They can optionally create a second block with an "else" keyword followed by a block.
pub struct IfStatement {
    pub condition: Expression,
    pub body: Body,
    pub else_body: Option<Body>,

    // Just for error reporting
    pub token: Token,
}

// A variable satisfy statement introduces new variables to the outside block.
// It is written like:
//   let a: Nat satisfy {
//     a > 0
//   }
pub struct VariableSatisfyStatement {
    pub declarations: Vec<Declaration>,
    pub condition: Expression,
}

// A function satisfy statement introduces a new function to the outside block,
// by giving a condition that the output of the function obeys, and claiming that
// there is such a function.
// It's like a combination of a "define" and a "theorem".
pub struct FunctionSatisfyStatement {
    // Name of the new function.
    pub name: String,
    pub name_token: Token,

    // The declarations are mostly arguments to the function, but the last one is the return
    // value of the function.
    pub declarations: Vec<Declaration>,

    pub satisfy_token: Token,

    // The condition is the only thing we know about the function, that the condition is true.
    pub condition: Expression,

    // The body is a proof that such a function exists, or more specifically, that an output
    // exists for every input.
    // This is implicitly using the axiom of choice. It's convenient for the axiom of choice
    // to just be true. Maybe we have to worry about this more in the future.
    pub body: Option<Body>,
}

// Struct statements define a new type by combining existing types
pub struct StructureStatement {
    pub name: String,
    pub name_token: Token,

    // Each field contains a field name-token and a type expression
    pub fields: Vec<(Token, Expression)>,
}

// Inductive statements define a new type by defining a set of constructors.
pub struct InductiveStatement {
    pub name: String,
    pub name_token: Token,

    // Each constructor has a name token and an expression for a list of types.
    // If the expression is None, the constructor is a base value.
    // The types can refer to the inductive type itself.
    pub constructors: Vec<(Token, Option<Expression>)>,
}

pub struct ImportStatement {
    // The full path to the module, like in "foo.bar.baz" the module would be ["foo", "bar", "baz"]
    pub components: Vec<String>,

    // What names to import from the module.
    // If this is empty, we just import the module itself.
    pub names: Vec<Token>,
}

// A class statement defines some class variables and instance methods that are scoped to the class.
pub struct ClassStatement {
    pub name: String,
    pub name_token: Token,

    // The body of a class statement
    pub body: Body,
}

// A numerals statement determines what class is used for numeric literals.
pub struct NumeralsStatement {
    pub type_expr: Expression,
}

pub struct SolveStatement {
    // The expression we are trying to find equalities for.
    pub target: Expression,

    // Statements used to solve the problem.
    pub body: Body,
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
    Let(LetStatement),
    Define(DefineStatement),
    Theorem(TheoremStatement),
    Prop(PropStatement),
    Type(TypeStatement),
    ForAll(ForAllStatement),
    If(IfStatement),
    VariableSatisfy(VariableSatisfyStatement),
    FunctionSatisfy(FunctionSatisfyStatement),
    Structure(StructureStatement),
    Inductive(InductiveStatement),
    Import(ImportStatement),
    Class(ClassStatement),
    Numerals(NumeralsStatement),
    Solve(SolveStatement),
    Problem(Body),
}

const ONE_INDENT: &str = "    ";

fn add_indent(indentation: &str) -> String {
    format!("{}{}", indentation, ONE_INDENT)
}

// Writes out a block, starting with the space before the open-brace, indenting the rest.
// Does not write a trailing newline.
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
// Consumes the right brace, but nothing after that.
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
// Finally we have the terminator token. This should appear after the closing paren.
// Returns the type params, the arguments, and the terminator token.
fn parse_args(
    tokens: &mut TokenIter,
    terminator: TokenType,
) -> Result<(Vec<Token>, Vec<Declaration>, Token)> {
    let mut token = tokens.expect_token()?;
    if token.token_type == terminator {
        return Ok((vec![], vec![], token));
    }
    let mut type_params = vec![];
    if token.token_type == TokenType::LessThan {
        loop {
            let token = tokens.expect_type(TokenType::Identifier)?;
            type_params.push(token);
            let token = tokens.expect_token()?;
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
        token = tokens.expect_token()?;
    }
    if token.token_type != TokenType::LeftParen {
        return Err(Error::new(&token, "expected an argument list"));
    }

    // Parse the arguments list
    let declarations = Declaration::parse_list(tokens)?;
    let terminator = tokens.expect_type(terminator)?;
    return Ok((type_params, declarations, terminator));
}

// Parses a by block if that's the next thing in the token stream.
// Takes the right brace that ended the previous expression.
// Returns the last token parsed..
// Consumes newlines in any case.
fn parse_by_block(right_brace: Token, tokens: &mut TokenIter) -> Result<(Option<Body>, Token)> {
    loop {
        match tokens.peek() {
            Some(token) => {
                if token.token_type == TokenType::NewLine {
                    tokens.next();
                    continue;
                }
                if token.token_type != TokenType::By {
                    break;
                }
                tokens.next();
                let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
                let (statements, right_brace) = parse_block(tokens)?;
                return Ok((
                    Some(Body {
                        left_brace,
                        statements,
                        right_brace: right_brace.clone(),
                    }),
                    right_brace,
                ));
            }
            None => break,
        }
    }
    Ok((None, right_brace))
}

// Parses a theorem where the keyword identifier (axiom or theorem) has already been found.
// "axiomatic" is whether this is an axiom.
fn parse_theorem_statement(
    keyword: Token,
    tokens: &mut TokenIter,
    axiomatic: bool,
) -> Result<Statement> {
    let name_token = tokens.expect_variable_name(false)?;
    let (type_params, args, _) = parse_args(tokens, TokenType::LeftBrace)?;
    if type_params.len() > 1 {
        return Err(Error::new(
            &type_params[1],
            "only one type parameter is supported",
        ));
    }
    let (claim, claim_right_brace) =
        Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;

    let (body, last_token) = parse_by_block(claim_right_brace.clone(), tokens)?;

    let ts = TheoremStatement {
        axiomatic,
        name: name_token.text().to_string(),
        type_params,
        args,
        claim,
        claim_right_brace,
        body,
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Theorem(ts),
    };
    Ok(statement)
}

// Finish the rest of a variable satisfy statement, after we've consumed the 'satisfy' keyword
fn complete_variable_satisfy(
    keyword: Token,
    tokens: &mut TokenIter,
    declarations: Vec<Declaration>,
) -> Result<Statement> {
    tokens.expect_type(TokenType::LeftBrace)?;
    let (condition, last_token) =
        Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;
    let es = VariableSatisfyStatement {
        declarations,
        condition,
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::VariableSatisfy(es),
    };
    Ok(statement)
}

// Parses a statement where the "let" keyword has already been found.
// This might not be a LetStatement because multiple statement types can start with "let".
fn parse_let_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    match tokens.peek() {
        Some(token) => {
            if token.token_type == TokenType::LeftParen {
                // This is a parenthesized let..satisfy.
                let (_, declarations, _) = parse_args(tokens, TokenType::Satisfy)?;
                return complete_variable_satisfy(keyword, tokens, declarations);
            }
        }
        None => return Err(tokens.error("unexpected end of file")),
    }
    let name_token = tokens.expect_variable_name(true)?;
    let name = name_token.text().to_string();
    if let Some(token) = tokens.peek() {
        if token.token_type == TokenType::LeftParen {
            // This is a function defined via let..satisfy.
            tokens.next();
            let mut declarations = Declaration::parse_list(tokens)?;
            tokens.expect_type(TokenType::RightArrow)?;
            let (return_value, satisfy_token) =
                Declaration::parse(tokens, Terminator::Is(TokenType::Satisfy))?;
            declarations.push(return_value);
            tokens.expect_type(TokenType::LeftBrace)?;
            let (condition, right_brace) =
                Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;
            let (body, last_token) = parse_by_block(right_brace, tokens)?;
            let fss = FunctionSatisfyStatement {
                name,
                name_token,
                declarations,
                satisfy_token,
                condition,
                body,
            };
            return Ok(Statement {
                first_token: keyword,
                last_token,
                statement: StatementInfo::FunctionSatisfy(fss),
            });
        }
    }
    tokens.expect_type(TokenType::Colon)?;
    let (type_expr, middle_token) = Expression::parse_type(
        tokens,
        Terminator::Or(TokenType::Equals, TokenType::Satisfy),
    )?;
    if middle_token.token_type == TokenType::Satisfy {
        return complete_variable_satisfy(
            keyword,
            tokens,
            vec![Declaration::Typed(name_token, type_expr)],
        );
    }

    let (value, last_token) = Expression::parse_value(tokens, Terminator::Is(TokenType::NewLine))?;
    let ls = LetStatement {
        name,
        name_token,
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
    let name_token = tokens.expect_variable_name(false)?;
    let (type_params, args, _) = parse_args(tokens, TokenType::RightArrow)?;
    if type_params.len() > 1 {
        return Err(Error::new(
            &type_params[1],
            "only one type parameter is supported",
        ));
    }
    let (return_type, _) = Expression::parse_type(tokens, Terminator::Is(TokenType::LeftBrace))?;
    let (return_value, last_token) =
        Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;
    let ds = DefineStatement {
        name: name_token.text().to_string(),
        name_token,
        type_params,
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
    let name_token = tokens.expect_type_name()?;
    tokens.expect_type(TokenType::Colon)?;
    tokens.skip_newlines();
    let (type_expr, _) = Expression::parse_type(tokens, Terminator::Is(TokenType::NewLine))?;
    let last_token = type_expr.last_token().clone();
    let ts = TypeStatement {
        name: name_token.to_string(),
        type_expr,
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Type(ts),
    };
    Ok(statement)
}

// Parses a forall statement where the "forall" keyword has already been found.
fn parse_forall_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let (_, quantifiers, left_brace) = parse_args(tokens, TokenType::LeftBrace)?;
    let (statements, right_brace) = parse_block(tokens)?;
    let body = Body {
        left_brace,
        statements,
        right_brace: right_brace.clone(),
    };
    let fas = ForAllStatement { quantifiers, body };
    let statement = Statement {
        first_token: keyword,
        last_token: right_brace,
        statement: StatementInfo::ForAll(fas),
    };
    Ok(statement)
}

// If there is an "else { ...statements }" body, parse and consume it.
// Returns None and consumes nothing if there is not an "else" body here.
fn parse_else_body(tokens: &mut TokenIter) -> Result<Option<Body>> {
    loop {
        match tokens.peek() {
            Some(token) => match token.token_type {
                TokenType::NewLine => {
                    tokens.next();
                }
                TokenType::Else => {
                    tokens.next();
                    break;
                }
                _ => return Ok(None),
            },
            None => return Ok(None),
        }
    }
    let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
    let (statements, right_brace) = parse_block(tokens)?;
    let body = Body {
        left_brace,
        statements,
        right_brace,
    };
    Ok(Some(body))
}

// Parses an if statement where the "if" keyword has already been found.
fn parse_if_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let token = tokens.peek().unwrap().clone();
    let (condition, left_brace) =
        Expression::parse_value(tokens, Terminator::Is(TokenType::LeftBrace))?;
    let (statements, right_brace) = parse_block(tokens)?;
    let body = Body {
        left_brace,
        statements,
        right_brace: right_brace.clone(),
    };
    let else_body = parse_else_body(tokens)?;
    let is = IfStatement {
        condition,
        body,
        else_body,
        token,
    };
    let statement = Statement {
        first_token: keyword,
        last_token: right_brace,
        statement: StatementInfo::If(is),
    };
    Ok(statement)
}

// Parses a structure statement where the "structure" keyword has already been found.
fn parse_structure_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let name_token = tokens.expect_type_name()?;
    tokens.expect_type(TokenType::LeftBrace)?;
    let mut fields = Vec::new();
    while let Some(token) = tokens.peek() {
        match token.token_type {
            TokenType::NewLine => {
                tokens.next();
            }
            TokenType::RightBrace => {
                if fields.len() == 0 {
                    return Err(Error::new(&token, "structs must have at least one field"));
                }
                return Ok(Statement {
                    first_token: keyword,
                    last_token: tokens.next().unwrap(),
                    statement: StatementInfo::Structure(StructureStatement {
                        name: name_token.to_string(),
                        name_token,
                        fields,
                    }),
                });
            }
            _ => {
                let token = tokens.expect_variable_name(false)?;
                tokens.expect_type(TokenType::Colon)?;
                let (type_expr, t) = Expression::parse_type(
                    tokens,
                    Terminator::Or(TokenType::NewLine, TokenType::RightBrace),
                )?;
                if t.token_type == TokenType::RightBrace {
                    return Err(Error::new(&t, "field declarations must end with a newline"));
                }
                fields.push((token, type_expr));
            }
        }
    }
    Err(Error::new(&keyword, "unterminated structure statement"))
}

// Parses an inductive statement where the "inductive" keyword has already been found.
fn parse_inductive_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let type_token = tokens.expect_type_name()?;
    tokens.expect_type(TokenType::LeftBrace)?;
    let mut constructors = vec![];
    loop {
        let next_type = match tokens.peek() {
            Some(token) => token.token_type,
            None => break,
        };
        match next_type {
            TokenType::NewLine => {
                tokens.next();
                continue;
            }
            TokenType::RightBrace => {
                if constructors.len() == 0 {
                    return Err(Error::new(
                        &type_token,
                        "inductive types must have a constructor",
                    ));
                }
                return Ok(Statement {
                    first_token: keyword,
                    last_token: tokens.next().unwrap(),
                    statement: StatementInfo::Inductive(InductiveStatement {
                        name: type_token.to_string(),
                        name_token: type_token,
                        constructors,
                    }),
                });
            }
            _ => {}
        }
        let name_token = tokens.expect_variable_name(true)?;
        let next_type = match tokens.peek() {
            Some(token) => token.token_type,
            None => break,
        };
        if next_type == TokenType::NewLine {
            // A no-argument constructor
            constructors.push((name_token, None));
            continue;
        }
        if next_type != TokenType::LeftParen {
            return Err(Error::new(&name_token, "expected a constructor definition"));
        }
        let (type_list_expr, _) =
            Expression::parse_type(tokens, Terminator::Is(TokenType::NewLine))?;
        constructors.push((name_token, Some(type_list_expr)));
    }
    Err(Error::new(&keyword, "unterminated inductive statement"))
}

// Parses a module component list, like "foo.bar.baz".
// Expects to consume a terminator token at the end.
// Returns the strings, along with the token right before the terminator.
fn parse_module_components(
    tokens: &mut TokenIter,
    terminator: TokenType,
) -> Result<(Vec<String>, Token)> {
    let mut components = Vec::new();
    let last_token = loop {
        let token = tokens.expect_type(TokenType::Identifier)?;
        components.push(token.text().to_string());
        let token = tokens.expect_token()?;
        if token.token_type == terminator {
            break token;
        }
        match token.token_type {
            TokenType::Dot => continue,
            _ => return Err(Error::new(&token, "unexpected token in module path")),
        }
    };
    Ok((components, last_token))
}

// Parses an import statement where the "import" keyword has already been found.
fn parse_import_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let (components, last_token) = parse_module_components(tokens, TokenType::NewLine)?;
    let is = ImportStatement {
        components,
        names: vec![],
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Import(is),
    };
    Ok(statement)
}

// Parses a "from" statement where the "from" keyword has already been found.
fn parse_from_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let (components, _) = parse_module_components(tokens, TokenType::Import)?;
    let mut names = vec![];
    let last_token = loop {
        let token = tokens.expect_type(TokenType::Identifier)?;
        let separator = tokens.expect_token()?;
        match separator.token_type {
            TokenType::NewLine => {
                names.push(token.clone());
                break token;
            }
            TokenType::Comma => {
                names.push(token);
                continue;
            }
            _ => {
                return Err(Error::new(&token, "expected comma or newline"));
            }
        }
    };
    let is = ImportStatement { components, names };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Import(is),
    };
    Ok(statement)
}

// Parses a class statement where the "class" keyword has already been found.
fn parse_class_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let name_token = tokens.expect_type_name()?;
    let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
    let (statements, right_brace) = parse_block(tokens)?;
    let body = Body {
        left_brace,
        statements,
        right_brace: right_brace.clone(),
    };
    let cs = ClassStatement {
        name: name_token.to_string(),
        name_token,
        body,
    };
    let statement = Statement {
        first_token: keyword,
        last_token: right_brace,
        statement: StatementInfo::Class(cs),
    };
    Ok(statement)
}

// Parses a solve statement where the "solve" keyword has already been found.
fn parse_solve_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let (target, _) = Expression::parse_value(tokens, Terminator::Is(TokenType::By))?;
    let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
    let (statements, right_brace) = parse_block(tokens)?;
    let body = Body {
        left_brace,
        statements,
        right_brace: right_brace.clone(),
    };
    let ss = SolveStatement { target, body };
    let s = Statement {
        first_token: keyword,
        last_token: right_brace,
        statement: StatementInfo::Solve(ss),
    };
    Ok(s)
}

fn write_type_params(f: &mut fmt::Formatter, type_params: &[Token]) -> fmt::Result {
    if type_params.len() == 0 {
        return Ok(());
    }
    write!(f, "<")?;
    for (i, param) in type_params.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}", param)?;
    }
    write!(f, ">")?;
    Ok(())
}

fn write_args(f: &mut fmt::Formatter, args: &[Declaration]) -> fmt::Result {
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
            StatementInfo::Let(ls) => {
                write!(f, "let {}: {} = {}", ls.name, ls.type_expr, ls.value)
            }

            StatementInfo::Define(ds) => {
                let new_indentation = add_indent(indentation);
                write!(f, "define {}", ds.name)?;
                write_type_params(f, &ds.type_params)?;
                write_args(f, &ds.args)?;
                write!(
                    f,
                    " -> {} {{\n{}{}\n{}}}",
                    ds.return_type, new_indentation, ds.return_value, indentation
                )
            }

            StatementInfo::Theorem(ts) => {
                let new_indentation = add_indent(indentation);
                if ts.axiomatic {
                    write!(f, "axiom")?;
                } else {
                    write!(f, "theorem")?;
                }
                write!(f, " {}", ts.name)?;
                write_type_params(f, &ts.type_params)?;
                write_args(f, &ts.args)?;
                write!(f, " {{\n{}{}\n{}}}", new_indentation, ts.claim, indentation)?;
                if let Some(body) = &ts.body {
                    write!(f, " by")?;
                    write_block(f, &body.statements, indentation)?;
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
                write_block(f, &fas.body.statements, indentation)
            }

            StatementInfo::If(is) => {
                write!(f, "if {}", is.condition)?;
                write_block(f, &is.body.statements, indentation)?;
                if let Some(else_body) = &is.else_body {
                    write!(f, " else")?;
                    write_block(f, &else_body.statements, indentation)?;
                }
                Ok(())
            }

            StatementInfo::VariableSatisfy(vss) => {
                let new_indentation = add_indent(indentation);
                write!(f, "let ")?;
                if vss.declarations.len() == 1 {
                    write!(f, "{}", vss.declarations[0])?;
                } else {
                    write_args(f, &vss.declarations)?;
                }
                write!(
                    f,
                    " satisfy {{\n{}{}\n{}}}",
                    &new_indentation, vss.condition, indentation
                )
            }

            StatementInfo::FunctionSatisfy(fss) => {
                let new_indentation = add_indent(indentation);
                write!(f, "let {}", fss.name)?;
                let i = fss.declarations.len() - 1;
                write_args(f, &fss.declarations[..i])?;
                write!(f, " -> {} satisfy {{\n", fss.declarations[i],)?;
                write!(f, "{}{}\n", new_indentation, fss.condition)?;
                write!(f, "{}}}", indentation)?;
                if let Some(body) = &fss.body {
                    write!(f, " by")?;
                    write_block(f, &body.statements, indentation)?;
                }
                Ok(())
            }

            StatementInfo::Structure(ss) => {
                let new_indentation = add_indent(indentation);
                write!(f, "structure {} {{\n", ss.name)?;
                for (name, type_expr) in &ss.fields {
                    write!(f, "{}{}: {}\n", new_indentation, name, type_expr)?;
                }
                write!(f, "{}}}", indentation)
            }

            StatementInfo::Inductive(is) => {
                let new_indentation = add_indent(indentation);
                write!(f, "inductive {} {{\n", is.name)?;
                for (name, type_expr) in &is.constructors {
                    match type_expr {
                        Some(te) => write!(f, "{}{}{}\n", new_indentation, name, te)?,
                        None => write!(f, "{}{}\n", new_indentation, name)?,
                    }
                }
                write!(f, "{}}}", indentation)
            }

            StatementInfo::Import(is) => {
                if is.names.is_empty() {
                    write!(f, "import {}", is.components.join("."))
                } else {
                    let names = is
                        .names
                        .iter()
                        .map(|t| t.text())
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "from {} import {}", is.components.join("."), names)
                }
            }

            StatementInfo::Class(cs) => {
                write!(f, "class {}", cs.name)?;
                write_block(f, &cs.body.statements, indentation)
            }

            StatementInfo::Numerals(ds) => {
                write!(f, "default {}", ds.type_expr)
            }

            StatementInfo::Solve(ss) => {
                write!(f, "solve {} by", ss.target)?;
                write_block(f, &ss.body.statements, indentation)
            }

            StatementInfo::Problem(body) => {
                write!(f, "problem")?;
                write_block(f, &body.statements, indentation)
            }
        }
    }

    // Tries to parse a single statement from the provided tokens.
    // If in_block is true, we might get a right brace instead of a statement.
    // Returns statement, as well as the right brace token, if the current block ended.
    // Returns Ok((None, None)) if the end of the file was reached.
    //
    // Normally, this function consumes the final newline.
    // When it's a right brace that ends a block, though, the last token consumed is the right brace.
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
                        let s = parse_define_statement(keyword, tokens)?;
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
                    TokenType::Structure => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_structure_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Inductive => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_inductive_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Import => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_import_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Class => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_class_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Numerals => {
                        let keyword = tokens.next().unwrap();
                        let (type_expr, last_token) =
                            Expression::parse_type(tokens, Terminator::Is(TokenType::NewLine))?;
                        let ds = NumeralsStatement { type_expr };
                        let s = Statement {
                            first_token: keyword,
                            last_token,
                            statement: StatementInfo::Numerals(ds),
                        };
                        return Ok((Some(s), None));
                    }
                    TokenType::From => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_from_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Solve => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_solve_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Problem => {
                        let keyword = tokens.next().unwrap();
                        let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
                        let (statements, right_brace) = parse_block(tokens)?;
                        let body = Body {
                            left_brace,
                            statements,
                            right_brace: right_brace.clone(),
                        };
                        let s = Statement {
                            first_token: keyword,
                            last_token: right_brace,
                            statement: StatementInfo::Problem(body),
                        };
                        return Ok((Some(s), None));
                    }
                    _ => {
                        if !in_block {
                            return Err(Error::new(token, "unexpected token at the top level"));
                        }
                        let first_token = tokens.peek().unwrap().clone();
                        let (claim, token) = Expression::parse_value(
                            tokens,
                            Terminator::Or(TokenType::NewLine, TokenType::RightBrace),
                        )?;
                        let block_ended = token.token_type == TokenType::RightBrace;
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

    pub fn first_line(&self) -> u32 {
        self.first_token.start_pos().line
    }

    pub fn last_line(&self) -> u32 {
        self.last_token.end_pos().line
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
        if Statement::parse_str(input).is_ok() {
            panic!("statement parsed okay but we expected error:\n{}\n", input);
        }
    }

    fn fail_with(input: &str, expected_error: &str) {
        match Statement::parse_str(input) {
            Ok(statement) => panic!("expected failure but got statement: {}", statement),
            Err(e) => {
                if !e.to_string().contains(expected_error) {
                    panic!("expected error '{}', got '{}'", expected_error, e);
                }
            }
        }
    }

    #[test]
    fn test_definition_statements() {
        ok("let a: int = x + 2");
        ok("let f: int -> bool = compose(g, h)");
        ok("let f: int -> int = x -> x + 1");
        ok("let g: (int, int, int) -> bool = swap(h)");
        ok(indoc! {"
        define orx(p: bool, q: bool) -> bool {
            (not p -> q)
        }"});
        ok(indoc! {"
        define andx(p: bool, q: bool) -> bool {
            not (p -> not q)
        }"});
        ok(indoc! {"
        define iff(p: bool, q: bool) -> bool {
            (p -> q) and (q -> p)
        }"});
    }

    #[test]
    fn test_theorem_statements() {
        ok(indoc! {"axiom simplification {
            p -> (q -> p)
        }"});
        ok(indoc! {"axiom distribution {
            (p -> (q -> r)) -> ((p -> q) -> (p -> r))
        }"});
        ok(indoc! {"axiom contraposition {
            (not p -> not q) -> (q -> p)
        }"});
        ok(indoc! {"theorem and_comm {
            p and q <-> q and p
        }"});
        ok(indoc! {"theorem and_assoc {
            (p and q) and r <-> p and (q and r)
        }"});
        ok(indoc! {"theorem or_comm {
            p or q <-> q or p
        }"});
        ok(indoc! {"theorem or_assoc {
            (p or q) or r <-> p or (q or r)
        }"});
        ok(indoc! {"theorem suc_gt_zero(x: nat) {
            suc(x) > 0
        }"});
    }

    #[test]
    fn test_prop_statements() {
        ok(indoc! {"
        theorem goal {
            true
        } by {
            p -> p
        }"});
    }

    #[test]
    fn test_forall_statements() {
        ok(indoc! {"
            forall(x: Nat) {
                f(x) -> f(suc(x))
            }"});
    }

    #[test]
    fn test_forall_value_in_statement() {
        ok("let p: bool = forall(b: bool) { b or not b }");
    }

    #[test]
    fn test_nat_ac_statements() {
        ok("type Nat: axiom");
        ok("let suc: Nat -> Nat = axiom");
        ok(indoc! {"
        axiom suc_injective(x: Nat, y: Nat) {
            suc(x) = suc(y) -> x = y
        }"});
        ok(indoc! {"
        axiom suc_neq_zero(x: Nat) {
            suc(x) != 0
        }"});
        ok(indoc! {"
            axiom induction(f: Nat -> bool, n: Nat) {
                f(0) and forall(k: Nat) { f(k) -> f(suc(k)) } -> f(n)
            }"});
        ok(indoc! {"
        define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat {
            axiom
        }"});
        ok(indoc! {"
        axiom recursion_base(f: Nat -> Nat, a: Nat) {
            recursion(f, a, 0) = a
        }"});
        ok(indoc! {"
            axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat) {
                recursion(f, a, suc(n)) = f(recursion(f, a, n))
            }"});
        ok(indoc! {"
        define add(x: Nat, y: Nat) -> Nat {
            recursion(suc, x, y)
        }"});
        ok(indoc! {"
        theorem add_zero_right(a: Nat) {
            add(a, 0) = a
        }"});
        ok(indoc! {"
        theorem add_zero_left(a: Nat) {
            add(0, a) = a
        }"});
        ok(indoc! {"
        theorem add_suc_right(a: Nat, b: Nat) {
            add(a, suc(b)) = suc(add(a, b))
        }"});
        ok(indoc! {"
        theorem add_suc_left(a: Nat, b: Nat) {
            add(suc(a), b) = suc(add(a, b))
        }"});
        ok(indoc! {"
        theorem add_comm(a: Nat, b: Nat) {
            add(a, b) = add(b, a)
        }"});
        ok(indoc! {"
            theorem add_assoc(a: Nat, b: Nat, c: Nat) {
                add(a, add(b, c)) = add(add(a, b), c)
            }"});
    }

    #[test]
    fn test_block_parsing() {
        ok(indoc! {"
            theorem foo {
                bar
            } by {
                baz
            }"});
        fail(indoc! {"
            foo {
                bar
            }"});
    }

    #[test]
    fn test_by_on_next_line() {
        let statement = should_parse(indoc! {"
            theorem foo { bar }
            by {
                baz
            }"});
        let expected = indoc! {"
        theorem foo {
            bar
        } by {
            baz
        }"};
        assert_eq!(expected, statement.to_string());
    }

    #[test]
    fn test_statement_errors() {
        fail("+ + +");
        fail("let p: Bool =");
        fail("let p: Bool = (");
        fail("let p: Bool = (x + 2");
        fail("let p: Bool = x + 2)");
    }

    #[test]
    fn test_declared_variable_names_lowercased() {
        ok("let p: Bool = true");
        fail("let P: Bool = true");
    }

    #[test]
    fn test_defined_variable_names_lowercased() {
        ok(indoc! {"
        define foo(x: Bool) -> Bool {
            true
        }"});
        fail("define Foo(x: Bool) -> Bool: true");
    }

    #[test]
    fn test_theorem_names_lowercased() {
        ok(indoc! {"
        theorem foo {
            true
        }"});
        fail("theorem Foo: true");
    }

    #[test]
    fn test_structure_names_titlecased() {
        ok(indoc! {"
        structure Foo {
            bar: Nat
        }"});
        fail(indoc! {"
        structure foo {
            bar: Nat
        }"});
    }

    #[test]
    fn test_type_names_titlecased() {
        ok("type Foo: axiom");
        fail("type foo: axiom");
    }

    #[test]
    fn test_only_declarations_in_signatures() {
        fail("theorem foo(x: int, x > 0): x + 1 > 0");
    }

    #[test]
    fn test_single_line_forall() {
        should_parse("forall(x: Nat) { f(x) -> f(suc(x)) }");
    }

    #[test]
    fn test_variable_satisfy_statement() {
        ok(indoc! {"
        let x: Nat satisfy {
            x > 0
        }"});
    }

    #[test]
    fn test_variable_satisfy_multivar_statement() {
        ok(indoc! {"
        let (x: Nat, y: Nat) satisfy {
            x > y
        }"});
    }

    #[test]
    fn test_single_line_variable_satisfy_statement() {
        should_parse("let x: Nat satisfy { x > 0 }");
    }

    #[test]
    fn test_single_line_variable_satisfy_multivar_statement() {
        should_parse("let (x: Nat, y: Nat) satisfy { x > y }");
    }

    #[test]
    fn test_function_satisfy_statement() {
        ok(indoc! {"
        let foo(a: Nat, m: Nat) -> r: Nat satisfy {
            r = a + m
        }"});
    }

    #[test]
    fn test_function_satisfy_statement_with_by_block() {
        ok(indoc! {"
        let foo(a: Nat, m: Nat) -> r: Nat satisfy {
            r > a + m
        } by {
            a + m + 1 > a + m
        }"});
    }

    #[test]
    fn test_if_statement() {
        ok(indoc! {"
        if x > 1 {
            x > 0
        }"});
    }

    #[test]
    fn test_structure_statement() {
        ok(indoc! {"
        structure NatPair {
            first: Nat
            second: Nat
        }"});
    }

    #[test]
    fn test_no_empty_structures() {
        fail("structure Foo {}");
    }

    #[test]
    fn test_structure_fields_need_newlines() {
        fail("structure Foo { bar: Nat }");
    }

    #[test]
    fn test_structure_fields_capitalized_correctly() {
        fail(indoc! {"
        structure fooBar {
            foo: Bar
        }"});
        fail(indoc! {"
        structure FooBar {
            Foo: Bar
        }"});
    }

    #[test]
    fn test_inductive_statement() {
        ok(indoc! {"
        inductive Nat {
            zero
            suc(Nat)
        }"});
    }

    #[test]
    fn test_no_empty_inductive_statements() {
        fail("inductive Nat {}");
    }

    #[test]
    fn test_inductive_fields_need_newlines() {
        fail("inductive Nat { zero }");
    }

    #[test]
    fn test_parametric_theorem() {
        ok(indoc! {"
        axiom recursion_base<T>(f: T -> T, a: T) {
            recursion(f, a, 0) = a
        }"});
    }

    #[test]
    fn test_parametric_definition() {
        ok(indoc! {"
        define recursion<T>(f: T -> T, a: T, n: Nat) -> Nat {
            axiom
        }"});
    }

    #[test]
    fn test_import_statement() {
        ok("import foo.bar.baz");
    }

    #[test]
    fn test_if_else_statement() {
        ok(indoc! {"
        if foo(x) {
            bar(x)
        } else {
            qux(x)
        }"});
    }

    #[test]
    fn test_no_lone_else_statement() {
        fail("else { qux(x) }");
    }

    #[test]
    fn test_class_statement() {
        ok(indoc! {"
        class Foo {
            let blorp: Foo = axiom
            let 0: Foo = axiom
        }"});
    }

    #[test]
    fn test_from_statement() {
        ok("from foo import bar");
        ok("from foo.bar import baz");
        ok("from foo.bar.qux import baz, zip");
        fail("from foo");
    }

    #[test]
    fn test_solve_statement() {
        ok(indoc! {"
        solve x by {
            x = 2
        }"});
    }

    #[test]
    fn test_solve_infix_expression() {
        ok(indoc! {"
        solve 1 - 1 by {
            1 - 1 = 0
        }"});
    }

    #[test]
    fn test_failing_early_on_bad_define_syntax() {
        fail_with(
            indoc! {"
        define foo(x: Nat) -> Nat: bar
        baz(qux)
        zip(dash)
        fo(fum)
        "},
            "unexpected token",
        );
    }
}
