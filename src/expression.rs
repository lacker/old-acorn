use std::{collections::VecDeque, fmt};

use tower_lsp::lsp_types::Range;

use crate::token::{Error, Result, Token, TokenIter, TokenType};

// An Expression represents the basic structuring of tokens into a syntax tree.
// There are three sorts of expressions.
// Value expressions, like:
//    1 + 2
// Type expressions, like:
//    (int, bool) -> bool
// And declaration expressions, like
//   p: bool
// The expression does not typecheck and enforce semantics; it's just parsing into a tree.
#[derive(Debug)]
pub enum Expression {
    // The keywords that work like identifiers are treated like identifiers here.
    // true, false, and axiom.
    // TODO: "axiom" as identifier is weird, let's change it.
    Identifier(Token),

    // A unary operator applied to another expression.
    Unary(Token, Box<Expression>),

    // An infix binary operator, with the left and right expressions.
    Binary(Box<Expression>, Token, Box<Expression>),

    // The application of a function. The second expression must be an arg list.
    Apply(Box<Expression>, Box<Expression>),

    // A grouping like ( <expr> ) or { <expr> }.
    // The tokens of the bracey things that delimit the grouping are included.
    Grouping(Token, Box<Expression>, Token),

    // A binder is an expression that binds variables, like a forall/exists/function.
    // The first token is the binder keyword, like "forall".
    // The first expression is the argument list, like "(x: Nat, y: Nat)".
    // The second expression is the body block.
    // The last token is the closing brace.
    Binder(Token, Box<Expression>, Box<Expression>, Token),

    // If-then-else expressions have to have the else block.
    // The first token is the "if" keyword.
    // The first expression is the condition.
    // The second expression is the "if" block.
    // The third expression is the "else" block.
    // The last token is the closing brace.
    IfThenElse(
        Token,
        Box<Expression>,
        Box<Expression>,
        Box<Expression>,
        Token,
    ),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Identifier(token) => write!(f, "{}", token),
            Expression::Unary(token, subexpression) => {
                write!(f, "{}{}", token, subexpression)
            }
            Expression::Binary(left, token, right) => {
                let left_spacer = if token.token_type.left_space() {
                    " "
                } else {
                    ""
                };
                let right_spacer = if token.token_type.right_space() {
                    " "
                } else {
                    ""
                };
                write!(
                    f,
                    "{}{}{}{}{}",
                    left, left_spacer, token, right_spacer, right
                )
            }
            Expression::Apply(left, right) => {
                write!(f, "{}{}", left, right)
            }
            Expression::Grouping(_, e, _) => {
                write!(f, "({})", e)
            }
            Expression::Binder(token, args, sub, _) => {
                write!(f, "{}{} {{ {} }}", token, args, sub)
            }
            Expression::IfThenElse(_, cond, if_block, else_block, _) => {
                write!(
                    f,
                    "if {} {{ {} }} else {{ {} }}",
                    cond, if_block, else_block
                )
            }
        }
    }
}

impl Expression {
    // This is not the first token or the last token, but the "conceptually top level" token.
    pub fn token(&self) -> &Token {
        match self {
            Expression::Identifier(token) => token,
            Expression::Unary(token, _) => token,
            Expression::Binary(_, token, _) => token,
            Expression::Apply(left, _) => left.token(),
            Expression::Grouping(left_paren, _, _) => left_paren,
            Expression::Binder(token, _, _, _) => token,
            Expression::IfThenElse(token, _, _, _, _) => token,
        }
    }

    pub fn first_token(&self) -> &Token {
        match self {
            Expression::Identifier(token) => token,
            Expression::Unary(token, _) => token,
            Expression::Binary(left, _, _) => left.first_token(),
            Expression::Apply(left, _) => left.first_token(),
            Expression::Grouping(left_paren, _, _) => left_paren,
            Expression::Binder(token, _, _, _) => token,
            Expression::IfThenElse(token, _, _, _, _) => token,
        }
    }

    pub fn last_token(&self) -> &Token {
        match self {
            Expression::Identifier(token) => token,
            Expression::Unary(_, subexpression) => subexpression.last_token(),
            Expression::Binary(_, _, right) => right.last_token(),
            Expression::Apply(_, right) => right.last_token(),
            Expression::Grouping(_, _, right_paren) => right_paren,
            Expression::Binder(_, _, _, right_brace) => right_brace,
            Expression::IfThenElse(_, _, _, _, right_brace) => right_brace,
        }
    }

    pub fn range(&self) -> Range {
        Range {
            start: self.first_token().start_pos(),
            end: self.last_token().end_pos(),
        }
    }

    // Flattens an expression like "1, 2, 3"
    pub fn flatten_comma_separated_list(&self) -> Vec<&Expression> {
        match self {
            Expression::Binary(left, token, right) => {
                if token.token_type == TokenType::Comma {
                    let mut args = left.flatten_comma_separated_list();
                    args.append(&mut right.flatten_comma_separated_list());
                    args
                } else {
                    vec![&self]
                }
            }
            _ => vec![&self],
        }
    }

    // Flattens an expression like "(1, 2, 3)"
    // If allow_singleton is true, then something like "1" also counts as a list.
    // If allow_singleton is false, a list of length 1 must be parenthesized like "(1)".
    pub fn flatten_list(&self, allow_singleton: bool) -> Result<Vec<&Expression>> {
        match self {
            Expression::Grouping(_, e, _) => Ok(e.flatten_comma_separated_list()),
            e => {
                if !allow_singleton {
                    Err(Error::new(
                        self.token(),
                        &format!("expected a grouped list but found: {}", self),
                    ))
                } else {
                    Ok(vec![e])
                }
            }
        }
    }

    // Parses a single expression from the provided tokens.
    // termination determines what tokens are allowed to be the terminator.
    // The terminating token is returned.
    pub fn parse(
        tokens: &mut TokenIter,
        is_value: bool,
        termination: fn(TokenType) -> bool,
    ) -> Result<(Expression, Token)> {
        let (partial_expressions, terminator) =
            parse_partial_expressions(tokens, is_value, termination)?;
        Ok((
            combine_partial_expressions(partial_expressions, is_value, tokens)?,
            terminator,
        ))
    }

    // Turn an expression like foo.bar.baz into ["foo", "bar", "baz"]
    pub fn flatten_dots(&self) -> Result<Vec<String>> {
        match self {
            Expression::Identifier(token) => Ok(vec![token.text().to_string()]),
            Expression::Binary(left, token, right) => {
                if token.token_type != TokenType::Dot {
                    return Err(Error::new(
                        token,
                        &format!("expected dot operator but found: {}", token),
                    ));
                }
                let mut left = left.flatten_dots()?;
                let mut right = right.flatten_dots()?;
                left.append(&mut right);
                Ok(left)
            }
            _ => Err(Error::new(
                self.token(),
                &format!("expected namespaced identifier but found: {}", self),
            )),
        }
    }
}

// A PartialExpression represents a state in the middle of parsing, where we can have
// either subexpressions or operators, and we haven't prioritized operators yet.
// A list of partial expressions can be turned into an expression, according to operator precedence.
#[derive(Debug)]
enum PartialExpression {
    // Already a complete expression
    Expression(Expression),
    Block(Token, Expression, Token),

    // Tokens that are only part of an expression
    Unary(Token),
    Binary(Token),
    Binder(Token),
    If(Token),
    Else(Token),
}

impl fmt::Display for PartialExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PartialExpression::Expression(e) => write!(f, "{}", e),
            PartialExpression::Block(_, e, _) => write!(f, "{{ {} }}", e),

            PartialExpression::Unary(token)
            | PartialExpression::Binary(token)
            | PartialExpression::Binder(token)
            | PartialExpression::If(token)
            | PartialExpression::Else(token) => write!(f, "{}", token),
        }
    }
}

impl PartialExpression {
    fn token(&self) -> &Token {
        match self {
            PartialExpression::Expression(e) => e.token(),
            PartialExpression::Block(token, _, _) => token,

            PartialExpression::Unary(token)
            | PartialExpression::Binary(token)
            | PartialExpression::Binder(token)
            | PartialExpression::If(token)
            | PartialExpression::Else(token) => token,
        }
    }
}

// Create partial expressions from tokens.
// termination determines what tokens are allowed to be the terminator.
// The terminating token is returned.
fn parse_partial_expressions(
    tokens: &mut TokenIter,
    is_value: bool,
    termination: fn(TokenType) -> bool,
) -> Result<(VecDeque<PartialExpression>, Token)> {
    let mut partials = VecDeque::<PartialExpression>::new();
    while let Some(token) = tokens.next() {
        if termination(token.token_type) {
            return Ok((partials, token));
        }
        if token.token_type == TokenType::Dot {
            // The dot has to be preceded by an expression, and followed by an identifier.
            // Handle it now, because it has the highest priority.
            let left = match partials.pop_back() {
                Some(PartialExpression::Expression(e)) => e,
                _ => {
                    return Err(Error::new(&token, "expected expression before dot"));
                }
            };
            let right = match tokens.next() {
                Some(token) => {
                    if token.token_type != TokenType::Identifier {
                        return Err(Error::new(&token, "expected identifier after dot"));
                    }
                    Expression::Identifier(token)
                }
                None => {
                    return Err(Error::new(&token, "expected identifier after dot"));
                }
            };
            partials.push_back(PartialExpression::Expression(Expression::Binary(
                Box::new(left),
                token,
                Box::new(right),
            )));
            continue;
        }
        if token.token_type.is_binary() {
            partials.push_back(PartialExpression::Binary(token));
            continue;
        }
        if token.token_type.is_unary() {
            partials.push_back(PartialExpression::Unary(token));
            continue;
        }
        match token.token_type {
            TokenType::LeftParen => {
                let (subexpression, last_token) =
                    Expression::parse(tokens, is_value, |t| t == TokenType::RightParen)?;
                let group = Expression::Grouping(token, Box::new(subexpression), last_token);
                partials.push_back(PartialExpression::Expression(group));
            }
            TokenType::Identifier | TokenType::Axiom | TokenType::True | TokenType::False => {
                partials.push_back(PartialExpression::Expression(Expression::Identifier(token)));
            }
            TokenType::ForAll | TokenType::Exists | TokenType::Function => {
                partials.push_back(PartialExpression::Binder(token));
            }
            TokenType::If => partials.push_back(PartialExpression::If(token)),
            TokenType::Else => partials.push_back(PartialExpression::Else(token)),
            TokenType::LeftBrace => {
                let (subexp, right_brace) =
                    Expression::parse(tokens, is_value, |t| t == TokenType::RightBrace)?;
                partials.push_back(PartialExpression::Block(token, subexp, right_brace));
            }
            TokenType::NewLine => {
                // Ignore newlines. The case where the newline is a terminator, we already caught.
            }

            _ => {
                return Err(Error::new(
                    &token,
                    "expected partial expression or terminator",
                ));
            }
        }
    }
    Err(tokens.error("expected expression but got EOF"))
}

// Find the index of the operator that should operate last. (Ie, the root of the tree.)
// If there are no operators, return None.
fn find_last_operator(
    partials: &VecDeque<PartialExpression>,
    is_value: bool,
) -> Result<Option<usize>> {
    let operators = partials.iter().enumerate().filter_map(|(i, partial)| {
        match partial {
            PartialExpression::Unary(token) => {
                // Only a unary operator at the beginning of the expression can operate last
                if i == 0 {
                    Some((-token.precedence(is_value), i))
                } else {
                    None
                }
            }
            PartialExpression::Binary(token) => Some((-token.precedence(is_value), i)),
            _ => None,
        }
    });

    match operators.max() {
        Some((neg_precedence, index)) => {
            if neg_precedence == 0 {
                let token = partials[index].token();
                return Err(Error::new(
                    token,
                    &format!("operator {} has precedence 0", token),
                ));
            }
            Ok(Some(index))
        }
        None => Ok(None),
    }
}

// Combines partial expressions into a single expression.
// Operators work in precedence order, and left-to-right within a single precedence.
// This algorithm is quadratic, so perhaps we should improve it at some point.
fn combine_partial_expressions(
    mut partials: VecDeque<PartialExpression>,
    is_value: bool,
    iter: &mut TokenIter,
) -> Result<Expression> {
    if partials.len() == 0 {
        return Err(iter.error("no partial expressions to combine"));
    }
    if partials.len() == 1 {
        let partial = partials.pop_back().unwrap();
        if let PartialExpression::Expression(e) = partial {
            return Ok(e);
        }
        return Err(Error::new(partial.token(), "incomplete expression"));
    }

    // If there are operators, find the operator that should operate last,
    // and recurse on each of the two sides.
    if let Some(index) = find_last_operator(&partials, is_value)? {
        if index == 0 {
            let partial = partials.pop_front().unwrap();
            if let PartialExpression::Unary(token) = partial {
                return Ok(Expression::Unary(
                    token,
                    Box::new(combine_partial_expressions(partials, is_value, iter)?),
                ));
            }
            return Err(Error::new(partial.token(), "expected unary operator"));
        }

        let mut right_partials = partials.split_off(index);
        let partial = right_partials.pop_front().unwrap();

        // If the operator is a colon, then the right side is definitely a type
        let right_is_value = is_value && partial.token().token_type != TokenType::Colon;

        if let PartialExpression::Binary(token) = partial {
            return Ok(Expression::Binary(
                Box::new(combine_partial_expressions(partials, is_value, iter)?),
                token,
                Box::new(combine_partial_expressions(
                    right_partials,
                    right_is_value,
                    iter,
                )?),
            ));
        }
        return Err(Error::new(partial.token(), "expected binary operator"));
    }

    // When there are no operators, the nature of the first partial expression should
    // tell us how to handle the rest of them.
    match partials.pop_front().unwrap() {
        // When the first partial is a normal expression, that looks like a function application.
        PartialExpression::Expression(mut answer) => {
            for partial in partials.into_iter() {
                match partial {
                    PartialExpression::Expression(expr) => match expr {
                        Expression::Grouping(_, _, _) => {
                            answer = Expression::Apply(Box::new(answer), Box::new(expr))
                        }
                        _ => return Err(Error::new(expr.token(), "expected a grouping")),
                    },
                    _ => return Err(Error::new(partial.token(), "unexpected operator")),
                }
            }
            Ok(answer)
        }

        // When the first token is a binder, we expect an arg list and a block.
        PartialExpression::Binder(token) => match partials.pop_front() {
            Some(PartialExpression::Expression(args)) => match partials.pop_front() {
                Some(PartialExpression::Block(_, block, right_brace)) => {
                    if partials.is_empty() {
                        Ok(Expression::Binder(
                            token.clone(),
                            Box::new(args),
                            Box::new(block),
                            right_brace,
                        ))
                    } else {
                        Err(Error::new(
                            partials[0].token(),
                            "unexpected extra expression after a binder expression",
                        ))
                    }
                }
                _ => Err(Error::new(&token, "this binder needs a block")),
            },
            _ => Err(Error::new(&token, "this binder needs arguments")),
        },

        PartialExpression::If(token) => match partials.pop_front() {
            Some(PartialExpression::Expression(cond)) => match partials.pop_front() {
                Some(PartialExpression::Block(_, if_value, _)) => match partials.pop_front() {
                    Some(PartialExpression::Else(else_token)) => match partials.pop_front() {
                        Some(PartialExpression::Block(_, else_value, right_brace)) => {
                            if partials.is_empty() {
                                Ok(Expression::IfThenElse(
                                    token.clone(),
                                    Box::new(cond),
                                    Box::new(if_value),
                                    Box::new(else_value),
                                    right_brace,
                                ))
                            } else {
                                Err(Error::new(
                                    partials[0].token(),
                                    "unexpected extra expression after an if-then-else expression",
                                ))
                            }
                        }
                        _ => Err(Error::new(&else_token, "this 'else' needs a block")),
                    },
                    _ => Err(Error::new(&token, "this 'if' needs an 'else'")),
                },
                _ => Err(Error::new(&token, "this 'if' needs a block")),
            },
            _ => Err(Error::new(&token, "this 'if' needs a condition")),
        },

        PartialExpression::Block(token, _, _) => {
            Err(Error::new(&token, "invalid location for a block"))
        }

        PartialExpression::Else(token) => Err(Error::new(&token, "invalid location for an else")),

        e => Err(Error::new(
            e.token(),
            "I don't think this can happen, but if it does, this expression is bad.",
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_parse(input: &str, is_value: bool) -> Expression {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        match Expression::parse(&mut tokens, is_value, |t| t == TokenType::NewLine) {
            Ok((e, _)) => e,
            Err(e) => panic!("unexpected error parsing: {}", e),
        }
    }

    fn expect_optimal(input: &str, is_value: bool) {
        let output = expect_parse(input, is_value).to_string();
        assert_eq!(input, output);
    }

    fn check_value(input: &str) {
        expect_optimal(input, true);
    }

    fn expect_value(input: &str) {
        expect_parse(input, true);
    }

    fn check_type(input: &str) {
        expect_optimal(input, false);
    }

    // Expects a parse error, or not-an-expression, but not a lex error
    fn expect_error(input: &str, is_value: bool) {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let res = Expression::parse(&mut tokens, is_value, |t| t == TokenType::NewLine);
        match res {
            Err(_) => {}
            Ok((e, _)) => panic!("unexpectedly parsed {} => {}", input, e),
        }
    }

    fn check_not_value(input: &str) {
        expect_error(input, true);
    }

    fn check_not_type(input: &str) {
        expect_error(input, false);
    }

    #[test]
    fn test_value_parsing() {
        check_value("p -> (q -> p)");
        check_value("(p -> (q -> r)) -> ((p -> q) -> (p -> r))");
        check_value("(p <-> q) = ((p -> q) & (q -> p))");
        check_value("p & q <-> q & p");
        check_value("(p & q) & r <-> p & (q & r)");
        check_value("p | q <-> q | p");
        check_value("(p | q) | r <-> p | (q | r)");
    }

    #[test]
    fn test_function_application() {
        check_value("f(x)");
        check_value("foo(x, y)");
        check_value("foo(x)(y)");
        check_value("foo(x, y + z, w)");
    }

    #[test]
    fn test_quantifiers() {
        check_value("forall(x: nat) { (Suc(x) = x + 1) }");
        check_value("exists(x: nat) { (x = 0) }");
        check_value("exists(f: (nat, nat) -> nat) { (f(0, 0) = 0) }");
    }

    #[test]
    fn test_function_signatures() {
        check_type("foo(a: bool, b: nat) -> bool");
    }

    #[test]
    fn test_type_parsing() {
        check_type("bool");
        check_type("bool -> bool");
        check_type("(bool, bool) -> bool");
    }

    #[test]
    fn test_comparisons() {
        check_value("p = q");
        check_value("p != q");
        check_value("p < q");
        check_value("p <= q");
        check_value("p > q");
        check_value("p >= q");
    }

    #[test]
    fn test_blocks() {
        check_value("forall(x: Nat) { x = x }");
    }

    #[test]
    fn test_empty_blocks() {
        // Empty blocks in expressions should fail to parse, but not crash
        check_not_value("forall(x: Nat) { }");
        check_not_value("exists(x: Nat) { }");
    }

    #[test]
    fn test_block_inside_binary() {
        check_value("p -> forall(x: Nat) { x = x }");
        check_value("f(forall(x: Nat) { x = x }, forall(y: Nat) { y = y })");
    }

    #[test]
    fn test_bad_values() {
        check_not_value("+ + +");

        // Not expressions
        check_not_value("let a: int = x + 2");
        check_not_value("define (p & q) = !(p -> !q)");
        check_not_value("type Nat: axiom");

        // A math-function has to have arguments
        check_not_value("f()");

        check_not_value("axiom contraposition: (!p -> !q) -> (q -> p)");
        check_not_value("f x");

        check_not_value("forall");
        check_not_value("exists");
        check_not_value("function");
    }

    #[test]
    fn test_bad_types() {
        check_not_type("bool, bool -> bool ->");
        check_not_type("(!p -> !q) -> (q -> p)");
    }

    #[test]
    fn test_extra_newline() {
        expect_value(
            "(1 +
            2)",
        );
    }

    #[test]
    fn test_dot_expressions() {
        check_value("NatPair.first(NatPair.new(a, b)) = a");
    }

    #[test]
    fn test_dot_parsing_priority() {
        let exp = expect_parse("foo.bar(baz)", true);
        if let Expression::Apply(_, _) = exp {
            // That's what we expect
            return;
        }
        panic!("unexpected expression: {:?}", exp);
    }

    #[test]
    fn test_if_then_else_expressions() {
        check_value("if p { q } else { r }");

        check_not_value("if");
        check_not_value("if p");
        check_not_value("if p { q }");
        check_not_value("else");
        check_not_value("else { r }");
        check_not_value("if p { q } else { r } else { s }");
    }

    #[test]
    fn test_bad_partials() {
        check_not_value("(1 +)");
        check_not_value("(!)");
        check_not_value("{ 1 }");
        check_not_value("forall(x: Nat)");
        check_not_value("forall(x: Nat) { x = x } { x }");
    }
}
