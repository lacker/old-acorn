use std::{collections::VecDeque, fmt};

use crate::token::{Error, Result, Token, TokenType};

// An Expression represents the basic structuring of tokens into a syntax tree.
// There are three sorts of expressions.
// Value expressions, like:
//    1 + 2
// Type expressions, like:
//    (int, bool) -> bool
// And declaration expressions, like
//   p: bool
// The expression does not typecheck and enforce semantics; it's just parsing into a tree.
// "Apply" is a function application which doesn't have a top-level token.
// "Grouping" is another expression enclosed in parentheses.
// "Block" is another expression enclosed in braces. Just one, for now.
#[derive(Debug)]
pub enum Expression<'a> {
    Identifier(Token<'a>),
    Unary(Token<'a>, Box<Expression<'a>>),
    Binary(Token<'a>, Box<Expression<'a>>, Box<Expression<'a>>),
    Apply(Box<Expression<'a>>, Box<Expression<'a>>),
    Grouping(Box<Expression<'a>>),
    Block(Box<Expression<'a>>),
}

impl fmt::Display for Expression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Identifier(token) => write!(f, "{}", token),
            Expression::Unary(token, subexpression) => {
                write!(f, "{}{}", token, subexpression)
            }
            Expression::Binary(token, left, right) => {
                let spacer = if token.token_type.left_space() {
                    " "
                } else {
                    ""
                };
                write!(f, "{}{}{} {}", left, spacer, token, right)
            }
            Expression::Apply(left, right) => {
                write!(f, "{}{}", left, right)
            }
            Expression::Grouping(e) => {
                write!(f, "({})", e)
            }
            Expression::Block(e) => {
                write!(f, "{{{}}}", e)
            }
        }
    }
}

impl Expression<'_> {
    pub fn token(&self) -> &Token<'_> {
        match self {
            Expression::Identifier(token) => token,
            Expression::Unary(token, _) => token,
            Expression::Binary(token, _, _) => token,
            Expression::Apply(left, _) => left.token(),
            Expression::Grouping(e) => e.token(),
            Expression::Block(e) => e.token(),
        }
    }

    // Expects the expression to be a list of comma-separated expressions
    // Gets rid of commas and groupings
    pub fn flatten_arg_list(&self) -> Vec<&Expression<'_>> {
        match self {
            Expression::Binary(token, left, right) => {
                if token.token_type == TokenType::Comma {
                    let mut args = left.flatten_arg_list();
                    args.append(&mut right.flatten_arg_list());
                    args
                } else {
                    vec![&self]
                }
            }
            Expression::Grouping(e) => e.flatten_arg_list(),
            _ => vec![&self],
        }
    }

    // Parses a single expression from the provided tokens.
    // termination determines what tokens are allowed to be the terminator.
    // The terminating token is returned.
    pub fn parse<'a>(
        tokens: &mut impl Iterator<Item = Token<'a>>,
        is_value: bool,
        termination: fn(TokenType) -> bool,
    ) -> Result<(Expression<'a>, Token<'a>)> {
        let (partial_expressions, terminator) =
            parse_partial_expressions(tokens, is_value, termination)?;
        Ok((
            combine_partial_expressions(partial_expressions, is_value)?,
            terminator,
        ))
    }
}

// A PartialExpression represents a state in the middle of parsing, where we can have
// either subexpressions or operators, and we haven't prioritized operators yet.
// A list of partial expressions can be turned into an expression, according to operator precedence.
#[derive(Debug)]
enum PartialExpression<'a> {
    Expression(Expression<'a>),
    Unary(Token<'a>),
    Binary(Token<'a>),
}

impl fmt::Display for PartialExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PartialExpression::Expression(e) => write!(f, "{}", e),
            PartialExpression::Unary(token) => write!(f, "{}", token),
            PartialExpression::Binary(token) => write!(f, "{}", token),
        }
    }
}

impl PartialExpression<'_> {
    fn token(&self) -> &Token<'_> {
        match self {
            PartialExpression::Expression(e) => e.token(),
            PartialExpression::Unary(token) => token,
            PartialExpression::Binary(token) => token,
        }
    }
}

// Create partial expressions from tokens.
// termination determines what tokens are allowed to be the terminator.
// The terminating token is returned.
fn parse_partial_expressions<'a>(
    tokens: &mut impl Iterator<Item = Token<'a>>,
    is_value: bool,
    termination: fn(TokenType) -> bool,
) -> Result<(VecDeque<PartialExpression<'a>>, Token<'a>)> {
    let mut partial_expressions = VecDeque::<PartialExpression<'a>>::new();
    while let Some(token) = tokens.next() {
        match token.token_type {
            token_type if termination(token_type) => {
                return Ok((partial_expressions, token));
            }
            TokenType::LeftParen => {
                let (subexpression, _) =
                    Expression::parse(tokens, is_value, |t| t == TokenType::RightParen)?;
                let group = Expression::Grouping(Box::new(subexpression));
                partial_expressions.push_back(PartialExpression::Expression(group));
            }
            TokenType::Identifier => {
                partial_expressions
                    .push_back(PartialExpression::Expression(Expression::Identifier(token)));
            }
            TokenType::Axiom => {
                partial_expressions
                    .push_back(PartialExpression::Expression(Expression::Identifier(token)));
            }
            TokenType::ForAll => {
                partial_expressions
                    .push_back(PartialExpression::Expression(Expression::Identifier(token)));
            }
            TokenType::Exists => {
                partial_expressions
                    .push_back(PartialExpression::Expression(Expression::Identifier(token)));
            }
            token_type if token_type.is_binary() => {
                partial_expressions.push_back(PartialExpression::Binary(token));
            }
            token_type if token_type.is_unary() => {
                partial_expressions.push_back(PartialExpression::Unary(token));
            }
            _ => {
                return Err(Error::new(
                    &token,
                    &format!("expected partial expression or terminator: {:?}", token),
                ));
            }
        }
    }
    Err(Error::EOF)
}

// Combines partial expressions into a single expression.
// Operators work in precedence order, and left-to-right within a single precedence.
// This algorithm is quadratic, so perhaps we should improve it at some point.
fn combine_partial_expressions<'a>(
    mut partials: VecDeque<PartialExpression<'a>>,
    is_value: bool,
) -> Result<Expression<'a>> {
    if partials.len() == 0 {
        return Err(Error::Misc("no partial expressions to combine".to_string()));
    }
    if partials.len() == 1 {
        let partial = partials.pop_back().unwrap();
        if let PartialExpression::Expression(e) = partial {
            return Ok(e);
        }
        return Err(Error::new(partial.token(), "expected an expression"));
    }

    // Find the index of the operator that should operate last
    let (neg_precedence, index) = match partials
        .iter()
        .enumerate()
        .filter_map(|(i, partial)| match partial {
            PartialExpression::Expression(_) => None,
            PartialExpression::Unary(token) => {
                // Only a unary operator at the beginning of the expression can operate last
                if i == 0 {
                    Some((-token.precedence(is_value), i))
                } else {
                    None
                }
            }
            PartialExpression::Binary(token) => Some((-token.precedence(is_value), i)),
        })
        .max()
    {
        Some((neg_precedence, index)) => (neg_precedence, index),
        None => {
            // There are no operators in partials. This must be a sequence of function applications.
            let first_partial = partials.pop_front().unwrap();
            let mut answer = match first_partial {
                PartialExpression::Expression(e) => e,
                _ => return Err(Error::new(first_partial.token(), "expected an expression")),
            };
            for partial in partials.into_iter() {
                if let PartialExpression::Expression(expr) = partial {
                    if let Expression::Grouping(_) = expr {
                        answer = Expression::Apply(Box::new(answer), Box::new(expr));
                    } else {
                        return Err(Error::new(
                            expr.token(),
                            "function arguments must be parenthesized",
                        ));
                    }
                } else {
                    return Err(Error::new(partial.token(), "unexpected operator"));
                }
            }
            return Ok(answer);
        }
    };
    if neg_precedence == 0 {
        let token = partials[index].token();
        return Err(Error::new(
            token,
            &format!("operator {} has precedence 0", token),
        ));
    }

    if index == 0 {
        let partial = partials.pop_front().unwrap();
        if let PartialExpression::Unary(token) = partial {
            return Ok(Expression::Unary(
                token,
                Box::new(combine_partial_expressions(partials, is_value)?),
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
            token,
            Box::new(combine_partial_expressions(partials, is_value)?),
            Box::new(combine_partial_expressions(right_partials, right_is_value)?),
        ));
    }
    return Err(Error::new(partial.token(), "expected binary operator"));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_optimal(input: &str, is_value: bool) {
        let tokens = Token::scan(input).unwrap();
        let mut tokens = tokens.into_iter();
        let exp = match Expression::parse(&mut tokens, is_value, |t| t == TokenType::NewLine) {
            Ok((e, _)) => e,
            Err(e) => panic!("unexpected error parsing: {}", e),
        };
        let output = exp.to_string();
        assert_eq!(input, output);
    }

    fn check_value(input: &str) {
        expect_optimal(input, true);
    }

    fn check_type(input: &str) {
        expect_optimal(input, false);
    }

    // Expects a parse error, or not-an-expression, but not a lex error
    fn expect_error(input: &str, is_value: bool) {
        let tokens = Token::scan(input).unwrap();
        let mut tokens = tokens.into_iter();
        let res = Expression::parse(&mut tokens, is_value, |t| t == TokenType::NewLine);
        match res {
            Err(_) => {}
            Ok((e, _)) => panic!("unexpected success parsing: {}", e),
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
        check_value("forall(x: nat, Suc(x) = x + 1)");
        check_value("exists(x: nat, x = 0)");
        check_value("exists(f: (nat, nat) -> nat, f(0, 0) = 0)");
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
    }

    #[test]
    fn test_bad_types() {
        check_not_type("bool, bool -> bool ->");
        check_not_type("(!p -> !q) -> (q -> p)");
    }
}
