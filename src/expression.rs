use std::{collections::VecDeque, fmt};

use crate::token::{Error, Result, Token, TokenType};

// An Expression represents a mathematical expression, like 2 + 2 or (P -> Q).
// It can represent either a type, like (int -> bool), or a value, like (2 + 2).
pub enum Expression<'a> {
    Identifier(Token<'a>),
    Unary(Token<'a>, Box<Expression<'a>>),
    Binary(Token<'a>, Box<Expression<'a>>, Box<Expression<'a>>),
}

impl fmt::Display for Expression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_helper(f, 0, 0)
    }
}

impl Expression<'_> {
    // Prints out this expression, parenthesizing only if necessary.
    // left_p and right_p are the precedences of the expressions to either side of this one.
    // They must happen after this one.
    fn fmt_helper(&self, f: &mut fmt::Formatter<'_>, left_p: i8, right_p: i8) -> fmt::Result {
        match self {
            Expression::Identifier(token) => write!(f, "{}", token),
            Expression::Unary(token, subexpression) => {
                let p = token.precedence();
                if right_p > p {
                    // If we didn't parenthesize, the right operator would happen first.
                    // So we do need to parenthesize.
                    write!(f, "({}", token)?;
                    subexpression.fmt_helper(f, p, 0)?;
                    write!(f, ")")
                } else {
                    // We don't need to parenthesize.
                    write!(f, "{}", token)?;
                    subexpression.fmt_helper(f, p, right_p)
                }
            }
            Expression::Binary(token, left, right) => {
                let p = token.precedence();
                if p <= left_p || p <= right_p {
                    // We need to parenthesize.
                    // We are a bit conservative so that we don't rely on left- or right-associativity.
                    write!(f, "(")?;
                    left.fmt_helper(f, 0, p)?;
                    if token.token_type.left_space() {
                        write!(f, " ")?;
                    }
                    write!(f, "{} ", token)?;
                    right.fmt_helper(f, p, 0)?;
                    write!(f, ")")
                } else {
                    // We don't need to parenthesize.
                    left.fmt_helper(f, left_p, p)?;
                    if token.token_type.left_space() {
                        write!(f, " ")?;
                    }
                    write!(f, "{} ", token)?;
                    right.fmt_helper(f, p, right_p)
                }
            }
        }
    }

    pub fn token(&self) -> &Token<'_> {
        match self {
            Expression::Identifier(token) => token,
            Expression::Unary(token, _) => token,
            Expression::Binary(token, _, _) => token,
        }
    }
}

// A PartialExpression represents a state in the middle of parsing, where we can have
// either subexpressions or operators, and we haven't prioritized operators yet.
// A list of partial expressions can be turned into an expression, according to operator precedence.
enum PartialExpression<'a> {
    Expression(Expression<'a>),
    Unary(Token<'a>),
    Binary(Token<'a>),
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
    termination: fn(TokenType) -> bool,
) -> Result<(VecDeque<PartialExpression<'a>>, Token<'a>)> {
    let mut partial_expressions = VecDeque::<PartialExpression<'a>>::new();
    while let Some(token) = tokens.next() {
        match token.token_type {
            token_type if termination(token_type) => {
                return Ok((partial_expressions, token));
            }
            TokenType::LeftParen => {
                let (subexpression, _) = parse_expression(tokens, |t| t == TokenType::RightParen)?;
                partial_expressions.push_back(PartialExpression::Expression(subexpression));
            }
            TokenType::Identifier => {
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
    let (neg_precedence, index) = partials
        .iter()
        .enumerate()
        .filter_map(|(i, partial)| match partial {
            PartialExpression::Expression(_) => None,
            PartialExpression::Unary(token) => {
                // Only a unary operator at the beginning of the expression can operate last
                if i == 0 {
                    Some((-token.precedence(), i))
                } else {
                    None
                }
            }
            PartialExpression::Binary(token) => Some((-token.precedence(), i)),
        })
        .max()
        .unwrap();
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
                Box::new(combine_partial_expressions(partials)?),
            ));
        }
        return Err(Error::new(partial.token(), "expected unary operator"));
    }

    let mut right_partials = partials.split_off(index);
    let partial = right_partials.pop_front().unwrap();
    if let PartialExpression::Binary(token) = partial {
        return Ok(Expression::Binary(
            token,
            Box::new(combine_partial_expressions(partials)?),
            Box::new(combine_partial_expressions(right_partials)?),
        ));
    }
    return Err(Error::new(partial.token(), "expected binary operator"));
}

// Parses a single expression from the provided tokens.
// termination determines what tokens are allowed to be the terminator.
// The terminating token is returned.
pub fn parse_expression<'a>(
    tokens: &mut impl Iterator<Item = Token<'a>>,
    termination: fn(TokenType) -> bool,
) -> Result<(Expression<'a>, Token<'a>)> {
    let (partial_expressions, terminator) = parse_partial_expressions(tokens, termination)?;
    Ok((
        combine_partial_expressions(partial_expressions)?,
        terminator,
    ))
}

#[cfg(test)]
mod tests {
    use crate::token::scan;

    use super::*;

    fn expect_optimal(input: &str) {
        let tokens = scan(input).unwrap();
        let mut tokens = tokens.into_iter();
        let (exp, _) = parse_expression(&mut tokens, |t| t == TokenType::NewLine).unwrap();
        let output = exp.to_string();
        assert_eq!(input, output);
    }

    // Expects a parse error, or not-an-expression, but not a lex error
    fn expect_error(input: &str) {
        let tokens = scan(input).unwrap();
        let mut tokens = tokens.into_iter();
        assert!(parse_expression(&mut tokens, |t| t == TokenType::NewLine).is_err());
    }

    #[test]
    fn test_expression_parsing() {
        expect_optimal("bool");
        expect_optimal("p -> (q -> p)");
        expect_optimal("(p -> (q -> r)) -> ((p -> q) -> (p -> r))");
        expect_optimal("(!p -> !q) -> (q -> p)");
        expect_optimal("p | q = !p -> q");
        expect_optimal("p & q = !(p -> !q)");
        expect_optimal("p <-> q = (p -> q) & (q -> p)");
        expect_optimal("p & q <-> q & p");
        expect_optimal("(p & q) & r <-> p & (q & r)");
        expect_optimal("p | q <-> q | p");
        expect_optimal("(p | q) | r <-> p | (q | r)");
    }

    #[test]
    fn test_expression_errors() {
        expect_error("+ + +");

        // Not expressions
        expect_error("let a: int = x + 2");
        expect_error("axiom contraposition: (!p -> !q) -> (q -> p)");
        expect_error("def (p & q) = !(p -> !q)");
    }
}
