use std::{collections::VecDeque, fmt};

use crate::token::Token;

// An Expression represents a mathematical expression, like 2 + 2 or (P -> Q).
pub enum Expression<'a> {
    Identifier(&'a str),
    Unary(&'a Token, Box<Expression<'a>>),
    Binary(&'a Token, Box<Expression<'a>>, Box<Expression<'a>>),
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
                    write!(f, " {} ", token)?;
                    right.fmt_helper(f, p, 0)?;
                    write!(f, ")")
                } else {
                    // We don't need to parenthesize.
                    left.fmt_helper(f, left_p, p)?;
                    write!(f, " {} ", token)?;
                    right.fmt_helper(f, p, right_p)
                }
            }
        }
    }
}

// A PartialExpression represents a state in the middle of parsing, where we can have
// either subexpressions or operators, and we haven't prioritized operators yet.
// A list of partial expressions can be turned into an expression, according to operator precedence.
enum PartialExpression<'a> {
    Expression(Expression<'a>),
    Unary(&'a Token),
    Binary(&'a Token),
}

// Create partial expressions from tokens.
// terminator is the token we expect to end the expression, which is consumed.
fn parse_partial_expressions<'a>(
    tokens: &mut impl Iterator<Item = &'a Token>,
    terminator: &Token,
) -> VecDeque<PartialExpression<'a>> {
    let mut partial_expressions = VecDeque::new();
    while let Some(token) = tokens.next() {
        match token {
            Token::LeftParen => {
                let subexpression = parse_expression(tokens, &Token::RightParen);
                partial_expressions.push_back(PartialExpression::Expression(subexpression));
            }
            Token::Identifier(s) => {
                partial_expressions
                    .push_back(PartialExpression::Expression(Expression::Identifier(s)));
            }
            token if token.is_binary() => {
                partial_expressions.push_back(PartialExpression::Binary(token));
            }
            token if token.is_unary() => {
                partial_expressions.push_back(PartialExpression::Unary(token));
            }
            token => {
                if token == terminator {
                    return partial_expressions;
                }
                panic!("unexpected token: {:?}", token);
            }
        }
    }
    panic!("unexpected end of input");
}

// Combines partial expressions into a single expression.
// Operators work in precedence order, and left-to-right within a single precedence.
// This algorithm is quadratic, so perhaps we should improve it at some point.
fn combine_partial_expressions<'a>(
    mut partials: VecDeque<PartialExpression<'a>>,
) -> Expression<'a> {
    if partials.len() == 0 {
        panic!("no partial expressions to combine");
    }
    if partials.len() == 1 {
        if let Some(PartialExpression::Expression(e)) = partials.pop_back() {
            return e;
        }
        panic!("expected an expression");
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
        panic!("operators should not have precedence 0");
    }

    if index == 0 {
        if let Some(PartialExpression::Unary(token)) = partials.pop_front() {
            return Expression::Unary(token, Box::new(combine_partial_expressions(partials)));
        }
        panic!("expected unary operator");
    }

    let mut right_partials = partials.split_off(index);
    if let Some(PartialExpression::Binary(token)) = right_partials.pop_front() {
        return Expression::Binary(
            token,
            Box::new(combine_partial_expressions(partials)),
            Box::new(combine_partial_expressions(right_partials)),
        );
    }
    panic!("expected binary operator");
}

// Parses a single expression from the provided tokens.
// terminator is the token we expect to end the expression, which is consumed.
pub fn parse_expression<'a>(
    tokens: &mut impl Iterator<Item = &'a Token>,
    terminator: &Token,
) -> Expression<'a> {
    let partial_expressions = parse_partial_expressions(tokens, terminator);
    combine_partial_expressions(partial_expressions)
}

#[cfg(test)]
mod tests {
    use crate::token::scan;

    use super::*;

    fn expect_optimal(input: &str) {
        let tokens = scan(input);
        let mut tokens = tokens.iter();
        let exp = parse_expression(&mut tokens, &Token::NewLine);
        let output = exp.to_string();
        assert_eq!(input, output);
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
}
