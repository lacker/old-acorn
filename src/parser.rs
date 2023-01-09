use std::collections::VecDeque;

use crate::scanner::Token;

// An Expression represents a mathematical expression, like 2 + 2 or (P -> Q).
pub enum Expression<'a> {
    Identifier(&'a Token),
    Unary(&'a Token, Box<Expression<'a>>),
    Binary(&'a Token, Box<Expression<'a>>, Box<Expression<'a>>),
}

// A PartialExpression represents a state in the middle of parsing, where we can have
// either subexpressions or operators, and we haven't prioritized operators yet.
// A list of partial expressions can be turned into an expression, according to operator priority.
enum PartialExpression<'a> {
    Expression(Expression<'a>),
    Unary(&'a Token),
    Binary(&'a Token),
}

// Create partial expressions from tokens.
// If expect_paren is set, we expect the list of partial expressions to end with a right paren.
// Otherwise, we expect it to end with a newline.
// Either way, this ending token is consumed.
fn parse_partial_expressions<'a>(
    tokens: &mut impl Iterator<Item = &'a Token>,
    expect_paren: bool,
) -> VecDeque<PartialExpression<'a>> {
    let mut partial_expressions = VecDeque::new();
    while let Some(token) = tokens.next() {
        match token {
            Token::LeftParen => {
                let subexpression = parse_expression(tokens, true);
                partial_expressions.push_back(PartialExpression::Expression(subexpression));
            }
            Token::Identifier(_) => {
                partial_expressions.push_back(PartialExpression::Expression(
                    Expression::Identifier(&token),
                ));
            }
            Token::NewLine => {
                if expect_paren {
                    // We can ignore newlines that are inside parentheses, Python-style.
                    continue;
                }
                return partial_expressions;
            }
            Token::RightParen => {
                if expect_paren {
                    return partial_expressions;
                }
                panic!("extra right parenthesis");
            }
            token if token.is_binary() => {
                partial_expressions.push_back(PartialExpression::Binary(token));
            }
            token if token.is_unary() => {
                partial_expressions.push_back(PartialExpression::Unary(token));
            }
            token => {
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
// If expect_paren is set, we expect this expression to end with a right paren.
// Otherwise, we expect it to end with a newline.
// Either way, this ending token is consumed.
pub fn parse_expression<'a>(
    tokens: &mut impl Iterator<Item = &'a Token>,
    expect_paren: bool,
) -> Expression<'a> {
    let partial_expressions = parse_partial_expressions(tokens, expect_paren);
    combine_partial_expressions(partial_expressions)
}

#[cfg(test)]
mod tests {
    use crate::scanner::scan;

    use super::*;

    fn parse_ok(input: &str) {
        let tokens = scan(input);
        let mut tokens = tokens.iter();
        parse_expression(&mut tokens, false);
    }

    #[test]
    fn test_expression_parsing() {
        parse_ok("bool");
        parse_ok("p -> (q -> p)");
        parse_ok("(p -> (q -> r)) -> ((p -> q) -> (p -> r))");
        parse_ok("(!p -> !q) -> (q -> p)");
        parse_ok("(p | q) = !p -> q");
        parse_ok("(p & q) = !(p -> !q)");
        parse_ok("(p <-> q) = (p -> q) & (q -> p)");
        parse_ok("p & q <-> q & p");
        parse_ok("(p & q) & r <-> p & (q & r)");
        parse_ok("p | q <-> q | p");
        parse_ok("(p | q) | r <-> p | (q | r)");
    }
}
