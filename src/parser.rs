use crate::scanner::Token;

// An Expression represents a mathematical expression, like 2 + 2 or (P -> Q).
pub enum Expression {
    Identifier(String),
    Unary(Token, Box<Expression>),
    Binary(Token, Box<Expression>, Box<Expression>),
}

// A PartialExpression represents a state in the middle of parsing, where we can have
// either subexpressions or operators, and we haven't prioritized operators yet.
// A list of partial expressions can be turned into an expression, according to operator priority.
enum PartialExpression {
    Expression(Expression),
    Unary(Token),
    Binary(Token),
}

// Create partial expressions from tokens.
// If expect_paren is set, we expect the list of partial expressions to end with a right paren.
// Otherwise, we expect it to end with a newline.
// Either way, this ending token is consumed.
fn parse_partial_expressions(
    tokens: &mut impl Iterator<Item = Token>,
    expect_paren: bool,
) -> Vec<PartialExpression> {
    let mut partial_expressions = Vec::new();
    while let Some(token) = tokens.next() {
        match token {
            Token::LeftParen => {
                let subexpression = parse_expression(tokens, true);
                partial_expressions.push(PartialExpression::Expression(subexpression));
            }
            Token::Identifier(_) => {
                partial_expressions.push(PartialExpression::Expression(Expression::Identifier(
                    token.to_string(),
                )));
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
                partial_expressions.push(PartialExpression::Binary(token));
            }
            token if token.is_unary() => {
                partial_expressions.push(PartialExpression::Unary(token));
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
fn combine_partial_expressions(partials: &[PartialExpression]) -> Expression {
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
        if let PartialExpression::Unary(token) = &partials[0] {
            return Expression::Unary(
                token.clone(),
                Box::new(combine_partial_expressions(&partials[1..])),
            );
        }
        panic!("expected unary operator");
    }

    if let PartialExpression::Binary(token) = &partials[index] {
        let left = combine_partial_expressions(&partials[..index]);
        let right = combine_partial_expressions(&partials[index + 1..]);
        return Expression::Binary(token.clone(), Box::new(left), Box::new(right));
    }
    panic!("expected binary operator");
}

// Parses a single expression from the provided tokens.
// If expect_paren is set, we expect this expression to end with a right paren.
// Otherwise, we expect it to end with a newline.
// Either way, this ending token is consumed.
pub fn parse_expression(
    tokens: &mut impl Iterator<Item = Token>,
    expect_paren: bool,
) -> Expression {
    let partial_expressions = parse_partial_expressions(tokens, expect_paren);
    combine_partial_expressions(&partial_expressions)
}
