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
                panic!("XXX");
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

fn combine_partial_expressions(partials: &[PartialExpression]) -> Expression {
    panic!("XXX");
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
