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
// "Apply" is the application of a function. The second expression must be an arg list.
// "Grouping" is another expression enclosed in parentheses.
// "Block" is another expression enclosed in braces. Just one for now.
// "Macro" is the application of a macro.
//   The second expression must be an arg list.
//   Macros include the terminating brace as a token.
#[derive(Debug)]
pub enum Expression {
    Identifier(Token),
    Unary(Token, Box<Expression>),
    Binary(Box<Expression>, Token, Box<Expression>),
    Apply(Box<Expression>, Box<Expression>),
    Grouping(Token, Box<Expression>, Token),
    Macro(Token, Box<Expression>, Box<Expression>, Token),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Identifier(token) => write!(f, "{}", token),
            Expression::Unary(token, subexpression) => {
                write!(f, "{}{}", token, subexpression)
            }
            Expression::Binary(left, token, right) => {
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
            Expression::Grouping(_, e, _) => {
                write!(f, "({})", e)
            }
            Expression::Macro(token, args, sub, _) => {
                write!(f, "{}{} {{ {} }}", token, args, sub)
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
            Expression::Macro(token, _, _, _) => token,
        }
    }

    pub fn first_token(&self) -> &Token {
        match self {
            Expression::Identifier(token) => token,
            Expression::Unary(token, _) => token,
            Expression::Binary(left, _, _) => left.first_token(),
            Expression::Apply(left, _) => left.first_token(),
            Expression::Grouping(left_paren, _, _) => left_paren,
            Expression::Macro(token, _, _, _) => token,
        }
    }

    pub fn last_token(&self) -> &Token {
        match self {
            Expression::Identifier(token) => token,
            Expression::Unary(_, subexpression) => subexpression.last_token(),
            Expression::Binary(_, _, right) => right.last_token(),
            Expression::Apply(_, right) => right.last_token(),
            Expression::Grouping(_, _, right_paren) => right_paren,
            Expression::Macro(_, _, _, right_brace) => right_brace,
        }
    }

    pub fn range(&self) -> Range {
        Range {
            start: self.first_token().start_pos(),
            end: self.last_token().end_pos(),
        }
    }

    // Expects the expression to be a list of comma-separated expressions
    // Gets rid of commas and groupings
    pub fn flatten_arg_list(&self) -> Vec<&Expression> {
        match self {
            Expression::Binary(left, token, right) => {
                if token.token_type == TokenType::Comma {
                    let mut args = left.flatten_arg_list();
                    args.append(&mut right.flatten_arg_list());
                    args
                } else {
                    vec![&self]
                }
            }
            Expression::Grouping(_, e, _) => e.flatten_arg_list(),
            _ => vec![&self],
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
}

// A PartialExpression represents a state in the middle of parsing, where we can have
// either subexpressions or operators, and we haven't prioritized operators yet.
// A list of partial expressions can be turned into an expression, according to operator precedence.
#[derive(Debug)]
enum PartialExpression {
    Expression(Expression),
    Unary(Token),
    Binary(Token),
    Block(Token, Expression, Token),
}

impl fmt::Display for PartialExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PartialExpression::Expression(e) => write!(f, "{}", e),
            PartialExpression::Unary(token) => write!(f, "{}", token),
            PartialExpression::Binary(token) => write!(f, "{}", token),
            PartialExpression::Block(_, e, _) => write!(f, "{{ {} }}", e),
        }
    }
}

impl PartialExpression {
    fn token(&self) -> &Token {
        match self {
            PartialExpression::Expression(e) => e.token(),
            PartialExpression::Unary(token) => token,
            PartialExpression::Binary(token) => token,
            PartialExpression::Block(token, _, _) => token,
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
    let mut partial_expressions = VecDeque::<PartialExpression>::new();
    while let Some(token) = tokens.next() {
        if termination(token.token_type) {
            return Ok((partial_expressions, token));
        }
        if token.token_type.is_binary() {
            partial_expressions.push_back(PartialExpression::Binary(token));
            continue;
        }
        if token.token_type.is_unary() {
            partial_expressions.push_back(PartialExpression::Unary(token));
            continue;
        }
        match token.token_type {
            TokenType::LeftParen => {
                let (subexpression, last_token) =
                    Expression::parse(tokens, is_value, |t| t == TokenType::RightParen)?;
                let group = Expression::Grouping(token, Box::new(subexpression), last_token);
                partial_expressions.push_back(PartialExpression::Expression(group));
            }
            TokenType::Identifier
            | TokenType::Axiom
            | TokenType::ForAll
            | TokenType::Exists
            | TokenType::Function => {
                partial_expressions
                    .push_back(PartialExpression::Expression(Expression::Identifier(token)));
            }
            TokenType::LeftBrace => {
                let (subexp, right_brace) =
                    Expression::parse(tokens, is_value, |t| t == TokenType::RightBrace)?;
                partial_expressions.push_back(PartialExpression::Block(token, subexp, right_brace));
            }
            TokenType::NewLine => {
                // Ignore newlines. The case where the newline is a terminator, we already caught.
            }
            _ => {
                return Err(Error::new(
                    &token,
                    &format!("expected partial expression or terminator: {:?}", token),
                ));
            }
        }
    }
    Err(tokens.error("expected expression but got EOF"))
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
        return Err(Error::new(partial.token(), "expected an expression"));
    }

    // Find the index of the operator that should operate last
    let (neg_precedence, index) = match partials
        .iter()
        .enumerate()
        .filter_map(|(i, partial)| match partial {
            PartialExpression::Expression(_) | PartialExpression::Block(_, _, _) => None,
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
            let first_partial = partials.pop_front().unwrap();

            // Check if this is a macro.
            if let PartialExpression::Expression(Expression::Identifier(token)) = &first_partial {
                if token.token_type.is_macro() {
                    if partials.len() != 2 {
                        return Err(Error::new(&token, "macro must have arguments and a block"));
                    }
                    let expect_args = partials.pop_front().unwrap();
                    if let PartialExpression::Expression(args) = expect_args {
                        let expect_block = partials.pop_back().unwrap();
                        if let PartialExpression::Block(_, block, right_brace) = expect_block {
                            return Ok(Expression::Macro(
                                token.clone(),
                                Box::new(args),
                                Box::new(block),
                                right_brace,
                            ));
                        } else {
                            return Err(Error::new(expect_block.token(), "expected a macro block"));
                        }
                    }
                    return Err(Error::new(expect_args.token(), "expected macro arguments"));
                }
            }

            // Otherwise, this must be a sequence of function applications.
            let mut answer = match first_partial {
                PartialExpression::Expression(e) => e,
                _ => return Err(Error::new(first_partial.token(), "expected an expression")),
            };
            for partial in partials.into_iter() {
                if let PartialExpression::Expression(expr) = partial {
                    match expr {
                        Expression::Grouping(_, _, _) => {
                            answer = Expression::Apply(Box::new(answer), Box::new(expr))
                        }
                        _ => return Err(Error::new(expr.token(), "expected a grouping")),
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

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_parse(input: &str, is_value: bool) -> String {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let exp = match Expression::parse(&mut tokens, is_value, |t| t == TokenType::NewLine) {
            Ok((e, _)) => e,
            Err(e) => panic!("unexpected error parsing: {}", e),
        };
        exp.to_string()
    }

    fn expect_optimal(input: &str, is_value: bool) {
        let output = expect_parse(input, is_value);
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
}
