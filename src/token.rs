use std::{fmt, iter::Peekable};

#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TokenType {
    Identifier,
    Invalid,
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    NewLine,
    Comma,
    Colon,
    RightArrow,
    Exclam,
    Pipe,
    Ampersand,
    LeftRightArrow,
    Equals,
    Plus,
    Minus,
    Let,
    Axiom,
    Def,
    Theorem,
}

impl TokenType {
    pub fn is_unary(&self) -> bool {
        match self {
            TokenType::Exclam => true,
            _ => false,
        }
    }

    pub fn is_binary(&self) -> bool {
        match self {
            TokenType::Plus => true,
            TokenType::Minus => true,
            TokenType::RightArrow => true,
            TokenType::Pipe => true,
            TokenType::Ampersand => true,
            TokenType::LeftRightArrow => true,
            TokenType::Equals => true,
            _ => false,
        }
    }

    // Higher precedence operators are evaluated first.
    // It is an error to not specify the order when the precedence is the same.
    // Only unary and binary operators should have precedences.
    pub fn precedence(&self) -> i8 {
        match self {
            TokenType::Plus => 6,
            TokenType::Minus => 6,
            TokenType::Exclam => 5,
            TokenType::Equals => 4,
            TokenType::Pipe => 3,
            TokenType::Ampersand => 3,
            TokenType::LeftRightArrow => 2,
            TokenType::RightArrow => 1,
            _ => 0,
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Token<'a> {
    pub token_type: TokenType,
    pub text: &'a str,
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.text)
    }
}

impl Token<'_> {
    pub fn precedence(&self) -> i8 {
        self.token_type.precedence()
    }
}

fn identifierish(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_'
}

pub fn scan(input: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut char_indices = input.char_indices().peekable();

    while let Some((pos, ch)) = char_indices.next() {
        let token_type = match ch {
            ' ' => continue,
            '\t' => continue,
            '(' => TokenType::LeftParen,
            ')' => TokenType::RightParen,
            '{' => TokenType::LeftBrace,
            '}' => TokenType::RightBrace,
            '\n' => TokenType::NewLine,
            ',' => TokenType::Comma,
            ':' => TokenType::Colon,
            '!' => TokenType::Exclam,
            '|' => TokenType::Pipe,
            '&' => TokenType::Ampersand,
            '=' => TokenType::Equals,
            '+' => TokenType::Plus,
            '-' => match char_indices.next_if_eq(&(pos + 1, '>')) {
                Some(_) => TokenType::RightArrow,
                None => TokenType::Minus,
            },
            '<' => match char_indices.next_if_eq(&(pos + 1, '-')) {
                Some(_) => match char_indices.next_if_eq(&(pos + 2, '>')) {
                    Some(_) => TokenType::LeftRightArrow,
                    None => TokenType::Invalid,
                },
                None => TokenType::Invalid,
            },
            '/' => match char_indices.next_if_eq(&(pos + 1, '/')) {
                Some(_) => {
                    // Advance to the end of the line
                    while let Some((_, ch)) = char_indices.next() {
                        if ch == '\n' {
                            break;
                        }
                    }
                    TokenType::NewLine
                }
                None => TokenType::Invalid,
            },
            t if identifierish(t) => {
                let end = loop {
                    match char_indices.peek() {
                        Some((_, ch)) if identifierish(*ch) => {
                            char_indices.next();
                        }
                        Some((end, _)) => break *end,
                        None => break input.len(),
                    }
                };
                let identifier = &input[pos..end];
                match identifier {
                    "let" => TokenType::Let,
                    "axiom" => TokenType::Axiom,
                    "def" => TokenType::Def,
                    "theorem" => TokenType::Theorem,
                    _ => TokenType::Identifier,
                }
            }
            _ => TokenType::Invalid,
        };
        let end = if let Some((pos, _)) = char_indices.peek() {
            *pos
        } else {
            input.len()
        };
        let text = &input[pos..end];
        tokens.push(Token { token_type, text });
    }

    // Add a newline if the last token is not a newline
    if let Some(token) = tokens.last() {
        if token.token_type != TokenType::NewLine {
            tokens.push(Token {
                token_type: TokenType::NewLine,
                text: "",
            });
        }
    }

    tokens
}

// Pops off one token, expecting it to be there.
pub fn expect_token<'a, I>(tokens: &mut Peekable<I>) -> Token<'a>
where
    I: Iterator<Item = Token<'a>>,
{
    tokens.next().expect("unexpected EOF")
}

// Pops off one token, expecting it to be of a known type.
pub fn expect_type<'a, I>(tokens: &mut Peekable<I>, expected: TokenType) -> Token<'a>
where
    I: Iterator<Item = Token<'a>>,
{
    let token = tokens.next().expect("unexpected EOF");
    if token.token_type != expected {
        panic!("expected {:?}, got {:?}", expected, token.token_type);
    }
    token
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scanning() {
        assert_eq!(scan("theorem t:A->B").len(), 7);
        assert_eq!(scan("theorem _t:A->B").len(), 7);
    }
}
