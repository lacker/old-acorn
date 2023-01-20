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
    Define,
    Theorem,
    Typedef,
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
            TokenType::Comma => true,
            TokenType::Colon => true,
            _ => false,
        }
    }

    // Higher precedence operators are bound to arguments first.
    // It is an error to not specify the order when the precedence is the same.
    // Only unary and binary operators should have precedences.
    // There are two precedences: for operators in a value, like 2 + 2, and operators in
    // a type expression, like (int -> int) -> int.
    // Operators that are not allowed in an expression have a precedence of 0.
    pub fn value_precedence(&self) -> i8 {
        match self {
            TokenType::Plus => 7,
            TokenType::Minus => 7,
            TokenType::Equals => 6,
            TokenType::Exclam => 5,
            TokenType::Pipe => 4,
            TokenType::Ampersand => 4,
            TokenType::LeftRightArrow => 3,
            TokenType::RightArrow => 2,
            _ => 0,
        }
    }

    pub fn type_precedence(&self) -> i8 {
        match self {
            TokenType::RightArrow => 3,
            TokenType::Comma => 2,
            TokenType::Colon => 1,
            _ => 0,
        }
    }

    // Whether we put a space to the left of this operator in the canonical style.
    pub fn left_space(&self) -> bool {
        match self {
            TokenType::Comma => false,
            TokenType::Colon => false,
            _ => true,
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Token<'a> {
    pub token_type: TokenType,

    // The text of the token.
    pub text: &'a str,

    // The entire line containing this token.
    pub line: &'a str,

    // The index of this token within the line.
    // Can be equal to line.len() if it's the final newline.
    pub index: usize,
}

fn fmt_line_part(f: &mut fmt::Formatter<'_>, text: &str, line: &str, index: usize) -> fmt::Result {
    write!(f, "{}\n", line)?;
    for (i, _) in line.char_indices() {
        if i < index {
            write!(f, " ")?;
        } else if i < index + text.len() {
            write!(f, "^")?;
        }
    }
    if index >= line.len() {
        // The token is the final newline.
        write!(f, "^")?;
    }
    write!(f, "\n")
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.text)
    }
}

impl Token<'_> {
    pub fn value_precedence(&self) -> i8 {
        self.token_type.value_precedence()
    }

    pub fn type_precedence(&self) -> i8 {
        self.token_type.type_precedence()
    }

    pub fn precedence(&self, is_value: bool) -> i8 {
        if is_value {
            self.value_precedence()
        } else {
            self.type_precedence()
        }
    }
}

#[derive(Debug)]
pub enum Error {
    Token(TokenError),
    EOF,

    // Errors that we can't figure out how to categorize well
    Misc(String),
}

#[derive(Debug)]
pub struct TokenError {
    message: String,
    text: String,
    line: String,
    index: usize,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Token(e) => {
                write!(f, "{}:\n", e.message)?;
                fmt_line_part(f, &e.text, &e.line, e.index)
            }
            Error::EOF => write!(f, "unexpected end of file"),
            Error::Misc(s) => write!(f, "{}", s),
        }
    }
}

impl Error {
    pub fn new(token: &Token, message: &str) -> Self {
        Error::Token(TokenError {
            message: message.to_string(),
            text: token.text.to_string(),
            line: token.line.to_string(),
            index: token.index,
        })
    }
}

pub type Result<'a, T> = std::result::Result<T, Error>;

fn identifierish(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_'
}

pub fn scan(input: &str) -> Result<Vec<Token>> {
    let mut tokens = Vec::new();

    for line in input.lines() {
        let mut char_indices = line.char_indices().peekable();
        while let Some((index, ch)) = char_indices.next() {
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
                '-' => match char_indices.next_if_eq(&(index + 1, '>')) {
                    Some(_) => TokenType::RightArrow,
                    None => TokenType::Minus,
                },
                '<' => match char_indices.next_if_eq(&(index + 1, '-')) {
                    Some(_) => match char_indices.next_if_eq(&(index + 2, '>')) {
                        Some(_) => TokenType::LeftRightArrow,
                        None => TokenType::Invalid,
                    },
                    None => TokenType::Invalid,
                },
                '/' => match char_indices.next_if_eq(&(index + 1, '/')) {
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
                    let identifier = &input[index..end];
                    match identifier {
                        "let" => TokenType::Let,
                        "axiom" => TokenType::Axiom,
                        "define" => TokenType::Define,
                        "theorem" => TokenType::Theorem,
                        "typedef" => TokenType::Typedef,
                        _ => TokenType::Identifier,
                    }
                }
                _ => TokenType::Invalid,
            };
            let end = if let Some((pos, _)) = char_indices.peek() {
                *pos
            } else {
                line.len()
            };
            let text = &line[index..end];
            let token = Token {
                token_type,
                text,
                line,
                index,
            };
            if token.token_type == TokenType::Invalid {
                return Err(Error::new(&token, &format!("invalid token: {}", text)));
            }
            tokens.push(token);
        }

        // Add a newline
        tokens.push(Token {
            token_type: TokenType::NewLine,
            text: "\n",
            line,
            index: input.len(),
        });
    }

    Ok(tokens)
}

// Pops off one token, expecting it to be there.
pub fn expect_token<'a, I>(tokens: &mut Peekable<I>) -> Result<Token<'a>>
where
    I: Iterator<Item = Token<'a>>,
{
    tokens.next().ok_or(Error::EOF)
}

// Pops off one token, expecting it to be of a known type.
pub fn expect_type<'a, I>(tokens: &mut Peekable<I>, expected: TokenType) -> Result<Token<'a>>
where
    I: Iterator<Item = Token<'a>>,
{
    let token = match tokens.next() {
        Some(t) => t,
        None => return Err(Error::EOF),
    };
    if token.token_type != expected {
        return Err(Error::new(&token, &format!("expected {:?}", expected)));
    }
    Ok(token)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scanning_ok() {
        assert_eq!(scan("theorem t:A->B").unwrap().len(), 7);
        assert_eq!(scan("theorem _t:A->B").unwrap().len(), 7);
    }

    #[test]
    fn test_scanning_errors() {
        assert!(scan("#$@%(#@)(#").is_err());
    }
}
