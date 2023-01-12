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
    pub fn precedence(&self) -> i8 {
        self.token_type.precedence()
    }
}

#[derive(Debug)]
pub enum Error {
    Token(TokenError),
    EOF,
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
                write!(f, "{}\n", e.message)?;
                fmt_line_part(f, &e.text, &e.line, e.index)
            }
            Error::EOF => write!(f, "unexpected end of file"),
        }
    }
}

impl Error {
    pub fn new(token: &Token, message: String) -> Self {
        Error::Token(TokenError {
            message,
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
                return Err(Error::new(&token, format!("invalid token: {}", text)));
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
    Ok(tokens.next().expect("unexpected EOF"))
}

// Pops off one token, expecting it to be of a known type.
pub fn expect_type<'a, I>(tokens: &mut Peekable<I>, expected: TokenType) -> Result<Token<'a>>
where
    I: Iterator<Item = Token<'a>>,
{
    let token = tokens.next().expect("unexpected EOF");
    if token.token_type != expected {
        return Err(Error::new(&token, format!("expected {:?}", expected)));
    }
    Ok(token)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scanning() {
        assert_eq!(scan("theorem t:A->B").unwrap().len(), 7);
        assert_eq!(scan("theorem _t:A->B").unwrap().len(), 7);
    }
}
