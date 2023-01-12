use std::{fmt, iter::Peekable, str::CharIndices};

#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Token<'a> {
    Identifier(&'a str),
    Invalid(&'a str),
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

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Identifier(s) => write!(f, "{}", s),
            Token::Invalid(s) => write!(f, "Invalid({})", s),
            Token::LeftParen => write!(f, "("),
            Token::RightParen => write!(f, ")"),
            Token::LeftBrace => write!(f, "{{"),
            Token::RightBrace => write!(f, "}}"),
            Token::NewLine => write!(f, "\\n"),
            Token::Comma => write!(f, ","),
            Token::Colon => write!(f, ":"),
            Token::RightArrow => write!(f, "->"),
            Token::Exclam => write!(f, "!"),
            Token::Pipe => write!(f, "|"),
            Token::Ampersand => write!(f, "&"),
            Token::LeftRightArrow => write!(f, "<->"),
            Token::Equals => write!(f, "="),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Let => write!(f, "let"),
            Token::Axiom => write!(f, "axiom"),
            Token::Def => write!(f, "def"),
            Token::Theorem => write!(f, "theorem"),
        }
    }
}

impl Token<'_> {
    pub fn is_unary(&self) -> bool {
        match self {
            Token::Exclam => true,
            _ => false,
        }
    }

    pub fn is_binary(&self) -> bool {
        match self {
            Token::Plus => true,
            Token::Minus => true,
            Token::RightArrow => true,
            Token::Pipe => true,
            Token::Ampersand => true,
            Token::LeftRightArrow => true,
            Token::Equals => true,
            _ => false,
        }
    }

    // Higher precedence operators are evaluated first.
    // It is an error to not specify the order when the precedence is the same.
    // Only unary and binary operators should have precedences.
    pub fn precedence(&self) -> i8 {
        match self {
            Token::Plus => 6,
            Token::Minus => 6,
            Token::Exclam => 5,
            Token::Equals => 4,
            Token::Pipe => 3,
            Token::Ampersand => 3,
            Token::LeftRightArrow => 2,
            Token::RightArrow => 1,
            _ => 0,
        }
    }
}

fn identifierish(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_'
}

// Returns the slice ending at this iterator.
fn get_slice<'a>(input: &'a str, begin: usize, iter: &mut Peekable<CharIndices<'_>>) -> &'a str {
    let end = if let Some((pos, _)) = iter.peek() {
        *pos
    } else {
        input.len()
    };
    &input[begin..end]
}

pub fn scan(input: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut char_indices = input.char_indices().peekable();

    while let Some((pos, ch)) = char_indices.next() {
        let token = match ch {
            ' ' => continue,
            '\t' => continue,
            '(' => Token::LeftParen,
            ')' => Token::RightParen,
            '{' => Token::LeftBrace,
            '}' => Token::RightBrace,
            '\n' => Token::NewLine,
            ',' => Token::Comma,
            ':' => Token::Colon,
            '!' => Token::Exclam,
            '|' => Token::Pipe,
            '&' => Token::Ampersand,
            '=' => Token::Equals,
            '+' => Token::Plus,
            '-' => match char_indices.next_if_eq(&(pos + 1, '>')) {
                Some(_) => Token::RightArrow,
                None => Token::Minus,
            },
            '<' => match char_indices.next_if_eq(&(pos + 1, '-')) {
                Some(_) => match char_indices.next_if_eq(&(pos + 2, '>')) {
                    Some(_) => Token::LeftRightArrow,
                    None => Token::Invalid(get_slice(input, pos, &mut char_indices)),
                },
                None => Token::Invalid(get_slice(input, pos, &mut char_indices)),
            },
            '/' => match char_indices.next_if_eq(&(pos + 1, '/')) {
                Some(_) => {
                    // Advance to the end of the line
                    while let Some((_, ch)) = char_indices.next() {
                        if ch == '\n' {
                            break;
                        }
                    }
                    Token::NewLine
                }
                None => Token::Invalid(get_slice(input, pos, &mut char_indices)),
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
                    "let" => Token::Let,
                    "axiom" => Token::Axiom,
                    "def" => Token::Def,
                    "theorem" => Token::Theorem,
                    _ => Token::Identifier(identifier),
                }
            }
            _ => Token::Invalid(get_slice(input, pos, &mut char_indices)),
        };
        tokens.push(token);
    }

    // Add a newline if the last token is not a newline
    if let Some(Token::NewLine) = tokens.last() {
    } else {
        tokens.push(Token::NewLine);
    }

    tokens
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scanning() {
        assert!(scan("theorem t:A->B").len() == 7);
        assert!(scan("theorem _t:A->B").len() == 7);
    }
}
