use std::fmt;

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Token {
    Identifier(String),
    Invalid(String),
    LeftParen,
    RightParen,
    NewLine,
    Comma,
    Colon,
    RightArrow,
    Exclam,
    Pipe,
    Ampersand,
    LeftRightArrow,
    Equals,
    Let,
    Axiom,
    Define,
    Theorem,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Identifier(s) => write!(f, "{}", s),
            Token::Invalid(s) => write!(f, "Invalid({})", s),
            Token::LeftParen => write!(f, "("),
            Token::RightParen => write!(f, ")"),
            Token::NewLine => write!(f, "\\n"),
            Token::Comma => write!(f, ","),
            Token::Colon => write!(f, ":"),
            Token::RightArrow => write!(f, "->"),
            Token::Exclam => write!(f, "!"),
            Token::Pipe => write!(f, "|"),
            Token::Ampersand => write!(f, "&"),
            Token::LeftRightArrow => write!(f, "<->"),
            Token::Equals => write!(f, "="),
            Token::Let => write!(f, "let"),
            Token::Axiom => write!(f, "axiom"),
            Token::Define => write!(f, "define"),
            Token::Theorem => write!(f, "theorem"),
        }
    }
}

impl Token {
    pub fn is_unary(&self) -> bool {
        match self {
            Token::Exclam => true,
            _ => false,
        }
    }

    pub fn is_binary(&self) -> bool {
        match self {
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
    pub fn precedence(&self) -> u8 {
        match self {
            Token::Exclam => 4,
            Token::Pipe => 3,
            Token::Ampersand => 3,
            Token::LeftRightArrow => 2,
            Token::RightArrow => 2,
            Token::Equals => 1,
            _ => 0,
        }
    }
}

fn identifierish(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_'
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
            '\n' => Token::NewLine,
            ',' => Token::Comma,
            ':' => Token::Colon,
            '!' => Token::Exclam,
            '|' => Token::Pipe,
            '&' => Token::Ampersand,
            '=' => Token::Equals,
            '-' => match char_indices.next_if_eq(&(pos + 1, '>')) {
                Some(_) => Token::RightArrow,
                None => Token::Invalid("-".to_string()),
            },
            '<' => match char_indices.next_if_eq(&(pos + 1, '-')) {
                Some(_) => match char_indices.next_if_eq(&(pos + 2, '>')) {
                    Some(_) => Token::LeftRightArrow,
                    None => Token::Invalid("<-".to_string()),
                },
                None => Token::Invalid("<".to_string()),
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
                None => Token::Invalid("/".to_string()),
            },
            t if identifierish(t) => {
                let mut identifier = String::new();
                identifier.push(t);
                while let Some((_, ch)) = char_indices.peek() {
                    if identifierish(*ch) {
                        identifier.push(*ch);
                        char_indices.next();
                    } else {
                        break;
                    }
                }
                match identifier.as_str() {
                    "let" => Token::Let,
                    "axiom" => Token::Axiom,
                    "define" => Token::Define,
                    "theorem" => Token::Theorem,
                    _ => Token::Identifier(identifier),
                }
            }
            _ => Token::Invalid(format!("{}", ch)),
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
