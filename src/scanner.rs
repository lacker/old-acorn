use std::fmt;

#[derive(Debug, Eq, PartialEq)]
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
        }
    }
}

pub fn scan(input: String) -> Vec<Token> {
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
            t if t.is_alphabetic() => {
                let mut identifier = String::new();
                identifier.push(t);
                while let Some((_, ch)) = char_indices.peek() {
                    if ch.is_alphanumeric() || ch == &'_' {
                        identifier.push(*ch);
                        char_indices.next();
                    } else {
                        break;
                    }
                }
                Token::Identifier(identifier)
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
        let tokens = scan("theorem t:A->B".to_string());
        assert!(tokens.len() == 7);
    }
}
