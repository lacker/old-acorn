use std::fmt;

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
    NotEquals,
    GreaterThan,
    LessThan,
    GreaterThanOrEquals,
    LessThanOrEquals,
    Plus,
    Minus,
    Let,
    Axiom,
    Define,
    Theorem,
    Type,
    ForAll,
    Exists,
    If,
    By,
    Function,
}

pub const MAX_PRECEDENCE: i8 = 100;

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
            TokenType::NotEquals => true,
            TokenType::GreaterThan => true,
            TokenType::LessThan => true,
            TokenType::GreaterThanOrEquals => true,
            TokenType::LessThanOrEquals => true,
            TokenType::Comma => true,
            TokenType::Colon => true,
            _ => false,
        }
    }

    // Associative operators don't have to be parenthesized in a sequence because it doesn't matter.
    pub fn always_associative(&self) -> bool {
        match self {
            TokenType::Comma => true,
            _ => false,
        }
    }

    // Higher precedence operators are bound to arguments first.
    // It is an error to not specify the order when the precedence is the same.
    // Only unary and binary operators should have precedences.
    // There are two precedences: for operators in a value, like 2 + 2, and operators in
    // a type expression, like (int -> int) -> int.
    // Operators that are not allowed in an expression have a precedence of 0.
    // "Value" expressions also include "declarations" which is why colons are allowed.
    pub fn value_precedence(&self) -> i8 {
        match self {
            TokenType::Plus => 8,
            TokenType::Minus => 8,
            TokenType::Equals => 7,
            TokenType::NotEquals => 7,
            TokenType::GreaterThan => 7,
            TokenType::LessThan => 7,
            TokenType::GreaterThanOrEquals => 7,
            TokenType::LessThanOrEquals => 7,
            TokenType::Exclam => 6,
            TokenType::Pipe => 5,
            TokenType::Ampersand => 5,
            TokenType::LeftRightArrow => 4,
            TokenType::RightArrow => 3,
            TokenType::Colon => 2,
            TokenType::Comma => 1,
            _ => 0,
        }
    }

    pub fn type_precedence(&self) -> i8 {
        match self {
            TokenType::RightArrow => 3,
            TokenType::Colon => 2,
            TokenType::Comma => 1,
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

    pub fn is_macro(&self) -> bool {
        match self {
            TokenType::ForAll => true,
            TokenType::Exists => true,
            TokenType::Function => true,
            _ => false,
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

    // The index of this line within the document.
    pub line_index: usize,

    // The index of this token within the line.
    // Can be equal to line.len() if it's the final newline.
    pub char_index: usize,
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

#[derive(Debug)]
pub enum Error {
    Token(TokenError),
    EOF,
}

#[derive(Debug)]
pub struct TokenError {
    pub message: String,

    // The text of the token itself
    pub text: String,

    // The whole line containing the error token
    pub line: String,

    // The index of the line within the document.
    // TODO: this numbers the lines in each "add" call differently.
    pub line_index: usize,

    // The index of this token within the line.
    pub char_index: usize,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Token(e) => {
                write!(f, "{}:\n", e.message)?;
                fmt_line_part(f, &e.text, &e.line, e.char_index)
            }
            Error::EOF => write!(f, "unexpected end of file"),
        }
    }
}

impl Error {
    pub fn new(token: &Token, message: &str) -> Self {
        Error::Token(TokenError {
            message: message.to_string(),
            text: token.text.to_string(),
            line: token.line.to_string(),
            line_index: 0,
            char_index: token.char_index,
        })
    }

    pub fn from_iter<'a>(tokens: &mut TokenIter<'a>, message: &str) -> Self {
        if let Some(token) = tokens.peek() {
            Error::new(token, message)
        } else {
            Error::EOF
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub type TokenIter<'a> = std::iter::Peekable<std::vec::IntoIter<Token<'a>>>;

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

    pub fn skip_newlines<'a>(tokens: &mut TokenIter<'a>) {
        while let Some(token) = tokens.peek() {
            if token.token_type == TokenType::NewLine {
                tokens.next();
            } else {
                break;
            }
        }
    }

    fn identifierish(ch: char) -> bool {
        ch.is_alphanumeric() || ch == '_'
    }

    // scanning always puts a NewLine token at the end of the input.
    pub fn scan(input: &str) -> Result<Vec<Token>> {
        let mut tokens = Vec::new();
        for (line_index, line) in input.lines().enumerate() {
            let mut char_indices = line.char_indices().peekable();
            while let Some((char_index, ch)) = char_indices.next() {
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
                    '!' => match char_indices.next_if_eq(&(char_index + 1, '=')) {
                        Some(_) => TokenType::NotEquals,
                        None => TokenType::Exclam,
                    },
                    '|' => TokenType::Pipe,
                    '&' => TokenType::Ampersand,
                    '=' => TokenType::Equals,
                    '+' => TokenType::Plus,
                    '-' => match char_indices.next_if_eq(&(char_index + 1, '>')) {
                        Some(_) => TokenType::RightArrow,
                        None => TokenType::Minus,
                    },
                    '<' => match char_indices.next_if_eq(&(char_index + 1, '-')) {
                        Some(_) => match char_indices.next_if_eq(&(char_index + 2, '>')) {
                            Some(_) => TokenType::LeftRightArrow,
                            None => TokenType::Invalid,
                        },
                        None => match char_indices.next_if_eq(&(char_index + 1, '=')) {
                            Some(_) => TokenType::LessThanOrEquals,
                            None => TokenType::LessThan,
                        },
                    },
                    '>' => match char_indices.next_if_eq(&(char_index + 1, '=')) {
                        Some(_) => TokenType::GreaterThanOrEquals,
                        None => TokenType::GreaterThan,
                    },
                    '/' => match char_indices.next_if_eq(&(char_index + 1, '/')) {
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
                    t if Token::identifierish(t) => {
                        let end = loop {
                            match char_indices.peek() {
                                Some((_, ch)) if Token::identifierish(*ch) => {
                                    char_indices.next();
                                }
                                Some((end, _)) => break *end,
                                None => break line.len(),
                            }
                        };
                        let identifier = &line[char_index..end];
                        match identifier {
                            "let" => TokenType::Let,
                            "axiom" => TokenType::Axiom,
                            "define" => TokenType::Define,
                            "theorem" => TokenType::Theorem,
                            "type" => TokenType::Type,
                            "forall" => TokenType::ForAll,
                            "exists" => TokenType::Exists,
                            "if" => TokenType::If,
                            "by" => TokenType::By,
                            "function" => TokenType::Function,
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
                let text = &line[char_index..end];
                let token = Token {
                    token_type,
                    text,
                    line,
                    line_index,
                    char_index,
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
                line_index,
                char_index: input.len(),
            });
        }

        Ok(tokens)
    }

    pub fn into_iter(tokens: Vec<Token>) -> TokenIter {
        tokens.into_iter().peekable()
    }

    // Pops off one token, expecting it to be there.
    pub fn expect_token<'a>(tokens: &mut TokenIter<'a>) -> Result<Token<'a>> {
        tokens.next().ok_or(Error::EOF)
    }

    // Pops off one token, expecting it to be of a known type.
    pub fn expect_type<'a>(tokens: &mut TokenIter<'a>, expected: TokenType) -> Result<Token<'a>> {
        let token = match tokens.next() {
            Some(t) => t,
            None => return Err(Error::EOF),
        };
        if token.token_type != expected {
            return Err(Error::new(&token, &format!("expected {:?}", expected)));
        }
        Ok(token)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scanning_ok() {
        assert_eq!(Token::scan("theorem t:A->B").unwrap().len(), 7);
        assert_eq!(Token::scan("theorem _t:A->B").unwrap().len(), 7);
    }

    #[test]
    fn test_scanning_errors() {
        assert!(Token::scan("#$@%(#@)(#").is_err());
    }

    #[test]
    fn test_token_types() {
        let tokens = Token::scan("type Nat: axiom\ndefine 0: Nat = axiom").unwrap();
        assert_eq!(tokens.len(), 12);
        assert_eq!(tokens[3].token_type, TokenType::Axiom);
        assert_eq!(tokens[4].token_type, TokenType::NewLine);
    }
}
