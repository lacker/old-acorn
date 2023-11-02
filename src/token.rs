use std::fmt;
use std::iter::Peekable;
use std::sync::Arc;
use std::vec::IntoIter;

use tower_lsp::lsp_types::{Position, Range, SemanticTokenType};

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
    Dot,
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
    Struct,
    Import,
    True,
    False,
}

pub const MAX_PRECEDENCE: i8 = 100;

// The token types that we export via the language server protocol
pub const LSP_TOKEN_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::VARIABLE,
    SemanticTokenType::COMMENT,
    SemanticTokenType::KEYWORD,
    SemanticTokenType::OPERATOR,
];

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
            TokenType::Dot => true,
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
            TokenType::Dot => 9,
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
            TokenType::Dot => false,
            TokenType::Comma => false,
            TokenType::Colon => false,
            _ => true,
        }
    }

    // Whether we put a space to the right of this operator in the canonical style.
    pub fn right_space(&self) -> bool {
        match self {
            TokenType::Dot => false,
            _ => true,
        }
    }

    pub fn is_binder(&self) -> bool {
        match self {
            TokenType::ForAll => true,
            TokenType::Exists => true,
            TokenType::Function => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Token {
    pub token_type: TokenType,

    // The entire line containing this token.
    pub line: Arc<String>,

    // The index of this line within the document.
    pub line_number: usize,

    // The index where this token starts, within the line.
    pub start: usize,

    // The length of this token.
    pub len: usize,
}

fn fmt_line_part(f: &mut fmt::Formatter, text: &str, line: &str, index: usize) -> fmt::Result {
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

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.text())
    }
}

impl Token {
    // A token to represent an empty file.
    fn empty() -> Self {
        Token {
            token_type: TokenType::NewLine,
            line: Arc::new("".to_string()),
            line_number: 0,
            start: 0,
            len: 0,
        }
    }

    pub fn text(&self) -> &str {
        &self.line[self.start..self.start + self.len]
    }

    pub fn start_pos(&self) -> Position {
        Position {
            line: self.line_number as u32,
            character: self.start as u32,
        }
    }

    pub fn end_pos(&self) -> Position {
        Position {
            line: self.line_number as u32,
            character: (self.start + self.len) as u32,
        }
    }

    pub fn range(&self) -> Range {
        Range {
            start: self.start_pos(),
            end: self.end_pos(),
        }
    }

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

    pub fn skip_newlines<'a>(tokens: &mut TokenIter) {
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

    pub fn lsp_type(&self) -> Option<SemanticTokenType> {
        match self.token_type {
            TokenType::Identifier => Some(SemanticTokenType::VARIABLE),

            TokenType::RightArrow
            | TokenType::Exclam
            | TokenType::Pipe
            | TokenType::Ampersand
            | TokenType::LeftRightArrow
            | TokenType::Equals
            | TokenType::NotEquals
            | TokenType::GreaterThan
            | TokenType::LessThan
            | TokenType::GreaterThanOrEquals
            | TokenType::LessThanOrEquals
            | TokenType::Plus
            | TokenType::Minus => Some(SemanticTokenType::OPERATOR),

            TokenType::Let
            | TokenType::Axiom
            | TokenType::Define
            | TokenType::Theorem
            | TokenType::Type
            | TokenType::ForAll
            | TokenType::Exists
            | TokenType::If
            | TokenType::By
            | TokenType::Function
            | TokenType::Struct
            | TokenType::Import
            | TokenType::True
            | TokenType::False => Some(SemanticTokenType::KEYWORD),

            TokenType::NewLine => {
                // Comments are encoded as newlines because syntactically they act like newlines.
                if self.len > 1 {
                    Some(SemanticTokenType::COMMENT)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    // Convert the lsp type to a u32 for the language server protocol.
    pub fn lsp_type_u32(&self) -> Option<u32> {
        let lsp_type = self.lsp_type()?;
        LSP_TOKEN_TYPES
            .iter()
            .position(|t| t == &lsp_type)
            .map(|i| i as u32)
    }

    // If there is an error in scanning, there will be one or more InvalidToken in the result.
    // scanning always puts a NewLine token at the end of the input.
    pub fn scan(input: &str) -> Vec<Token> {
        let mut tokens = Vec::new();
        for (line_number, line) in input.lines().enumerate() {
            let rc_line = Arc::new(line.to_string());
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
                    '.' => TokenType::Dot,
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
                            "struct" => TokenType::Struct,
                            "import" => TokenType::Import,
                            "true" => TokenType::True,
                            "false" => TokenType::False,
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
                let token = Token {
                    token_type,
                    line: rc_line.clone(),
                    line_number,
                    start: char_index,
                    len: end - char_index,
                };
                tokens.push(token);
            }

            // Add a newline
            tokens.push(Token {
                token_type: TokenType::NewLine,
                line: rc_line,
                line_number,
                start: line.len(),
                len: 0,
            });
        }

        tokens
    }

    pub fn has_invalid_token(tokens: &[Token]) -> bool {
        for token in tokens {
            if token.token_type == TokenType::Invalid {
                return true;
            }
        }
        false
    }

    // Pops off one token, expecting it to be there.
    pub fn expect_token<'a>(tokens: &mut TokenIter) -> Result<Token> {
        tokens.next().ok_or(tokens.error("unexpected end of file"))
    }

    // Pops off one token, expecting it to be of a known type.
    pub fn expect_type<'a>(tokens: &mut TokenIter, expected: TokenType) -> Result<Token> {
        let token = match tokens.next() {
            Some(t) => t,
            None => return Err(tokens.error("unexpected end of file")),
        };
        if token.token_type != expected {
            return Err(Error::new(&token, &format!("expected {:?}", expected)));
        }
        Ok(token)
    }
}

#[derive(Debug)]
pub struct Error {
    pub message: String,
    pub token: Token,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:\n", self.message)?;
        fmt_line_part(f, &self.token.text(), &self.token.line, self.token.start)
    }
}

impl Error {
    pub fn new(token: &Token, message: &str) -> Self {
        Error {
            message: message.to_string(),
            token: token.clone(),
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub struct TokenIter {
    inner: Peekable<IntoIter<Token>>,

    last: Token,
}

impl TokenIter {
    pub fn new(tokens: Vec<Token>) -> TokenIter {
        let last = tokens.last().cloned().unwrap_or_else(Token::empty);
        TokenIter {
            inner: tokens.into_iter().peekable(),
            last,
        }
    }

    pub fn peek(&mut self) -> Option<&Token> {
        self.inner.peek()
    }

    pub fn next(&mut self) -> Option<Token> {
        self.inner.next()
    }

    pub fn error(&mut self, message: &str) -> Error {
        match self.peek() {
            Some(token) => Error::new(token, message),
            None => Error::new(&self.last, message),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scanning_ok() {
        assert_eq!(Token::scan("theorem t:A->B").len(), 7);
        assert_eq!(Token::scan("theorem _t:A->B").len(), 7);
    }

    #[test]
    fn test_scanning_errors() {
        let tokens = Token::scan("#$@%(#@)(#");
        assert!(Token::has_invalid_token(&tokens));
    }

    #[test]
    fn test_token_types() {
        let tokens = Token::scan("type Nat: axiom\nlet 0: Nat = axiom");
        assert_eq!(tokens.len(), 12);
        assert_eq!(tokens[3].token_type, TokenType::Axiom);
        assert_eq!(tokens[4].token_type, TokenType::NewLine);
    }
}
