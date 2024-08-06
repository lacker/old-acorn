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
    Not,
    Or,
    And,
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
    Structure,
    Import,
    True,
    False,
    Else,
    Class,
    Asterisk,
    Percent,
    Slash,
    Numeral,
    Numerals,
    From,
    Solve,
    Problem,
    Satisfy,
    SelfToken,
    Inductive,
}

// The token types that we export via the language server protocol
pub const LSP_TOKEN_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::VARIABLE,
    SemanticTokenType::COMMENT,
    SemanticTokenType::KEYWORD,
    SemanticTokenType::OPERATOR,
    SemanticTokenType::NUMBER,
];

// Infix operators are represented by a "magic method name", where you implement a method
// with that name, and then the infix operator with this token can be used to invoke that method.
// The term "magic method name", along with this general idea, are from Python.
const MAGIC_METHOD_NAMES: &[(&str, TokenType)] = &[
    ("gt", TokenType::GreaterThan),
    ("lt", TokenType::LessThan),
    ("gte", TokenType::GreaterThanOrEquals),
    ("lte", TokenType::LessThanOrEquals),
    ("add", TokenType::Plus),
    ("sub", TokenType::Minus),
    ("mul", TokenType::Asterisk),
    ("mod", TokenType::Percent),
    ("div", TokenType::Slash),
];

impl TokenType {
    pub fn is_unary(&self) -> bool {
        match self {
            TokenType::Not => true,
            _ => false,
        }
    }

    pub fn is_binary(&self) -> bool {
        match self {
            TokenType::Plus => true,
            TokenType::Minus => true,
            TokenType::RightArrow => true,
            TokenType::Or => true,
            TokenType::And => true,
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
            TokenType::Asterisk => true,
            TokenType::Percent => true,
            TokenType::Slash => true,
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
    // Function application implicitly has the same precedence as dot.
    pub fn value_precedence(&self) -> i8 {
        match self {
            TokenType::Dot => 12,
            TokenType::Asterisk => 11,
            TokenType::Slash => 11,
            TokenType::Plus => 10,
            TokenType::Minus => 10,
            TokenType::Percent => 9,
            TokenType::GreaterThan => 8,
            TokenType::LessThan => 8,
            TokenType::GreaterThanOrEquals => 8,
            TokenType::LessThanOrEquals => 8,
            TokenType::Equals => 7,
            TokenType::NotEquals => 7,
            TokenType::Not => 6,
            TokenType::Or => 5,
            TokenType::And => 5,
            TokenType::LeftRightArrow => 4,
            TokenType::RightArrow => 3,
            TokenType::Colon => 2,
            TokenType::Comma => 1,
            _ => 0,
        }
    }

    pub fn type_precedence(&self) -> i8 {
        match self {
            TokenType::Dot => 4,
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

    // Converts a token to its magic method name, if it has on.
    pub fn to_magic_method_name(&self) -> Option<&str> {
        for (name, token_type) in MAGIC_METHOD_NAMES {
            if token_type == self {
                return Some(name);
            }
        }
        None
    }

    // Converting the other way, from a (potential) magic method name to an infix token.
    pub fn from_magic_method_name(name: &str) -> Option<TokenType> {
        for (method_name, token_type) in MAGIC_METHOD_NAMES {
            if method_name == &name {
                return Some(*token_type);
            }
        }
        None
    }

    // A token created without a line.
    // This is used for code generation, when we have an expression and then we wish to create
    // code for it.
    pub fn new_token(self, text: &str) -> Token {
        let len = text.len() as u32;
        Token {
            token_type: self,
            line: Arc::new(text.to_string()),
            line_number: 0,
            start: 0,
            len,
        }
    }

    // Used for code generation.
    pub fn to_str(&self) -> &str {
        match self {
            TokenType::Identifier => "<identifier>",
            TokenType::Invalid => "<invalid>",
            TokenType::LeftParen => "(",
            TokenType::RightParen => ")",
            TokenType::LeftBrace => "{",
            TokenType::RightBrace => "}",
            TokenType::NewLine => "\n",
            TokenType::Comma => ",",
            TokenType::Colon => ":",
            TokenType::Dot => ".",
            TokenType::RightArrow => "->",
            TokenType::Not => "not",
            TokenType::Or => "or",
            TokenType::And => "and",
            TokenType::LeftRightArrow => "<->",
            TokenType::Equals => "=",
            TokenType::NotEquals => "!=",
            TokenType::GreaterThan => ">",
            TokenType::LessThan => "<",
            TokenType::GreaterThanOrEquals => ">=",
            TokenType::LessThanOrEquals => "<=",
            TokenType::Plus => "+",
            TokenType::Minus => "-",
            TokenType::Let => "let",
            TokenType::Axiom => "axiom",
            TokenType::Define => "define",
            TokenType::Theorem => "theorem",
            TokenType::Type => "type",
            TokenType::ForAll => "forall",
            TokenType::Exists => "exists",
            TokenType::If => "if",
            TokenType::By => "by",
            TokenType::Function => "function",
            TokenType::Structure => "structure",
            TokenType::Import => "import",
            TokenType::True => "true",
            TokenType::False => "false",
            TokenType::Else => "else",
            TokenType::Class => "class",
            TokenType::Asterisk => "*",
            TokenType::Percent => "%",
            TokenType::Slash => "/",
            TokenType::Numeral => "<numeral>",
            TokenType::Numerals => "numerals",
            TokenType::From => "from",
            TokenType::Solve => "solve",
            TokenType::Problem => "problem",
            TokenType::Satisfy => "satisfy",
            TokenType::SelfToken => "self",
            TokenType::Inductive => "inductive",
        }
    }

    // Used to create error messages.
    pub fn describe(&self) -> String {
        match self {
            TokenType::Identifier => "identifier".to_string(),
            TokenType::Invalid => "invalid".to_string(),
            TokenType::NewLine => "newline".to_string(),
            TokenType::Numeral => "number".to_string(),
            _ => format!("\"{}\"", self.to_str()),
        }
    }

    pub fn generate(self) -> Token {
        self.new_token(self.to_str())
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Token {
    pub token_type: TokenType,

    // The entire line containing this token.
    pub line: Arc<String>,

    // The index of this line within the document.
    pub line_number: u32,

    // The index where this token starts, within the line.
    pub start: u32,

    // The length of this token.
    pub len: u32,
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
    pub fn empty() -> Self {
        Token {
            token_type: TokenType::NewLine,
            line: Arc::new("".to_string()),
            line_number: 0,
            start: 0,
            len: 0,
        }
    }

    pub fn text(&self) -> &str {
        let start = self.start as usize;
        let end = (self.start + self.len) as usize;
        &self.line[start..end]
    }

    pub fn start_pos(&self) -> Position {
        Position {
            line: self.line_number,
            character: self.start,
        }
    }

    pub fn end_pos(&self) -> Position {
        Position {
            line: self.line_number,
            character: (self.start + self.len),
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

    fn identifierish(ch: char) -> bool {
        ch.is_alphanumeric() || ch == '_'
    }

    pub fn lsp_type(&self) -> Option<SemanticTokenType> {
        match self.token_type {
            TokenType::Identifier => Some(SemanticTokenType::VARIABLE),

            TokenType::RightArrow
            | TokenType::LeftRightArrow
            | TokenType::Equals
            | TokenType::NotEquals
            | TokenType::GreaterThan
            | TokenType::LessThan
            | TokenType::GreaterThanOrEquals
            | TokenType::LessThanOrEquals
            | TokenType::Plus
            | TokenType::Minus
            | TokenType::Asterisk
            | TokenType::Percent
            | TokenType::Slash => Some(SemanticTokenType::OPERATOR),

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
            | TokenType::Structure
            | TokenType::Import
            | TokenType::True
            | TokenType::False
            | TokenType::Else
            | TokenType::Class
            | TokenType::Numerals
            | TokenType::From
            | TokenType::Solve
            | TokenType::Problem
            | TokenType::Satisfy
            | TokenType::Not
            | TokenType::Or
            | TokenType::And
            | TokenType::SelfToken
            | TokenType::Inductive => Some(SemanticTokenType::KEYWORD),

            TokenType::NewLine => {
                // Comments are encoded as newlines because syntactically they act like newlines.
                if self.len > 1 {
                    Some(SemanticTokenType::COMMENT)
                } else {
                    None
                }
            }

            TokenType::Numeral => Some(SemanticTokenType::NUMBER),

            TokenType::Comma
            | TokenType::Invalid
            | TokenType::LeftParen
            | TokenType::RightParen
            | TokenType::LeftBrace
            | TokenType::RightBrace
            | TokenType::Colon
            | TokenType::Dot => None,
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
            let line_number = line_number as u32;
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
                        None => TokenType::Invalid,
                    },
                    '=' => TokenType::Equals,
                    '+' => TokenType::Plus,
                    '*' => TokenType::Asterisk,
                    '%' => TokenType::Percent,
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
                        None => TokenType::Slash,
                    },
                    t if t.is_ascii_digit() => {
                        loop {
                            match char_indices.peek() {
                                Some((_, ch)) if ch.is_ascii_digit() => {
                                    char_indices.next();
                                }
                                _ => break,
                            }
                        }
                        TokenType::Numeral
                    }
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
                            "structure" => TokenType::Structure,
                            "import" => TokenType::Import,
                            "true" => TokenType::True,
                            "false" => TokenType::False,
                            "else" => TokenType::Else,
                            "class" => TokenType::Class,
                            "numerals" => TokenType::Numerals,
                            "from" => TokenType::From,
                            "solve" => TokenType::Solve,
                            "problem" => TokenType::Problem,
                            "satisfy" => TokenType::Satisfy,
                            "and" => TokenType::And,
                            "or" => TokenType::Or,
                            "not" => TokenType::Not,
                            "self" => TokenType::SelfToken,
                            "inductive" => TokenType::Inductive,
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
                    start: char_index as u32,
                    len: (end - char_index) as u32,
                };
                tokens.push(token);
            }

            // Add a newline
            tokens.push(Token {
                token_type: TokenType::NewLine,
                line: rc_line,
                line_number,
                start: line.len() as u32,
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

    pub fn validate_type_name(&self) -> Result<()> {
        for (i, char) in self.text().chars().enumerate() {
            if i == 0 {
                if !char.is_ascii_uppercase() {
                    return Err(Error::new(
                        &self,
                        "type names must start with an uppercase letter",
                    ));
                }
            } else {
                if !char.is_alphanumeric() {
                    return Err(Error::new(&self, "type names must be alphanumeric"));
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct Error {
    pub message: String,
    pub token: Token,

    // external is true when the root error is in a different module.
    pub external: bool,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:\n", self.message)?;
        fmt_line_part(
            f,
            &self.token.text(),
            &self.token.line,
            self.token.start as usize,
        )
    }
}

impl Error {
    pub fn new(token: &Token, message: &str) -> Self {
        Error {
            message: message.to_string(),
            token: token.clone(),
            external: false,
        }
    }

    pub fn external(token: &Token, message: &str) -> Self {
        Error {
            message: message.to_string(),
            token: token.clone(),
            external: true,
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

    // Pops off one token, expecting it to be there.
    pub fn expect_token(&mut self) -> Result<Token> {
        self.next().ok_or(self.error("unexpected end of file"))
    }

    // Pops off one token, expecting it to be of a known type.
    pub fn expect_type(&mut self, expected: TokenType) -> Result<Token> {
        let token = match self.next() {
            Some(t) => t,
            None => return Err(self.error("unexpected end of file")),
        };
        if token.token_type != expected {
            return Err(Error::new(&token, &format!("expected {:?}", expected)));
        }
        Ok(token)
    }

    // Pops off one token, expecting it to be a variable name.
    pub fn expect_variable_name(&mut self, numeral_ok: bool) -> Result<Token> {
        let name_token = self.expect_token()?;
        match name_token.token_type {
            TokenType::SelfToken => {}
            TokenType::Identifier => match name_token.text().chars().next() {
                Some(c) => {
                    if !c.is_ascii_lowercase() {
                        return Err(Error::new(&name_token, "invalid variable name"));
                    }
                }
                None => return Err(Error::new(&name_token, "empty token (probably a bug)")),
            },
            TokenType::Numeral => {
                if !numeral_ok {
                    return Err(Error::new(&name_token, "did not expect a numeral here"));
                }
            }
            _ => return Err(Error::new(&name_token, "expected a variable name")),
        }
        Ok(name_token)
    }

    // Pops off one token, expecting it to be a type name.
    pub fn expect_type_name(&mut self) -> Result<Token> {
        let name_token = self.expect_type(TokenType::Identifier)?;
        name_token.validate_type_name()?;
        Ok(name_token)
    }

    pub fn skip_newlines(&mut self) {
        while let Some(token) = self.peek() {
            if token.token_type == TokenType::NewLine {
                self.next();
            } else {
                break;
            }
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
