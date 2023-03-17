use std::path::PathBuf;

use acorn::token::{Token, TokenType};

fn main() {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("acorn/prop.ac");
    let input = std::fs::read_to_string(d).unwrap();
    let tokens = Token::scan(&input).unwrap();
    for token in &tokens {
        if token.token_type == TokenType::NewLine {
            println!();
        } else {
            print!("{} ", token);
        }
    }
}
