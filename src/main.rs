use std::path::PathBuf;

use acorn::token::{scan, Token};

fn main() {
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("acorn/prop.ac");
    let input = std::fs::read_to_string(d).unwrap();
    let tokens = scan(&input);
    for token in &tokens {
        if token == &Token::NewLine {
            println!();
        } else {
            print!("{} ", token);
        }
    }
}
