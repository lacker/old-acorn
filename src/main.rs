use std::path::PathBuf;

use acorn::{environment::Environment, prover::Prover};

const USAGE: &str = "Usage: acorn <input file> <theorem name>";

fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let input_file = args.next().expect(USAGE);
    let theorem_name = args.next().expect(USAGE);

    // Read input file
    let input_path = PathBuf::from(input_file);
    let input = std::fs::read_to_string(&input_path).unwrap();

    // Initialize a prover
    let mut env = Environment::new();
    env.add(&input);
    let mut prover = Prover::new(&env);
    prover.assume_false(&theorem_name);
}
