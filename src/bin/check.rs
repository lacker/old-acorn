// Checks an acorn file to see if it compiles.
// Try:
//   cargo run --bin=check nat.ac

use acorn::environment::Environment;
use acorn::prover::Prover;

const USAGE: &str = "Usage: cargo run --bin=check <filename>";

fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let input_file = args.next().expect(USAGE);

    // Initialize a prover
    let mut env = Environment::new();
    env.load_file(&input_file).unwrap();
    let mut prover = Prover::new(&env);

    todo!("prove something");
}
