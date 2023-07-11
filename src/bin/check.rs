// Checks an acorn file to see if it compiles.
// Try:
//   cargo run --bin=check nat.ac

use acorn::environment::Environment;
use acorn::prover::{Outcome, Prover};

const USAGE: &str = "Usage: cargo run --bin=check <filename>";

fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let input_file = args.next().expect(USAGE);

    // Load the environment
    let mut env = Environment::new();
    env.load_file(&input_file).unwrap();
    let named_theorems: Vec<_> = env.iter_theorems().collect();

    // Prove each theorem
    for (name, _) in named_theorems.iter() {
        let mut prover = Prover::new(&env);
        prover.verbose = false;
        match prover.prove_limited(name, 1000, 1.0) {
            Outcome::Success => {
                println!("{} proved", name);
            }
            Outcome::Failure => {
                println!("{} is unprovable", name);
            }
            Outcome::Unknown => {
                println!("{} could not be proved", name);
            }
        }
    }
}
