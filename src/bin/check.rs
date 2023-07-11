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

    // Prove each theorem
    for (i, (maybe_name, axiomatic, value)) in env.theorems.iter().enumerate() {
        let name = if let Some(name) = maybe_name {
            name.to_string()
        } else {
            value.to_string()
        };

        if *axiomatic {
            // Don't need to prove these
            println!("{} is axiomatic", name);
            continue;
        }

        let mut prover = Prover::new(&env);
        prover.verbose = false;

        if i > 0 {
            for (_, _, value) in env.theorems.iter().take(i - 1) {
                prover.add_proposition(value.clone());
            }
        }
        prover.add_negated(value.clone());

        let outcome = prover.search_for_contradiction(1000, 1.0);
        match outcome {
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
