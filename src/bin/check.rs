// Checks an acorn file to see if it compiles.
// Try:
//   cargo run --bin=check nat.ac

use acorn::acorn_value::AcornValue;
use acorn::environment::{Environment, Theorem};
use acorn::prover::{Outcome, Prover};

const USAGE: &str = "Usage: cargo run --bin=check <filename>";

// Proves a theorem, using the provided list of previously proved claims.
// If the theorem is axiomatic, it is assumed to be true.
// Any claims within the theorem body are also proved.
// After the theorem is proved, its claim is added to the list of claims.
fn prove(env: &Environment, claims: &mut Vec<AcornValue>, theorem: &Theorem) {
    let name = if let Some(name) = &theorem.name {
        name.to_string()
    } else {
        theorem.claim.to_string()
    };

    if theorem.axiomatic {
        // Don't need to prove these
        println!("{} is axiomatic", name);
    } else {
        let mut prover = Prover::new(&env);
        prover.verbose = false;

        for claim in claims.iter() {
            prover.add_proposition(claim.clone());
        }
        prover.add_negated(theorem.claim.clone());

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

    claims.push(theorem.claim.clone());
}

// Proves all theorems in the environment.
// Returns claims to its initial state after running.
fn prove_all(env: &Environment, claims: &mut Vec<AcornValue>) {
    let initial_len = claims.len();
    for theorem in &env.theorems {
        prove(env, claims, theorem);
    }
    claims.truncate(initial_len);
}

fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let input_file = args.next().expect(USAGE);

    // Load the environment
    let mut env = Environment::new();
    env.load_file(&input_file).unwrap();

    // Once each theorem gets proved, we add its claim
    let mut claims: Vec<AcornValue> = Vec::new();
    prove_all(&env, &mut claims);
}
