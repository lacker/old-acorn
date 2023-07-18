// Checks an acorn file to see if it compiles.
// Try:
//   cargo run --bin=check nat.ac

use acorn::acorn_value::AcornValue;
use acorn::environment::{Environment, Theorem};
use acorn::prover::{Outcome, Prover};

const USAGE: &str = "Usage: cargo run --bin=check <filename>";

// Proves a theorem, without doing any recursion.
// It is assumed that all claims we need to prove this theorem are provided in claims.
fn prove_one(env: &Environment, claims: &Vec<AcornValue>, theorem: &Theorem) {
    let theorem_string = if let Some(name) = &theorem.name {
        name.to_string()
    } else {
        env.value_str(&theorem.claim)
    };

    if theorem.axiomatic {
        // Don't need to prove these
        println!("{} is axiomatic", theorem_string);
        return;
    }

    let mut prover = Prover::new(&env);
    prover.verbose = false;

    for claim in claims {
        prover.add_proposition(claim.clone());
    }
    prover.add_negated(theorem.claim.clone());

    let outcome = prover.search_for_contradiction(1000, 1.0);
    match outcome {
        Outcome::Success => {
            println!("{} proved", theorem_string);
        }
        Outcome::Failure => {
            println!("{} is unprovable", theorem_string);
        }
        Outcome::Unknown => {
            println!("{} could not be proved", theorem_string);
        }
    }
}

// Proves a theorem, using the provided list of previously proved claims.
// If the theorem is axiomatic, it is just assumed to be true.
// If there are claims within the body, those are proved first, and used to prove the theorem's
// main claim.
// After the proof, 'claims' is updated to contain the new claim.
fn prove_rec(env: &Environment, claims: &mut Vec<AcornValue>, theorem: &Theorem) {
    if let Some(subenv) = &theorem.env {
        let claims_len = claims.len();

        // Prove all the claims within the body
        for theorem in &subenv.theorems {
            prove_rec(subenv, claims, theorem);
        }

        // Prove the main claim
        prove_one(subenv, claims, theorem);

        // Drop the subclaims
        claims.truncate(claims_len);
    } else {
        prove_one(env, claims, theorem);
    }
    claims.push(theorem.claim.clone());
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
    for theorem in &env.theorems {
        prove_rec(&env, &mut claims, theorem);
    }
}
