// Checks an acorn file to see if it compiles.
// Try:
//   cargo run --bin=check nat.ac

use acorn::acorn_value::AcornValue;
use acorn::environment::{Environment, Proposition};
use acorn::prover::{Outcome, Prover};

const USAGE: &str = "Usage: cargo run --bin=check <filename>";

// Proves one proposition, without doing any recursion.
// It is assumed that all facts we need to prove this theorem are provided in facts.
fn prove_one(env: &Environment, facts: &Vec<AcornValue>, goal_name: &str, goal_value: &AcornValue) {
    let mut prover = Prover::new(&env);
    prover.verbose = false;

    for claim in facts {
        prover.add_proposition(claim.clone());
    }
    prover.add_negated(env.expand_constants(&goal_value));

    let outcome = prover.search_for_contradiction(1000, 1.0);
    match outcome {
        Outcome::Success => {
            println!("{} proved", goal_name);
        }
        Outcome::Failure => {
            println!("{} is unprovable", goal_name);
        }
        Outcome::Unknown => {
            println!("{} could not be proved", goal_name);
        }
    }
}

// Proves a theorem, using the provided list of previously proved claims.
// If the theorem is axiomatic, it is just assumed to be true.
// If there are claims within the body, those are proved first, and used to prove the theorem's
// main claim.
// After the proof, 'facts' is updated to contain the new proposition.
fn prove_rec(env: &Environment, facts: &mut Vec<AcornValue>, goal: &Proposition) {
    let goal_name = if let Some(name) = &goal.display_name {
        name.to_string()
    } else {
        env.value_str(&goal.claim)
    };
    if let Some(block) = &goal.block {
        let facts_len = facts.len();

        // Prove all the claims within the block
        for prop in &block.env.propositions {
            prove_rec(&block.env, facts, prop);
        }

        // Prove the block's main goal
        prove_one(&block.env, facts, &goal_name, &block.claim);

        // Drop the subclaims
        facts.truncate(facts_len);
    } else if goal.proven {
        println!("{} is axiomatic", goal_name);
    } else {
        prove_one(env, facts, &goal_name, &goal.claim);
    }
    facts.push(env.expand_constants(&goal.claim));
}

fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let input_file = args.next().expect(USAGE);

    // Load the environment
    let mut env = Environment::new();
    env.load_file(&input_file).unwrap();

    // Once each theorem gets proved, we add it to the fact list
    let mut facts: Vec<AcornValue> = Vec::new();
    for theorem in &env.propositions {
        prove_rec(&env, &mut facts, theorem);
    }
}
