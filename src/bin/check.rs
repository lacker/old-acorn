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

    let paths = env.goal_paths();
    for path in paths {
        let goal_context = env.get_goal_context(&path);
        let mut prover = Prover::load_goal(&goal_context);
        let outcome = prover.search_for_contradiction(1000, 1.0);

        match outcome {
            Outcome::Success => {
                // println!("{} proved", goal_context.name);
            }
            Outcome::Exhausted => {
                println!("{} is unprovable", goal_context.name);
            }
            Outcome::Unknown => {
                println!("{} could not be proved", goal_context.name);
            }
            Outcome::Interrupted => {
                panic!("interrupted");
            }
        }
    }
}
