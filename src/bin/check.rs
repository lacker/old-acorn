// Checks an acorn file to see if it compiles.
// Try:
//   cargo run --bin=check nat

use acorn::project::Project;
use acorn::prover::{Outcome, Prover};

const USAGE: &str = "Usage: cargo run --bin=check <module name>";

fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let module_name = args.next().expect(USAGE);

    // Load the environment
    let env = Project::force_load("math", &module_name);

    let paths = env.goal_paths();
    for path in paths {
        let goal_context = env.get_goal_context(&path);
        let mut prover = Prover::old_new(&goal_context, false, None);
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
