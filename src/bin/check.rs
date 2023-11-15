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
    let mut project = Project::new("math");
    let namespace = project.load(&module_name).unwrap();
    let env = project.get_env(namespace).unwrap();

    let paths = env.goal_paths();
    for path in paths {
        let goal_context = env.get_goal_context(&project, &path);
        let mut prover = Prover::new(&project, &goal_context, false, None);
        let outcome = prover.search_for_contradiction(10000, 2.0);

        match outcome {
            Outcome::Success => {
                // println!("{} proved", goal_context.name);
            }
            Outcome::Inconsistent => {
                println!("Inconsistent: {}", goal_context.name);
                prover.print_proof();
                return;
            }
            _ => {
                println!("{}: {}", outcome, goal_context.name);
            }
        }
    }
}
