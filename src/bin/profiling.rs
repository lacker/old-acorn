// A representative run of the prover, to use for profiling.
// Try:
//   cargo flamegraph --bin=profiling

use acorn::project::Project;
use acorn::prover::Prover;

fn main() {
    let mut project = Project::new("math");
    let namespace = project.load("nat").unwrap();
    let env = project.get_env(namespace).unwrap();
    let paths = env.goal_paths();
    for path in paths {
        let goal_context = env.get_goal_context(&project, &path);
        let mut prover = Prover::new(&project, &goal_context, false, None);
        let result = prover.search_for_contradiction(1000000, 30.0);
        println!("{}: {}", result, goal_context.name);
    }
}
