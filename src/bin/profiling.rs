// A representative run of the prover, to use for profiling.
// Try:
//   cargo flamegraph --bin=profiling

use acorn::project::Project;
use acorn::prover::Prover;

fn main() {
    let module_name = "nat";
    let theorem_name = "add_suc_left";
    let mut project = Project::new("math");
    let namespace = project.load(&module_name).unwrap();
    let env = project.get_env(namespace).unwrap();
    let goal_context = env.get_theorem_context(theorem_name);
    let mut prover = Prover::new(&project, &goal_context, false, None);
    let result = prover.search_for_contradiction(1000000, 30.0);
    println!("result: {:?}", result);
    prover.print_stats();
}
