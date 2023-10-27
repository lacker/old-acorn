// A representative run of the prover, to use for profiling.
// Try:
//   cargo flamegraph --bin=profiling

use acorn::project::Project;
use acorn::prover::Prover;

fn main() {
    let module_name = "nat";
    let theorem_name = "add_suc_left";
    let env = Project::force_load("math", &module_name);
    let goal_context = env.get_theorem_context(theorem_name);
    let mut prover = Prover::new(&goal_context, false, None);
    let result = prover.search_for_contradiction(1000000, 30.0);
    println!("result: {:?}", result);
    prover.print_stats();
}
