// A representative run of the prover, to use for profiling.
// Try:
//   cargo flamegraph --bin=profiling

use acorn::environment::Environment;
use acorn::prover::Prover;

fn main() {
    let input_file = "nat.ac";
    let theorem_name = "add_suc_left";
    let mut env = Environment::new();
    env.load_file(&input_file).unwrap();
    let goal_context = env.get_theorem_context(theorem_name);
    let mut prover = Prover::load_goal(&goal_context, true);
    let result = prover.search_for_contradiction(1000000, 30.0);
    println!("result: {:?}", result);
    prover.print_stats();
}
