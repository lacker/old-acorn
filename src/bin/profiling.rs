// A representative run of the prover, to use for profiling.

use acorn::environment::Environment;
use acorn::prover::Prover;

fn main() {
    let input_file = "nat.ac";
    let theorem_name = "add_suc_left";
    let mut env = Environment::new();
    env.load_file(&input_file).unwrap();
    let mut prover = Prover::new(&env);
    prover.verbose = false;
    let result = prover.prove_limited(theorem_name, 1000000, 30.0);
    println!("result: {:?}", result);
    prover.print_stats();
}
