use acorn::environment::Environment;
use acorn::prover::Prover;

fn main() {
    let input_file = "nat.ac";
    let theorem_name = "add_assoc";
    let mut env = Environment::new();
    env.load_file(&input_file).unwrap();
    let mut prover = Prover::new(&env);
    prover.prove_limited(theorem_name, 10000, 10.0);
}
