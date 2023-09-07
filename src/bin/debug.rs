// Analyzes an acorn file interactively.
// Try:
//   cargo run --bin=debug nat.ac add_assoc

use std::io::Write;

use acorn::environment::Environment;
use acorn::prover::{Outcome, Prover};

const USAGE: &str = "Usage: cargo run --bin=debug <filename> <goal name>";

fn trim_command<'a>(command: &str, line: &'a str) -> Option<&'a str> {
    if line.starts_with(command) {
        Some(line.trim_start_matches(command).trim())
    } else {
        None
    }
}

fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let input_file = args.next().expect(USAGE);
    let theorem_name = args.next().expect(USAGE);

    // Find all the goals in the file
    let mut env = Environment::new();
    env.load_file(&input_file).unwrap();
    let goal_paths = env.goal_paths();
    let goals = goal_paths
        .iter()
        .map(|path| env.get_goal_context(path))
        .collect::<Vec<_>>();

    // Find the goal whose name matches theorem_name
    let current: Option<usize> = goals.iter().position(|goal| goal.name == theorem_name);
    let mut current = match current {
        Some(current) => current,
        None => {
            println!("theorem {} not found in:", theorem_name);
            for goal in &goals {
                println!("  {}", goal.name);
            }
            return;
        }
    };
    let mut prover = Prover::load_goal(&goals[current], false);
    println!("loaded {}", goals[current].name);

    loop {
        // Read a line from the input
        let mut line = String::new();
        print!("$ ");
        std::io::stdout().flush().unwrap();
        std::io::stdin().read_line(&mut line).unwrap();

        // Most commands alter the debug output or print out some one-off debug info.
        if let Some(trace) = trim_command("trace", &line) {
            println!("setting trace: {}", trace);
            prover.set_trace(trace);
            continue;
        }

        if let Some(_) = trim_command("untrace", &line) {
            println!("unsetting trace");
            prover.unset_trace();
            continue;
        }

        if let Some(atom_str) = trim_command("atom", &line) {
            prover.print_atom_info(atom_str);
            continue;
        }

        if let Some(term_str) = trim_command("term", &line) {
            prover.print_term_info(term_str);
            continue;
        }

        if let Some(constant_str) = trim_command("define", &line) {
            let env = goals[current].env;
            if let Some(definition) = env.get_defined_value(constant_str) {
                println!("{} = {}", constant_str, env.value_str(definition));
            } else {
                println!("{} is not a defined constant", constant_str);
            }
            continue;
        }

        if let Some(substr) = trim_command("active", &line) {
            if line == "" {
                prover.print_active(None);
            } else {
                prover.print_active(Some(substr));
            }
            continue;
        }

        if let Some(substr) = trim_command("passive", &line) {
            if line == "" {
                prover.print_passive(None);
            } else {
                prover.print_passive(Some(substr));
            }
            continue;
        }

        if let Some(_) = trim_command("stats", &line) {
            prover.print_stats();
            continue;
        }

        if let Some(_) = trim_command("env", &line) {
            prover.print_env();
            continue;
        }

        // The "next" command moves to the next proposition.
        if let Some(_) = trim_command("next", &line) {
            if current == goals.len() - 1 {
                println!("already at the last proposition");
                continue;
            }
            current = current + 1;
            prover = Prover::load_goal(&goals[current], false);
            println!("loaded {}", goals[current].name);
            continue;
        }

        if let Some(_) = trim_command("reset", &line) {
            prover = Prover::load_goal(&goals[current], false);
            println!("loaded {}", goals[current].name);
            continue;
        }

        // A / will try to prove the next proposition for a while.
        if line.trim_end() == "/" {
            prover.hit_trace = false;
            let start_time = std::time::Instant::now();
            loop {
                let outcome = prover.activate_next();
                match outcome {
                    Outcome::Success => {
                        println!("Success! ({}s)", start_time.elapsed().as_secs_f32());
                        prover.print_proof();
                        break;
                    }
                    Outcome::Failure => {
                        println!("Failure!");
                        break;
                    }
                    Outcome::Unknown => {
                        if prover.hit_trace {
                            println!("trace found!");
                            break;
                        }
                    }
                }
                if start_time.elapsed().as_secs_f32() > 10.0 {
                    println!("Timeout!");
                    break;
                }
            }
            continue;
        }

        if line.trim_end() != "" {
            println!("bad command: {}", line);
            continue;
        }

        // Hitting enter does one step of proving.
        prover.verbose = true;
        let outcome = prover.activate_next();
        match outcome {
            Outcome::Success => {
                println!("Success!");
                break;
            }
            Outcome::Failure => {
                println!("Failure!");
                break;
            }
            Outcome::Unknown => (),
        }
        prover.verbose = false;
    }
}
