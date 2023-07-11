// Analyzes an acorn file interactively.
// Try:
//   cargo run --bin=debug nat.ac add_assoc

use std::io::Write;

use acorn::environment::Environment;
use acorn::prover::{Outcome, Prover};

const USAGE: &str = "Usage: cargo run --bin=debug <filename> <theorem name>";

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

    // Initialize a prover
    let mut env = Environment::new();
    env.load_file(&input_file).unwrap();
    let mut prover = Prover::new(&env);
    prover.assume_false(&theorem_name);

    loop {
        // Read a line from the input
        let mut line = String::new();
        print!("$ ");
        std::io::stdout().flush().unwrap();
        std::io::stdin().read_line(&mut line).unwrap();

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

        if let Some(substr) = trim_command("active", &line) {
            if line == "" {
                prover.print_active(None);
            } else {
                prover.print_active(Some(substr));
            }
            continue;
        }

        if let Some(_) = trim_command("passive", &line) {
            prover.print_passive();
            continue;
        }

        if let Some(_) = trim_command("stats", &line) {
            prover.print_stats();
            continue;
        }

        if line.trim_end() == "/" {
            prover.hit_trace = false;
            let start_time = std::time::Instant::now();
            loop {
                let outcome = prover.activate_next();
                match outcome {
                    Outcome::Success => {
                        println!("Success!");
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
    }
}
