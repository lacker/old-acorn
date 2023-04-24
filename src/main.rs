use std::path::PathBuf;

use acorn::environment::Environment;
use acorn::prover::{Outcome, Prover};

const USAGE: &str = "Usage: acorn <input file> <theorem name>";

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

    // Read input file
    let input_path = PathBuf::from(input_file);
    let input = std::fs::read_to_string(&input_path).unwrap();

    // Initialize a prover
    let mut env = Environment::new();
    env.add(&input);
    let mut prover = Prover::new(&env);
    prover.assume_false(&theorem_name);

    loop {
        // Read a line from the input
        let mut line = String::new();
        std::io::stdin().read_line(&mut line).unwrap();

        if let Some(trace) = trim_command("trace", &line) {
            println!("setting trace: {}", trace);
            prover.set_trace(trace);
            continue;
        }

        if let Some(query) = trim_command("?", &line) {
            prover.print_info(query);
            continue;
        }

        if line.trim_end() == "/" {
            prover.hit_trace = false;
            println!("looking for trace...");
            loop {
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
                    Outcome::Unknown => {
                        if prover.hit_trace {
                            println!("trace found!");
                            break;
                        }
                    }
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
