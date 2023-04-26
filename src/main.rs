use std::io::Write;

use acorn::environment::Environment;
use acorn::prover::{Outcome, Prover};

const USAGE: &str = "Usage: acorn <filename> <theorem name>";

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

        if let Some(atom_str) = trim_command("atom", &line) {
            prover.print_atom_info(atom_str);
            continue;
        }

        if let Some(term_str) = trim_command("term", &line) {
            prover.print_term_info(term_str);
            continue;
        }

        if let Some(_) = trim_command("active", &line) {
            prover.print_active();
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
