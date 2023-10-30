// Analyzes an acorn file interactively.
// Try:
//   cargo run --bin=debug nat.ac add_assoc

use std::io::Write;

use acorn::project::Project;
use acorn::prover::{Outcome, Prover};

const USAGE: &str = "Usage: cargo run --bin=debug <module name> <goal name>";

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
    let module_name = args.next().expect(USAGE);
    let theorem_name = args.next().expect(USAGE);

    // Find all the goals in the file
    let mut project = Project::new("math");
    let namespace = project.load(&module_name).unwrap();
    let env = project.get_env(namespace).unwrap();
    let goal_paths = env.goal_paths();
    let goals = goal_paths
        .iter()
        .map(|path| env.get_goal_context(&project, path))
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
    let mut prover = Prover::new(&project, &goals[current], false, None);
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
            if let Some(definition) = env.get_definition(constant_str) {
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

        match line.trim_end() {
            "stats" => {
                prover.print_stats();
            }
            "env" => {
                prover.print_env();
            }

            "next" => {
                if current == goals.len() - 1 {
                    println!("already at the last proposition");
                } else {
                    current = current + 1;
                    prover = Prover::new(&project, &goals[current], false, None);
                    println!("loaded {}", goals[current].name);
                }
            }

            "reset" => {
                prover = Prover::new(&project, &goals[current], false, None);
                println!("loaded {}", goals[current].name);
            }

            "/" => {
                // A / will try to prove the next proposition for a while.
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
                        Outcome::Exhausted => {
                            println!("Failure!");
                            break;
                        }
                        Outcome::Unknown => {
                            if prover.hit_trace {
                                println!("trace found!");
                                break;
                            }
                        }
                        Outcome::Interrupted => {
                            panic!("interrupted");
                        }
                    }
                    if start_time.elapsed().as_secs_f32() > 10.0 {
                        println!("Timeout!");
                        break;
                    }
                }
            }

            "ff" => {
                // "ff" runs to the end of the fact-fact inference stage.
                prover.verbose = true;
                while !prover.done_with_facts() {
                    let outcome = prover.activate_next();
                    match outcome {
                        Outcome::Success => {
                            println!("Success!");
                            break;
                        }
                        Outcome::Exhausted => {
                            println!("Failure!");
                            break;
                        }
                        Outcome::Unknown => (),
                        Outcome::Interrupted => {
                            panic!("interrupted");
                        }
                    }
                }
                prover.verbose = false;
            }

            "" => {
                // Hitting enter does one step of proving.
                prover.verbose = true;
                let outcome = prover.activate_next();
                match outcome {
                    Outcome::Success => {
                        println!("Success!");
                        break;
                    }
                    Outcome::Exhausted => {
                        println!("Failure!");
                        break;
                    }
                    Outcome::Unknown => (),
                    Outcome::Interrupted => {
                        panic!("interrupted");
                    }
                }
                prover.verbose = false;
            }

            _ => {
                println!("bad command: {}", line);
            }
        }
    }
}
