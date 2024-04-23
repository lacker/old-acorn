// Searches for a proof for a particular goal in an acorn file.
//
// This is the CLI equivalent of what the IDE runs when you click on a proposition.
//
// The user passes the line in externally-visible line number, which starts at 1.
// Don't forget that the release build is much faster than debug.

const USAGE: &str = "cargo run --release --bin=search <module name> <line number>";

use acorn::project::Project;
use acorn::prover::{Outcome, Prover};

#[tokio::main]
async fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let module_name = args.next().expect(USAGE);
    let external_line_number = args.next().expect(USAGE).parse::<u32>().expect(USAGE);
    let internal_line_number = external_line_number - 1;

    let mut project = Project::new("math");
    let module_id = project.load_module(&module_name).unwrap();
    let env = project.get_env(module_id).unwrap();
    let path = match env.get_path_for_line(internal_line_number) {
        Ok(path) => path,
        Err(s) => {
            eprintln!(
                "no proposition for line {} in {}: {}",
                external_line_number, module_name, s
            );
            return;
        }
    };

    let goal_context = env.get_goal_context(&project, &path).unwrap();
    println!("proving {} ...", goal_context.name);
    let mut prover = Prover::new(&project, &goal_context, false, None);
    let outcome = prover.medium_search();

    match outcome {
        Outcome::Success => {
            println!("Success!");
            prover.print_proof();
            let proof = prover.get_proof().unwrap();
            match proof.to_code(&env.bindings) {
                Ok(code) => {
                    println!("\ngenerated code:\n");
                    for line in &code {
                        println!("{}", line);
                    }
                }
                Err(e) => {
                    eprintln!("\nerror generating code: {}", e);
                }
            }
        }
        Outcome::Inconsistent => {
            println!("Found inconsistency!");
            prover.print_proof();
        }
        Outcome::Exhausted => {
            println!("All possibilities have been exhausted.");
        }
        Outcome::Unknown => {
            println!("Timeout.");
        }
        Outcome::Interrupted => {
            println!("Interrupted.");
        }
        Outcome::Error => {
            println!(
                "Error: {}",
                prover.error.unwrap_or("unknown error".to_string())
            );
        }
    }
}
