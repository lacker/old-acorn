// Verifies an acorn file, or the whole project.
//
// This is the CLI equivalent of what the IDE runs when you save.
//
// Try:
//   cargo build --release --bin=verify; time ~/acorn/target/release/verify

use acorn::build::Builder;
use acorn::project::Project;

const USAGE: &str = "Usage: cargo run --bin=verify [module name]";

#[tokio::main]
async fn main() {
    let mut project = Project::new("math");

    // Parse command line arguments
    let args = std::env::args();
    match args.len() {
        1 => {
            project.add_all_targets();
        }
        2 => {
            let module_name = args.skip(1).next().unwrap();
            project.add_target(&module_name);
        }
        _ => {
            eprintln!("{}", USAGE);
            return;
        }
    }

    let mut builder = Builder::new(|event| {
        if let Some(m) = event.log_message {
            if let Some((target, diagnostic)) = event.diagnostic {
                if let Some(diagnostic) = diagnostic {
                    println!(
                        "{}, line {}: {}",
                        target,
                        diagnostic.range.start.line + 1,
                        m
                    );
                } else {
                    println!("{}: {}", target, m);
                }
            } else {
                println!("{}", m);
            }
        }
    });
    builder.log_when_slow = true;
    project.build(&mut builder);
    builder.print_stats();
}
