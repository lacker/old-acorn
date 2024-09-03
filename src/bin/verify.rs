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

    let mut failures = 0;
    let mut logger = Builder::new(|event| {
        if let Some(m) = event.log_message {
            if let Some((target, diagnostic)) = event.diagnostic {
                if let Some(diagnostic) = diagnostic {
                    if !event.is_slow_warning {
                        failures += 1;
                    }
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
        if let Some((d, t)) = event.progress {
            if d == t {
                if failures == 0 {
                    println!("{}/{} OK", d, t);
                } else {
                    println!("FAILED");
                }
            }
        }
    });
    logger.warn_when_slow = true;
    project.build(&mut logger);
}
