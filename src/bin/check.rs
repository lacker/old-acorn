// Checks an acorn file to see if it compiles.
// Try:
//   cargo run --bin=check nat

use acorn::project::Project;

const USAGE: &str = "Usage: cargo run --bin=check [module name]";

#[tokio::main]
async fn main() {
    let mut project = Project::new("math");
    project.warn_when_slow = true;

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

    let mut all_ok = true;
    project.build(&mut |event| {
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
            all_ok = false;
        }
        if let Some((d, t)) = event.progress {
            if d == t {
                println!("{}/{} OK", d, t);
            }
        }
    });
}
