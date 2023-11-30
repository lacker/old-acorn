// Checks an acorn file to see if it compiles.
// Try:
//   cargo run --bin=check nat

use acorn::project::Project;

const USAGE: &str = "Usage: cargo run --bin=check [module name]";

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

    let mut all_ok = true;
    project.build(&mut |event| {
        if let Some(m) = event.log_message {
            println!("{}", m);
            all_ok = false;
        }
        if let Some((d, t)) = event.progress {
            if d == t {
                println!("{}/{} OK", d, t);
            }
        }
    });
}
