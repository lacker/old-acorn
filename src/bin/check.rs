// Checks an acorn file to see if it compiles.
// Try:
//   cargo run --bin=check nat

use acorn::project::Project;

const USAGE: &str = "Usage: cargo run --bin=check <module name>";

#[tokio::main]
async fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let module_name = args.next().expect(USAGE);

    let mut project = Project::new("math");
    project.add_target(&module_name);

    let mut all_ok = true;
    project
        .build(&mut |event| {
            if let Some(m) = event.log_message {
                println!("{}", m);
                all_ok = false;
            }
            if let Some((d, t)) = event.progress {
                if d == t {
                    println!("{}/{} OK", d, t);
                }
            }
        })
        .await;
}
