// Checks an acorn file to see if it compiles.
// Try:
//   cargo run --bin=check nat

use acorn::project::Project;

const USAGE: &str = "Usage: cargo run --bin=check <module name>";

fn main() {
    // Parse command line arguments
    let mut args = std::env::args().skip(1);
    let module_name = args.next().expect(USAGE);

    let mut project = Project::new("math");
    project.load(&module_name, true).unwrap();

    let success = project.build(&mut |event| {
        if let Some(m) = event.log_message {
            println!("{}", m);
        }
    });
    if success {
        println!("OK");
    }
}
