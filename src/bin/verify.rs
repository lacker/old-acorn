// Verifies an acorn file, or the whole project.
//
// This is the CLI equivalent of what the IDE runs when you save.
//
// Try:
//   cargo build --release --bin=verify; time ~/acorn/target/release/verify

use acorn::builder::Builder;
use acorn::project::Project;
use clap::Parser;

#[derive(Parser)]
struct Args {
    // Just verify a single module.
    #[clap(long)]
    module: Option<String>,

    // Create a dataset from the prover logs.
    #[clap(long)]
    dataset: bool,
}

#[tokio::main]
async fn main() {
    let mut project = Project::new("math");

    let args = Args::parse();
    if let Some(module_name) = args.module {
        project.add_target(&module_name);
    } else {
        project.add_all_targets();
    }

    // Set up the builder
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
    if args.dataset {
        builder.create_dataset();
    }

    // Build
    project.build(&mut builder);
    builder.print_stats();
    if let Some(dataset) = builder.dataset {
        dataset.save();
    }
}
