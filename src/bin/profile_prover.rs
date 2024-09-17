// A representative run of the prover, to use for profiling.
// To profile using samply:
//
//   cargo build --bin=profile_prover --profile=profiling
//   samply record target/profiling/profile_prover

use acorn::builder::Builder;
use acorn::project::Project;

fn main() {
    for _ in 0..10 {
        let mut project = Project::new("math");
        assert!(project.add_target("nat"));
        assert!(project.add_target("nat_gcd"));
        assert!(project.add_target("int"));
        let mut logger = Builder::new(|event| {
            if let Some(m) = event.log_message {
                println!("{}", m);
            }
            if let Some((d, t)) = event.progress {
                if d == t {
                    println!("{}/{} done", d, t);
                }
            }
        });
        project.build(&mut logger);
    }
}
