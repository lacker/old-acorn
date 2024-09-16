// A representative run of the scorer, to use for profiling.
// To profile using samply:
//
//   cargo build --bin=profile_scorer --profile=profiling
//   samply record target/profiling/profile_scorer

use acorn::features::Features;
use acorn::model::ScoringModel;
use acorn::proof_step::ProofStep;
use acorn::scorer::Scorer;

fn main() {
    for i in 1..11 {
        let scorer = ScoringModel::load(true).unwrap();
        let step = ProofStep::mock("c0(c3) = c2");
        let features = Features::new(&step);
        let start = std::time::Instant::now();
        for _ in 0..100000 {
            let score = scorer.score(&features).unwrap();
            assert!(score.is_finite());
        }
        let elapsed = start.elapsed();
        println!("batch {} took {:.3} seconds", i, elapsed.as_secs_f64());
    }
}
