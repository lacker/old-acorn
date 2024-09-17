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
    let m = 10;
    let n = 100000;
    let mut total_seconds = 0.0;
    for i in 1..(m + 1) {
        let scorer = ScoringModel::load(true).unwrap();
        let step = ProofStep::mock("c0(c3) = c2");
        let features = Features::new(&step);
        let start = std::time::Instant::now();
        for _ in 0..n {
            let score = scorer.score(&features).unwrap();
            assert!(score.is_finite());
        }
        let elapsed = start.elapsed().as_secs_f32();
        total_seconds += elapsed;
        println!("batch {} took {:.3} seconds", i, elapsed);
    }
    let nps = (n * m) as f32 / total_seconds;
    println!("{:.1} scores per second", nps);
}
