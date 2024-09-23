// A representative run of the scorer, to use for profiling.
// To profile using samply:
//
//   cargo build --bin=profile_scorer --profile=profiling
//   samply record target/profiling/profile_scorer

use acorn::features::Features;
use acorn::ort_model::OrtModel;
use acorn::proof_step::ProofStep;
use acorn::scorer::Scorer;

fn main() {
    let m = 10;
    let n = 10000;
    let mut total_seconds = 0.0;
    for i in 1..(m + 1) {
        let scorer = OrtModel::load(true).unwrap();

        let step1 = ProofStep::mock("c0(c3) = c2");
        let step2 = ProofStep::mock("c4(c1, c1) = c4(c2, c2)");
        let step3 = ProofStep::mock("c4(c1, c1) = c4(c2)");
        let step4 = ProofStep::mock("c4(c1, c1) = c4(c2, c2)");
        let step5 = ProofStep::mock("c4(c1, c1) = c5(c2)");
        let step6 = ProofStep::mock("c4(c1, c1) = c5(c2, c2)");
        let step7 = ProofStep::mock("c4(c1, c1) = c5(c2)");
        let step8 = ProofStep::mock("c4(c1, c1) = c5(c2, c2)");
        let step9 = ProofStep::mock("c4(c1, c1) = c5(c2)");
        let step10 = ProofStep::mock("c4(c1, c1) = c5(c2, c2)");
        let steps = vec![
            step1, step2, step3, step4, step5, step6, step7, step8, step9, step10,
        ];
        let features = steps
            .iter()
            .map(|step| Features::new(step))
            .collect::<Vec<_>>();

        let start = std::time::Instant::now();
        for _ in 0..n {
            let scores = scorer.score_batch(&features).unwrap();
            for score in scores {
                assert!(score.is_finite());
            }
        }
        let elapsed = start.elapsed().as_secs_f32();
        total_seconds += elapsed;
        println!("batch {} took {:.3} seconds", i, elapsed);
    }
    let nps = (n * m * 10) as f32 / total_seconds;
    println!("{:.1} scores per second", nps);
}
