// Each proof step has a score, which encapsulates all heuristic judgments about
// the proof step.
// The better the score, the more we want to activate this proof step.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Score {
    // The first element of a regular score is the negative depth.
    // It's bounded at -MAX_DEPTH so after that we don't use depth for scoring any more.
    //
    // The second element of the score is a deterministic ordering:
    //
    //   Global facts, both explicit and deductions
    //   The negated goal
    //   Explicit hypotheses
    //   Local deductions
    //
    // The third element of the score is heuristic.
    Regular(i32, i32, i32),

    // Contradictions immediately end the proof and thus score highest.
    Contradiction,
}

// Don't bother differentiating depth for score purposes after this point.
// Basic proofs ignore everything at max depth (and below).
pub const MAX_DEPTH: i32 = 3;

impl Score {
    pub fn is_basic(&self) -> bool {
        match self {
            Score::Regular(negadepth, _, _) => *negadepth > -MAX_DEPTH,
            Score::Contradiction => true,
        }
    }
}
