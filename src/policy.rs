use crate::clause::Clause;
use crate::proof_step::{Rule, Truthiness};

pub struct ManualPolicy {}

impl ManualPolicy {
    pub fn new() -> ManualPolicy {
        ManualPolicy {}
    }

    // The first heuristic is like negative depth.
    // It's bounded at -2 so after that we don't use depth for scoring any more.
    //
    // The second heuristic is an ordering by the type
    //
    //   Global facts, both explicit and deductions
    //   The negated goal
    //   Explicit hypotheses
    //   Local deductions
    //
    // The third heuristic is a combination of a bunch of stuff, roughly to discourage
    // complexity.
    pub fn score(
        &self,
        clause: &Clause,
        truthiness: Truthiness,
        rule: &Rule,
        proof_size: u32,
        depth: u32,
    ) -> (i32, i32, i32) {
        // The first heuristic is 0 for zero depth, -1 for depth 1, -2 for anything deeper.
        let heuristic1 = match depth {
            0 => 0,
            1 => -1,
            _ => -2,
        };

        // The second heuristic is based on truthiness.
        // Higher = more important.
        let heuristic2 = match truthiness {
            Truthiness::Counterfactual => {
                if rule.is_negated_goal() {
                    3
                } else {
                    1
                }
            }
            Truthiness::Hypothetical => {
                if let Rule::Assumption(_) = rule {
                    2
                } else {
                    1
                }
            }
            Truthiness::Factual => 4,
        };

        // The third heuristic is a hodgepodge.
        let mut heuristic3 = 0;
        heuristic3 -= clause.atom_count() as i32;
        heuristic3 -= 2 * proof_size as i32;
        if truthiness == Truthiness::Hypothetical {
            heuristic3 -= 3;
        }
        (heuristic1, heuristic2, heuristic3)
    }
}
