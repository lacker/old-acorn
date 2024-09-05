use crate::clause::Clause;
use crate::proof_step::{Rule, Truthiness};

// Features of a proof step that can be used to score it.
// This is like a feature vector but in struct rather than vector form.
// Try to only use bools, i32s, and f32s.
pub struct Features {
    pub is_contradiction: bool,

    // Features from the clause
    pub atom_count: i32,

    // Features from truthiness
    pub is_counterfactual: bool,
    pub is_hypothetical: bool,
    pub is_factual: bool,

    // Features from the rule
    pub is_assumption: bool,
    pub is_negated_goal: bool,

    // Features from the search process
    pub proof_size: i32,
    pub depth: i32,
}

impl Features {
    pub fn new(
        clause: &Clause,
        truthiness: Truthiness,
        rule: &Rule,
        proof_size: u32,
        depth: u32,
    ) -> Self {
        Features {
            is_contradiction: clause.is_impossible(),
            atom_count: clause.atom_count() as i32,
            is_counterfactual: truthiness == Truthiness::Counterfactual,
            is_hypothetical: truthiness == Truthiness::Hypothetical,
            is_factual: truthiness == Truthiness::Factual,
            is_assumption: rule.is_assumption(),
            is_negated_goal: rule.is_negated_goal(),
            proof_size: proof_size as i32,
            depth: depth as i32,
        }
    }
}
