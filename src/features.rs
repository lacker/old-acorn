use crate::clause::Clause;
use crate::proof_step::{Rule, Truthiness};

// Features of a proof step that can be used to score it.
// This is like a feature vector but in struct rather than vector form.
pub struct Features {
    pub contradiction: bool,

    // Features from the clause
    pub atom_count: u32,

    // Features from truthiness
    pub is_counterfactual: bool,
    pub is_hypothetical: bool,
    pub is_factual: bool,

    // Features from the rule
    pub is_negated_goal: bool,

    // Features from the search process
    pub proof_size: u32,
    pub depth: u32,
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
            contradiction: clause.is_impossible(),
            atom_count: clause.atom_count(),
            is_counterfactual: truthiness == Truthiness::Counterfactual,
            is_hypothetical: truthiness == Truthiness::Hypothetical,
            is_factual: truthiness == Truthiness::Factual,
            is_negated_goal: rule.is_negated_goal(),
            proof_size,
            depth,
        }
    }
}
