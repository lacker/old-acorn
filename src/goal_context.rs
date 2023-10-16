use tower_lsp::lsp_types::Range;

use crate::acorn_value::AcornValue;
use crate::environment::Environment;

// A goal and the information used to prove it.
pub struct GoalContext<'a> {
    pub env: &'a Environment,

    // The facts that can be used to prove the goal.
    pub facts: Vec<AcornValue>,

    // A printable name for this goal.
    pub name: String,

    // The goal itself.
    pub goal: AcornValue,

    // The range in the source document corresponding to this goal.
    pub range: Range,
}

impl GoalContext<'_> {
    // Find all instantiations of the facts that are needed to prove the goal.
    pub fn instantiate_facts(&self) -> Vec<AcornValue> {
        self.facts.clone()
    }
}
