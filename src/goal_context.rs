use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
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

// A helper structure to determine which instantiations are necessary.
// This only handles a single templated type.
struct DependencyGraph {
    // Parallel to facts
    instantiations_for_fact: Vec<Vec<AcornType>>,

    // Indexed by constant id
    instantiations_for_constant: Vec<Vec<AcornType>>,

    // Which facts mention each templated constant.
    // This one is static and only needs to be computed once.
    facts_for_constant: Vec<Vec<usize>>,
}

impl DependencyGraph {
    // Construct a new dependency graph but only populate facts_for_constant
    fn new(facts: &Vec<AcornValue>) -> DependencyGraph {
        todo!();
    }
}
