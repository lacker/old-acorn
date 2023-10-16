use std::collections::HashMap;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::atom::AtomId;
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
        // let graph = DependencyGraph::new(&self.facts);
        self.facts.clone()
    }
}

// A helper structure to determine which instantiations are necessary.
// This only handles a single templated type.
struct DependencyGraph {
    // The instantiations that we need/want for each fact.
    // Parallel to facts.
    // The entry is None if the fact is not generic.
    instantiations_for_fact: Vec<Option<Vec<AcornType>>>,

    // Indexed by constant id
    instantiations_for_constant: HashMap<AtomId, Vec<AcornType>>,

    // Which facts mention each templated constant *without* instantiating it.
    // This one is static and only needs to be computed once.
    facts_for_constant: HashMap<AtomId, Vec<usize>>,
}

impl DependencyGraph {
    // Populates facts_for_constant but not the other fields.
    fn new(facts: &Vec<AcornValue>) -> DependencyGraph {
        let mut instantiations_for_fact: Vec<Option<Vec<AcornType>>> = vec![];
        let mut facts_for_constant = HashMap::new();
        for (i, fact) in facts.iter().enumerate() {
            let mut generic_constants = vec![];
            fact.find_generic_constants(&mut generic_constants);
            if generic_constants.is_empty() {
                instantiations_for_fact.push(None);
                continue;
            }
            instantiations_for_fact.push(Some(vec![]));
            for c in generic_constants {
                facts_for_constant
                    .entry(c as AtomId)
                    .or_insert(vec![])
                    .push(i);
            }
        }

        DependencyGraph {
            instantiations_for_fact,
            instantiations_for_constant: HashMap::new(),
            facts_for_constant,
        }
    }
}
