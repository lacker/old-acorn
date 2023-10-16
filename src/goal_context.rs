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
        let mut graph = DependencyGraph::new(&self.facts);
        for fact in &self.facts {
            graph.handle_instantiations(&self.facts, fact);
        }
        graph.handle_instantiations(&self.facts, &self.goal);

        let mut answer = vec![];
        for (fact, instantiations) in self.facts.iter().zip(graph.instantiations_for_fact) {
            if instantiations.is_none() {
                answer.push(fact.clone());
                continue;
            }
            for instantiation in instantiations.unwrap() {
                answer.push(fact.instantiate(&[instantiation]));
            }
        }
        self.facts.clone()
    }
}

// A helper structure to determine which instantiations are necessary.
// Doesn't include facts in order to make memory ownership easier.
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
    // Populates facts_for_constant, and puts None vs Some([]) in the right place for
    // instantiations_for_fact.
    fn new(facts: &Vec<AcornValue>) -> DependencyGraph {
        let mut instantiations_for_fact: Vec<Option<Vec<AcornType>>> = vec![];
        let mut facts_for_constant = HashMap::new();
        for (i, fact) in facts.iter().enumerate() {
            let mut generic_constants = vec![];
            fact.find_templated(&mut generic_constants);
            if generic_constants.is_empty() {
                instantiations_for_fact.push(None);
                continue;
            }
            instantiations_for_fact.push(Some(vec![]));
            for c in generic_constants {
                facts_for_constant.entry(c).or_insert(vec![]).push(i);
            }
        }

        DependencyGraph {
            instantiations_for_fact,
            instantiations_for_constant: HashMap::new(),
            facts_for_constant,
        }
    }

    // Called when we realize that we need to instantiate constant_id with acorn_type.
    fn handle_instantiation(
        &mut self,
        facts: &Vec<AcornValue>,
        constant_id: AtomId,
        acorn_type: &AcornType,
    ) {
        let instantiations = self
            .instantiations_for_constant
            .entry(constant_id)
            .or_insert(vec![]);
        if instantiations.contains(acorn_type) {
            // We already have this instantiation
            return;
        }
        instantiations.push(acorn_type.clone());
        let instantiation_arg = vec![acorn_type.clone()];

        // Handle all the facts that mention this constant without instantiating it.
        if let Some(fact_ids) = self.facts_for_constant.get(&constant_id) {
            for fact_id in fact_ids.clone() {
                let fact_instance = facts[fact_id].instantiate(&instantiation_arg);
                self.handle_instantiations(facts, &fact_instance);
            }
        }
    }

    // Make sure that we are generating any instantiations that are used in this value.
    fn handle_instantiations(&mut self, facts: &Vec<AcornValue>, value: &AcornValue) {
        let mut instantiated = vec![];
        value.find_instantiated(&mut instantiated);
        for (constant_id, acorn_type) in instantiated {
            self.handle_instantiation(facts, constant_id, &acorn_type);
        }
    }
}
