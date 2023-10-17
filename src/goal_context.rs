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
    // Find all monomorphizations of the facts that are needed to prove the goal.
    pub fn monomorphize_facts(&self) -> Vec<AcornValue> {
        let mut graph = DependencyGraph::new(&self.facts);

        for fact in &self.facts {
            graph.inspect_value(&self.facts, fact);
        }
        graph.inspect_value(&self.facts, &self.goal);

        let mut answer = vec![];
        for (fact, monomorph_types) in self.facts.iter().zip(graph.monomorphs_for_fact) {
            if monomorph_types.is_none() {
                if fact.has_generic() {
                    panic!(
                        "allegedly non-polymorphic fact {} still has generics",
                        self.env.value_str(fact)
                    );
                }
                answer.push(fact.clone());
                continue;
            }
            for monomorph_type in monomorph_types.unwrap() {
                let monomorph = fact.monomorphize(&[monomorph_type]);
                if monomorph.has_generic() {
                    panic!(
                        "alleged monomorph {} still has generics",
                        self.env.value_str(&monomorph)
                    );
                }
                answer.push(monomorph);
            }
        }
        answer
    }
}

// A helper structure to determine which monomorphs are necessary.
// Doesn't include facts in order to make memory ownership easier.
// This only handles a single templated type.
struct DependencyGraph {
    // The monomorphic types that we need/want for each fact.
    // Parallel to facts.
    // The entry is None if the fact is not polymorphic.
    monomorphs_for_fact: Vec<Option<Vec<AcornType>>>,

    // Indexed by constant id
    monomorphs_for_constant: HashMap<AtomId, Vec<AcornType>>,

    // Which facts mention each templated constant *without* monomorphizing it.
    // This one is static and only needs to be computed once.
    facts_for_constant: HashMap<AtomId, Vec<usize>>,
}

impl DependencyGraph {
    // Populates facts_for_constant, and puts None vs Some([]) in the right place for
    // monomorphs_for_fact.
    fn new(facts: &Vec<AcornValue>) -> DependencyGraph {
        let mut monomorphs_for_fact = vec![];
        let mut facts_for_constant = HashMap::new();
        for (i, fact) in facts.iter().enumerate() {
            let mut polymorphic_constants = vec![];
            fact.find_polymorphic(&mut polymorphic_constants);
            if polymorphic_constants.is_empty() {
                if let AcornValue::ForAll(args, _) = fact {
                    if args.iter().any(|arg| arg.is_polymorphic()) {
                        // This is a polymorphic fact with no polymorphic constants.
                        // It could be something trivial and purely propositional, like
                        // forall(x: T) { x = x }
                        // Just skip it.
                        monomorphs_for_fact.push(Some(vec![]));
                        continue;
                    }
                }

                monomorphs_for_fact.push(None);
                continue;
            }
            monomorphs_for_fact.push(Some(vec![]));
            for c in polymorphic_constants {
                facts_for_constant.entry(c).or_insert(vec![]).push(i);
            }
        }

        DependencyGraph {
            monomorphs_for_fact,
            monomorphs_for_constant: HashMap::new(),
            facts_for_constant,
        }
    }

    // Called when we realize that we need to monomorphize constant_id with acorn_type.
    fn monomorphize(
        &mut self,
        facts: &Vec<AcornValue>,
        constant_id: AtomId,
        acorn_type: &AcornType,
    ) {
        let monomorphs = self
            .monomorphs_for_constant
            .entry(constant_id)
            .or_insert(vec![]);
        if monomorphs.contains(acorn_type) {
            // We already have this monomorph
            return;
        }
        monomorphs.push(acorn_type.clone());
        let monomorphize_arg = vec![acorn_type.clone()];

        // Handle all the facts that mention this constant without monomorphizing it.
        if let Some(fact_ids) = self.facts_for_constant.get(&constant_id) {
            for fact_id in fact_ids.clone() {
                // Check if we already know we need this monomorph for the fact
                // If not, insert it
                let monomorphs_for_fact = self.monomorphs_for_fact[fact_id]
                    .as_mut()
                    .expect("Should have been Some");
                if monomorphs_for_fact.contains(acorn_type) {
                    continue;
                }
                monomorphs_for_fact.push(acorn_type.clone());

                let monomorph = facts[fact_id].monomorphize(&monomorphize_arg);
                self.inspect_value(facts, &monomorph);
            }
        }
    }

    // Make sure that we are generating any monomorphizations that are used in this value.
    fn inspect_value(&mut self, facts: &Vec<AcornValue>, value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_monomorphs(&mut monomorphs);
        for (constant_id, acorn_type) in monomorphs {
            self.monomorphize(facts, constant_id, &acorn_type);
        }
    }
}
