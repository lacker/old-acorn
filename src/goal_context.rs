use std::collections::HashMap;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::constant_map::ConstantKey;
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

// Given a bunch of polymorphic facts and goal, return a list of monomorphs just of the facts.
pub fn monomorphize_facts(facts: &[AcornValue], goal: &AcornValue) -> Vec<AcornValue> {
    let mut graph = DependencyGraph::new(facts);

    for fact in facts {
        graph.inspect_value(facts, fact);
    }
    graph.inspect_value(facts, &goal);

    assert!(facts.len() == graph.monomorphs_for_fact.len());

    let mut answer = vec![];
    for (fact, monomorph_types) in facts.iter().zip(graph.monomorphs_for_fact) {
        if monomorph_types.is_none() {
            if fact.is_polymorphic() {
                panic!(
                    "allegedly non-polymorphic fact {} still has type parameters",
                    fact
                );
            }
            answer.push(fact.clone());
            continue;
        }
        for monomorph_type in monomorph_types.unwrap() {
            let monomorph = fact.monomorphize(&[monomorph_type]);
            if monomorph.is_polymorphic() {
                panic!("alleged monomorph {} still has type parameters", monomorph);
            }
            answer.push(monomorph);
        }
    }
    answer
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
    monomorphs_for_constant: HashMap<ConstantKey, Vec<AcornType>>,

    // Which facts mention each templated constant *without* monomorphizing it.
    // This one is static and only needs to be computed once.
    facts_for_constant: HashMap<ConstantKey, Vec<usize>>,
}

impl DependencyGraph {
    // Populates facts_for_constant, and puts None vs Some([]) in the right place for
    // monomorphs_for_fact.
    fn new(facts: &[AcornValue]) -> DependencyGraph {
        let mut monomorphs_for_fact = vec![];
        let mut facts_for_constant = HashMap::new();
        for (i, fact) in facts.iter().enumerate() {
            let mut polymorphic_fns = vec![];
            fact.find_polymorphic(&mut polymorphic_fns);
            if polymorphic_fns.is_empty() {
                if let AcornValue::ForAll(args, _) = fact {
                    if args.iter().any(|arg| arg.is_polymorphic()) {
                        // This is a polymorphic fact with no polymorphic functions.
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
            for c in polymorphic_fns {
                facts_for_constant.entry(c).or_insert(vec![]).push(i);
            }
        }

        DependencyGraph {
            monomorphs_for_fact,
            monomorphs_for_constant: HashMap::new(),
            facts_for_constant,
        }
    }

    // Called when we realize that we need to monomorphize the constant specified by constant_key
    // with acorn_type.
    fn add_monomorph(
        &mut self,
        facts: &[AcornValue],
        constant_key: ConstantKey,
        acorn_type: &AcornType,
    ) {
        let monomorphs = self
            .monomorphs_for_constant
            .entry(constant_key.clone())
            .or_insert(vec![]);
        if monomorphs.contains(acorn_type) {
            // We already have this monomorph
            return;
        }
        monomorphs.push(acorn_type.clone());
        let monomorphize_arg = vec![acorn_type.clone()];

        // Handle all the facts that mention this constant without monomorphizing it.
        if let Some(fact_ids) = self.facts_for_constant.get(&constant_key) {
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
    fn inspect_value(&mut self, facts: &[AcornValue], value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_monomorphs(&mut monomorphs);
        for (constant_key, acorn_type) in monomorphs {
            self.add_monomorph(facts, constant_key, &acorn_type);
        }
    }
}
