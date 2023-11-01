use std::collections::HashMap;
use std::fmt;

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
        fact.validate().unwrap_or_else(|e| {
            panic!("bad fact: {} ({})", fact, e);
        });
        graph.inspect_value(facts, fact);
    }
    graph.inspect_value(facts, &goal);

    assert!(facts.len() == graph.monomorphs_for_fact.len());

    let mut answer = vec![];
    for (fact, monomorph_keys) in facts.iter().zip(graph.monomorphs_for_fact) {
        if monomorph_keys.is_none() {
            answer.push(fact.clone());
            continue;
        }
        for monomorph_key in monomorph_keys.unwrap() {
            let monomorph = fact.specialize(&monomorph_key.params);
            if monomorph.is_parametric() {
                panic!("monomorph {} is still parametric", monomorph);
            }
            answer.push(monomorph);
        }
    }
    answer
}

// Each monomorph is identified by its MonomorphKey
#[derive(PartialEq, Eq, Hash, Clone)]
struct MonomorphKey {
    // Sorted
    params: Vec<(String, AcornType)>,
}

impl fmt::Display for MonomorphKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, (name, t)) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{} => {}", name, t)?;
        }
        Ok(())
    }
}

impl MonomorphKey {
    fn new(params: Vec<(String, AcornType)>) -> MonomorphKey {
        let mut params = params;
        params.sort();
        for (name, t) in &params {
            if t.is_parametric() {
                panic!("bad monomorphization: {} = {}", name, t);
            }
        }
        MonomorphKey { params }
    }
}

// A helper structure to determine which monomorphs are necessary.
// Doesn't include facts in order to make memory ownership easier.
// This only handles a single parametric type.
struct DependencyGraph {
    // The monomorphic types that we need/want for each fact.
    // Parallel to facts.
    // The entry is None if the fact is not polymorphic.
    monomorphs_for_fact: Vec<Option<Vec<MonomorphKey>>>,

    // Indexed by constant id
    monomorphs_for_constant: HashMap<ConstantKey, Vec<MonomorphKey>>,

    // Which facts mention each parametric constant *without* monomorphizing it.
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
            fact.find_parametric(&mut polymorphic_fns);
            if polymorphic_fns.is_empty() {
                if let AcornValue::ForAll(args, _) = fact {
                    if args.iter().any(|arg| arg.is_parametric()) {
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
            for (c, _) in polymorphic_fns {
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
    // using the types in monomorph_key.
    fn add_monomorph(
        &mut self,
        facts: &[AcornValue],
        constant_key: ConstantKey,
        monomorph_key: &MonomorphKey,
    ) {
        let monomorphs = self
            .monomorphs_for_constant
            .entry(constant_key.clone())
            .or_insert(vec![]);
        if monomorphs.contains(&monomorph_key) {
            // We already have this monomorph
            return;
        }
        monomorphs.push(monomorph_key.clone());

        // Handle all the facts that mention this constant without monomorphizing it.
        if let Some(fact_ids) = self.facts_for_constant.get(&constant_key) {
            for fact_id in fact_ids.clone() {
                // Check if we already know we need this monomorph for the fact
                // If not, insert it
                let monomorphs_for_fact = self.monomorphs_for_fact[fact_id]
                    .as_mut()
                    .expect("Should have been Some");
                if monomorphs_for_fact.contains(monomorph_key) {
                    continue;
                }
                monomorphs_for_fact.push(monomorph_key.clone());

                // TODO: this logic is wrong. We know that this constant is mentioned in the fact,
                // but that doesn't mean we can monomorphize the whole fact using parameters
                // that make sense for the constant alone. The names of the parameters in the fact
                // could be totally different from the names of the parameters in the constant's
                // definition.
                let monomorph = facts[fact_id].specialize(&monomorph_key.params);

                self.inspect_value(facts, &monomorph);
            }
        }
    }

    // Make sure that we are generating any monomorphizations that are used in this value.
    fn inspect_value(&mut self, facts: &[AcornValue], value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_monomorphs(&mut monomorphs);
        for (constant_key, params) in monomorphs {
            self.add_monomorph(facts, constant_key, &MonomorphKey::new(params));
        }
    }
}
