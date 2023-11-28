use std::collections::HashMap;
use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::constant_map::ConstantKey;
use crate::environment::Environment;
use crate::module::NamespaceId;

// A goal and the information used to prove it.
pub struct GoalContext<'a> {
    env: &'a Environment,

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
    pub fn new(
        env: &Environment,
        facts: Vec<AcornValue>,
        name: String,
        goal: AcornValue,
        range: Range,
    ) -> GoalContext {
        GoalContext {
            env,
            facts,
            name,
            goal,
            range,
        }
    }

    pub fn includes_explicit_false(&self) -> bool {
        self.env.includes_explicit_false
    }

    pub fn namespace(&self) -> NamespaceId {
        self.env.namespace
    }
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

// For the purposes of the goal context, we store parameter lists that correspond to
// monomorphizations.
#[derive(PartialEq, Eq, Hash, Clone)]
struct ParamList {
    // Sorted
    params: Vec<(String, AcornType)>,
}

impl fmt::Display for ParamList {
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

impl ParamList {
    fn new(params: Vec<(String, AcornType)>) -> ParamList {
        ParamList { params }
    }

    fn assert_monomorph(&self) {
        for (name, t) in &self.params {
            if t.is_parametric() {
                panic!("bad monomorphization: {} = {}", name, t);
            }
        }
    }
}

// A helper structure to determine which monomorphs are necessary.
// Doesn't include facts in order to make memory ownership easier.
// This only handles a single parametric type.
struct DependencyGraph {
    // The monomorphic types that we need/want for each fact.
    // Parallel to facts.
    // The entry is None if the fact is not polymorphic.
    monomorphs_for_fact: Vec<Option<Vec<ParamList>>>,

    // Indexed by constant id
    monomorphs_for_constant: HashMap<ConstantKey, Vec<ParamList>>,

    // Where each parametric constant is mentioned in a parametric way.
    // Lists (fact id, params for the constant) for each occurrence.
    // parametric_instances only needs to be computed once.
    parametric_instances: HashMap<ConstantKey, Vec<(usize, ParamList)>>,
}

impl DependencyGraph {
    // Populates facts_for_constant, and puts None vs Some([]) in the right place for
    // monomorphs_for_fact.
    fn new(facts: &[AcornValue]) -> DependencyGraph {
        let mut monomorphs_for_fact = vec![];
        let mut parametric_instances = HashMap::new();
        for (i, fact) in facts.iter().enumerate() {
            let mut instances = vec![];
            fact.find_parametric(&mut instances);
            if instances.is_empty() {
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
            for (constant_key, params) in instances {
                let params = ParamList::new(params);
                parametric_instances
                    .entry(constant_key)
                    .or_insert(vec![])
                    .push((i, params));
            }
        }

        DependencyGraph {
            monomorphs_for_fact,
            monomorphs_for_constant: HashMap::new(),
            parametric_instances,
        }
    }

    // Called when we realize that we need to monomorphize the constant specified by constant_key
    // using the types in monomorph_key.
    fn add_monomorph(
        &mut self,
        facts: &[AcornValue],
        constant_key: ConstantKey,
        monomorph_params: &ParamList,
    ) {
        monomorph_params.assert_monomorph();
        let monomorphs = self
            .monomorphs_for_constant
            .entry(constant_key.clone())
            .or_insert(vec![]);
        if monomorphs.contains(&monomorph_params) {
            // We already have this monomorph
            return;
        }
        monomorphs.push(monomorph_params.clone());

        // Handle all the facts that mention this constant without monomorphizing it.
        if let Some(instances) = self.parametric_instances.get(&constant_key) {
            for (fact_id, instance_params) in instances.clone() {
                // The instance params are the way this instance was parametrized in the fact.
                // The monomorph params are how we would like to parametrize this instance.
                // It may or may not be possible to match them up.
                // For example, this may be a fact about foo<bool, T>, and our goal
                // is saying something about foo<Nat, Nat>.
                // Our goal is to find the "fact params", a way in which we can parametrize
                // the whole fact so that the instance params become the monomorph params.
                assert_eq!(instance_params.params.len(), monomorph_params.params.len());
                let mut fact_params = HashMap::new();
                for ((i_name, instance_type), (m_name, monomorph_type)) in instance_params
                    .params
                    .iter()
                    .zip(monomorph_params.params.iter())
                {
                    assert_eq!(i_name, m_name);
                    instance_type.match_specialized(monomorph_type, &mut fact_params);
                }

                // We sort because there's no inherently canonical order.
                let mut fact_params: Vec<_> = fact_params.into_iter().collect();
                fact_params.sort();
                let fact_params = ParamList::new(fact_params);

                let monomorphs_for_fact = self.monomorphs_for_fact[fact_id]
                    .as_mut()
                    .expect("Should have been Some");
                if monomorphs_for_fact.contains(&fact_params) {
                    // We already have this monomorph
                    continue;
                }

                let monomorph = facts[fact_id].specialize(&fact_params.params);
                if monomorph.is_parametric() {
                    // This is a little awkward. Completely monomorphizing this instance
                    // still doesn't monomorphize the whole fact.
                    // TODO: instead of bailing out, partially monomorphize, and continue.
                    continue;
                }
                monomorphs_for_fact.push(fact_params);
                self.inspect_value(facts, &monomorph);
            }
        }
    }

    // Make sure that we are generating any monomorphizations that are used in this value.
    fn inspect_value(&mut self, facts: &[AcornValue], value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_monomorphs(&mut monomorphs);
        for (constant_key, params) in monomorphs {
            self.add_monomorph(facts, constant_key, &ParamList::new(params));
        }
    }
}
