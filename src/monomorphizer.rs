use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::constant_map::ConstantKey;
use crate::fact::Fact;
use crate::goal::Goal;

// A parameter lists corresponds to a monomorphization.
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
pub struct Monomorphizer {
    // Facts that are not yet monomorphized.
    polymorphic_facts: Vec<Fact>,

    // Facts that are fully monomorphized.
    monomorphic_facts: Vec<Fact>,

    // The parameters we use to monomorphize each fact.
    // Parallel to polymorphic_facts.
    monomorphs_for_fact: Vec<Vec<ParamList>>,

    // Indexed by constant id
    monomorphs_for_constant: HashMap<ConstantKey, Vec<ParamList>>,

    // Where each parametric constant is mentioned in a parametric way.
    // Lists (index in polymorphic facts, params for the constant) for each occurrence.
    // parametric_instances only needs to be computed once.
    parametric_instances: HashMap<ConstantKey, Vec<(usize, ParamList)>>,
}

impl Monomorphizer {
    // Populates monomorphs_for_constant, and puts None vs Some([]) in the right place for
    // monomorphs_for_fact.
    fn new(input_facts: Vec<Fact>) -> Monomorphizer {
        let mut m = Monomorphizer {
            polymorphic_facts: vec![],
            monomorphic_facts: vec![],
            monomorphs_for_fact: vec![],
            monomorphs_for_constant: HashMap::new(),
            parametric_instances: HashMap::new(),
        };
        for fact in input_facts {
            m.add_fact(fact);
        }
        m
    }

    // Adds a fact that could be either polymorphic or monomorphic.
    fn add_fact(&mut self, fact: Fact) {
        let i = self.polymorphic_facts.len();
        let mut instances = vec![];
        fact.value.find_parametric(&mut instances);
        if instances.is_empty() {
            if let AcornValue::ForAll(args, _) = &fact.value {
                if args.iter().any(|arg| arg.is_parametric()) {
                    // This is a polymorphic fact with no polymorphic functions.
                    // It could be something trivial and purely propositional, like
                    // forall(x: T) { x = x }
                    // Just skip it.
                    return;
                }
            }

            // There's nothing to monomorphize here. Just output it.
            self.monomorphic_facts.push(fact);
            return;
        }

        self.polymorphic_facts.push(fact);
        self.monomorphs_for_fact.push(vec![]);
        for (constant_key, params) in instances {
            let params = ParamList::new(params);
            self.parametric_instances
                .entry(constant_key)
                .or_insert(vec![])
                .push((i, params));
        }
    }

    // Do all monomorphization in one big batch.
    pub fn batch(input_facts: Vec<Fact>, goal: &Goal) -> Vec<Fact> {
        let mut graph = Monomorphizer::new(input_facts.clone());

        for fact in &input_facts {
            fact.value.validate().unwrap_or_else(|e| {
                panic!("bad fact: {} ({})", &fact.value, e);
            });
            graph.inspect_value(&fact.value);
        }
        graph.inspect_value(&goal.value());

        assert!(graph.polymorphic_facts.len() == graph.monomorphs_for_fact.len());

        for (fact, monomorph_keys) in graph
            .polymorphic_facts
            .iter()
            .zip(graph.monomorphs_for_fact)
        {
            for monomorph_key in monomorph_keys {
                graph
                    .monomorphic_facts
                    .push(fact.specialize(&monomorph_key.params));
            }
        }
        graph.monomorphic_facts
    }

    // Called when we realize that we need to monomorphize the constant specified by constant_key
    // using the types in monomorph_key.
    fn add_monomorph(&mut self, constant_key: ConstantKey, monomorph_params: &ParamList) {
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

                if self.monomorphs_for_fact[fact_id].contains(&fact_params) {
                    // We already have this monomorph
                    continue;
                }

                let monomorph = self.polymorphic_facts[fact_id]
                    .value
                    .specialize(&fact_params.params);
                if monomorph.is_parametric() {
                    // This is a little awkward. Completely monomorphizing this instance
                    // still doesn't monomorphize the whole fact.
                    // TODO: instead of bailing out, partially monomorphize, and continue.
                    continue;
                }
                self.monomorphs_for_fact[fact_id].push(fact_params);
                self.inspect_value(&monomorph);
            }
        }
    }

    // Make sure that we are generating any monomorphizations that are used in this value.
    fn inspect_value(&mut self, value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_monomorphs(&mut monomorphs);
        for (constant_key, params) in monomorphs {
            self.add_monomorph(constant_key, &ParamList::new(params));
        }
    }
}
