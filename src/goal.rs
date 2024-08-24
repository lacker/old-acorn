use std::collections::HashMap;
use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::constant_map::ConstantKey;
use crate::environment::Environment;
use crate::module::ModuleId;
use crate::proposition::Proposition;

#[derive(Debug, Clone)]
pub enum Goal {
    // Prove that this proposition is true.
    Prove(Proposition),

    // Find a simplified form of this value.
    Solve(AcornValue, Range),
}

impl Goal {
    pub fn value(&self) -> &AcornValue {
        match self {
            Goal::Prove(p) => &p.value,
            Goal::Solve(v, _) => v,
        }
    }

    pub fn range(&self) -> Range {
        match self {
            Goal::Prove(p) => p.source.range,
            Goal::Solve(_, r) => *r,
        }
    }
}

// A goal and the information that can be used to achieve it.
pub struct GoalContext<'a> {
    env: &'a Environment,
    pub module_id: ModuleId,

    // Facts that occur outside any block, before this goal.
    global_facts: Vec<Proposition>,

    // Facts that are in a block containing this goal.
    local_facts: Vec<Proposition>,

    // A printable name for this goal.
    pub name: String,

    // The goal itself.
    pub goal: Goal,

    // The zero-based line where we would insert a proof for this goal.
    // None if we do not want to insert a proof for this goal.
    // Logically, we think of it as inserting at the beginning of the line.
    // Code already on that line should be moved down.
    pub proof_insertion_line: u32,
}

impl GoalContext<'_> {
    pub fn new(
        env: &Environment,
        global_facts: Vec<Proposition>,
        local_facts: Vec<Proposition>,
        goal: Goal,
        proof_insertion_line: u32,
    ) -> GoalContext {
        let name = match &goal {
            Goal::Prove(proposition) => match proposition.name() {
                Some(name) => name.to_string(),
                None => env.bindings.value_to_code(&proposition.value).unwrap(),
            },
            Goal::Solve(value, _) => {
                let value_str = env.bindings.value_to_code(value).unwrap();
                format!("solve {}", value_str)
            }
        };
        GoalContext {
            env,
            module_id: env.module_id,
            global_facts,
            local_facts,
            name,
            goal,
            proof_insertion_line,
        }
    }

    pub fn includes_explicit_false(&self) -> bool {
        self.env.includes_explicit_false
    }

    pub fn implicit_block(&self) -> bool {
        self.env.implicit
    }

    pub fn module_id(&self) -> ModuleId {
        self.env.module_id
    }

    // Finds all relevant monomorphizations and a list of monomorphic facts.
    // Returns (global facts, local facts).
    // Sometimes we need to monomorphize an imported fact, so those need to be provided.
    pub fn monomorphize(
        &self,
        imported_facts: Vec<Proposition>,
    ) -> (Vec<Proposition>, Vec<Proposition>) {
        let mut facts = imported_facts;
        facts.extend(self.global_facts.iter().cloned());
        let num_global = facts.len();
        facts.extend(self.local_facts.iter().cloned());
        let mut graph = DependencyGraph::new(&facts);

        for fact in &facts {
            fact.value.validate().unwrap_or_else(|e| {
                panic!("bad fact: {} ({})", &fact.value, e);
            });
            graph.inspect_value(&facts, &fact.value);
        }
        graph.inspect_value(&facts, &self.goal.value());

        assert!(facts.len() == graph.monomorphs_for_fact.len());

        let mut global_out = vec![];
        let mut local_out = vec![];
        for (i, (fact, monomorph_keys)) in facts.iter().zip(graph.monomorphs_for_fact).enumerate() {
            if monomorph_keys.is_none() {
                if i < num_global {
                    global_out.push(fact.clone());
                } else {
                    local_out.push(fact.clone());
                }
                continue;
            }
            for monomorph_key in monomorph_keys.unwrap() {
                let new_fact = fact.specialize(&monomorph_key.params);
                if i < num_global {
                    global_out.push(new_fact);
                } else {
                    local_out.push(new_fact);
                }
            }
        }
        (global_out, local_out)
    }
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
    fn new(facts: &[Proposition]) -> DependencyGraph {
        let mut monomorphs_for_fact = vec![];
        let mut parametric_instances = HashMap::new();
        for (i, fact) in facts.iter().enumerate() {
            let mut instances = vec![];
            fact.value.find_parametric(&mut instances);
            if instances.is_empty() {
                if let AcornValue::ForAll(args, _) = &fact.value {
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
        facts: &[Proposition],
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

                let monomorph = facts[fact_id].value.specialize(&fact_params.params);
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
    fn inspect_value(&mut self, facts: &[Proposition], value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_monomorphs(&mut monomorphs);
        for (constant_key, params) in monomorphs {
            self.add_monomorph(facts, constant_key, &ParamList::new(params));
        }
    }
}
