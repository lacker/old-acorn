use tower_lsp::lsp_types::Range;

use crate::acorn_value::AcornValue;
use crate::environment::Environment;
use crate::fact::Fact;
use crate::module::ModuleId;
use crate::monomorphizer::Monomorphizer;
use crate::proof_step::Truthiness;
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

    // Propositions in global scope, but not imported ones.
    global_props: Vec<Proposition>,

    // Propositions that are in a block containing this goal.
    local_props: Vec<Proposition>,

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
        global_props: Vec<Proposition>,
        local_props: Vec<Proposition>,
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
            global_props,
            local_props,
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
    // Sometimes we need to monomorphize an imported fact, so those need to be provided.
    pub fn monomorphize(&self, imported_props: Vec<Proposition>) -> Vec<Fact> {
        let mut input_facts = vec![];
        for prop in imported_props {
            input_facts.push(Fact::new(prop, Truthiness::Factual));
        }
        for prop in &self.global_props {
            input_facts.push(Fact::new(prop.clone(), Truthiness::Factual));
        }
        for prop in &self.local_props {
            input_facts.push(Fact::new(prop.clone(), Truthiness::Hypothetical));
        }
        let mut graph = Monomorphizer::new(&input_facts);

        for fact in &input_facts {
            fact.value.validate().unwrap_or_else(|e| {
                panic!("bad fact: {} ({})", &fact.value, e);
            });
            graph.inspect_value(&input_facts, &fact.value);
        }
        graph.inspect_value(&input_facts, &self.goal.value());

        assert!(input_facts.len() == graph.monomorphs_for_fact.len());

        let mut output_facts = vec![];
        for (fact, monomorph_keys) in input_facts.into_iter().zip(graph.monomorphs_for_fact) {
            if monomorph_keys.is_none() {
                output_facts.push(fact);
                continue;
            }
            for monomorph_key in monomorph_keys.unwrap() {
                output_facts.push(fact.specialize(&monomorph_key.params));
            }
        }
        output_facts
    }
}
