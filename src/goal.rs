use tower_lsp::lsp_types::Range;

use crate::acorn_value::AcornValue;
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

// A goal along with some information related to it.
pub struct GoalContext<'a> {
    env: &'a Environment,
    pub module_id: ModuleId,

    // Propositions in global scope, but not imported ones.
    pub global_props: Vec<Proposition>,

    // Propositions that are in a block containing this goal.
    pub local_props: Vec<Proposition>,

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
}
