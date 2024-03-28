use tower_lsp::lsp_types::Range;

use crate::acorn_value::AcornValue;
use crate::module::ModuleId;

// The different reasons that can lead us to create a proposition.
#[derive(Debug, Clone)]
pub enum Source {
    // A named axiom
    Axiom(String),

    // A named theorem that is not an axiom.
    Theorem(String),

    // An anonymous proposition that has previously been proved
    Anonymous,

    // A proposition that is implicit in the definition of a struct or constant
    Definition(String),

    // Conditions become propositions inside their conditional block
    Condition,
}

// A value along with information on where to find it in the source.
#[derive(Debug, Clone)]
pub struct Proposition {
    // A boolean value. The essence of the proposition is "value is true".
    pub value: AcornValue,

    // The module where this value was defined
    pub module: ModuleId,

    // The range in the source document that corresponds to the value's definition
    pub range: Range,

    // Where this proposition came from.
    pub source: Source,
}

impl Proposition {
    pub fn axiom(
        value: AcornValue,
        module: ModuleId,
        range: Range,
        axiom_name: String,
    ) -> Proposition {
        Proposition {
            value,
            module,
            range,
            source: Source::Axiom(axiom_name),
        }
    }

    pub fn theorem(
        axiomatic: bool,
        value: AcornValue,
        module: ModuleId,
        range: Range,
        theorem_name: String,
    ) -> Proposition {
        let source = if axiomatic {
            Source::Axiom(theorem_name)
        } else {
            Source::Theorem(theorem_name)
        };
        Proposition {
            value,
            module,
            range,
            source,
        }
    }

    pub fn anonymous(value: AcornValue, module: ModuleId, range: Range) -> Proposition {
        Proposition {
            value,
            module,
            range,
            source: Source::Anonymous,
        }
    }

    pub fn definition(
        value: AcornValue,
        module: ModuleId,
        range: Range,
        name: String,
    ) -> Proposition {
        Proposition {
            value,
            module,
            range,
            source: Source::Definition(name),
        }
    }

    pub fn condition(value: AcornValue, module: ModuleId, range: Range) -> Proposition {
        Proposition {
            value,
            module,
            range,
            source: Source::Condition,
        }
    }

    // Just changes the value while keeping the other stuff intact
    pub fn with_value(&self, value: AcornValue) -> Proposition {
        Proposition {
            value,
            module: self.module,
            range: self.range,
            source: self.source.clone(),
        }
    }

    // Theorems and axioms have names
    pub fn name(&self) -> Option<&str> {
        match &self.source {
            Source::Axiom(name) => Some(name),
            Source::Theorem(name) => Some(name),
            _ => None,
        }
    }
}
