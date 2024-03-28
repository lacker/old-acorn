use tower_lsp::lsp_types::Range;

use crate::acorn_value::AcornValue;
use crate::module::ModuleId;

// The different reasons that can lead us to create a proposition.
#[derive(Debug, Clone)]
pub enum Source {
    // A named theorem
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

    // Only set when this value is a named theorem
    pub theorem_name: Option<String>,

    // Where this proposition came from.
    pub source: Source,
}

impl Proposition {
    pub fn theorem(
        value: AcornValue,
        module: ModuleId,
        range: Range,
        theorem_name: String,
    ) -> Proposition {
        Proposition {
            value,
            module,
            range,
            theorem_name: Some(theorem_name.clone()),
            source: Source::Theorem(theorem_name),
        }
    }

    pub fn anonymous(value: AcornValue, module: ModuleId, range: Range) -> Proposition {
        Proposition {
            value,
            module,
            range,
            theorem_name: None,
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
            theorem_name: None,
            source: Source::Definition(name),
        }
    }

    pub fn condition(value: AcornValue, module: ModuleId, range: Range) -> Proposition {
        Proposition {
            value,
            module,
            range,
            theorem_name: None,
            source: Source::Condition,
        }
    }

    // Just changes the value while keeping the other stuff intact
    pub fn with_value(&self, value: AcornValue) -> Proposition {
        Proposition {
            value,
            module: self.module,
            range: self.range,
            theorem_name: self.theorem_name.clone(),
            source: self.source.clone(),
        }
    }
}
