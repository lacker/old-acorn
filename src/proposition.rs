use tower_lsp::lsp_types::Range;

use crate::acorn_value::AcornValue;
use crate::module::ModuleId;

// The different reasons that can lead us to create a proposition.
#[derive(Debug, Clone)]
pub enum SourceType {
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

// The information about where a proposition comes from.
#[derive(Debug, Clone)]
pub struct Source {
    // The module where this value was defined
    pub module: ModuleId,

    // The range in the source document that corresponds to the value's definition
    pub range: Range,

    // How the expression at this location was turned into a proposition
    pub source_type: SourceType,
}

// A value along with information on where to find it in the source.
#[derive(Debug, Clone)]
pub struct Proposition {
    // A boolean value. The essence of the proposition is "value is true".
    pub value: AcornValue,

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
            source: Source {
                module,
                range,
                source_type: SourceType::Axiom(axiom_name),
            },
        }
    }

    pub fn theorem(
        axiomatic: bool,
        value: AcornValue,
        module: ModuleId,
        range: Range,
        theorem_name: String,
    ) -> Proposition {
        let source_type = if axiomatic {
            SourceType::Axiom(theorem_name)
        } else {
            SourceType::Theorem(theorem_name)
        };
        Proposition {
            value,
            source: Source {
                module,
                range,
                source_type,
            },
        }
    }

    pub fn anonymous(value: AcornValue, module: ModuleId, range: Range) -> Proposition {
        Proposition {
            value,
            source: Source {
                module,
                range,
                source_type: SourceType::Anonymous,
            },
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
            source: Source {
                module,
                range,
                source_type: SourceType::Definition(name),
            },
        }
    }

    pub fn condition(value: AcornValue, module: ModuleId, range: Range) -> Proposition {
        Proposition {
            value,
            source: Source {
                module,
                range,
                source_type: SourceType::Condition,
            },
        }
    }

    // Just changes the value while keeping the other stuff intact
    pub fn with_value(&self, value: AcornValue) -> Proposition {
        Proposition {
            value,
            source: self.source.clone(),
        }
    }

    // Theorems and axioms have names
    pub fn name(&self) -> Option<&str> {
        match &self.source.source_type {
            SourceType::Axiom(name) => Some(name),
            SourceType::Theorem(name) => Some(name),
            _ => None,
        }
    }
}
