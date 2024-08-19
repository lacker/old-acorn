use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::module::ModuleId;

// The different reasons that can lead us to create a proposition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceType {
    // A named axiom
    Axiom(String),

    // A named theorem that is not an axiom.
    Theorem(String),

    // An anonymous proposition that has previously been proved
    Anonymous,

    // A proposition that is implicit in the definition of a type
    TypeDefinition(String),

    // A proposition that is implicit in the definition of a constant
    ConstantDefinition(AcornValue),

    // A premise for a block that contains the current environment
    Premise,

    // A proposition generated by negating a goal, for the sake of proving it by contradiction
    NegatedGoal,
}

// The information about where a proposition comes from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Source {
    // The module where this value was defined
    pub module: ModuleId,

    // The range in the source document that corresponds to the value's definition
    pub range: Range,

    // How the expression at this location was turned into a proposition
    pub source_type: SourceType,
}

impl Source {
    pub fn mock() -> Source {
        Source {
            module: 0,
            range: Range::default(),
            source_type: SourceType::Anonymous,
        }
    }

    // The line the user sees, starting from 1.
    pub fn user_visible_line(&self) -> u32 {
        self.range.start.line + 1
    }

    pub fn description(&self) -> String {
        match &self.source_type {
            SourceType::Axiom(name) => format!("the '{}' axiom", name),
            SourceType::Theorem(name) => format!("the '{}' theorem", name),
            SourceType::Anonymous => format!("line {}", self.user_visible_line()),
            SourceType::TypeDefinition(name) => format!("the '{}' definition", name),
            SourceType::ConstantDefinition(value) => format!("the '{}' definition", value),
            SourceType::Premise => "an assumed premise".to_string(),
            SourceType::NegatedGoal => "negating the goal".to_string(),
        }
    }

    pub fn is_axiom(&self) -> bool {
        match self.source_type {
            SourceType::Axiom(_) => true,
            _ => false,
        }
    }
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

    pub fn type_definition(
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
                source_type: SourceType::TypeDefinition(name),
            },
        }
    }

    pub fn constant_definition(
        value: AcornValue,
        module: ModuleId,
        range: Range,
        constant: AcornValue,
    ) -> Proposition {
        Proposition {
            value,
            source: Source {
                module,
                range,
                source_type: SourceType::ConstantDefinition(constant),
            },
        }
    }

    pub fn premise(value: AcornValue, module: ModuleId, range: Range) -> Proposition {
        Proposition {
            value,
            source: Source {
                module,
                range,
                source_type: SourceType::Premise,
            },
        }
    }

    pub fn with_negated_goal(&self, value: AcornValue) -> Proposition {
        Proposition {
            value,
            source: Source {
                module: self.source.module,
                range: self.source.range,
                source_type: SourceType::NegatedGoal,
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

    // Specializes a templated proposition.
    pub fn specialize(&self, params: &[(String, AcornType)]) -> Proposition {
        let value = self.value.specialize(params);
        if value.is_parametric() {
            panic!("monomorph {} is still parametric", value);
        }
        let source = match &self.source.source_type {
            SourceType::ConstantDefinition(v) => {
                let new_type = SourceType::ConstantDefinition(v.specialize(params));
                Source {
                    module: self.source.module,
                    range: self.source.range.clone(),
                    source_type: new_type,
                }
            }
            _ => self.source.clone(),
        };
        Proposition { value, source }
    }
}
