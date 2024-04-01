use std::fmt;

use crate::acorn_type::AcornType;
use crate::module::ModuleId;

#[derive(Debug)]
pub enum CodeGenError {
    // Trouble expressing a skolem function created during normalization.
    Skolem(String),

    // Trouble referencing a module that has not been directly imported.
    UnimportedModule(ModuleId),

    // Trouble using a type that we can't find the name for.
    UnnamedType(String),

    // Some sort of value we could handle, but we don't yet, because it's rare.
    UnhandledValue(String),

    // The goal is implicit, so we can't generate code for it.
    ImplicitGoal,

    // When you try to generate code but there is no proof
    NoProof,
}

impl CodeGenError {
    pub fn skolem(s: &str) -> CodeGenError {
        CodeGenError::Skolem(s.to_string())
    }

    pub fn unnamed_type(acorn_type: &AcornType) -> CodeGenError {
        CodeGenError::UnnamedType(format!("{:?}", acorn_type))
    }

    pub fn unhandled_value(s: &str) -> CodeGenError {
        CodeGenError::UnhandledValue(s.to_string())
    }
}

impl fmt::Display for CodeGenError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CodeGenError::Skolem(s) => {
                write!(f, "could not find a name for the skolem constant: {}", s)
            }
            CodeGenError::UnimportedModule(m) => {
                write!(f, "could not find local name for module {}", m)
            }
            CodeGenError::UnnamedType(s) => {
                write!(f, "could not figure out a name for the type: {}", s)
            }
            CodeGenError::UnhandledValue(s) => {
                write!(f, "codegen for '{}' values is not yet implemented", s)
            }
            CodeGenError::ImplicitGoal => write!(
                f,
                "unable to find a simpler proposition that implies the goal"
            ),
            CodeGenError::NoProof => write!(f, "no proof"),
        }
    }
}
