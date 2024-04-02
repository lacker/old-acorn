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

    // The code contains the explicit goal, which we can't generate code for.
    ExplicitGoal,

    // When you try to generate code but there is no proof
    NoProof,

    // Something went wrong, it's our fault, and we can't figure out what it is
    InternalError(String),
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

    pub fn error_type(&self) -> &'static str {
        match self {
            CodeGenError::Skolem(_) => "Skolem",
            CodeGenError::UnimportedModule(_) => "UnimportedModule",
            CodeGenError::UnnamedType(_) => "UnnamedType",
            CodeGenError::UnhandledValue(_) => "UnhandledValue",
            CodeGenError::ExplicitGoal => "ExplicitGoal",
            CodeGenError::NoProof => "NoProof",
            CodeGenError::InternalError(_) => "InternalError",
        }
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
            CodeGenError::ExplicitGoal => {
                write!(f, "could not isolate the goal at the end of the proof")
            }
            CodeGenError::NoProof => write!(f, "no proof"),
            CodeGenError::InternalError(s) => {
                write!(f, "internal error: {}", s)
            }
        }
    }
}
