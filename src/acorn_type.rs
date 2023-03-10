use std::fmt;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FunctionType {
    pub arg_types: Vec<AcornType>,
    pub return_type: Box<AcornType>,
}

// An argument list isn't really a type, but it's part of a type.
// It's used when we have more than one argument to a function.
// "Macro" indicates either "forall" or "exists".
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AcornType {
    Bool,
    Axiomatic(usize),
    Function(FunctionType),
    ArgList(Vec<AcornType>),
    Macro,
}

impl AcornType {
    pub fn into_vec(self) -> Vec<AcornType> {
        match self {
            AcornType::ArgList(t) => t,
            _ => vec![self],
        }
    }

    pub fn into_arg_list(self) -> AcornType {
        AcornType::ArgList(self.into_vec())
    }
}

impl fmt::Display for AcornType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AcornType::Bool => write!(f, "bool"),
            AcornType::Axiomatic(index) => write!(f, "a{}", index),
            AcornType::Function(function_type) => {
                write!(
                    f,
                    "({} -> {})",
                    types_to_str(&function_type.arg_types),
                    function_type.return_type
                )
            }
            AcornType::ArgList(arg_types) => {
                write!(f, "({})", types_to_str(arg_types))
            }
            AcornType::Macro => write!(f, "macro"),
        }
    }
}

pub fn types_to_str(types: &Vec<AcornType>) -> String {
    let mut result = String::new();
    for (i, acorn_type) in types.iter().enumerate() {
        if i > 0 {
            result.push_str(", ");
        }
        result.push_str(&format!("{}", acorn_type));
    }
    result
}

pub fn declarations_to_str(dec_types: &Vec<AcornType>, stack_size: usize) -> String {
    let mut result = String::new();
    for (i, dec_type) in dec_types.iter().enumerate() {
        if i > 0 {
            result.push_str(", ");
        }
        result.push_str(&format!("x{}: {}", i + stack_size, dec_type));
    }
    result
}
