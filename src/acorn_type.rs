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
    Any,
}

impl AcornType {
    // Constructs a type nested into x -> y -> z form.
    fn curry(mut arg_types: Vec<AcornType>, return_type: AcornType) -> AcornType {
        if arg_types.len() == 0 {
            return_type
        } else {
            let first_arg = arg_types.remove(0);
            AcornType::Function(FunctionType {
                arg_types: vec![first_arg],
                return_type: Box::new(AcornType::curry(arg_types, return_type)),
            })
        }
    }

    // Curries all the way down.
    pub fn curry_all(&self) -> AcornType {
        match self {
            AcornType::Function(function_type) => {
                let args = function_type
                    .arg_types
                    .iter()
                    .map(|t| t.curry_all())
                    .collect();
                let return_type = function_type.return_type.curry_all();
                AcornType::curry(args, return_type)
            }
            AcornType::Bool => AcornType::Bool,
            AcornType::Axiomatic(_) => self.clone(),
            _ => panic!("Can't curry {:?}", self),
        }
    }

    // Create the type, in non-curried form, for a function with the given arguments and return type.
    pub fn functional(arg_types: Vec<AcornType>, return_type: AcornType) -> AcornType {
        if arg_types.is_empty() {
            return_type
        } else {
            AcornType::Function(FunctionType {
                arg_types,
                return_type: Box::new(return_type),
            })
        }
    }

    // Create the type you get when you apply this type to the given type.
    // Does partial application.
    pub fn apply(&self, arg_type: &AcornType) -> AcornType {
        todo!();
    }

    // A normal type is something we'd expect the theorem prover to be able to use
    pub fn is_normal(&self) -> bool {
        match self {
            AcornType::Function(function_type) => {
                if function_type.arg_types.len() == 0 {
                    return false;
                }
                for arg_type in &function_type.arg_types {
                    if !arg_type.is_normal() {
                        return false;
                    }
                }
                function_type.return_type.is_normal()
            }
            AcornType::Bool => true,
            AcornType::Axiomatic(_) => true,
            _ => false,
        }
    }

    pub fn into_vec(self) -> Vec<AcornType> {
        match self {
            AcornType::ArgList(t) => t,
            _ => vec![self],
        }
    }

    pub fn into_arg_list(self) -> AcornType {
        AcornType::ArgList(self.into_vec())
    }

    pub fn vec_to_str(types: &Vec<AcornType>) -> String {
        let mut result = String::new();
        for (i, acorn_type) in types.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            result.push_str(&format!("{}", acorn_type));
        }
        result
    }

    pub fn decs_to_str(dec_types: &Vec<AcornType>, stack_size: usize) -> String {
        let mut result = String::new();
        for (i, dec_type) in dec_types.iter().enumerate() {
            if i > 0 {
                result.push_str(", ");
            }
            result.push_str(&format!("x{}: {}", i + stack_size, dec_type));
        }
        result
    }
}

impl fmt::Display for AcornType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AcornType::Bool => write!(f, "bool"),
            AcornType::Axiomatic(index) => write!(f, "T{}", index),
            AcornType::Function(function_type) => {
                write!(
                    f,
                    "({} -> {})",
                    AcornType::vec_to_str(&function_type.arg_types),
                    function_type.return_type
                )
            }
            AcornType::ArgList(arg_types) => {
                write!(f, "({})", AcornType::vec_to_str(arg_types))
            }
            AcornType::Macro => write!(f, "macro"),
            AcornType::Any => write!(f, "any"),
        }
    }
}
