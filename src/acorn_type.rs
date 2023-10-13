use std::fmt;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FunctionType {
    pub arg_types: Vec<AcornType>,
    pub return_type: Box<AcornType>,
}

// Functional types can be applied.
// Data types include both axiomatic types and struct types.
// Generics are types that are not yet known.
//
// An argument list isn't really a type, but it's part of a type.
// It's used while parsing types.
// For example, the left hand side of (Nat, Nat) -> Nat is an arg list.
//
// "Any" is a hack used for testing.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AcornType {
    Bool,
    Data(usize),
    Generic(usize),
    Function(FunctionType),
    ArgList(Vec<AcornType>),
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
            AcornType::Data(_) => self.clone(),
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

    // Whether this type refers to the other type.
    // For example, (Nat, Int) -> Rat refers to all of Nat, Int, and Rat.
    pub fn refers_to(&self, other_type: &AcornType) -> bool {
        if self == other_type {
            return true;
        }
        match self {
            AcornType::Function(function_type) => {
                for arg_type in &function_type.arg_types {
                    if arg_type.refers_to(other_type) {
                        return true;
                    }
                }
                function_type.return_type.refers_to(other_type)
            }
            AcornType::Data(_) => false,
            AcornType::Generic(_) => false,
            AcornType::ArgList(arg_types) => {
                for arg_type in arg_types {
                    if arg_type.refers_to(other_type) {
                        return true;
                    }
                }
                false
            }
            AcornType::Bool => false,
            AcornType::Any => false,
        }
    }

    // Whether this type has any generic parts.
    pub fn has_generic(&self) -> bool {
        match self {
            AcornType::Function(function_type) => {
                for arg_type in &function_type.arg_types {
                    if arg_type.has_generic() {
                        return true;
                    }
                }
                function_type.return_type.has_generic()
            }
            AcornType::Data(_) => false,
            AcornType::Generic(_) => true,
            AcornType::ArgList(arg_types) => {
                for arg_type in arg_types {
                    if arg_type.has_generic() {
                        return true;
                    }
                }
                false
            }
            AcornType::Bool => false,
            AcornType::Any => false,
        }
    }

    // Whether this type is a template-instantation of the other type.
    // Includes the null instantiation where they are both a non-templated type.
    pub fn instantiates_from(&self, template_type: &AcornType) -> bool {
        if self == template_type {
            return true;
        }
        match (self, template_type) {
            (_, AcornType::Generic(_)) => true,
            (AcornType::Function(function_type), AcornType::Function(template_function_type)) => {
                if function_type.arg_types.len() != template_function_type.arg_types.len() {
                    return false;
                }
                for (arg_type, template_arg_type) in function_type
                    .arg_types
                    .iter()
                    .zip(&template_function_type.arg_types)
                {
                    if !arg_type.instantiates_from(template_arg_type) {
                        return false;
                    }
                }
                function_type
                    .return_type
                    .instantiates_from(&template_function_type.return_type)
            }
            (AcornType::ArgList(left_types), AcornType::ArgList(right_types)) => {
                if left_types.len() != right_types.len() {
                    return false;
                }
                for (left_type, right_type) in left_types.iter().zip(right_types) {
                    if !left_type.instantiates_from(right_type) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }

    // Create the type you get when you apply this type to the given type.
    // Panics if the application is invalid.
    // Does partial application.
    pub fn apply(&self, arg_type: &AcornType) -> AcornType {
        if let AcornType::Function(function_type) = self {
            assert_eq!(function_type.arg_types[0], *arg_type);
            if function_type.arg_types.len() == 1 {
                *function_type.return_type.clone()
            } else {
                let mut new_arg_types = function_type.arg_types.clone();
                new_arg_types.remove(0);
                AcornType::Function(FunctionType {
                    arg_types: new_arg_types,
                    return_type: function_type.return_type.clone(),
                })
            }
        } else {
            panic!("Can't apply {:?} to {:?}", self, arg_type);
        }
    }

    // A normalized type is something the theorem prover can use.
    pub fn is_normalized(&self) -> bool {
        match self {
            AcornType::Function(function_type) => {
                if function_type.arg_types.len() == 0 {
                    // A function type with no arguments, not normal
                    return false;
                }
                for arg_type in &function_type.arg_types {
                    if !arg_type.is_normalized() {
                        return false;
                    }
                }
                function_type.return_type.is_normalized()
            }
            AcornType::Bool => true,
            AcornType::Data(_) => true,
            AcornType::Generic(_) => {
                // Generic types should be instantiated before passing it to the prover
                false
            }
            AcornType::ArgList(_) => false,
            AcornType::Any => false,
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

    // Replace the generic types with a type from the list
    pub fn instantiate(&self, types: &[AcornType]) -> AcornType {
        match self {
            AcornType::Generic(index) => types[*index].clone(),
            AcornType::Function(function_type) => AcornType::Function(FunctionType {
                arg_types: function_type
                    .arg_types
                    .iter()
                    .map(|t| t.instantiate(types))
                    .collect(),
                return_type: Box::new(function_type.return_type.instantiate(types)),
            }),
            AcornType::ArgList(arg_types) => {
                AcornType::ArgList(arg_types.iter().map(|t| t.instantiate(types)).collect())
            }
            _ => self.clone(),
        }
    }
}

impl fmt::Display for AcornType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AcornType::Bool => write!(f, "bool"),
            AcornType::Data(index) => write!(f, "D{}", index),
            AcornType::Generic(index) => write!(f, "T{}", index),
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
            AcornType::Any => write!(f, "any"),
        }
    }
}
