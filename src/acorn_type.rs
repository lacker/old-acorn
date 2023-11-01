use std::{collections::HashMap, fmt};

use crate::namespace::NamespaceId;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct FunctionType {
    pub arg_types: Vec<AcornType>,
    pub return_type: Box<AcornType>,
}

impl fmt::Display for FunctionType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let lhs = if self.arg_types.len() == 1 {
            format!("{}", self.arg_types[0])
        } else {
            format!("({})", AcornType::types_to_str(&self.arg_types))
        };
        write!(f, "{} -> {}", lhs, self.return_type)
    }
}

// Every AcornValue has an AcornType.
// This is the "richer" form of a type. The environment uses these types; the prover uses ids.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub enum AcornType {
    // Nothing can ever be the empty type.
    Empty,

    // Booleans are special
    Bool,

    // Data types are structs or axiomatic types.
    // For their canonical representation, we track the namespace they were initially defined in.
    Data(NamespaceId, String),

    // Function types are defined by their inputs and output.
    Function(FunctionType),

    // Type parameters can be used inside polymorphic expressions.
    Parameter(String),

    // Usually before proving we monomorphize everything.
    // When we don't have a specific type to monomorphize to, we use a placeholder type.
    Placeholder(String),
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
            AcornType::Data(_, _) => self.clone(),
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
    pub fn refers_to(&self, namespace: NamespaceId, name: &str) -> bool {
        if self.equals_data_type(namespace, name) {
            return true;
        }
        match self {
            AcornType::Function(function_type) => {
                for arg_type in &function_type.arg_types {
                    if arg_type.refers_to(namespace, name) {
                        return true;
                    }
                }
                function_type.return_type.refers_to(namespace, name)
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
            AcornType::Data(_, _) => true,
            AcornType::Parameter(_) => {
                // Parametric types should be monomorphized before passing them the prover
                false
            }
            AcornType::Empty => true,
            AcornType::Placeholder(_) => true,
        }
    }

    pub fn equals_data_type(&self, data_type_namespace: NamespaceId, data_type_name: &str) -> bool {
        match self {
            AcornType::Data(namespace, name) => {
                *namespace == data_type_namespace && name == data_type_name
            }
            _ => false,
        }
    }

    pub fn types_to_str(types: &[AcornType]) -> String {
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

    // Replaces the type with the given namespace and name with a parameter of the same name.
    pub fn genericize(&self, data_type_namespace: NamespaceId, data_type_name: &str) -> AcornType {
        match self {
            AcornType::Function(function_type) => AcornType::Function(FunctionType {
                arg_types: function_type
                    .arg_types
                    .iter()
                    .map(|t| t.genericize(data_type_namespace, data_type_name))
                    .collect(),
                return_type: Box::new(
                    function_type
                        .return_type
                        .genericize(data_type_namespace, data_type_name),
                ),
            }),
            AcornType::Data(namespace, name) => {
                if *namespace == data_type_namespace && name == data_type_name {
                    AcornType::Parameter(name.to_string())
                } else {
                    self.clone()
                }
            }
            _ => self.clone(),
        }
    }

    pub fn monomorphize(&self, params: &[(String, AcornType)]) -> AcornType {
        match self {
            AcornType::Parameter(name) => {
                for (param_name, param_type) in params {
                    if name == param_name {
                        return param_type.clone();
                    }
                }
                panic!("couldn't find mapping for {} while monomorphizing", name);
            }
            AcornType::Function(function_type) => AcornType::Function(FunctionType {
                arg_types: function_type
                    .arg_types
                    .iter()
                    .map(|t| t.monomorphize(params))
                    .collect(),
                return_type: Box::new(function_type.return_type.monomorphize(params)),
            }),
            _ => self.clone(),
        }
    }

    // Tries to monomorphize self to get monomorph.
    // Fills in a mapping for any parametric types that need to be specified, in order to make it match.
    // Returns whether it was successful.
    pub fn match_monomorph(
        &self,
        monomorph: &AcornType,
        mapping: &mut HashMap<String, AcornType>,
    ) -> bool {
        if self == monomorph {
            return true;
        }

        match (self, monomorph) {
            (AcornType::Parameter(name), _) => {
                if let Some(t) = mapping.get(name) {
                    // This parametric type is already mapped
                    return t == monomorph;
                }
                mapping.insert(name.clone(), monomorph.clone());
                true
            }
            (AcornType::Function(f), AcornType::Function(g)) => {
                if f.arg_types.len() != g.arg_types.len() {
                    return false;
                }
                if !f.return_type.match_monomorph(&g.return_type, mapping) {
                    return false;
                }
                for (f_arg_type, g_arg_type) in f.arg_types.iter().zip(&g.arg_types) {
                    if !f_arg_type.match_monomorph(g_arg_type, mapping) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }

    // A type is parametric if any of its components are typed with type parameters.
    pub fn is_parametric(&self) -> bool {
        match self {
            AcornType::Bool
            | AcornType::Data(_, _)
            | AcornType::Empty
            | AcornType::Placeholder(_) => false,
            AcornType::Parameter(_) => true,
            AcornType::Function(ftype) => {
                for arg_type in &ftype.arg_types {
                    if arg_type.is_parametric() {
                        return true;
                    }
                }
                ftype.return_type.is_parametric()
            }
        }
    }

    // Converts type parameters to placeholder types
    pub fn to_placeholder(&self) -> AcornType {
        match self {
            AcornType::Parameter(name) => AcornType::Placeholder(name.to_string()),
            AcornType::Function(ftype) => AcornType::Function(FunctionType {
                arg_types: ftype.arg_types.iter().map(|t| t.to_placeholder()).collect(),
                return_type: Box::new(ftype.return_type.to_placeholder()),
            }),
            _ => self.clone(),
        }
    }
}

impl fmt::Display for AcornType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AcornType::Bool => write!(f, "bool"),
            AcornType::Data(_, name) => write!(f, "{}", name),
            AcornType::Parameter(name) => write!(f, "{}", name),
            AcornType::Function(function_type) => write!(f, "{}", function_type),
            AcornType::Empty => write!(f, "empty"),
            AcornType::Placeholder(name) => write!(f, "{}", name),
        }
    }
}
