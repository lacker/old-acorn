use std::{collections::HashMap, fmt};

use crate::module::ModuleId;

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

impl FunctionType {
    fn new(arg_types: Vec<AcornType>, return_type: AcornType) -> FunctionType {
        assert!(arg_types.len() > 0);
        if let AcornType::Function(ftype) = return_type {
            // Normalize function types by un-currying.
            let combined_args = arg_types
                .into_iter()
                .chain(ftype.arg_types.into_iter())
                .collect();
            FunctionType {
                arg_types: combined_args,
                return_type: ftype.return_type,
            }
        } else {
            FunctionType {
                arg_types,
                return_type: Box::new(return_type),
            }
        }
    }

    fn new_partial(&self, remove_args: usize) -> FunctionType {
        assert!(remove_args < self.arg_types.len());
        FunctionType {
            arg_types: self.arg_types[remove_args..].to_vec(),
            return_type: self.return_type.clone(),
        }
    }

    // The type after applying this function to a certain number of arguments.
    // Panics if the application is invalid.
    pub fn applied_type(&self, num_args: usize) -> AcornType {
        if num_args > self.arg_types.len() {
            panic!(
                "Can't apply function type {:?} taking {} args to {} args",
                self,
                self.arg_types.len(),
                num_args
            );
        }
        if num_args == self.arg_types.len() {
            *self.return_type.clone()
        } else {
            AcornType::Function(self.new_partial(num_args))
        }
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
    // For their canonical representation, we track the module they were initially defined in.
    Data(ModuleId, String),

    // Function types are defined by their inputs and output.
    Function(FunctionType),

    // Type parameters can be used inside polymorphic expressions.
    Parameter(String),

    // Usually before proving we monomorphize everything.
    // When we don't have a specific type to monomorphize to, we use a placeholder type.
    Placeholder(String),
}

impl AcornType {
    // Create the type, in non-curried form, for a function with the given arguments and return type.
    // arg_types can be empty.
    pub fn new_functional(arg_types: Vec<AcornType>, return_type: AcornType) -> AcornType {
        if arg_types.is_empty() {
            return_type
        } else {
            AcornType::Function(FunctionType::new(arg_types, return_type))
        }
    }

    // Whether this type refers to the other type.
    // For example, (Nat, Int) -> Rat refers to all of Nat, Int, and Rat.
    pub fn refers_to(&self, module_id: ModuleId, name: &str) -> bool {
        if self.equals_data_type(module_id, name) {
            return true;
        }
        match self {
            AcornType::Function(function_type) => {
                for arg_type in &function_type.arg_types {
                    if arg_type.refers_to(module_id, name) {
                        return true;
                    }
                }
                function_type.return_type.refers_to(module_id, name)
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
            function_type.applied_type(1)
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
                if function_type.return_type.is_functional() {
                    // A function type with a function return type, not normal
                    return false;
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

    pub fn equals_data_type(&self, data_type_module_id: ModuleId, data_type_name: &str) -> bool {
        match self {
            AcornType::Data(module_id, name) => {
                *module_id == data_type_module_id && name == data_type_name
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

    // parametrize should only be called on concrete types.
    // It replaces every data type with the given module and name with a type parameter.
    pub fn parametrize(&self, module_id: ModuleId, type_names: &[String]) -> AcornType {
        match self {
            AcornType::Function(function_type) => AcornType::new_functional(
                function_type
                    .arg_types
                    .iter()
                    .map(|t| t.parametrize(module_id, type_names))
                    .collect(),
                function_type.return_type.parametrize(module_id, type_names),
            ),
            AcornType::Data(ns, name) => {
                if *ns == module_id && type_names.contains(name) {
                    AcornType::Parameter(name.clone())
                } else {
                    self.clone()
                }
            }
            _ => self.clone(),
        }
    }

    // Replaces type parameters in the provided list with the corresponding type.
    pub fn specialize(&self, params: &[(String, AcornType)]) -> AcornType {
        match self {
            AcornType::Parameter(name) => {
                for (param_name, param_type) in params {
                    if name == param_name {
                        return param_type.clone();
                    }
                }
                self.clone()
            }
            AcornType::Function(function_type) => AcornType::new_functional(
                function_type
                    .arg_types
                    .iter()
                    .map(|t| t.specialize(params))
                    .collect(),
                function_type.return_type.specialize(params),
            ),
            _ => self.clone(),
        }
    }

    // Figures out whether it is possible to specialize self to get specialized.
    // Fills in a mapping for any parametric types that need to be specified, in order to make it match.
    // This will include "Foo" -> Parameter("Foo") mappings for types that should remain the same.
    // Every parameter used in self will get a mapping entry.
    // Returns whether it was successful.
    pub fn match_specialized(
        &self,
        specialized: &AcornType,
        mapping: &mut HashMap<String, AcornType>,
    ) -> bool {
        match (self, specialized) {
            (AcornType::Parameter(name), _) => {
                if let Some(t) = mapping.get(name) {
                    // This parametric type is already mapped
                    return t == specialized;
                }
                mapping.insert(name.clone(), specialized.clone());
                true
            }
            (AcornType::Function(f), AcornType::Function(g)) => {
                if f.arg_types.len() != g.arg_types.len() {
                    return false;
                }
                if !f.return_type.match_specialized(&g.return_type, mapping) {
                    return false;
                }
                for (f_arg_type, g_arg_type) in f.arg_types.iter().zip(&g.arg_types) {
                    if !f_arg_type.match_specialized(g_arg_type, mapping) {
                        return false;
                    }
                }
                true
            }
            _ => self == specialized,
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
            AcornType::Function(ftype) => AcornType::new_functional(
                ftype.arg_types.iter().map(|t| t.to_placeholder()).collect(),
                ftype.return_type.to_placeholder(),
            ),
            _ => self.clone(),
        }
    }

    pub fn is_functional(&self) -> bool {
        match self {
            AcornType::Function(_) => true,
            _ => false,
        }
    }
}

impl fmt::Display for AcornType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AcornType::Bool => write!(f, "Bool"),
            AcornType::Data(_, name) => write!(f, "{}", name),
            AcornType::Parameter(name) => write!(f, "{}", name),
            AcornType::Function(function_type) => write!(f, "{}", function_type),
            AcornType::Empty => write!(f, "empty"),
            AcornType::Placeholder(name) => write!(f, "{}", name),
        }
    }
}
