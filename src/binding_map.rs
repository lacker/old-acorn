use std::collections::HashMap;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::atom::{Atom, AtomId, TypedAtom};

// In order to convert an Expression to an AcornValue, we need to convert the string representation
// of types, variable names, and constant names into numeric identifiers, detect name collisions,
// and typecheck everything.
// The BindingMap handles this. It does not handle Statements, just Expressions.
// It does not have to be efficient enough to run in the inner loop of the prover.
#[derive(Clone)]
pub struct BindingMap {
    // data_types[i] is the name of AcornType::Data(i).
    pub data_types: Vec<String>,

    // Maps the name of a type to the type object.
    pub type_names: HashMap<String, AcornType>,

    // Maps an identifier name to its type.
    pub identifier_types: HashMap<String, AcornType>,

    // Maps the name of a constant to information about it.
    // Doesn't handle variables defined on the stack, only ones that will be in scope for the
    // entirety of this environment.
    pub constants: HashMap<String, ConstantInfo>,

    // Reverse lookup for the information in constants.
    // constant_names[i] is the name of Atom::Constant(i).
    // constants[constant_names[i]] = (i, _)
    pub constant_names: Vec<String>,

    // For variables defined on the stack, we keep track of their depth from the top.
    pub stack: HashMap<String, AtomId>,
}

#[derive(Clone)]
pub struct ConstantInfo {
    // The id of this constant, used for constructing its atom or for the index in constant_names.
    pub id: AtomId,

    // The definition of this constant.
    // If it doesn't have a definition, this is just an atomic constant.
    // TODO: simplify. should be called "definition"
    pub value: AcornValue,
}

impl BindingMap {
    pub fn new() -> Self {
        BindingMap {
            data_types: Vec::new(),
            constant_names: Vec::new(),
            type_names: HashMap::from([("bool".to_string(), AcornType::Bool)]),
            identifier_types: HashMap::new(),
            constants: HashMap::new(),
            stack: HashMap::new(),
        }
    }

    // The names of all the stack variables, in order.
    pub fn stack_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = vec![""; self.stack.len()];
        for (name, i) in &self.stack {
            names[*i as usize] = name;
        }
        names
    }

    // Adds a new data type to the binding map.
    // Panics if the name is already a typename. (TODO)
    pub fn add_data_type(&mut self, name: &str) -> AcornType {
        let data_type = AcornType::Data(self.data_types.len());
        self.data_types.push(name.to_string());
        if let Some(_) = self.type_names.insert(name.to_string(), data_type.clone()) {
            panic!("type name {} already exists", name);
        }
        data_type
    }

    // Returns an AcornValue::Atom representing this name, if there is one.
    // Returns None if this name does not refer to a constant.
    pub fn get_constant_atom(&self, name: &str) -> Option<AcornValue> {
        let info = self.constants.get(name)?;
        Some(AcornValue::Atom(TypedAtom {
            atom: Atom::Constant(info.id),
            acorn_type: self.identifier_types[name].clone(),
        }))
    }

    // Returns the defined value, if there is a defined value.
    // If there isn't, returns None.
    pub fn get_definition(&self, name: &str) -> Option<AcornValue> {
        let info = self.constants.get(name)?;
        // TODO: avoid needing this weird clause, once ConstantInfo is simplified
        if let AcornValue::Atom(ta) = &info.value {
            if let Atom::Constant(i) = ta.atom {
                if i == info.id {
                    return None;
                }
            }
        }
        Some(info.value.clone())
    }

    pub fn type_list_str(&self, types: &[AcornType]) -> String {
        let mut s = "".to_string();
        for (i, acorn_type) in types.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            s.push_str(&self.type_str(acorn_type));
        }
        s
    }

    pub fn type_str(&self, acorn_type: &AcornType) -> String {
        match acorn_type {
            AcornType::Bool => "bool".to_string(),
            AcornType::Data(i) => {
                if i >= &self.data_types.len() {
                    panic!("AcornType::Data({}) is invalid in this scope", i);
                }
                self.data_types[*i].to_string()
            }
            AcornType::Generic(i) => {
                // This return value doesn't mean anything, but it's useful for debugging.
                format!("T{}", i)
            }
            AcornType::Function(function_type) => {
                let ret = self.type_str(&function_type.return_type);
                if function_type.arg_types.len() > 1 {
                    format!(
                        "({}) -> {}",
                        self.type_list_str(&function_type.arg_types),
                        ret
                    )
                } else {
                    format!("{} -> {}", self.type_str(&function_type.arg_types[0]), ret)
                }
            }
            AcornType::Any => "any".to_string(),
        }
    }

    // Check that the given name actually does have this type in the environment.
    pub fn expect_type(&self, name: &str, type_string: &str) {
        let env_type = match self.identifier_types.get(name) {
            Some(t) => t,
            None => panic!("{} not found", name),
        };
        assert_eq!(self.type_str(env_type), type_string);
    }
}
