use std::collections::HashMap;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::atom::{Atom, AtomId, TypedAtom};
use crate::token::{Error, Result, Token};

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

    ////////////////////////////////////////////////////////////////////////////////
    // Simple helper functions.
    ////////////////////////////////////////////////////////////////////////////////

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

    // This creates an atomic value for the next constant, but does not bind it to any name.
    pub fn next_constant_atom(&self, acorn_type: &AcornType) -> AcornValue {
        let atom = Atom::Constant(self.constant_names.len() as AtomId);
        AcornValue::Atom(TypedAtom {
            atom,
            acorn_type: acorn_type.clone(),
        })
    }

    // Returns the defined value, if there is a defined value.
    // If there isn't, returns None.
    pub fn get_definition(&self, name: &str) -> Option<&AcornValue> {
        let info = self.constants.get(name)?;
        // TODO: avoid needing this weird clause, once ConstantInfo is simplified
        if let AcornValue::Atom(ta) = &info.value {
            if let Atom::Constant(i) = ta.atom {
                if i == info.id {
                    return None;
                }
            }
        }
        Some(&info.value)
    }

    pub fn get_definition_for_id(&self, id: AtomId) -> Option<&AcornValue> {
        let name = &self.constant_names[id as usize];
        self.get_definition(name)
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for parsing Expressions and similar structures
    ////////////////////////////////////////////////////////////////////////////////

    // Return an error if the types don't match.
    // This doesn't do full polymorphic typechecking, but it will fail if there's no
    // way that the types can match, for example if a function expects T -> Nat and
    // the value provided is Nat.
    // actual_type should be non-generic here.
    // expected_type can be generic.
    pub fn check_type<'a>(
        &self,
        error_token: &Token,
        expected_type: Option<&AcornType>,
        actual_type: &AcornType,
    ) -> Result<()> {
        if let Some(e) = expected_type {
            if e != actual_type {
                return Err(Error::new(
                    error_token,
                    &format!(
                        "expected type {}, but got {}",
                        self.type_str(e),
                        self.type_str(actual_type)
                    ),
                ));
            }
        }
        Ok(())
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for converting things to displayable strings.
    ////////////////////////////////////////////////////////////////////////////////

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

    pub fn atom_str(&self, atom: &Atom) -> String {
        match atom {
            Atom::True => "true".to_string(),
            Atom::Constant(i) => {
                if *i as usize >= self.constant_names.len() {
                    panic!(
                        "atom is c{} but we have only {} constants",
                        i,
                        self.constant_names.len()
                    );
                }
                self.constant_names[*i as usize].to_string()
            }
            Atom::Skolem(i) => format!("s{}", i),
            Atom::Monomorph(i) => format!("m{}", i),
            Atom::Synthetic(i) => format!("p{}", i),
            Atom::Variable(i) => format!("x{}", i),
        }
    }

    pub fn monomorph_str(&self, constant_id: AtomId, types: &[AcornType]) -> String {
        format!(
            "{}<{}>",
            self.constant_names[constant_id as usize],
            self.type_list_str(types)
        )
    }

    fn macro_str_stacked(
        &self,
        macro_name: &str,
        types: &Vec<AcornType>,
        value: &AcornValue,
        stack_size: usize,
    ) -> String {
        let parts: Vec<_> = types
            .iter()
            .enumerate()
            .map(|(i, t)| format!("x{}: {}", i + stack_size, self.type_str(t)))
            .collect();
        let value_str = self.value_str_stacked(value, stack_size + types.len());
        format!("{}({}) {{ {} }}", macro_name, parts.join(", "), value_str)
    }

    fn value_str_stacked(&self, value: &AcornValue, stack_size: usize) -> String {
        match value {
            AcornValue::Atom(a) => self.atom_str(&a.atom),
            AcornValue::Application(app) => {
                let fn_name = self.value_str_stacked(&app.function, stack_size);
                let args: Vec<_> = app
                    .args
                    .iter()
                    .map(|a| self.value_str_stacked(a, stack_size))
                    .collect();
                format!("{}({})", fn_name, args.join(", "))
            }
            AcornValue::Implies(left, right) => format!(
                "({} -> {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::Equals(left, right) => format!(
                "({} = {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::NotEquals(left, right) => format!(
                "({} != {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::And(left, right) => format!(
                "({} & {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::Or(left, right) => format!(
                "({} | {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::ForAll(types, values) => {
                self.macro_str_stacked("forall", types, values, stack_size)
            }
            AcornValue::Exists(types, values) => {
                self.macro_str_stacked("exists", types, values, stack_size)
            }
            AcornValue::Not(subvalue) => {
                format!("!{}", self.value_str_stacked(subvalue, stack_size))
            }
            AcornValue::Lambda(types, values) => {
                self.macro_str_stacked("lambda", types, values, stack_size)
            }
            AcornValue::Monomorph(c, _, types) => self.monomorph_str(*c, types),
        }
    }

    pub fn value_str(&self, value: &AcornValue) -> String {
        self.value_str_stacked(value, 0)
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for testing.
    ////////////////////////////////////////////////////////////////////////////////

    // Check that the given name actually does have this type in the environment.
    pub fn expect_type(&self, name: &str, type_string: &str) {
        let env_type = match self.identifier_types.get(name) {
            Some(t) => t,
            None => panic!("{} not found", name),
        };
        assert_eq!(self.type_str(env_type), type_string);
    }

    // Checks that the given constant id matches the given name
    pub fn expect_constant(&mut self, id: usize, name: &str) {
        let constant = match self.constant_names.get(id) {
            Some(c) => c,
            None => panic!("constant {} not found", id),
        };
        assert_eq!(constant, name);
        let info = match self.constants.get(name) {
            Some(info) => info,
            None => panic!(
                "inconsistency: c{} evalutes to {}, for which we have no info",
                id, name
            ),
        };
        assert_eq!(info.id, id as AtomId);
    }
}
