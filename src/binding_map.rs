use std::collections::HashMap;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::atom::AtomId;

// In order to convert an Expression to an AcornValue, we need to convert the string representation
// of types, variable names, and constant names into numeric identifiers, detect name collisions,
// and typecheck everything.
// The BindingMap handles this. It does not handle Statements, just Expressions.
// It does not have to be efficient enough to run in the inner loop of the prover.
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
    pub value: AcornValue,
}
