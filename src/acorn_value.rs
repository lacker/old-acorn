use crate::acorn_type::AcornType;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FunctionApplication {
    pub function: Box<AcornValue>,
    pub args: Vec<AcornValue>,
}

// Two AcornValue compare to equal if they are structurally identical.
// Comparison doesn't do any evaluations.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AcornValue {
    // An atomic value could be an axiom.
    // It could be a defined value that we don't want to expand inline.
    // It could be a function produced by skolemization.
    // Basically anything that isn't composed of smaller parts.
    Atomic(usize),

    Application(FunctionApplication),
    ArgList(Vec<AcornValue>),

    // A Reference is a reference to a variable on the stack.
    // We drop the variable name. Instead we track the "depth" of the binding.
    // Although we store arg lists as a vector, we consider the leftmost parts to be "higher up" in
    // the syntax tree.
    // So in the expression:
    // define foo(x: bool, y: bool) -> bool = bar(x, y)
    // In bar(x, y), the binding for x is at depth 1, and the binding for y is at depth 0.
    // We do this counting-backwards thing so that we can clone an AcornValue to use it in other
    // values without having to account for different stacks.
    Reference(usize),

    // A function definition that introduces a certain number of variables onto the stack.
    Lambda(Vec<AcornType>, Box<AcornValue>),

    // Some functions are hardcoded because we want to treat them specially during inference.
    Implies(Box<AcornValue>, Box<AcornValue>),
    Equals(Box<AcornValue>, Box<AcornValue>),
    NotEquals(Box<AcornValue>, Box<AcornValue>),
    And(Box<AcornValue>, Box<AcornValue>),
    Or(Box<AcornValue>, Box<AcornValue>),
    ForAll(Vec<AcornType>, Box<AcornValue>),
    Exists(Vec<AcornType>, Box<AcornValue>),
    Not(Box<AcornValue>),

    // The unbound macros themselves
    ForAllMacro,
    ExistsMacro,
}

impl AcornValue {
    pub fn into_vec(self) -> Vec<AcornValue> {
        match self {
            AcornValue::ArgList(t) => t,
            _ => vec![self],
        }
    }
}
