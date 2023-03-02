use crate::acorn_type::{AcornType, FunctionType};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FunctionApplication {
    pub function: Box<AcornValue>,
    pub args: Vec<AcornValue>,
}

// An atomic value is one that we don't want to expand inline.
// We could add more things here, like defined constants.
// For now, we expand everything we can inline.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Atom {
    // Values defined like "define 0: Nat = axiom"
    Axiomatic(usize),

    // Functions created in the normalization process
    Skolem(usize),

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
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TypedAtom {
    pub atom: Atom,
    pub acorn_type: AcornType,
}

// Two AcornValue compare to equal if they are structurally identical.
// Comparison doesn't do any evaluations.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AcornValue {
    // An atomic value could be an axiom.
    // It could be a defined value that we don't want to expand inline.
    // It could be a function produced by skolemization.
    // Basically anything that isn't composed of smaller parts.
    Atom(TypedAtom),

    Application(FunctionApplication),
    ArgList(Vec<AcornValue>),

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

    pub fn get_type(&self) -> AcornType {
        match self {
            AcornValue::Atom(t) => t.acorn_type.clone(),
            AcornValue::Application(t) => t.function.get_type(),
            AcornValue::ArgList(t) => {
                AcornType::ArgList(t.into_iter().map(|x| x.get_type()).collect())
            }
            AcornValue::Lambda(args, return_value) => AcornType::Function(FunctionType {
                args: args.clone(),
                return_type: Box::new(return_value.get_type()),
            }),
            AcornValue::Implies(_, _) => AcornType::Bool,
            AcornValue::Equals(_, _) => AcornType::Bool,
            AcornValue::NotEquals(_, _) => AcornType::Bool,
            AcornValue::And(_, _) => AcornType::Bool,
            AcornValue::Or(_, _) => AcornType::Bool,
            AcornValue::ForAll(_, _) => AcornType::Bool,
            AcornValue::Exists(_, _) => AcornType::Bool,
            AcornValue::Not(_) => AcornType::Bool,
            AcornValue::ForAllMacro => AcornType::Macro,
            AcornValue::ExistsMacro => AcornType::Macro,
        }
    }
}

// If args is not empty, then atom should be treated as a function.
// Otherwise, the term is just the atom.
pub struct Term {
    pub atom: TypedAtom,
    pub args: Vec<Term>,
}

// Literals are always boolean-valued.
pub enum Literal {
    Positive(Term),
    Negative(Term),
    Equals(Term, Term),
    NotEquals(Term, Term),
}

// A clause is a disjunction of literals, universally quantified over some variables.
// We include the types of the universal variables it is quantified over.
// It cannot contain existential quantifiers.
pub struct Clause {
    pub universal: Vec<AcornType>,
    pub literals: Vec<Literal>,
}
