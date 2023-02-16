#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FunctionApplication {
    pub function: Box<AcornValue>,
    pub args: Vec<AcornValue>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AcornValue {
    Axiomatic(usize),
    Application(FunctionApplication),
    ArgList(Vec<AcornValue>),

    // Bindings drop the variable name. Instead we track the "depth" of the binding.
    // Although we store arg lists as a vector, we consider the leftmost parts to be "higher up" in
    // the syntax tree.
    // So in the expression:
    // define foo(x: bool, y: bool) -> bool = bar(x, y)
    // In bar(x, y), the binding for x is at depth 1, and the binding for y is at depth 0.
    // We do this counting-backwards thing so that we can clone an AcornValue to use it in other values
    // without having to account for different stacks.
    Binding(usize),

    // A function definition that introduces a certain number of variables onto the stack.
    Lambda(usize, Box<AcornValue>),
}

impl AcornValue {
    pub fn into_arg_list(self) -> Vec<AcornValue> {
        match self {
            AcornValue::ArgList(t) => t,
            _ => vec![self],
        }
    }
}
