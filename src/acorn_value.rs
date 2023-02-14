#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FunctionApplication {
    pub function: Box<AcornValue>,
    pub args: Vec<AcornValue>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AcornValue {
    Axiomatic(usize),
    Function(FunctionApplication),
    ArgList(Vec<AcornValue>),
}

impl AcornValue {
    pub fn into_arg_list(self) -> Vec<AcornValue> {
        match self {
            AcornValue::ArgList(t) => t,
            _ => vec![self],
        }
    }
}
