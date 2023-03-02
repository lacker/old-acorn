#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FunctionType {
    pub args: Vec<AcornType>,
    pub return_type: Box<AcornType>,
}

// An argument list isn't really a type, but it's part of a type.
// It's used when we have more than one argument to a function.
// "Macro" indicates either "forall" or "exists".
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AcornType {
    Bool,
    Axiomatic(usize),
    Function(FunctionType),
    ArgList(Vec<AcornType>),
    Macro,
}

impl AcornType {
    pub fn into_vec(self) -> Vec<AcornType> {
        match self {
            AcornType::ArgList(t) => t,
            _ => vec![self],
        }
    }

    pub fn into_arg_list(self) -> AcornType {
        AcornType::ArgList(self.into_vec())
    }
}
