use std::fmt;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct AcornFunctionType {
    pub args: Vec<AcornType>,
    pub value: Box<AcornType>,
}

impl fmt::Display for AcornFunctionType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let parens = self.args.len() > 1;
        if parens {
            write!(f, "(")?;
        }
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        if parens {
            write!(f, ")")?;
        }
        write!(f, " -> {}", self.value)
    }
}

// An argument list isn't really a type, but it's part of a type.
// It's used when we have more than one argument to a function.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AcornType {
    Bool,
    Axiomatic(usize),
    Function(AcornFunctionType),
    ArgList(Vec<AcornType>),
}

impl fmt::Display for AcornType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AcornType::Bool => write!(f, "bool"),
            AcornType::Axiomatic(_) => write!(f, "axiom"),
            AcornType::Function(t) => write!(f, "{}", t),
            AcornType::ArgList(t) => {
                write!(f, "(")?;
                for (i, item) in t.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl AcornType {
    pub fn into_arg_list(self) -> Vec<AcornType> {
        match self {
            AcornType::ArgList(t) => t,
            _ => vec![self],
        }
    }
}
