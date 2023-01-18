use std::fmt;

pub struct AcornFunctionType {
    args: Vec<AcornType>,
    value: Box<AcornType>,
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

pub enum AcornType {
    Bool,
    Nat,
    Int,
    Function(AcornFunctionType),
}

impl fmt::Display for AcornType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AcornType::Bool => write!(f, "bool"),
            AcornType::Nat => write!(f, "nat"),
            AcornType::Int => write!(f, "int"),
            AcornType::Function(t) => write!(f, "{}", t),
        }
    }
}
