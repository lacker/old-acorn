use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;

// An atomic value is one that we don't want to expand inline.
// We could add more things here, like defined constants.
// For now, we expand everything we can inline.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Atom {
    // Values defined like "define 0: Nat = axiom"
    Axiomatic(usize),

    // A Reference is a reference to a variable on the stack.
    // We drop the variable name. Instead we track the index on the stack of the binding.
    // This does mean that you must be careful when moving values between different stack environments.
    Reference(usize),

    // Functions created in the normalization process
    Skolem(usize),
}

impl Atom {
    pub fn is_axiomatic(&self) -> bool {
        match self {
            Atom::Axiomatic(_) => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TypedAtom {
    pub atom: Atom,
    pub acorn_type: AcornType,
}

impl fmt::Display for TypedAtom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.atom {
            Atom::Axiomatic(i) => write!(f, "a{}", i),
            Atom::Skolem(i) => write!(f, "s{}", i),
            Atom::Reference(i) => write!(f, "x{}", i),
        }
    }
}

impl TypedAtom {
    // Binds this atom if it matches one of the new stack values.
    // They start at the provided stack index.
    // Since stack references are stored by height on the stack, this will also change the
    // reference id if this is a reference to a subsequent stack value.
    pub fn bind_values(self, stack_index: usize, values: &Vec<AcornValue>) -> AcornValue {
        match self.atom {
            Atom::Reference(i) => {
                if i < stack_index {
                    // This reference is unchanged
                    return AcornValue::Atom(self);
                }
                if i < stack_index + values.len() {
                    // This reference is bound to a new value
                    return values[i - stack_index].clone();
                }
                // This reference just needs to be shifted
                AcornValue::Atom(TypedAtom {
                    atom: Atom::Reference(i - values.len()),
                    acorn_type: self.acorn_type,
                })
            }
            _ => AcornValue::Atom(self),
        }
    }

    pub fn insert_stack(self, index: usize, increment: usize) -> TypedAtom {
        match self.atom {
            Atom::Reference(i) => {
                if i < index {
                    // This reference is unchanged
                    return self;
                }
                // This reference just needs to be shifted
                TypedAtom {
                    atom: Atom::Reference(i + increment),
                    acorn_type: self.acorn_type,
                }
            }
            _ => self,
        }
    }

    pub fn is_axiomatic(&self) -> bool {
        self.atom.is_axiomatic()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atom_ordering() {
        assert!(Atom::Axiomatic(0) < Atom::Axiomatic(1));
    }
}
