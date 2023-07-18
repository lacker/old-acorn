use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use std::cmp::Ordering;
use std::fmt;

pub type AtomId = u16;

pub const MIN_ATOM: Atom = Atom::Constant(0);

// An atomic value does not have any internal structure.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Atom {
    True,

    // Constant values that are user-visible.
    // These could be axioms, imported things, named functions, named variables.
    // Not types, types are their own thing.
    Constant(AtomId),

    // Functions created in the normalization process
    Skolem(AtomId),

    // Functions created by the synthesizer
    Synthetic(AtomId),

    // A Variable can be a reference to a variable on the stack, or its meaning can be implicit,
    // depending on the context.
    // We drop the variable name. Instead we track an id.
    // This does mean that you must be careful when moving values between different environments.
    Variable(AtomId),

    // A variable with no name. Not useful in most contexts.
    Anonymous,
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Atom::True => write!(f, "true"),
            Atom::Constant(i) => write!(f, "c{}", i),
            Atom::Skolem(i) => write!(f, "s{}", i),
            Atom::Synthetic(i) => write!(f, "p{}", i),
            Atom::Variable(i) => write!(f, "x{}", i),
            Atom::Anonymous => write!(f, "_"),
        }
    }
}

impl Atom {
    pub fn new(s: &str) -> Atom {
        Atom::parse(s).unwrap()
    }

    pub fn parse(s: &str) -> Option<Atom> {
        let mut chars = s.trim().chars();
        let first = chars.next()?;
        let rest = chars.as_str();
        match first {
            'c' => Some(Atom::Constant(rest.parse().unwrap())),
            'a' => Some(Atom::Constant(rest.parse().unwrap())), // backward compatibility
            's' => Some(Atom::Skolem(rest.parse().unwrap())),
            'p' => Some(Atom::Synthetic(rest.parse().unwrap())),
            'x' => Some(Atom::Variable(rest.parse().unwrap())),
            _ => None,
        }
    }

    pub fn is_axiomatic(&self) -> bool {
        match self {
            Atom::Constant(_) => true,
            _ => false,
        }
    }

    pub fn is_variable(&self) -> bool {
        match self {
            Atom::Variable(_) => true,
            _ => false,
        }
    }

    pub fn is_skolem(&self) -> bool {
        match self {
            Atom::Skolem(_) => true,
            _ => false,
        }
    }

    pub fn shift_variables(self, shift: u16) -> Atom {
        match self {
            Atom::Variable(i) => Atom::Variable(i + shift),
            _ => self,
        }
    }

    // Orders two atoms, but considers all references the same, so that the ordering
    // is stable under variable renaming.
    pub fn stable_partial_order(&self, other: &Atom) -> Ordering {
        match (self, other) {
            (Atom::Variable(_), Atom::Variable(_)) => Ordering::Equal,
            (x, y) => x.cmp(y),
        }
    }

    // Replaces x_i with x_{var_map[i]}.
    pub fn remap_variables(&self, var_map: &Vec<AtomId>) -> Atom {
        match self {
            Atom::Variable(i) => Atom::Variable(var_map[*i as usize]),
            a => *a,
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
        self.atom.fmt(f)
    }
}

impl TypedAtom {
    // Binds this atom if it matches one of the new stack values.
    // They start at the provided stack index.
    // Since stack references are stored by height on the stack, this will also change the
    // reference id if this is a reference to a subsequent stack value.
    pub fn bind_values(self, stack_index: AtomId, values: &Vec<AcornValue>) -> AcornValue {
        match self.atom {
            Atom::Variable(i) => {
                if i < stack_index {
                    // This reference is unchanged
                    return AcornValue::Atom(self);
                }
                if i < stack_index + values.len() as AtomId {
                    // This reference is bound to a new value
                    return values[(i - stack_index) as usize].clone();
                }
                // This reference just needs to be shifted
                AcornValue::Atom(TypedAtom {
                    atom: Atom::Variable(i - values.len() as AtomId),
                    acorn_type: self.acorn_type,
                })
            }
            _ => AcornValue::Atom(self),
        }
    }

    pub fn insert_stack(self, index: AtomId, increment: AtomId) -> TypedAtom {
        match self.atom {
            Atom::Variable(i) => {
                if i < index {
                    // This reference is unchanged
                    return self;
                }
                // This reference just needs to be shifted
                TypedAtom {
                    atom: Atom::Variable(i + increment),
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
        assert!(Atom::Constant(0) < Atom::Constant(1));
        assert!(Atom::Constant(1) < Atom::Skolem(0));
        assert!(Atom::Skolem(1) < Atom::Variable(0));

        assert!(MIN_ATOM <= Atom::Constant(0));
        assert!(MIN_ATOM <= Atom::Skolem(0));
        assert!(MIN_ATOM <= Atom::Variable(0));
    }

    #[test]
    fn test_atom_stable_partial_ordering() {
        assert_eq!(
            Atom::Constant(0).stable_partial_order(&Atom::Constant(1)),
            Ordering::Less
        );
        assert_eq!(
            Atom::Constant(1).stable_partial_order(&Atom::Skolem(0)),
            Ordering::Less
        );
        assert_eq!(
            Atom::Skolem(1).stable_partial_order(&Atom::Variable(0)),
            Ordering::Less
        );
        assert_eq!(
            Atom::Variable(0).stable_partial_order(&Atom::Variable(1)),
            Ordering::Equal
        );
    }
}
