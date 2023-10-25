use std::cmp::Ordering;
use std::fmt;

pub type AtomId = u16;

pub const INVALID_ATOM_ID: AtomId = 0xffff;

// An atomic value does not have any internal structure.
// The Atom is a lower-level representation.
// It is used in the prover, but not in the AcornValue / Environment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Atom {
    True,

    // Constant values that are user-visible.
    // These could be axioms, imported things, named functions, named variables.
    // Not types, types are their own thing.
    Constant(AtomId),

    // Monomorphizations of polymorphic functions.
    Monomorph(AtomId),

    // Functions created by the synthesizer
    Synthetic(AtomId),

    // A Variable can be a reference to a variable on the stack, or its meaning can be implicit,
    // depending on the context.
    // We drop the variable name. Instead we track an id.
    // This does mean that you must be careful when moving values between different environments.
    Variable(AtomId),
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Atom::True => write!(f, "true"),
            Atom::Constant(i) => write!(f, "c{}", i),
            Atom::Monomorph(i) => write!(f, "m{}", i),
            Atom::Synthetic(i) => write!(f, "p{}", i),
            Atom::Variable(i) => write!(f, "x{}", i),
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
            'p' => Some(Atom::Synthetic(rest.parse().unwrap())),
            'x' => Some(Atom::Variable(rest.parse().unwrap())),
            _ => None,
        }
    }

    pub fn is_constant(&self) -> bool {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atom_ordering() {
        assert!(Atom::True < Atom::Constant(0));
        assert!(Atom::Constant(0) < Atom::Constant(1));
    }

    #[test]
    fn test_atom_stable_partial_ordering() {
        assert_eq!(
            Atom::Constant(0).stable_partial_order(&Atom::Constant(1)),
            Ordering::Less
        );
        assert_eq!(
            Atom::Variable(0).stable_partial_order(&Atom::Variable(1)),
            Ordering::Equal
        );
    }
}
