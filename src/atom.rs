use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::namespace::NamespaceId;
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
    //
    // The first_binding_index is the first index that we should bind to.
    // For example, if stack_index is 2, and the values
    // are "foo", "bar", and "baz" we should set x2 = foo, x3 = bar, x4 = baz.
    // Any subsequent variables, x5 x6 x7 etc, should be renumbered downwards.
    //
    // The stack_size is the size of the stack where this atom occurs. This is relevant because any
    // variables in the bound values will be moved into this environment, so we need to renumber
    // their variables appropriately.
    pub fn bind_values(
        self,
        first_binding_index: AtomId,
        stack_size: AtomId,
        values: &Vec<AcornValue>,
    ) -> AcornValue {
        match self.atom {
            Atom::Variable(i) => {
                if i < first_binding_index {
                    // This reference is unchanged
                    return AcornValue::Atom(self);
                }
                if i < first_binding_index + values.len() as AtomId {
                    // This reference is bound to a new value
                    let new_value = values[(i - first_binding_index) as usize].clone();

                    // We are moving this value between contexts with possibly different stack sizes
                    assert!(stack_size >= first_binding_index);
                    return new_value
                        .insert_stack(first_binding_index, stack_size - first_binding_index);
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

    pub fn is_constant(&self) -> bool {
        self.atom.is_constant()
    }

    pub fn find_constants_gte(&self, index: AtomId, answer: &mut Vec<(AtomId, AcornType)>) {
        match self.atom {
            Atom::Constant(c) => {
                if c >= index {
                    // Insert tuple into answer, sorted by index
                    let tuple = (c, self.acorn_type.clone());
                    if let Err(pos) = answer.binary_search(&tuple) {
                        answer.insert(pos, tuple);
                    };
                }
            }
            _ => {}
        }
    }

    pub fn genericize(
        &self,
        data_type_namespace: NamespaceId,
        data_type_name: &str,
        generic_type: usize,
    ) -> TypedAtom {
        TypedAtom {
            atom: self.atom.clone(),
            acorn_type: self.acorn_type.genericize(
                data_type_namespace,
                data_type_name,
                generic_type,
            ),
        }
    }

    pub fn monomorphize(&self, types: &[AcornType]) -> TypedAtom {
        TypedAtom {
            atom: self.atom.clone(),
            acorn_type: self.acorn_type.monomorphize(types),
        }
    }

    // Converts all the parametrized types to placeholder types
    pub fn to_placeholder(&self) -> TypedAtom {
        TypedAtom {
            atom: self.atom.clone(),
            acorn_type: self.acorn_type.to_placeholder(),
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
