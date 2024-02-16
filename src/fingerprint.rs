use std::collections::BTreeMap;

use crate::atom::Atom;
use crate::term::Term;
use crate::type_map::TypeId;

// A fingerprint component describes the head of a term at a particular "path" from this term.
// The path is the sequence of arg indices to get to that term
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FingerprintComponent {
    // This term is below a variable on the path. So it might match anything,
    // either nothing or something.
    Below,

    // The term cannot match any subterm at this path
    Nothing,

    // The head of the subterm at this path.
    // Variable ids are all replaced with 0, because we want to store all variables the same way
    // in the fingerprint tree.
    Something(TypeId, Atom),
}

impl FingerprintComponent {
    pub fn new(term: &Term, path: &&[usize]) -> FingerprintComponent {
        let mut current_term = term;
        for &i in *path {
            if i >= current_term.args.len() {
                if current_term.atomic_variable().is_some() {
                    return FingerprintComponent::Below;
                }
                return FingerprintComponent::Nothing;
            }
            current_term = &current_term.args[i];
        }

        match &current_term.head {
            Atom::Variable(_) => {
                FingerprintComponent::Something(current_term.get_term_type(), Atom::Variable(0))
            }
            a => FingerprintComponent::Something(current_term.get_term_type(), *a),
        }
    }

    // Whether unification could possibly identify terms with these two fingerprints
    pub fn matches(&self, other: &FingerprintComponent) -> bool {
        match (self, other) {
            (FingerprintComponent::Below, _) => true,
            (_, FingerprintComponent::Below) => true,
            (FingerprintComponent::Nothing, FingerprintComponent::Nothing) => true,
            (FingerprintComponent::Something(t1, a1), FingerprintComponent::Something(t2, a2)) => {
                if t1 != t2 {
                    return false;
                }
                if a1.is_variable() || a2.is_variable() {
                    return true;
                }
                a1 == a2
            }
            _ => false,
        }
    }
}

const PATHS: &[&[usize]] = &[&[], &[0], &[1], &[0, 0], &[0, 1], &[1, 0], &[1, 1]];

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Fingerprint {
    components: [FingerprintComponent; PATHS.len()],
}

impl Fingerprint {
    pub fn new(term: &Term) -> Fingerprint {
        let mut components = [FingerprintComponent::Nothing; PATHS.len()];
        for (i, path) in PATHS.iter().enumerate() {
            components[i] = FingerprintComponent::new(term, path);
        }
        Fingerprint { components }
    }

    pub fn matches(&self, other: &Fingerprint) -> bool {
        for i in 0..PATHS.len() {
            if !self.components[i].matches(&other.components[i]) {
                return false;
            }
        }
        true
    }
}

#[derive(Debug)]
pub struct FingerprintTree<T> {
    tree: BTreeMap<Fingerprint, Vec<T>>,
}

impl<T> FingerprintTree<T> {
    pub fn new() -> FingerprintTree<T> {
        FingerprintTree {
            tree: BTreeMap::new(),
        }
    }

    pub fn insert(&mut self, term: &Term, value: T) {
        let fingerprint = Fingerprint::new(term);
        self.tree.entry(fingerprint).or_insert(vec![]).push(value);
    }

    // Find all T with a fingerprint that could unify with this one.
    pub fn get_unifying(&self, term: &Term) -> Vec<&T> {
        let fingerprint = Fingerprint::new(term);
        let mut result = vec![];

        // TODO: do smart tree things instead of this dumb exhaustive search
        for (f, values) in &self.tree {
            if f.matches(&fingerprint) {
                for v in values {
                    result.push(v);
                }
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fingerprint() {
        let term = Term::parse("c0(x0, x1)");
        Fingerprint::new(&term);
    }

    #[test]
    fn test_fingerprint_matching() {
        let term1 = Term::parse("c2(x0, x1, c0)");
        let term2 = Term::parse("c2(c1, c3(x0), c0)");
        assert!(Fingerprint::new(&term1).matches(&Fingerprint::new(&term2)));
    }

    #[test]
    fn test_fingerprint_tree() {
        let mut tree = FingerprintTree::new();
        let term1 = Term::parse("c2(x0, x1, c0)");
        let term2 = Term::parse("c2(c1, c3(x0), c0)");
        tree.insert(&term1, 1);
        assert!(tree.get_unifying(&term1).len() > 0);
        assert!(tree.get_unifying(&term2).len() > 0);
    }
}
