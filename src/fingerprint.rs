use std::collections::{BTreeMap, HashMap};

use crate::atom::Atom;
use crate::literal::Literal;
use crate::term::Term;
use crate::type_map::TypeId;

// A fingerprint component describes the head of a term at a particular "path" from this term.
// The path is the sequence of arg indices to get to that term
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FingerprintComponent {
    // The path to this term goes through a variable.
    Below,

    // The path to this term goes through a leaf node.
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

    // Whether a unification could combine paths with these fingerprint components
    pub fn could_unify(&self, other: &FingerprintComponent) -> bool {
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

    // Whether a specialization could turn the 'self' component into the 'other' component
    pub fn could_specialize(&self, other: &FingerprintComponent) -> bool {
        match (self, other) {
            (FingerprintComponent::Below, _) => true,
            (_, FingerprintComponent::Below) => false,
            (FingerprintComponent::Nothing, FingerprintComponent::Nothing) => true,
            (FingerprintComponent::Something(t1, a1), FingerprintComponent::Something(t2, a2)) => {
                if t1 != t2 {
                    return false;
                }
                if a1.is_variable() {
                    return true;
                }
                a1 == a2
            }
            _ => false,
        }
    }
}

const PATHS: &[&[usize]] = &[&[], &[0], &[1], &[0, 0], &[0, 1], &[1, 0], &[1, 1]];

// The fingerprints of a term, at a selection of paths.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TermFingerprint {
    components: [FingerprintComponent; PATHS.len()],
}

impl TermFingerprint {
    pub fn new(term: &Term) -> TermFingerprint {
        let mut components = [FingerprintComponent::Nothing; PATHS.len()];
        for (i, path) in PATHS.iter().enumerate() {
            components[i] = FingerprintComponent::new(term, path);
        }
        TermFingerprint { components }
    }

    pub fn could_unify(&self, other: &TermFingerprint) -> bool {
        for i in 0..PATHS.len() {
            if !self.components[i].could_unify(&other.components[i]) {
                return false;
            }
        }
        true
    }

    pub fn could_specialize(&self, other: &TermFingerprint) -> bool {
        for i in 0..PATHS.len() {
            if !self.components[i].could_specialize(&other.components[i]) {
                return false;
            }
        }
        true
    }
}

// A data structure designed to quickly find which terms unify with a query term.
#[derive(Clone, Debug)]
pub struct FingerprintUnifier<T> {
    tree: BTreeMap<TermFingerprint, Vec<T>>,
}

impl<T> FingerprintUnifier<T> {
    pub fn new() -> FingerprintUnifier<T> {
        FingerprintUnifier {
            tree: BTreeMap::new(),
        }
    }

    pub fn insert(&mut self, term: &Term, value: T) {
        let fingerprint = TermFingerprint::new(term);
        self.tree.entry(fingerprint).or_insert(vec![]).push(value);
    }

    // Find all T with a fingerprint that this term could unify with.
    pub fn find_unifying(&self, term: &Term) -> Vec<&T> {
        let fingerprint = TermFingerprint::new(term);
        let mut result = vec![];

        // TODO: do smart tree things instead of this dumb exhaustive search
        for (f, values) in &self.tree {
            if fingerprint.could_unify(f) {
                for v in values {
                    result.push(v);
                }
            }
        }

        result
    }
}

// The fingerprints of a literal, at a selection of paths.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct LiteralFingerprint {
    left: TermFingerprint,
    right: TermFingerprint,
}

impl LiteralFingerprint {
    pub fn new(left: &Term, right: &Term) -> LiteralFingerprint {
        LiteralFingerprint {
            left: TermFingerprint::new(left),
            right: TermFingerprint::new(right),
        }
    }

    pub fn could_specialize(&self, other: &LiteralFingerprint) -> bool {
        self.left.could_specialize(&other.left) && self.right.could_specialize(&other.right)
    }
}

// A data structure designed to quickly find which literals are a specialization of a query literal.
// Identifies literals by a usize id.
#[derive(Clone)]
pub struct FingerprintSpecializer<T> {
    trees: HashMap<TypeId, BTreeMap<LiteralFingerprint, Vec<T>>>,
}

impl<T> FingerprintSpecializer<T> {
    pub fn new() -> FingerprintSpecializer<T> {
        FingerprintSpecializer {
            trees: HashMap::new(),
        }
    }

    pub fn insert(&mut self, literal: &Literal, value: T) {
        let fingerprint = LiteralFingerprint::new(&literal.left, &literal.right);
        let tree = self
            .trees
            .entry(literal.left.get_term_type())
            .or_insert(BTreeMap::new());
        tree.entry(fingerprint).or_insert(vec![]).push(value);
    }

    // Find all ids with a fingerprint that this literal could specialize into.
    // Only does a single left->right direction of lookup.
    pub fn find_specializing(&self, left: &Term, right: &Term) -> Vec<&T> {
        let fingerprint = LiteralFingerprint::new(left, right);
        let mut result = vec![];

        let tree = match self.trees.get(&left.get_term_type()) {
            Some(tree) => tree,
            None => return result,
        };

        // TODO: do smart tree things instead of this dumb exhaustive search
        for (f, values) in tree {
            if fingerprint.could_specialize(f) {
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
        TermFingerprint::new(&term);
    }

    #[test]
    fn test_fingerprint_matching() {
        let term1 = Term::parse("c2(x0, x1, c0)");
        let term2 = Term::parse("c2(c1, c3(x0), c0)");
        assert!(TermFingerprint::new(&term1).could_unify(&TermFingerprint::new(&term2)));
    }

    #[test]
    fn test_fingerprint_tree() {
        let mut tree = FingerprintUnifier::new();
        let term1 = Term::parse("c2(x0, x1, c0)");
        let term2 = Term::parse("c2(c1, c3(x0), c0)");
        tree.insert(&term1, 1);
        assert!(tree.find_unifying(&term1).len() > 0);
        assert!(tree.find_unifying(&term2).len() > 0);
    }
}
