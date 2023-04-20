use std::collections::BTreeMap;

use crate::fingerprint::Fingerprint;
use crate::term::Literal;
use crate::unifier::{Scope, Unifier};

// A datastructure for storing a set of literals to make it quick, for a new
// literal, to discover if we already know it or not.
pub struct LiteralSet {
    // Indexed by (left-fingerprint, right-fingerprint)
    tree: BTreeMap<(Fingerprint, Fingerprint), Vec<Literal>>,
}

impl LiteralSet {
    pub fn new() -> LiteralSet {
        LiteralSet {
            tree: BTreeMap::new(),
        }
    }

    pub fn insert(&mut self, literal: Literal) {
        let key = (
            Fingerprint::new(&literal.left),
            Fingerprint::new(&literal.right),
        );
        self.tree.entry(key).or_insert(vec![]).push(literal);
    }

    // Checks whether this literal is a specialization of any literal in the set.
    // If so, returns the literal in the set that it is a specialization of, as well
    // as the sign.
    // "true" means that this literal is true for every value of the free variables.
    // "false" means that this literal is false for every value of the free variables.
    pub fn lookup(&self, literal: &Literal) -> Option<(bool, &Literal)> {
        // TODO: do smart tree things instead of this dumb exhaustive search
        let f_left = Fingerprint::new(&literal.left);
        let f_right = Fingerprint::new(&literal.right);
        for ((key_left, key_right), known_literals) in &self.tree {
            if key_left.generalizes(&f_left) && key_right.generalizes(&f_right) {
                for known_literal in known_literals {
                    // We want to check if the known_literal is a generalization. Just a
                    // unification isn't enough to use. So we try unifying, but we keep
                    // the scope of the query literal as Output to prevent its variables from remapping.
                    let mut u = Unifier::new();
                    if !u.unify(
                        Scope::Left,
                        &known_literal.left,
                        Scope::Output,
                        &literal.left,
                    ) {
                        continue;
                    }
                    if !u.unify(
                        Scope::Left,
                        &known_literal.right,
                        Scope::Output,
                        &literal.right,
                    ) {
                        continue;
                    }
                    return Some((literal.positive == known_literal.positive, known_literal));
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_set_lookup() {
        let mut set = LiteralSet::new();
        set.insert(Literal::parse("a0(x0, a1) = x0"));
        assert!(set.lookup(&Literal::parse("a0(x0, a1) = x0")).unwrap().0);
        assert!(set.lookup(&Literal::parse("a0(a2, a1) = a2")).unwrap().0);
        assert!(set.lookup(&Literal::parse("a0(x0, x1) = x0")).is_none());
        assert!(!set.lookup(&Literal::parse("a0(x0, a1) != x0")).unwrap().0);
    }
}
