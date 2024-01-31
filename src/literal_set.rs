use std::collections::BTreeMap;

use crate::fingerprint::Fingerprint;
use crate::literal::Literal;
use crate::specializer::Specializer;

// A datastructure for storing a set of literals to make it quick, for a new
// literal, to discover if we already know it or not.
// Each literal has an associated id as well.
pub struct LiteralSet {
    // Indexed by (left-fingerprint, right-fingerprint)
    tree: BTreeMap<(Fingerprint, Fingerprint), Vec<(Literal, usize)>>,
}

impl LiteralSet {
    pub fn new() -> LiteralSet {
        LiteralSet {
            tree: BTreeMap::new(),
        }
    }

    pub fn insert(&mut self, literal: Literal, id: usize) {
        let key = (
            Fingerprint::new(&literal.left),
            Fingerprint::new(&literal.right),
        );
        self.tree.entry(key).or_insert(vec![]).push((literal, id));
    }

    // Checks whether this literal is a specialization of any literal in the set.
    // If so, returns the literal in the set that it is a specialization of, as well
    // as the sign.
    // "true" means that this literal is true for every value of the free variables.
    // "false" means that this literal is false for every value of the free variables.
    pub fn lookup(&self, literal: &Literal) -> Option<(bool, &Literal, usize)> {
        // TODO: do smart tree things instead of this dumb exhaustive search
        let f_left = Fingerprint::new(&literal.left);
        let f_right = Fingerprint::new(&literal.right);
        for ((key_left, key_right), known_literals) in &self.tree {
            if key_left.generalizes(&f_left) && key_right.generalizes(&f_right) {
                for (known_literal, id) in known_literals {
                    // Check if the given literal is a specialization of the known literal.
                    // Note that we illogically only check one direction.
                    let mut s = Specializer::new();
                    if !s.match_terms(&known_literal.left, &literal.left) {
                        continue;
                    }
                    if !s.match_terms(&known_literal.right, &literal.right) {
                        continue;
                    }

                    return Some((
                        literal.positive == known_literal.positive,
                        known_literal,
                        *id,
                    ));
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
        set.insert(Literal::parse("c0(x0, c1) = x0"), 7);
        assert!(set.lookup(&Literal::parse("c0(x0, c1) = x0")).unwrap().0);
        assert!(set.lookup(&Literal::parse("c0(c2, c1) = c2")).unwrap().0);
        assert!(set.lookup(&Literal::parse("c0(x0, x1) = x0")).is_none());
        assert!(!set.lookup(&Literal::parse("c0(x0, c1) != x0")).unwrap().0);

        set.insert(Literal::parse("x0 = x0"), 8);
        assert!(set.lookup(&Literal::parse("x0 = c0")).is_none());
        assert!(set.lookup(&Literal::parse("c0 = x0")).is_none());
        assert!(set.lookup(&Literal::parse("c0 = c0")).unwrap().0);
    }
}
