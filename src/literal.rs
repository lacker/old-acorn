use std::cmp::Ordering;
use std::fmt;

use crate::atom::{Atom, AtomId};
use crate::term::Term;
use crate::type_map::TypeId;

// Literals are always boolean-valued.
// In normalized form, left is the "larger" term.
// Literals like "foo(a, b, c)" are treated as equalities having both
// a left and a right side, by making a right side equal to the special constant "true".
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Literal {
    pub positive: bool,
    pub left: Term,
    pub right: Term,
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.positive {
            if self.is_boolean() {
                write!(f, "{}", self.left)
            } else {
                write!(f, "{} = {}", self.left, self.right)
            }
        } else {
            if self.is_boolean() {
                write!(f, "not {}", self.left)
            } else {
                write!(f, "{} != {}", self.left, self.right)
            }
        }
    }
}

impl Literal {
    // Normalizes the direction.
    // The larger term should be on the left of the literal.
    pub fn new(positive: bool, left: Term, right: Term) -> Literal {
        if left.extended_kbo_cmp(&right) == Ordering::Less {
            Literal {
                positive,
                left: right,
                right: left,
            }
        } else {
            Literal {
                positive,
                left,
                right,
            }
        }
    }

    pub fn positive(term: Term) -> Literal {
        Literal::new(true, term, Term::new_true())
    }

    pub fn negative(term: Term) -> Literal {
        Literal::new(false, term, Term::new_true())
    }

    pub fn equals(left: Term, right: Term) -> Literal {
        Literal::new(true, left, right)
    }

    pub fn not_equals(left: Term, right: Term) -> Literal {
        Literal::new(false, left, right)
    }

    pub fn negate(&self) -> Literal {
        Literal {
            positive: !self.positive,
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }

    pub fn parse(s: &str) -> Literal {
        if s.contains(" != ") {
            let mut parts = s.split(" != ");
            let left = Term::parse(parts.next().unwrap());
            let right = Term::parse(parts.next().unwrap());
            Literal::not_equals(left, right)
        } else if s.contains(" = ") {
            let mut parts = s.split(" = ");
            let left = Term::parse(parts.next().unwrap());
            let right = Term::parse(parts.next().unwrap());
            Literal::equals(left, right)
        } else if s.starts_with("not ") {
            let term = Term::parse(&s[4..]);
            Literal::negative(term)
        } else {
            let term = Term::parse(s);
            Literal::positive(term)
        }
    }

    // Returns true if this literal is a tautology, i.e. foo = foo
    pub fn is_tautology(&self) -> bool {
        self.positive && self.left == self.right
    }

    // Returns whether this literal is syntactically impossible, i.e. foo != foo
    pub fn is_impossible(&self) -> bool {
        !self.positive && self.left == self.right
    }

    // Returns whether this literal is a boolean literal, i.e. "foo" or "!foo"
    pub fn is_boolean(&self) -> bool {
        self.right.is_true()
    }

    pub fn is_higher_order(&self) -> bool {
        self.left.is_higher_order() || self.right.is_higher_order()
    }

    pub fn num_quantifiers(&self) -> AtomId {
        self.left
            .least_unused_variable()
            .max(self.right.least_unused_variable())
    }

    pub fn var_type(&self, i: AtomId) -> Option<AtomId> {
        self.left.var_type(i).or_else(|| self.right.var_type(i))
    }

    // Deduplicates
    pub fn typed_atoms(&self) -> Vec<(TypeId, Atom)> {
        let mut answer = self.left.typed_atoms();
        answer.extend(self.right.typed_atoms());
        answer.sort();
        answer.dedup();
        answer
    }

    pub fn map(&self, f: &mut impl FnMut(&Term) -> Term) -> Literal {
        Literal::new(self.positive, f(&self.left), f(&self.right))
    }

    pub fn replace_atom(&self, atom: &Atom, replacement: &Atom) -> Literal {
        self.map(&mut |term| term.replace_atom(atom, replacement))
    }

    pub fn atom_count(&self) -> u32 {
        self.left.atom_count() + self.right.atom_count()
    }

    pub fn has_any_variable(&self) -> bool {
        self.left.has_any_variable() || self.right.has_any_variable()
    }

    pub fn has_local_constant(&self) -> bool {
        self.left.has_local_constant() || self.right.has_local_constant()
    }

    // Whether the components of this literal are strictly ordered according to the KBO.
    pub fn strict_kbo(&self) -> bool {
        match self.left.kbo_cmp(&self.right) {
            Ordering::Less => panic!("kbo inconsistency"),
            Ordering::Equal => false,
            Ordering::Greater => true,
        }
    }

    // Helper function to treat a literal as two terms.
    // For a literal s = t, get a vector with:
    // (true, s, t)
    // (false, t, s)
    pub fn both_term_pairs(&self) -> Vec<(bool, &Term, &Term)> {
        vec![
            (true, &self.left, &self.right),
            (false, &self.right, &self.left),
        ]
    }

    // Returns (right, left) with normalized var ids.
    pub fn normalized_reversed(&self) -> (Term, Term) {
        let mut var_ids = vec![];
        let mut right = self.right.clone();
        right.normalize_var_ids(&mut var_ids);
        let mut left = self.left.clone();
        left.normalize_var_ids(&mut var_ids);
        (right, left)
    }

    pub fn least_unused_variable(&self) -> AtomId {
        self.left
            .least_unused_variable()
            .max(self.right.least_unused_variable())
    }

    pub fn validate_type(&self) {
        if self.left.term_type != self.right.term_type {
            panic!(
                "Literal type mismatch: {} has type {} but {} has type {}",
                self.left, self.left.term_type, self.right, self.right.term_type
            );
        }
    }

    // An extension of the kbo ordering on literals.
    // Ignores sign.
    pub fn extended_kbo_cmp(&self, other: &Literal) -> Ordering {
        let left_cmp = self.left.extended_kbo_cmp(&other.left);
        if left_cmp != Ordering::Equal {
            return left_cmp;
        }
        self.right.extended_kbo_cmp(&other.right)
    }

    pub fn has_skolem(&self) -> bool {
        self.left.has_skolem() || self.right.has_skolem()
    }

    // Whether either side of the literal has this as its head.
    pub fn has_head(&self, head: &Atom) -> bool {
        self.left.get_head() == head || self.right.get_head() == head
    }
}

// Literals are ordered so that you can normalize a clause by sorting its literals.
// This is using a traditional saturation-based ordering, which might not really make sense.
// Anyway.
// Negative literals come first. We depend on that in miscellaneous places.
// Then, we order backwards by term ordering for the left term.
// Then, backwards (I guess?) for the right term.
impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let positive_cmp = self.positive.cmp(&other.positive);
        if positive_cmp != Ordering::Equal {
            return Some(positive_cmp);
        }

        let left_cmp = other.left.extended_kbo_cmp(&self.left);
        if left_cmp != Ordering::Equal {
            return Some(left_cmp);
        }

        Some(other.right.extended_kbo_cmp(&self.right))
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}
