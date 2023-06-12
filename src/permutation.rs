use crate::atom::AtomId;

// A permutation is represented in "functional" form.
// Specifically, it is a vector v where v[i] = j means that the permutation maps i to j.
pub type Permutation = Vec<AtomId>;

pub fn identity(degree: AtomId) -> Permutation {
    let mut result = Vec::new();
    for i in 0..degree {
        result.push(i);
    }
    result
}

pub fn apply(permutation: &Permutation, item: AtomId) -> AtomId {
    permutation[item as usize]
}

pub fn compose(left: &Permutation, right: &Permutation) -> Permutation {
    assert_eq!(left.len(), right.len());
    let mut result = Vec::new();
    for r in right {
        result.push(apply(left, *r));
    }
    result
}

pub fn is_identity(permutation: &Permutation) -> bool {
    for (i, j) in permutation.iter().enumerate() {
        if i != *j as usize {
            return false;
        }
    }
    true
}
