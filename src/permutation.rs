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

// Parses a cycle in the math-standard (1 2 3) form, except it's indexed to start at 0.
fn parse_cycle(degree: AtomId, s: &str) -> Permutation {
    let s = s.replace(&['(', ')'], " ");
    let s = s.trim();

    let items: Vec<AtomId> = s.split_whitespace().map(|x| x.parse().unwrap()).collect();

    let mut result = identity(degree);
    for i in 0..items.len() {
        let j = (i + 1) % items.len();
        result[items[i] as usize] = items[j];
    }
    result
}

// Parses a permutation represented as a composition of cycles
pub fn parse(degree: AtomId, s: &str) -> Permutation {
    let mut result = identity(degree);
    // Split on (
    for cycle in s.split('(').skip(1) {
        let cycle = parse_cycle(degree, cycle);
        result = compose(&cycle, &result);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_permutations() {
        let p1 = parse(4, "(0 1)");
        let p2 = parse(4, "(2 3)");
        let p3a = compose(&p1, &p2);
        let p3b = parse(4, "(0 1)(2 3)");
        assert_eq!(p3a, p3b);
    }
}
