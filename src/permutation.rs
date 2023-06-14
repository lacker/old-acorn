use crate::atom::AtomId;
use std::cmp::Ordering;

// A permutation is represented in "functional" form.
// Specifically, v[i] = j means that the permutation moves the ith element to the jth element.
pub type Permutation = Vec<AtomId>;

pub fn identity(degree: AtomId) -> Permutation {
    let mut result = Vec::new();
    for i in 0..degree {
        result.push(i);
    }
    result
}

pub fn destructive_apply<T>(p: Permutation, list: &mut Vec<T>) {
    let mut p = p;
    for i in 0..p.len() {
        loop {
            let j = p[i] as usize;
            if i == j {
                break;
            }
            p.swap(i, j);
            list.swap(i, j);
        }
    }
}

// (left o right) is the permutation you get by first doing the right permutation, then the left.
pub fn compose(left: &Permutation, right: &Permutation) -> Permutation {
    assert_eq!(left.len(), right.len());
    let mut result = Vec::new();
    for r in right {
        result.push(left[*r as usize]);
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

pub fn to_string(permutation: &Permutation) -> String {
    let mut result = String::new();
    let mut done = vec![false; permutation.len()];
    for i in 0..permutation.len() {
        if done[i] {
            continue;
        }
        if i == permutation[i] as usize {
            done[i] = true;
            continue;
        }
        // Add this cycle
        result.push('(');
        let mut i = i;
        loop {
            result.push_str(&i.to_string());
            done[i] = true;
            i = permutation[i] as usize;
            if done[i] {
                break;
            }
            result.push(' ');
        }
        result.push(')');
    }
    if result.is_empty() {
        result.push_str("()");
    }
    result
}

pub fn compare<T: Ord>(left: &Permutation, right: &Permutation, list: &Vec<T>) -> Ordering {
    for (left_index, right_index) in left.iter().zip(right.iter()) {
        let left_item = &list[*left_index as usize];
        let right_item = &list[*right_index as usize];
        let cmp = left_item.cmp(right_item);
        if cmp != Ordering::Equal {
            return cmp;
        }
    }
    Ordering::Equal
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_parse(degree: AtomId, s: &str) -> Permutation {
        let p = parse(degree, s);
        assert_eq!(to_string(&p), s);
        p
    }

    #[test]
    fn test_basic_permutations() {
        let p1 = check_parse(4, "(0 1)");
        let p2 = check_parse(4, "(2 3)");
        let p3a = compose(&p1, &p2);
        let p3b = check_parse(4, "(0 1)(2 3)");
        assert_eq!(p3a, p3b);
    }

    #[test]
    fn test_destructive_apply() {
        let stuff = vec![100, 200, 300, 400, 500];
        let p1 = check_parse(5, "(0 1)(2 4 3)");
        let p2 = check_parse(5, "(1 3 4)");

        let mut one_at_a_time = stuff.clone();
        destructive_apply(p2.clone(), &mut one_at_a_time);
        destructive_apply(p1.clone(), &mut one_at_a_time);

        let mut all_at_once = stuff.clone();
        destructive_apply(compose(&p1, &p2), &mut all_at_once);

        assert_eq!(one_at_a_time, all_at_once);
    }
}
