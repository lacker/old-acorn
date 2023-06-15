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

pub fn apply<T>(p: Permutation, list: Vec<T>) -> Vec<T> {
    let mut p = p;
    let mut list = list;
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
    list
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

// (left o right^-1) is what you get by first doing the inverse right permutation, then the left.
pub fn compose_inverse(left: Permutation, right: Permutation) -> Permutation {
    apply(right, left)
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

pub fn invert(permutation: &Permutation) -> Permutation {
    let mut result = permutation.clone();
    for (i, j) in permutation.iter().enumerate() {
        result[*j as usize] = i as AtomId;
    }
    result
}

// Lexicographically compare left^-1(list) and right^-1(list)
pub fn compare_apply_inverse<T: Ord>(
    left: &Permutation,
    right: &Permutation,
    list: &Vec<T>,
) -> Ordering {
    for (left_index, right_index) in left.iter().zip(right.iter()) {
        // i = left^-1(left_index) = right^-1(right_index)
        // where i is the index of this iteration that we don't explicitly use.
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
    fn test_compose() {
        let p1 = check_parse(3, "(0 1)");
        let p2 = check_parse(3, "(1 2)");

        // Doing p2 and then p1 should take 2 -> 0, 1 -> 2, 0 -> 1
        let expected = check_parse(3, "(0 1 2)");
        let actual = compose(&p1, &p2);
        assert_eq!(actual, expected);

        println!("actual: {:?}", &actual);

        let stuff = vec![100, 200, 300];
        let stuff = apply(actual, stuff);
        assert_eq!(stuff, vec![300, 100, 200]);
    }

    #[test]
    fn test_destructive_apply() {
        let stuff = vec![100, 200, 300, 400, 500];
        let p1 = check_parse(5, "(0 1)(2 4 3)");
        let p2 = check_parse(5, "(1 3 4)");

        let one_at_a_time = stuff.clone();
        let one_at_a_time = apply(p2.clone(), one_at_a_time);
        let one_at_a_time = apply(p1.clone(), one_at_a_time);
        let all_at_once = stuff.clone();
        let all_at_once = apply(compose(&p1, &p2), all_at_once);

        assert_eq!(one_at_a_time, all_at_once);
    }

    #[test]
    fn test_identity() {
        let e = identity(5);
        let p = check_parse(5, "(0 1)(2 4 3)");
        assert_eq!(compose(&e, &p), p);
        assert_eq!(compose(&p, &e), p);
        let stuff = vec![100, 200, 300, 400, 500];
        let stuff2 = apply(e, stuff.clone());
        assert_eq!(stuff2, stuff);
    }

    #[test]
    fn test_associative() {
        let p1 = check_parse(5, "(0 1)(2 4 3)");
        let p2 = check_parse(5, "(1 3 4)");
        let p3 = check_parse(5, "(0 1 2)");
        let left_first = compose(&compose(&p1, &p2), &p3);
        let right_first = compose(&p1, &compose(&p2, &p3));
        assert_eq!(left_first, right_first);
    }

    #[test]
    fn test_compose_inverse() {
        let p1 = check_parse(5, "(0 1)(2 4 3)");
        let p2 = check_parse(5, "(1 3 4)");
        let invert_first = compose(&p1, &invert(&p2));
        let in_one_op = compose_inverse(p1, p2);
        assert_eq!(invert_first, in_one_op);
    }
}
