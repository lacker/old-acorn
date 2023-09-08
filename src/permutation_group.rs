use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::iter;

use crate::atom::AtomId;
use crate::permutation::{self, Permutation};

// The goal of this object is to represent the permutations of the arguments of a function.
// For now, everything we want is applicable to general permutation groups.
// The "degree" of a permutation group is the number of items it is permuting.
#[derive(Debug)]
pub struct PermutationGroup {
    degree: AtomId,

    // All permutations in the group.
    elements: BTreeSet<Permutation>,
}

impl PermutationGroup {
    pub fn trivial(degree: AtomId) -> PermutationGroup {
        PermutationGroup {
            degree,
            elements: iter::once(permutation::identity(degree)).collect(),
        }
    }

    pub fn contains(&self, permutation: &Permutation) -> bool {
        self.elements.contains(permutation)
    }

    pub fn size(&self) -> usize {
        self.elements.len()
    }

    pub fn is_trivial(&self) -> bool {
        self.size() == 1
    }

    // Add all permutations in the queue and their compositions to the queue
    fn consume(&mut self, queue: &mut BTreeSet<Permutation>) {
        while let Some(permutation) = queue.pop_first() {
            if self.contains(&permutation) {
                continue;
            }
            self.elements.insert(permutation.clone());

            for existing in &self.elements {
                let composition = permutation::compose(&permutation, existing);

                if self.contains(&composition) {
                    continue;
                }
                queue.insert(composition);
            }
        }
    }

    pub fn add(&mut self, permutation: Permutation) {
        assert_eq!(permutation.len(), self.degree as usize);
        let mut queue = iter::once(permutation).collect();
        self.consume(&mut queue);
    }

    // Normalize the list by picking the lexicographically first way to permute it,
    // among all the permutations in this group.
    pub fn normalize<T: Ord>(&self, list: Vec<T>) -> Vec<T> {
        if self.size() == 1 {
            return list;
        }

        // Find the permutation whose inverse applied to the list is minimal
        let mut perms = self.elements.iter();
        let mut min_p = perms.next().unwrap();
        for p in perms {
            if permutation::compare_apply_inverse(p, min_p, &list) == Ordering::Less {
                min_p = p;
            }
        }

        let inverse = permutation::invert(min_p);
        permutation::apply(inverse, list)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_permutation_groups() {
        let mut g = PermutationGroup::trivial(6);
        assert_eq!(g.size(), 1);
        let p = permutation::parse(6, "(0 1)");
        g.add(p);
        assert_eq!(g.size(), 2);
        let p = permutation::parse(6, "(0 2)");
        g.add(p);
        assert_eq!(g.size(), 6);

        // Slow
        // let p = permutation::parse(6, "(3 4)");
        // g.add(p);
        // assert_eq!(g.size(), 12);
        // let p = permutation::parse(6, "(4 5)");
        // g.add(p);
        // assert_eq!(g.size(), 36);
        // let p = permutation::parse(6, "(1 5)");
        // g.add(p);
        // assert_eq!(g.size(), 720);
    }
}
