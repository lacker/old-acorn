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
        let p = permutation::parse(6, "(3 4)");
        g.add(p);
        assert_eq!(g.size(), 12);
        let p = permutation::parse(6, "(4 5)");
        g.add(p);
        assert_eq!(g.size(), 36);
        let p = permutation::parse(6, "(1 5)");
        g.add(p);
        assert_eq!(g.size(), 720);
    }
}
