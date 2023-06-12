use crate::atom::AtomId;

// The goal of this object is to represent the permutations of the arguments of a function.
// For now, everything we want is applicable to general permutation groups.
// The "degree" of a permutation group is the number of items it is permuting.
#[derive(Debug)]
pub struct PermutationGroup {
    degree: AtomId,

    // A sorted list of all permutations in the group.
    elements: Vec<Vec<AtomId>>,
}

impl PermutationGroup {
    pub fn trivial(degree: AtomId) -> PermutationGroup {
        PermutationGroup {
            degree,
            elements: Vec::new(),
        }
    }
}
