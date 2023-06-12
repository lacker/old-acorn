use crate::atom::AtomId;

// The goal of this object is to represent the permutations of the arguments of a function.
// For now, everything we want is applicable to general permutation groups.
// The "degree" of a permutation group is the number of items it is permuting.
#[derive(Debug)]
pub struct PermutationGroup {
    degree: AtomId,
    representation: Representation,
}

// There are better ways to efficiently represent permutation groups. We're going to hardcode
// some of the special cases and fall back to a general and inefficient representation otherwise.
#[derive(Debug)]
enum Representation {
    // No permutations
    Trivial,

    // All permutations
    Symmetric,

    // Specifically this list of permutations
    List(Vec<Vec<AtomId>>),
}

impl PermutationGroup {
    pub fn trivial(degree: AtomId) -> PermutationGroup {
        PermutationGroup {
            degree,
            representation: Representation::Trivial,
        }
    }
}
