use crate::atom::AtomId;

// The SymmetryGroup represents the symmetry group of a function's arguments.
// For example, f(a, b, c, d) = a * b + c * d is symmetric under any of the operations:
// swap a-b
// swap c-d
// swap both a-c and b-d
// and any composition of those operations.
#[derive(Debug)]
pub struct SymmetryGroup {
    // The number of arguments
    n: AtomId,
}

impl SymmetryGroup {
    fn trivial(n: AtomId) -> SymmetryGroup {
        SymmetryGroup { n }
    }
}
