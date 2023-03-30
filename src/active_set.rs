use std::fmt;

use crate::atom::Atom;

type TermId = u32;

// The TermInfo struct is the data we store for each term.
#[derive(Debug)]
pub struct TermInfo {
    pub itype: usize,
    pub head: Atom,
    pub args: Vec<TermId>,
}

// The ActiveSet stores rich data for a bunch of terms.
// Within the ActiveSet, term data is perfectly shared, so that
// we can check term equality cheaply, and cheaply augment terms with
// additional data as needed.
pub struct ActiveSet {
    // None should only exist at index 0 and indicates the special term, True
    terms: Vec<Option<TermInfo>>,
}

// The ActiveTerm is a wrapper that contains some information for a term.
// I'm not entirely sure this is the right entity to use.
pub struct ActiveTerm<'a> {
    pub active_set: &'a ActiveSet,
    pub id: TermId,

    // info is "None" for the special term "true"
    pub info: Option<&'a TermInfo>,
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet { terms: vec![None] }
    }

    pub fn get_true(&self) -> ActiveTerm {
        ActiveTerm {
            active_set: self,
            id: 0,
            info: None,
        }
    }

    // Panics if the id is bad
    pub fn get_term(&self, term_id: TermId) -> ActiveTerm {
        ActiveTerm {
            active_set: self,
            id: term_id,
            info: self.terms[term_id as usize].as_ref(),
        }
    }
}

impl ActiveTerm<'_> {
    pub fn is_true(&self) -> bool {
        self.id == 0
    }
}

impl PartialEq for ActiveTerm<'_> {
    // This can compare terms from different active sets as equal, so, don't do that.
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for ActiveTerm<'_> {}

impl fmt::Debug for ActiveTerm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "term({}, {:?})", self.id, self.info)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_term() {
        let set = ActiveSet::new();
        let term_zero = set.get_term(0);
        assert!(term_zero.is_true());
        assert_eq!(term_zero, set.get_true());
    }
}
