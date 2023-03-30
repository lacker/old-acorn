use crate::atom::Atom;
use std::collections::hash_map::Entry;
use std::collections::HashMap;

type TermId = u32;

// The ActiveTerm contains enough information to uniquely determine the term.
// Two matching ActiveTerm will be given the same TermId.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ActiveTerm {
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
    terms: Vec<Option<ActiveTerm>>,

    // Used to make sure each term is only stored once
    id_for_term: HashMap<ActiveTerm, TermId>,
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet {
            terms: vec![None],
            id_for_term: HashMap::new(),
        }
    }

    // Panics if the id is bad
    pub fn get_term(&self, term_id: TermId) -> Option<&ActiveTerm> {
        self.terms[term_id as usize].as_ref()
    }

    pub fn add_term(&mut self, term: ActiveTerm) -> TermId {
        match self.id_for_term.entry(term) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                // We need to clone the key, because one goes in terms, one goes in id_for_term
                let term_clone = entry.key().clone();
                let new_id = self.terms.len() as TermId;
                entry.insert(new_id);
                self.terms.push(Some(term_clone));
                new_id
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_term() {
        let mut set = ActiveSet::new();
        let term_zero = set.get_term(0);
        assert!(term_zero.is_none());

        let key1 = ActiveTerm {
            itype: 0,
            head: Atom::new("a0"),
            args: vec![],
        };
        let key2 = key1.clone();
        let id1 = set.add_term(key1);
        let id2 = set.add_term(key2);
        assert_eq!(id1, id2);
    }
}
