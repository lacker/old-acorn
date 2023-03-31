use crate::atom::Atom;
use crate::type_space::TypeId;
use std::collections::hash_map::Entry;
use std::collections::HashMap;

type TermId = u32;
const TRUE: TermId = 0;

// The ActiveTerm contains enough information to uniquely determine the term.
// Two matching ActiveTerm will be given the same TermId.
// Non-true terms cannot contain a "true".
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ActiveTerm {
    pub term_type: TypeId,
    pub head_type: TypeId,
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

    // Panics if the id is bad or TRUE
    pub fn get_term(&self, term_id: TermId) -> &ActiveTerm {
        if term_id == TRUE {
            panic!("Attempted to get_term on TRUE");
        }
        self.terms[term_id as usize].as_ref().unwrap()
    }

    // We could check for no references to True here, if that becomes a problem.
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

        let key1 = ActiveTerm {
            head_type: 0,
            term_type: 0,
            head: Atom::new("a0"),
            args: vec![],
        };
        let key2 = key1.clone();
        let id1 = set.add_term(key1);
        let id2 = set.add_term(key2);
        assert_eq!(id1, id2);
    }
}
