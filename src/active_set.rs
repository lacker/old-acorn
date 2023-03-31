use crate::atom::Atom;
use crate::type_space::TypeId;
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, HashMap};

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

    pub fn get_term_at_path<'a>(
        &'a self,
        term: &'a ActiveTerm,
        path: &[usize],
    ) -> Option<&'a ActiveTerm> {
        let mut current_term = term;
        for &i in path {
            if i >= current_term.args.len() {
                return None;
            }
            current_term = self.get_term(current_term.args[i]);
        }
        Some(current_term)
    }
}

// A fingerprint component describes the head of a term at a particular "route" from this term.
// The route is the sequence of arg indices to get to that term
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum FingerprintComponent {
    Constant(TypeId, Atom),
    Variable(TypeId),
    Nonexistent,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Fingerprint {
    components: Vec<FingerprintComponent>,
}

impl ActiveTerm {
    fn fingerprint_component(&self) -> FingerprintComponent {
        match &self.head {
            Atom::Reference(_) => FingerprintComponent::Variable(self.head_type),
            a => FingerprintComponent::Constant(self.head_type, *a),
        }
    }
}

impl ActiveSet {
    fn fingerprint(&self, term: &ActiveTerm) -> Fingerprint {
        let mut components = vec![term.fingerprint_component()];
        let paths: &[&[usize]] = &[&[0], &[1], &[0, 0], &[0, 1], &[1, 0], &[1, 1]];
        for path in paths {
            let component = match self.get_term_at_path(term, path) {
                Some(t) => t.fingerprint_component(),
                None => FingerprintComponent::Nonexistent,
            };
            components.push(component);
        }
        Fingerprint { components }
    }
}

struct FingerprintTree {
    tree: BTreeMap<Fingerprint, TermId>,
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
