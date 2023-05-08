use std::collections::{HashMap, HashSet};

use nohash_hasher::BuildNoHashHasher;

use crate::atom::{Atom, AtomId};
use crate::term::Term;
use crate::type_space::TypeId;

// The TermInfo stores information about an abstract term.
// The idea behind the abstract term is that if we know two terms are identical, like:
//   double(x)
//   add(x, x)
// then we can store them as the same abstract term. Instead of rewriting terms, we can
// merge nodes in our graph of abstract terms. If we are careful about always merging the
// "smaller" node into the "larger" one, we can do these merges cheaply (amortized).
pub struct TermInfo {
    term_type: TypeId,
    arg_types: Vec<TypeId>,

    // All edges that touch this term
    adjacent: HashSet<EdgeId, BuildNoHashHasher<EdgeId>>,

    // The canonical way to produce this term.
    canonical: CanonicalForm,
}
pub type TermId = u32;

// An edge represents a single substitution.
// All variables get renamed, and some in the template can get replaced.
// For example:
// template = add(x0, x1)
// replacement = mul(x0, x1)
//
pub struct EdgeInfo {
    // The base term that will be substituted into
    template: TermId,

    // variable i in template gets mapped to var_map[i] after substitution.
    // "None" means "replace with the replacement"
    template_var_map: Vec<Option<AtomId>>,

    // variable i in replacement gets mapped to variable varmap[i]
    replacement: TermId,
    replacement_var_map: Vec<AtomId>,

    // What we get
    result: TermId,
}
pub type EdgeId = u32;

// The canonical form of a term can either be an atom, or it can be a particular way
// of constructing this term.
enum CanonicalForm {
    Atom(Atom),
    Edge(EdgeId),
}

pub struct TermGraph {
    atoms: HashMap<Atom, TermId>,
    terms: Vec<TermInfo>,
    edges: Vec<EdgeInfo>,

    edgemap: HashMap<(TermId, TermId), Vec<EdgeId>, BuildNoHashHasher<(TermId, TermId)>>,
}

impl TermGraph {
    pub fn new() -> TermGraph {
        TermGraph {
            atoms: HashMap::default(),
            terms: Vec::new(),
            edges: Vec::new(),
            edgemap: HashMap::default(),
        }
    }

    // Inserts a term for an atom, or returns the existing term.
    pub fn insert_atom(&mut self, atom: Atom, atom_type: TypeId, arg_types: Vec<TypeId>) -> TermId {
        if let Some(term_id) = self.atoms.get(&atom) {
            return *term_id;
        }

        let term_id = self.terms.len() as TermId;
        self.terms.push(TermInfo {
            term_type: atom_type,
            arg_types,
            adjacent: HashSet::default(),
            canonical: CanonicalForm::Atom(atom),
        });
        self.atoms.insert(atom, term_id);
        term_id
    }

    // Inserts a new term, or returns the existing term.
    // The term graph normalizes by variable order, whereas Term doesn't, so we also
    // return a map from id in the term graph -> id in the term.
    // So, for example, if we insert add(x2, x4) we will get a pair of:
    // first element: add(x0, x1)
    // second element: [2, 4]
    pub fn insert_term(&mut self, term: &Term) -> (TermId, Vec<AtomId>) {
        todo!("insert_term");
    }
}
