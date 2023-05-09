use std::collections::{HashMap, HashSet};

use fxhash::FxHashMap;
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

// TermInfo normalizes across all namings of the input variables.
// A TermInstance represents a particular ordering.
// var_map[i] = j means that the variable the TermInfo would display as x_i, the TermInstance would
// display as x_j.
// So for example to represent a TermInstance:
//   foo(x4, x0)
// we would use:
//   term: foo(x0, x1)
//   var_map: [4, 0]
// The length of varmap must be the same as arg_types.
// No two variables should be named the same thing.
pub struct TermInstance {
    term: TermId,
    var_map: Vec<AtomId>,
}

impl TermInstance {
    // Panics if there is a logical inconsistency
    pub fn check(&self) {
        let mut reverse_map = vec![None; self.var_map.len()];
        for (i, &var) in self.var_map.iter().enumerate() {
            if let Some(old) = reverse_map[var as usize] {
                panic!(
                    "TermInstance has two variables named {} (at {} and {})",
                    var, i, old
                );
            }
            reverse_map[var as usize] = Some(i as AtomId);
        }
    }
}

// The different ways to replace a single variable in a substitution.
// Either we rename the variable, or we expand it into a different term.
// "Do-nothing" replacements are represented by a Rename with the same index.
pub enum Replacement {
    Rename(AtomId),
    Expand(TermInstance),
}

impl Replacement {
    // Calls f on each variable id used by this replacement.
    fn map_vars(&self, f: &mut impl FnMut(&AtomId)) {
        match self {
            Replacement::Rename(var) => f(var),
            Replacement::Expand(term) => {
                for &var in &term.var_map {
                    f(&var);
                }
            }
        }
    }
}

// An edge represents a single substitution.
// An EdgeKey is enough information to uniquely specify one substitution.
// All variables get renamed, and some in the template can get replaced.
// For example:
// template = add(x0, x1)
// replacement = mul(x0, x1)
pub struct EdgeKey {
    // The base term that will be substituted into
    template: TermId,

    // The replacement for each variable in the template.
    // Should have as many entries as the template has variables.
    // This list is normalized so that a single substitution is represented in only one way.
    // The first time a new variable appears, it should get the first available index.
    replacements: Vec<Replacement>,
}

impl EdgeKey {
    // Panics if this edge is not normalized.
    pub fn check(&self) {
        // We expect to see the variables in increasing order
        let mut expected = 0;

        for replacement in &self.replacements {
            replacement.map_vars(&mut |&var| {
                if var > expected {
                    panic!(
                        "EdgeKey is not normalized: expected {}, got {}",
                        expected, var
                    );
                }
                if var == expected {
                    expected += 1;
                }
            });
        }
    }
}

pub struct EdgeInfo {
    // The parameters that determine the substitution
    key: EdgeKey,

    // The result of the substitution
    result: TermInstance,
}
pub type EdgeId = u32;

impl EdgeInfo {}

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

    // Maps (template, replacement) -> edges
    edgemap: FxHashMap<EdgeKey, EdgeId>,
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

    pub fn get_term_info(&self, term: TermId) -> &TermInfo {
        &self.terms[term as usize]
    }

    // Inserts a term for an atom, or returns the existing term if there is one.
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

    // Creates a new term by applying a substitution to a template, or returns the existing term
    // if there is one.
    pub fn replace(
        &mut self,
        template: &TermInstance,
        position: AtomId,
        replacement: &TermInstance,
    ) -> TermInstance {
        todo!("replace");
    }

    // Inserts a new term, or returns the existing term if there is one.
    pub fn insert_term(&mut self, term: &Term) -> TermInstance {
        todo!("insert_term");
    }

    pub fn extract_term(&self, instance: &TermInstance) -> Term {
        todo!("extract_term");
    }
}
