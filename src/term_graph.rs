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
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
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
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
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
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
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

// Renumbers the variables in the replacements so that they are in increasing order.
// Returns the new replacements, and a vector mapping new variable ids to old ones.
//
// For example, if the replacements are:
//   x0 -> foo(x2, x4)
//   x1 -> foo(x2, x6)
// Then we see the variables in the order x2, x4, x6.
// The normalized numbering would be 0, 1, 2.
// So the new replacements would be:
//   x0 -> foo(x0, x1)
//   x1 -> foo(x0, x2)
// and the vector map would be:
//   [2, 4, 6]
fn normalize_replacements(replacements: &Vec<Replacement>) -> (Vec<Replacement>, Vec<AtomId>) {
    let mut new_replacements = vec![];
    let mut new_to_old = vec![];
    for r in replacements {
        match r {
            Replacement::Rename(old_var) => {
                // Figure out the new id for this variable
                let new_var = match new_to_old.iter().position(|&v| v == *old_var) {
                    Some(i) => i,
                    None => {
                        let new_var = new_to_old.len();
                        new_to_old.push(*old_var);
                        new_var
                    }
                };
                new_replacements.push(Replacement::Rename(new_var as AtomId));
            }
            Replacement::Expand(old_term) => {
                let mut new_term = TermInstance {
                    term: old_term.term,
                    var_map: vec![],
                };
                for old_var in &old_term.var_map {
                    // Figure out the new id for this variable
                    let new_var = match new_to_old.iter().position(|&v| v == *old_var) {
                        Some(i) => i,
                        None => {
                            let new_var = new_to_old.len();
                            new_to_old.push(*old_var);
                            new_var
                        }
                    };
                    new_term.var_map.push(new_var as AtomId);
                }
                new_replacements.push(Replacement::Expand(new_term));
            }
        }
    }
    (new_replacements, new_to_old)
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

    // Returns the term that is the result of the given substitution.
    // If it's already in the graph, returns the existing term.
    // Otherwise, creates a new edge and a new term and returns the new term.
    // key must be normalized.
    pub fn insert_edge(&mut self, key: EdgeKey) -> &TermInstance {
        // Check if this edge is already in the graph
        if let Some(edge_id) = self.edgemap.get(&key) {
            return &self.edges[*edge_id as usize].result;
        }

        // Figure out the type signature of our new term
        let template = self.get_term_info(key.template);
        let mut result_arg_types = vec![];
        for (i, replacement) in key.replacements.iter().enumerate() {
            match replacement {
                Replacement::Rename(j) => {
                    // x_i in the template is being renamed to x_j in the result.
                    let next_open_var = result_arg_types.len() as AtomId;
                    if j < &next_open_var {
                        // Check that the type matches
                        if template.arg_types[i] != result_arg_types[*j as usize] {
                            panic!(
                                "Type mismatch: {} != {}",
                                template.arg_types[i], result_arg_types[*j as usize]
                            );
                        }
                    } else if j == &next_open_var {
                        // This is the first time we've seen this variable
                        result_arg_types.push(template.arg_types[i]);
                    } else {
                        panic!("bad variable numbering");
                    }
                }
                Replacement::Expand(term) => {
                    // x_i in the template is being replaced with a term
                    let term_info = self.get_term_info(term.term);
                    for (j, k) in term.var_map.iter().enumerate() {
                        // x_j in the template is being renamed to x_k in the result.
                        let next_open_var = result_arg_types.len() as AtomId;
                        if k < &next_open_var {
                            // Check that the type matches
                            let expected_type = result_arg_types[*k as usize];
                            if term_info.arg_types[j] != expected_type {
                                panic!(
                                    "Type mismatch: {} != {}",
                                    term_info.arg_types[j], expected_type
                                );
                            }
                        } else if k == &next_open_var {
                            // This is the first time we've seen this variable
                            result_arg_types.push(term_info.arg_types[j]);
                        } else {
                            panic!("bad variable numbering");
                        }
                    }
                }
            }
        }

        // Insert the new stuff into the graph
        let edge_id = self.edges.len() as EdgeId;
        let term_id = self.terms.len() as TermId;
        let term_type = template.term_type;
        let canonical = CanonicalForm::Edge(edge_id);
        let var_map: Vec<AtomId> = (0..result_arg_types.len() as AtomId).collect();
        let result = TermInstance {
            term: term_id,
            var_map,
        };

        let term_info = TermInfo {
            term_type,
            arg_types: result_arg_types,
            adjacent: std::iter::once(edge_id).collect(),
            canonical,
        };
        let edge_info = EdgeInfo {
            key: key.clone(),
            result,
        };

        self.terms.push(term_info);
        self.edges.push(edge_info);
        self.edgemap.insert(key, edge_id);

        &self.edges[edge_id as usize].result
    }

    // Does a substitution with the given template and replacements.
    // This does not have to be normalized.
    pub fn replace(
        &mut self,
        template: &TermInstance,
        replacements: &Vec<Replacement>,
    ) -> TermInstance {
        // The overall strategy is to normalize the replacements, do the substitution with
        // the graph, and then map from new ids back to old ones.
        let (new_replacements, new_to_old) = normalize_replacements(&replacements);
        let new_term = self.insert_edge(EdgeKey {
            template: template.term,
            replacements: new_replacements,
        });
        let var_map = new_term
            .var_map
            .iter()
            .map(|i| new_to_old[*i as usize])
            .collect();
        TermInstance {
            term: new_term.term,
            var_map,
        }
    }

    // Inserts a new term, or returns the existing term if there is one.
    pub fn insert_term(&mut self, term: &Term) -> TermInstance {
        todo!("insert_term");
    }

    pub fn extract_term(&self, instance: &TermInstance) -> Term {
        todo!("extract_term");
    }
}
