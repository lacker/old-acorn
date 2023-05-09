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
// varmap[i] = j means that TermInstance replaces x_i with x_j.
// So for example to represent a TermInstance:
//   foo(x4, x0)
// we would use:
//   term: foo(x0, x1)
//   varmap: [4, 0]
// The length of varmap must be the same as arg_types.
// No two variables should be named the same thing.
pub struct TermInstance {
    term: TermId,
    var_map: Vec<AtomId>,
}

// An edge represents a single substitution.
// All variables get renamed, and some in the template can get replaced.
// For example:
// template = add(x0, x1)
// replacement = mul(x0, x1)
pub struct EdgeInfo {
    // The base term that will be substituted into
    template: TermId,

    // variable i in template gets renamed to variable var_map[i] after substitution.
    // "None" means "replace with the replacement"
    template_var_map: Vec<Option<AtomId>>,

    // variable i in replacement gets renamed to variable varmap[i]
    replacement: TermId,
    replacement_var_map: Vec<AtomId>,

    // What we get.
    // The number of variables in the result can be different, even for edges that share the same
    // template and replacement, when the var maps are different.
    result: TermId,
    result_num_vars: AtomId,
}
pub type EdgeId = u32;

impl EdgeInfo {
    // Check whether an edge matches two instances.
    // This fails if the instances are using term indexing in a way that doesn't match this edge.
    // If it succeeds, it returns a map of (var index -> instance index) usable to construct a
    // TermInstance we get by following this edge.
    // position is relative to the instance.
    fn matches(
        &self,
        template_instance: &TermInstance,
        position: AtomId,
        replacement_instance: &TermInstance,
    ) -> Option<Vec<AtomId>> {
        // Leave a "None" in any entry when we don't know what it is yet
        let mut output_var_map: Vec<Option<AtomId>> = vec![None; self.result_num_vars as usize];

        // Check which variables in the output come from the template
        assert_eq!(self.template, template_instance.term);
        assert_eq!(self.template_var_map.len(), template_instance.var_map.len());
        for (i, instance_i) in template_instance.var_map.iter().enumerate() {
            // Consider variable i in the underlying template, which is called instance_i
            // in this instance.
            if let Some(template_var) = self.template_var_map[i] {
                // The edge renames it to template_var in the output.
                // Thus our output instance should have output_var_map[instance_i] = template_var.
                if let Some(output_var) = output_var_map[*instance_i as usize] {
                    // If we already have a value for this variable, it should match.
                    if output_var != template_var {
                        return None;
                    }
                } else {
                    // Otherwise, we should set it.
                    output_var_map[*instance_i as usize] = Some(template_var);
                }
            } else {
                // The edge thinks that variable i should be replaced.
                // Thus instance_i should be position.
                if *instance_i != position {
                    return None;
                }
            }
        }

        // Check which variables in the output come from the replacement
        assert_eq!(self.replacement, replacement_instance.term);
        assert_eq!(
            self.replacement_var_map.len(),
            replacement_instance.var_map.len()
        );
        for (i, instance_i) in replacement_instance.var_map.iter().enumerate() {
            // Consider variable i n the underlying replacement, which is called instance_i
            // in this instance.
            // The edge renames it to replacement_var_map[i] in the output.
            let replacement_var = self.replacement_var_map[i];
            if let Some(output_var) = output_var_map[*instance_i as usize] {
                // If we already have a value for this variable, it should match.
                if output_var != replacement_var {
                    return None;
                }
            } else {
                // Otherwise, we should set it.
                output_var_map[*instance_i as usize] = Some(replacement_var);
            }
        }

        // To be a valid output map, every variable should be set.
        let mut answer = vec![];
        for (i, output_var) in output_var_map.iter().enumerate() {
            if let Some(output_var) = output_var {
                answer.push(*output_var);
            } else {
                return None;
            }
        }
        Some(answer)
    }
}

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
    edgemap: FxHashMap<(TermId, TermId), Vec<EdgeId>>,
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

    // An instance with the variables numbered in standard order.
    pub fn instance(&self, term: TermId) -> TermInstance {
        let num_vars = self.get_term_info(term).arg_types.len();
        let varmap: Vec<AtomId> = (0..num_vars).map(|i| i as AtomId).collect();
        TermInstance {
            term,
            var_map: varmap,
        }
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
        // Check if any existing edge covers this case
        let key = (template.term, replacement.term);
        if let Some(edges) = self.edgemap.get(&key) {
            for edge_id in edges {
                let edge = &self.edges[*edge_id as usize];
                if let Some(var_map) = edge.matches(template, position, replacement) {
                    return TermInstance {
                        term: edge.result,
                        var_map,
                    };
                }
            }
        }

        // We need to create a new term.
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
