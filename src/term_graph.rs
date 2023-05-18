use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::{fmt, mem};

use fxhash::FxHashMap;
use nohash_hasher::BuildNoHashHasher;

use crate::atom::{Atom, AtomId};
use crate::specializer::Specializer;
use crate::term::Term;
use crate::type_space::TypeId;

// The TermInfo stores information about an abstract term.
// The idea behind the abstract term is that if we know two terms are identical, like:
//   double(x)
//   add(x, x)
// then we can store them as the same abstract term. Instead of rewriting terms, we can
// merge nodes in our graph of abstract terms. If we are careful about always merging the
// "smaller" node into the "larger" one, we can do these merges cheaply (amortized).
//
// Note that an abstract term does not have a "head", so its term_type is the type
// that it has after all the args are replaced with substitutions.
#[derive(Debug)]
pub struct TermInfo {
    term_type: TypeId,
    arg_types: Vec<TypeId>,

    // All edges that touch this term
    adjacent: HashSet<EdgeId, BuildNoHashHasher<EdgeId>>,

    // All atom keys that lead to this term
    atom_keys: Vec<(Atom, u8)>,

    // The canonical way to produce this term.
    canonical: CanonicalForm,
}
pub type TermId = u32;

// The canonical form of a term can be:
//   a plain atom
//   a way of recursively constructing this term
//   a generic template for a type like x0(x1, x2) with no items specified
#[derive(Debug)]
enum CanonicalForm {
    Atom(Atom),
    Edge(EdgeId),
    TypeTemplate(TypeId),
}

// Information about how an atom gets turned into a term.
// Each atom has a default expansion, represented by term, but we also
// need to track the type of the atom itself, so that we know how to extract it.
pub struct AtomInfo {
    head_type: TypeId,
    term: TermInstance,
}

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

fn invert_var_map(var_map: &Vec<AtomId>) -> Vec<AtomId> {
    let invalid = var_map.len() as AtomId;
    let mut result = vec![invalid; var_map.len()];
    for (i, &var) in var_map.iter().enumerate() {
        if result[var as usize] != invalid {
            panic!("Duplicate variable in var_map");
        }
        result[var as usize] = i as AtomId;
    }
    result
}

// Composes two var_maps by applying the left one first, then the right one.
fn compose_var_maps(left: &Vec<AtomId>, right: &Vec<AtomId>) -> Vec<AtomId> {
    left.iter().map(|&var| right[var as usize]).collect()
}

impl fmt::Display for TermInstance {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "t{}(", self.term)?;
        for (i, &var) in self.var_map.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "x{} -> x{}", i, var)?;
        }
        write!(f, ")")
    }
}

impl TermInstance {
    // Panics if there is a logical inconsistency
    pub fn check(&self) {
        invert_var_map(&self.var_map);
    }

    // Replaces any use of old_term_id with a new term instance.
    fn replace_term_id(&self, old_term_id: TermId, new_term: &TermInstance) -> TermInstance {
        if self.term != old_term_id {
            return self.clone();
        }
        TermInstance {
            term: new_term.term,
            var_map: compose_var_maps(&new_term.var_map, &self.var_map),
        }
    }
}

// The different ways to replace a single variable in a substitution.
// Either we rename the variable, or we expand it into a different term.
// "Do-nothing" replacements are represented by a Rename with the same index.
//
// "Any" is a special case where it doesn't matter what we replace this variable with,
// it always results in the same thing.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Replacement {
    Rename(AtomId),
    Expand(TermInstance),
}

impl fmt::Display for Replacement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Replacement::Rename(var) => write!(f, "x{}", var),
            Replacement::Expand(term) => write!(f, "{}", term),
        }
    }
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

    pub fn assert_is_expansion(self) -> TermInstance {
        match self {
            Replacement::Rename(_) => panic!("Expected an expansion, got a rename"),
            Replacement::Expand(term) => term,
        }
    }

    fn replace_term_id(&self, old_term_id: TermId, new_term: &TermInstance) -> Replacement {
        match self {
            Replacement::Rename(var) => Replacement::Rename(*var),
            Replacement::Expand(term) => {
                Replacement::Expand(term.replace_term_id(old_term_id, new_term))
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

impl fmt::Display for EdgeKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "t{}[", self.template)?;
        for (i, replacement) in self.replacements.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "x{} -> {}", i, replacement)?;
        }
        write!(f, "]")
    }
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

        if replacements_are_noop(&self.replacements) {
            panic!("key is a no-op");
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
    let mut new_to_old: Vec<AtomId> = vec![];
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

// Returns whether this list of replacements is the noop that renames x_i to x_i for all i.
fn replacements_are_noop(replacements: &Vec<Replacement>) -> bool {
    replacements
        .iter()
        .enumerate()
        .all(|(i, r)| *r == Replacement::Rename(i as AtomId))
}

#[derive(Debug)]
pub struct EdgeInfo {
    // The parameters that determine the substitution
    key: EdgeKey,

    // The result of the substitution
    result: TermInstance,
}
pub type EdgeId = u32;

impl fmt::Display for EdgeInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} -> {}", self.key, self.result)
    }
}

impl EdgeInfo {
    fn adjacent_terms(&self) -> Vec<TermId> {
        let mut terms = vec![];
        terms.push(self.key.template);
        terms.push(self.result.term);
        for replacement in &self.key.replacements {
            if let Replacement::Expand(term) = replacement {
                terms.push(term.term);
            }
        }
        terms
    }

    // Create a new edge with all use of TermId replaced by the new term instance
    fn replace_term_id(&self, old_term_id: TermId, new_term: &TermInstance) -> EdgeInfo {
        // The result and the replacements are relatively straightforward, we just recurse.
        let new_result = self.result.replace_term_id(old_term_id, new_term);
        let new_replacements: Vec<_> = self
            .key
            .replacements
            .iter()
            .map(|replacement| replacement.replace_term_id(old_term_id, new_term))
            .collect();

        if self.key.template != old_term_id {
            // Great, we're done
            return EdgeInfo {
                key: EdgeKey {
                    template: self.key.template,
                    replacements: new_replacements,
                },
                result: new_result,
            };
        }

        // Replacing the template is trickier, because we could be reordering
        // the variables, and thus the canonical form could be changing.
        if self.key.replacements.len() < new_term.var_map.len() {
            panic!(
                "replacing term {} with {} is increasing the number of template variables",
                old_term_id, new_term
            );
        }
        let mut reordered_replacements = vec![None; new_term.var_map.len()];

        for (i, j) in new_term.var_map.iter().enumerate() {
            // x_i in the old term is x_j in the new term.
            reordered_replacements[*j as usize] = Some(self.key.replacements[i].clone());
        }

        // We shouldn't have missed any
        let unwrapped_replacements: Vec<_> = reordered_replacements
            .into_iter()
            .map(|replacement| replacement.unwrap())
            .collect();

        // We need to renormalize because reordering may have denormalized it
        let (normalized, new_to_old) = normalize_replacements(&unwrapped_replacements);
        let var_map = new_result
            .var_map
            .iter()
            .map(|&v| new_to_old[v as usize])
            .collect();

        EdgeInfo {
            key: EdgeKey {
                template: new_term.term,
                replacements: normalized,
            },
            result: TermInstance {
                term: new_result.term,
                var_map,
            },
        }
    }
}

enum TermInfoReference {
    TermInfo(TermInfo),
    Replaced(TermInstance),
}

impl TermInfoReference {
    pub fn is_there(&self) -> bool {
        match self {
            TermInfoReference::TermInfo(_) => true,
            TermInfoReference::Replaced(_) => false,
        }
    }
}

pub struct TermGraph {
    // We replace elements of terms or edges with None when they are replaced with
    // an identical one that we have chosen to be the canonical one.
    terms: Vec<TermInfoReference>,
    edges: Vec<Option<EdgeInfo>>,

    // We expand non-variable atoms into different terms depending on the number of
    // arguments they have. This lets us handle, for example, "add(2, 3)" and "reduce(add, mylist)".
    // The second parameter to the index is the number of arguments.
    atoms: HashMap<(Atom, u8), AtomInfo>,

    // Templates that let us expand terms where the head is a variable.
    // Keyed on the type of the head and the number of arguments.
    // This lets us represent terms like x0(x1, x2).
    type_templates: HashMap<(TypeId, u8), TermId>,

    // Maps (template, replacement) -> edges
    edgemap: FxHashMap<EdgeKey, EdgeId>,
}

impl TermGraph {
    pub fn new() -> TermGraph {
        TermGraph {
            terms: Vec::new(),
            edges: Vec::new(),
            atoms: HashMap::default(),
            type_templates: HashMap::default(),
            edgemap: HashMap::default(),
        }
    }

    fn has_term_info(&self, term: TermId) -> bool {
        self.terms[term as usize].is_there()
    }

    fn get_term_info_ref(&self, term: TermId) -> &TermInfoReference {
        &self.terms[term as usize]
    }

    // Does not handle the case where a TermInfo was replaced
    fn get_term_info(&self, term: TermId) -> &TermInfo {
        match self.get_term_info_ref(term) {
            TermInfoReference::TermInfo(info) => info,
            TermInfoReference::Replaced(_) => panic!("Term {} has been replaced", term),
        }
    }

    fn mut_term_info(&mut self, term: TermId) -> &mut TermInfo {
        match &mut self.terms[term as usize] {
            TermInfoReference::TermInfo(info) => info,
            TermInfoReference::Replaced(_) => panic!("Term {} has been replaced", term),
        }
    }

    fn has_edge_info(&self, edge: EdgeId) -> bool {
        self.edges[edge as usize].is_some()
    }

    fn get_edge_info(&self, edge: EdgeId) -> &EdgeInfo {
        &self.edges[edge as usize].as_ref().unwrap()
    }

    fn set_edge_info(&mut self, edge: EdgeId, info: EdgeInfo) {
        self.edges[edge as usize] = Some(info);
    }

    fn take_edge_info(&mut self, edge: EdgeId) -> EdgeInfo {
        self.edges[edge as usize].take().unwrap()
    }

    // An EdgeKey represents a substitution. It can exist before the analogous edge
    // in the graph exists.
    // This method creates the analogous edge and term if they don't already exist.
    // Returns the term that this edge leads to.
    // Should not be called on noop keys or unnormalized keys.
    // The type of the output is the same as the type of the key's template.
    fn expand_edge_key(&mut self, key: EdgeKey) -> &TermInstance {
        // Check if this edge is already in the graph
        if let Some(edge_id) = self.edgemap.get(&key) {
            return &self.get_edge_info(*edge_id).result;
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

        // Create the info structs
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
            atom_keys: vec![],
            canonical,
        };
        let edge_info = EdgeInfo {
            key: key.clone(),
            result,
        };

        // Insert everything into the graph
        self.terms.push(TermInfoReference::TermInfo(term_info));
        self.mut_term_info(key.template).adjacent.insert(edge_id);
        for r in &key.replacements {
            if let Replacement::Expand(term) = r {
                self.mut_term_info(term.term).adjacent.insert(edge_id);
            }
        }
        self.edges.push(Some(edge_info));
        self.edgemap.insert(key, edge_id);

        &self.get_edge_info(edge_id).result
    }

    // Does a substitution with the given template and replacements.
    // Creates new entries in the term graph if necessary.
    // This does not have to be normalized.
    fn replace_in_term_id(
        &mut self,
        template: TermId,
        replacements: &Vec<Replacement>,
    ) -> TermInstance {
        // The overall strategy is to normalize the replacements, do the substitution with
        // the graph, and then map from new ids back to old ones.
        let (new_replacements, new_to_old) = normalize_replacements(&replacements);
        if replacements_are_noop(&new_replacements) {
            // No need to even do a substitution
            return TermInstance {
                term: template,
                var_map: new_to_old,
            };
        }
        let new_term = self.expand_edge_key(EdgeKey {
            template,
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

    fn replace_in_term_instance(
        &mut self,
        template: &TermInstance,
        replacements: &Vec<Replacement>,
    ) -> TermInstance {
        // We need to reorder and/or subset the replacements so that they are relative to the
        // underlying term id, rather than the term instance
        let mut new_replacements = vec![];
        for v in &template.var_map {
            // We don't need an explicit index i, but x_i in the term is x_v in the instance.
            new_replacements.push(replacements[*v as usize].clone());
        }
        self.replace_in_term_id(template.term, &new_replacements)
    }

    // Inserts a new term, or returns the existing term if there is one.
    // A Term can be just a single renumbered variable, which the graph doesn't count
    // as a separate term, so we have to convert a Term into a Replacement.
    pub fn insert_term(&mut self, term: &Term) -> Replacement {
        if term.is_true() {
            panic!("True should not be a separate node in the term graph")
        }
        if let Some(i) = term.atomic_variable() {
            return Replacement::Rename(i);
        }

        // Handle the case where the head is a variable
        if let Atom::Variable(i) = term.head {
            let type_template: u32 = *self
                .type_templates
                .entry((term.head_type, term.args.len() as u8))
                .or_insert_with(|| {
                    let type_template = self.terms.len() as TermId;
                    // The head of the term counts as one of the args in the template
                    let mut arg_types = vec![term.head_type];
                    arg_types.extend(term.args.iter().map(|a| a.term_type));
                    self.terms.push(TermInfoReference::TermInfo(TermInfo {
                        term_type: term.term_type,
                        arg_types,
                        adjacent: HashSet::default(),
                        atom_keys: vec![],
                        canonical: CanonicalForm::TypeTemplate(term.head_type),
                    }));
                    type_template
                });
            let mut replacements = vec![Replacement::Rename(i)];
            for arg in &term.args {
                replacements.push(self.insert_term(arg));
            }
            return Replacement::Expand(self.replace_in_term_id(type_template, &replacements));
        }

        // Handle the (much more common) case where the head is not a variable
        let atom_key = (term.head, term.args.len() as u8);
        if !self.atoms.contains_key(&atom_key) {
            let head_id = self.terms.len() as TermId;
            self.terms.push(TermInfoReference::TermInfo(TermInfo {
                term_type: term.term_type,
                arg_types: term.args.iter().map(|a| a.term_type).collect(),
                adjacent: HashSet::default(),
                atom_keys: vec![atom_key.clone()],
                canonical: CanonicalForm::Atom(term.head),
            }));
            let term_instance = TermInstance {
                term: head_id,
                var_map: (0..term.args.len() as AtomId).collect(),
            };
            let atom_info = AtomInfo {
                term: term_instance.clone(),
                head_type: term.head_type,
            };
            self.atoms.insert(atom_key, atom_info);
        };

        // Substitute the arguments into the head
        let term_instance = self.atoms.get(&atom_key).unwrap().term.clone();
        let replacements: Vec<_> = term.args.iter().map(|a| self.insert_term(a)).collect();
        Replacement::Expand(self.replace_in_term_instance(&term_instance, &replacements))
    }

    pub fn extract_term_id(&self, term_id: TermId) -> Term {
        let term_info = self.get_term_info(term_id);
        let edge_info = match term_info.canonical {
            CanonicalForm::Atom(a) => {
                let atom_key = (a, term_info.arg_types.len() as u8);
                let atom_info = match self.atoms.get(&atom_key) {
                    Some(atom_info) => atom_info,
                    None => panic!("atom key {:?} cannot be extracted", atom_key),
                };
                return Term {
                    term_type: term_info.term_type,
                    head_type: atom_info.head_type,
                    head: a,
                    args: term_info
                        .arg_types
                        .iter()
                        .enumerate()
                        .map(|(i, t)| Term::atom(*t, Atom::Variable(i as AtomId)))
                        .collect(),
                };
            }
            CanonicalForm::Edge(edge_id) => self.get_edge_info(edge_id),
            CanonicalForm::TypeTemplate(type_id) => {
                return Term {
                    term_type: term_info.term_type,
                    head_type: type_id,
                    head: Atom::Variable(0),
                    args: (0..(term_info.arg_types.len() - 1) as AtomId)
                        .map(|i| Term::atom(type_id, Atom::Variable(i + 1)))
                        .collect(),
                };
            }
        };

        // Construct a Term according to the information provided by the edge
        let template = self.extract_term_id(edge_info.key.template);
        let mut s = Specializer::new();
        for (i, r) in edge_info.key.replacements.iter().enumerate() {
            let i = i as AtomId;
            match r {
                Replacement::Rename(j) => {
                    // We want the specializer to replace x_i with x_j, which is slightly annoying
                    // because it wants to know the type.
                    if let Some(var_type) = template.var_type(i) {
                        assert!(s.match_var(i, &Term::atom(var_type, Atom::Variable(*j))));
                    } else {
                        panic!("cannot rename x{} -> x{} in {}", i, j, template);
                    }
                }
                Replacement::Expand(t) => {
                    let t = self.extract_term_id(t.term).remap_variables(&t.var_map);
                    assert!(s.match_var(i, &t));
                }
            }
        }
        let unmapped_term = s.specialize(&template);
        unmapped_term.remap_variables(&edge_info.result.var_map)
    }

    pub fn extract_term_instance(&self, instance: &TermInstance) -> Term {
        let unmapped_term = self.extract_term_id(instance.term);
        let answer = unmapped_term.remap_variables(&instance.var_map);
        answer
    }

    // Replaces all references to old_term_id with references to new_term.
    // The caller should be sure that old_term_id has not been replaced already.
    // If we discover more pairs of terms that should be identified in the process of doing
    // this replacement, push them onto pending_identification.
    fn replace_term_id(
        &mut self,
        old_term_id: TermId,
        new_term: &TermInstance,
        pending_identification: &mut Vec<(TermInstance, TermInstance)>,
    ) {
        let old_term_info_ref = mem::replace(
            &mut self.terms[old_term_id as usize],
            TermInfoReference::Replaced(new_term.clone()),
        );
        let old_term_info = match old_term_info_ref {
            TermInfoReference::TermInfo(t) => t,
            TermInfoReference::Replaced(_) => panic!("term {} already replaced", old_term_id),
        };

        if let CanonicalForm::TypeTemplate(_) = old_term_info.canonical {
            panic!("how could we be updating a type template?");
        }

        // Update information for any atoms that are primarily represented by this term
        for atom_key in &old_term_info.atom_keys {
            let atom_info = self.atoms.get_mut(atom_key).unwrap();
            atom_info.term = atom_info.term.replace_term_id(old_term_id, new_term);
        }

        // Update all edges that touch this term
        for edge_id in &old_term_info.adjacent {
            let old_edge_info = self.take_edge_info(*edge_id);
            let new_edge_info = old_edge_info.replace_term_id(old_term_id, new_term);
            if old_edge_info.key == new_edge_info.key {
                // We didn't change the key. Just update the edge info.
                self.set_edge_info(*edge_id, new_edge_info);
                continue;
            }

            // We did change the key.
            if let Some(duplicate_edge_id) = self.edgemap.get(&new_edge_info.key) {
                let duplicate_edge_info = self.get_edge_info(*duplicate_edge_id);
                // new_edge_info and duplicate_edge_info are the same edge, but
                // they're going to different terms.
                // This means we need to identify the terms.
                pending_identification.push((
                    new_edge_info.result.clone(),
                    duplicate_edge_info.result.clone(),
                ));
            }

            // We're good to go. Update the edge.
            self.edgemap.insert(new_edge_info.key.clone(), *edge_id);
            self.set_edge_info(*edge_id, new_edge_info);
            self.edgemap.remove(&old_edge_info.key);
        }

        // new_term is now adjacent to all these updated edges
        let new_term_info = self.mut_term_info(new_term.term);
        new_term_info.adjacent.extend(old_term_info.adjacent);
        new_term_info.atom_keys.extend(old_term_info.atom_keys);
    }

    // Applies any replacements that have happened for the given term.
    pub fn apply_replacements(&self, term: TermInstance) -> TermInstance {
        let replacement = match self.get_term_info_ref(term.term) {
            TermInfoReference::TermInfo(_) => return term,
            TermInfoReference::Replaced(r) => r,
        };
        let updated = term.replace_term_id(term.term, replacement);
        self.apply_replacements(updated)
    }

    // The term we most want to keep compares as the largest in the keeping order.
    fn keeping_order(&self, left: TermId, right: TermId) -> Ordering {
        let left_term_info = self.get_term_info(left);
        let right_term_info = self.get_term_info(right);

        // If one of the terms has more arguments, it is less keepable.
        let arg_len_cmp = right_term_info
            .arg_types
            .len()
            .cmp(&left_term_info.arg_types.len());
        if arg_len_cmp != Ordering::Equal {
            return arg_len_cmp;
        }

        // If one of the terms has more adjacent edges, it is more keepable.
        let adj_cmp = left_term_info
            .adjacent
            .len()
            .cmp(&right_term_info.adjacent.len());
        if adj_cmp != Ordering::Equal {
            return adj_cmp;
        }

        // If all else fails, the lower term ids are more keepable.
        right.cmp(&left)
    }

    pub fn identify_terms(&mut self, instance1: TermInstance, instance2: TermInstance) {
        let mut pending_identification = vec![];
        pending_identification.push((instance1, instance2));

        while let Some((instance1, instance2)) = pending_identification.pop() {
            let instance1 = self.apply_replacements(instance1);
            let instance2 = self.apply_replacements(instance2);
            if instance1.term == instance2.term {
                if instance1.var_map == instance2.var_map {
                    // Nothing to do
                    return;
                }
                todo!("handle permutations of variables");
            }

            // Discard the term that we least want to keep
            let (discard, keep) = match self.keeping_order(instance1.term, instance2.term) {
                Ordering::Less => (instance1, instance2),
                Ordering::Greater => (instance2, instance1),
                Ordering::Equal => {
                    panic!("flow control error, code should not reach here");
                }
            };

            // Find a TermInstance equal to the term to be discarded
            let new_var_map = compose_var_maps(&keep.var_map, &invert_var_map(&discard.var_map));
            let new_instance = TermInstance {
                term: keep.term,
                var_map: new_var_map,
            };

            self.replace_term_id(discard.term, &new_instance, &mut pending_identification);
        }
    }

    // A linear pass through the graph checking that everything is consistent.
    pub fn check(&self) {
        println!();
        let mut all_terms: HashSet<String> = HashSet::new();
        for term_id in 0..self.terms.len() {
            let term_id = term_id as TermId;
            if !self.has_term_info(term_id) {
                println!("term {} has been collapsed", term_id);
                continue;
            }
            let term_info = self.get_term_info(term_id);
            for edge_id in &term_info.adjacent {
                if !self.has_edge_info(*edge_id) {
                    panic!("term {} refers to collapsed edge {}", term_id, edge_id);
                }
                let edge_info = self.get_edge_info(*edge_id);
                if !edge_info.adjacent_terms().contains(&term_id) {
                    panic!(
                        "term {} thinks it is adjacent to edge {} but not vice versa",
                        term_id, edge_id
                    );
                }
                if term_id == edge_info.key.template {
                    if edge_info.key.replacements.len() != term_info.arg_types.len() {
                        panic!(
                            "edge {} has template {:?} but arg lengths mismatch",
                            edge_info, term_info,
                        );
                    }
                }
                if term_id == edge_info.result.term {
                    assert_eq!(edge_info.result.var_map.len(), term_info.arg_types.len());
                }
            }

            let term = self.extract_term_id(term_id as TermId);
            let s = term.to_string();
            println!("term {}: {}", term_id, s);

            // This check can raise a false alarm with type templates, for which
            // different ones can stringify the same
            assert!(!all_terms.contains(&s), "duplicate term: {}", s);

            all_terms.insert(s);
        }

        for (key, edge_id) in self.edgemap.iter() {
            key.check();
            if !self.has_edge_info(*edge_id) {
                panic!("edge {} has been collapsed", edge_id);
            }
            let edge_info = self.get_edge_info(*edge_id);
            for term_id in edge_info.adjacent_terms().iter() {
                if !self.has_term_info(*term_id) {
                    panic!("edge {} refers to collapsed term {}", edge_info, term_id);
                }
                let term_info = self.get_term_info(*term_id);
                if !term_info.adjacent.contains(edge_id) {
                    panic!(
                        "edge {} thinks it is adjacent to term {} but not vice versa",
                        edge_info, term_id
                    );
                }
            }
        }

        for ((atom, num_args), atom_info) in self.atoms.iter() {
            if !self.has_term_info(atom_info.term.term) {
                panic!(
                    "atom ({}, {}) is represented by term {} which has been collapsed",
                    atom, num_args, atom_info.term
                );
            }
        }
    }

    pub fn parse(&mut self, term_string: &str) -> TermInstance {
        let term = Term::parse(term_string);
        let term_instance = self.insert_term(&term).assert_is_expansion();
        self.check();
        term_instance
    }

    pub fn check_identify_terms(&mut self, term1: &TermInstance, term2: &TermInstance) {
        self.identify_terms(term1.clone(), term2.clone());
        self.check();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn insert_and_extract(term_strings: &[&str]) {
        let mut g = TermGraph::new();
        for s in term_strings {
            println!("inserting {}", s);
            let ti = g.parse(s);
            println!("extracting {}", s);
            let output = g.extract_term_instance(&ti);
            let output_str = output.to_string();
            if s.to_string() != output_str {
                panic!("\ninput {} != output {}\n", s, output_str);
            }
            println!("  OK\n");
        }
    }

    #[test]
    fn test_graph_insert_and_extract() {
        insert_and_extract(&[
            "a0",
            "a1(x0)",
            "a1(x1)",
            "a2(x0, x1)",
            "a3(x0, x1, x2)",
            "a2(x3, x2)",
            "a2(a2(x0, x1), x2)",
            "a2(x1, x1)",
            "a3(x1, x3, x1)",
            "a1(a1(x1))",
            "a2(x0, a1(x1))",
            "a2(a2(x1, x0), a2(x0, x2))",
            "a2(a2(x0, x2), a2(x1, x0))",
            "a3(x0, a3(x1, a3(x0, x1, x0), a0), x1)",
        ]);
    }

    #[test]
    fn test_functional_arguments() {
        insert_and_extract(&["a0(x0)", "a0"]);
    }

    #[test]
    fn test_variable_heads() {
        insert_and_extract(&[
            "x0(x1)",
            "x0(x1(x2))",
            "x3(x1(x2), x1(a0))",
            "x4(a1(x8, x3), x0(x1), x0(a2))",
        ]);
    }

    #[test]
    fn test_identifying_terms() {
        let mut g = TermGraph::new();
        let a0 = g.parse("a0(a3)");
        let a1 = g.parse("a1(a3)");
        g.check_identify_terms(&a0, &a1);
        let a2a0 = g.parse("a2(a0(a3))");
        let a2a1 = g.parse("a2(a1(a3))");
        assert_eq!(a2a0, a2a1);
    }

    #[test]
    fn test_updating_constructor() {
        let mut g = TermGraph::new();
        let a0 = g.parse("a0");
        let a1 = g.parse("a1");
        g.check_identify_terms(&a0, &a1);
        let a2a0 = g.parse("a2(a0)");
        let a2a1 = g.parse("a2(a1)");
        assert_eq!(a2a0, a2a1);
    }

    #[test]
    fn test_apply_replacements() {
        let mut g = TermGraph::new();
        let a0 = g.parse("a0(x0, x1)");
        let a1 = g.parse("a1(x1, x0)");
        g.check_identify_terms(&a0, &a1);
        let rep0 = g.apply_replacements(a0);
        let rep1 = g.apply_replacements(a1);
        assert_eq!(&rep0, &rep1);
    }

    #[test]
    fn test_duplicating_edge() {
        let mut g = TermGraph::new();
        let a0 = g.parse("a0");
        let a1 = g.parse("a1");
        g.parse("a2(a0)");
        g.parse("a2(a1)");
        g.check_identify_terms(&a0, &a1);
        let a2a0 = g.parse("a2(a0)");
        let a2a1 = g.parse("a2(a1)");
        assert_eq!(a2a0, a2a1);
    }

    #[test]
    fn test_multi_hop_term_identification() {
        let mut g = TermGraph::new();
        let a0 = g.parse("a0");
        let a1 = g.parse("a1");
        let a2 = g.parse("a2");
        let a3 = g.parse("a3");
        g.check_identify_terms(&a0, &a1);
        g.check_identify_terms(&a2, &a3);
        g.check_identify_terms(&a0, &a2);
        let a4a3 = g.parse("a4(a3)");
        let a4a1 = g.parse("a4(a1)");
        assert_eq!(a4a3, a4a1);
    }

    #[test]
    fn test_atom_identification() {
        let mut g = TermGraph::new();
        let a0x0x1 = g.parse("a0(x0, x1)");
        let a1x1x0 = g.parse("a1(x1, x0)");
        g.check_identify_terms(&a0x0x1, &a1x1x0);
        let a0a2a3 = g.parse("a0(a2, a3)");
        let a1a3a2 = g.parse("a1(a3, a2)");
        assert_eq!(a0a2a3, a1a3a2);
    }

    #[test]
    fn test_explicit_argument_collapse() {
        let mut g = TermGraph::new();
        let a0x0 = g.parse("a0(x0)");
        let a1 = g.parse("a1");
        g.check_identify_terms(&a0x0, &a1);
        let a0a2 = g.parse("a0(a2)");
        let a0a3 = g.parse("a0(a3)");
        assert_eq!(a0a2, a0a3);
    }

    #[test]
    fn test_template_collapse() {
        let mut g = TermGraph::new();
        let a0x0 = g.parse("a0(x0)");
        // Make the less concise term the more popular one
        g.parse("a0(a2)");
        let a1 = g.parse("a1");
        g.check_identify_terms(&a0x0, &a1);
        let a0a2 = g.parse("a0(a2)");
        let a0a3 = g.parse("a0(a3)");
        assert_eq!(a0a2, a0a3);
    }

    // #[test]
    // fn test_implicit_argument_collapse() {
    //     let mut g = TermGraph::new();
    //     let a0x0 = g.parse("a0(x0)");
    //     let a1x1 = g.parse("a1(x1)");
    //     g.check_identify_terms(&a0x0, &a1x1);
    //     let a0a2 = g.parse("a0(a2)");
    //     let a0a3 = g.parse("a0(a3)");
    //     assert_eq!(a0a2, a0a3);
    // }

    // #[test]
    // fn test_cyclic_argument_identification() {
    //     let mut g = TermGraph::new();
    //     let base = g.parse("a0(x0, x1, x2)");
    //     let rotated = g.parse("a0(x1, x2, x0)");
    //     g.check_identify_terms(&base, &rotated);

    //     let term1 = g.parse("a0(a1, a2, a3)");
    //     let term2 = g.parse("a0(a2, a3, a1)");
    //     assert_eq!(term1, term2);

    //     let term3 = g.parse("a0(a3, a1, a2)");
    //     assert_eq!(term1, term3);

    //     let term4 = g.parse("a0(a1, a3, a2)");
    //     assert_ne!(term1, term4);

    //     let term5 = g.parse("a0(a3, a2, a1)");
    //     assert_eq!(term4, term5);

    //     let term6 = g.parse("a0(a2, a1, a3)");
    //     assert_eq!(term4, term6);
    // }
}
