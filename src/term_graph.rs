use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::{fmt, mem};

use fxhash::FxHashMap;
use nohash_hasher::BuildNoHashHasher;

use crate::atom::{Atom, AtomId};
use crate::specializer::Specializer;
use crate::term::Term;
use crate::type_space::{self, TypeId};

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

    // Whether this term can be produced by a type template.
    type_template: Option<TypeId>,

    // A term of a given depth can be created from terms of only smaller depth.
    // A depth zero term can be created from atoms.
    depth: u32,
}
pub type TermId = u32;

// Information about how an atom gets turned into a term.
// Each atom has a default expansion, represented by term, but we also
// need to track the type of the atom itself, so that we know how to extract it.
pub struct AtomInfo {
    head_type: TypeId,
    term: TermInstance,
}

// TermInfo normalizes across all namings of the input variables.
// A MappedTerm represents a particular ordering.
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
pub struct MappedTerm {
    term_id: TermId,
    var_map: Vec<AtomId>,
}

// A particular instance of a term can either be a mapped term from the graph, or a single variable.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum TermInstance {
    Mapped(MappedTerm),
    Variable(TypeId, AtomId),
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
    replacements: Vec<TermInstance>,
}

#[derive(Debug)]
pub struct EdgeInfo {
    // The parameters that determine the substitution
    key: EdgeKey,

    // The result of the substitution
    result: TermInstance,
}
pub type EdgeId = u32;

// The Operation is used to represent a change to the graph that can cascade into a series of other
// changes.
// This can either be adding a new edge, or identifying two terms with each other.
enum Operation {
    InsertEdge(EdgeInfo),
    IdentifyTerms(TermInstance, TermInstance),
}

enum TermInfoReference {
    TermInfo(TermInfo),
    Replaced(TermInstance),
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

// -----------------------------------------------------------------------------------------------
//                       implementation
// -----------------------------------------------------------------------------------------------

// Composes two var_maps by applying the left one first, then the right one.
fn compose_var_maps(left: &Vec<AtomId>, right: &Vec<AtomId>) -> Vec<AtomId> {
    left.iter().map(|&var| right[var as usize]).collect()
}

impl fmt::Display for MappedTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "t{}(", self.term_id)?;
        for (i, &var) in self.var_map.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "x{} -> x{}", i, var)?;
        }
        write!(f, ")")
    }
}

impl MappedTerm {
    // Replaces any use of old_term_id with a new term instance.
    fn replace_term_id(&self, old_term_id: TermId, new_term: &TermInstance) -> TermInstance {
        if self.term_id != old_term_id {
            return TermInstance::Mapped(self.clone());
        }
        match new_term {
            TermInstance::Mapped(new_term) => TermInstance::mapped(
                new_term.term_id,
                compose_var_maps(&new_term.var_map, &self.var_map),
            ),
            TermInstance::Variable(var_type, i) => {
                let new_index = self.var_map[*i as usize];
                TermInstance::Variable(*var_type, new_index)
            }
        }
    }
}

impl fmt::Display for TermInstance {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermInstance::Mapped(term) => write!(f, "{}", term),
            TermInstance::Variable(_, var_id) => write!(f, "x{}", var_id),
        }
    }
}

impl TermInstance {
    fn mapped(term_id: TermId, var_map: Vec<AtomId>) -> TermInstance {
        TermInstance::Mapped(MappedTerm { term_id, var_map })
    }

    // Calls f on each variable id used by this term
    fn for_var(&self, f: &mut impl FnMut(&AtomId)) {
        match self {
            TermInstance::Mapped(term) => {
                for &var in &term.var_map {
                    f(&var);
                }
            }
            TermInstance::Variable(_, var_id) => f(var_id),
        }
    }

    fn variable(&self) -> Option<AtomId> {
        match self {
            TermInstance::Mapped(_) => None,
            TermInstance::Variable(_, var_id) => Some(*var_id),
        }
    }

    fn term_id(&self) -> Option<TermId> {
        match self {
            TermInstance::Mapped(term) => Some(term.term_id),
            TermInstance::Variable(_, _) => None,
        }
    }

    fn forward_map_vars(&self, var_map: &Vec<AtomId>) -> TermInstance {
        match self {
            TermInstance::Mapped(term) => {
                TermInstance::mapped(term.term_id, compose_var_maps(&term.var_map, var_map))
            }
            TermInstance::Variable(term_type, var_id) => {
                TermInstance::Variable(*term_type, var_map[*var_id as usize])
            }
        }
    }

    fn backward_map_vars(&self, var_map: &Vec<AtomId>) -> TermInstance {
        match self {
            TermInstance::Mapped(term) => {
                let new_var_map = term
                    .var_map
                    .iter()
                    .map(|v| var_map.iter().position(|w| w == v).unwrap() as AtomId)
                    .collect();
                TermInstance::mapped(term.term_id, new_var_map)
            }
            TermInstance::Variable(term_type, v) => TermInstance::Variable(
                *term_type,
                var_map.iter().position(|w| w == v).unwrap() as AtomId,
            ),
        }
    }

    fn replace_term_id(&self, old_term_id: TermId, new_term: &TermInstance) -> TermInstance {
        match self {
            TermInstance::Mapped(term) => term.replace_term_id(old_term_id, new_term),
            TermInstance::Variable(_, _) => self.clone(),
        }
    }
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
            replacement.for_var(&mut |&var| {
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
            panic!("replacements are a noop");
        }
    }

    // Whether this is an edge that does nothing, taking the template to itself
    pub fn is_noop(&self) -> bool {
        replacements_are_noop(&self.replacements)
    }

    fn template_instance(&self) -> TermInstance {
        TermInstance::mapped(
            self.template,
            (0..self.replacements.len() as AtomId).collect(),
        )
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
fn normalize_replacements(replacements: &Vec<TermInstance>) -> (Vec<TermInstance>, Vec<AtomId>) {
    let mut new_replacements = vec![];
    let mut new_to_old: Vec<AtomId> = vec![];
    for r in replacements {
        match r {
            TermInstance::Variable(term_type, old_var) => {
                // Figure out the new id for this variable
                let new_var = match new_to_old.iter().position(|&v| v == *old_var) {
                    Some(i) => i,
                    None => {
                        let new_var = new_to_old.len();
                        new_to_old.push(*old_var);
                        new_var
                    }
                };
                new_replacements.push(TermInstance::Variable(*term_type, new_var as AtomId));
            }
            TermInstance::Mapped(old_term) => {
                let mut new_term = MappedTerm {
                    term_id: old_term.term_id,
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
                new_replacements.push(TermInstance::Mapped(new_term));
            }
        }
    }
    (new_replacements, new_to_old)
}

// Returns whether this list of replacements is the noop that renames x_i to x_i for all i.
fn replacements_are_noop(replacements: &Vec<TermInstance>) -> bool {
    replacements
        .iter()
        .enumerate()
        .all(|(i, r)| r.variable() == Some(i as AtomId))
}

impl fmt::Display for EdgeInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} -> {}", self.key, self.result)
    }
}

impl EdgeInfo {
    fn adjacent_terms(&self) -> Vec<TermId> {
        let mut terms = vec![];
        terms.push(self.key.template);
        if let Some(term_id) = self.result.term_id() {
            terms.push(term_id);
        }
        for replacement in &self.key.replacements {
            if let TermInstance::Mapped(term) = replacement {
                terms.push(term.term_id);
            }
        }
        terms
    }

    // Create a new edge with all use of TermId replaced by the new term instance.
    // This newly-created edge may be a no-op; the caller is responsible for handling that.
    fn replace_term_id(&self, old_term_id: TermId, new_term: &TermInstance) -> Operation {
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
            return Operation::InsertEdge(EdgeInfo {
                key: EdgeKey {
                    template: self.key.template,
                    replacements: new_replacements,
                },
                result: new_result,
            });
        }

        // We're replacing the template.
        let mapped_term = match new_term {
            TermInstance::Mapped(term) => term,
            TermInstance::Variable(_, var_id) => {
                let new_template = &new_replacements[*var_id as usize];
                // We want to identify new_template and new_result here.
                return Operation::IdentifyTerms(new_template.clone(), new_result);
            }
        };

        // Replacing the template is trickier, because we could be reordering
        // the variables, and thus the canonical form could be changing.
        if self.key.replacements.len() < mapped_term.var_map.len() {
            panic!(
                "replacing term {} with {} is increasing the number of template variables",
                old_term_id, mapped_term
            );
        }
        let mut reordered_replacements = vec![None; mapped_term.var_map.len()];

        for (i, j) in mapped_term.var_map.iter().enumerate() {
            // x_i in the old term is x_j in the new term.
            reordered_replacements[*j as usize] = Some(self.key.replacements[i].clone());
        }

        // We shouldn't have missed any
        let unwrapped_replacements: Vec<_> = reordered_replacements
            .into_iter()
            .map(|replacement| replacement.unwrap())
            .collect();

        Operation::new(mapped_term.term_id, unwrapped_replacements, new_result)
    }
}

impl Operation {
    // Normalizing can produce an edge, or it can just conclude that two term instances are the same
    fn new(template: TermId, replacements: Vec<TermInstance>, result: TermInstance) -> Operation {
        let (normalized, new_to_old) = normalize_replacements(&replacements);
        let normalized_key = EdgeKey {
            template,
            replacements: normalized,
        };
        let normalized_result = result.forward_map_vars(&new_to_old);

        if replacements_are_noop(&normalized_key.replacements) {
            // There's no edge here, we just want to identify two terms
            return Operation::IdentifyTerms(normalized_key.template_instance(), normalized_result);
        }

        Operation::InsertEdge(EdgeInfo {
            key: normalized_key,
            result: normalized_result,
        })
    }
}

impl TermInfoReference {
    pub fn is_there(&self) -> bool {
        match self {
            TermInfoReference::TermInfo(_) => true,
            TermInfoReference::Replaced(_) => false,
        }
    }
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
        let mut max_edge_depth = template.depth;
        let mut result_arg_types = vec![];
        for (i, replacement) in key.replacements.iter().enumerate() {
            match replacement {
                TermInstance::Variable(_, j) => {
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
                TermInstance::Mapped(term) => {
                    // x_i in the template is being replaced with a term
                    let term_info = self.get_term_info(term.term_id);
                    max_edge_depth = std::cmp::max(max_edge_depth, term_info.depth);
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
        let var_map: Vec<AtomId> = (0..result_arg_types.len() as AtomId).collect();
        let result = MappedTerm { term_id, var_map };
        let term_info = TermInfo {
            term_type,
            arg_types: result_arg_types,
            adjacent: std::iter::once(edge_id).collect(),
            atom_keys: vec![],
            type_template: None,
            depth: max_edge_depth + 1,
        };
        let edge_info = EdgeInfo {
            key: key.clone(),
            result: TermInstance::Mapped(result),
        };

        // Insert everything into the graph
        self.terms.push(TermInfoReference::TermInfo(term_info));
        self.mut_term_info(key.template).adjacent.insert(edge_id);
        for r in &key.replacements {
            if let TermInstance::Mapped(term) = r {
                self.mut_term_info(term.term_id).adjacent.insert(edge_id);
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
        replacements: &Vec<TermInstance>,
    ) -> TermInstance {
        // The overall strategy is to normalize the replacements, do the substitution with
        // the graph, and then map from new ids back to old ones.
        let (new_replacements, new_to_old) = normalize_replacements(&replacements);
        if replacements_are_noop(&new_replacements) {
            // No need to even do a substitution
            return TermInstance::mapped(template, new_to_old);
        }
        let new_term = self.expand_edge_key(EdgeKey {
            template,
            replacements: new_replacements,
        });
        new_term.forward_map_vars(&new_to_old)
    }

    // Does a substitution with the given template and replacements.
    // Creates new entries in the term graph if necessary.
    fn replace_in_term_instance(
        &mut self,
        template: &TermInstance,
        replacements: &Vec<TermInstance>,
    ) -> TermInstance {
        match template {
            TermInstance::Mapped(template) => {
                // We need to reorder and/or subset the replacements so that they are relative to the
                // underlying term id, rather than the term instance
                let mut new_replacements = vec![];
                for v in &template.var_map {
                    // We don't need an explicit index i, but x_i in the term is x_v in the instance.
                    new_replacements.push(replacements[*v as usize].clone());
                }
                self.replace_in_term_id(template.term_id, &new_replacements)
            }
            TermInstance::Variable(_, i) => replacements[*i as usize].clone(),
        }
    }

    // Inserts a new term, or returns the existing term if there is one.
    pub fn insert_term(&mut self, term: &Term) -> TermInstance {
        if term.is_true() {
            panic!("True should not be a separate node in the term graph")
        }
        if let Some(i) = term.atomic_variable() {
            return TermInstance::Variable(term.term_type, i);
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
                        type_template: Some(term.head_type),
                        depth: 0,
                    }));
                    type_template
                });
            let mut replacements = vec![TermInstance::Variable(term.head_type, i)];
            for arg in &term.args {
                replacements.push(self.insert_term(arg));
            }
            return self.replace_in_term_id(type_template, &replacements);
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
                type_template: None,
                depth: 0,
            }));
            let term_instance =
                TermInstance::mapped(head_id, (0..term.args.len() as AtomId).collect());
            let atom_info = AtomInfo {
                term: term_instance.clone(),
                head_type: term.head_type,
            };
            self.atoms.insert(atom_key, atom_info);
        };

        // Substitute the arguments into the head
        let term_instance = self.atoms.get(&atom_key).unwrap().term.clone();
        let replacements: Vec<_> = term.args.iter().map(|a| self.insert_term(a)).collect();
        self.replace_in_term_instance(&term_instance, &replacements)
    }

    // The depth of an edge is the maximum depth of any term that it references.
    fn edge_depth(&self, edge_id: EdgeId) -> u32 {
        let edge_info = self.get_edge_info(edge_id);
        let mut max_depth = 0;
        for term_id in edge_info.adjacent_terms() {
            let term_info = self.get_term_info(term_id);
            max_depth = std::cmp::max(max_depth, term_info.depth);
        }
        max_depth
    }

    // Find the least deep edge that creates this term
    // Panics if no edge creates this term
    fn shallowest_edge(&self, term_id: TermId) -> EdgeId {
        let term_info = self.get_term_info(term_id);
        let mut shallowest_edge = None;
        let mut shallowest_depth = std::u32::MAX;
        for &edge_id in &term_info.adjacent {
            let depth = self.edge_depth(edge_id);
            if depth < shallowest_depth {
                shallowest_edge = Some(edge_id);
                shallowest_depth = depth;
            }
        }
        shallowest_edge.unwrap()
    }

    pub fn extract_term_id(&self, term_id: TermId) -> Term {
        let term_info = self.get_term_info(term_id);

        if let Some(type_id) = term_info.type_template {
            return Term {
                term_type: term_info.term_type,
                head_type: type_id,
                head: Atom::Variable(0),
                args: (0..(term_info.arg_types.len() - 1) as AtomId)
                    .map(|i| Term::atom(type_id, Atom::Variable(i + 1)))
                    .collect(),
            };
        }

        if let Some(atom_key) = term_info.atom_keys.get(0) {
            // This term can be extracted as an atom
            let (atom, num_args) = atom_key;
            let atom_info = match self.atoms.get(&atom_key) {
                Some(atom_info) => atom_info,
                None => panic!("atom key {:?} cannot be extracted", atom_key),
            };
            let var_map = match atom_info.term {
                TermInstance::Mapped(ref term) => &term.var_map,
                TermInstance::Variable(_, _) => {
                    panic!(
                        "term is not collapsed but atom key {:?} is a variable",
                        atom_key
                    )
                }
            };
            let mut args = vec![Term::atom(type_space::ANY, Atom::Anonymous); *num_args as usize];
            for (i, v) in var_map.iter().enumerate() {
                args[*v as usize] = Term::atom(term_info.arg_types[i], Atom::Variable(i as AtomId));
            }
            return Term {
                term_type: term_info.term_type,
                head_type: atom_info.head_type,
                head: *atom,
                args,
            };
        }

        // Figure out which edge is the best one to represent this term
        assert!(term_info.depth > 0);
        let edge_id = self.shallowest_edge(term_id);
        let edge_info = self.get_edge_info(edge_id);

        // Construct a Term according to the information provided by the edge
        let template = self.extract_term_id(edge_info.key.template);
        let mut s = Specializer::new();
        for (i, r) in edge_info.key.replacements.iter().enumerate() {
            let i = i as AtomId;
            match r {
                TermInstance::Variable(var_type, j) => {
                    assert!(s.match_var(i, &Term::atom(*var_type, Atom::Variable(*j))));
                }
                TermInstance::Mapped(t) => {
                    let t = self.extract_term_id(t.term_id).remap_variables(&t.var_map);
                    assert!(s.match_var(i, &t));
                }
            }
        }
        let unmapped_term = s.specialize(&template);
        let var_map = match &edge_info.result {
            TermInstance::Mapped(t) => &t.var_map,
            TermInstance::Variable(_, _) => panic!("shallowest edge should never be a variable"),
        };

        unmapped_term.remap_variables(var_map)
    }

    pub fn extract_term_instance(&self, instance: &TermInstance) -> Term {
        match instance {
            TermInstance::Mapped(term) => {
                let unmapped_term = self.extract_term_id(term.term_id);
                let answer = unmapped_term.remap_variables(&term.var_map);
                answer
            }
            TermInstance::Variable(term_type, var_id) => {
                Term::atom(*term_type, Atom::Variable(*var_id))
            }
        }
    }

    // Inserts a single edge if possible.
    // When this discovers more valid operations it pushes them onto pending.
    fn insert_edge_once(&mut self, new_edge_info: EdgeInfo, pending: &mut Vec<Operation>) {
        // Check to see if the new edge is a duplicate
        if let Some(duplicate_edge_id) = self.edgemap.get(&new_edge_info.key) {
            let duplicate_edge_info = self.get_edge_info(*duplicate_edge_id);
            // new_edge_info and duplicate_edge_info are the same edge, but
            // they're going to different terms.
            // This means we need to identify the terms.
            pending.push(Operation::IdentifyTerms(
                new_edge_info.result.clone(),
                duplicate_edge_info.result.clone(),
            ));
            return;
        }

        // Add the new edge
        let new_edge_id = self.edges.len() as EdgeId;
        self.edgemap.insert(new_edge_info.key.clone(), new_edge_id);
        for term in new_edge_info.adjacent_terms() {
            let mut_term = self.mut_term_info(term);
            mut_term.adjacent.insert(new_edge_id);
        }
        self.edges.push(Some(new_edge_info));
    }

    // Replaces all references to old_term_id with references to new_term.
    // The caller should be sure that old_term_id has not been replaced already.
    // When this discovers more valid operations it pushes them onto pending.
    fn replace_term_id(
        &mut self,
        old_term_id: TermId,
        new_term: &TermInstance,
        pending: &mut Vec<Operation>,
    ) {
        let old_term_info_ref = mem::replace(
            &mut self.terms[old_term_id as usize],
            TermInfoReference::Replaced(new_term.clone()),
        );
        let old_term_info = match old_term_info_ref {
            TermInfoReference::TermInfo(t) => t,
            TermInfoReference::Replaced(_) => panic!("term {} already replaced", old_term_id),
        };

        if old_term_info.type_template.is_some() {
            panic!("we should never be replacing a type template");
        }

        // Update information for any atoms that are primarily represented by this term
        for atom_key in &old_term_info.atom_keys {
            let atom_info = self.atoms.get_mut(atom_key).unwrap();
            atom_info.term = atom_info.term.replace_term_id(old_term_id, new_term);
        }

        if let Some(term_id) = new_term.term_id() {
            // Update the term info for the new term
            let new_term_info = self.mut_term_info(term_id);
            new_term_info.atom_keys.extend(old_term_info.atom_keys);
            if new_term_info.depth > old_term_info.depth {
                new_term_info.depth = old_term_info.depth;
            }
        }

        // Update all edges that touch this term
        for old_edge_id in &old_term_info.adjacent {
            // Remove the old edge
            let old_edge_info = self.take_edge_info(*old_edge_id);
            for term in old_edge_info.adjacent_terms() {
                if term != old_term_id {
                    let mut_term = self.mut_term_info(term);
                    mut_term.adjacent.remove(old_edge_id);
                }
            }
            self.edgemap.remove(&old_edge_info.key);

            let operation = old_edge_info.replace_term_id(old_term_id, new_term);
            pending.push(operation);
        }
    }

    // Applies any replacements that have happened for the given term.
    pub fn apply_replacements(&self, term: TermInstance) -> TermInstance {
        match term {
            TermInstance::Variable(_, _) => term,
            TermInstance::Mapped(t) => {
                let replacement = match self.get_term_info_ref(t.term_id) {
                    TermInfoReference::TermInfo(_) => return TermInstance::Mapped(t),
                    TermInfoReference::Replaced(r) => r,
                };
                let updated = t.replace_term_id(t.term_id, replacement);
                self.apply_replacements(updated)
            }
        }
    }

    // The term we most want to keep compares as the largest in the keeping order.
    fn keeping_order(
        &self,
        left_instance: &TermInstance,
        right_instance: &TermInstance,
    ) -> Ordering {
        // If one of the terms is a variable, it is more keepable.
        let (left_id, right_id) = match left_instance {
            TermInstance::Variable(_, _) => return Ordering::Greater,
            TermInstance::Mapped(left) => match right_instance {
                TermInstance::Variable(_, _) => return Ordering::Less,
                TermInstance::Mapped(right) => (left.term_id, right.term_id),
            },
        };

        let left_term_info = self.get_term_info(left_id);
        let right_term_info = self.get_term_info(right_id);

        // If one of the terms has more arguments, it is less keepable.
        // This condition is required - we can't add more arguments to the result of an edge.
        let arg_len_cmp = right_term_info
            .arg_types
            .len()
            .cmp(&left_term_info.arg_types.len());
        if arg_len_cmp != Ordering::Equal {
            return arg_len_cmp;
        }

        // If one of the terms has more adjacent edges, it is more keepable.
        // This is a performance heuristic, because we do work for each changed edge.
        let adj_cmp = left_term_info
            .adjacent
            .len()
            .cmp(&right_term_info.adjacent.len());
        if adj_cmp != Ordering::Equal {
            return adj_cmp;
        }

        // If all else fails, the lower term ids are more keepable.
        // This probably doesn't matter very much.
        right_id.cmp(&left_id)
    }

    // Identifies the two terms, and adds any followup operations to the queue rather than
    // processing them all.
    fn identify_terms_once(
        &mut self,
        instance1: TermInstance,
        instance2: TermInstance,
        pending: &mut Vec<Operation>,
    ) {
        let instance1 = self.apply_replacements(instance1);
        let instance2 = self.apply_replacements(instance2);
        if instance1 == instance2 {
            // Nothing to do
            return;
        }

        if instance1.term_id().is_some() && instance1.term_id() == instance2.term_id() {
            todo!("handle permutations of arguments");
        }

        // Discard the term that we least want to keep
        let (discard_instance, keep_instance) = match self.keeping_order(&instance1, &instance2) {
            Ordering::Less => (instance1, instance2),
            Ordering::Greater => (instance2, instance1),
            Ordering::Equal => {
                panic!("flow control error");
            }
        };

        let discard = match &discard_instance {
            TermInstance::Variable(_, _) => panic!("flow control error"),
            TermInstance::Mapped(t) => t,
        };

        if let TermInstance::Mapped(keep) = &keep_instance {
            if keep.var_map.iter().any(|v| !discard.var_map.contains(v)) {
                // The "keep" term contains some arguments that the "discard" term doesn't.
                // These arguments can be eliminated.
                // We make a new reduced term with these arguments eliminated and identify
                // the "keep" term before doing this identification.
                let keep_info = self.get_term_info(keep.term_id);
                let mut reduced_arg_types = vec![];
                let mut reduced_var_map = vec![];
                for (i, v) in keep.var_map.iter().enumerate() {
                    if discard.var_map.contains(v) {
                        reduced_var_map.push(*v);
                        reduced_arg_types.push(keep_info.arg_types[i]);
                    }
                }
                let reduced_term_info = TermInfo {
                    term_type: keep_info.term_type,
                    arg_types: reduced_arg_types,
                    adjacent: HashSet::default(),
                    atom_keys: vec![],
                    type_template: None,
                    depth: keep_info.depth,
                };
                let reduced_term_id = self.terms.len() as TermId;
                self.terms
                    .push(TermInfoReference::TermInfo(reduced_term_info));
                let reduced_instance = TermInstance::mapped(reduced_term_id, reduced_var_map);

                // We need to identify keep+reduced before keep+discard.
                // Since our "priority queue" is just a vector, this works.
                // Ie, order does matter here.
                pending.push(Operation::IdentifyTerms(
                    keep_instance.clone(),
                    discard_instance,
                ));
                pending.push(Operation::IdentifyTerms(keep_instance, reduced_instance));
                return;
            }
        }

        // Find a TermInstance equal to the term to be discarded
        let new_instance = keep_instance.backward_map_vars(&discard.var_map);
        self.replace_term_id(discard.term_id, &new_instance, pending);
    }

    fn process_all(&mut self, pending: Vec<Operation>) {
        let mut pending = pending;
        loop {
            match pending.pop() {
                Some(Operation::IdentifyTerms(instance1, instance2)) => {
                    self.identify_terms_once(instance1, instance2, &mut pending);
                }
                Some(Operation::InsertEdge(edge_info)) => {
                    self.insert_edge_once(edge_info, &mut pending);
                }
                None => break,
            }
        }
    }

    // Identifies the two terms, and continues processing any followup operations until
    // all operations are processed.
    pub fn identify_terms(&mut self, instance1: TermInstance, instance2: TermInstance) {
        let ops = vec![Operation::IdentifyTerms(instance1, instance2)];
        self.process_all(ops)
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
            if term_info.type_template.is_none() && term_info.atom_keys.is_empty() {
                // Make sure there is some edge to produce this term
                self.shallowest_edge(term_id);
            }
            for edge_id in &term_info.adjacent {
                if !self.has_edge_info(*edge_id) {
                    panic!("term {} is adjacent to collapsed edge {}", term_id, edge_id);
                }
                let edge_info = self.get_edge_info(*edge_id);
                if !edge_info.adjacent_terms().contains(&term_id) {
                    panic!(
                        "term {} thinks it is adjacent to edge {} ({}) but not vice versa",
                        term_id, edge_id, edge_info
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
                if let TermInstance::Mapped(result) = &edge_info.result {
                    if term_id == result.term_id {
                        assert_eq!(result.var_map.len(), term_info.arg_types.len());
                    }
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
            if let Some(term_id) = atom_info.term.term_id() {
                if !self.has_term_info(term_id) {
                    panic!(
                        "atom ({}, {}) is represented by term {} which has been collapsed",
                        atom, num_args, atom_info.term
                    );
                }
            }
        }
    }

    pub fn parse(&mut self, term_string: &str) -> TermInstance {
        let term = Term::parse(term_string);
        let term_instance = self.insert_term(&term);
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

    fn check_insert(g: &mut TermGraph, input: &str, expected_output: &str) {
        let ti = g.parse(input);
        let actual_output = g.extract_term_instance(&ti);
        if expected_output != actual_output.to_string() {
            panic!(
                "\nwhen inserting {}, expected {} but got {}\n",
                input, expected_output, actual_output
            );
        }
    }

    fn insert_and_extract(term_strings: &[&str]) {
        let mut g = TermGraph::new();
        for s in term_strings {
            check_insert(&mut g, s, s);
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

    #[test]
    fn test_extracting_infinite_loop() {
        let mut g = TermGraph::new();
        let a0a0a1 = g.parse("a0(a1)");
        let other_term = g.parse("a2(a3)");
        g.check_identify_terms(&a0a0a1, &other_term);
        let a1 = g.parse("a1");
        g.check_identify_terms(&a0a0a1, &a1);
    }

    #[test]
    fn test_double_touched_edges() {
        let mut g = TermGraph::new();

        let a0a1a1 = g.parse("a0(a1, a1)");
        let a2 = g.parse("a2");
        g.check_identify_terms(&a0a1a1, &a2);

        let a1 = g.parse("a1");
        let a2 = g.parse("a3");
        g.check_identify_terms(&a1, &a2);

        let a0a3a3 = g.parse("a0(a3, a3)");
        let a2 = g.parse("a2");
        assert_eq!(a0a3a3, a2);
    }

    #[test]
    fn test_atom_vs_less_args() {
        let mut g = TermGraph::new();
        let a0x0 = g.parse("a0(x0)");
        let a1a2 = g.parse("a1(a2)");
        g.check_identify_terms(&a0x0, &a1a2);
    }

    #[test]
    fn test_implicit_argument_collapse() {
        let mut g = TermGraph::new();
        let a0x0 = g.parse("a0(x0)");
        let a1x1 = g.parse("a1(x1)");
        g.check_identify_terms(&a0x0, &a1x1);
        let a0a2 = g.parse("a0(a2)");
        let a0a3 = g.parse("a0(a3)");
        assert_eq!(a0a2, a0a3);

        check_insert(&mut g, "a0(x0)", "a0(_)");
    }

    #[test]
    fn test_identifying_with_the_identity() {
        let mut g = TermGraph::new();
        let a0x0 = g.parse("a0(x0)");
        let x0 = g.parse("x0");
        g.check_identify_terms(&a0x0, &x0);
        let a0a1 = g.parse("a0(a1)");
        let a1 = g.parse("a1");
        assert_eq!(a0a1, a1);
    }

    #[test]
    fn test_edge_template_identifying_with_variable() {
        let mut g = TermGraph::new();
        g.parse("a0(a1)");
        let x0 = g.parse("x0");
        let a0x0 = g.parse("a0(x0)");
        g.check_identify_terms(&x0, &a0x0);
    }

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
