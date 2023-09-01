use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;
use std::{fmt, mem, vec};

use fxhash::FxHashMap;
use nohash_hasher::BuildNoHashHasher;

use crate::atom::{Atom, AtomId};
use crate::permutation;
use crate::permutation_group::PermutationGroup;
use crate::specializer::Specializer;
use crate::term::{Literal, Term};
use crate::type_space::{self, TypeId, ANY};

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

    // The symmetry group formed by the permutations of this term's arguments for which
    // the term is invariant.
    symmetry: PermutationGroup,

    // The terms that this term can never be equal to.
    not_equal: HashSet<TermInstance>,
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
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct MappedTerm {
    term_id: TermId,
    var_map: Vec<AtomId>,
}

// A particular instance of a term can either be a mapped term from the graph, or a single variable.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum TermInstance {
    Mapped(MappedTerm),
    Variable(AtomId),
}

// A TermInstance along with type information.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct TypedTermInstance {
    pub term_type: TypeId,
    pub instance: TermInstance,
}

pub type EdgeId = u32;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Replacement {
    // The variable we are replacing
    var: AtomId,

    // What we replace it with
    value: TermInstance,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct EdgeKey {
    // The template that we are substituting into
    template: TermId,

    // The replacement we are doing
    replacement: Replacement,

    // The number of variables used in the replacements.
    //
    // NOTE: This also includes the variable that the Replacement is removing.
    // So it is generally one more than the EdgeKey vars_used would be.
    //
    // This can be larger than the number of variables used in the result, if the result ignores
    // some of the variables.
    vars_used: AtomId,
}

#[derive(Debug)]
struct EdgeInfo {
    // The parameters that determine the substitution
    key: EdgeKey,

    // The result of the substitution.
    // This can have non-consecutive variable ids but not duplicated ones.
    result: TermInstance,
}

enum NormalizedEdge {
    // The edge is degenerate.
    // Without using the graph, we know that the result of the edge is this TermInstance.
    Degenerate(TermInstance),

    // The edge is not degenerate.
    // The key for edge lookup, and the denormalizer which maps from normalized to original ids.
    Key(EdgeKey, Vec<AtomId>),
}

// An operation on the graph that is pending.
// We keep a pending operation queue rather than doing operations immediately so that we
// can control when we do expensive operations.
enum Operation {
    // Make these two term instances represent the same thing.
    Identification(TermInstance, TermInstance),
}

enum TermInfoReference {
    TermInfo(TermInfo),
    Replaced(TermInstance),
}

// A conversion of all the parts of a Term to TermInstance.
pub struct DecomposedTerm {
    // The 0th subterm is the whole term itself.
    subterms: Vec<TypedTermInstance>,

    // The initial variable that we substitute into.
    // Each subsequent replacement will increment its variable by 1.
    start_var: AtomId,

    // x_{i+start_var} gets replaced with replacement_values[i].
    replacement_values: Vec<TypedTermInstance>,

    // subterm_sizes[n] is the number of replacements used for subterms[n].
    // The first entry is the whole term as a subterm, even though its size is always
    // the entire list of replacement_values, so it's a bit redundant.
    // The last entry is always the last atom, so it should be 1.
    subterm_sizes: Vec<usize>,
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
    edge_key_map: FxHashMap<EdgeKey, EdgeId>,

    // A flag to indicate when we find a contradiction
    found_contradiction: bool,
}

// -----------------------------------------------------------------------------------------------
//                       implementation
// -----------------------------------------------------------------------------------------------

impl TermInfo {
    fn new(term_type: TypeId, arg_types: Vec<TypeId>, depth: u32) -> Self {
        let num_args = arg_types.len() as AtomId;
        TermInfo {
            term_type,
            arg_types,
            adjacent: HashSet::default(),
            atom_keys: vec![],
            type_template: None,
            depth,
            symmetry: PermutationGroup::trivial(num_args),
            not_equal: HashSet::default(),
        }
    }
}

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
    fn has_var(&self, i: AtomId) -> bool {
        self.var_map.iter().any(|&j| j == i)
    }

    fn rename_var(&self, from: AtomId, to: AtomId) -> MappedTerm {
        let new_var_map = self
            .var_map
            .iter()
            .map(|&v| if v == from { to } else { v })
            .collect();
        MappedTerm {
            term_id: self.term_id,
            var_map: new_var_map,
        }
    }

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
            TermInstance::Variable(i) => {
                let new_index = self.var_map[*i as usize];
                TermInstance::Variable(new_index)
            }
        }
    }
}

impl fmt::Display for TermInstance {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermInstance::Mapped(term) => write!(f, "{}", term),
            TermInstance::Variable(var_id) => write!(f, "x{}", var_id),
        }
    }
}

impl TermInstance {
    fn mapped(term_id: TermId, var_map: Vec<AtomId>) -> TermInstance {
        TermInstance::Mapped(MappedTerm { term_id, var_map })
    }

    fn has_var(&self, i: AtomId) -> bool {
        match self {
            TermInstance::Mapped(term) => term.var_map.iter().any(|&j| j == i),
            TermInstance::Variable(j) => *j == i,
        }
    }

    fn term_id(&self) -> Option<TermId> {
        match self {
            TermInstance::Mapped(term) => Some(term.term_id),
            TermInstance::Variable(_) => None,
        }
    }

    fn forward_map_vars(&self, var_map: &Vec<AtomId>) -> TermInstance {
        match self {
            TermInstance::Mapped(term) => {
                TermInstance::mapped(term.term_id, compose_var_maps(&term.var_map, var_map))
            }
            TermInstance::Variable(var_id) => TermInstance::Variable(var_map[*var_id as usize]),
        }
    }

    // Backward map the variables, so that when var_map[i] = j, we replace x_j with x_i.
    // For any variables that are not present in the var map, we extend the var map.
    fn extended_backward_map(&self, var_map: &Vec<AtomId>) -> TermInstance {
        match self {
            TermInstance::Mapped(term) => {
                // Make a copy so that we can extend if we need to
                let mut old_var_map = var_map.clone();
                let mut new_var_map = vec![];
                for v in &term.var_map {
                    match old_var_map.iter().position(|w| w == v) {
                        Some(i) => new_var_map.push(i as AtomId),
                        None => {
                            let i = old_var_map.len();
                            old_var_map.push(*v);
                            new_var_map.push(i as AtomId);
                        }
                    }
                }
                TermInstance::mapped(term.term_id, new_var_map)
            }
            TermInstance::Variable(var_id) => match var_map.iter().position(|&w| w == *var_id) {
                Some(i) => TermInstance::Variable(i as AtomId),
                None => TermInstance::Variable(var_map.len() as AtomId),
            },
        }
    }

    // Attempt to backward map the variables, so that when var_map[i] = j, we replace x_j with x_i.
    // Returns None if there's any variable with no entry to backward map it to.
    fn try_backward_map_vars(&self, var_map: &Vec<AtomId>) -> Option<TermInstance> {
        match self {
            TermInstance::Mapped(term) => {
                let mut new_var_map = vec![];
                for v in &term.var_map {
                    new_var_map.push(var_map.iter().position(|w| w == v)? as AtomId);
                }
                Some(TermInstance::mapped(term.term_id, new_var_map))
            }
            TermInstance::Variable(v) => {
                let i = var_map.iter().position(|w| w == v)?;
                Some(TermInstance::Variable(i as AtomId))
            }
        }
    }

    fn backward_map_vars(&self, var_map: &Vec<AtomId>) -> TermInstance {
        self.try_backward_map_vars(var_map).unwrap()
    }

    fn replace_term_id(&self, old_term_id: TermId, new_term: &TermInstance) -> TermInstance {
        match self {
            TermInstance::Mapped(term) => term.replace_term_id(old_term_id, new_term),
            TermInstance::Variable(_) => self.clone(),
        }
    }

    fn _as_mapped(&self) -> &MappedTerm {
        match self {
            TermInstance::Mapped(term) => term,
            TermInstance::Variable(_) => panic!("TermInstance is a variable"),
        }
    }
}

impl Replacement {
    fn new(var: AtomId, replacement: TermInstance) -> Replacement {
        Replacement {
            var,
            value: replacement,
        }
    }

    fn backward_map_vars(&self, var_map: &Vec<AtomId>) -> Replacement {
        Replacement {
            var: var_map.iter().position(|&v| v == self.var).unwrap() as AtomId,
            value: self.value.backward_map_vars(var_map),
        }
    }

    fn replace_term_id(&self, old_term_id: TermId, new_term: &TermInstance) -> Replacement {
        match self.value {
            TermInstance::Mapped(ref term) => Replacement {
                var: self.var,
                value: term.replace_term_id(old_term_id, new_term),
            },
            TermInstance::Variable(_) => self.clone(),
        }
    }

    // This replacement should be normalized, relative to the underlying term id.
    // Renumbers this replacement in terms of the numbering used in the provided template instance.
    // Any new variables used are allocated starting at next_var.
    //
    // Providing the result instance is optional. If we get it, we create a new result term
    // instance that is renumbered in the same way that this replacement renumbered.
    //
    // Returns the replacement, the least unused variable, and the renumbered result.
    // TODO: are we going to use this?
    pub fn relativize(
        &self,
        template_instance: &MappedTerm,
        next_var: AtomId,
        result: &TermInstance,
    ) -> (Replacement, TermInstance) {
        let mut var_map = template_instance.var_map.clone();
        let mut next_var = next_var;
        let relative_var = var_map[self.var as usize];
        let relative_replacement = match &self.value {
            TermInstance::Mapped(mapped) => {
                // rep_var_map is a translation of mapped.var_map into the template instance's space.
                let mut rep_var_map = vec![];
                for &var in &mapped.var_map {
                    // var is a variable in the normalized space.
                    if var < var_map.len() as AtomId {
                        // This variable is already in the template instance's space.
                        rep_var_map.push(var_map[var as usize]);
                    } else {
                        // The edge is supposed to be normalized
                        assert_eq!(var, var_map.len() as AtomId);

                        // This variable doesn't exist in the template instance's space, yet.
                        // We need to add a var -> next_var mapping.
                        var_map.push(next_var);
                        rep_var_map.push(next_var);
                        next_var += 1;
                    }
                }
                TermInstance::mapped(mapped.term_id, rep_var_map)
            }
            TermInstance::Variable(i) => {
                let relative_i = var_map[*i as usize];
                TermInstance::Variable(relative_i)
            }
        };
        let edge = Replacement::new(relative_var, relative_replacement);
        let answer = result.forward_map_vars(&var_map);
        (edge, answer)
    }
}

impl fmt::Display for Replacement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "x{} -> {}", self.var, self.value)
    }
}

impl EdgeInfo {
    fn adjacent_terms(&self) -> Vec<TermId> {
        let mut terms = vec![];
        terms.push(self.key.template);
        if let TermInstance::Mapped(term) = &self.key.replacement.value {
            terms.push(term.term_id);
        }
        if let Some(term_id) = self.result.term_id() {
            terms.push(term_id);
        }
        terms
    }
}

impl NormalizedEdge {
    // Normalizes a TermInstance and an edge that comes from that term.
    // This constructor ignores symmetry.
    // The denormalizer maps (normalized ids) -> (original ids).
    // If you think about it, that makes sense, since the normalized ids are consecutive
    // starting at zero.
    fn new(template: &TermInstance, edge: &Replacement) -> NormalizedEdge {
        match template {
            TermInstance::Mapped(mapped) => {
                if !mapped.has_var(edge.var) {
                    // This edge isn't changing anything.
                    return NormalizedEdge::Degenerate(template.clone());
                }

                if let TermInstance::Variable(i) = &edge.value {
                    // Check for degenerate cases.
                    if i == &edge.var {
                        // We're replacing a variable with itself.
                        return NormalizedEdge::Degenerate(template.clone());
                    }
                    if !mapped.has_var(*i) {
                        // We're renaming a variable but not duplicating anything.
                        return NormalizedEdge::Degenerate(TermInstance::Mapped(
                            mapped.rename_var(edge.var, *i),
                        ));
                    }
                }

                // First assign variable ids starting at zero to the template variables.
                let mut denormalizer = mapped.var_map.clone();

                let edge = match &edge.value {
                    TermInstance::Mapped(replacement) => {
                        // Now assign variable ids starting at the end of the template variables
                        // to the replacement variables.
                        for &var in &replacement.var_map {
                            match denormalizer.iter().position(|&v| v == var) {
                                Some(_) => {}
                                None => {
                                    denormalizer.push(var);
                                }
                            }
                        }
                        edge.backward_map_vars(&denormalizer)
                    }
                    TermInstance::Variable(i) => {
                        assert_ne!(*i, edge.var);

                        // In the original namespace, both i and edge.var are being combined to i.
                        let new_var_1 = denormalizer.iter().position(|&v| v == *i).unwrap();
                        let new_var_2 = denormalizer.iter().position(|&v| v == edge.var).unwrap();
                        let (low_var, high_var) = if new_var_1 < new_var_2 {
                            (new_var_1, new_var_2)
                        } else {
                            (new_var_2, new_var_1)
                        };

                        // We want to combine both new vars into the low var.
                        denormalizer[low_var] = *i;
                        denormalizer[high_var] = edge.var; // shouldn't be used, but just in case
                        Replacement::new(
                            high_var as AtomId,
                            TermInstance::Variable(low_var as AtomId),
                        )
                    }
                };
                let key = EdgeKey {
                    template: mapped.term_id,
                    replacement: edge,
                    vars_used: denormalizer.len() as AtomId,
                };

                NormalizedEdge::Key(key, denormalizer)
            }
            TermInstance::Variable(i) => {
                // This edge is degenerate because it just starts from a variable.
                // Still, we can give the degenerate answer.
                if i == &edge.var {
                    NormalizedEdge::Degenerate(edge.value.clone())
                } else {
                    NormalizedEdge::Degenerate(template.clone())
                }
            }
        }
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
            edge_key_map: HashMap::default(),
            found_contradiction: false,
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

    pub fn term_instance(&self, term_id: TermId) -> TermInstance {
        let info = self.get_term_info(term_id);
        TermInstance::mapped(term_id, (0..info.arg_types.len() as AtomId).collect())
    }

    fn has_edge_info(&self, edge: EdgeId) -> bool {
        self.edges[edge as usize].is_some()
    }

    // The arg types for every variable used in the given term and replacement.
    // The replacement should be normalized, always using either an existing variable
    // or the next available one.
    fn get_var_types(&self, term_info: &TermInfo, replacement: &Replacement) -> Vec<TypeId> {
        match replacement.value {
            TermInstance::Variable(_) => term_info.arg_types.clone(),
            TermInstance::Mapped(ref replacement) => {
                let mut arg_types = term_info.arg_types.clone();
                let term_info = self.get_term_info(replacement.term_id);
                for (i, v) in replacement.var_map.iter().enumerate() {
                    if *v < arg_types.len() as AtomId {
                        // This is a variable that we already know about
                        continue;
                    }
                    if *v > arg_types.len() as AtomId {
                        panic!("non-normalized variable numbering in get_arg_types")
                    }
                    arg_types.push(term_info.arg_types[i]);
                }
                arg_types
            }
        }
    }

    // Creates a new term, along with an edge that leads to it.
    // key should already be normalized.
    // There must be no analogous edge already in the graph.
    fn create_term(&mut self, key: EdgeKey) -> TermInstance {
        // Figure out the type signature of the new term
        let template = self.get_term_info(key.template);
        let mut arg_types = self.get_var_types(template, &key.replacement);
        let mut var_map: Vec<AtomId> = (0..arg_types.len() as AtomId).collect();

        // The edge replaces one variable so we must remove it from arg_types and var_map
        arg_types.remove(key.replacement.var as usize);
        var_map.remove(key.replacement.var as usize);

        // Figure out depth
        let mut max_edge_depth = template.depth;
        if let TermInstance::Mapped(replacement) = &key.replacement.value {
            let replacement_info = self.get_term_info(replacement.term_id);
            max_edge_depth = std::cmp::max(max_edge_depth, replacement_info.depth);
        }

        let term_id = self.terms.len() as TermId;
        let term_type = template.term_type;
        let term_info = TermInfo::new(term_type, arg_types, max_edge_depth + 1);
        self.terms.push(TermInfoReference::TermInfo(term_info));
        let answer = TermInstance::mapped(term_id, var_map);
        let edge_info = EdgeInfo {
            key,
            result: answer.clone(),
        };

        self.create_edge(edge_info);
        answer
    }

    // Given a template term and an edge, follow the edge.
    // If the edge is already there, this uses the existing edge.
    // If the edge is not already there, this will create one.
    //
    // result is provided if the result of the edge should be an existing node in the graph.
    // If result is None, that means we should create a new node if needed.
    // If result is provided and also there is already a node in the graph for this edge,
    // then we identify the two results.
    //
    // Returns the term instance that this edge leads to after the insertion.
    fn follow_or_create_edge(
        &mut self,
        template: &TermInstance,
        edge: &Replacement,
        result: Option<TermInstance>,
        pending: &mut VecDeque<Operation>,
    ) -> TermInstance {
        let (key, denormalizer) = match NormalizedEdge::new(template, edge) {
            NormalizedEdge::Degenerate(term) => {
                if let Some(result) = result {
                    pending.push_front(Operation::Identification(term.clone(), result));
                }
                return term;
            }
            NormalizedEdge::Key(key, denormalizer) => (key, denormalizer),
        };

        if let Some(edge_id) = self.edge_key_map.get(&key).cloned() {
            // We already have an edge
            let edge_info = self.edges[edge_id as usize].as_ref().unwrap();
            let existing = edge_info.result.forward_map_vars(&denormalizer);
            if let Some(result) = result {
                pending.push_front(Operation::Identification(existing.clone(), result));
            }
            return existing;
        }

        if let Some(result) = result {
            if let Some(normalized_result) = result.try_backward_map_vars(&denormalizer) {
                // We can just create a new edge to an existing term
                let edge_info = EdgeInfo {
                    key,
                    result: normalized_result,
                };
                self.create_edge(edge_info);
                return result;
            }

            // We have an existing term, but its argument is collapsing.
            // So create a new term and subsequently identify the result.
            let new_term = self.create_term(key);
            let answer = new_term.forward_map_vars(&denormalizer);
            pending.push_front(Operation::Identification(answer.clone(), result));
            return answer;
        }

        // No existing term, so create a new one
        let new_term = self.create_term(key);
        new_term.forward_map_vars(&denormalizer)
    }

    // Follows this edge, if there is such an edge in the graph.
    // Returns None is there is not.
    pub fn follow_edge(&self, template: &TermInstance, edge: &Replacement) -> Option<TermInstance> {
        let (key, denormalizer) = match NormalizedEdge::new(template, edge) {
            NormalizedEdge::Degenerate(term) => return Some(term),
            NormalizedEdge::Key(key, denormalizer) => (key, denormalizer),
        };

        if let Some(edge_id) = self.edge_key_map.get(&key).cloned() {
            let edge_info = self.edges[edge_id as usize].as_ref().unwrap();
            let existing = edge_info.result.forward_map_vars(&denormalizer);
            return Some(existing);
        }
        None
    }

    fn type_template_term_id(
        &mut self,
        term_type: TypeId,
        head_type: TypeId,
        arg_types: &Vec<TypeId>,
    ) -> TermId {
        if arg_types.len() == 0 {
            panic!("there should be no zero-arg type templates");
        }
        let term_id = self
            .type_templates
            .entry((head_type, arg_types.len() as u8))
            .or_insert_with(|| {
                let term_id = self.terms.len() as TermId;
                // The head of the term is an argument for the term instance.
                let mut instance_arg_types = vec![head_type];
                for arg_type in arg_types {
                    instance_arg_types.push(*arg_type);
                }
                let mut term_info = TermInfo::new(term_type, instance_arg_types, 0);
                term_info.type_template = Some(head_type);
                self.terms.push(TermInfoReference::TermInfo(term_info));
                term_id
            });
        *term_id
    }

    fn atomic_instance(&mut self, atom_type: TypeId, atom: Atom) -> TermInstance {
        match atom {
            Atom::Variable(i) => TermInstance::Variable(i),
            _ => {
                let atom_key = (atom, 0);
                if !self.atoms.contains_key(&atom_key) {
                    let term_id = self.terms.len() as TermId;
                    let mut term_info = TermInfo::new(atom_type, vec![], 0);
                    term_info.atom_keys.push(atom_key.clone());
                    self.terms.push(TermInfoReference::TermInfo(term_info));
                    let term_instance = TermInstance::mapped(term_id, vec![]);
                    let atom_info = AtomInfo {
                        term: term_instance.clone(),
                        head_type: atom_type,
                    };
                    self.atoms.insert(atom_key, atom_info);
                };
                self.atoms.get(&atom_key).unwrap().term.clone()
            }
        }
    }

    // The depth of an edge is the maximum depth of any term that its key references.
    fn edge_depth(&self, edge_id: EdgeId) -> u32 {
        let edge_info = self.edges[edge_id as usize].as_ref().unwrap();
        let template_info = self.get_term_info(edge_info.key.template);
        let mut max_depth = template_info.depth;
        if let TermInstance::Mapped(replacement) = &edge_info.key.replacement.value {
            let replacement_info = self.get_term_info(replacement.term_id);
            max_depth = std::cmp::max(max_depth, replacement_info.depth);
        }
        max_depth
    }

    // Find the least deep edge that creates this term.
    // Panics if no edge creates this term.
    // Don't call this for terms that are atoms or type templates.
    //
    // The depths are accurate, but only if we process all of the pending operation queue.
    // So this function does not work correctly when there are still pending operations.
    fn shallowest_edge(&self, term_id: TermId) -> EdgeId {
        let term_info = self.get_term_info(term_id);
        if term_info.depth == 0 {
            panic!(
                "don't call shallowest_edge for non-composite terms like term {} = {:?}",
                term_id, term_info
            );
        }
        let mut shallowest_edge = None;
        let mut shallowest_depth = std::u32::MAX;
        for &edge_id in &term_info.adjacent {
            let depth = self.edge_depth(edge_id);
            if depth < shallowest_depth {
                shallowest_edge = Some(edge_id);
                shallowest_depth = depth;
            }
        }
        if shallowest_depth >= term_info.depth {
            panic!(
                "term {} has depth {} but its shallowest edge has depth {}",
                term_id, term_info.depth, shallowest_depth
            );
        }
        shallowest_edge.unwrap()
    }

    fn extract_term_id(&self, term_id: TermId) -> Term {
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
                TermInstance::Variable(_) => {
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
        let edge_info = self.edges[edge_id as usize].as_ref().unwrap();

        // Construct a Term according to the information provided by the edge
        let template = self.extract_term_id(edge_info.key.template);
        let template_info = self.get_term_info(edge_info.key.template);
        let mut s = Specializer::new();
        for (i, arg_type) in template_info.arg_types.iter().enumerate() {
            let i = i as AtomId;
            if i == edge_info.key.replacement.var {
                match &edge_info.key.replacement.value {
                    TermInstance::Variable(j) => {
                        s.match_var(i, &Term::atom(*arg_type, Atom::Variable(*j)));
                    }
                    TermInstance::Mapped(t) => {
                        let t = self.extract_term_id(t.term_id).remap_variables(&t.var_map);
                        s.match_var(i, &t);
                    }
                }
            } else {
                s.match_var(i, &Term::atom(*arg_type, Atom::Variable(i)));
            }
        }

        let unmapped_term = s.specialize(&template);
        let var_map = match &edge_info.result {
            TermInstance::Mapped(t) => &t.var_map,
            TermInstance::Variable(_) => panic!("shallowest edge should never be a variable"),
        };
        unmapped_term.unmap_variables(var_map)
    }

    pub fn validate_typed_term_instance(&self, instance: &TypedTermInstance) {
        match &instance.instance {
            TermInstance::Mapped(mapped) => {
                let term_info = self.get_term_info(mapped.term_id);
                assert_eq!(term_info.term_type, instance.term_type, "type mismatch");
                assert_eq!(
                    term_info.arg_types.len(),
                    mapped.var_map.len(),
                    "num args mismatch"
                );
            }
            TermInstance::Variable(_) => {
                // We have no way to validate these, so don't try
            }
        }
    }

    pub fn extract_term_instance(&self, instance: &TypedTermInstance) -> Term {
        self.validate_typed_term_instance(instance);
        match &instance.instance {
            TermInstance::Mapped(term) => {
                let unmapped_term = self.extract_term_id(term.term_id);
                let answer = unmapped_term.remap_variables(&term.var_map);
                answer
            }
            TermInstance::Variable(var_id) => {
                Term::atom(instance.term_type, Atom::Variable(*var_id))
            }
        }
    }

    // Creates a new edge.
    // All adjacent terms must already exist, and the edge itself must not already exist.
    fn create_edge(&mut self, edge_info: EdgeInfo) -> EdgeId {
        let new_edge_id = self.edges.len() as EdgeId;
        assert!(self
            .edge_key_map
            .insert(edge_info.key.clone(), new_edge_id)
            .is_none());
        for term in edge_info.adjacent_terms() {
            let mut_term = self.mut_term_info(term);
            mut_term.adjacent.insert(new_edge_id);
        }
        self.edges.push(Some(edge_info));
        new_edge_id
    }

    // Removes an edge, updating the appropriate maps.
    // The term may not exist any more by the time this is called.
    // The edge must exist.
    fn remove_edge(&mut self, edge_id: EdgeId) -> EdgeInfo {
        let edge_info = self.edges[edge_id as usize].take().unwrap();
        for term in edge_info.adjacent_terms() {
            match &mut self.terms[term as usize] {
                TermInfoReference::Replaced(_) => (),
                TermInfoReference::TermInfo(term_info) => {
                    term_info.adjacent.remove(&edge_id);
                }
            }
        }
        self.edge_key_map.remove(&edge_info.key);
        edge_info
    }

    // Replaces old_term_id with new_term in the given edge.
    // This can lead us to discover new Identifications, which we push onto pending.
    fn replace_term_id_in_edge(
        &mut self,
        old_edge_id: EdgeId,
        old_term_id: TermId,
        old_term_num_args: AtomId,
        new_term: &TermInstance,
        pending: &mut VecDeque<Operation>,
    ) {
        let edge_info = self.remove_edge(old_edge_id);

        let old_edge_num_args = if edge_info.key.template == old_term_id {
            old_term_num_args
        } else {
            self.get_term_info(edge_info.key.template).arg_types.len() as AtomId
        };

        // Recurse on the result and the edge key.
        let new_result = edge_info.result.replace_term_id(old_term_id, new_term);
        let new_edge = edge_info
            .key
            .replacement
            .replace_term_id(old_term_id, new_term);

        if edge_info.key.template == old_term_id {
            self.follow_or_create_edge(new_term, &new_edge, Some(new_result), pending);
        } else {
            // The template is unchanged, but we still have to renormalize the edge
            let template =
                TermInstance::mapped(edge_info.key.template, (0..old_edge_num_args).collect());
            self.follow_or_create_edge(&template, &new_edge, Some(new_result), pending);
        }
    }

    // Replaces all references to old_term_id with references to new_term.
    // The caller should be sure that old_term_id has not been replaced already.
    // When this discovers more valid Identifications it pushes them onto pending.
    fn identify_term_id(
        &mut self,
        old_term_id: TermId,
        new_term: &TermInstance,
        pending: &mut VecDeque<Operation>,
    ) {
        let old_term_info_ref = mem::replace(
            &mut self.terms[old_term_id as usize],
            TermInfoReference::Replaced(new_term.clone()),
        );
        let old_term_info = match old_term_info_ref {
            TermInfoReference::TermInfo(t) => t,
            TermInfoReference::Replaced(_) => panic!("term {} already replaced", old_term_id),
        };
        let old_term_num_args = old_term_info.arg_types.len() as AtomId;

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
            self.replace_term_id_in_edge(
                *old_edge_id,
                old_term_id,
                old_term_num_args,
                new_term,
                pending,
            );
        }
    }

    // Applies any replacements that have happened for the given term.
    pub fn update_term(&self, term: TermInstance) -> TermInstance {
        match term {
            TermInstance::Variable(_) => term,
            TermInstance::Mapped(t) => {
                let replacement = match self.get_term_info_ref(t.term_id) {
                    TermInfoReference::TermInfo(_) => return TermInstance::Mapped(t),
                    TermInfoReference::Replaced(r) => r,
                };
                let updated = t.replace_term_id(t.term_id, replacement);
                self.update_term(updated)
            }
        }
    }

    // Sometimes we discover that a term doesn't use some of its arguments.
    // For example, in the term (0 * x0 + 2 * x1), the value of x0 is irrelevant.
    // This function creates a new "reduced" term that eliminates some arguments.
    // The caller is responsible for identifying this new term with things.
    //
    // "eliminate" specifies which variables on the given term instance can be eliminated.
    fn eliminate_vars(
        &mut self,
        mapped_term: &MappedTerm,
        eliminate: impl Fn(AtomId) -> bool,
    ) -> TermInstance {
        let term_info = self.get_term_info(mapped_term.term_id);
        let mut reduced_arg_types = vec![];
        let mut reduced_var_map = vec![];
        for (i, v) in mapped_term.var_map.iter().enumerate() {
            if eliminate(*v) {
                continue;
            }
            reduced_var_map.push(*v);
            reduced_arg_types.push(term_info.arg_types[i]);
        }
        let reduced_term_info =
            TermInfo::new(term_info.term_type, reduced_arg_types, term_info.depth);
        let reduced_term_id = self.terms.len() as TermId;
        self.terms
            .push(TermInfoReference::TermInfo(reduced_term_info));
        TermInstance::mapped(reduced_term_id, reduced_var_map)
    }

    // The term we most want to keep compares as the largest in the keeping order.
    fn keeping_order(
        &self,
        left_instance: &TermInstance,
        right_instance: &TermInstance,
    ) -> Ordering {
        // If one of the terms is a variable, it is more keepable.
        let (left_id, right_id) = match left_instance {
            TermInstance::Variable(_) => return Ordering::Greater,
            TermInstance::Mapped(left) => match right_instance {
                TermInstance::Variable(_) => return Ordering::Less,
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

    // Identifies the two terms, and adds any followup Identifications to the queue rather than
    // processing them all.
    fn process_identify_terms(
        &mut self,
        instance1: TermInstance,
        instance2: TermInstance,
        pending: &mut VecDeque<Operation>,
    ) {
        let instance1 = self.update_term(instance1);
        let instance2 = self.update_term(instance2);
        if instance1 == instance2 {
            // Nothing to do
            return;
        }

        // Discard the term that we least want to keep
        let (discard_instance, keep_instance) = match self.keeping_order(&instance1, &instance2) {
            Ordering::Less => (instance1, instance2),
            Ordering::Greater => (instance2, instance1),
            Ordering::Equal => {
                // A permutation. So, whichever
                (instance1, instance2)
            }
        };

        let discard = match &discard_instance {
            TermInstance::Variable(_) => panic!("flow control error"),
            TermInstance::Mapped(t) => t,
        };

        match &keep_instance {
            TermInstance::Mapped(keep) => {
                if keep.var_map.iter().any(|v| !discard.var_map.contains(v)) {
                    // The "keep" term contains some arguments that the "discard" term doesn't.
                    // The "discard" term must also contain some arguments that the "keep" term
                    // doesn't, because otherwise we would have discarded the keep term.
                    // These arguments can be eliminated to form a third, reduced term.
                    let reduced_instance =
                        self.eliminate_vars(keep, |v| !discard.var_map.contains(&v));

                    // Identify both onto the reduced term.
                    // Note: order matters!
                    pending.push_front(Operation::Identification(
                        reduced_instance.clone(),
                        discard_instance,
                    ));
                    pending.push_front(Operation::Identification(keep_instance, reduced_instance));
                    return;
                }

                if keep.term_id == discard.term_id {
                    // This is a permutation of arguments.
                    let permutation =
                        permutation::compose_inverse(keep.var_map.clone(), discard.var_map.clone());
                    let term_info = self.mut_term_info(keep.term_id);
                    if term_info.symmetry.contains(&permutation) {
                        // We already know about this permutation
                        return;
                    }
                    term_info.symmetry.add(permutation);
                    // We track the symmetries we know about, but we don't use them to normalize
                    // anything.
                    return;
                }
            }
            TermInstance::Variable(i) => {
                if !discard_instance.has_var(*i) {
                    // We are trying to identify a variable x_i with a formula that doesn't
                    // have an x_i in it.
                    // That means that all values of this type must be the same.
                    // For now, this is considered to be a contradiction. We will only
                    // allow types with multiple things in them. The correct thing to do would
                    // be more like, identifying this type as a singleton and handling singleton
                    // types explicitly.
                    self.found_contradiction = true;
                    return;
                }
            }
        }

        // Find a TermInstance equal to the term to be discarded
        let new_instance = keep_instance.backward_map_vars(&discard.var_map);
        self.identify_term_id(discard.term_id, &new_instance, pending);
    }

    fn process_all(&mut self, pending: VecDeque<Operation>) {
        let mut pending = pending;
        let mut processed = 0;
        loop {
            match pending.pop_front() {
                Some(Operation::Identification(instance1, instance2)) => {
                    self.process_identify_terms(instance1, instance2, &mut pending);
                }
                None => break,
            }
            processed += 1;
            if processed > 50000 {
                panic!("too many operations");
            }
        }
    }

    //
    // Tools for interacting with more complicated graph things like DecomposedTerm and Literal.
    //

    pub fn insert_term(&mut self, term: &Term) -> TermInstance {
        let mut decomposed = self.linear_insert(term);
        decomposed.subterms.swap_remove(0).instance
    }

    // The linear insertion algorithm finds or creates O(n) graph nodes for a term of size n.
    // Imagine the term as a binary tree where each interior node is an "apply" operator
    // with two arguments.
    // We find or create a graph node for each node in this binary tree.
    //
    // The decomposition uses temporary variable ids, starting at the first available variable.
    pub fn linear_insert(&mut self, term: &Term) -> DecomposedTerm {
        let start_var = term.least_unused_variable();
        self.linear_insert_with_start_var(term, start_var)
    }

    // Helper function for linear insertion.
    // Turns the provided term into a DecomposedTerm, starting at start_var.
    fn linear_insert_with_start_var(&mut self, term: &Term, start_var: AtomId) -> DecomposedTerm {
        let head_instance = TypedTermInstance {
            term_type: term.head_type,
            instance: self.atomic_instance(term.head_type, term.head),
        };

        if term.is_atomic() {
            // This is a leaf term, the head instance is all we have
            return DecomposedTerm {
                subterms: vec![head_instance.clone()],
                start_var,
                replacement_values: vec![head_instance],
                subterm_sizes: vec![1],
            };
        }

        // The first subterm is the entire term, but we don't know its information yet.
        // So we populate all the rest of the information first, starting with the information
        // about the head of the root, and insert the root information at the end.
        // start_var will be the root term, with the first replacement being its type template.
        // start_var + 1 will be the head of the term.
        let mut replaced_vars = vec![start_var + 1];
        let mut args = vec![head_instance.clone()];
        let mut subterms = vec![head_instance.clone()];
        let mut replacement_values = vec![head_instance];
        let mut subterm_sizes = vec![1];
        let mut next_var = start_var + 2;

        for subterm in &term.args {
            let subterm_decomp = self.linear_insert_with_start_var(subterm, next_var);
            replaced_vars.push(next_var);
            args.push(subterm_decomp.subterms[0].clone());
            next_var += subterm_decomp.replacement_values.len() as AtomId;
            subterms.extend(subterm_decomp.subterms);
            replacement_values.extend(subterm_decomp.replacement_values);
            subterm_sizes.extend(subterm_decomp.subterm_sizes);
        }

        // Construct the type template instance for the root term
        let arg_types: Vec<_> = term.args.iter().map(|t| t.term_type).collect();
        let type_template_term_id =
            self.type_template_term_id(term.term_type, term.head_type, &arg_types);
        let type_template_instance = TypedTermInstance {
            term_type: term.term_type,
            instance: TermInstance::mapped(type_template_term_id, replaced_vars.clone()),
        };
        self.validate_typed_term_instance(&type_template_instance);

        // Construct a TermInstance for the root term
        let mut term_instance = type_template_instance.instance.clone();
        for (&var, arg) in replaced_vars.iter().zip(args.into_iter()) {
            let replacement = Replacement::new(var, arg.instance);
            let mut pending = VecDeque::new();
            term_instance =
                self.follow_or_create_edge(&term_instance, &replacement, None, &mut pending);
            self.process_all(pending);
        }

        // Insert the root term information at the beginning
        subterms.insert(
            0,
            TypedTermInstance {
                term_type: type_template_instance.term_type,
                instance: term_instance,
            },
        );
        replacement_values.insert(0, type_template_instance.clone());
        subterm_sizes.insert(0, replacement_values.len());

        DecomposedTerm {
            subterms,
            start_var,
            replacement_values,
            subterm_sizes,
        }
    }

    // Identifies the two terms, and continues processing any followup Identifications until
    // all Identifications are processed.
    pub fn make_equal(&mut self, instance1: TermInstance, instance2: TermInstance) {
        let mut ops = VecDeque::new();
        ops.push_front(Operation::Identification(instance1, instance2));
        self.process_all(ops);
    }

    // Sets these terms to be not equal.
    pub fn make_not_equal(&mut self, instance1: &TermInstance, instance2: &TermInstance) {
        if instance1 == instance2 {
            self.found_contradiction = true;
            return;
        }
        let mut inserted = 0;
        if let TermInstance::Mapped(t1) = instance1 {
            inserted += 1;
            self.make_mapped_term_not_equal(t1, instance2);
        }
        if let TermInstance::Mapped(t2) = instance2 {
            inserted += 1;
            self.make_mapped_term_not_equal(t2, instance1);
        }
        if inserted == 0 {
            panic!("observe_not_equal called with two variables");
        }
    }

    // Helper function
    fn make_mapped_term_not_equal(&mut self, mapped: &MappedTerm, instance: &TermInstance) {
        let new_instance = instance.extended_backward_map(&mapped.var_map);
        let info = self.mut_term_info(mapped.term_id);
        info.not_equal.insert(new_instance);
    }

    // Checks whether these terms are known to be equal or not equal.
    // "true" means that these terms are equal.
    // "false" means that these terms are not equal, for every value of the free variables.
    // "None" means that we don't know, or that they are only sometimes equal.
    fn evaluate_equality(
        &self,
        instance1: &TermInstance,
        instance2: &TermInstance,
    ) -> Option<bool> {
        if instance1 == instance2 {
            return Some(true);
        }
        let id1 = match instance1 {
            TermInstance::Mapped(t1) => {
                let new_instance = instance2.extended_backward_map(&t1.var_map);
                let info = self.get_term_info(t1.term_id);
                if info.not_equal.contains(&new_instance) {
                    return Some(false);
                } else {
                    return None;
                }
            }
            TermInstance::Variable(i) => i,
        };
        let id2 = match instance2 {
            TermInstance::Mapped(t2) => {
                let new_instance = instance1.extended_backward_map(&t2.var_map);
                let info = self.get_term_info(t2.term_id);
                if info.not_equal.contains(&new_instance) {
                    return Some(false);
                } else {
                    return None;
                }
            }
            TermInstance::Variable(i) => i,
        };
        if id1 == id2 {
            return Some(true);
        }
        None
    }

    pub fn insert_literal(&mut self, literal: &Literal) {
        let left = self.insert_term(&literal.left);
        let right = self.insert_term(&literal.right);
        if literal.positive {
            self.make_equal(left, right);
        } else {
            self.make_not_equal(&left, &right);
        }
    }

    // Checks if we have an evaluation for this literal.
    // Return Some(true) if this literal is true (for all values of the free variables).
    // Return Some(false) if this literal is false (for all values of the free variables).
    // Return None if we don't know or if the literal does not consistently evaluate.
    pub fn evaluate_literal(&mut self, literal: &Literal) -> Option<bool> {
        let left = self.insert_term(&literal.left);
        let right = self.insert_term(&literal.right);
        match self.evaluate_equality(&left, &right) {
            Some(equality) => {
                if literal.positive {
                    Some(equality)
                } else {
                    Some(!equality)
                }
            }
            None => None,
        }
    }

    //
    // Tools for testing and inspecting the term graph.
    //

    pub fn print_edge(&self, edge_id: EdgeId) {
        let edge_info = self.edges[edge_id as usize].as_ref().unwrap();
        let term_id = edge_info.key.template;
        print!(
            "edge {}: term {} = {}; {} => {}",
            edge_id,
            term_id,
            self.extract_term_id(term_id),
            self.edge_str(&edge_info.key.replacement),
            self.term_str(&edge_info.result)
        );
    }

    // Finds edges that connect two terms.
    // This ignores variables, so is only really useful for debugging.
    fn find_edges(&self, from: TermId, to: TermId) -> Option<Vec<EdgeId>> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back((from, vec![]));
        while let Some((term_id, path)) = queue.pop_front() {
            if term_id == to {
                return Some(path);
            }
            if !visited.insert(term_id) {
                continue;
            }
            let term_info = self.get_term_info(term_id);
            for edge_id in &term_info.adjacent {
                let edge_info = self.edges[*edge_id as usize].as_ref().unwrap();
                if edge_info.key.template == term_id {
                    if let Some(result_id) = edge_info.result.term_id() {
                        let mut path = path.clone();
                        path.push(*edge_id);
                        queue.push_back((result_id, path));
                    }
                }
            }
        }
        None
    }

    // A linear pass through the graph checking that everything is consistent.
    pub fn check(&self) {
        let mut all_terms: HashSet<String> = HashSet::new();
        let mut duplicate_term = None;
        for term_id in 0..self.terms.len() {
            let term_id = term_id as TermId;
            if let TermInfoReference::Replaced(ti) = self.get_term_info_ref(term_id) {
                println!("term {} has been replaced with {}", term_id, ti);
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
                let edge_info = self.edges[*edge_id as usize].as_ref().unwrap();
                if !edge_info.adjacent_terms().contains(&term_id) {
                    panic!(
                        "term {} thinks it is adjacent to edge {} ({:?}) but not vice versa",
                        term_id, edge_id, edge_info
                    );
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

            if all_terms.contains(&s) {
                duplicate_term = Some(s);
            } else {
                all_terms.insert(s);
            }
        }

        for edge_id in 0..self.edges.len() {
            let edge_id = edge_id as EdgeId;

            if !self.has_edge_info(edge_id) {
                continue;
            }
            self.print_edge(edge_id);
            let edge_info = self.edges[edge_id as usize].as_ref().unwrap();

            for term_id in edge_info.adjacent_terms().iter() {
                if !self.has_term_info(*term_id) {
                    panic!("edge {:?} refers to collapsed term {}", edge_info, term_id);
                }
                let term_info = self.get_term_info(*term_id);
                if !term_info.adjacent.contains(&edge_id) {
                    panic!(
                        "edge {:?} thinks it is adjacent to term {} but not vice versa",
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

        if let Some(duplicate_term) = duplicate_term {
            panic!("duplicate term: {}", duplicate_term);
        }
    }

    pub fn parse(&mut self, term_string: &str) -> TypedTermInstance {
        println!();
        println!("parsing: {}", term_string);
        let term = Term::parse(term_string);
        let instance = self.insert_term(&term);
        self.check();
        TypedTermInstance {
            term_type: term.term_type,
            instance,
        }
    }

    pub fn insert_literal_str(&mut self, literal_string: &str) {
        let literal = Literal::parse(literal_string);
        self.insert_literal(&literal);
    }

    pub fn evaluate_literal_str(&mut self, literal_string: &str) -> Option<bool> {
        let literal = Literal::parse(literal_string);
        self.evaluate_literal(&literal)
    }

    pub fn check_make_equal(&mut self, term1: &TypedTermInstance, term2: &TypedTermInstance) {
        println!();
        println!("making equal: {} = {}", term1.instance, term2.instance);
        self.make_equal(term1.instance.clone(), term2.instance.clone());
        self.check();
    }

    // Updates first for convenience
    pub fn check_equal(&self, term1: &TypedTermInstance, term2: &TypedTermInstance) {
        let t1 = self.update_term(term1.instance.clone());
        let t2 = self.update_term(term2.instance.clone());
        assert_eq!(t1, t2);
    }

    fn term_str(&self, term: &TermInstance) -> String {
        let updated = self.update_term(term.clone());
        let t = TypedTermInstance {
            term_type: ANY,
            instance: updated,
        };
        self.extract_term_instance(&t).to_string()
    }

    pub fn edge_str(&self, edge: &Replacement) -> String {
        format!("x{} -> {}", edge.var, self.term_str(&edge.value))
    }

    pub fn check_str(&self, term: &TypedTermInstance, s: &str) {
        assert_eq!(self.term_str(&term.instance), s)
    }

    pub fn check_path(&self, from: &TypedTermInstance, to: &TypedTermInstance) {
        let from = self.update_term(from.instance.clone());
        let to = self.update_term(to.instance.clone());
        let from_id = from.term_id().unwrap();
        let to_id = to.term_id().unwrap();
        let path = self.find_edges(from_id, to_id);
        if path.is_none() {
            panic!(
                "no path from term {} to term {}, {} to {}",
                from_id,
                to_id,
                self.term_str(&from),
                self.term_str(&to)
            );
        }
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
            "c0",
            "c1(x0)",
            "c1(x1)",
            "c2(x0, x1)",
            "c3(x0, x1, x2)",
            "c2(x3, x2)",
            "c2(c2(x0, x1), x2)",
            "c2(x1, x1)",
            "c3(x1, x3, x1)",
            "c1(c1(x1))",
            "c2(x0, c1(x1))",
            "c2(c2(x1, x0), c2(x0, x2))",
            "c2(c2(x0, x2), c2(x1, x0))",
            "c3(x0, c3(x1, c3(x0, x1, x0), c0), x1)",
        ]);
    }

    #[test]
    fn test_functional_arguments() {
        insert_and_extract(&["c0(x0)", "c0"]);
    }

    #[test]
    fn test_variable_heads() {
        insert_and_extract(&[
            "x0(x1)",
            "x0(x1(x2))",
            "x3(x1(x2), x1(c0))",
            "x4(c1(x8, x3), x0(x1), x0(c2))",
        ]);
    }

    #[test]
    fn test_insertion_efficiency() {
        let mut g = TermGraph::new();
        g.parse("c0(c1, c2, c3)");
        let pre_size = g.terms.len();
        g.parse("c0(x0, c2, c3)");
        let post_size = g.terms.len();
        assert!(
            post_size > pre_size,
            "c0(x0, c2, c3) should not be in the initial graph"
        );
    }

    #[test]
    fn test_identifying_terms() {
        let mut g = TermGraph::new();
        let c0 = g.parse("c0(c3)");
        let c1 = g.parse("c1(c3)");
        g.check_make_equal(&c0, &c1);
        let c2c0 = g.parse("c2(c0(c3))");
        let c2c1 = g.parse("c2(c1(c3))");
        assert_eq!(c2c0, c2c1);
    }

    #[test]
    fn test_updating_constructor() {
        let mut g = TermGraph::new();

        let c0 = g.parse("c0");
        let c1 = g.parse("c1");
        g.check_make_equal(&c0, &c1);
        let c2c0 = g.parse("c2(c0)");
        let c2c1 = g.parse("c2(c1)");
        assert_eq!(c2c0, c2c1);
    }

    #[test]
    fn test_apply_replacements() {
        let mut g = TermGraph::new();

        let c0 = g.parse("c0(x0, x1)");
        let c1 = g.parse("c1(x1, x0)");
        g.check_make_equal(&c0, &c1);
        g.check_equal(&c0, &c1);
    }

    #[test]
    fn test_duplicating_edge() {
        let mut g = TermGraph::new();

        let c0 = g.parse("c0");
        let c1 = g.parse("c1");
        g.parse("c2(c0)");
        g.parse("c2(c1)");
        g.check_make_equal(&c0, &c1);
        let c2c0 = g.parse("c2(c0)");
        let c2c1 = g.parse("c2(c1)");
        assert_eq!(c2c0, c2c1);
    }

    #[test]
    fn test_multi_hop_term_identification() {
        let mut g = TermGraph::new();

        let c0 = g.parse("c0");
        let c1 = g.parse("c1");
        let c2 = g.parse("c2");
        let c3 = g.parse("c3");
        g.check_make_equal(&c0, &c1);
        g.check_make_equal(&c2, &c3);
        g.check_make_equal(&c0, &c2);
        let c4c3 = g.parse("c4(c3)");
        let c4c1 = g.parse("c4(c1)");
        assert_eq!(c4c3, c4c1);
    }

    // #[test]
    // fn test_atom_identification() {
    //     let mut g = TermGraph::new();
    //     let c0x0x1 = g.parse("c0(x0, x1)");
    //     let c1x1x0 = g.parse("c1(x1, x0)");
    //     g.check_make_equal(&c0x0x1, &c1x1x0);
    //     let c0c2c3 = g.parse("c0(c2, c3)");
    //     let c1c3c2 = g.parse("c1(c3, c2)");
    //     assert_eq!(c0c2c3, c1c3c2);
    // }

    #[test]
    fn test_explicit_argument_collapse() {
        let mut g = TermGraph::new();

        let c0x0 = g.parse("c0(x0)");
        let c1 = g.parse("c1");
        g.check_make_equal(&c0x0, &c1);
        let c0c2 = g.parse("c0(c2)");
        let c0c3 = g.parse("c0(c3)");
        assert_eq!(c0c2, c0c3);
    }

    #[test]
    fn test_template_collapse() {
        let mut g = TermGraph::new();

        let c0x0 = g.parse("c0(x0)");
        // Make the less concise term the more popular one
        g.parse("c0(c2)");
        let c1 = g.parse("c1");
        g.check_make_equal(&c0x0, &c1);
        let c0c2 = g.parse("c0(c2)");
        let c0c3 = g.parse("c0(c3)");
        assert_eq!(c0c2, c0c3);
    }

    #[test]
    fn test_extracting_infinite_loop() {
        let mut g = TermGraph::new();

        let c0c0c1 = g.parse("c0(c1)");
        let other_term = g.parse("c2(c3)");
        g.check_make_equal(&c0c0c1, &other_term);
        let c1 = g.parse("c1");
        g.check_make_equal(&c0c0c1, &c1);
    }

    #[test]
    fn test_double_touched_edges() {
        let mut g = TermGraph::new();

        let c0c1c1 = g.parse("c0(c1, c1)");
        let c2 = g.parse("c2");
        g.check_make_equal(&c0c1c1, &c2);

        let c1 = g.parse("c1");
        let c2 = g.parse("c3");
        g.check_make_equal(&c1, &c2);

        let c0c3c3 = g.parse("c0(c3, c3)");
        let c2 = g.parse("c2");
        assert_eq!(c0c3c3, c2);
    }

    #[test]
    fn test_atom_vs_less_args() {
        let mut g = TermGraph::new();

        let c0x0 = g.parse("c0(x0)");
        let c1c2 = g.parse("c1(c2)");
        g.check_make_equal(&c0x0, &c1c2);
        g.check_str(&c0x0, "c0(_)");
        g.check_str(&c1c2, "c0(_)");
    }

    #[test]
    fn test_argument_collapse() {
        let mut g = TermGraph::new();

        let term1 = g.parse("c0(c1, x0, x1, x2, x3)");
        let term2 = g.parse("c0(c1, x0, x4, x2, x5)");
        g.check_make_equal(&term1, &term2);
        g.check_str(&term1, "c0(c1, x0, _, x2, _)");
    }

    #[test]
    fn test_inference_from_argument_collapse() {
        let mut g = TermGraph::new();

        let c0x0 = g.parse("c0(x0)");
        let c1x1 = g.parse("c1(x1)");
        g.check_make_equal(&c0x0, &c1x1);
        let c0c2 = g.parse("c0(c2)");
        let c0c3 = g.parse("c0(c3)");
        assert_eq!(c0c2, c0c3);

        check_insert(&mut g, "c0(x0)", "c0(_)");
    }

    #[test]
    fn test_identifying_with_the_identity() {
        let mut g = TermGraph::new();

        let c0x0 = g.parse("c0(x0)");
        let x0 = g.parse("x0");
        g.check_make_equal(&c0x0, &x0);
        let c0c1 = g.parse("c0(c1)");
        let c1 = g.parse("c1");
        assert_eq!(c0c1, c1);
    }

    #[test]
    fn test_edge_template_identifying_with_variable() {
        let mut g = TermGraph::new();

        g.parse("c0(c1)");
        let x0 = g.parse("x0");
        let c0x0 = g.parse("c0(x0)");
        g.check_make_equal(&x0, &c0x0);
    }

    #[test]
    fn test_template_discovery() {
        let mut g = TermGraph::new();

        let c0c1x0 = g.parse("c0(c1, x0)");
        let c2 = g.parse("c2");
        g.check_make_equal(&c0c1x0, &c2);
        let c0c1c3 = g.parse("c0(c1, c3)");
        let c2 = g.parse("c2");
        assert_eq!(c0c1c3, c2);
    }

    // #[test]
    // fn test_ignoring_var_in_replacement() {
    //     let mut g = TermGraph::new();
    //     let template = g.parse("c0(x0, c1(x1))");
    //     let reduction = g.parse("c2(x0)");
    //     g.check_make_equal(&template, &reduction);
    //     let matching = g.parse("c0(x0, c1(c3))");
    //     let expected = g.parse("c2(x0)");
    //     assert_eq!(matching, expected);
    // }

    #[test]
    fn test_eliminating_a_replacement_var() {
        let mut g = TermGraph::new();

        let c0c1x0 = g.parse("c0(c1(x0))");
        let c2x0 = g.parse("c2(x0)");
        g.check_make_equal(&c0c1x0, &c2x0);
        let c1x0 = g.parse("c1(x0)");
        let c3 = g.parse("c3");
        g.check_make_equal(&c1x0, &c3);
    }

    // #[test]
    // fn test_ignoring_two_vars() {
    //     let mut g = TermGraph::new();
    //     let template = g.parse("c0(c1(x0), x1)");
    //     let reduction = g.parse("c2");
    //     g.check_make_equal(&template, &reduction);
    //     let matching = g.parse("c0(c1(c3), x1)");
    //     let expected = g.parse("c2");
    //     assert_eq!(matching, expected);
    // }

    // #[test]
    // fn test_single_speculation() {
    //     let mut g = TermGraph::new();
    //     let template = g.parse("c0(x0, c2)");
    //     let result = g.parse("c0(c1, c2)");
    //     g.check_path(&template, &result);
    // }

    // #[test]
    // fn test_double_speculation_base_first() {
    //     let mut g = TermGraph::new();
    //     let base_term = g.parse("x0(x1, c2, x3, c4)");
    //     let leaf_term = g.parse("x0(c1, c2, c3, c4)");
    //     g.check_path(&base_term, &leaf_term);
    // }

    // #[test]
    // fn test_double_speculation_leaf_first() {
    //     let mut g = TermGraph::new();
    //     let leaf_term = g.parse("x0(c1, c2, c3, c4)");
    //     let base_term = g.parse("x0(x1, c2, x3, c4)");
    //     g.check_path(&base_term, &leaf_term);
    // }

    // #[test]
    // fn test_long_template() {
    //     let mut g = TermGraph::new();
    //     let template = g.parse("c0(x0, c1, x2, c2(x3), x4)");
    //     let reduction = g.parse("c3(x2)");
    //     g.check_make_equal(&template, &reduction);
    //     let matching = g.parse("c0(c4, c1, x0, c2(c5), x1)");
    //     let expected = g.parse("c3(x0)");
    //     assert_eq!(matching, expected);
    // }

    #[test]
    fn test_unused_vars_on_both_sides() {
        let mut g = TermGraph::new();

        let template = g.parse("c0(c1, x0)");
        let reduction = g.parse("c2(x1)");
        g.check_make_equal(&template, &reduction);
        let left = g.parse("c0(c1, c3)");
        let right = g.parse("c2(c4)");
        assert_eq!(left, right);
    }

    // #[test]
    // fn test_implicit_unification() {
    //     let mut g = TermGraph::new();
    //     let template = g.parse("c0(c1, x0)");
    //     let reduction = g.parse("c2");
    //     g.check_make_equal(&template, &reduction);
    //     let template = g.parse("c0(x0, c1)");
    //     let reduction = g.parse("c3");
    //     g.check_make_equal(&template, &reduction);
    //     g.parse("c0(c1, c1)");
    //     let c2 = g.parse("c2");
    //     let c3 = g.parse("c3");
    //     assert_eq!(c2, c3);
    // }

    // #[test]
    // fn test_implicit_three_way_unification() {
    //     let mut g = TermGraph::new();
    //     let template = g.parse("c0(c1, x0, x1)");
    //     let reduction = g.parse("c2");
    //     g.check_make_equal(&template, &reduction);
    //     let template = g.parse("c0(x0, c1, x1)");
    //     let reduction = g.parse("c3");
    //     g.check_make_equal(&template, &reduction);
    //     let template = g.parse("c0(x0, x1, c1)");
    //     let reduction = g.parse("c4");
    //     g.check_make_equal(&template, &reduction);
    //     g.parse("c0(c1, c1, c1)");
    //     let c3 = g.parse("c3");
    //     let c4 = g.parse("c4");
    //     assert_eq!(c3, c4);
    // }

    // #[test]
    // fn test_variable_used_only_in_replacement() {
    //     let mut g = TermGraph::new();
    //     let template = g.parse("c0(x0, c1(x1))");
    //     let reduction = g.parse("c2(x0)");
    //     g.check_make_equal(&template, &reduction);
    //     let left = g.parse("c2(c3)");
    //     let right = g.parse("c0(c3, c1(c4))");
    //     assert_eq!(left, right);
    // }

    #[test]
    fn test_reducing_var_through_self_identify() {
        let mut g = TermGraph::new();

        let first = g.parse("c0(x0, x1)");
        let second = g.parse("c0(x0, x2)");
        g.check_make_equal(&first, &second);
        let left = g.parse("c0(c1, c2)");
        let right = g.parse("c0(c1, c3)");
        assert_eq!(left, right);
    }

    // #[test]
    // fn test_cyclic_argument_identification() {
    //     let mut g = TermGraph::new();
    //     let base = g.parse("c0(x0, x1, x2)");
    //     let rotated = g.parse("c0(x1, x2, x0)");
    //     g.check_make_equal(&base, &rotated);
    //     let term1 = g.parse("c0(c1, c2, c3)");
    //     let term2 = g.parse("c0(c2, c3, c1)");
    //     assert_eq!(term1, term2);
    //     let term3 = g.parse("c0(c3, c1, c2)");
    //     assert_eq!(term1, term3);
    //     let term4 = g.parse("c0(c1, c3, c2)");
    //     assert_ne!(term1, term4);
    //     let term5 = g.parse("c0(c3, c2, c1)");
    //     assert_eq!(term4, term5);
    //     let term6 = g.parse("c0(c2, c1, c3)");
    //     assert_eq!(term4, term6);
    // }

    // #[test]
    // fn test_adding_symmetry_later() {
    //     let mut g = TermGraph::new();
    //     let c0c1c2 = g.parse("c0(c1, c2)");
    //     let c3 = g.parse("c3");
    //     g.check_make_equal(&c0c1c2, &c3);
    //     let c0c2c1 = g.parse("c0(c2, c1)");
    //     let c4 = g.parse("c4");
    //     g.check_make_equal(&c0c2c1, &c4);
    //     let c0x0x1 = g.parse("c0(x0, x1)");
    //     let c0x1x0 = g.parse("c0(x1, x0)");
    //     g.check_make_equal(&c0x0x1, &c0x1x0);
    //     let c3 = g.parse("c3");
    //     let c4 = g.parse("c4");
    //     assert_eq!(c3, c4);
    // }

    // #[test]
    // fn test_identifying_with_variable() {
    //     let mut g = TermGraph::new();
    //     let c0x0c1 = g.parse("c0(x0, c1)");
    //     let x0 = g.parse("x0");
    //     g.check_make_equal(&c0x0c1, &x0);
    //     let c0c2c1 = g.parse("c0(c2, c1)");
    //     let c2 = g.parse("c2");
    //     assert_eq!(c0c2c1, c2);
    // }

    // #[test]
    // fn test_identifying_with_variable_seeing_template_last() {
    //     let mut g = TermGraph::new();
    //     g.parse("c0(c2, c1)");
    //     let c0x0c1 = g.parse("c0(x0, c1)");
    //     let x0 = g.parse("x0");
    //     g.check_make_equal(&c0x0c1, &x0);
    //     let c0c2c1 = g.parse("c0(c2, c1)");
    //     let c2 = g.parse("c2");
    //     assert_eq!(c0c2c1, c2);
    // }

    // #[test]
    // fn test_repeated_variable() {
    //     let mut g = TermGraph::new();
    //     let c0x0x0 = g.parse("c0(x0, x0)");
    //     let c0c1c1 = g.parse("c0(c1, c1)");
    //     let c2 = g.parse("c2");
    //     g.check_make_equal(&c2, &c0x0x0);
    //     g.check_equal(&c2, &c0c1c1);
    // }

    // #[test]
    // fn test_repeated_variable_seeing_template_last() {
    //     let mut g = TermGraph::new();
    //     let c0c1c1 = g.parse("c0(c1, c1)");
    //     let c0x0x0 = g.parse("c0(x0, x0)");
    //     let c2 = g.parse("c2");
    //     g.check_make_equal(&c2, &c0x0x0);
    //     g.check_equal(&c2, &c0c1c1);
    // }

    // #[test]
    // fn test_literal_evaluation() {
    //     let mut g = TermGraph::new();
    //     g.insert_literal_str("c0(x0, c1) = x0");
    //     assert_eq!(g.evaluate_literal_str("c0(x0, c1) = x0"), Some(true));
    //     assert_eq!(g.evaluate_literal_str("c0(c2, c1) = c2"), Some(true));
    //     assert_eq!(g.evaluate_literal_str("c0(x0, x1) = x0"), None);
    //     assert_eq!(g.evaluate_literal_str("c0(x0, c1) != x0"), Some(false));
    //     g.insert_literal_str("x0 = x0");
    //     assert_eq!(g.evaluate_literal_str("x0 = c0"), None);
    //     assert_eq!(g.evaluate_literal_str("c0 = x0"), None);
    //     assert_eq!(g.evaluate_literal_str("c0 = c0"), Some(true));
    // }

    #[test]
    fn test_linear_insert() {
        let mut g = TermGraph::new();
        let s = "c0(c1, c2(c3), x0(c4, x1, c5(c6, c7)))";
        let term = Term::parse(s);
        let decomp = g.linear_insert(&term);
        assert_eq!(decomp.subterm_sizes.len(), 14);

        let subterm = |i: usize| {
            let sub = &decomp.subterms[i].instance;
            g.term_str(sub)
        };

        assert_eq!(subterm(0), "c0(c1, c2(c3), x0(c4, x1, c5(c6, c7)))");
        assert_eq!(subterm(1), "c0");
        assert_eq!(subterm(2), "c1");
        assert_eq!(subterm(3), "c2(c3)");
        assert_eq!(subterm(4), "c2");
        assert_eq!(subterm(5), "c3");
        assert_eq!(subterm(6), "x0(c4, x1, c5(c6, c7))");
        assert_eq!(subterm(7), "x0");
        assert_eq!(subterm(8), "c4");
        assert_eq!(subterm(9), "x1");
        assert_eq!(subterm(10), "c5(c6, c7)");
        assert_eq!(subterm(11), "c5");
        assert_eq!(subterm(12), "c6");
        assert_eq!(subterm(13), "c7");
    }
}
