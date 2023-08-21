use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;
use std::{fmt, mem, vec};

use fxhash::FxHashMap;
use nohash_hasher::BuildNoHashHasher;

use crate::atom::{Atom, AtomId, INVALID_ATOM_ID};
use crate::permutation;
use crate::permutation_group::PermutationGroup;
use crate::specializer::Specializer;
use crate::term::{Literal, Term, TermFormatter};
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

    // The number of variables used in the replacements.
    // This can be larger than the number of variables used in the result, if the result ignores
    // some of the variables.
    vars_used: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub struct EdgeInfo {
    // The parameters that determine the substitution
    key: EdgeKey,

    // The result of the substitution.
    // This can have reordered variable ids but not duplicated or non-consecutive ones.
    result: TermInstance,
}
pub type EdgeId = u32;

#[derive(Debug, Eq, PartialEq)]
struct SimpleEdge {
    // The variable we are replacing
    var: AtomId,

    // What we replace it with
    replacement: TermInstance,
}

// An operation on the graph that is pending.
// We keep a pending operation queue rather than doing operations immediately so that we
// can control when we do expensive operations.
enum Operation {
    // Make these two term instances represent the same thing.
    Identification(TermInstance, TermInstance),

    // Infer new relations based on this new edge
    Inference(EdgeId),
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
    edge_key_map: FxHashMap<EdgeKey, EdgeId>,

    // Whether to use "fat edges" mode
    fat_edges: bool,

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

    // Calls f on each variable id used by this term
    fn for_var(&self, f: &mut impl FnMut(&AtomId)) {
        match self {
            TermInstance::Mapped(term) => {
                for &var in &term.var_map {
                    f(&var);
                }
            }
            TermInstance::Variable(var_id) => f(var_id),
        }
    }

    fn has_var(&self, i: AtomId) -> bool {
        match self {
            TermInstance::Mapped(term) => term.var_map.iter().any(|&j| j == i),
            TermInstance::Variable(j) => *j == i,
        }
    }

    fn variable(&self) -> Option<AtomId> {
        match self {
            TermInstance::Mapped(_) => None,
            TermInstance::Variable(var_id) => Some(*var_id),
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

    // A version of this term with variables normalized.
    fn normalize_vars(&self) -> TermInstance {
        match self {
            TermInstance::Mapped(term) => {
                TermInstance::mapped(term.term_id, (0..term.var_map.len() as AtomId).collect())
            }
            TermInstance::Variable(_) => TermInstance::Variable(0),
        }
    }

    fn num_vars(&self) -> usize {
        match self {
            TermInstance::Mapped(term) => term.var_map.len(),
            TermInstance::Variable(_) => 1,
        }
    }

    fn as_mapped(&self) -> &MappedTerm {
        match self {
            TermInstance::Mapped(term) => term,
            TermInstance::Variable(_) => panic!("TermInstance is a variable"),
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

impl SimpleEdge {
    fn replace(var: AtomId, replacement: MappedTerm) -> SimpleEdge {
        SimpleEdge {
            var,
            replacement: TermInstance::Mapped(replacement),
        }
    }

    fn identify(from: AtomId, to: AtomId) -> SimpleEdge {
        SimpleEdge {
            var: from,
            replacement: TermInstance::Variable(to),
        }
    }

    fn new(var: AtomId, replacement: TermInstance) -> SimpleEdge {
        SimpleEdge { var, replacement }
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
        assert_eq!(
            expected, self.vars_used as AtomId,
            "edge key {} uses {} vars but vars_used is {}",
            self, expected, self.vars_used
        );

        if self.is_noop() {
            panic!("edge is a noop");
        }
    }

    // Whether this is an edge that does nothing, taking the template to itself
    pub fn is_noop(&self) -> bool {
        self.replacements
            .iter()
            .enumerate()
            .all(|(i, r)| r.variable() == Some(i as AtomId))
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
//
// This is useful when we want to create new edges, and check whether an edge that
// "does the same thing" already exists.
//
// This function takes "new_to_old" as a constraint on the replacements. It can be
// empty if we don't want to constrain them.
fn normalize_replacements(
    replacements: &Vec<TermInstance>,
    new_to_old: &mut Vec<AtomId>,
) -> Vec<TermInstance> {
    let mut new_replacements = vec![];
    for r in replacements {
        match r {
            TermInstance::Variable(old_var) => {
                // Figure out the new id for this variable
                let new_var = match new_to_old.iter().position(|&v| v == *old_var) {
                    Some(i) => i,
                    None => {
                        let new_var = new_to_old.len();
                        new_to_old.push(*old_var);
                        new_var
                    }
                };
                new_replacements.push(TermInstance::Variable(new_var as AtomId));
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
    new_replacements
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

    // Renumbers the variables in the replacements so that the replacements work with the
    // normalize_vars version of the result.
    //
    // This is useful when we want to analyze edges that already exist, rather than
    // creating a new edge.
    fn normalize_result(&self) -> Vec<TermInstance> {
        let mut var_map = match &self.result {
            TermInstance::Mapped(term) => term.var_map.clone(),
            TermInstance::Variable(_) => {
                // The result is a variable, ie x0, so the replacements are already normalized
                return self.key.replacements.clone();
            }
        };
        normalize_replacements(&self.key.replacements, &mut var_map)
    }

    // Renumbers the variables so that they are relative to the provided template and result.
    // The provided template may skip numbers, so we return a vec of (var id, replacement).
    // It isn't sorted.
    fn relativize_replacements(
        &self,
        provided_template: &MappedTerm,
        provided_result: &MappedTerm,
    ) -> Vec<(AtomId, TermInstance)> {
        let mut answer = vec![];
        for (i, r) in self.key.replacements.iter().enumerate() {
            // The edge replaces x_i with r.
            // The provided template has a different number for x_i.
            let provided_template_var = provided_template.var_map[i as usize];

            // We also have a different numbering for r.
            let renumbered_replacement = r.forward_map_vars(&provided_result.var_map);

            answer.push((provided_template_var, renumbered_replacement));
        }
        answer
    }

    // Returns a SimpleEdge describing this edge in terms of the variable numbering used in
    // the provided template instance.
    //
    // Any new variables used are allocated starting at next_var.
    // This includes both variables introduced in the replacement, and the variable introduced
    // by combining two variables in the template.
    //
    // Returns the simple edge, the result term instance, and the least unused variable after
    // taking into account all variables in the template, replacement, and result.
    fn simplify(
        &self,
        template_instance: &MappedTerm,
        next_var: AtomId,
    ) -> (SimpleEdge, TermInstance, AtomId) {
        assert_eq!(self.key.template, template_instance.term_id);

        // We need to renumber the variables that are in the result instance.
        // Keep track of the renumbering.
        let mut result_rename = vec![INVALID_ATOM_ID; self.key.vars_used];

        let mut simple_edge: Option<SimpleEdge> = None;
        let mut next_var = next_var;

        // Deal with replacements at the end, so that we know which variable ids are
        // renames of existing variables, and which are new variables.
        let mut replacement_info: Option<(AtomId, &MappedTerm)> = None;

        for (i, rep) in template_instance.var_map.iter().zip(&self.key.replacements) {
            match rep {
                TermInstance::Mapped(r) => {
                    // This is a "replace" edge.
                    assert_eq!(replacement_info, None);
                    replacement_info = Some((*i, &r));
                }
                TermInstance::Variable(j) => {
                    // This edge is renaming x_i -> x_j
                    let existing = result_rename[*j as usize];
                    if existing != INVALID_ATOM_ID {
                        // This is an "identify" edge. It is renumbering both
                        // x_existing and x_i to x_j.
                        assert_eq!(simple_edge, None);
                        simple_edge = Some(SimpleEdge::identify(*i, existing));
                    } else {
                        result_rename[*j as usize] = *i;
                    }
                }
            }
        }

        if let Some((i, replacement)) = replacement_info {
            assert_eq!(simple_edge, None);

            // Renumber the replacement's var_map so that reused variables are correct,
            // and newly introduced variables get new variable numbers.
            let var_map = replacement.var_map.iter().map(|&j| {
                let existing = result_rename[j as usize];
                if existing == INVALID_ATOM_ID {
                    // This is a new variable, introduced by the replacement.
                    let answer = next_var;
                    next_var += 1;
                    result_rename[j as usize] = answer;
                    answer
                } else {
                    existing
                }
            });

            simple_edge = Some(SimpleEdge::replace(
                i,
                MappedTerm {
                    term_id: replacement.term_id,
                    var_map: var_map.collect(),
                },
            ));
        }

        match simple_edge {
            Some(simple_edge) => {
                let instance = self.result.forward_map_vars(&result_rename);
                (simple_edge, instance, next_var)
            }
            None => {
                panic!("noop edge in simplify");
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
            fat_edges: false,
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

    fn has_edge_info(&self, edge: EdgeId) -> bool {
        self.edges[edge as usize].is_some()
    }

    fn get_edge_info(&self, edge: EdgeId) -> &EdgeInfo {
        &self.edges[edge as usize].as_ref().unwrap()
    }

    fn take_edge_info(&mut self, edge: EdgeId) -> EdgeInfo {
        self.edges[edge as usize].take().unwrap()
    }

    // An EdgeKey represents a substitution. The EdgeKey object can exist before the
    // analogous edge in the graph exists.
    // This method creates the analogous edge and term if they don't already exist.
    // Should not be called on noop keys or unnormalized keys.
    //
    // Returns the term that this edge leads to.
    // The type of the output is the same as the type of the key's template.
    //
    // Creating an edge can cause terms in the graph to collapse, so any term you have
    // before calling expand_edge_key may need to be updated.
    fn expand_edge_key(&mut self, key: EdgeKey, pending: &mut VecDeque<Operation>) -> TermInstance {
        // Check if this edge is already in the graph
        if let Some(edge_id) = self.edge_key_map.get(&key) {
            return self.get_edge_info(*edge_id).result.clone();
        }

        // Figure out the type signature of our new term
        let template = self.get_term_info(key.template);
        let mut max_edge_depth = template.depth;
        let mut result_arg_types = vec![];
        for (i, replacement) in key.replacements.iter().enumerate() {
            match replacement {
                TermInstance::Variable(j) => {
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
        let term_id = self.terms.len() as TermId;
        let term_type = template.term_type;
        let num_args = result_arg_types.len() as AtomId;
        let var_map: Vec<AtomId> = (0..num_args).collect();
        let result = MappedTerm { term_id, var_map };
        let term_info = TermInfo::new(term_type, result_arg_types, max_edge_depth + 1);
        let answer = TermInstance::Mapped(result);
        let edge_info = EdgeInfo {
            key,
            result: answer.clone(),
        };

        // Insert everything into the graph
        self.terms.push(TermInfoReference::TermInfo(term_info));
        let edge_id = self.insert_edge_info(edge_info);
        if self.fat_edges {
            self.infer_from_fat_edge(edge_id, pending);
        } else {
            pending.push_back(Operation::Inference(edge_id));
        }
        answer
    }

    // Returns an EdgeKey along with a new_to_old map that shows how we renumbered the variables.
    fn normalize_edge_key(
        &self,
        template: TermId,
        replacements: Vec<TermInstance>,
    ) -> (EdgeKey, Vec<AtomId>) {
        // Use the template's symmetry group to normalize the replacements
        let template_info = self.get_term_info(template);
        let replacements = template_info.symmetry.normalize(replacements);

        // Number variables in ascending order
        let mut new_to_old = vec![];
        let replacements = normalize_replacements(&replacements, &mut new_to_old);
        let key = EdgeKey {
            template,
            replacements,
            vars_used: new_to_old.len(),
        };
        (key, new_to_old)
    }

    // Does a substitution with the given template and replacements.
    // Creates new entries in the term graph if necessary.
    // This does not have to be normalized.
    fn replace_in_term_id(
        &mut self,
        template: TermId,
        replacements: Vec<TermInstance>,
        pending: &mut VecDeque<Operation>,
    ) -> TermInstance {
        // The overall strategy is to normalize the replacements, do the substitution with
        // the graph, and then map from new ids back to old ones.
        let (key, new_to_old) = self.normalize_edge_key(template, replacements);
        if key.is_noop() {
            // No need to even do a substitution
            return TermInstance::mapped(template, new_to_old);
        }
        let new_term = self.expand_edge_key(key, pending);
        new_term.forward_map_vars(&new_to_old)
    }

    // Does a substitution with the given template and replacements.
    // Creates new entries in the term graph if necessary.
    fn replace_in_term_instance(
        &mut self,
        template: &TermInstance,
        replacements: &Vec<TermInstance>,
        pending: &mut VecDeque<Operation>,
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
                self.replace_in_term_id(template.term_id, new_replacements, pending)
            }
            TermInstance::Variable(i) => replacements[*i as usize].clone(),
        }
    }

    // Inserts an edge into the graph, if it isn't there already.
    // Returns the term instance that it leads to.
    fn insert_edge(
        &mut self,
        template: &TermInstance,
        edge: &SimpleEdge,
        pending: &mut VecDeque<Operation>,
    ) -> TermInstance {
        match template {
            TermInstance::Mapped(template) => {
                let replacements = template
                    .var_map
                    .iter()
                    .map(|&v| {
                        if v == edge.var {
                            edge.replacement.clone()
                        } else {
                            TermInstance::Variable(v)
                        }
                    })
                    .collect();
                self.replace_in_term_id(template.term_id, replacements, pending)
            }
            TermInstance::Variable(i) => {
                if i == &edge.var {
                    edge.replacement.clone()
                } else {
                    template.clone()
                }
            }
        }
    }

    pub fn insert_term(&mut self, term: &Term) -> TermInstance {
        if self.fat_edges {
            self.insert_term_fat(term)
        } else {
            self.insert_term_skinny(term)
        }
    }

    // Inserts a new term.
    // Returns the existing term if there is one.
    fn insert_term_fat(&mut self, term: &Term) -> TermInstance {
        assert!(self.fat_edges);
        if term.is_true() {
            panic!("True should not be a separate node in the term graph")
        }
        if let Some(i) = term.atomic_variable() {
            return TermInstance::Variable(i);
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
                    let mut term_info = TermInfo::new(term.term_type, arg_types, 0);
                    term_info.type_template = Some(term.head_type);
                    self.terms.push(TermInfoReference::TermInfo(term_info));
                    type_template
                });
            let mut replacements = vec![TermInstance::Variable(i)];
            for arg in &term.args {
                replacements.push(self.insert_term_fat(arg));
            }
            let mut pending = VecDeque::new();
            let answer = self.replace_in_term_id(type_template, replacements, &mut pending);
            self.process_all(pending);
            return self.update_term(answer);
        }

        // Handle the (much more common) case where the head is not a variable
        let atom_key = (term.head, term.args.len() as u8);
        if !self.atoms.contains_key(&atom_key) {
            let head_id = self.terms.len() as TermId;
            let mut term_info = TermInfo::new(
                term.term_type,
                term.args.iter().map(|a| a.term_type).collect(),
                0,
            );
            term_info.atom_keys.push(atom_key.clone());
            self.terms.push(TermInfoReference::TermInfo(term_info));
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
        let replacements: Vec<_> = term.args.iter().map(|a| self.insert_term_fat(a)).collect();
        let mut pending = VecDeque::new();
        let answer = self.replace_in_term_instance(&term_instance, &replacements, &mut pending);
        self.process_all(pending);
        self.update_term(answer)
    }

    // Get a TermInstance for a type template, plus the number of variables used.
    // A type template is a term where everything is a variable.
    // Like x0(x1, x2).
    // The variables will be numbered in increasing order, but you can decide where to start at.
    // This will use (arg_types.len() + 1) variables.
    fn type_template_instance(
        &mut self,
        term_type: TypeId,
        head_type: TypeId,
        arg_types: &Vec<TypeId>,
        next_var: AtomId,
    ) -> (TermInstance, AtomId) {
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

        // Construct the instance by shifting the variable numbers
        let delta = 1 + arg_types.len() as AtomId;
        (
            TermInstance::mapped(*term_id, (next_var..(next_var + delta)).collect()),
            delta,
        )
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

    // Inserts a new term using "skinny edges".
    // A skinny edge is one that:
    //   * changes only a single variable
    //   * uses only new variables in replacements
    // Returns the existing term if there is one.
    fn insert_term_skinny(&mut self, term: &Term) -> TermInstance {
        assert!(!self.fat_edges);
        if let Some(i) = term.atomic_variable() {
            return TermInstance::Variable(i);
        }

        // We accumulate an instance by substituting in one atom or type template at a time
        let mut accumulated_instance: Option<TermInstance> = None;

        // Temporary variables, used during construction only, start numbering here
        let mut next_var = term.least_unused_variable();

        // Stored in reverse order for nice popping
        let mut temporary_vars: Vec<AtomId> = vec![];

        let mut pending: VecDeque<Operation> = VecDeque::new();

        let mut answer = None;

        for (term_type, head_type, head, arg_types) in term.inorder() {
            assert_eq!(answer, None);
            if arg_types.len() > 0 {
                // Expand the accumulated instance with a type template
                let (type_template_instance, vars_used) =
                    self.type_template_instance(term_type, head_type, &arg_types, next_var);
                if let Some(instance) = accumulated_instance {
                    let replace_var = temporary_vars.pop().unwrap();
                    let replaced = self.insert_edge(
                        &instance,
                        &SimpleEdge::new(replace_var, type_template_instance),
                        &mut pending,
                    );
                    accumulated_instance = Some(replaced);
                } else {
                    // This is the root type template for the term
                    accumulated_instance = Some(type_template_instance);
                }
                next_var += vars_used;
                for i in 0..vars_used {
                    temporary_vars.push(next_var - 1 - i);
                }
            } else if accumulated_instance == None {
                // This term is just a single constant.
                answer = Some(self.atomic_instance(head_type, head));
                break;
            }

            // Expand the accumulated instance with an atom
            let replace_var = temporary_vars.pop().unwrap();
            let atomic_instance = self.atomic_instance(head_type, head);
            let replaced = self.insert_edge(
                &accumulated_instance.unwrap(),
                &SimpleEdge::new(replace_var, atomic_instance),
                &mut pending,
            );
            accumulated_instance = Some(replaced);

            if temporary_vars.is_empty() {
                answer = accumulated_instance;
                break;
            }
        }

        let answer = answer.unwrap();
        self.process_all(pending);
        self.update_term(answer)
    }

    // The depth of an edge is the maximum depth of any term that its key references.
    fn edge_depth(&self, edge_id: EdgeId) -> u32 {
        let edge_info = self.get_edge_info(edge_id);
        let template_info = self.get_term_info(edge_info.key.template);
        let mut max_depth = template_info.depth;
        for rep in &edge_info.key.replacements {
            if let TermInstance::Mapped(term) = rep {
                let term_info = self.get_term_info(term.term_id);
                max_depth = std::cmp::max(max_depth, term_info.depth);
            }
        }
        max_depth
    }

    // Find the least deep edge that creates this term
    // Panics if no edge creates this term.
    // Don't call this for terms that are atoms or type templates.
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
        let edge_info = self.get_edge_info(edge_id);

        // Construct a Term according to the information provided by the edge
        let template = self.extract_term_id(edge_info.key.template);
        let template_info = self.get_term_info(edge_info.key.template);
        let mut s = Specializer::new();
        for (i, r) in edge_info.key.replacements.iter().enumerate() {
            let i = i as AtomId;
            match r {
                TermInstance::Variable(j) => {
                    let var_type = template_info.arg_types[i as usize];
                    assert!(s.match_var(i, &Term::atom(var_type, Atom::Variable(*j))));
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
            TermInstance::Variable(_) => panic!("shallowest edge should never be a variable"),
        };
        unmapped_term.unmap_variables(var_map)
    }

    pub fn extract_term_instance(&self, instance: &TypedTermInstance) -> Term {
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

    // Inserts an edge, updating the appropriate maps.
    // The edge must not already exist.
    fn insert_edge_info(&mut self, edge_info: EdgeInfo) -> EdgeId {
        let new_edge_id = self.edges.len() as EdgeId;
        self.edge_key_map.insert(edge_info.key.clone(), new_edge_id);
        for term in edge_info.adjacent_terms() {
            let mut_term = self.mut_term_info(term);
            mut_term.adjacent.insert(new_edge_id);
        }
        self.edges.push(Some(edge_info));
        new_edge_id
    }

    // Removes an edge, updating the appropriate maps.
    // The edge must exist.
    fn remove_edge(&mut self, edge_id: EdgeId) -> EdgeInfo {
        let old_edge_info = self.take_edge_info(edge_id);
        for term in old_edge_info.adjacent_terms() {
            match &mut self.terms[term as usize] {
                TermInfoReference::Replaced(_) => (),
                TermInfoReference::TermInfo(term_info) => {
                    term_info.adjacent.remove(&edge_id);
                }
            }
        }
        self.edge_key_map.remove(&old_edge_info.key);
        old_edge_info
    }

    // Inserts a single edge that already has a normalized key.
    // If it's a duplicate, identify the appropriate terms instead.
    // When this discovers more valid Identifications it pushes them onto pending.
    fn process_normalized_edge(&mut self, edge_info: EdgeInfo, pending: &mut VecDeque<Operation>) {
        // Check to see if the new edge is a duplicate
        if let Some(duplicate_edge_id) = self.edge_key_map.get(&edge_info.key) {
            let duplicate_edge_info = self.get_edge_info(*duplicate_edge_id);
            // new_edge_info and duplicate_edge_info are the same edge, but
            // they may go to different terms.
            // This means we need to identify the terms.
            pending.push_back(Operation::Identification(
                edge_info.result,
                duplicate_edge_info.result.clone(),
            ));
            return;
        }

        let edge_id = self.insert_edge_info(edge_info);
        if !self.fat_edges {
            pending.push_back(Operation::Inference(edge_id));
        }
    }

    // Replaces old_term_id with new_term in the given edge.
    // This can lead us to discover new Identifications, which we push onto pending.
    fn replace_edge_term(
        &mut self,
        old_edge_id: EdgeId,
        old_term_id: TermId,
        new_term: &TermInstance,
        pending: &mut VecDeque<Operation>,
    ) {
        let old_edge_info = self.remove_edge(old_edge_id);

        // The result and the replacements are relatively straightforward, we just recurse.
        let new_result = old_edge_info.result.replace_term_id(old_term_id, new_term);
        let new_replacements: Vec<_> = old_edge_info
            .key
            .replacements
            .iter()
            .map(|replacement| replacement.replace_term_id(old_term_id, new_term))
            .collect();

        if old_edge_info.key.template == old_term_id {
            // We're also replacing the template
            self.process_unnormalized_edge(new_term, &new_replacements, new_result, pending);
        } else {
            // The template is unchanged, but we still have to renormalize the edge
            let template = old_edge_info.key.template_instance();
            self.process_unnormalized_edge(&template, &new_replacements, new_result, pending);
        }
    }

    // Replaces all references to old_term_id with references to new_term.
    // The caller should be sure that old_term_id has not been replaced already.
    // When this discovers more valid Identifications it pushes them onto pending.
    fn replace_term_id(
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
            self.replace_edge_term(*old_edge_id, old_term_id, new_term, pending);
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

    // Handles a template + replacements -> result data that is not normalized.
    // This might lead to a new edge but it might not.
    fn process_unnormalized_edge(
        &mut self,
        template: &TermInstance,
        replacements: &Vec<TermInstance>,
        result: TermInstance,
        pending: &mut VecDeque<Operation>,
    ) {
        let mapped_term = match template {
            TermInstance::Mapped(term) => term,
            TermInstance::Variable(var_id) => {
                let new_template = &replacements[*var_id as usize];
                // We want to identify new_template and new_result here.
                pending.push_back(Operation::Identification(new_template.clone(), result));
                return;
            }
        };

        // Renumber the replacements so that they are relative to term_id rather than the instance
        let new_replacements = mapped_term
            .var_map
            .iter()
            .map(|v| {
                if *v >= replacements.len() as AtomId {
                    panic!(
                        "template {:?} has variable {} but only {} replacements",
                        mapped_term,
                        v,
                        replacements.len()
                    );
                }
                replacements[*v as usize].clone()
            })
            .collect();

        let (key, new_to_old) = self.normalize_edge_key(mapped_term.term_id, new_replacements);

        let normalized_result = if result.num_vars() > new_to_old.len() {
            // The result must have some variables that aren't in new_to_old at all.
            if let TermInstance::Mapped(mapped_result) = &result {
                // We can eliminate these variables
                let reduced_result =
                    self.eliminate_vars(mapped_result, |v| !new_to_old.contains(&v));
                pending.push_back(Operation::Identification(result, reduced_result.clone()));
                reduced_result.forward_map_vars(&new_to_old)
            } else {
                panic!("a replacement with no variables becomes a variable. what does this mean?");
            }
        } else {
            result.forward_map_vars(&new_to_old)
        };

        if key.is_noop() {
            // There's no edge here, we just want to identify two terms
            pending.push_back(Operation::Identification(
                key.template_instance(),
                normalized_result,
            ));
            return;
        }

        self.process_normalized_edge(
            EdgeInfo {
                key,
                result: normalized_result,
            },
            pending,
        );
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
                    // These arguments can be eliminated.
                    let reduced_instance =
                        self.eliminate_vars(keep, |v| !discard.var_map.contains(&v));

                    // Identify both onto the reduced term
                    // Note: order matters!
                    pending.push_back(Operation::Identification(
                        keep_instance,
                        reduced_instance.clone(),
                    ));
                    pending.push_back(Operation::Identification(
                        reduced_instance,
                        discard_instance,
                    ));
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
                    let term_info = self.get_term_info(keep.term_id);

                    // Find all edges that have this term as the template
                    let mut edge_ids: Vec<EdgeId> = vec![];
                    for edge_id in &term_info.adjacent {
                        let edge_info = self.get_edge_info(*edge_id);
                        if edge_info.key.template == keep.term_id {
                            edge_ids.push(*edge_id);
                        }
                    }

                    // Find the edges that need to be renormalized
                    for edge_id in edge_ids {
                        let edge_info = self.get_edge_info(edge_id);
                        if edge_info.key.template != keep.term_id {
                            continue;
                        }

                        let (key, new_to_old) = self
                            .normalize_edge_key(keep.term_id, edge_info.key.replacements.clone());
                        if key == edge_info.key {
                            // The edge is already normalized
                            continue;
                        }

                        let result = edge_info.result.forward_map_vars(&new_to_old);
                        self.process_normalized_edge(EdgeInfo { key, result }, pending);
                    }
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
        self.replace_term_id(discard.term_id, &new_instance, pending);
    }

    fn process_all(&mut self, pending: VecDeque<Operation>) {
        let mut pending = pending;
        loop {
            match pending.pop_front() {
                Some(Operation::Identification(instance1, instance2)) => {
                    self.process_identify_terms(instance1, instance2, &mut pending);
                }
                Some(Operation::Inference(edge_id)) => {
                    assert!(!self.fat_edges);
                    self.infer_from_skinny_edge(edge_id, &mut pending);
                }
                None => break,
            }
        }
    }

    // Identifies the two terms, and continues processing any followup Identifications until
    // all Identifications are processed.
    pub fn make_equal(&mut self, instance1: TermInstance, instance2: TermInstance) {
        let mut ops = VecDeque::new();
        ops.push_back(Operation::Identification(instance1, instance2));
        self.process_all(ops)
    }

    // Sets these terms to be not equal.
    // The caller should handle the contradictory case where they are already known to be equal.
    pub fn make_not_equal(&mut self, instance1: &TermInstance, instance2: &TermInstance) {
        assert_ne!(instance1, instance2);
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

    // Find edges that can be a template expansion to create this term.
    // The edges are returned as a map from template id to a list of edges from that template.
    // When where more than one substitution is possible, we pick the first one, trying to
    // get the "simpler" edge. This is a heuristic but maybe it's okay.
    //
    // Does not include the cases where a single variable expands into
    // this term, or where a term maps to itself.
    fn inbound_edge_map(
        &self,
        term_id: TermId,
    ) -> HashMap<TermId, EdgeId, BuildNoHashHasher<TermId>> {
        let term_info = self.get_term_info(term_id);
        let mut answer: HashMap<TermId, EdgeId, BuildNoHashHasher<TermId>> = HashMap::default();
        for edge_id in &term_info.adjacent {
            let edge_info = self.get_edge_info(*edge_id);
            if edge_info.result.term_id() == Some(term_id) {
                //  Keep the smallest edge id in answer
                answer
                    .entry(edge_info.key.template)
                    .and_modify(|i| *i = (*i).min(*edge_id))
                    .or_insert(*edge_id);
            }
        }
        answer
    }

    // All edges that result in this term.
    fn inbound_edges(&self, term_id: TermId) -> Vec<EdgeId> {
        let term_info = self.get_term_info(term_id);
        term_info
            .adjacent
            .iter()
            .filter(move |edge_id| {
                let edge_info = self.get_edge_info(**edge_id);
                edge_info.result.term_id() == Some(term_id)
            })
            .copied()
            .collect()
    }

    // All edges that use this term as a template.
    fn outbound_edges(&self, term_id: TermId) -> Vec<EdgeId> {
        let term_info = self.get_term_info(term_id);
        term_info
            .adjacent
            .iter()
            .filter(move |edge_id| {
                let edge_info = self.get_edge_info(**edge_id);
                edge_info.key.template == term_id
            })
            .copied()
            .collect()
    }

    // Look for edges that can fit this pattern:
    // A -> B -> C
    //
    // A -> C is the "long edge" that we start with.
    // A -> B is the "short edge" that we will look for.
    // B -> C is the "new edge" that we will create, when the long and short edges are compatible.
    fn infer_from_fat_edge(&mut self, long_edge_id: EdgeId, pending: &mut VecDeque<Operation>) {
        assert!(self.fat_edges);
        let long_edge_info = self.get_edge_info(long_edge_id);
        let long_reps = long_edge_info.normalize_result();
        let long_result = long_edge_info.result.normalize_vars();

        // Find inbound edges for each of the replacements.
        // When they are a rename, leave the inbound entry as "None".
        let inbound: Vec<Option<_>> = long_edge_info
            .key
            .replacements
            .iter()
            .map(|r| match r {
                TermInstance::Variable(_) => None,
                TermInstance::Mapped(t) => Some(self.inbound_edge_map(t.term_id)),
            })
            .collect();

        // Check all the short edges that are compatible with the long edge.
        let outbound_edges = self.outbound_edges(long_edge_info.key.template);
        for short_edge_id in outbound_edges {
            if long_edge_id == short_edge_id {
                continue;
            }
            let short_edge_info = self.get_edge_info(short_edge_id);
            let short_reps = &short_edge_info.normalize_result();
            assert_eq!(short_reps.len(), inbound.len());

            // This replacements vector starts with Nones when we have no idea what
            // the replacement is going to be, and we fill it in as we go.
            // We create it using the endpoint-normalized numbering.
            let mut replacements: Vec<Option<TermInstance>> =
                vec![None; short_edge_info.key.vars_used];
            let mut found_conflict = false;
            for (template_var_id, short_rep) in short_reps.iter().enumerate() {
                let long_rep = &long_reps[template_var_id];
                match short_rep {
                    TermInstance::Variable(short_var_id) => {
                        // The short edge renames template_var_id to short_var_id.
                        // So the new edge must treat short_var_id the same way that
                        // the long edge treats template_var_id.
                        if let Some(existing) = &replacements[*short_var_id as usize] {
                            if existing != long_rep {
                                found_conflict = true;
                                break;
                            }
                        } else {
                            replacements[*short_var_id as usize] = Some(long_rep.clone());
                        }
                    }
                    TermInstance::Mapped(short_mapped_term) => match long_rep {
                        TermInstance::Variable(_) => {
                            // The short edge does something with this variable, but
                            // the long edge doesn't. This is a conflict, unless perhaps
                            // there's a substitution that turns something back into nothing,
                            // like neg(x) with x := neg(x) creating x, but let's ignore that
                            // case for now.
                            found_conflict = true;
                            break;
                        }
                        TermInstance::Mapped(long_mapped_term) => {
                            let short_term_id = short_mapped_term.term_id;
                            if long_mapped_term.term_id == short_term_id {
                                // No edge is necessary to turn the short term into the long term.
                                // We just need to make sure our variable renumbering is compatible.
                                // Ignore the permutation case for now.
                                for (i, short_var_id) in
                                    short_mapped_term.var_map.iter().enumerate()
                                {
                                    let long_var_id = long_mapped_term.var_map[i];
                                    let expected = TermInstance::Variable(long_var_id);
                                    if let Some(existing) = &replacements[*short_var_id as usize] {
                                        if existing != &expected {
                                            found_conflict = true;
                                            break;
                                        }
                                    } else {
                                        replacements[*short_var_id as usize] = Some(expected);
                                    }
                                }
                                continue;
                            }

                            // This should always exist due to the construction of inbound
                            let inbound_edges = inbound[template_var_id].as_ref().unwrap();

                            // Figure out what edge takes the short term to the long term
                            // Call this the "minor edge", kind of running out of coherent names here
                            let minor_edge_info = match inbound_edges.get(&short_term_id) {
                                Some(edge) => self.get_edge_info(*edge),
                                None => {
                                    found_conflict = true;
                                    break;
                                }
                            };

                            let minor_reps = minor_edge_info
                                .relativize_replacements(short_mapped_term, long_mapped_term);
                            for (i, r) in minor_reps {
                                if let Some(existing) = &replacements[i as usize] {
                                    if *existing != r {
                                        found_conflict = true;
                                        break;
                                    }
                                } else {
                                    replacements[i as usize] = Some(r);
                                }
                            }
                        }
                    },
                }
            }
            if found_conflict {
                continue;
            }

            // We can create a new edge.
            let template = short_edge_info.result.normalize_vars();

            // The short edge could use variables that are dropped in the intermediate term.
            // So these replacements could include some we won't use, and we have to trim them so
            // that they only use variables that are in the replacements.
            let trimmed_replacements = replacements
                .into_iter()
                .take(template.num_vars())
                .map(|r| r.unwrap())
                .collect::<Vec<_>>();

            self.process_unnormalized_edge(
                &template,
                &trimmed_replacements,
                long_result.clone(),
                pending,
            );
        }
    }

    // Checks for any inferences from a pair of consecutive edges.
    // The edges should form a pattern:
    //
    // A -> B -> C
    //
    // where the first edge goes A -> B, the second goes B -> C.
    fn infer_from_edge_pair(
        &mut self,
        ab_edge_id: EdgeId,
        bc_edge_id: EdgeId,
        pending: &mut VecDeque<Operation>,
    ) {
        // Create term instances that use the same numbering scheme for all of A, B, and C.
        let ab_edge_info = self.get_edge_info(ab_edge_id);
        let instance_a = ab_edge_info.key.template_instance();
        let mapped_a = instance_a.as_mapped();
        let num_a_vars = mapped_a.var_map.len() as AtomId;
        let (ab_edge, instance_b, num_ab_vars) = ab_edge_info.simplify(mapped_a, num_a_vars);
        let mapped_b = instance_b.as_mapped();
        let bc_edge_info = self.get_edge_info(bc_edge_id);
        let (bc_edge, instance_c, _) = bc_edge_info.simplify(mapped_b, num_ab_vars);

        match (&ab_edge.replacement, &bc_edge.replacement) {
            (TermInstance::Mapped(ab_rep), TermInstance::Mapped(bc_rep)) => {
                if bc_edge.var >= num_a_vars {
                    // B->C is changing a variable that was newly introduced in A->B.
                    // This means we can do a "combining" inference, to introduce a composite term
                    // in one step.
                    let composite_instance =
                        self.insert_edge(&ab_edge.replacement, &bc_edge, pending);
                    let one_step_result = self.insert_edge(
                        &instance_a,
                        &SimpleEdge::new(ab_edge.var, composite_instance),
                        pending,
                    );
                    pending.push_back(Operation::Identification(instance_c, one_step_result));
                    return;
                }

                if ab_rep.var_map.contains(&bc_edge.var) {
                    // B->C is changing a variable that exists in A, but the A->B replacement also
                    // used that variable.
                    // TODO: handle this case
                    return;
                }

                if ab_rep == bc_rep {
                    // A->B->C is swapping the same thing in for multiple variables.
                    // We could also do a variable combination first, then a substitution.
                    let combine_first = self.insert_edge(
                        &instance_a,
                        &SimpleEdge::identify(ab_edge.var, bc_edge.var),
                        pending,
                    );
                    let then_substitute = self.insert_edge(&combine_first, &bc_edge, pending);
                    pending.push_back(Operation::Identification(
                        instance_c.clone(),
                        then_substitute,
                    ));
                }

                // B->C doesn't change anything that was affected by A->B.
                // So we can do a "commuting" inference.
                let bc_first = self.insert_edge(&instance_a, &bc_edge, pending);
                let bc_then_ab = self.insert_edge(&bc_first, &ab_edge, pending);
                pending.push_back(Operation::Identification(instance_c, bc_then_ab));
                return;
            }
            (TermInstance::Variable(ab_keep_id), TermInstance::Mapped(_)) => {
                if *ab_keep_id == bc_edge.var {
                    // B->C is substituting into the variable that A->B identified.
                    // TODO: handle this case
                    return;
                } else {
                    // These operations purely commute.
                    let bc_first = self.insert_edge(&instance_a, &bc_edge, pending);
                    let bc_then_ab = self.insert_edge(&bc_first, &ab_edge, pending);
                    pending.push_back(Operation::Identification(instance_c, bc_then_ab));
                    return;
                }
            }
            (TermInstance::Variable(ab_keep_id), TermInstance::Variable(bc_keep_id)) => {
                if ab_keep_id == bc_keep_id {
                    // Both edge vars are getting identified into bc_keep_id.
                    // They are getting identified into their final value directly.
                    // Try doing it in the other order
                    let one_step = self.insert_edge(&instance_a, &bc_edge, pending);
                    let two_steps = self.insert_edge(&one_step, &ab_edge, pending);
                    pending.push_back(Operation::Identification(instance_c.clone(), two_steps));

                    // Try identifying them together first
                    let one_step = self.insert_edge(
                        &instance_a,
                        &SimpleEdge::identify(ab_edge.var, bc_edge.var),
                        pending,
                    );
                    let two_steps = self.insert_edge(&one_step, &bc_edge, pending);
                    pending.push_back(Operation::Identification(instance_c, two_steps));
                    return;
                }

                // TODO: do we want to infer from the other cases?
                return;
            }
            (TermInstance::Mapped(_), TermInstance::Variable(_)) => {
                // TODO: do we want to infer from this case?
                return;
            }
        }
    }

    // Look for inferences that involve this edge.
    fn infer_from_skinny_edge(&mut self, edge_id: EdgeId, pending: &mut VecDeque<Operation>) {
        if !self.has_edge_info(edge_id) {
            // This edge has been collapsed
            return;
        }
        let edge_info = self.get_edge_info(edge_id);
        let result_term_id = edge_info.result.term_id();

        // Find A -> B -> C patterns where this edge is B -> C
        let template_term_id = edge_info.key.template;
        let inbound_edges = self.inbound_edges(template_term_id);
        for inbound_edge_id in inbound_edges {
            self.infer_from_edge_pair(inbound_edge_id, edge_id, pending);
        }

        // Find A -> B -> C patterns where this edge is A -> B
        if let Some(result_term_id) = result_term_id {
            let outbound_edges = self.outbound_edges(result_term_id);
            for outbound_edge_id in outbound_edges {
                self.infer_from_edge_pair(edge_id, outbound_edge_id, pending);
            }
        }
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

    pub fn print_edge(&self, edge_id: EdgeId) {
        let edge_info = self.get_edge_info(edge_id);
        let template = self.extract_term_id(edge_info.key.template);
        print!(
            "edge {}: in term {}, {},",
            edge_id,
            edge_info.key.template,
            TermFormatter {
                term: &template,
                var: 'y'
            }
        );
        for (i, replacement) in edge_info.key.replacements.iter().enumerate() {
            let untyped_rep = TypedTermInstance {
                term_type: ANY,
                instance: replacement.clone(),
            };
            let term = self.extract_term_instance(&untyped_rep);
            print!(
                "{} y{} = {}",
                if i == 0 { " replacing" } else { "," },
                i,
                term
            );
        }
        let untyped_result = TypedTermInstance {
            term_type: ANY,
            instance: edge_info.result.clone(),
        };
        let result = self.extract_term_instance(&untyped_result);
        match &edge_info.result {
            TermInstance::Mapped(t) => {
                println!(" yields term {}, {}", t.term_id, result);
            }
            TermInstance::Variable(_) => {
                println!(" yields variable {}", result);
            }
        }
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

            if all_terms.contains(&s) {
                duplicate_term = Some(s);
            } else {
                all_terms.insert(s);
            }
        }

        let mut edge_keys_and_ids = self.edge_key_map.iter().collect::<Vec<_>>();
        // Sort by id
        edge_keys_and_ids.sort_by_key(|(_, id)| *id);

        for (key, edge_id) in edge_keys_and_ids {
            key.check();
            if !self.has_edge_info(*edge_id) {
                panic!("edge {} has been collapsed", edge_id);
            }
            self.print_edge(*edge_id);
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

    pub fn check_str(&self, term: &TypedTermInstance, s: &str) {
        assert_eq!(self.term_str(&term.instance), s)
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

    #[test]
    fn test_atom_identification() {
        let mut g = TermGraph::new();

        let c0x0x1 = g.parse("c0(x0, x1)");
        let c1x1x0 = g.parse("c1(x1, x0)");
        g.check_make_equal(&c0x0x1, &c1x1x0);
        let c0c2c3 = g.parse("c0(c2, c3)");
        let c1c3c2 = g.parse("c1(c3, c2)");
        assert_eq!(c0c2c3, c1c3c2);
    }

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

    #[test]
    fn test_ignoring_var_in_replacement() {
        let mut g = TermGraph::new();

        let template = g.parse("c0(x0, c1(x1))");
        let reduction = g.parse("c2(x0)");
        g.check_make_equal(&template, &reduction);
        let matching = g.parse("c0(x0, c1(c3))");
        let expected = g.parse("c2(x0)");
        assert_eq!(matching, expected);
    }

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

    #[test]
    fn test_ignoring_two_vars() {
        let mut g = TermGraph::new();

        let template = g.parse("c0(c1(x0), x1)");
        let reduction = g.parse("c2");
        g.check_make_equal(&template, &reduction);
        let matching = g.parse("c0(c1(c3), x1)");
        let expected = g.parse("c2");
        assert_eq!(matching, expected);
    }

    #[test]
    fn test_long_template() {
        let mut g = TermGraph::new();

        let template = g.parse("c0(x0, c1, x2, c2(x3), x4)");
        let reduction = g.parse("c3(x2)");
        g.check_make_equal(&template, &reduction);
        let matching = g.parse("c0(c4, c1, x0, c2(c5), x1)");
        let expected = g.parse("c3(x0)");
        assert_eq!(matching, expected);
    }

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

    #[test]
    fn test_variable_used_only_in_replacement() {
        let mut g = TermGraph::new();

        let template = g.parse("c0(x0, c1(x1))");
        let reduction = g.parse("c2(x0)");
        g.check_make_equal(&template, &reduction);
        let left = g.parse("c2(c3)");
        let right = g.parse("c0(c3, c1(c4))");
        assert_eq!(left, right);
    }

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

    #[test]
    fn test_cyclic_argument_identification() {
        let mut g = TermGraph::new();

        let base = g.parse("c0(x0, x1, x2)");
        let rotated = g.parse("c0(x1, x2, x0)");
        g.check_make_equal(&base, &rotated);

        let term1 = g.parse("c0(c1, c2, c3)");
        let term2 = g.parse("c0(c2, c3, c1)");
        assert_eq!(term1, term2);

        let term3 = g.parse("c0(c3, c1, c2)");
        assert_eq!(term1, term3);

        let term4 = g.parse("c0(c1, c3, c2)");
        assert_ne!(term1, term4);

        let term5 = g.parse("c0(c3, c2, c1)");
        assert_eq!(term4, term5);

        let term6 = g.parse("c0(c2, c1, c3)");
        assert_eq!(term4, term6);
    }

    #[test]
    fn test_adding_symmetry_later() {
        let mut g = TermGraph::new();

        let c0c1c2 = g.parse("c0(c1, c2)");
        let c3 = g.parse("c3");
        g.check_make_equal(&c0c1c2, &c3);

        let c0c2c1 = g.parse("c0(c2, c1)");
        let c4 = g.parse("c4");
        g.check_make_equal(&c0c2c1, &c4);

        let c0x0x1 = g.parse("c0(x0, x1)");
        let c0x1x0 = g.parse("c0(x1, x0)");
        g.check_make_equal(&c0x0x1, &c0x1x0);

        let c3 = g.parse("c3");
        let c4 = g.parse("c4");
        assert_eq!(c3, c4);
    }

    #[test]
    fn test_identifying_with_variable() {
        let mut g = TermGraph::new();

        let c0x0c1 = g.parse("c0(x0, c1)");
        let x0 = g.parse("x0");
        g.check_make_equal(&c0x0c1, &x0);
        let c0c2c1 = g.parse("c0(c2, c1)");
        let c2 = g.parse("c2");
        assert_eq!(c0c2c1, c2);
    }

    #[test]
    fn test_identifying_with_variable_seeing_template_last() {
        let mut g = TermGraph::new();

        g.parse("c0(c2, c1)");

        let c0x0c1 = g.parse("c0(x0, c1)");
        let x0 = g.parse("x0");
        g.check_make_equal(&c0x0c1, &x0);
        let c0c2c1 = g.parse("c0(c2, c1)");
        let c2 = g.parse("c2");
        assert_eq!(c0c2c1, c2);
    }

    #[test]
    fn test_repeated_variable() {
        let mut g = TermGraph::new();

        let c0x0x0 = g.parse("c0(x0, x0)");
        let c0c1c1 = g.parse("c0(c1, c1)");
        let c2 = g.parse("c2");
        g.check_make_equal(&c2, &c0x0x0);
        g.check_equal(&c2, &c0c1c1);
    }

    #[test]
    fn test_repeated_variable_seeing_template_last() {
        let mut g = TermGraph::new();

        let c0c1c1 = g.parse("c0(c1, c1)");
        let c0x0x0 = g.parse("c0(x0, x0)");
        let c2 = g.parse("c2");
        g.check_make_equal(&c2, &c0x0x0);
        g.check_equal(&c2, &c0c1c1);
    }

    #[test]
    fn test_literal_evaluation() {
        let mut g = TermGraph::new();

        g.insert_literal_str("c0(x0, c1) = x0");
        assert_eq!(g.evaluate_literal_str("c0(x0, c1) = x0"), Some(true));
        assert_eq!(g.evaluate_literal_str("c0(c2, c1) = c2"), Some(true));
        assert_eq!(g.evaluate_literal_str("c0(x0, x1) = x0"), None);
        assert_eq!(g.evaluate_literal_str("c0(x0, c1) != x0"), Some(false));

        g.insert_literal_str("x0 = x0");
        assert_eq!(g.evaluate_literal_str("x0 = c0"), None);
        assert_eq!(g.evaluate_literal_str("c0 = x0"), None);
        assert_eq!(g.evaluate_literal_str("c0 = c0"), Some(true));
    }
}
