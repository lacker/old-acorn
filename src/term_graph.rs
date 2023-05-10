use std::collections::{HashMap, HashSet};
use std::fmt;

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
// Note that an abstract term does not have a "head", so its term_type is the type
// that it has after all the args are replaced with substitutions.
pub struct TermInfo {
    term_type: TypeId,
    arg_types: Vec<TypeId>,

    // All edges that touch this term
    adjacent: HashSet<EdgeId, BuildNoHashHasher<EdgeId>>,

    // The canonical way to produce this term.
    canonical: CanonicalForm,
}
pub type TermId = u32;

// Information about how an atom gets turned into a term.
// Each atom has a default expansion, represented by term, but we also
// need to track the type of the atom itself, so that we know how to extract it.
pub struct AtomInfo {
    head_type: TypeId,
    term: TermId,
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

pub struct EdgeInfo {
    // The parameters that determine the substitution
    key: EdgeKey,

    // The result of the substitution
    result: TermInstance,
}
pub type EdgeId = u32;

impl EdgeInfo {}

// The canonical form of a term can be:
//   a plain atom
//   a way of recursively constructing this term
//   a generic template for a type like x0(x1, x2) with no items specified
enum CanonicalForm {
    Atom(Atom),
    Edge(EdgeId),
    TypeTemplate(TypeId),
}

pub struct TermGraph {
    terms: Vec<TermInfo>,
    edges: Vec<EdgeInfo>,

    // We expand non-variable atoms into different terms depending on the number of
    // arguments they have. This lets us handle, for example, "add(2, 3)" and "reduce(add, mylist)".
    // The second parameter to the index is the number of arguments.
    atoms: HashMap<(Atom, u8), AtomInfo>,

    // Templates that let us expand terms where the head is a variable.
    // Keyed on the type of the head.
    // This lets us represent terms like x0(x1, x2).
    type_templates: HashMap<TypeId, TermId, BuildNoHashHasher<TypeId>>,

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

    pub fn get_term_info(&self, term: TermId) -> &TermInfo {
        &self.terms[term as usize]
    }

    pub fn get_edge_info(&self, edge: EdgeId) -> &EdgeInfo {
        &self.edges[edge as usize]
    }

    pub fn get_atom_info(&self, atom: Atom, num_args: u8) -> &AtomInfo {
        self.atoms.get(&(atom, num_args)).unwrap()
    }

    // Returns the term that is the result of the given substitution.
    // If it's already in the graph, returns the existing term with an appropriate instance.
    // Otherwise, creates a new edge and a new term and returns the new term.
    // Should not be called on noop keys or unnormalized keys.
    // The type of the output is the same as the type of the key's template.
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
            canonical,
        };
        let edge_info = EdgeInfo {
            key: key.clone(),
            result,
        };

        // Insert everything into the graph
        self.terms.push(term_info);
        self.terms[key.template as usize].adjacent.insert(edge_id);
        for r in &key.replacements {
            if let Replacement::Expand(term) = r {
                self.terms[term.term as usize].adjacent.insert(edge_id);
            }
        }
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
        if replacements_are_noop(&new_replacements) {
            // No need to even do a substitution
            return TermInstance {
                term: template.term,
                var_map: new_to_old,
            };
        }
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
            let type_template = self
                .type_templates
                .entry(term.head_type)
                .or_insert_with(|| {
                    let type_template = self.terms.len() as TermId;
                    // The head of the term counts as one of the args in the template
                    let mut arg_types = vec![term.head_type];
                    arg_types.extend(term.args.iter().map(|a| a.term_type));
                    self.terms.push(TermInfo {
                        term_type: term.term_type,
                        arg_types,
                        adjacent: HashSet::default(),
                        canonical: CanonicalForm::TypeTemplate(term.head_type),
                    });
                    type_template
                });
            let var_map = (0..(term.args.len() + 1) as AtomId).collect();
            let template_instance = TermInstance {
                term: *type_template,
                var_map,
            };

            let mut replacements = vec![Replacement::Rename(i)];
            for arg in &term.args {
                replacements.push(self.insert_term(arg));
            }
            return Replacement::Expand(self.replace(&template_instance, &replacements));
        }

        // Handle the (much more common) case where the head is not a variable
        let atom_key = (term.head, term.args.len() as u8);
        let head_id = if let Some(atom_info) = self.atoms.get(&atom_key) {
            atom_info.term
        } else {
            let head_id = self.terms.len() as TermId;
            self.terms.push(TermInfo {
                term_type: term.term_type,
                arg_types: term.args.iter().map(|a| a.term_type).collect(),
                adjacent: HashSet::default(),
                canonical: CanonicalForm::Atom(term.head),
            });
            let atom_info = AtomInfo {
                term: head_id,
                head_type: term.head_type,
            };
            self.atoms.insert(atom_key, atom_info);
            head_id
        };
        let head_var_map: Vec<_> = (0..term.args.len() as AtomId).collect();
        let head = TermInstance {
            term: head_id,
            var_map: head_var_map,
        };

        // Substitute the arguments into the head
        let replacements = term.args.iter().map(|a| self.insert_term(a)).collect();
        Replacement::Expand(self.replace(&head, &replacements))
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
            CanonicalForm::Edge(edge_id) => &self.edges[edge_id as usize],
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

    // An expensive checking that everything in the graph is coherent.
    pub fn check(&self) {
        let mut all_terms: HashSet<String> = HashSet::new();
        for term_id in 0..self.terms.len() {
            let term = self.extract_term_id(term_id as TermId);
            let s = term.to_string();
            println!("term {}: {}", term_id, s);
            assert!(!all_terms.contains(&s), "duplicate term: {}", s);
            all_terms.insert(s);
        }

        for key in self.edgemap.keys() {
            key.check();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn insert_and_extract(term_strings: &[&str]) {
        let mut g = TermGraph::new();
        for s in term_strings {
            let input = Term::parse(s);
            let ti = g.insert_term(&input).assert_is_expansion();
            println!("extracting {}", s);
            let output = g.extract_term_instance(&ti);
            if input != output {
                panic!("\ninput {} != output {}\n", input, output);
            }
        }
        g.check();
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
        insert_and_extract(&["x0(x1)", "x0(x1(x2))"]);
    }
}
