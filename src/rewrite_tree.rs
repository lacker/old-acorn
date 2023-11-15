use qp_trie::{SubTrie, Trie};

use crate::atom::Atom;
use crate::term::Term;
use crate::type_map::TypeId;

// The TermComponent is designed so that a &[TermComponent] represents a preorder
// traversal of the term, and each subterm is represented by a subslice.
#[derive(Debug, PartialEq, Eq, Clone)]
enum TermComponent {
    // The u16 is the number of term components in the term, including this one.
    // Must be at least 3. Otherwise this would just be an atom.
    Composite(TypeId, u16),

    Atom(TypeId, Atom),
}

impl TermComponent {
    // The number of TermComponents in the component starting with this one
    fn size(&self) -> usize {
        match self {
            TermComponent::Composite(_, size) => *size as usize,
            TermComponent::Atom(_, _) => 1,
        }
    }

    fn increase_size(&mut self, delta: u16) {
        match self {
            TermComponent::Composite(_, size) => *size += delta,
            TermComponent::Atom(_, _) => panic!("cannot increase size of atom"),
        }
    }
}

fn flatten_next(term: &Term, output: &mut Vec<TermComponent>) {
    if term.args.is_empty() {
        output.push(TermComponent::Atom(term.term_type, term.head));
        return;
    }

    let initial_size = output.len();

    // The zero is a placeholder. We'll fill in the real size later.
    output.push(TermComponent::Composite(term.term_type, 0));
    output.push(TermComponent::Atom(term.head_type, term.head));
    for arg in &term.args {
        flatten_next(arg, output);
    }

    // Now we can fill in the real size
    let real_size = output.len() - initial_size;
    println!("XXX real size = {}", real_size);
    output[initial_size] = TermComponent::Composite(term.term_type, real_size as u16);
}

fn flatten_term(term: &Term) -> Vec<TermComponent> {
    let mut output = Vec::new();
    flatten_next(term, &mut output);
    output
}

// Constructs a term, starting at components[i].
// Returns the next unused index and the term.
fn unflatten_next(components: &[TermComponent], i: usize) -> (usize, Term) {
    match components[i] {
        TermComponent::Composite(term_type, size) => {
            let size = size as usize;
            let (head_type, head) = match components[i + 1] {
                TermComponent::Atom(head_type, head) => (head_type, head),
                _ => panic!("Composite term must have an atom as its head"),
            };

            let mut args = Vec::new();
            let mut j = i + 2;
            while j < i + size {
                let (next_j, arg) = unflatten_next(components, j);
                j = next_j;
                args.push(arg);
            }
            if j != i + size {
                panic!("Composite term has wrong size");
            }
            (j, Term::new(term_type, head_type, head, args))
        }
        TermComponent::Atom(term_type, atom) => (i + 1, Term::atom(term_type, atom)),
    }
}

fn unflatten_term(components: &[TermComponent]) -> Term {
    let (size, term) = unflatten_next(components, 0);
    if size != components.len() {
        panic!("Term has wrong size");
    }
    term
}

// A rewrite tree is a "perfect discrimination tree" specifically designed to rewrite
// terms into simplified versions.
// Each path from the root to a leaf is a series of edges that represents a term.
// The linear representation of a term is a preorder traversal of the tree.
// For any non-atomic term, we include the type of its head, then recurse.
// For any atom, we just include the atom.
// This doesn't contain enough type information to extract a term from the tree, but it
// does contain enough type information to match against an existing term, as long as having
// an atomic variable at the root level is forbidden.

// Used for converting Edges into byte sequences.
const HEAD_TYPE: u8 = 0;
const TRUE: u8 = 1;
const CONSTANT: u8 = 2;
const MONOMORPH: u8 = 3;
const SYNTHETIC: u8 = 4;
const VARIABLE: u8 = 5;

enum Edge {
    HeadType(TypeId),
    Atom(Atom),
}

impl Edge {
    fn discriminant_byte(&self) -> u8 {
        match self {
            Edge::HeadType(_) => HEAD_TYPE,
            Edge::Atom(a) => match a {
                Atom::True => TRUE,
                Atom::Constant(_) => CONSTANT,
                Atom::Monomorph(_) => MONOMORPH,
                Atom::Synthetic(_) => SYNTHETIC,
                Atom::Variable(_) => VARIABLE,
            },
        }
    }

    fn append_to(&self, v: &mut Vec<u8>) {
        v.push(self.discriminant_byte());
        let id: u16 = match self {
            Edge::HeadType(t) => *t,
            Edge::Atom(a) => match a {
                Atom::True => 0,
                Atom::Constant(c) => *c,
                Atom::Monomorph(m) => *m,
                Atom::Synthetic(s) => *s,
                Atom::Variable(i) => *i,
            },
        };
        v.extend_from_slice(&id.to_ne_bytes());
    }
}

// Appends the path to the term, but does not add the top-level type
fn path_from_term_helper(term: &Term, path: &mut Vec<u8>) {
    if term.args.is_empty() {
        Edge::Atom(term.head).append_to(path);
    } else {
        Edge::HeadType(term.head_type).append_to(path);
        Edge::Atom(term.head).append_to(path);
        for arg in &term.args {
            path_from_term_helper(arg, path);
        }
    }
}

// Appends the path to the term, prefixing with the top-level type
fn path_from_term(term: &Term) -> Vec<u8> {
    let mut path = Vec::new();
    path_from_term_helper(term, &mut path);
    path
}

// Replace the variable x_i with the contents of replacements[i].
// Appends the result to output.
// We only update the size indices for components we add to the output, not
// components that are already in the output.
fn replace_components(
    components: &[TermComponent],
    replacements: &[&[TermComponent]],
) -> Vec<TermComponent> {
    let mut output: Vec<TermComponent> = vec![];
    println!(
        "XXX replace_components: {:?} with {:?}",
        components, replacements
    );

    // path contains all the indices of composite parents, in *output*, of the current node
    let mut path: Vec<usize> = vec![];

    for component in components {
        // Pop any elements of the path that are no longer parents
        while path.len() > 0 {
            let j = path[path.len() - 1];
            if j + output[j].size() <= output.len() {
                path.pop();
            } else {
                break;
            }
        }

        match component {
            TermComponent::Composite(_, _) => {
                path.push(output.len());
                output.push(component.clone());
            }
            TermComponent::Atom(_, a) => {
                if let Atom::Variable(i) = a {
                    let replacement = replacements[*i as usize];

                    // Every parent of this node, its size is getting bigger by delta
                    let delta = (replacement.len() - 1) as u16;
                    for j in &path {
                        output[*j].increase_size(delta);
                    }
                    output.extend_from_slice(replacement);
                } else {
                    output.push(component.clone());
                }
            }
        }
    }
    output
}

// Information stored in each trie leaf.
#[derive(Debug, Clone, Copy)]
struct Leaf {
    // The rewrite tree just sees an opaque id for each rewrite rule.
    // When we do a rewrite, we want to know which rule was used.
    rule_id: usize,

    // An id for the rewritten form of the term.
    rewritten_id: usize,
}

// Finds a leaf in the trie that matches the given term components.
// These term components could represent a single term, or they could represent a
// sequence of terms that are a suffix of a subterm. The "right part" of a subterm cut by a path.
// Kind of confusing, just be aware that it does not correspond to a single term.
//
// Returns None if there is no matching leaf.
// A "match" can replace any variable i in the trie with replacements[i].
// If this does not find a match, it returns key and replacements to their initial state.
fn find_leaf<'a>(
    subtrie: &SubTrie<Vec<u8>, Leaf>,
    key: &mut Vec<u8>,
    components: &'a [TermComponent],
    replacements: &mut Vec<&'a [TermComponent]>,
) -> Option<Leaf> {
    println!("XXX find_leaf: {:?}", key);
    if subtrie.is_empty() {
        return None;
    }

    if components.is_empty() {
        match subtrie.get(key as &[u8]) {
            Some(leaf) => return Some(*leaf),
            None => {
                panic!("type mismatch. components are exhausted but subtrie is not");
            }
        }
    }
    let initial_key_len = key.len();

    // Case 1: the first term in the components could match an existing replacement
    println!("XXX components: {:?}", components);
    let size = components[0].size();
    println!("XXX size = {}", size);
    let first = &components[..size];
    let rest = &components[size..];
    for i in 0..replacements.len() {
        if first == replacements[i] {
            // This term could match x_i as a backreference.
            Edge::Atom(Atom::Variable(i as u16)).append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);
            if let Some(leaf) = find_leaf(&new_subtrie, key, rest, replacements) {
                return Some(leaf);
            }
            key.truncate(initial_key_len);
        }
    }

    // Case 2: the first term could match an entirely new variable
    Edge::Atom(Atom::Variable(replacements.len() as u16)).append_to(key);
    let new_subtrie = subtrie.subtrie(key as &[u8]);
    if !new_subtrie.is_empty() {
        replacements.push(first);
        if let Some(leaf) = find_leaf(&new_subtrie, key, rest, replacements) {
            return Some(leaf);
        }
        replacements.pop();
    }
    key.truncate(initial_key_len);

    // Case 3: we could exactly match just the first component
    let bytes = match components[0] {
        TermComponent::Composite(_, _) => {
            if let TermComponent::Atom(head_type, _) = components[1] {
                Edge::HeadType(head_type)
            } else {
                panic!("Composite term must have an atom as its head");
            }
        }
        TermComponent::Atom(_, a) => Edge::Atom(a),
    };
    bytes.append_to(key);
    let new_subtrie = subtrie.subtrie(key as &[u8]);
    if let Some(leaf) = find_leaf(&new_subtrie, key, &components[1..], replacements) {
        return Some(leaf);
    }
    key.truncate(initial_key_len);
    None
}

pub struct RewriteTree {
    trie: Trie<Vec<u8>, Leaf>,

    // Indexed by rewritten_id.
    rewritten: Vec<Vec<TermComponent>>,
}

const EMPTY_SLICE: &[u8] = &[];

impl RewriteTree {
    pub fn new() -> RewriteTree {
        RewriteTree {
            trie: Trie::new(),
            rewritten: vec![],
        }
    }

    pub fn add_rule(&mut self, rule_id: usize, input_term: &Term, output_term: &Term) {
        if input_term.atomic_variable().is_some() {
            panic!("cannot rewrite atomic variables to something else");
        }
        let path = path_from_term(input_term);
        println!("XXX inserting path: {:?}", path);
        let rewritten_id = self.rewritten.len();
        self.rewritten.push(flatten_term(output_term));
        let leaf = Leaf {
            rule_id,
            rewritten_id,
        };
        self.trie.insert(path, leaf);
    }

    // Does one rewrite.
    // Checks all subterms.
    // Returns the rewrite rule used, and the new sequence of components, if there is a rewrite.
    fn rewrite_once(&self, components: &Vec<TermComponent>) -> Option<(usize, Vec<TermComponent>)> {
        for i in 0..components.len() {
            let subterm_size = components[i].size();
            let subterm = &components[i..i + subterm_size];
            let subtrie = self.trie.subtrie(EMPTY_SLICE);
            let mut replacements = vec![];
            let mut key = vec![];

            if let Some(leaf) = find_leaf(&subtrie, &mut key, subterm, &mut replacements) {
                let new_subterm = replace_components(subterm, &replacements);
                if i == 0 {
                    // We just replaced the whole term
                    return Some((leaf.rule_id, new_subterm));
                }

                todo!("handle proper subterms");
            }
        }
        None
    }

    // Rewrites repeatedly.
    // Returns a list of the rewrite rules used, and the final term.
    pub fn rewrite(&self, term: &Term) -> Option<(Vec<usize>, Term)> {
        let mut components = flatten_term(term);
        let mut rules = vec![];

        // Infinite loops are hard to debug, so cap this loop.
        for _ in 0..100 {
            let subtrie = self.trie.subtrie(EMPTY_SLICE);
            let mut replacements = vec![];
            let mut key = vec![];

            let leaf = match find_leaf(&subtrie, &mut key, &components, &mut replacements) {
                Some(leaf) => leaf,
                None => {
                    if rules.is_empty() {
                        return None;
                    } else {
                        return Some((rules, unflatten_term(&components)));
                    }
                }
            };

            rules.push(leaf.rule_id);
            components = replace_components(&self.rewritten[leaf.rewritten_id], &replacements);
            println!("XXX new components: {:?}", components);
        }

        panic!("rewrite looped too many times");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rewriting_an_atom() {
        let mut tree = RewriteTree::new();
        tree.add_rule(0, &Term::parse("c1"), &Term::parse("c0"));
        let (rules, term) = tree.rewrite(&Term::parse("c1")).unwrap();
        assert_eq!(rules, vec![0]);
        assert_eq!(term, Term::parse("c0"));
    }

    #[test]
    fn test_rewriting_a_function() {
        let mut tree = RewriteTree::new();
        tree.add_rule(0, &Term::parse("c1(x0)"), &Term::parse("c0(x0)"));
        let (rules, term) = tree.rewrite(&Term::parse("c1(c2)")).unwrap();
        assert_eq!(rules, vec![0]);
        assert_eq!(term, Term::parse("c0(c2)"));
    }

    #[test]
    fn test_multiple_rewrites() {
        let mut tree = RewriteTree::new();
        tree.add_rule(0, &Term::parse("c1(x0)"), &Term::parse("c0(x0)"));
        tree.add_rule(1, &Term::parse("c0(c2)"), &Term::parse("c3"));
        let (rules, term) = tree.rewrite(&Term::parse("c1(c2)")).unwrap();
        assert_eq!(rules, vec![0, 1]);
        assert_eq!(term, Term::parse("c3"));
    }
}
