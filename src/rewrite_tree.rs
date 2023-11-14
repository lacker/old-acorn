use std::borrow::Borrow;

use qp_trie::{SubTrie, Trie};

use crate::atom::Atom;
use crate::term::Term;
use crate::type_map::TypeId;

// The TermComponent is designed so that a &[TermComponent] represents a preorder
// traversal of the term, and subslices represent subterms.
#[derive(Debug, PartialEq, Eq)]
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
    output[initial_size] =
        TermComponent::Composite(term.term_type, (output.len() - initial_size) as u16);
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

// The possible discriminants.
// HEAD_TYPE indicates the following id encodes a type, The rest encode atoms.
const HEAD_TYPE: u8 = 0;
const TRUE: u8 = 1;
const CONSTANT: u8 = 2;
const MONOMORPH: u8 = 3;
const SYNTHETIC: u8 = 4;
const VARIABLE: u8 = 5;

const EMPTY: &[u8] = &[];

#[repr(C, packed)]
struct EdgeBytes {
    // Which type of edge it is
    discriminant: u8,

    // Either a type id or an atom id depending on the discriminant
    id: u16,
}

impl Borrow<[u8]> for EdgeBytes {
    fn borrow(&self) -> &[u8] {
        unsafe {
            // SAFETY: `Edge` is `repr(C, packed)` and consists of a `u8` and a `u16`.
            // It has the same memory layout as `[u8; 3]`. The endianness of the `u16` means
            // the representation is different on different platforms. But, that should be okay.
            std::slice::from_raw_parts(self as *const EdgeBytes as *const u8, 3)
        }
    }
}

impl EdgeBytes {
    fn from_head_type(t: TypeId) -> EdgeBytes {
        EdgeBytes {
            discriminant: HEAD_TYPE,
            id: t,
        }
    }

    fn from_variable(i: u16) -> EdgeBytes {
        EdgeBytes {
            discriminant: VARIABLE,
            id: i,
        }
    }

    fn from_atom(a: Atom) -> EdgeBytes {
        match a {
            Atom::True => EdgeBytes {
                discriminant: TRUE,
                id: 0,
            },
            Atom::Constant(i) => EdgeBytes {
                discriminant: CONSTANT,
                id: i,
            },
            Atom::Monomorph(i) => EdgeBytes {
                discriminant: MONOMORPH,
                id: i,
            },
            Atom::Synthetic(i) => EdgeBytes {
                discriminant: SYNTHETIC,
                id: i,
            },
            Atom::Variable(i) => EdgeBytes::from_variable(i),
        }
    }

    fn append_to(&self, v: &mut Vec<u8>) {
        v.push(self.discriminant);
        // Native-endian for consistency with the borrowing
        v.extend_from_slice(&self.id.to_ne_bytes());
    }
}

// Appends the path to the term, but does not add the top-level type
fn path_from_term_helper(term: &Term, path: &mut Vec<u8>) {
    if term.args.is_empty() {
        EdgeBytes::from_atom(term.head).append_to(path);
    } else {
        EdgeBytes::from_head_type(term.head_type).append_to(path);
        EdgeBytes::from_atom(term.head).append_to(path);
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
// The "size" indices have to be updated as well.
fn replace_components(
    components: &[TermComponent],
    replacements: &[&[TermComponent]],
) -> Vec<TermComponent> {
    todo!();
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
// If this does not find a match, it returns replacements to their initial state.
fn find_leaf<'a>(
    trie: &SubTrie<Vec<u8>, Leaf>,
    components: &'a [TermComponent],
    replacements: &mut Vec<&'a [TermComponent]>,
) -> Option<Leaf> {
    if trie.is_empty() {
        return None;
    }

    if components.is_empty() {
        match trie.get(EMPTY) {
            Some(leaf) => return Some(*leaf),
            None => {
                panic!("type mismatch. components are exhausted but subtrie is not");
            }
        }
    }

    // Case 1: the first term in the components could match an existing replacement
    let size = components[0].size();
    let first = &components[..size];
    let rest = &components[size..];
    for i in 0..replacements.len() {
        if first == replacements[i] {
            // This term could match x_i as a backreference.
            let bytes = EdgeBytes::from_variable(i as u16);
            let subtrie = trie.subtrie(bytes);
            if let Some(leaf) = find_leaf(&subtrie, rest, replacements) {
                return Some(leaf);
            }
        }
    }

    // Case 2: the first term could match an entirely new variable
    let bytes = EdgeBytes::from_variable(replacements.len() as u16);
    let subtrie = trie.subtrie(bytes);
    if !subtrie.is_empty() {
        replacements.push(first);
        if let Some(leaf) = find_leaf(&subtrie, rest, replacements) {
            return Some(leaf);
        }
        replacements.pop();
    }

    // Case 3: we could exactly match just the first component
    let bytes = match components[0] {
        TermComponent::Composite(_, _) => {
            if let TermComponent::Atom(head_type, _) = components[1] {
                EdgeBytes::from_head_type(head_type)
            } else {
                panic!("Composite term must have an atom as its head");
            }
        }
        TermComponent::Atom(_, a) => EdgeBytes::from_atom(a),
    };
    let subtrie = trie.subtrie(bytes);
    find_leaf(&subtrie, &components[1..], replacements)
}

pub struct RewriteTree {
    trie: Trie<Vec<u8>, Leaf>,

    // Indexed by rewritten_id.
    rewritten: Vec<Vec<TermComponent>>,
}

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
        let rewritten_id = self.rewritten.len();
        self.rewritten.push(flatten_term(output_term));
        let leaf = Leaf {
            rule_id,
            rewritten_id,
        };
        self.trie.insert(path, leaf);
    }

    // Rewrites repeatedly.
    // Returns a list of the rewrite rules used, and the final term.
    pub fn rewrite(&self, term: &Term) -> Option<(Vec<usize>, Term)> {
        let mut components = flatten_term(term);
        let mut rules = vec![];

        // Infinite loops are hard to debug. Large numbers are close to infinity so they probably also
        // indicate a bug.
        for _ in 0..100 {
            let subtrie = self.trie.subtrie(EMPTY);
            let mut replacements = vec![];
            let leaf = match find_leaf(&subtrie, &components, &mut replacements) {
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
        }

        panic!("rewrite looped too many times");
    }
}
