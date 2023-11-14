use std::borrow::Borrow;

use qp_trie::{SubTrie, Trie};

use crate::atom::Atom;
use crate::term::Term;
use crate::type_map::TypeId;

// The TermComponent is designed so that a &[TermComponent] represents a preorder
// traversal of the term, and subslices represent subterms.
#[derive(Debug)]
enum TermComponent {
    // The u16 is the number of term components in the term, including this one.
    // Must be at least 3. Otherwise this would just be an atom.
    Composite(TypeId, u16),

    Atom(TypeId, Atom),
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
// The linear representation of a term is:
// First, the type of the term itself
// Then, a preorder traversal of the tree.
// For any non-atomic term, we include the type of its head, then recurse.
// For any atom, we just include the atom.
// This doesn't contain enough type information to extract a term from the tree, but it
// does contain enough type information to match against an existing term.

// The possible discriminants.
// "type" encodes a type, the rest encode atoms.
const TYPE: u8 = 0;
const TRUE: u8 = 1;
const CONSTANT: u8 = 2;
const MONOMORPH: u8 = 3;
const SYNTHETIC: u8 = 4;
const VARIABLE: u8 = 5;

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
    fn from_type(t: TypeId) -> EdgeBytes {
        EdgeBytes {
            discriminant: TYPE,
            id: t,
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
            Atom::Variable(i) => EdgeBytes {
                discriminant: VARIABLE,
                id: i,
            },
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
        EdgeBytes::from_type(term.head_type).append_to(path);
        EdgeBytes::from_atom(term.head).append_to(path);
        for arg in &term.args {
            path_from_term_helper(arg, path);
        }
    }
}

// Appends the path to the term, prefixing with the top-level type
fn path_from_term(term: &Term) -> Vec<u8> {
    let mut path = Vec::new();
    EdgeBytes::from_type(term.get_term_type()).append_to(&mut path);
    path_from_term_helper(term, &mut path);
    path
}

// Information stored in each trie leaf.
struct Leaf {
    // The rewrite tree just sees an opaque id for each rewrite rule.
    // When we do a rewrite, we want to know which rule was used.
    rule_id: usize,

    // The rewritten form of the term
    rewritten: Vec<TermComponent>,
}

pub struct RewriteTree {
    trie: Trie<Vec<u8>, Leaf>,
}

impl RewriteTree {
    pub fn new() -> RewriteTree {
        RewriteTree { trie: Trie::new() }
    }

    pub fn add_rule(&mut self, rule_id: usize, term: &Term) {
        let path = path_from_term(term);
        let leaf = Leaf {
            rule_id,
            rewritten: flatten_term(term),
        };
        self.trie.insert(path, leaf);
    }
}
