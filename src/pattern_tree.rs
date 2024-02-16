use qp_trie::{Entry, SubTrie, Trie};

use crate::atom::Atom;
use crate::literal::Literal;
use crate::term::Term;
use crate::type_map::TypeId;

// The TermComponent is designed so that a &[TermComponent] represents a preorder
// traversal of the term, and each subterm is represented by a subslice.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TermComponent {
    // The u8 is the number of args in the term.
    // The u16 is the number of term components in the term, including this one.
    // Must be at least 3. Otherwise this would just be an atom.
    Composite(TypeId, u8, u16),

    Atom(TypeId, Atom),

    // This can only be the first element of a &[TermComponent].
    // It indicates that this slice represents a pair of terms rather than a single term.
    // The u16 is the number of term components in the pair, including this one.
    Pair(TypeId, u16),
}

impl TermComponent {
    // The number of TermComponents in the component starting with this one
    pub fn size(&self) -> usize {
        match self {
            TermComponent::Composite(_, _, size) | TermComponent::Pair(_, size) => *size as usize,
            TermComponent::Atom(_, _) => 1,
        }
    }

    pub fn alter_size(&self, delta: i32) -> TermComponent {
        match self {
            TermComponent::Composite(term_type, num_args, size) => {
                TermComponent::Composite(*term_type, *num_args, (*size as i32 + delta) as u16)
            }
            TermComponent::Atom(_, _) => panic!("cannot increase size of atom"),
            TermComponent::Pair(..) => panic!("cannot increase size of pair"),
        }
    }

    fn flatten_next(term: &Term, output: &mut Vec<TermComponent>) {
        if term.args.is_empty() {
            output.push(TermComponent::Atom(term.term_type, term.head));
            return;
        }

        let initial_size = output.len();

        // The zeros are a placeholder. We'll fill in the real info later.
        output.push(TermComponent::Composite(0, 0, 0));
        output.push(TermComponent::Atom(term.head_type, term.head));
        for arg in &term.args {
            TermComponent::flatten_next(arg, output);
        }

        // Now we can fill in the real size
        let real_size = output.len() - initial_size;
        output[initial_size] =
            TermComponent::Composite(term.term_type, term.args.len() as u8, real_size as u16);
    }

    pub fn flatten_term(term: &Term) -> Vec<TermComponent> {
        let mut output = Vec::new();
        TermComponent::flatten_next(term, &mut output);
        output
    }

    fn flatten_pair(term1: &Term, term2: &Term) -> Vec<TermComponent> {
        assert_eq!(term1.term_type, term2.term_type);
        let mut output = Vec::new();
        // The zero is a placeholder. We'll fill in the real info later.
        output.push(TermComponent::Pair(0, 0));
        TermComponent::flatten_next(term1, &mut output);
        TermComponent::flatten_next(term2, &mut output);
        output[0] = TermComponent::Pair(term1.term_type, output.len() as u16);
        output
    }

    // Constructs a term, starting at components[i].
    // Returns the next unused index and the term.
    fn unflatten_next(components: &[TermComponent], i: usize) -> (usize, Term) {
        match components[i] {
            TermComponent::Composite(term_type, num_args, size) => {
                let size = size as usize;
                let (head_type, head) = match components[i + 1] {
                    TermComponent::Atom(head_type, head) => (head_type, head),
                    _ => panic!("Composite term must have an atom as its head"),
                };

                let mut args = Vec::new();
                let mut j = i + 2;
                while j < i + size {
                    let (next_j, arg) = TermComponent::unflatten_next(components, j);
                    j = next_j;
                    args.push(arg);
                }
                if j != i + size {
                    panic!("Composite term has wrong size");
                }
                if args.len() != num_args as usize {
                    panic!("Composite term has wrong number of args");
                }
                (j, Term::new(term_type, head_type, head, args))
            }
            TermComponent::Atom(term_type, atom) => (i + 1, Term::atom(term_type, atom)),
            TermComponent::Pair(..) => panic!("unflatten_next called with a pair"),
        }
    }

    pub fn unflatten_term(components: &[TermComponent]) -> Term {
        let (size, term) = TermComponent::unflatten_next(components, 0);
        if size != components.len() {
            panic!("Term has wrong size");
        }
        term
    }

    pub fn unflatten_pair(components: &[TermComponent]) -> (Term, Term) {
        match components[0] {
            TermComponent::Pair(..) => {
                let (j, term1) = TermComponent::unflatten_next(components, 1);
                let (k, term2) = TermComponent::unflatten_next(components, j);
                if k != components.len() {
                    panic!("Pair has wrong size");
                }
                (term1, term2)
            }
            _ => panic!("unflatten_pair called with a non-pair"),
        }
    }

    // Validates the subterm starting at the given position.
    // Returns the position the next subterm should start at.
    fn validate_one(components: &[TermComponent], position: usize) -> Result<usize, String> {
        if position > components.len() {
            return Err(format!("ran off the end, position {}", position));
        }
        match components[position] {
            TermComponent::Composite(_, num_args, size) => {
                if size < 3 {
                    return Err(format!("composite terms must have size at least 3"));
                }
                if position + 1 >= components.len() {
                    return Err(format!(
                        "composite terms must have a head, but we ran off the end"
                    ));
                }
                if let TermComponent::Composite(..) = components[position + 1] {
                    return Err(format!("composite terms must have an atom as their head"));
                }
                // The position we expect to end up in after parsing
                let final_pos = position + size as usize;
                let mut next_pos = position + 2;
                let mut args_seen = 0;
                while next_pos < final_pos {
                    next_pos = TermComponent::validate_one(components, next_pos)?;
                    args_seen += 1;
                }
                if next_pos != final_pos {
                    return Err(format!(
                        "expected composite term at {} to end by {} but it went until {}",
                        position, final_pos, next_pos
                    ));
                }
                if args_seen != num_args as usize {
                    return Err(format!(
                        "expected composite term at {} to have {} args but it had {}",
                        position, num_args, args_seen
                    ));
                }
                Ok(final_pos)
            }
            TermComponent::Atom(_, _) => return Ok(position + 1),
            TermComponent::Pair(_, size) => {
                if size < 3 {
                    return Err(format!("pairs must have size at least 3"));
                }
                let final_pos = position + size as usize;
                let mut next_pos = position + 1;
                let mut args_seen = 0;
                while next_pos < final_pos {
                    next_pos = TermComponent::validate_one(components, next_pos)?;
                    args_seen += 1;
                }
                if next_pos != final_pos {
                    return Err(format!(
                        "expected pair at {} to end by {} but it went until {}",
                        position, final_pos, next_pos
                    ));
                }
                if args_seen != 2 {
                    return Err(format!(
                        "expected pair at {} to be made up of two terms but it had {}",
                        position, args_seen
                    ));
                }
                Ok(final_pos)
            }
        }
    }

    pub fn validate_slice(components: &[TermComponent]) {
        match TermComponent::validate_one(components, 0) {
            Ok(final_pos) => {
                if final_pos != components.len() {
                    panic!(
                        "validation fail in {:?}. we have {} components but parsing used {}",
                        components,
                        components.len(),
                        final_pos
                    );
                }
            }
            Err(e) => panic!("validation fail in {:?}. error: {}", components, e),
        }
    }

    // Replace the variable x_i with the contents of replacements[i].
    // Appends the result to output.
    // We only update the size indices for components we add to the output, not
    // components that are already in the output.
    pub fn replace(
        components: &[TermComponent],
        replacements: &[&[TermComponent]],
    ) -> Vec<TermComponent> {
        let mut output: Vec<TermComponent> = vec![];

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
                TermComponent::Composite(..) => {
                    path.push(output.len());
                    output.push(component.clone());
                }
                TermComponent::Atom(_, a) => {
                    if let Atom::Variable(i) = a {
                        let mut replacement = replacements[*i as usize];

                        // If the replacement is a composite, and this is the head of a term,
                        // we need to flatten the two terms together.
                        if replacement.len() > 1 && output.len() > 0 {
                            let last_index = output.len() - 1;
                            if let TermComponent::Composite(t, num_args, size) = output[last_index]
                            {
                                match replacement[0] {
                                    TermComponent::Composite(_, replacement_num_args, _) => {
                                        // This composite now has more args, both old and new ones.
                                        let new_num_args = num_args + replacement_num_args;
                                        output[last_index] =
                                            TermComponent::Composite(t, new_num_args, size);

                                        // We don't need the replacement head any more.
                                        replacement = &replacement[1..];
                                    }
                                    _ => panic!("replacement has length > 1 but is not composite"),
                                }
                            }
                        }

                        // Every parent of this node, its size is changing by delta
                        let delta = (replacement.len() - 1) as i32;
                        for j in &path {
                            output[*j] = output[*j].alter_size(delta);
                        }
                        output.extend_from_slice(replacement);
                    } else {
                        output.push(component.clone());
                    }
                }
                TermComponent::Pair(..) => {
                    panic!("replacing in pairs is not implemented");
                }
            }
        }
        output
    }
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
// Any byte below MAX_ARGS indicates a composite term with that number of arguments.
const MAX_ARGS: u8 = 100;
const TRUE: u8 = 101;
const GLOBAL_CONSTANT: u8 = 102;
const LOCAL_CONSTANT: u8 = 103;
const MONOMORPH: u8 = 104;
const VARIABLE: u8 = 105;
const LITERAL: u8 = 106;

#[derive(Debug)]
enum Edge {
    // Number of args, and the type.
    HeadType(u8, TypeId),

    Atom(Atom),

    Literal(TypeId),
}

impl Edge {
    fn first_byte(&self) -> u8 {
        match self {
            Edge::HeadType(num_args, _) => *num_args,
            Edge::Atom(a) => match a {
                Atom::True => TRUE,
                Atom::GlobalConstant(_) => GLOBAL_CONSTANT,
                Atom::LocalConstant(_) => LOCAL_CONSTANT,
                Atom::Monomorph(_) => MONOMORPH,
                Atom::Variable(_) => VARIABLE,
            },
            Edge::Literal(..) => LITERAL,
        }
    }

    fn append_to(&self, v: &mut Vec<u8>) {
        v.push(self.first_byte());
        let id: u16 = match self {
            Edge::HeadType(_, t) => *t,
            Edge::Atom(a) => match a {
                Atom::True => 0,
                Atom::GlobalConstant(c) => *c,
                Atom::LocalConstant(c) => *c,
                Atom::Monomorph(m) => *m,
                Atom::Variable(i) => *i,
            },
            Edge::Literal(t) => *t,
        };
        v.extend_from_slice(&id.to_ne_bytes());
    }

    fn from_bytes(byte1: u8, byte2: u8, byte3: u8) -> Edge {
        let id = u16::from_ne_bytes([byte2, byte3]);
        match byte1 {
            TRUE => Edge::Atom(Atom::True),
            GLOBAL_CONSTANT => Edge::Atom(Atom::GlobalConstant(id)),
            LOCAL_CONSTANT => Edge::Atom(Atom::LocalConstant(id)),
            MONOMORPH => Edge::Atom(Atom::Monomorph(id)),
            VARIABLE => Edge::Atom(Atom::Variable(id)),
            LITERAL => Edge::Literal(id),
            num_args => {
                if num_args > MAX_ARGS {
                    panic!("invalid discriminant byte");
                }
                Edge::HeadType(num_args, id)
            }
        }
    }

    fn debug_bytes(bytes: &[u8]) -> String {
        let mut i = 0;
        let mut parts: Vec<String> = vec![];
        while i < bytes.len() {
            if i + 3 <= bytes.len() {
                let edge = Edge::from_bytes(bytes[i], bytes[i + 1], bytes[i + 2]);
                parts.push(format!("{:?}", edge));
            } else {
                parts.push(format!("plus extra bytes {:?}", &bytes[i..]));
            }
            i += 3;
        }

        parts.join(", ")
    }
}

// Appends the path to the term, but does not add the top-level type
fn path_from_term_helper(term: &Term, path: &mut Vec<u8>) {
    if term.args.is_empty() {
        Edge::Atom(term.head).append_to(path);
    } else {
        Edge::HeadType(term.args.len() as u8, term.head_type).append_to(path);
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

fn path_from_pair(term1: &Term, term2: &Term) -> Vec<u8> {
    let mut path = Vec::new();
    Edge::Literal(term1.term_type).append_to(&mut path);
    path_from_term_helper(&term1, &mut path);
    path_from_term_helper(&term2, &mut path);
    path
}

// Finds leaves in the trie that match the given term components.
// These term components could represent a single term, or they could represent a
// sequence of terms that are a suffix of a subterm. The "right part" of a subterm cut by a path.
// Kind of confusing, just be aware that it does not correspond to a single term.
//
// For each match, it calls the callback with the value id matched, and the replacements used.
// If the callback returns false, the search is stopped early.
// The function returns whether the search fully completed (without stopping early).
//
// If the search does fully complete, we reset key and replacements to their initial state.
fn find_matches_while<'a, F>(
    subtrie: &SubTrie<Vec<u8>, usize>,
    key: &mut Vec<u8>,
    components: &'a [TermComponent],
    replacements: &mut Vec<&'a [TermComponent]>,
    callback: &mut F,
) -> bool
where
    F: FnMut(usize, &Vec<&[TermComponent]>) -> bool,
{
    if subtrie.is_empty() {
        return true;
    }

    if components.is_empty() {
        match subtrie.get(key as &[u8]) {
            Some(value_id) => {
                return callback(*value_id, replacements);
            }
            None => {
                // The entire term is matched, but we are not yet at the leaf.
                // The key format is supposed to ensure that two different valid
                // keys don't have a prefix relationship.
                // This indicates some sort of problem, like that some atom
                // is being used with an inconsistent number of args.
                let (sample, _) = subtrie.iter().next().unwrap();
                panic!(
                    "\nkey mismatch.\nquerying: {}\nexisting: {}\n",
                    Edge::debug_bytes(key),
                    Edge::debug_bytes(sample)
                );
            }
        }
    }
    let initial_key_len = key.len();

    // Case 1: this is a pair, which must match a pair using the same types.
    if let TermComponent::Pair(term_type, _) = components[0] {
        let edge = Edge::Literal(term_type);
        edge.append_to(key);
        let new_subtrie = subtrie.subtrie(key as &[u8]);
        if !find_matches_while(&new_subtrie, key, &components[1..], replacements, callback) {
            return false;
        }
        key.truncate(initial_key_len);
        return true;
    }

    // Case 2: the first term in the components could match an existing replacement
    let size = components[0].size();
    let first = &components[..size];
    let rest = &components[size..];
    for i in 0..replacements.len() {
        if first == replacements[i] {
            // This term could match x_i as a backreference.
            Edge::Atom(Atom::Variable(i as u16)).append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);
            if !find_matches_while(&new_subtrie, key, rest, replacements, callback) {
                return false;
            }
            key.truncate(initial_key_len);
        }
    }

    // Case 3: the first term could match an entirely new variable
    Edge::Atom(Atom::Variable(replacements.len() as u16)).append_to(key);
    let new_subtrie = subtrie.subtrie(key as &[u8]);
    if !new_subtrie.is_empty() {
        replacements.push(first);
        if !find_matches_while(&new_subtrie, key, rest, replacements, callback) {
            return false;
        }
        replacements.pop();
    }
    key.truncate(initial_key_len);

    // Case 4: we could exactly match just the first component
    let edge = match components[0] {
        TermComponent::Composite(_, num_args, _) => {
            if let TermComponent::Atom(head_type, _) = components[1] {
                Edge::HeadType(num_args, head_type)
            } else {
                panic!("Composite term must have an atom as its head");
            }
        }
        TermComponent::Atom(_, a) => {
            if a.is_variable() {
                // Variables in the term have to match a replacement, they can't exact-match.
                return true;
            }
            Edge::Atom(a)
        }
        TermComponent::Pair(..) => panic!("pairs should have been handled already"),
    };
    edge.append_to(key);
    let new_subtrie = subtrie.subtrie(key as &[u8]);
    if !find_matches_while(&new_subtrie, key, &components[1..], replacements, callback) {
        return false;
    }
    key.truncate(initial_key_len);
    true
}

// Finds a leaf in the trie that matches the given term components.
// These term components could represent a single term, or they could represent a
// sequence of terms that are a suffix of a subterm. The "right part" of a subterm cut by a path.
// Kind of confusing, just be aware that it does not correspond to a single term.
//
// Returns None if there is no matching leaf.
// A "match" can replace any variable i in the trie with replacements[i].
// If this does not find a match, it returns key and replacements to their initial state.
fn find_one_match<'a>(
    subtrie: &SubTrie<Vec<u8>, usize>,
    key: &mut Vec<u8>,
    components: &'a [TermComponent],
    replacements: &mut Vec<&'a [TermComponent]>,
) -> Option<usize> {
    if subtrie.is_empty() {
        return None;
    }

    if components.is_empty() {
        match subtrie.get(key as &[u8]) {
            Some(leaf) => return Some(leaf.clone()),
            None => {
                // The entire term is matched, but we are not yet at the leaf.
                // The key format is supposed to ensure that two different valid
                // keys don't have a prefix relationship.
                // This indicates some sort of problem, like that some atom
                // is being used with an inconsistent number of args.
                let (sample, _) = subtrie.iter().next().unwrap();
                panic!(
                    "\nkey mismatch.\nquerying: {}\nexisting: {}\n",
                    Edge::debug_bytes(key),
                    Edge::debug_bytes(sample)
                );
            }
        }
    }
    let initial_key_len = key.len();

    // Case 1: this is a pair, which must match a pair using the same types.
    if let TermComponent::Pair(term_type, _) = components[0] {
        let edge = Edge::Literal(term_type);
        edge.append_to(key);
        let new_subtrie = subtrie.subtrie(key as &[u8]);
        if let Some(leaf) = find_one_match(&new_subtrie, key, &components[1..], replacements) {
            return Some(leaf);
        }
        key.truncate(initial_key_len);
        return None;
    }

    // Case 2: the first term in the components could match an existing replacement
    let size = components[0].size();
    let first = &components[..size];
    let rest = &components[size..];
    for i in 0..replacements.len() {
        if first == replacements[i] {
            // This term could match x_i as a backreference.
            Edge::Atom(Atom::Variable(i as u16)).append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);
            if let Some(leaf) = find_one_match(&new_subtrie, key, rest, replacements) {
                return Some(leaf);
            }
            key.truncate(initial_key_len);
        }
    }

    // Case 3: the first term could match an entirely new variable
    Edge::Atom(Atom::Variable(replacements.len() as u16)).append_to(key);
    let new_subtrie = subtrie.subtrie(key as &[u8]);
    if !new_subtrie.is_empty() {
        replacements.push(first);
        if let Some(leaf) = find_one_match(&new_subtrie, key, rest, replacements) {
            return Some(leaf);
        }
        replacements.pop();
    }
    key.truncate(initial_key_len);

    // Case 4: we could exactly match just the first component
    let edge = match components[0] {
        TermComponent::Composite(_, num_args, _) => {
            if let TermComponent::Atom(head_type, _) = components[1] {
                Edge::HeadType(num_args, head_type)
            } else {
                panic!("Composite term must have an atom as its head");
            }
        }
        TermComponent::Atom(_, a) => {
            if a.is_variable() {
                // Variables in the term have to match a replacement, they can't exact-match.
                return None;
            }
            Edge::Atom(a)
        }
        TermComponent::Pair(..) => panic!("pairs should have been handled already"),
    };
    edge.append_to(key);
    let new_subtrie = subtrie.subtrie(key as &[u8]);
    if let Some(leaf) = find_one_match(&new_subtrie, key, &components[1..], replacements) {
        return Some(leaf);
    }
    key.truncate(initial_key_len);
    None
}

pub struct PatternTree<T> {
    // Maps to an index into values.
    // The values are stored separately because subtrie lifetimes get weird.
    trie: Trie<Vec<u8>, usize>,

    values: Vec<T>,
}

const EMPTY_SLICE: &[u8] = &[];

impl<T> PatternTree<T> {
    pub fn new() -> PatternTree<T> {
        PatternTree {
            trie: Trie::new(),
            values: vec![],
        }
    }

    pub fn insert_term(&mut self, key: &Term, value: T) {
        let path = path_from_term(key);
        let value_id = self.values.len();
        self.values.push(value);
        self.trie.insert(path, value_id);
    }

    pub fn insert_pair(&mut self, key1: &Term, key2: &Term, value: T) {
        let path = path_from_pair(key1, key2);
        let value_id = self.values.len();
        self.values.push(value);
        self.trie.insert(path, value_id);
    }

    // Appends to the existing value if possible. Otherwises, inserts a vec![U].
    pub fn insert_or_append<U>(pt: &mut PatternTree<Vec<U>>, key: &Term, value: U) {
        let path = path_from_term(key);
        match pt.trie.entry(path) {
            Entry::Occupied(entry) => {
                let value_id = entry.get();
                pt.values[*value_id].push(value);
            }
            Entry::Vacant(entry) => {
                let value_id = pt.values.len();
                pt.values.push(vec![value]);
                entry.insert(value_id);
            }
        }
    }

    // Finds a single match, if possible.
    // Returns the value id of the match, and the set of replacements used for the match.
    pub fn find_one_match<'a>(
        &'a self,
        term: &'a [TermComponent],
    ) -> Option<(&T, Vec<&'a [TermComponent]>)> {
        let mut key = vec![];
        let mut replacements = vec![];
        let subtrie = self.trie.subtrie(EMPTY_SLICE);
        match find_one_match(&subtrie, &mut key, term, &mut replacements) {
            Some(value_id) => Some((&self.values[value_id], replacements)),
            None => None,
        }
    }
}

pub struct LiteralTree {
    // Stores (sign, id) for each literal.
    tree: PatternTree<(bool, usize)>,
}

impl LiteralTree {
    pub fn new() -> LiteralTree {
        LiteralTree {
            tree: PatternTree::new(),
        }
    }

    // Inserts a literal along with its id.
    // This only inserts the given direction.
    pub fn insert(&mut self, literal: &Literal, id: usize) {
        self.tree
            .insert_pair(&literal.left, &literal.right, (literal.positive, id));
    }

    // Checks whether any literal in the tree is a generalization of the provided literal.
    // If so, returns a pair with:
    //   1. whether the sign of the provided literal and the generalization match
    //   2. the id of the generalization
    //
    // TODO: we just don't handle flipping literals around. That seems relevant though.
    pub fn find_generalization(&self, literal: &Literal) -> Option<(bool, usize)> {
        let flat = TermComponent::flatten_pair(&literal.left, &literal.right);
        match self.tree.find_one_match(&flat) {
            Some(((positive, id), _)) => Some((positive == &literal.positive, *id)),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_term(s: &str) {
        let input_term = Term::parse(s);
        let flat = TermComponent::flatten_term(&input_term);
        TermComponent::validate_slice(&flat);
        let output_term = TermComponent::unflatten_term(&flat);
        assert_eq!(input_term, output_term);
    }

    #[test]
    fn test_flatten_and_unflatten_term() {
        check_term("x0");
        check_term("c0(x0)");
        check_term("c0(x0, x1)");
        check_term("c0(x0, c1(x1))");
    }

    fn check_pair(s1: &str, s2: &str) {
        let input_term1 = Term::parse(s1);
        let input_term2 = Term::parse(s2);
        let flat = TermComponent::flatten_pair(&input_term1, &input_term2);
        TermComponent::validate_slice(&flat);
        let (output_term1, output_term2) = TermComponent::unflatten_pair(&flat);
        assert_eq!(input_term1, output_term1);
        assert_eq!(input_term2, output_term2);
    }

    #[test]
    fn test_flatten_and_unflatten_pair() {
        check_pair("x0", "x1");
        check_pair("c0(x0)", "c1(x1)");
        check_pair("c0(x0, x1)", "c1(x2, x3)");
        check_pair("c0(x0, c1(x1))", "c2(x2, x3)");
    }

    #[test]
    fn test_literal_tree() {
        let mut tree = LiteralTree::new();
        tree.insert(&Literal::parse("c0(x0, c1) = x0"), 7);

        let lit = Literal::parse("c0(x0, c1) = x0");
        assert!(tree.find_generalization(&lit).unwrap().0);

        let lit = Literal::parse("c0(c2, c1) = c2");
        assert!(tree.find_generalization(&lit).unwrap().0);

        let lit = Literal::parse("c0(x0, x1) = x0");
        assert!(tree.find_generalization(&lit).is_none());

        let lit = Literal::parse("c0(x0, c1) != x0");
        assert!(!tree.find_generalization(&lit).unwrap().0);

        tree.insert(&Literal::parse("x0 = x0"), 8);

        let lit = Literal::parse("x0 = c0");
        assert!(tree.find_generalization(&lit).is_none());

        let lit = Literal::parse("c0 = x0");
        assert!(tree.find_generalization(&lit).is_none());

        let lit = Literal::parse("c0 = c0");
        assert!(tree.find_generalization(&lit).unwrap().0);
    }
}
