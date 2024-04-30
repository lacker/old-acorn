use std::collections::HashMap;
use std::fmt;

use crate::atom::Atom;
use crate::term::Term;

// Each term has a unique id.
// We never invent new terms. We only make copies of terms that the caller created and find
// relationships between them.
type TermId = u32;

// Each term has a Decomposition that describes how it is created.
#[derive(Debug, Eq, Hash, PartialEq, Clone)]
enum Decomposition {
    // The term is just equal to an atom
    Atomic(Atom),

    // Head and args
    Compound(TermId, Vec<TermId>),
}

struct TermInfo {
    term: Term,
    group: GroupId,
}

// Each term belongs to a group.
// Terms that belong to the same group are equal.
type GroupId = u32;

// When groups are combined, we point the old one to the new one
enum GroupInfoReference {
    Remapped(GroupId),
    Present(GroupInfo),
}

struct GroupInfo {
    // All of the terms that belong to this group.
    terms: Vec<TermId>,

    // All of the adjacent edges, in any direction.
    // This might include references to deleted edges. They are only cleaned up lazily.
    edges: Vec<EdgeId>,
}

impl GroupInfo {
    fn heuristic_size(&self) -> usize {
        self.terms.len() + self.edges.len()
    }
}

// Each relation between terms implies a relation between groups.
// The relation among groups is called an "edge".
// You could call it a "hyperedge" but that feels a bit too fancy.
type EdgeId = u32;

#[derive(Debug, Eq, Hash, PartialEq, Clone)]
struct EdgeKey {
    head: GroupId,
    args: Vec<GroupId>,
}

impl EdgeKey {
    fn remap_group(&mut self, small_group: GroupId, large_group: GroupId) {
        if self.head == small_group {
            self.head = large_group;
        }
        for arg in &mut self.args {
            if *arg == small_group {
                *arg = large_group;
            }
        }
    }

    fn groups(&self) -> Vec<GroupId> {
        let mut answer = vec![self.head];
        answer.extend(self.args.iter().copied());
        answer.sort();
        answer.dedup();
        answer
    }
}

impl fmt::Display for EdgeKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.head)?;
        if !self.args.is_empty() {
            write!(f, "(")?;
            for (i, arg) in self.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

struct EdgeInfo {
    key: EdgeKey,
    result: GroupId,
}

impl EdgeInfo {
    fn remap_group(&mut self, small_group: GroupId, large_group: GroupId) {
        self.key.remap_group(small_group, large_group);
        if self.result == small_group {
            self.result = large_group;
        }
    }
}

impl fmt::Display for EdgeInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} -> {}", self.key, self.result)
    }
}

// The TermGraph stores concrete terms, along with relationships between them that represent
// equality, inequality, and subterm relationships.
pub struct TermGraph {
    // terms maps TermId to TermInfo.
    terms: Vec<TermInfo>,

    // groups maps GroupId to GroupInfo.
    groups: Vec<GroupInfoReference>,

    // edges maps EdgeId to EdgeInfo.
    // When an edge is deleted, we replace it with None.
    edges: Vec<Option<EdgeInfo>>,

    // An alternate way of keying the information in edges, by head+args.
    edge_map: HashMap<EdgeKey, GroupId>,

    // Each term has its decomposition stored so that we can look it back up again
    decompositions: HashMap<Decomposition, TermId>,

    // Pairs of groups that we have discovered are identical
    pending: Vec<(GroupId, GroupId)>,
}

impl TermGraph {
    pub fn new() -> TermGraph {
        TermGraph {
            terms: Vec::new(),
            groups: Vec::new(),
            edges: Vec::new(),
            edge_map: HashMap::new(),
            decompositions: HashMap::new(),
            pending: Vec::new(),
        }
    }

    // Returns None if this term isn't in the graph.
    pub fn get_term_id(&self, term: &Term) -> Option<TermId> {
        // Look up the head
        let head_key = Decomposition::Atomic(term.head.clone());
        let head_id = *self.decompositions.get(&head_key)?;

        if term.args.is_empty() {
            return Some(head_id);
        }

        // Look up the args
        let mut arg_ids = Vec::new();
        for arg in &term.args {
            arg_ids.push(self.get_term_id(arg)?);
        }

        let compound_key = Decomposition::Compound(head_id, arg_ids);
        self.decompositions.get(&compound_key).copied()
    }

    pub fn get_term(&self, term_id: TermId) -> &Term {
        &self.terms[term_id as usize].term
    }

    pub fn get_group(&self, term_id: TermId) -> GroupId {
        self.terms[term_id as usize].group
    }

    // Inserts the head of the provided term as an atom.
    // If it's already in the graph, return the existing term id.
    // Otherwise, make a new term id and give it a new group.
    fn insert_head(&mut self, term: &Term) -> TermId {
        let key = Decomposition::Atomic(term.head.clone());
        if let Some(&id) = self.decompositions.get(&key) {
            return id;
        }

        // Make a new term and group
        let term_id = self.terms.len() as TermId;
        let group_id = self.groups.len() as GroupId;

        let head = Term {
            term_type: term.head_type,
            head_type: term.head_type,
            head: term.head.clone(),
            args: vec![],
        };
        let term_info = TermInfo {
            term: head,
            group: group_id,
        };
        self.terms.push(term_info);
        let group_info = GroupInfoReference::Present(GroupInfo {
            terms: vec![term_id],
            edges: vec![],
        });
        self.groups.push(group_info);
        self.decompositions.insert(key, term_id);
        term_id
    }

    // Inserts a term.
    // Makes a new term, group, and edge if necessary.
    pub fn insert_term(&mut self, term: &Term) -> TermId {
        let head = self.insert_head(term);
        if term.args.is_empty() {
            return head;
        }
        let mut arg_ids = vec![];
        let mut arg_groups = vec![];
        for arg in &term.args {
            let arg_id = self.insert_term(arg);
            arg_ids.push(arg_id);
            let arg_group = self.terms[arg_id as usize].group;
            arg_groups.push(arg_group);
        }
        let key = Decomposition::Compound(head, arg_ids);
        if let Some(&id) = self.decompositions.get(&key) {
            return id;
        }
        let term_id = self.terms.len() as TermId;
        let head_group = self.terms[head as usize].group;
        let edge_key = EdgeKey {
            head: head_group,
            args: arg_groups,
        };

        let group_id = if let Some(&id) = self.edge_map.get(&edge_key) {
            // We already have an appropriate group and edge
            id
        } else {
            // We need to make a new group and edge
            let group_id = self.groups.len() as GroupId;
            let edge_id = self.edges.len() as EdgeId;
            let group_info = GroupInfo {
                terms: vec![term_id],
                edges: vec![edge_id],
            };
            self.groups.push(GroupInfoReference::Present(group_info));

            // Add references to this edge, to the old groups
            for g in edge_key.groups() {
                match &mut self.groups[g as usize] {
                    GroupInfoReference::Remapped(_) => {
                        panic!("unhandled case");
                    }
                    GroupInfoReference::Present(info) => {
                        info.edges.push(edge_id);
                    }
                }
            }
            let edge_info = EdgeInfo {
                key: edge_key.clone(),
                result: group_id,
            };
            self.edges.push(Some(edge_info));
            self.edge_map.insert(edge_key, group_id);

            group_id
        };

        let term_info = TermInfo {
            term: term.clone(),
            group: group_id,
        };
        self.terms.push(term_info);

        term_id
    }

    // Turn the small group into part of the large group.
    // Returns true if it's okay; return false if we ran into a contradiction.
    fn remap_group(&mut self, small_group: GroupId, large_group: GroupId) -> bool {
        let mut info_ref = GroupInfoReference::Remapped(large_group);
        std::mem::swap(&mut self.groups[small_group as usize], &mut info_ref);
        let info = match info_ref {
            GroupInfoReference::Remapped(_) => panic!("remapped from a remapped group"),
            GroupInfoReference::Present(info) => info,
        };

        for &term_id in &info.terms {
            self.terms[term_id as usize].group = large_group;
        }

        let mut keep_edges = vec![];
        for edge_id in info.edges {
            let edge = match &mut self.edges[edge_id as usize] {
                Some(edge) => edge,
                None => {
                    // This edge has already been deleted.
                    // Time to lazily delete the reference to it.
                    continue;
                }
            };
            self.edge_map.remove(&edge.key);
            edge.remap_group(small_group, large_group);
            if let Some(result_group) = self.edge_map.get(&edge.key) {
                // An edge for the new relationship already exists.
                // Instead of inserting edge.result, we need to delete this edge, and merge the
                // intended result with result_group.
                self.pending.push((edge.result, *result_group));
                self.edges[edge_id as usize] = None;
            } else {
                self.edge_map.insert(edge.key.clone(), edge.result);
                keep_edges.push(edge_id);
            }
        }

        match &mut self.groups[large_group as usize] {
            GroupInfoReference::Remapped(_) => panic!("remapped into a remapped group"),
            GroupInfoReference::Present(large_info) => {
                large_info.terms.extend(info.terms);
                large_info.edges.extend(keep_edges);
            }
        }

        true
    }

    // Returns false if we ran into a contradiction.
    fn clear_pending(&mut self) -> bool {
        while let Some((group1, group2)) = self.pending.pop() {
            if !self.set_groups_equal_once(group1, group2) {
                return false;
            }
        }
        true
    }

    // Set two groups to be equal.
    // Doesn't repeat to find the logical closure.
    // For that, use set_groups_equal.
    // Returns true if it's okay; return false if we ran into a contradiction.
    pub fn set_groups_equal_once(&mut self, group1: GroupId, group2: GroupId) -> bool {
        let size1 = match &self.groups[group1 as usize] {
            GroupInfoReference::Remapped(new_group1) => {
                return self.set_groups_equal_once(*new_group1, group2);
            }
            GroupInfoReference::Present(info) => info.heuristic_size(),
        };
        let size2 = match &self.groups[group2 as usize] {
            GroupInfoReference::Remapped(new_group2) => {
                return self.set_groups_equal_once(group1, *new_group2);
            }
            GroupInfoReference::Present(info) => info.heuristic_size(),
        };
        if size1 < size2 {
            self.remap_group(group1, group2)
        } else {
            self.remap_group(group2, group1)
        }
    }

    pub fn set_groups_equal(&mut self, group1: GroupId, group2: GroupId) {
        self.pending.push((group1, group2));
        self.clear_pending();
    }

    pub fn show_graph(&self) {
        println!("terms:");
        for (i, term_info) in self.terms.iter().enumerate() {
            println!("term {}, group {}: {}", i, term_info.group, term_info.term);
        }
        println!("edges:");
        for edge in &self.edges {
            if let Some(edge) = edge {
                println!("{}", edge);
            }
        }
    }

    #[cfg(test)]
    fn insert_str(&mut self, s: &str) -> TermId {
        self.insert_term(&Term::parse(s))
    }

    #[cfg(test)]
    fn assert_eq(&self, t1: TermId, t2: TermId) {
        assert_eq!(self.get_group(t1), self.get_group(t2));
    }

    #[cfg(test)]
    fn set_eq(&mut self, t1: TermId, t2: TermId) {
        self.set_groups_equal(self.get_group(t1), self.get_group(t2));
        self.assert_eq(t1, t2);
    }

    #[cfg(test)]
    fn assert_ne(&self, t1: TermId, t2: TermId) {
        assert_ne!(self.get_group(t1), self.get_group(t2));
    }

    #[cfg(test)]
    fn get_str(&self, s: &str) -> TermId {
        self.get_term_id(&Term::parse(s)).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identifying_atomic_subterms() {
        let mut g = TermGraph::new();
        let id1 = g.insert_str("c1(c2, c3)");
        let id2 = g.insert_str("c1(c4, c3)");
        g.assert_ne(id1, id2);
        let c2id = g.get_str("c2");
        let c4id = g.get_str("c4");
        g.assert_ne(c2id, c4id);
        g.set_eq(c2id, c4id);
        g.assert_eq(id1, id2);
    }

    #[test]
    fn test_multilevel_cascade() {
        let mut g = TermGraph::new();
        let term1 = g.insert_str("c1(c2(c3, c4), c2(c4, c3))");
        let term2 = g.insert_str("c1(c5, c5)");
        g.assert_ne(term1, term2);
        let sub1 = g.insert_str("c2(c3, c3)");
        let sub2 = g.get_str("c5");
        g.assert_ne(sub1, sub2);
        g.set_eq(sub1, sub2);
        let c3 = g.get_str("c3");
        let c4 = g.get_str("c4");
        g.assert_ne(c3, c4);
        g.set_eq(c3, c4);
        g.assert_eq(term1, term2);
    }
}
