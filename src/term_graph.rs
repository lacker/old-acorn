use std::collections::HashMap;
use std::fmt;

use crate::atom::Atom;
use crate::term::Term;

// Each term has a unique id.
// We never invent new terms. We only make copies of terms that the caller created and find
// relationships between them.
type TermId = u32;

// Every time we set two terms equal or not equal, that action is tagged with a StepId.
// The term graph uses it to provide a history of the reasoning that led to a conclusion.
type StepId = usize;

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
    original_group: GroupId,
    decomp: Decomposition,
}

// Each term belongs to a group.
// Terms that belong to the same group are equal.
type GroupId = u32;

// When groups are combined, we point the old one to the new one
enum GroupInfoReference {
    // The new group, along with the reasoning for the remap
    Remapped(Reasoning),

    // The information for the existing group
    Present(GroupInfo),
}

// The reasoning that led us to combine two groups.
// Reasoning is always based on terms. When we learn that two terms from different groups are
// identical, we combine the groups that they belong to.
struct Reasoning {
    // The old group is the one we eliminated, and the old term is the representative we used.
    old_term: TermId,
    old_group: GroupId,

    // The new group is the one that we created, and the new term is the representative we used.
    new_term: TermId,
    new_group: GroupId,

    // If step is set, we combined these groups because we were explicitly instructed in this step
    // that these two terms are equal.
    // If step is not set, this is a recursive reasoning based on the decomposition of the terms.
    step: Option<StepId>,
}

struct GroupInfo {
    // All of the terms that belong to this group, in the order they were added.
    terms: Vec<TermId>,

    // All of the edges that use this group in the key.
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

    fn touches_group(&self, group: GroupId) -> bool {
        if self.head == group {
            return true;
        }
        self.args.contains(&group)
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
    result_term: TermId,
}

impl fmt::Display for EdgeInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "key {} -> term {}", self.key, self.result_term)
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
    edge_map: HashMap<EdgeKey, TermId>,

    // Each term has its decomposition stored so that we can look it back up again
    decompositions: HashMap<Decomposition, TermId>,

    // Pairs of terms that we have discovered are identical
    pending: Vec<(TermId, TermId)>,
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

    pub fn get_group_id(&self, term_id: TermId) -> GroupId {
        self.terms[term_id as usize].group
    }

    fn get_group_info(&self, group_id: GroupId) -> &GroupInfo {
        match &self.groups[group_id as usize] {
            GroupInfoReference::Remapped(_) => panic!("group is remapped"),
            GroupInfoReference::Present(info) => info,
        }
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
            original_group: group_id,
            decomp: key.clone(),
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

    // Inserts a compound term.
    // If it's already in the graph, return the existing term id.
    // Otherwise, make a new term and group.
    fn insert_compound(&mut self, term: &Term, head: TermId, args: Vec<TermId>) -> TermId {
        let key = Decomposition::Compound(head, args);
        if let Some(&id) = self.decompositions.get(&key) {
            return id;
        }

        // Make a new term and group
        let term_id = self.terms.len() as TermId;
        let group_id = self.groups.len() as GroupId;
        let term_info = TermInfo {
            term: term.clone(),
            group: group_id,
            original_group: group_id,
            decomp: key.clone(),
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

    // Adds an edge to the graph.
    // If we should combine groups, add them to the pending list.
    fn insert_edge(&mut self, head: GroupId, args: Vec<GroupId>, result_term: TermId) {
        let result_group = self.get_group_id(result_term);
        let key = EdgeKey { head, args };
        if let Some(&existing_result_term) = self.edge_map.get(&key) {
            let existing_result_group = self.get_group_id(existing_result_term);
            if existing_result_group != result_group {
                self.pending.push((existing_result_term, result_term));
            }
            return;
        }

        // We need to make a new edge
        let edge_info = EdgeInfo {
            key: key.clone(),
            result_term,
        };
        for group in key.groups() {
            match &mut self.groups[group as usize] {
                GroupInfoReference::Remapped(_) => {
                    panic!("edge refers to a remapped group");
                }
                GroupInfoReference::Present(info) => {
                    info.edges.push(self.edges.len() as EdgeId);
                }
            }
        }
        self.edges.push(Some(edge_info));
        self.edge_map.insert(key, result_term);
        return;
    }

    // Inserts a term.
    // Makes a new term, group, and edge if necessary.
    pub fn insert_term(&mut self, term: &Term) -> TermId {
        let head_term_id = self.insert_head(term);
        if term.args.is_empty() {
            return head_term_id;
        }
        let head_group_id = self.get_group_id(head_term_id);

        let mut arg_term_ids = vec![];
        let mut arg_group_ids = vec![];
        for arg in &term.args {
            let arg_term_id = self.insert_term(arg);
            arg_term_ids.push(arg_term_id);
            let arg_group_id = self.get_group_id(arg_term_id);
            arg_group_ids.push(arg_group_id);
        }

        let result_term_id = self.insert_compound(term, head_term_id, arg_term_ids);
        self.insert_edge(head_group_id, arg_group_ids, result_term_id);
        self.clear_pending();
        result_term_id
    }

    // Merge the small group into the large group.
    fn remap_group(
        &mut self,
        old_term: TermId,
        old_group: GroupId,
        new_term: TermId,
        new_group: GroupId,
        step: Option<StepId>,
    ) {
        let reasoning = Reasoning {
            old_term,
            old_group,
            new_term,
            new_group,
            step,
        };
        let mut info_ref = GroupInfoReference::Remapped(reasoning);
        std::mem::swap(&mut self.groups[old_group as usize], &mut info_ref);
        let info = match info_ref {
            GroupInfoReference::Remapped(_) => panic!("remapped from a remapped group"),
            GroupInfoReference::Present(info) => info,
        };

        for &term_id in &info.terms {
            self.terms[term_id as usize].group = new_group;
        }

        let mut keep_edges = vec![];
        for edge_id in info.edges {
            {
                let edge = match &mut self.edges[edge_id as usize] {
                    Some(edge) => edge,
                    None => {
                        // This edge has already been deleted.
                        // Time to lazily delete the reference to it.
                        continue;
                    }
                };
                self.edge_map.remove(&edge.key);
                edge.key.remap_group(old_group, new_group);
            }
            let edge = match &self.edges[edge_id as usize] {
                Some(edge) => edge,
                None => panic!("how does this happen"),
            };
            if let Some(&existing_result_term) = self.edge_map.get(&edge.key) {
                // An edge for the new relationship already exists.
                // Instead of inserting edge.result, we need to delete this edge, and merge the
                // intended result with result_group.
                self.pending.push((edge.result_term, existing_result_term));
                self.edges[edge_id as usize] = None;
            } else {
                self.edge_map.insert(edge.key.clone(), edge.result_term);
                keep_edges.push(edge_id);
            }
        }

        match &mut self.groups[new_group as usize] {
            GroupInfoReference::Remapped(_) => panic!("remapped into a remapped group"),
            GroupInfoReference::Present(large_info) => {
                large_info.terms.extend(info.terms);
                large_info.edges.extend(keep_edges);
            }
        }
    }

    fn clear_pending(&mut self) {
        while let Some((term1, term2)) = self.pending.pop() {
            self.set_terms_equal_once(term1, term2, None)
        }
    }

    // Set two terms to be equal.
    // Doesn't repeat to find the logical closure.
    // For that, use identify_terms.
    fn set_terms_equal_once(&mut self, term1: TermId, term2: TermId, step: Option<StepId>) {
        let group1 = self.get_group_id(term1);
        let info1 = self.get_group_info(group1);
        let group2 = self.get_group_id(term2);
        let info2 = self.get_group_info(group2);
        if info1.heuristic_size() < info2.heuristic_size() {
            self.remap_group(term1, group1, term2, group2, step)
        } else {
            self.remap_group(term2, group2, term1, group1, step)
        };
    }

    pub fn identify_terms(&mut self, term1: TermId, term2: TermId, step: StepId) {
        self.pending.push((term1, term2));
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

    // Checks that the group id has not been remapped
    fn validate_group_id(&self, group_id: GroupId) -> &GroupInfo {
        assert!(group_id < self.groups.len() as GroupId);
        match &self.groups[group_id as usize] {
            GroupInfoReference::Remapped(_) => {
                panic!("group {} is remapped", group_id)
            }
            GroupInfoReference::Present(info) => info,
        }
    }

    // Panics if it finds a consistency problem.
    pub fn validate(&self) {
        for (term_id, term_info) in self.terms.iter().enumerate() {
            let info = self.validate_group_id(term_info.group);
            assert!(info.terms.contains(&(term_id as TermId)));
        }

        for (group_id, group_info) in self.groups.iter().enumerate() {
            let group_info = match group_info {
                GroupInfoReference::Remapped(reasoning) => {
                    assert_eq!(reasoning.old_group, group_id as GroupId);
                    let current1 = self.get_group_id(reasoning.old_term);
                    let current2 = self.get_group_id(reasoning.new_term);
                    assert_eq!(current1, current2);
                    continue;
                }
                GroupInfoReference::Present(info) => info,
            };
            for term_id in &group_info.terms {
                let term_group = self.terms[*term_id as usize].group;
                assert_eq!(term_group, group_id as GroupId);
            }
            for edge_id in &group_info.edges {
                let edge = &self.edges[*edge_id as usize];
                let edge = match edge {
                    Some(edge) => edge,
                    None => continue,
                };
                assert!(edge.key.touches_group(group_id as GroupId));
            }
        }

        for (edge_id, edge) in self.edges.iter().enumerate() {
            let edge = match edge {
                Some(edge) => edge,
                None => continue,
            };
            let groups = edge.key.groups();
            for group in groups {
                let info = self.validate_group_id(group);
                assert!(info.edges.contains(&(edge_id as EdgeId)));
            }
        }
    }

    #[cfg(test)]
    fn insert_str(&mut self, s: &str) -> TermId {
        let id = self.insert_term(&Term::parse(s));
        self.validate();
        id
    }

    #[cfg(test)]
    fn assert_eq(&self, t1: TermId, t2: TermId) {
        assert_eq!(self.get_group_id(t1), self.get_group_id(t2));
    }

    #[cfg(test)]
    fn set_eq(&mut self, t1: TermId, t2: TermId, step: usize) {
        self.identify_terms(t1, t2, step);
        self.validate();
        self.assert_eq(t1, t2);
    }

    #[cfg(test)]
    fn assert_ne(&self, t1: TermId, t2: TermId) {
        assert_ne!(self.get_group_id(t1), self.get_group_id(t2));
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
        g.set_eq(c2id, c4id, 0);
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
        g.set_eq(sub1, sub2, 0);
        let c3 = g.get_str("c3");
        let c4 = g.get_str("c4");
        g.assert_ne(c3, c4);
        g.set_eq(c3, c4, 1);
        g.assert_eq(term1, term2);
    }

    #[test]
    fn test_identifying_heads() {
        let mut g = TermGraph::new();
        let id1 = g.insert_str("c1(c2, c3)");
        let id2 = g.insert_str("c4(c2, c3)");
        g.assert_ne(id1, id2);
        let c1 = g.get_str("c1");
        let c4 = g.get_str("c4");
        g.set_eq(c1, c4, 0);
        g.assert_eq(id1, id2);
    }
}
