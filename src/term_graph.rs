use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::hash::Hash;

use crate::atom::Atom;
use crate::term::Term;

// Each term has a unique id.
// We never invent new terms. We only make copies of terms that the caller created and find
// relationships between them.
pub type TermId = u32;

// Every time we set two terms equal or not equal, that action is tagged with a StepId.
// The term graph uses it to provide a history of the reasoning that led to a conclusion.
type StepId = usize;

// The rationale for a single rewrite step.
#[derive(Debug, Eq, PartialEq, Copy, Clone, Ord, PartialOrd)]
pub struct RewriteStep {
    // The external id of the rule used for this rewrite.
    // We know this rewrite is true based on the pattern step alone.
    pub pattern_id: StepId,

    // The depth of the subterm that inspired this rewrite.
    // If this rewrite is an exact math to the pattern, there is no particular subterm, so the
    // subterm depth is None.
    pub subterm_depth: Option<u32>,
}

// The goal of the TermGraph is to find a contradiction.
// When we do, we need to explain to the outside world why this is actually a contradiction.
// The TermGraphContradiction encodes this.
#[derive(Debug, Eq, PartialEq)]
pub struct TermGraphContradiction {
    // Every contradiction is based on one inequality, plus a set of rewrites that turn
    // one site of the inequality into the other.
    pub inequality_id: StepId,

    // The rewrites that turn one side of the inequality into the other.
    pub rewrite_chain: Vec<(Term, Term, RewriteStep)>,
}

// Each term has a Decomposition that describes how it is created.
#[derive(Debug, Eq, Hash, PartialEq, Clone)]
enum Decomposition {
    // The term is just equal to an atom
    Atomic(Atom),

    // Head and args
    Compound(TermId, Vec<TermId>),
}

#[derive(Clone)]
struct TermInfo {
    term: Term,
    group: GroupId,
    decomp: Decomposition,

    // The terms that this one can be directly turned into.
    // When the step id is not provided, we concluded it from composition.
    adjacent: Vec<(TermId, Option<RewriteStep>)>,
}

// Each term belongs to a group.
// Terms that belong to the same group are equal.
type GroupId = u32;

#[derive(Clone)]
struct GroupInfo {
    // All of the terms that belong to this group, in the order they were added.
    terms: Vec<TermId>,

    // Each way to create a term of this group by composing subterms from other groups.
    // This might include references to deleted compounds. They are only cleaned up lazily.
    compounds: Vec<CompoundId>,

    // The other groups that we know are not equal to this one.
    // For each inequality, we store the two terms that we know are not equal,
    // along with the step that we know it from.
    inequalities: HashMap<GroupId, (TermId, TermId, StepId)>,
}

impl GroupInfo {
    fn heuristic_size(&self) -> usize {
        self.terms.len() + self.compounds.len()
    }
}

// Each composition relation between terms implies a composition relation between groups.
// The composition relations between groups each get their own id, so we can update them when
// we combine groups.
type CompoundId = u32;

#[derive(Debug, Eq, Hash, PartialEq, Clone)]
struct CompoundKey {
    head: GroupId,
    args: Vec<GroupId>,
}

impl CompoundKey {
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

impl fmt::Display for CompoundKey {
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

#[derive(Clone)]
struct CompoundInfo {
    key: CompoundKey,
    result_term: TermId,
}

impl fmt::Display for CompoundInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "key {} -> term {}", self.key, self.result_term)
    }
}

// The TermGraph stores concrete terms, along with relationships between them that represent
// equality, inequality, and subterm relationships.
#[derive(Clone)]
pub struct TermGraph {
    // terms maps TermId to TermInfo.
    terms: Vec<TermInfo>,

    // groups maps GroupId to GroupInfo.
    groups: Vec<Option<GroupInfo>>,

    // compounds maps CompoundId to CompoundInfo.
    // When a compound is deleted, we replace it with None.
    compounds: Vec<Option<CompoundInfo>>,

    // Keying the compounds so that we can check if a composition belongs to an existing group.
    compound_map: HashMap<CompoundKey, TermId>,

    // Each term has its decomposition stored so that we can look it back up again
    decompositions: HashMap<Decomposition, TermId>,

    // Pairs of terms that we have discovered are identical
    pending: Vec<(TermId, TermId, Option<RewriteStep>)>,

    // Set when we discover a contradiction.
    // The provided step sets these terms to be unequal. However, the term graph also
    // knows that they are equal. This is a contradiction.
    contradiction: Option<(TermId, TermId, StepId)>,
}

impl TermGraph {
    pub fn new() -> TermGraph {
        TermGraph {
            terms: Vec::new(),
            groups: Vec::new(),
            compounds: Vec::new(),
            compound_map: HashMap::new(),
            decompositions: HashMap::new(),
            pending: Vec::new(),
            contradiction: None,
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

    pub fn has_contradiction(&self) -> bool {
        self.contradiction.is_some()
    }

    // Used to explain which steps lead to a contradiction.
    // Returns None if there is no contradiction.
    pub fn get_contradiction(&self) -> Option<TermGraphContradiction> {
        let (term1, term2, inequality_id) = self.contradiction?;
        let mut rewrite_chain = vec![];
        self.expand_steps(term1, term2, &mut rewrite_chain);
        Some(TermGraphContradiction {
            inequality_id,
            rewrite_chain,
        })
    }

    fn get_group_info(&self, group_id: GroupId) -> &GroupInfo {
        match &self.groups[group_id as usize] {
            None => panic!("group is remapped"),
            Some(info) => info,
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
            decomp: key.clone(),
            adjacent: vec![],
        };
        self.terms.push(term_info);
        let group_info = Some(GroupInfo {
            terms: vec![term_id],
            compounds: vec![],
            inequalities: HashMap::new(),
        });
        self.groups.push(group_info);
        self.decompositions.insert(key, term_id);
        term_id
    }

    // Inserts a term composition relationship.
    // If it's already in the graph, return the existing term id.
    // Otherwise, make a new term and group.
    fn insert_term_compound(&mut self, term: &Term, head: TermId, args: Vec<TermId>) -> TermId {
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
            decomp: key.clone(),
            adjacent: vec![],
        };
        self.terms.push(term_info);
        let group_info = Some(GroupInfo {
            terms: vec![term_id],
            compounds: vec![],
            inequalities: HashMap::new(),
        });
        self.groups.push(group_info);
        self.decompositions.insert(key, term_id);
        term_id
    }

    // Adds a group composition relationship.
    // If we should combine groups, add them to the pending list.
    fn insert_group_compound(&mut self, head: GroupId, args: Vec<GroupId>, result_term: TermId) {
        let result_group = self.get_group_id(result_term);
        let key = CompoundKey { head, args };
        if let Some(&existing_result_term) = self.compound_map.get(&key) {
            let existing_result_group = self.get_group_id(existing_result_term);
            if existing_result_group != result_group {
                self.pending.push((existing_result_term, result_term, None));
            }
            return;
        }

        // We need to make a new relatinoship
        let compound_info = CompoundInfo {
            key: key.clone(),
            result_term,
        };
        for group in key.groups() {
            match &mut self.groups[group as usize] {
                None => {
                    panic!("compound info refers to a remapped group");
                }
                Some(info) => {
                    info.compounds.push(self.compounds.len() as CompoundId);
                }
            }
        }
        self.compounds.push(Some(compound_info));
        self.compound_map.insert(key, result_term);
        return;
    }

    // Inserts a term.
    // Makes a new term, group, and compound if necessary.
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

        let result_term_id = self.insert_term_compound(term, head_term_id, arg_term_ids);
        self.insert_group_compound(head_group_id, arg_group_ids, result_term_id);
        self.process_pending();
        result_term_id
    }

    // Merge the small group into the large group.
    fn remap_group(
        &mut self,
        old_term: TermId,
        old_group: GroupId,
        new_term: TermId,
        new_group: GroupId,
        step: Option<RewriteStep>,
    ) {
        let old_info = self.groups[old_group as usize]
            .take()
            .expect("group is remapped");

        for &term_id in &old_info.terms {
            self.terms[term_id as usize].group = new_group;
        }

        let mut keep_compounds = vec![];
        for compound_id in old_info.compounds {
            {
                let compound = match &mut self.compounds[compound_id as usize] {
                    Some(compound) => compound,
                    None => {
                        // This compound has already been deleted.
                        // Time to lazily delete the reference to it.
                        continue;
                    }
                };
                self.compound_map.remove(&compound.key);
                compound.key.remap_group(old_group, new_group);
            }
            let compound = self.compounds[compound_id as usize]
                .as_ref()
                .expect("how does this happen?");

            if let Some(&existing_result_term) = self.compound_map.get(&compound.key) {
                // An compound for the new relationship already exists.
                // Instead of inserting compound.result, we need to delete this compound, and merge the
                // intended result with result_group.
                self.pending
                    .push((compound.result_term, existing_result_term, None));
                self.compounds[compound_id as usize] = None;
            } else {
                self.compound_map
                    .insert(compound.key.clone(), compound.result_term);
                keep_compounds.push(compound_id);
            }
        }

        // Rekey the inequalities that refer to this group from elsewhere
        for &unequal_group in old_info.inequalities.keys() {
            let unequal_info = self.groups[unequal_group as usize]
                .as_mut()
                .expect("group is remapped");
            let value = unequal_info
                .inequalities
                .remove(&old_group)
                .expect("inequality not there");
            if unequal_group == new_group {
                // We found a contradiction.
                self.contradiction = Some(value);
            }
            if !unequal_info.inequalities.contains_key(&new_group) {
                unequal_info.inequalities.insert(new_group, value);
            }
        }

        // Merge the old info into the new info
        let new_info = self.groups[new_group as usize]
            .as_mut()
            .expect("group is remapped");
        new_info.terms.extend(old_info.terms);
        new_info.compounds.extend(keep_compounds);
        for (group, value) in old_info.inequalities {
            if !new_info.inequalities.contains_key(&group) {
                new_info.inequalities.insert(group, value);
            }
        }

        self.terms[old_term as usize]
            .adjacent
            .push((new_term, step));
        self.terms[new_term as usize]
            .adjacent
            .push((old_term, step));
    }

    fn process_pending(&mut self) {
        while let Some((term1, term2, step)) = self.pending.pop() {
            // We can stop processing when we find a contradiction.
            if self.contradiction.is_none() {
                self.set_terms_equal_once(term1, term2, step)
            }
        }
    }

    // Set two terms to be equal.
    // Doesn't repeat to find the logical closure.
    // For that, use identify_terms.
    fn set_terms_equal_once(&mut self, term1: TermId, term2: TermId, step: Option<RewriteStep>) {
        let group1 = self.get_group_id(term1);
        let group2 = self.get_group_id(term2);
        if group1 == group2 {
            // They already are equal
            return;
        }
        let info1 = self.get_group_info(group1);
        let info2 = self.get_group_info(group2);

        // Keep around the smaller number, as a tiebreak
        if (info1.heuristic_size(), group2) < (info2.heuristic_size(), group1) {
            self.remap_group(term1, group1, term2, group2, step)
        } else {
            self.remap_group(term2, group2, term1, group1, step)
        };
    }

    pub fn set_terms_equal(
        &mut self,
        term1: TermId,
        term2: TermId,
        pattern_id: StepId,
        subterm_depth: Option<u32>,
    ) {
        let step = RewriteStep {
            pattern_id,
            subterm_depth,
        };
        self.pending.push((term1, term2, Some(step)));
        self.process_pending();
    }

    pub fn set_terms_not_equal(&mut self, term1: TermId, term2: TermId, step: StepId) {
        let group1 = self.get_group_id(term1);
        let group2 = self.get_group_id(term2);
        if group1 == group2 {
            self.contradiction = Some((term1, term2, step));
            return;
        }

        let info1 = &mut self.groups[group1 as usize]
            .as_mut()
            .expect("group is remapped");
        if info1.inequalities.contains_key(&group2) {
            return;
        }
        info1.inequalities.insert(group2, (term1, term2, step));
        let info2 = &mut self.groups[group2 as usize]
            .as_mut()
            .expect("group is remapped");
        let prev = info2.inequalities.insert(group1, (term1, term2, step));
        if prev.is_some() {
            panic!("asymmetry in group inequalities");
        }
    }

    fn as_compound(&self, term: TermId) -> (TermId, &Vec<TermId>) {
        match &self.terms[term as usize].decomp {
            Decomposition::Compound(head, args) => (*head, args),
            _ => panic!("not a compound"),
        }
    }

    // Gets a step of edges that demonstrate that term1 and term2 are equal.
    // The step is None if the edge is composite.
    // Panics if there is no path.
    fn get_path(&self, term1: TermId, term2: TermId) -> Vec<(TermId, TermId, Option<RewriteStep>)> {
        if term1 == term2 {
            return vec![];
        }

        // Find paths that lead to term2 from everywhere.
        // predecessor maps term_a -> (term_b, step) where the edge
        //   (term_a, term_b, step)
        // is the first edge to get to term2 from term_a.
        let mut next_edge = HashMap::new();

        let mut queue = vec![term2];
        'outer: loop {
            let term_b = queue.pop().expect("no path between terms");
            for (term_a, step) in &self.terms[term_b as usize].adjacent {
                if next_edge.contains_key(term_a) {
                    // We already have a way to get from term_a to term2
                    continue;
                }
                next_edge.insert(*term_a, (term_b, *step));
                if *term_a == term1 {
                    break 'outer;
                }
                queue.push(*term_a);
            }
        }

        let mut answer = vec![];
        let mut term_a = term1;
        while term_a != term2 {
            let (term_b, step) = next_edge[&term_a];
            answer.push((term_a, term_b, step));
            term_a = term_b;
        }
        answer
    }

    // For every step from term1 to term2, show the rewritten subterms, as well as the
    // id of the rule that enabled it, if there is one.
    // This is "postorder" in the sense that we show a rewritten compound term after showing
    // the rewrites for the subterms.
    // The compound rewrites have a step id of None.
    // The rewritten subterms have a step id with the rule that they are based on.
    fn expand_steps(
        &self,
        term1: TermId,
        term2: TermId,
        output: &mut Vec<(Term, Term, RewriteStep)>,
    ) {
        if term1 == term2 {
            return;
        }
        let path = self.get_path(term1, term2);
        for (a_id, b_id, step) in path {
            if step.is_none() {
                // We have a compound relationship between a_id and b_id
                let (head_a, args_a) = self.as_compound(a_id);
                let (head_b, args_b) = self.as_compound(b_id);
                assert_eq!(args_a.len(), args_b.len());
                self.expand_steps(head_a, head_b, output);
                for (arg_a, arg_b) in args_a.iter().zip(args_b.iter()) {
                    self.expand_steps(*arg_a, *arg_b, output);
                }
            }

            let term_a = self.get_term(a_id);
            let term_b = self.get_term(b_id);

            if let Some(step) = step {
                output.push((term_a.clone(), term_b.clone(), step));
            }
        }
    }

    fn get_step_ids_helper(&self, term1: TermId, term2: TermId, output: &mut BTreeSet<StepId>) {
        if term1 == term2 {
            return;
        }
        let path = self.get_path(term1, term2);
        for (term_a, term_b, step) in path {
            match step {
                Some(step) => {
                    output.insert(step.pattern_id);
                }
                None => {
                    let (head_a, args_a) = self.as_compound(term_a);
                    let (head_b, args_b) = self.as_compound(term_b);
                    assert_eq!(args_a.len(), args_b.len());
                    self.get_step_ids_helper(head_a, head_b, output);
                    for (arg_a, arg_b) in args_a.iter().zip(args_b.iter()) {
                        self.get_step_ids_helper(*arg_a, *arg_b, output);
                    }
                }
            }
        }
    }

    // Extract a list of steps ids that we used to prove that these two terms are equal.
    // This does deduplicate.
    pub fn get_step_ids(&self, term1: TermId, term2: TermId) -> Vec<usize> {
        let mut answer = BTreeSet::new();
        self.get_step_ids_helper(term1, term2, &mut answer);
        answer.into_iter().collect()
    }

    pub fn show_graph(&self) {
        println!("terms:");
        for (i, term_info) in self.terms.iter().enumerate() {
            println!("term {}, group {}: {}", i, term_info.group, term_info.term);
        }
        println!("compounds:");
        for compound in &self.compounds {
            if let Some(compound) = compound {
                println!("{}", compound);
            }
        }
    }

    // Checks that the group id has not been remapped
    fn validate_group_id(&self, group_id: GroupId) -> &GroupInfo {
        assert!(group_id < self.groups.len() as GroupId);
        match &self.groups[group_id as usize] {
            None => {
                panic!("group {} is remapped", group_id)
            }
            Some(info) => info,
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
                None => {
                    continue;
                }
                Some(info) => info,
            };
            for term_id in &group_info.terms {
                let term_group = self.terms[*term_id as usize].group;
                assert_eq!(term_group, group_id as GroupId);
            }
            for compound_id in &group_info.compounds {
                let compound = &self.compounds[*compound_id as usize];
                let compound = match compound {
                    Some(compound) => compound,
                    None => continue,
                };
                assert!(compound.key.touches_group(group_id as GroupId));
            }
        }

        for (compound_id, compound) in self.compounds.iter().enumerate() {
            let compound = match compound {
                Some(compound) => compound,
                None => continue,
            };
            let groups = compound.key.groups();
            for group in groups {
                let info = self.validate_group_id(group);
                assert!(info.compounds.contains(&(compound_id as CompoundId)));
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
    fn set_eq(&mut self, t1: TermId, t2: TermId, id: usize) {
        self.set_terms_equal(t1, t2, id, None);
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
        assert_eq!(g.get_step_ids(id1, id2), vec![0]);
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
        assert_eq!(g.get_step_ids(term1, term2), vec![0, 1]);
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
        assert_eq!(g.get_step_ids(id1, id2), vec![0]);
    }

    #[test]
    fn test_skipping_unneeded_steps() {
        let mut g = TermGraph::new();
        let c0 = g.insert_str("c0");
        let c1 = g.insert_str("c1");
        let c2 = g.insert_str("c2");
        let c3 = g.insert_str("c3");
        let c4 = g.insert_str("c4");
        let c5 = g.insert_str("c5");
        g.set_eq(c1, c2, 0);
        g.set_eq(c4, c5, 1);
        g.set_eq(c0, c1, 2);
        g.set_eq(c3, c4, 3);
        g.set_eq(c0, c3, 4);
        g.show_graph();
        assert_eq!(g.get_step_ids(c0, c3), vec![4]);
    }

    #[test]
    fn test_finding_contradiction() {
        let mut g = TermGraph::new();
        let term1 = g.insert_str("c1(c2, c3)");
        let term2 = g.insert_str("c4(c5, c6)");
        g.set_terms_not_equal(term1, term2, 0);
        assert!(!g.has_contradiction());
        let c1 = g.get_str("c1");
        let c4 = g.get_str("c4");
        g.set_eq(c1, c4, 1);
        assert!(!g.has_contradiction());
        let c2 = g.get_str("c2");
        let c5 = g.get_str("c5");
        g.set_eq(c2, c5, 2);
        assert!(!g.has_contradiction());
        let c3 = g.get_str("c3");
        let c6 = g.get_str("c6");
        g.set_eq(c3, c6, 3);
        assert!(g.has_contradiction());
    }
}
