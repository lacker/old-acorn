// The CanonicalRewriteTree stores a set of "canonical rewrites", that we want to always do when possible.
//
// We aren't currently using the CanonicalRewriteTree, but it's here for reference.
// It demonstrates the use of TermComponent and PatternTree, and its tests are testing things
// we care about indirectly.

use crate::pattern_tree::{PatternTree, TermComponent};
use crate::term::Term;

struct CanonicalRewriteValue {
    rule_id: usize,
    output: Vec<TermComponent>,
}

pub struct CanonicalRewriteTree {
    tree: PatternTree<CanonicalRewriteValue>,

    validate: bool,
}

impl CanonicalRewriteTree {
    pub fn new() -> CanonicalRewriteTree {
        CanonicalRewriteTree {
            tree: PatternTree::new(),
            validate: false,
        }
    }

    // Overwrites any existing rule.
    pub fn add_rule(&mut self, rule_id: usize, input_term: &Term, output_term: &Term) {
        if input_term.atomic_variable().is_some() {
            panic!("cannot rewrite atomic variables to something else");
        }
        let value = CanonicalRewriteValue {
            rule_id,
            output: TermComponent::flatten_term(output_term),
        };
        self.tree.insert_term(input_term, value);
    }

    // Does one rewrite.
    // Checks all subterms.
    // Returns the new sequence of components, if there is a rewrite.
    // Appends any rule used to rules.
    fn rewrite_once(
        &self,
        components: &Vec<TermComponent>,
        rules: &mut Vec<usize>,
    ) -> Option<Vec<TermComponent>> {
        for i in 0..components.len() {
            let subterm_size = components[i].size();
            let subterm = &components[i..i + subterm_size];

            if let Some((value, replacements)) = self.tree.find_one_match(subterm) {
                rules.push(value.rule_id);
                // Construct a new subterm.
                let new_subterm =
                    TermComponent::replace_or_shift(&value.output, &replacements, None);
                if self.validate {
                    TermComponent::validate_slice(&new_subterm);
                }
                if i == 0 {
                    // We just replaced the whole term
                    return Some(new_subterm);
                }

                // Replace the old subterm with the new subterm.
                // It's important that delta can be negative, if a rewrite shrinks the term.
                let delta: i32 = (new_subterm.len() as i32) - (subterm_size as i32);
                let mut new_components = vec![];
                for (j, component) in components[..i].iter().enumerate() {
                    if j + component.size() <= i {
                        // This component doesn't contain the new subterm
                        new_components.push(component.clone());
                    } else {
                        // This component does contain the new subterm, so alter its size
                        new_components.push(component.alter_size(delta));
                    }
                }
                new_components.extend_from_slice(&new_subterm);
                new_components.extend_from_slice(&components[i + subterm_size..]);
                return Some(new_components);
            }
        }
        None
    }

    // Rewrites repeatedly.
    // Returns the final term, if any rewrites happen.
    // Appends the rules used to rules.
    pub fn rewrite(&self, term: &Term, rules: &mut Vec<usize>) -> Option<Term> {
        let mut components = TermComponent::flatten_term(term);

        // Infinite loops are hard to debug, so cap this loop.
        for i in 0..100 {
            match self.rewrite_once(&components, rules) {
                Some(new_components) => {
                    components = new_components;
                    continue;
                }
                None => {
                    if i == 0 {
                        return None;
                    } else {
                        let term = TermComponent::unflatten_term(&components);
                        return Some(term);
                    }
                }
            }
        }

        panic!("rewrite looped too many times");
    }

    pub fn rewrite_or_clone(&self, term: &Term, rules: &mut Vec<usize>) -> Term {
        match self.rewrite(term, rules) {
            Some(t) => t,
            None => term.clone(),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_crt_atoms() {
        let mut tree = CanonicalRewriteTree::new();
        tree.validate = true;
        let mut rules = vec![];
        tree.add_rule(0, &Term::parse("c1"), &Term::parse("c0"));
        let term = tree.rewrite(&Term::parse("c1"), &mut rules).unwrap();
        assert_eq!(rules, vec![0]);
        assert_eq!(term, Term::parse("c0"));
    }

    #[test]
    fn test_crt_functions() {
        let mut tree = CanonicalRewriteTree::new();
        tree.validate = true;
        let mut rules = vec![];
        tree.add_rule(0, &Term::parse("c1(x0)"), &Term::parse("c0(x0)"));
        let term = tree.rewrite(&Term::parse("c1(c2)"), &mut rules).unwrap();
        assert_eq!(rules, vec![0]);
        assert_eq!(term, Term::parse("c0(c2)"));
    }

    #[test]
    fn test_crt_multiple_rewrites() {
        let mut tree = CanonicalRewriteTree::new();
        tree.validate = true;
        let mut rules = vec![];
        tree.add_rule(0, &Term::parse("c1(x0)"), &Term::parse("c0(x0)"));
        tree.add_rule(1, &Term::parse("c0(c2)"), &Term::parse("c3"));
        let term = tree.rewrite(&Term::parse("c1(c2)"), &mut rules).unwrap();
        assert_eq!(rules, vec![0, 1]);
        assert_eq!(term, Term::parse("c3"));
    }

    #[test]
    fn test_crt_tail_subterms() {
        let mut tree = CanonicalRewriteTree::new();
        tree.validate = true;
        let mut rules = vec![];
        tree.add_rule(0, &Term::parse("c1(x0)"), &Term::parse("c0(x0)"));
        tree.add_rule(1, &Term::parse("c0(c2)"), &Term::parse("c3"));
        let term = tree
            .rewrite(&Term::parse("c4(c1(c2))"), &mut rules)
            .unwrap();
        assert_eq!(rules, vec![0, 1]);
        assert_eq!(term, Term::parse("c4(c3)"));
    }

    #[test]
    fn test_crt_non_tail_subterms() {
        let mut tree = CanonicalRewriteTree::new();
        tree.validate = true;
        let mut rules = vec![];
        tree.add_rule(0, &Term::parse("c1(x0)"), &Term::parse("c0(x0)"));
        tree.add_rule(1, &Term::parse("c0(c2)"), &Term::parse("c3"));
        tree.add_rule(2, &Term::parse("c4(x0, x0)"), &Term::parse("c1(x0)"));
        let term = tree
            .rewrite(&Term::parse("c4(c1(c2), c3)"), &mut rules)
            .unwrap();
        assert_eq!(rules, vec![0, 1, 2, 0]);
        assert_eq!(term, Term::parse("c0(c3)"));
    }

    #[test]
    fn test_rewriting_same_head_different_num_args() {
        let mut tree = CanonicalRewriteTree::new();
        tree.validate = true;
        let mut rules = vec![];
        tree.add_rule(0, &Term::parse("c1(x0, x1)"), &Term::parse("c0(x0, x1)"));
        assert!(tree.rewrite(&Term::parse("c1(x0)"), &mut rules).is_none());
    }

    #[test]
    fn test_crt_variables_cant_just_match_themselves() {
        let mut tree = CanonicalRewriteTree::new();
        tree.validate = true;
        let mut rules = vec![];
        tree.add_rule(0, &Term::parse("c1(x0, x0)"), &Term::parse("c2"));
        assert!(tree
            .rewrite(&Term::parse("c1(x0, c3)"), &mut rules)
            .is_none());
    }

    #[test]
    fn test_crt_function_variables() {
        let mut tree = CanonicalRewriteTree::new();
        tree.validate = true;
        let mut rules = vec![];
        tree.add_rule(0, &Term::parse("c1(x0, x1)"), &Term::parse("x0(x1)"));
        let term = tree
            .rewrite(&Term::parse("c1(c2(c3), c4)"), &mut rules)
            .unwrap();
        assert_eq!(rules, vec![0]);
        assert_eq!(term, Term::parse("c2(c3, c4)"));
    }
}
