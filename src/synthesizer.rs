use std::collections::{HashMap, HashSet};

use crate::atom::{Atom, AtomId};
use crate::clause::Clause;
use crate::literal::Literal;
use crate::normalizer::Normalizer;
use crate::term::Term;
use crate::type_map::{TypeId, BOOL};

pub struct Synthesizer {
    // Map of var_type to the "var_type -> bool" type, for each argument we want to synthesize
    types: HashMap<TypeId, TypeId>,

    // Stores all literals we've already synthesized from
    definitions: Vec<Literal>,
    history: HashSet<Literal>,
}

impl Synthesizer {
    pub fn new() -> Synthesizer {
        Synthesizer {
            types: HashMap::new(),
            history: HashSet::new(),
            definitions: Vec::new(),
        }
    }

    // Adds entries to types for any higher-order variables that are observed.
    pub fn observe_types(&mut self, clause: &Clause) {
        for lit in &clause.literals {
            if lit.is_boolean() && lit.positive && lit.is_higher_order() {
                let term = &lit.left;
                if term.args.len() != 1 {
                    // For now we only synthesize propositions with a single argument
                    continue;
                }
                let var_type = term.args[0].term_type;
                let prop_type = term.head_type;
                if !self.types.contains_key(&var_type) {
                    self.types.insert(var_type, prop_type);
                }
            }
        }
    }

    // literal should have precisely one free variable, with id 0
    // var_type is the type of that free variable
    // prop_type is (var_type -> bool)
    fn synthesize_from_literal(
        &mut self,
        literal: Literal,
        var_type: TypeId,
        prop_type: TypeId,
        answer: &mut Vec<Clause>,
    ) {
        // Skip synthesizing if we already synthesized an equivalent function
        if self.history.contains(&literal) {
            return;
        }
        self.history.insert(literal.clone());

        // Synthesize an atom which in the comments we will call "p" for the new
        // var_type -> bool function.
        // In practice it will have some id, like p3 or p7.
        // p will be defined as !literal, so that p(_) can unify with a x0(x1) term.
        let prop_atom = Atom::Synthetic(self.definitions.len() as AtomId);
        self.definitions.push(literal.negate());

        // The free variable in our "definition", always "x0"
        let var_term = Term {
            term_type: var_type,
            head_type: var_type,
            head: Atom::Variable(0),
            args: vec![],
        };

        // p(x0)
        let prop_term = Term {
            term_type: BOOL,
            head_type: prop_type,
            head: prop_atom,
            args: vec![var_term.clone()],
        };

        // We want to define:
        //   p(x0) <-> !literal
        // We can do this with two clauses.
        //   p(x0) | literal
        //   !p(x0) | !literal
        // println!("defining {} <-> {}", prop_term, literal);
        answer.push(Clause::new(vec![
            Literal::negative(prop_term.clone()),
            literal.negate(),
        ]));
        answer.push(Clause::new(vec![Literal::positive(prop_term), literal]));
    }

    pub fn get_definition(&self, atom_id: AtomId) -> Option<&Literal> {
        self.definitions.get(atom_id as usize)
    }

    // Synthesize some new functions that provide alternative ways of writing the given clause.
    // This is really heuristically restricted right now - we only allow synthesis by abstracting over
    // a skolem variable, which basically means we can only find a particular sort of induction.
    pub fn synthesize(&mut self, normalizer: &Normalizer, clause: &Clause) -> Vec<Clause> {
        let mut answer = Vec::new();
        if clause.literals.len() > 1 {
            // For now we only synthesize clauses with a single literal
            return answer;
        }
        let literal = &clause.literals[0];
        if literal.has_synthetic() {
            // For now we only synthesize clauses with no synthetic atoms
            return answer;
        }
        let num_quantifiers = literal.num_quantifiers();
        if num_quantifiers > 0 {
            // For now we just don't synthesize for propositions that already have quantifiers.
            // This really seems like a hack, focused on proving things by induction.
            return answer;
        }

        let mut typed_atoms = literal.typed_atoms();
        typed_atoms.sort();
        typed_atoms.dedup();

        // Try replacing each atom with a free variable
        for (var_type, atom) in typed_atoms {
            if !normalizer.is_skolem(&atom) {
                continue;
            }
            if let Some(prop_type) = self.types.get(&var_type) {
                let abstract_literal = literal.replace_atom(&atom, &Atom::Variable(0));
                self.synthesize_from_literal(abstract_literal, var_type, *prop_type, &mut answer);
            }
        }

        answer
    }
}

#[cfg(test)]
mod tests {
    use crate::environment::Environment;
    use crate::normalizer::Normalizer;

    use super::*;

    #[test]
    fn test_synthesis() {
        let mut env = Environment::new_test();
        let mut norm = Normalizer::new();
        let mut synth = Synthesizer::new();

        env.add("type Thing: axiom");
        env.add("let t: Thing = axiom");
        env.add("axiom t_implies_all(q: Thing -> bool): q(t) -> forall(x: Thing) { q(x) }");
        env.add("theorem goal(x: Thing): x = t");

        let clauses = norm
            .normalize(env.get_theorem_claim("t_implies_all").unwrap())
            .unwrap()
            .unwrap();
        for clause in &clauses {
            synth.observe_types(clause);
        }

        let neg_goal_clauses = norm
            .normalize(env.get_theorem_claim("goal").unwrap().negate())
            .unwrap()
            .unwrap();
        assert_eq!(neg_goal_clauses.len(), 1);
        let synthesized = synth.synthesize(&norm, &neg_goal_clauses[0]);
        assert_eq!(synthesized.len(), 2);
        for clause in synthesized {
            norm.type_map.check_clause(&clause);
        }

        // Check that we won't re-synthesize
        let synthesized_again = synth.synthesize(&norm, &neg_goal_clauses[0]);
        assert_eq!(synthesized_again.len(), 0);
    }
}
