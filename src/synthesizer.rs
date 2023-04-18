use std::collections::{HashMap, HashSet};

use crate::atom::{Atom, AtomId};
use crate::term::{Clause, Literal, Term};
use crate::type_space::{TypeId, BOOL};

pub struct Synthesizer {
    // Map of var_type to the "var_type -> bool" type, for each argument we want to synthesize
    types: HashMap<TypeId, TypeId>,

    // The next synthetic proposition id to use
    next_id: AtomId,

    // Stores all literals we've already synthesized from
    history: HashSet<Literal>,
}

impl Synthesizer {
    pub fn new() -> Synthesizer {
        Synthesizer {
            types: HashMap::new(),
            next_id: 0,
            history: HashSet::new(),
        }
    }

    // Adds entries to types for any higher-order variables that are observed.
    pub fn observe(&mut self, clause: &Clause) {
        for lit in &clause.literals {
            if lit.is_boolean() && lit.is_higher_order() {
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
        self.history.insert(literal.negate());

        // Synthesize an atom like "p1" for the new var_type -> bool function
        let first_prop_atom = Atom::Synthetic(self.next_id);
        self.next_id += 1;

        // The free variable in our "definition", always "x0"
        let var_term = Term {
            term_type: var_type,
            head_type: var_type,
            head: Atom::Variable(0),
            args: vec![],
        };

        // p1(x3)
        let first_prop_term = Term {
            term_type: BOOL,
            head_type: prop_type,
            head: first_prop_atom,
            args: vec![var_term.clone()],
        };

        // We want to define:
        //   p1(x3) <-> abstract_literal
        // We can do this with two clauses.
        //   p1(x3) | !abstract_literal
        //   !p1(x3) | abstract_literal
        println!("defining {} <-> {}", first_prop_term, literal);
        answer.push(Clause::new(vec![
            Literal::positive(first_prop_term.clone()),
            literal.negate(),
        ]));
        answer.push(Clause::new(vec![
            Literal::negative(first_prop_term.clone()),
            literal,
        ]));

        // Now we want to define p2 = !p1
        let second_prop_atom = Atom::Synthetic(self.next_id);
        self.next_id += 1;

        // p2(x0)
        let second_prop_term = Term {
            term_type: BOOL,
            head_type: prop_type,
            head: second_prop_atom,
            args: vec![var_term],
        };

        // We want to define:
        //   p2(x0) <-> !p1(x0)
        // We can do this with two clauses.
        //   !p2(x0) | !p1(x0)
        //   p2(x0) | p1(x0)
        answer.push(Clause::new(vec![
            Literal::negative(second_prop_term.clone()),
            Literal::negative(first_prop_term.clone()),
        ]));
        answer.push(Clause::new(vec![
            Literal::positive(second_prop_term),
            Literal::positive(first_prop_term),
        ]));
    }

    // Synthesize some new functions that provide alternative ways of writing the given clause.
    pub fn synthesize(&mut self, clause: &Clause) -> Vec<Clause> {
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
        if num_quantifiers > 1 {
            // For now we don't synthesize when we need to abstract over any additional quantifiers
            return answer;
        }

        if let Some(var_type) = literal.var_type(0) {
            // We have a higher-order variable, so we can synthesize a function
            if let Some(prop_type) = self.types.get(&var_type) {
                self.synthesize_from_literal(literal.clone(), var_type, *prop_type, &mut answer);
            }
        } else {
            let mut typed_atoms = literal.typed_atoms();
            typed_atoms.sort();
            typed_atoms.dedup();

            // Try replacing each atom with a free variable
            for (var_type, atom) in typed_atoms {
                if let Some(prop_type) = self.types.get(&var_type) {
                    let abstract_literal = literal.replace_atom(&atom, &Atom::Variable(0));
                    self.synthesize_from_literal(
                        abstract_literal,
                        var_type,
                        *prop_type,
                        &mut answer,
                    );
                }
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
        let mut env = Environment::new();
        let mut norm = Normalizer::new();
        let mut synth = Synthesizer::new();

        env.add("type Thing: axiom");
        env.add("define t: Thing = axiom");
        env.add("axiom t_implies_all(q: Thing -> bool): q(t) -> forall(x: Thing, q(x))");
        env.add("theorem goal(x: Thing): x = t");

        let clauses = norm.normalize(env.get_value("t_implies_all").unwrap().clone());
        for clause in &clauses {
            synth.observe(clause);
        }

        let neg_goal_clauses = norm.normalize(env.get_value("goal").unwrap().clone().negate());
        assert_eq!(neg_goal_clauses.len(), 1);
        let synthesized = synth.synthesize(&neg_goal_clauses[0]);
        assert_eq!(synthesized.len(), 8);
        for clause in synthesized {
            norm.typespace.check_clause(&clause);
        }

        // Check that we won't re-synthesize
        let synthesized_again = synth.synthesize(&neg_goal_clauses[0]);
        assert_eq!(synthesized_again.len(), 0);
    }
}
