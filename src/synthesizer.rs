use std::collections::HashMap;

use crate::atom::{Atom, AtomId};
use crate::term::Clause;
use crate::type_space::TypeId;

pub struct Synthesizer {
    // Map of var_type to a list of templates
    templates: HashMap<TypeId, Vec<Template>>,
}

struct Template {
    // The type of the free variable in the synthesized proposition.
    var_type: TypeId,

    // The type of the synthesized proposition variable itself.
    // Represents a function from var_type to bool.
    prop_type: TypeId,

    // The id of the free variable in the template that we will replace with our
    // synthesized proposition.
    prop_id: AtomId,

    // The clause that we will use as a template for synthesis.
    clause: Clause,
}

impl Synthesizer {
    pub fn new() -> Synthesizer {
        Synthesizer {
            templates: HashMap::new(),
        }
    }

    // Whether this clause can be expanded with synthesized propositions.
    pub fn is_template(clause: &Clause) -> bool {
        clause
            .literals
            .iter()
            .any(|lit| lit.is_boolean() && lit.is_higher_order())
    }

    pub fn add_template(&mut self, clause: Clause) {
        for lit in &clause.literals {
            if lit.is_boolean() && lit.is_higher_order() {
                let term = &lit.left;
                if term.args.len() != 1 {
                    // For now we only synthesize propositions with a single argument
                    continue;
                }
                let var_type = term.args[0].term_type;
                let prop_type = term.head_type;
                let prop_id = match term.head {
                    Atom::Variable(id) => id,
                    _ => continue,
                };
                let template = Template {
                    var_type,
                    prop_type,
                    prop_id,
                    clause,
                };
                self.templates
                    .entry(var_type)
                    .or_insert_with(Vec::new)
                    .push(template);
                return;
            }
        }
        panic!("clause could not be added as a template: {}", clause);
    }

    pub fn synthesize(&mut self, clause: &Clause) -> Vec<Clause> {
        let mut answer = Vec::new();
        if clause.literals.len() > 1 {
            // For now we only synthesize clauses with a single literal
            return answer;
        }
        let literal = &clause.literals[0];

        // TODO:
        // see what types we might want to template
        // for each type, find all the atoms
        // for each atom, make a lambda by replacing that atom with a free variable
        // for each lambda, synthesize enough props to define it

        unimplemented!("Synthesize from literal: {}", literal);
    }
}
