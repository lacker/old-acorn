use std::collections::HashMap;

use crate::atom::AtomId;
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
        unimplemented!()
    }

    pub fn synthesize(&mut self, clause: &Clause) -> Vec<Clause> {
        unimplemented!("Synthesize from clause: {:?}", clause)
    }
}
