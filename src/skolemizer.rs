#![allow(dead_code)]
use crate::acorn_type::{AcornType, FunctionType};
use crate::acorn_value::{AcornValue, Atom, FunctionApplication, TypedAtom};

pub struct Skolemizer {
    // Types of the skolem functions produced
    types: Vec<FunctionType>,
}

impl Skolemizer {
    pub fn new() -> Skolemizer {
        Skolemizer { types: vec![] }
    }

    // The input should already have negations moved inwards.
    // The stack must be entirely universal quantifiers.
    pub fn skolemize(&mut self, stack: &Vec<AcornType>, value: AcornValue) -> AcornValue {
        match value {
            AcornValue::ForAll(quants, subvalue) => {
                let mut new_stack = stack.clone();
                new_stack.extend(quants);
                self.skolemize(&new_stack, *subvalue)
            }
            AcornValue::Exists(quants, subvalue) => {
                // The current stack will be the arguments for the skolem functions
                let mut args = vec![];
                for (i, quant) in quants.iter().enumerate() {
                    args.push(AcornValue::Atom(TypedAtom {
                        atom: Atom::Reference(i),
                        acorn_type: quant.clone(),
                    }));
                }

                // Find a replacement for each of the quantifiers.
                // Each one will be a skolem function applied to the current stack.
                let mut replacements = vec![];
                for quant in quants {
                    let skolem_type = FunctionType {
                        args: stack.clone(),
                        return_type: Box::new(quant),
                    };
                    let skolem_index = self.types.len();
                    self.types.push(skolem_type.clone());
                    let function = AcornValue::Atom(TypedAtom {
                        atom: Atom::Skolem(skolem_index),
                        acorn_type: AcornType::Function(skolem_type),
                    });
                    let replacement = AcornValue::Application(FunctionApplication {
                        function: Box::new(function),
                        args: args.clone(),
                    });
                    replacements.push(replacement);
                }

                // Replace references to the existential quantifiers
                self.skolemize(stack, subvalue.bind_values(stack.len(), &replacements))
            }

            // Skolemization only affects top-level chains of "forall" and "exists" nodes.
            // We could do some validation here, but we don't.
            _ => value,
        }
    }
}
