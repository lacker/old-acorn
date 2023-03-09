use crate::acorn_type::{AcornType, FunctionType};
use crate::acorn_value::{AcornValue, Atom, Clause, FunctionApplication, Literal, TypedAtom};

pub struct Normalizer {
    // Types of the skolem functions produced
    skolem_types: Vec<FunctionType>,
}

impl Normalizer {
    pub fn new() -> Normalizer {
        Normalizer {
            skolem_types: vec![],
        }
    }

    // The input should already have negations moved inwards.
    // The stack must be entirely universal quantifiers.
    //
    // The value does *not* need to be in prenex normal form.
    // I.e., it can still have quantifier nodes, either "exists" or "forall", inside of
    // logical nodes, like "and" and "or".
    // All negations must be moved inside quantifiers, though.
    //
    // In general I think converting to prenex seems bad. Consider:
    //   forall(x, f(x)) & exists(y, g(y))
    // If we convert to prenex, we get:
    //   forall(x, exists(y, f(x) & g(y)))
    // which skolemizes to
    //   forall(x, f(x) & g(skolem(x)))
    // But there's a redundant arg here. The simpler form is just
    //   forall(x, f(x) & g(skolem()))
    // which is what we get if we don't convert to prenex first.
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
                        arg_types: stack.clone(),
                        return_type: Box::new(quant),
                    };
                    let skolem_index = self.skolem_types.len();
                    self.skolem_types.push(skolem_type.clone());
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

            AcornValue::And(left, right) => {
                let left = self.skolemize(stack, *left);
                let right = self.skolemize(stack, *right);
                AcornValue::And(Box::new(left), Box::new(right))
            }

            AcornValue::Or(left, right) => {
                let left = self.skolemize(stack, *left);
                let right = self.skolemize(stack, *right);
                AcornValue::Or(Box::new(left), Box::new(right))
            }

            // Acceptable terminal nodes for the skolemization algorithm
            AcornValue::Atom(_) => value,
            AcornValue::Application(_) => value,
            AcornValue::Not(_) => value,
            AcornValue::Equals(_, _) => value,
            AcornValue::NotEquals(_, _) => value,

            _ => panic!(
                "moving negation inwards should have eliminated this node: {:?}",
                value
            ),
        }
    }

    pub fn normalize(&mut self, value: AcornValue) -> Vec<Clause> {
        let expanded = value.expand_lambdas(0);
        let neg_in = expanded.move_negation_inwards(false);
        let skolemized = self.skolemize(&vec![], neg_in);
        let mut universal = vec![];
        let dequantified = skolemized.remove_forall(&mut universal);
        let mut literal_lists = vec![];
        Literal::into_cnf(dequantified, &mut literal_lists);

        let mut clauses = vec![];
        for literals in literal_lists {
            clauses.push(Clause {
                universal: universal.clone(),
                literals,
            });
        }
        clauses
    }
}
