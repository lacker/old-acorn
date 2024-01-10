use std::{cmp::Ordering, fmt};

use crate::clause::Clause;

// Use this to toggle experimental algorithm mode
// There is no current experiment.
pub const EXPERIMENT: bool = false;

// The "truthiness" categorizes the different types of true statements, relative to a proof.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Truthiness {
    // A "factual" truth is true globally, regardless of this particular proof.
    Factual,

    // A "hypothetical" truth is something that we are assuming true in the context of this proof.
    // For example, we might assume that a and b are nonzero, and then prove that a * b != 0.
    Hypothetical,

    // When we want to prove a goal G, we tell the prover that !G is true, and search
    // for contradictions.
    // A "counterfactual" truth is this negated goal, or something derived from it, that we expect
    // to lead to a contradiction.
    Counterfactual,
}

impl Truthiness {
    // When combining truthinesses, the result is the "most untruthy" of the two.
    pub fn combine(&self, other: Truthiness) -> Truthiness {
        match (self, other) {
            (Truthiness::Counterfactual, _) => Truthiness::Counterfactual,
            (_, Truthiness::Counterfactual) => Truthiness::Counterfactual,
            (Truthiness::Hypothetical, _) => Truthiness::Hypothetical,
            (_, Truthiness::Hypothetical) => Truthiness::Hypothetical,
            (Truthiness::Factual, Truthiness::Factual) => Truthiness::Factual,
        }
    }
}

// Information about a superposition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SuperpositionInfo {
    // Which clauses were used as the sources.
    paramodulator_id: usize,
    resolver_id: usize,

    // The truthiness of the source clauses.
    paramodulator_truthiness: Truthiness,
    resolver_truthiness: Truthiness,

    // How many literals were in the source clauses
    paramodulator_literals: usize,
    resolver_literals: usize,

    // Whether the sources are "rewrites" clauses - a single positive literal with strict kbo ordering.
    paramodulator_is_rewrite: bool,
    resolver_is_rewrite: bool,
}

// The rules that can generate new clauses, along with the clause ids used to generate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rule {
    Assumption,

    // (paramodulator, resolver)
    Superposition(SuperpositionInfo),

    // The equality rules only have one source clause
    EqualityFactoring(usize),
    EqualityResolution(usize),
}

impl Rule {
    // The ids of the clauses that this rule depends on.
    fn dependencies(&self) -> impl Iterator<Item = &usize> {
        match self {
            Rule::Assumption => vec![].into_iter(),
            Rule::Superposition(info) => {
                vec![&info.paramodulator_id, &info.resolver_id].into_iter()
            }
            Rule::EqualityFactoring(rewritten) => vec![rewritten].into_iter(),
            Rule::EqualityResolution(rewritten) => vec![rewritten].into_iter(),
        }
    }

    // (description, id) for every clause this rule depends on.
    pub fn descriptive_dependencies(&self) -> Vec<(String, usize)> {
        let mut answer = vec![];
        match self {
            Rule::Assumption => {}
            Rule::Superposition(info) => {
                answer.push(("paramodulator".to_string(), info.paramodulator_id));
                answer.push(("resolver".to_string(), info.resolver_id));
            }
            Rule::EqualityFactoring(source) => {
                answer.push(("source".to_string(), *source));
            }
            Rule::EqualityResolution(source) => {
                answer.push(("source".to_string(), *source));
            }
        }
        answer
    }

    pub fn name(&self) -> &str {
        match self {
            Rule::Assumption => "Assumption",
            Rule::Superposition(_) => "Superposition",
            Rule::EqualityFactoring(_) => "EqualityFactoring",
            Rule::EqualityResolution(_) => "EqualityResolution",
        }
    }

    pub fn is_superposition(&self) -> bool {
        match self {
            Rule::Superposition(_) => true,
            _ => false,
        }
    }
}

// A proof is made up of ProofSteps.
// Each ProofStep contains an output clause, plus a bunch of heuristic information about it, to
// decide if we should "activate" the proof step or not.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ProofStep {
    // The proof step is primarily defined by a clause that it proves.
    // Semantically, this clause is implied by the input clauses (activated and existing).
    pub clause: Clause,

    // Whether this clause is the normal sort of true, or just something we're hypothesizing for
    // the sake of the proof.
    pub truthiness: Truthiness,

    // How this clause was generated.
    pub rule: Rule,

    // Clauses that we used for additional simplification.
    pub simplification_rules: Vec<usize>,

    // The number of proof steps that this proof step depends on.
    // The size includes this proof step itself, but does not count assumptions and definitions.
    // So the size for any assumption or definition is zero.
    // This does not deduplicate among different branches, so it may be an overestimate.
    // This also ignores rewrites, which may or may not be the ideal behavior.
    proof_size: u32,

    // Cached for simplicity
    atom_count: u32,

    // The order in which this ProofStep was created.
    // This is different from the order in which the ProofStep was activated.
    generation_ordinal: usize,
}

impl Ord for ProofStep {
    // The heuristic used to decide which clause is the most promising.
    // The passive set is a "max heap", so we want the best clause to compare as the largest.
    fn cmp(&self, other: &ProofStep) -> Ordering {
        self.score().cmp(&other.score())
    }
}

impl PartialOrd for ProofStep {
    fn partial_cmp(&self, other: &ProofStep) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for ProofStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} atoms, {} proof size",
            self.atom_count, self.proof_size
        )
    }
}

impl ProofStep {
    fn new(
        clause: Clause,
        truthiness: Truthiness,
        rule: Rule,
        simplification_rules: Vec<usize>,
        proof_size: u32,
        generation_ordinal: usize,
    ) -> ProofStep {
        let atom_count = clause.atom_count();
        ProofStep {
            clause,
            truthiness,
            rule,
            simplification_rules,
            proof_size,
            atom_count,
            generation_ordinal,
        }
    }

    // Construct a ProofStep for an assumption that the prover starts with.
    pub fn new_assumption(
        clause: Clause,
        truthiness: Truthiness,
        generation_ordinal: usize,
    ) -> ProofStep {
        ProofStep::new(
            clause,
            truthiness,
            Rule::Assumption,
            vec![],
            0,
            generation_ordinal,
        )
    }

    // Construct a new ProofStep that is a direct implication of a single activated step,
    // not requiring any other clauses.
    pub fn new_direct(
        activated_step: &ProofStep,
        rule: Rule,
        clause: Clause,
        generation_ordinal: usize,
    ) -> ProofStep {
        ProofStep::new(
            clause,
            activated_step.truthiness,
            rule,
            vec![],
            activated_step.proof_size + 1,
            generation_ordinal,
        )
    }

    // Construct a new ProofStep via superposition.
    pub fn new_superposition(
        paramodulator_id: usize,
        paramodulator_step: &ProofStep,
        resolver_id: usize,
        resolver_step: &ProofStep,
        clause: Clause,
        generation_ordinal: usize,
    ) -> ProofStep {
        let rule = Rule::Superposition(SuperpositionInfo {
            paramodulator_id,
            resolver_id,
            paramodulator_truthiness: paramodulator_step.truthiness,
            resolver_truthiness: resolver_step.truthiness,
            paramodulator_literals: paramodulator_step.clause.len(),
            resolver_literals: resolver_step.clause.len(),
            paramodulator_is_rewrite: paramodulator_step.clause.is_rewrite_rule(),
            resolver_is_rewrite: resolver_step.clause.is_rewrite_rule(),
        });
        ProofStep::new(
            clause,
            paramodulator_step
                .truthiness
                .combine(resolver_step.truthiness),
            rule,
            vec![],
            paramodulator_step.proof_size + resolver_step.proof_size + 1,
            generation_ordinal,
        )
    }

    // Create a replacement for this clause that has extra simplification rules
    pub fn simplify(
        self,
        clause: Clause,
        new_rules: Vec<usize>,
        new_truthiness: Truthiness,
    ) -> ProofStep {
        let rules = self
            .simplification_rules
            .iter()
            .chain(new_rules.iter())
            .cloned()
            .collect();
        ProofStep::new(
            clause,
            new_truthiness,
            self.rule,
            rules,
            self.proof_size,
            self.generation_ordinal,
        )
    }

    // Construct a ProofStep with fake heuristic data for testing
    pub fn mock(s: &str) -> ProofStep {
        let clause = Clause::parse(s);

        ProofStep::new_assumption(clause, Truthiness::Factual, 0)
    }

    // The ids of the other clauses that this clause depends on.
    pub fn dependencies(&self) -> impl Iterator<Item = &usize> {
        self.rule
            .dependencies()
            .chain(self.simplification_rules.iter())
    }

    // (description, id) for every clause this rule depends on.
    pub fn descriptive_dependencies(&self) -> Vec<(String, usize)> {
        let mut answer = self.rule.descriptive_dependencies();
        for rule in &self.simplification_rules {
            answer.push(("simplification".to_string(), *rule));
        }
        answer
    }

    // Whether this is the last step of the proof
    pub fn finishes_proof(&self) -> bool {
        self.clause.is_impossible()
    }

    // Whether this step is just the direct normalization of the negated goal
    pub fn is_negated_goal(&self) -> bool {
        self.rule == Rule::Assumption && self.truthiness == Truthiness::Counterfactual
    }

    // The better the score, the more we want to activate this proof step.
    // The first element of the score is the deterministic ordering:
    //
    //   Global facts, both explicit and deductions
    //   The negated goal
    //   Explicit hypotheses
    //   Local deductions
    //
    // The second element of the score is heuristic. Any value should work there.
    pub fn score(&self) -> (i32, i32) {
        // Higher = more important, for the deterministic tier.
        let deterministic_tier = match self.truthiness {
            Truthiness::Counterfactual => {
                if self.is_negated_goal() {
                    3
                } else {
                    1
                }
            }
            Truthiness::Hypothetical => {
                if self.rule == Rule::Assumption {
                    2
                } else {
                    1
                }
            }
            Truthiness::Factual => 4,
        };

        let mut heuristic = 0;
        heuristic -= self.atom_count as i32;
        heuristic -= 2 * self.proof_size as i32;
        if self.truthiness == Truthiness::Hypothetical {
            heuristic -= 3;
        }

        return (deterministic_tier, heuristic);
    }

    // We have to strictly limit deduction that happens between two library facts, because
    // the plan is for the library to grow very large.
    pub fn automatic_reject(&self) -> bool {
        if self.truthiness == Truthiness::Factual && self.proof_size > 2 {
            // Only do one step of deduction with global facts.
            return true;
        }

        false
    }
}
