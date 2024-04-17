use std::cmp::Ordering;
use std::fmt;

use crate::clause::Clause;
use crate::proposition::{Proposition, Source, SourceType};

// Use this to toggle experimental algorithm mode
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

// Information about a resolution inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolutionInfo {
    // Which clauses were used as the sources.
    // Resolution requires one positive and one negative clause.
    pub positive_id: usize,
    pub negative_id: usize,
}

// Information about a rewrite inference.
// Rewrites have two parts, the "pattern" that determines what gets rewritten into what,
// and the "target" which contains the subterm that gets rewritten.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteInfo {
    // Which clauses were used as the sources.
    pub pattern_id: usize,
    pub target_id: usize,

    // The truthiness of the source clauses.
    pattern_truthiness: Truthiness,
    target_truthiness: Truthiness,

    // An exact rewrite is when A = B, B ?= C, therefore A ?= C.
    // Inexact rewrites only operate on subterms.
    exact: bool,
}

// The rules that can generate new clauses, along with the clause ids used to generate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rule {
    Assumption(Source),

    // Rules based on multiple source clauses
    Resolution(ResolutionInfo),
    Rewrite(RewriteInfo),

    // Rules with only one source clause
    EqualityFactoring(usize),
    EqualityResolution(usize),
    FunctionElimination(usize),
}

impl Rule {
    // The ids of the clauses that this rule directly depends on.
    fn premises(&self) -> impl Iterator<Item = &usize> {
        match self {
            Rule::Assumption(_) => vec![].into_iter(),
            Rule::Resolution(info) => vec![&info.positive_id, &info.negative_id].into_iter(),
            Rule::Rewrite(info) => vec![&info.pattern_id, &info.target_id].into_iter(),
            Rule::EqualityFactoring(rewritten)
            | Rule::EqualityResolution(rewritten)
            | Rule::FunctionElimination(rewritten) => vec![rewritten].into_iter(),
        }
    }

    // (description, id) for every clause this rule directly depends on.
    pub fn descriptive_premises(&self) -> Vec<(String, usize)> {
        let mut answer = vec![];
        match self {
            Rule::Assumption(_) => {}
            Rule::Resolution(info) => {
                answer.push(("positive resolver".to_string(), info.positive_id));
                answer.push(("negative resolver".to_string(), info.negative_id));
            }
            Rule::Rewrite(info) => {
                answer.push(("pattern".to_string(), info.pattern_id));
                answer.push(("target".to_string(), info.target_id));
            }
            Rule::EqualityFactoring(source)
            | Rule::EqualityResolution(source)
            | Rule::FunctionElimination(source) => {
                answer.push(("source".to_string(), *source));
            }
        }
        answer
    }

    // Human-readable.
    pub fn name(&self) -> &str {
        match self {
            Rule::Assumption(_) => "Assumption",
            Rule::Resolution(_) => "Resolution",
            Rule::Rewrite(_) => "Rewrite",
            Rule::EqualityFactoring(_) => "Equality Factoring",
            Rule::EqualityResolution(_) => "Equality Resolution",
            Rule::FunctionElimination(_) => "Function Elimination",
        }
    }

    pub fn is_rewrite(&self) -> bool {
        match self {
            Rule::Rewrite(_) => true,
            _ => false,
        }
    }

    pub fn is_assumption(&self) -> bool {
        match self {
            Rule::Assumption(_) => true,
            _ => false,
        }
    }

    pub fn new_assumption(prop: &Proposition) -> Rule {
        Rule::Assumption(prop.source.clone())
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

    // Whether this proof step is considered "cheap".
    // Cheapness can be amortized. We don't want it to be possible to create an infinite
    // chain of cheap proof steps.
    // The idea is that in the future, we can consider more and more steps to be "cheap".
    // Any step that the AI considers to be "obvious", we can call it "cheap".
    cheap: bool,

    // The depth is the number of non-cheap steps it takes to reach this step.
    // A proof of depth 1 is "basic".
    // A proof of depth 0 is "trivial".
    depth: u32,

    // Cached for simplicity
    atom_count: u32,
}

pub type Score = (i32, i32);

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
        write!(f, "{} ; rule = {:?}", self.clause, self.rule)
    }
}

impl ProofStep {
    fn new(
        clause: Clause,
        truthiness: Truthiness,
        rule: Rule,
        simplification_rules: Vec<usize>,
        proof_size: u32,
        cheap: bool,
        depth: u32,
    ) -> ProofStep {
        let atom_count = clause.atom_count();
        ProofStep {
            clause,
            truthiness,
            rule,
            simplification_rules,
            proof_size,
            cheap,
            depth,
            atom_count,
        }
    }

    // Construct a new assumption ProofStep that is not dependent on any other steps.
    pub fn new_assumption(clause: Clause, truthiness: Truthiness, rule: Rule) -> ProofStep {
        ProofStep::new(clause, truthiness, rule, vec![], 0, true, 0)
    }

    // Construct a new ProofStep that is a direct implication of a single activated step,
    // not requiring any other clauses.
    pub fn new_direct(activated_step: &ProofStep, rule: Rule, clause: Clause) -> ProofStep {
        ProofStep::new(
            clause,
            activated_step.truthiness,
            rule,
            vec![],
            activated_step.proof_size + 1,
            true,
            activated_step.depth,
        )
    }

    // Construct a new ProofStep via resolution.
    pub fn new_resolution(
        positive_id: usize,
        positive_step: &ProofStep,
        negative_id: usize,
        negative_step: &ProofStep,
        clause: Clause,
    ) -> ProofStep {
        let rule = Rule::Resolution(ResolutionInfo {
            positive_id,
            negative_id,
        });

        // When the output of a resolution still has multiple literals, it can only be used
        // for further resolution steps, and these resolution chains are limited.
        // So we only need to consider a resolution to be expensive when its output is
        // a single literal.
        let cheap = clause.literals.len() > 1;
        let depth =
            std::cmp::max(positive_step.depth, negative_step.depth) + if cheap { 0 } else { 1 };

        ProofStep::new(
            clause,
            positive_step.truthiness.combine(negative_step.truthiness),
            rule,
            vec![],
            positive_step.proof_size + negative_step.proof_size + 1,
            cheap,
            depth,
        )
    }

    // Construct a new ProofStep via rewriting.
    pub fn new_rewrite(
        pattern_id: usize,
        pattern_step: &ProofStep,
        target_id: usize,
        target_step: &ProofStep,
        clause: Clause,
        exact: bool,
    ) -> ProofStep {
        let rule = Rule::Rewrite(RewriteInfo {
            pattern_id,
            target_id,
            pattern_truthiness: pattern_step.truthiness,
            target_truthiness: target_step.truthiness,
            exact,
        });

        // TODO: consider the reductive sort of rewrite to be cheap.
        let cheap = false;
        let depth =
            std::cmp::max(pattern_step.depth, target_step.depth) + if cheap { 0 } else { 1 };

        ProofStep::new(
            clause,
            pattern_step.truthiness.combine(target_step.truthiness),
            rule,
            vec![],
            pattern_step.proof_size + target_step.proof_size + 1,
            cheap,
            depth,
        )
    }

    // Create a replacement for this clause that has extra simplification rules
    // TODO: logically it seems like we should be updating depth.
    pub fn simplify(
        self,
        new_clause: Clause,
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
            new_clause,
            new_truthiness,
            self.rule,
            rules,
            self.proof_size,
            self.cheap,
            self.depth,
        )
    }

    // Construct a ProofStep with fake heuristic data for testing
    pub fn mock(s: &str) -> ProofStep {
        let clause = Clause::parse(s);
        ProofStep::new(
            clause,
            Truthiness::Factual,
            Rule::Assumption(Source::mock()),
            vec![],
            0,
            false,
            0,
        )
    }

    // The ids of the other clauses that this clause depends on.
    pub fn dependencies(&self) -> impl Iterator<Item = &usize> {
        self.rule.premises().chain(self.simplification_rules.iter())
    }

    pub fn depends_on(&self, id: usize) -> bool {
        self.dependencies().any(|i| *i == id)
    }

    // (description, id) for every clause this rule depends on.
    pub fn descriptive_dependencies(&self) -> Vec<(String, usize)> {
        let mut answer = self.rule.descriptive_premises();
        for rule in &self.simplification_rules {
            answer.push(("simplification".to_string(), *rule));
        }
        answer
    }

    // Whether this is the last step of the proof
    pub fn finishes_proof(&self) -> bool {
        self.clause.is_impossible()
    }

    // Whether this step is created by the normalization of the negated goal
    pub fn is_negated_goal(&self) -> bool {
        if let Rule::Assumption(source) = &self.rule {
            matches!(source.source_type, SourceType::NegatedGoal)
        } else {
            false
        }
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
    pub fn score(&self) -> Score {
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
                if let Rule::Assumption(_) = self.rule {
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
