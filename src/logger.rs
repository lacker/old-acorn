use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity};

use crate::environment::Environment;
use crate::goal::GoalContext;
use crate::project::BuildStatus;
use crate::prover::{Outcome, Prover};
use crate::token::Error;

// The build process generates a number of build events
#[derive(Debug)]
pub struct BuildEvent {
    // Current progress is done / total.
    // This is across all modules.
    pub progress: Option<(i32, i32)>,

    // Human-readable
    pub log_message: Option<String>,

    // Whether this event is a slowness warning
    pub is_slow_warning: bool,

    // Whenever we run into a problem, report the module name, plus the diagnostic itself.
    pub diagnostic: Option<(String, Option<Diagnostic>)>,
}

impl BuildEvent {
    pub fn default() -> BuildEvent {
        BuildEvent {
            progress: None,
            log_message: None,
            is_slow_warning: false,
            diagnostic: None,
        }
    }
}

// The Logger collects information about what happens during a build.
// A single logger is used across all modules.
pub struct Logger<'a> {
    event_handler: Box<dyn FnMut(BuildEvent) + 'a>,

    pub status: BuildStatus,

    // The total number of goals to be verified.
    // Counted up during the loading phase.
    pub total: i32,

    // The number of goals for which the proof search finished.
    // This includes both successful and unsuccessful searches.
    pub done: i32,

    // When this flag is set, we emit warnings when we are slow, for some definition of "slow".
    pub warn_when_slow: bool,
}

impl<'a> Logger<'a> {
    pub fn new(event_handler: impl FnMut(BuildEvent) + 'a) -> Self {
        let event_handler = Box::new(event_handler);
        Logger {
            event_handler,
            status: BuildStatus::Good,
            total: 0,
            done: 0,
            warn_when_slow: false,
        }
    }

    pub fn handle_event(&mut self, event: BuildEvent) {
        (self.event_handler)(event);
    }

    // Called when a single module is loaded successfully.
    pub fn module_loaded(&mut self, env: &Environment) {
        self.total += env.iter_goals().count() as i32;
    }

    // Called when the entire loading phase is done.
    pub fn loading_phase_complete(&mut self) {
        self.handle_event(BuildEvent {
            progress: Some((0, self.total)),
            ..BuildEvent::default()
        });
    }

    // Called when a single proof search completes.
    // Returns the status for just this proof search.
    pub fn search_finished(
        &mut self,
        module: &str,
        goal_context: &GoalContext,
        prover: &Prover,
        outcome: Outcome,
        elapsed: f64,
    ) -> BuildStatus {
        self.done += 1;
        let elapsed_str = format!("{:.3}s", elapsed);

        match outcome {
            Outcome::Success => match prover.get_proof() {
                None => self.log_proving_warning(
                    module,
                    &goal_context,
                    &prover,
                    "had a missing proof",
                    false,
                ),
                Some(proof) => {
                    if proof.needs_simplification() {
                        self.log_proving_warning(
                            module,
                            &goal_context,
                            &prover,
                            "needs simplification",
                            false,
                        )
                    } else if self.warn_when_slow && elapsed > 0.1 {
                        self.log_proving_warning(
                            module,
                            &goal_context,
                            &prover,
                            &format!("took {}", elapsed_str),
                            true,
                        )
                    } else {
                        self.log_proving_success()
                    }
                }
            },
            Outcome::Exhausted => self.log_proving_warning(
                module,
                &goal_context,
                &prover,
                "could not be verified",
                false,
            ),
            Outcome::Inconsistent => self.log_proving_warning(
                module,
                &goal_context,
                &prover,
                "- prover found an inconsistency",
                false,
            ),
            Outcome::Timeout => self.log_proving_warning(
                module,
                &goal_context,
                &prover,
                &format!("timed out after {}", elapsed_str),
                false,
            ),
            Outcome::Interrupted => {
                self.log_proving_error(module, &goal_context, &prover, "was interrupted")
            }
            Outcome::Error => {
                self.log_proving_error(module, &goal_context, &prover, "had an error")
            }
            Outcome::Constrained => self.log_proving_warning(
                module,
                &goal_context,
                &prover,
                "stopped after hitting constraints",
                false,
            ),
        }
    }

    // Called when a module completes with no errors.
    pub fn module_verified(&mut self, module: &str) {
        self.handle_event(BuildEvent {
            diagnostic: Some((module.to_string(), None)),
            ..BuildEvent::default()
        });
    }

    // Logs an informational message that doesn't change build status.
    pub fn log_info(&mut self, message: String) {
        self.handle_event(BuildEvent {
            log_message: Some(message),
            ..BuildEvent::default()
        });
    }

    // Logs an error during the loading phase, that can be localized to a particular place.
    pub fn log_loading_error(&mut self, module: &str, error: &Error) {
        let diagnostic = Diagnostic {
            range: error.token.range(),
            severity: Some(DiagnosticSeverity::ERROR),
            message: error.to_string(),
            ..Diagnostic::default()
        };
        self.handle_event(BuildEvent {
            log_message: Some(format!("fatal error: {}", error)),
            diagnostic: Some((module.to_string(), Some(diagnostic))),
            ..BuildEvent::default()
        });
        self.status = BuildStatus::Error;
    }

    // Logs a successful proof.
    fn log_proving_success(&mut self) -> BuildStatus {
        self.handle_event(BuildEvent {
            progress: Some((self.done, self.total)),
            ..BuildEvent::default()
        });
        BuildStatus::Good
    }

    // Logs a warning. Warnings can only happen during the proving phase.
    fn log_proving_warning(
        &mut self,
        module: &str,
        goal_context: &GoalContext,
        prover: &Prover,
        message: &str,
        is_slow_warning: bool,
    ) -> BuildStatus {
        let mut full_message = format!("{} {}", goal_context.name, message);
        if let Some(e) = &prover.error {
            full_message.push_str(&format!(": {}", e));
        }
        let diagnostic = Diagnostic {
            range: goal_context.goal.range(),
            severity: Some(DiagnosticSeverity::WARNING),
            message: full_message.clone(),
            ..Diagnostic::default()
        };
        self.handle_event(BuildEvent {
            progress: Some((self.done, self.total)),
            log_message: Some(full_message),
            is_slow_warning,
            diagnostic: Some((module.to_string(), Some(diagnostic))),
        });
        self.status = self.status.combine(&BuildStatus::Warning);
        return BuildStatus::Warning;
    }

    // Logs an error during the proving phase.
    fn log_proving_error(
        &mut self,
        module: &str,
        goal_context: &GoalContext,
        prover: &Prover,
        message: &str,
    ) -> BuildStatus {
        let mut full_message = format!("{} {}", goal_context.name, message);
        if let Some(e) = &prover.error {
            full_message.push_str(&format!(": {}", e));
        }
        let diagnostic = Diagnostic {
            range: goal_context.goal.range(),
            severity: Some(DiagnosticSeverity::ERROR),
            message: full_message.clone(),
            ..Diagnostic::default()
        };
        // Set progress as complete, because an error will halt the build
        self.handle_event(BuildEvent {
            progress: Some((self.total, self.total)),
            log_message: Some(full_message),
            diagnostic: Some((module.to_string(), Some(diagnostic))),
            ..BuildEvent::default()
        });
        self.status = BuildStatus::Error;
        return BuildStatus::Error;
    }
}
