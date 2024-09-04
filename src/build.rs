use std::time::Duration;

use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity};

use crate::environment::Environment;
use crate::goal::GoalContext;
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

    // Whenever we run into a problem, report the module name, plus the diagnostic itself.
    pub diagnostic: Option<(String, Option<Diagnostic>)>,
}

impl BuildEvent {
    fn default() -> BuildEvent {
        BuildEvent {
            progress: None,
            log_message: None,
            diagnostic: None,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum BuildStatus {
    // No problems of any kind
    Good,

    // Warnings indicate code that parses okay but can't be verified
    Warning,

    // Errors indicate either the user entered bad code, or we ran into a bug in the build process
    Error,
}

impl BuildStatus {
    pub fn verb(&self) -> &str {
        match self {
            BuildStatus::Good => "succeeded",
            BuildStatus::Warning => "warned",
            BuildStatus::Error => "errored",
        }
    }

    pub fn warn(&mut self) {
        if *self == BuildStatus::Good {
            *self = BuildStatus::Warning;
        }
    }

    pub fn is_error(&self) -> bool {
        match self {
            BuildStatus::Error => true,
            _ => false,
        }
    }

    pub fn is_good(&self) -> bool {
        match self {
            BuildStatus::Good => true,
            _ => false,
        }
    }
}

// The Builder exists to manage a single build.
// A single Project can correspond to many builds.
// A single logger is used across all modules.
pub struct Builder<'a> {
    event_handler: Box<dyn FnMut(BuildEvent) + 'a>,

    pub status: BuildStatus,

    // The total number of goals to be verified.
    // Counted up during the loading phase.
    pub total: i32,

    // The number of goals for which the proof search finished.
    // This includes both successful and unsuccessful searches.
    pub done: i32,

    // When this flag is set, we emit build events when a goal is slow.
    pub log_when_slow: bool,

    // The current module we are proving. Not set when we are loading.
    current_module: Option<String>,

    // Whether the current module is good so far.
    current_module_good: bool,
}

impl<'a> Builder<'a> {
    pub fn new(event_handler: impl FnMut(BuildEvent) + 'a) -> Self {
        let event_handler = Box::new(event_handler);
        Builder {
            event_handler,
            status: BuildStatus::Good,
            total: 0,
            done: 0,
            log_when_slow: false,
            current_module: None,
            current_module_good: true,
        }
    }

    fn module(&self) -> &str {
        match self.current_module {
            None => "<no module>",
            Some(ref s) => s,
        }
    }

    // Called when a single module is loaded successfully.
    pub fn module_loaded(&mut self, env: &Environment) {
        self.total += env.iter_goals().count() as i32;
    }

    // Called when the entire loading phase is done.
    pub fn loading_phase_complete(&mut self) {
        (self.event_handler)(BuildEvent {
            progress: Some((0, self.total)),
            ..BuildEvent::default()
        });
    }

    // Logs an informational message that doesn't change build status.
    pub fn log_info(&mut self, message: String) {
        (self.event_handler)(BuildEvent {
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
        (self.event_handler)(BuildEvent {
            log_message: Some(format!("fatal error: {}", error)),
            diagnostic: Some((module.to_string(), Some(diagnostic))),
            ..BuildEvent::default()
        });
        self.status = BuildStatus::Error;
    }

    // Called when we start proving a module.
    pub fn module_proving_started(&mut self, module: &str) {
        self.current_module = Some(module.to_string());
        self.current_module_good = true;
    }

    pub fn module_proving_complete(&mut self, module: &str) {
        assert_eq!(self.module(), module);
        if self.current_module_good {
            // Send a no-problems diagnostic, so that the IDE knows to clear squiggles.
            (self.event_handler)(BuildEvent {
                diagnostic: Some((module.to_string(), None)),
                ..BuildEvent::default()
            });
        }
        self.current_module = None;
    }

    // Called when a single proof search completes.
    pub fn search_finished(
        &mut self,
        prover: &Prover,
        goal_context: &GoalContext,
        outcome: Outcome,
        elapsed: Duration,
    ) {
        self.done += 1;

        // Standard messing around with times
        let secs = elapsed.as_secs() as f64;
        let subsec_nanos = elapsed.subsec_nanos() as f64;
        let elapsed_f64 = secs + subsec_nanos * 1e-9;
        let elapsed_str = format!("{:.3}s", elapsed_f64);

        match outcome {
            Outcome::Success => match prover.get_proof() {
                None => self.log_proving_warning(&prover, &goal_context, "had a missing proof"),
                Some(proof) => {
                    if proof.needs_simplification() {
                        self.log_proving_warning(&prover, &goal_context, "needs simplification");
                    } else if self.log_when_slow && elapsed_f64 > 0.1 {
                        self.log_proving_info(
                            &prover,
                            &goal_context,
                            &format!("took {}", elapsed_str),
                        );
                    } else {
                        self.log_proving_success();
                    }
                }
            },
            Outcome::Exhausted => {
                self.log_proving_warning(&prover, &goal_context, "could not be verified")
            }
            Outcome::Inconsistent => {
                self.log_proving_warning(&prover, &goal_context, "- prover found an inconsistency")
            }
            Outcome::Timeout => self.log_proving_warning(
                &prover,
                &goal_context,
                &format!("timed out after {}", elapsed_str),
            ),
            Outcome::Interrupted => {
                self.log_proving_error(&prover, &goal_context, "was interrupted");
            }
            Outcome::Error => {
                self.log_proving_error(&prover, &goal_context, "had an error");
            }
            Outcome::Constrained => self.log_proving_warning(
                &prover,
                &goal_context,
                "stopped after hitting constraints",
            ),
        }
    }

    // Logs a successful proof.
    fn log_proving_success(&mut self) {
        (self.event_handler)(BuildEvent {
            progress: Some((self.done, self.total)),
            ..BuildEvent::default()
        });
    }

    // Create a build event for a proof that was other than successful.
    fn make_event(
        &mut self,
        prover: &Prover,
        goal_context: &GoalContext,
        message: &str,
        sev: DiagnosticSeverity,
    ) -> BuildEvent {
        let module = self.module().to_string();
        let mut full_message = format!("{} {}", goal_context.name, message);
        if let Some(e) = &prover.error {
            full_message.push_str(&format!(": {}", e));
        }
        let diagnostic = Diagnostic {
            range: goal_context.goal.range(),
            severity: Some(sev),
            message: full_message.clone(),
            ..Diagnostic::default()
        };
        BuildEvent {
            progress: Some((self.done, self.total)),
            log_message: Some(full_message),
            diagnostic: Some((module, Some(diagnostic))),
        }
    }

    fn log_proving_info(&mut self, prover: &Prover, goal_context: &GoalContext, message: &str) {
        let event = self.make_event(
            prover,
            goal_context,
            message,
            DiagnosticSeverity::INFORMATION,
        );
        (self.event_handler)(event);
    }

    // Logs a warning. Warnings can only happen during the proving phase.
    fn log_proving_warning(&mut self, prover: &Prover, goal_context: &GoalContext, message: &str) {
        let event = self.make_event(prover, goal_context, message, DiagnosticSeverity::WARNING);
        (self.event_handler)(event);
        self.current_module_good = false;
        self.status.warn();
    }

    // Logs an error during the proving phase.
    fn log_proving_error(&mut self, prover: &Prover, goal_context: &GoalContext, message: &str) {
        let mut event = self.make_event(prover, goal_context, message, DiagnosticSeverity::WARNING);

        // Set progress as complete, because an error will halt the build
        event.progress = Some((self.total, self.total));
        (self.event_handler)(event);
        self.current_module_good = false;
        self.status = BuildStatus::Error;
    }
}
