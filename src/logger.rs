use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity};

use crate::environment::Environment;
use crate::project::BuildStatus;
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
}

impl<'a> Logger<'a> {
    pub fn new(event_handler: impl FnMut(BuildEvent) + 'a) -> Self {
        let event_handler = Box::new(event_handler);
        Logger {
            event_handler,
            status: BuildStatus::Good,
            total: 0,
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

    // Logs an informational message that doesn't change build status.
    pub fn log_info(&mut self, message: String) {
        self.handle_event(BuildEvent {
            log_message: Some(message),
            ..BuildEvent::default()
        });
    }

    // Logs an error that can be localized to a particular place.
    // This sort of error is fatal to the build.
    pub fn log_error(&mut self, module: &str, error: &Error) {
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
}
