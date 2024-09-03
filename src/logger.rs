use tower_lsp::lsp_types::Diagnostic;

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
}

impl<'a> Logger<'a> {
    pub fn new(event_handler: impl FnMut(BuildEvent) + 'a) -> Self {
        let event_handler = Box::new(event_handler);
        Logger { event_handler }
    }

    pub fn handle_event(&mut self, event: BuildEvent) {
        (self.event_handler)(event);
    }

    // Logs an informational message that doesn't change build status.
    pub fn log_info(&mut self, message: String) {
        self.handle_event(BuildEvent {
            log_message: Some(message),
            ..BuildEvent::default()
        });
    }
}
