use crate::project::BuildEvent;

// The Logger collects information about what happens during a build.
pub struct Logger {
    event_handler: Box<dyn FnMut(BuildEvent)>,
}

impl Logger {
    pub fn new(event_handler: Box<dyn FnMut(BuildEvent)>) -> Logger {
        Logger { event_handler }
    }

    pub fn handle_event(&mut self, event: BuildEvent) {
        (self.event_handler)(event);
    }
}
