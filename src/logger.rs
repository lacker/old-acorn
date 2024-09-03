use crate::project::BuildEvent;

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
}
