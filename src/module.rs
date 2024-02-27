use crate::{environment::Environment, token};

// The code in one file is exposed to other Acorn code as a "module".
// You could have two different types both named "MyStruct" but defined in different places.
// Each name is uniquely identified not just by its string name, but also by the module it's defined in.
// When you look at the AcornType object, they should have each have a different ModuleId.
pub type ModuleId = u16;

// Some entities that are created for the prover get their own modules.
// Skolem functions are created during normalization to replace "exists" quantifiers.
pub const SKOLEM: ModuleId = 0;

// The regular module ids start here.
pub const FIRST_NORMAL: ModuleId = 1;

// The Module represents a module that can be in different states of being loaded.
pub enum Module {
    // There is no such module, not even an id for it
    None,

    // The module is in the process of being loaded.
    // Modules that fail on circular import will be in this state forever.
    Loading,

    // The module has been loaded, but there is an error in its code
    Error(token::Error),

    // The module has been loaded successfully and we have its environment
    Ok(Environment),
}
