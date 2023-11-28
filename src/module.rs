// The code in one file is exposed to other Acorn code as a "module".
// You could have two different types both named "MyStruct" but defined in different places.
// Each name is uniquely identified not just by its string name, but also by the module it's defined in.
// When you look at the AcornType object, they should have each have a different ModuleId.
pub type ModuleId = u16;

// Some entities that are created for the prover get their own modules.
// Skolem functions are ones created to replace "exists" quantifiers.
pub const SKOLEM: ModuleId = 0;

// The regular module ids start here.
pub const FIRST_NORMAL: ModuleId = 1;
