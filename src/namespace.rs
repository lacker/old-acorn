// Each file has its own namespace, and perhaps we'll add more later.
// You could have two different types both named "MyStruct" but defined in different places.
// When you look at the AcornType object, they should have each have a different NamespaceId.
pub type NamespaceId = u16;

// Some entities that are created for the prover get their own namespaces.
// Skolem functions are ones created to replace "exists" quantifiers.
pub const SKOLEM: NamespaceId = 0;

// Synthetic functions are created to assist in the proof search.
pub const SYNTHETIC: NamespaceId = 1;

// The regular namespaces start after the artificial ones.
pub const FIRST_NORMAL: NamespaceId = 2;
