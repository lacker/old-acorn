// Each file has its own namespace, and perhaps we'll add more later.
// You could have two different types both named "MyStruct" but defined in different places.
// When you look at the AcornType object, they should have each have a different NamespaceId.
pub type NamespaceId = u16;

// Intermediate entities created by the normalizer exist in the synthetic namespace.
// This includes skolemized variables and synthetic propositions.
pub const SYNTHETIC: NamespaceId = 0;
