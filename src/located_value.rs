use tower_lsp::lsp_types::Range;

use crate::{acorn_value::AcornValue, module::ModuleId};

// A value along with information on where to find it in the source.
pub struct LocatedValue {
    pub value: AcornValue,

    // The module where this value was defined
    pub module: ModuleId,

    // The range in the source document that corresponds to the value's definition
    pub range: Range,

    // Only set when this value is a named theorem
    pub theorem_name: Option<String>,
}
