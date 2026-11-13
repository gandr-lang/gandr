//! The record of a module that a block statement opens, which the lowering's
//! context holds.
//!
//! The block statement `import P ;` opens the module `P` over the rest of its
//! block. This record holds the module and the bytes it is open over, and
//! `gandr-surface-lowering` names it at its old path.

use gandr_surface_syntax::ByteSpan;

use crate::module::StructureIndex;

/// A module a block statement opens, and the bytes it is open over.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each value was read by `Lowerer::open`.
/// - executable: none — the carrier holds no collection to check the module
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::open`.
/// - witness: `gandr-surface-lowering::lower::opening::tests::an_opened_module_answers_the_rest_of_its_block`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Opened
{
    /// The bytes the module is open over: from the statement's `;` to the
    /// end of its block.
    pub scope: ByteSpan,
    /// The module.
    pub module: StructureIndex,
}
