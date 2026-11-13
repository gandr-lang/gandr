//! What an inert declaration's check reads: the declaration or the
//! component that a read resolved to.
//!
//! A declaration marked `@[ inert ]`, or a model's inert component, is read
//! only by another inert declaration. The lowering and the model family both
//! name the record, so it lives here, and `gandr-surface-lowering` names it at
//! its old path.

use crate::module::SlotIndex;
use crate::resolve::SurfaceName;

/// What a read resolved to, which `Families::inert_read` judges.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a declaration by its slot, or a component that its theory marks
///   inert, by its name.
/// - executable: none — the record holds no collection to check the slot
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::inert_read`.
/// - witness: `gandr-surface-lowering::tests::modules::models::an_inert_field_is_read_only_by_another_3029`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Read<'source>
{
    /// A declaration, by its slot.
    Slot(SlotIndex),
    /// A component its theory marks inert, selected off a model binder, by
    /// its name.
    Selected(SurfaceName<'source>),
}
