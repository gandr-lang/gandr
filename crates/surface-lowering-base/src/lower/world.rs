//! The record of a located form that the lowering's context holds.
//!
//! The classification reads a handle type, a hold and a migration into this
//! record. The mint sweep reads it back, and `gandr-surface-lowering` names it
//! at its old path.

use gandr_core_term::world::World;
use gandr_surface_syntax::NodeIndex;

use super::Block;

/// A located form or type, as the classification read it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each node names a child of the form; a migration's body reads
///   where the migration stands.
/// - executable: none — the plan holds no tree to resolve its nodes in.
///
/// # Adequacy
/// - hypothesis: L3 — a handle type, a hold and a migration each lower to the
///   core form they name.
/// - witness: `gandr-surface-lowering::lower::world::tests::the_located_forms_lower_to_their_world_forms`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Worlded
{
    /// `A at w`.
    At
    {
        /// The held type `A`.
        inner: NodeIndex,
        /// The world `w` names.
        world: World,
    },
    /// `hold v`.
    Hold
    {
        /// The value held.
        value: NodeIndex,
    },
    /// `migrate [w] { t }`.
    Migrate
    {
        /// The world `w` names.
        world: World,
        /// The block run there.
        body: Block,
    },
}
