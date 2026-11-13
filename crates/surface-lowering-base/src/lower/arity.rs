//! The records of the arity-shaped formers that the lowering's context holds.
//!
//! The classification reads a sub-record, an observation and a link of a type
//! over labels into these records. The mint sweep reads them back, and
//! `gandr-surface-lowering` names each one at its old path.

use gandr_kernel_term::FieldLabel;
use gandr_surface_syntax::NodeIndex;

/// How a sub-record projects one field of the value it selects from.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a stated projection carries the entry and the type over labels
///   the value's name is written with; a field carries nothing more.
/// - executable: none — the record holds no form to check against.
///
/// # Adequacy
/// - hypothesis: L3 — a sub-record of a stated record and of a record no type
///   states, each projecting every label it names.
/// - witness: `gandr-surface-lowering::lower::arity::tests::a_sub_record_binds_each_field_and_returns_their_record`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Projection
{
    /// The entry `Observed` names of the type over labels at the node, as a
    /// selection `p.l` off a name written with that type projects it.
    Stated(Observed, NodeIndex),
    /// The field at the label of a record no written type states, for the
    /// checker to read off the record type the value synthesises.
    Field,
}

/// One field a sub-record selects: its label and how it is projected.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the label as written and its projection.
/// - executable: none — the record holds no form to check against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Projection`].
/// - witness: `gandr-surface-lowering::lower::arity::tests::a_sub_record_binds_each_field_and_returns_their_record`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Selected
{
    /// The field's label.
    pub label: FieldLabel,
    /// How the field is projected.
    pub projection: Projection,
}

/// The entry an observation selects of a lazy record, or a selection of a
/// dependent record: its index among `count` entries.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `index < count` where the classification built it.
/// - executable: none — the classification checks the label it read.
///
/// # Adequacy
/// - hypothesis: L3 — the first, a middle and the last entry of a lazy record
///   of three each project their own component.
/// - witness: `gandr-surface-lowering::lower::arity::tests::an_observation_projects_its_entry`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Observed
{
    /// The selected entry's index.
    pub index: usize,
    /// How many entries the lazy record has.
    pub count: usize,
}

/// Whether a lookup reads through a thunk type `+U X` to the `X` it holds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Thunked(pub bool);

/// Whether a link of a type over labels binds: a later entry names the
/// link's label, so the link is a `Σ` and a split of it reads the match's
/// motive at its scrutinee.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Dependent(pub bool);
