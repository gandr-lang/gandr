//! The records of the session types that the lowering's context holds.
//!
//! The classification reads every site where a protocol's state is written,
//! and each parameter at a session type that a body places, into these
//! records. The mint sweep reads them back, and `gandr-surface-lowering` names
//! each one at its old path.

use alloc::vec::Vec;

use gandr_core_term::session::ProtocolState;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;

use super::Frame;
use crate::form::Placed;

/// An offer's arm labels, each with the bytes its pattern is written at, in
/// source order (#298).
pub type ArmLabels = Vec<(ByteSpan, FieldLabel)>;

/// A place the source writes a protocol's state at.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `state` is a state of the protocol the site was read in.
/// - executable: none — the site holds no protocol to check its state against.
///
/// # Adequacy
/// - hypothesis: L3 — each continuation answers at its own state, and each
///   branch label and `mu` variable at the state it names.
/// - witness: `gandr-surface-lowering::lower::session::tests::each_state_answers_where_it_is_written`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StateSite
{
    /// Where the source writes it.
    pub at: Placed,
    /// The state written there.
    pub state: ProtocolState,
    /// Whether the site is the state's own form or a name for it.
    pub naming: Naming,
}

/// Whether a site writes a state or names one.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Naming
{
    /// The state's own form, a session type standing where it is written.
    Form,
    /// A branch's label or a `mu`'s variable, naming the state it continues
    /// with or binds.
    Label,
}

/// What a session type's mint needs beside its protocol: every site a state
/// is written at, and the frame its payloads are read under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: every site names a state of the protocol it is planned with.
/// - executable: none — the record holds no protocol.
///
/// # Adequacy
/// - hypothesis: L3 — as [`StateSite`].
/// - witness: `gandr-surface-lowering::lower::session::tests::each_state_answers_where_it_is_written`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Written
{
    /// The sites, in the order the walk read them.
    pub sites: Vec<StateSite>,
    /// The frame the protocol is read under.
    pub frame: Frame,
}

/// A function's parameter at a session type, placed in a linear binder of
/// its name at its body's entry.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `index` is the parameter's intuitionistic index past every
///   parameter and the function's own name.
/// - executable: none — the plan holds no scope.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter at `end` closed in its body.
/// - witness: `gandr-surface-lowering::lower::session::tests::a_parameter_at_a_session_type_is_placed_1862`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct PlacedEndpoint
{
    /// The parameter's binder tile, the placement's origin.
    pub binder: NodeIndex,
    /// The parameter's intuitionistic index past every parameter.
    pub index: DeBruijnIndex,
}
