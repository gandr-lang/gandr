//! The record of a capability scope that a model answers.
//!
//! The classification reads the model that answers a scope over a theory into
//! this record. The mint sweep reads it when it writes the scope's clauses.

use crate::lower::model::ModelSlot;
use crate::lower::model::Supplied;
use crate::origin::ScopeAnswer;

/// The model that answers a capability scope over a theory.
///
/// It holds the theory's slot without the sorts that the scope's manifest
/// fixes. It holds what the named module passes for the slot, or the holes
/// that the scope nominates for it. It also holds the answer as the scope
/// writes it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Answering
{
    /// The theory's slot.
    pub slot: ModelSlot,
    /// The module's members, or the scope's holes.
    pub supplied: Supplied,
    /// The module the scope names, or none.
    pub written: ScopeAnswer,
}
