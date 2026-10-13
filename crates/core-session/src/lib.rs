//! Contractive binary session types, one coinductive relation engine, and
//! search-free endpoint replay. Payload identities and digests stay opaque.
//!
//! The monitor checks conformance; it produces no kernel certificate. The
//! `certified` boundary exports candidate relations, moves recorded skeletons
//! forward along a simulation, and transports them through `Flow_U` only after
//! independent kernel replay.

#![no_std]

extern crate alloc;

pub mod certified;
mod relation;
mod replay;
mod session;

pub use crate::relation::Decision;
pub use crate::relation::Relation;
pub use crate::relation::RelationResult;
pub use crate::relation::decide;
pub use crate::relation::duality;
pub use crate::relation::relate;
pub use crate::relation::relate_states;
pub use crate::replay::Completion;
pub use crate::replay::Move;
pub use crate::replay::MoveIndex;
pub use crate::replay::Payload;
pub use crate::replay::PayloadDigest;
pub use crate::replay::Refusal;
pub use crate::replay::ReplayError;
pub use crate::replay::replay;
pub use crate::session::Action;
pub use crate::session::Label;
pub use crate::session::Node;
pub use crate::session::NodeId;
pub use crate::session::Session;
pub use crate::session::TypeError;
pub use crate::session::ValueTypeId;
