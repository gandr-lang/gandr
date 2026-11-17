//! Contractive binary session types, one coinductive relation engine, and
//! search-free endpoint replay. Payload identities and digests stay opaque.
//!
//! The monitor checks conformance; it produces no kernel certificate. The
//! `certified` boundary exports candidate relations, moves recorded skeletons
//! forward along a simulation, and transports them through `Flow_U` only after
//! independent kernel replay.
//!
//! A recorded dialogue of both endpoints is admitted by its logical time
//! ([`admit`]): each endpoint's moves replay against its protocol, and the
//! recorded order is one linearization of the session's causal web, whose
//! green edges are each endpoint's own order and every send before its
//! receipt. A dialogue that records a receipt before its send is refused by
//! that edge.

#![no_std]

extern crate alloc;

pub mod certified;
mod dialogue;
mod relation;
mod replay;
mod session;

pub use crate::dialogue::DialogueRefusal;
pub use crate::dialogue::DialogueWeb;
pub use crate::dialogue::Event;
pub use crate::dialogue::Facing;
pub use crate::dialogue::Turn;
pub use crate::dialogue::admit;
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
