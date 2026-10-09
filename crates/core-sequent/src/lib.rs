//! The sequent tier of gandr's core: the command IL a call-by-push-value
//! program is focused into, and the store the abstract machine that runs it
//! works over.
//!
//! - [`CommandArena`] holds producers, consumers and commands —
//!   [`ProducerNode`], [`ConsumerNode`], [`CommandNode`] — minted only over
//!   children it holds, with [`SequentWatermark`] and
//!   [`CommandArena::truncate_to`] the rollback a refused build takes.
//!   Covariables are de Bruijn indices ([`CovariableIndex`]); nothing mints a
//!   continuation name.
//! - [`focus_computation`], [`focus_value`] and [`focus_top_value`] translate
//!   core terms into the IL, recording each created command's [`FocusOrigin`]
//!   in a [`Provenance`] table; [`unfocus_command`] and [`unfocus_value`] read
//!   the IL back, their left inverse.
//! - [`check_command`] is the typed-IL check: reference integrity, arity, focus
//!   and polarity, answering a command's [`FreeSet`].
//! - [`render_command`], [`render_producer`] and [`render_consumer`] write the
//!   IL's notation.
//! - [`Store`] is the machine's two-region store: the heap region of
//!   [`HeapValue`]s, memo cells and environment chains, and the walkable frame
//!   region of [`Frame`]s addressed by [`ContinuationMark`]s.
//! - [`Machine`] runs a command over the store, unfolding constants from
//!   [`Definitions`], to an [`Outcome`] within a [`StepCount`] budget, and
//!   reads a halted value back as a core term.
//! - [`stats`], [`origin_histogram`] and [`dump`] inspect a focused arena.
//! - [`reify_command`] reifies a ground cell pattern into the IL over a
//!   [`ConstructorResolver`].
//!
//! The crate is `no_std` and depends on `core`, `alloc`, the core language's
//! syntax, the kernel's leaf vocabularies and the cell substrate's
//! [`Polarity`](gandr_theory_cell_complexes::Polarity). The design and the
//! papers it draws on are in its `README.md`.

#![no_std]

extern crate alloc;

mod boundary;
mod bridge;
mod check;
mod focus;
mod il;
mod inspect;
mod machine;
mod pretty;
mod readback;
mod store;
mod unfocus;

pub use crate::boundary::ConsumerArity;
pub use crate::boundary::FrameHeight;
pub use crate::boundary::FrameSerial;
pub use crate::boundary::NodeCount;
pub use crate::boundary::ProducerArity;
pub use crate::boundary::StepCount;
pub use crate::bridge::ConstructorResolver;
pub use crate::bridge::ReifyRefusal;
pub use crate::bridge::reify_command;
pub use crate::check::ArityHead;
pub use crate::check::CheckRefusal;
pub use crate::check::FreeSet;
pub use crate::check::check_command;
pub use crate::focus::FocusOrigin;
pub use crate::focus::FocusRefusal;
pub use crate::focus::Provenance;
pub use crate::focus::focus_computation;
pub use crate::focus::focus_top_value;
pub use crate::focus::focus_value;
pub use crate::il::CommandArena;
pub use crate::il::CommandId;
pub use crate::il::CommandNode;
pub use crate::il::ConstructorTag;
pub use crate::il::ConsumerId;
pub use crate::il::ConsumerNode;
pub use crate::il::CopatternArm;
pub use crate::il::CovariableIndex;
pub use crate::il::DestructorTag;
pub use crate::il::MintRefusal;
pub use crate::il::NodeFamily;
pub use crate::il::PatternArm;
pub use crate::il::ProducerId;
pub use crate::il::ProducerNode;
pub use crate::il::SequentWatermark;
pub use crate::inspect::Stats;
pub use crate::inspect::dump;
pub use crate::inspect::origin_histogram;
pub use crate::inspect::stats;
pub use crate::machine::Definition;
pub use crate::machine::Definitions;
pub use crate::machine::Machine;
pub use crate::machine::MachineFault;
pub use crate::machine::Outcome;
pub use crate::machine::Stuck;
pub use crate::pretty::render_command;
pub use crate::pretty::render_consumer;
pub use crate::pretty::render_producer;
pub use crate::readback::ReadbackRefusal;
pub use crate::store::CellId;
pub use crate::store::ContinuationMark;
pub use crate::store::CovalueBindingId;
pub use crate::store::CovalueScope;
pub use crate::store::Environment;
pub use crate::store::ForceEntry;
pub use crate::store::Frame;
pub use crate::store::HeapFamily;
pub use crate::store::HeapValue;
pub use crate::store::HeapValueId;
pub use crate::store::MemoState;
pub use crate::store::Store;
pub use crate::store::StoreFault;
pub use crate::store::ValueBindingId;
pub use crate::store::ValueScope;
pub use crate::unfocus::UnfocusRefusal;
pub use crate::unfocus::unfocus_command;
pub use crate::unfocus::unfocus_value;
