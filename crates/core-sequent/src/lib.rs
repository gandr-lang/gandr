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
//! - [`Store`] is the machine's two-region store: the heap region of
//!   [`HeapValue`]s, memo cells and environment chains, and the walkable frame
//!   region of [`Frame`]s addressed by [`ContinuationMark`]s.
//!
//! The crate is `no_std` and depends on `core`, `alloc`, the core language's
//! syntax, the kernel's leaf vocabularies and the cell substrate's
//! [`Polarity`](gandr_theory_cell_complexes::Polarity). The design and the
//! papers it draws on are in its `README.md`.

#![no_std]

extern crate alloc;

mod boundary;
mod il;
mod store;

pub use crate::boundary::ConsumerArity;
pub use crate::boundary::FrameHeight;
pub use crate::boundary::FrameSerial;
pub use crate::boundary::NodeCount;
pub use crate::boundary::ProducerArity;
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
