//! The elaborator seam of gandr's cell-rewriting stack: where a levitated
//! description's rules become command cells, and where a circuit rule's two
//! sequentializations are identified.
//!
//! [`elaborate_data_desc`] reads a whole description — its constructors,
//! operations, rule faces, circuit rules and η licence — into one cell store
//! at the declaration's polarity, admitting each cell through one seam that
//! refuses a copied hole and a hole worn at both polarities apart, and
//! reporting every declined member beside the store ([`DescElaboration`]).
//! [`elaborate_rule`] is the face-to-cell step on its own.
//!
//! [`instantiate_two_redex_rule`] applies a two-redex circuit rule: the
//! positions come from the body's occurrence record, the cells from the
//! caller's [`RewriteBinding`]s, the independence verdict from the shift guard,
//! and the convexity re-check a withheld discharge is owed from the caller's
//! [`ConvexitySupply`]. [`instantiate_cell`] instantiates one stored cell under
//! a substitution into the same store.
//!
//! The crate is `no_std` and depends on `core`, `alloc`, the cell substrate,
//! the rewriting engine, the shift guard, the description table and the shape
//! vocabulary of `quenchant-shape`; it re-exports none of their types, so a
//! dependent names each crate whose types it reads. The papers it draws on are
//! in its `README.md`, § References.

#![no_std]

extern crate alloc;

mod boundary;
mod elaborate;
mod instantiate;

pub use crate::boundary::ConstructorCount;
pub use crate::boundary::DeclinedFaceIndex;
pub use crate::boundary::DeclinedOpIndex;
pub use crate::boundary::OperationInputCount;
pub use crate::boundary::RedexOccurrenceCount;
pub use crate::elaborate::CircuitElaboration;
pub use crate::elaborate::DescElaboration;
pub use crate::elaborate::ElaborateError;
pub use crate::elaborate::EtaElaborateError;
pub use crate::elaborate::EtaElaboration;
pub use crate::elaborate::MixedPolarityHole;
pub use crate::elaborate::OpElaborateError;
pub use crate::elaborate::OpFrame;
pub use crate::elaborate::elaborate_data_desc;
pub use crate::elaborate::elaborate_rule;
pub use crate::instantiate::CellInstantiationError;
pub use crate::instantiate::CircuitShift;
pub use crate::instantiate::CircuitShiftObstruction;
pub use crate::instantiate::ConvexityGrant;
pub use crate::instantiate::ConvexitySupply;
pub use crate::instantiate::RewriteBinding;
pub use crate::instantiate::instantiate_cell;
pub use crate::instantiate::instantiate_two_redex_rule;
