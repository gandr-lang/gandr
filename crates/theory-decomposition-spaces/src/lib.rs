//! Certificate algebra: sequential composition and bounded backward pathway
//! queries.
//!
//! The directed gate reads recorded cell support at the left certificate's
//! join. Its verdict is presentation-sensitive; an admitted graft preserves the
//! replay boundary. Pathway acceptance is relative to the shift guard.

#![no_std]

extern crate alloc;

mod boundary;
pub mod compose;
pub mod pathway;

pub use crate::boundary::PathwayCandidateBudget;
pub use crate::boundary::PathwayCandidateCount;
pub use crate::boundary::PathwayLength;
pub use crate::boundary::PathwayLengthBudget;
pub use crate::boundary::TargetEventCount;
pub use crate::compose::CompositionObstruction;
pub use crate::compose::compose_directed;
pub use crate::compose::compose_invertible;
