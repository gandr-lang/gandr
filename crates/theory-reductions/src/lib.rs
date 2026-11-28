//! Reductions of one complex onto another: the interface that a collapse, a
//! cover and a block of rules state, and that a reader replays.
//!
//! A [`Reduction`] gives a collapse `φ` from its source to its target, an
//! inclusion `ι` back, a section from each source composite to `ι ∘ φ` of it,
//! and a retraction from `φ ∘ ι` of each target composite back to it. Its
//! replay checks each of them and names each [`Refusal`]. [`Then`] sets two
//! reductions in sequence, and a [`Sum`] sets reductions of one type side by
//! side. Each is a reduction again, so a reader replays one value.
//!
//! The crate holds no search. A matching, a strategy of rules or a cover
//! derivation finds a reduction elsewhere and states it here.
//!
//! # Items
//!
//! | Item | What it holds |
//! | ---- | ------------- |
//! | [`Reduction`], [`Then`], [`Answer`] | a reduction: the collapse, the inclusion, both inverse witnesses and the replay, two reductions in sequence, and what a step gives |
//! | [`Sum`], [`Summand`], [`PartIndex`], [`SumFault`] | reductions of one type side by side as one reduction, a value of one part with its part, the place of a part, and why a sum cannot answer |
//! | [`Refusal`], [`Closure`], [`matched()`] | each refusal of a replay by name, whether a witness closes, and the check that two lists of cells agree |
//! | [`MorseError`], [`Budget`], [`Count`] | the caller's own fault, a walk past its budget, or a sum past the integers, and the units that a walk and a check count in |
//!
//! # References
//!
//! - `Doré-2023-computing_spaces_type_theory` — exemplar: § 3.5 states the
//!   collapse `φ` and the inclusion `ι` of a graph with both inverse proofs,
//!   and § 3.6 lifts them to an equality of types, which composes. A
//!   [`Reduction`] states those four parts and their replay. Maximilian Doré,
//!   "Computing Spaces in Type Theory", doctoral thesis, University of Oxford,
//!   2023.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: §
//!   presented-spaces-normal-forms. Reductions compose in sequence and from
//!   local to global.

#![no_std]

extern crate alloc;

/// Defines a transparent newtype over one primitive with `From` conversions
/// both ways.
macro_rules! wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident($raw:ty);) => {
        $(#[$meta])*
        #[repr(transparent)]
        $vis struct $name($raw);

        impl From<$raw> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $raw) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $raw
        {
            /// Unwraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }
    };
}

mod error;
mod reduction;
mod refusal;
mod sum;

pub use error::Budget;
pub use error::Count;
pub use error::MorseError;
pub use reduction::Answer;
pub use reduction::Reduction;
pub use reduction::Then;
pub use refusal::Closure;
pub use refusal::Refusal;
pub use refusal::matched;
pub use sum::PartIndex;
pub use sum::Sum;
pub use sum::SumFault;
pub use sum::Summand;
