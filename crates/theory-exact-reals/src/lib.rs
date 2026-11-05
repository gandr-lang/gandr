//! Canonical dyadics and oriented intervals: the finite arithmetic that exact
//! real computation reads.
//!
//! A real number is an infinite object, and a program can hold only finite
//! approximations of it. Floating point gives such approximations, but it
//! rounds each result without a record, so its enclosures are not sound. This
//! crate gives two exact finite domains instead. A [`Dyadic`] is a number
//! `m · 2^e` in one canonical form. A [`NumericInterval`] is a pair of dyadic
//! or infinite endpoints with an explicit closure for each endpoint and an
//! explicit orientation.
//!
//! The interval operations round outward. The lower endpoint rounds toward
//! the floor and the upper endpoint toward the ceiling, so each result
//! contains every exact result of its operands. An interval is an
//! approximant. It is never evidence that a comparison holds. A later
//! refinement machine emits certificates, and a checker replays them. The
//! crate does not depend on the gandr kernel, and no real number enters
//! kernel conversion.
//!
//! Every operation is total. A malformed interval is refused by name, an
//! exponent outside its range is a typed error, and no operation panics. The
//! work of one operation is bounded by its operands' bit widths and the
//! requested precision.
//!
//! # References
//!
//! - `vault:01a178aa-a419-7ab1-82e7-40a4f95938c6` — lineage: the exact-reals
//!   design, its canonical dyadics with an inline path, its oriented intervals
//!   as runtime approximants, and its firewall from the kernel.

#![no_std]

pub mod dyadic;
pub mod interval;

pub use crate::dyadic::BitWidth;
pub use crate::dyadic::Dyadic;
pub use crate::dyadic::DyadicError;
pub use crate::dyadic::Exactness;
pub use crate::dyadic::Exponent;
pub use crate::dyadic::Precision;
pub use crate::dyadic::Rounded;
pub use crate::dyadic::Rounding;
pub use crate::dyadic::Sign;
pub use crate::interval::Bound;
pub use crate::interval::Closure;
pub use crate::interval::Containment;
pub use crate::interval::Endpoint;
pub use crate::interval::IntervalError;
pub use crate::interval::NumericInterval;
pub use crate::interval::Orientation;
