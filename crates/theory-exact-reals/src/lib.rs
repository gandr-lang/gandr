//! Canonical dyadics, oriented intervals and the scoped plan DAG: the finite
//! arithmetic and the plan language that exact real computation reads.
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
//! approximant. It is never evidence that a comparison holds. The crate does
//! not depend on the gandr kernel, and no real number enters kernel
//! conversion.
//!
//! A computation over the reals is held as a [`Plan`]: a finite DAG of real,
//! open and domain nodes whose binders are de Bruijn indices. A plan holds
//! each distinct subterm once, and it has one canonical byte form, which
//! [`Plan::encode`] writes and [`Plan::decode`] reads.
//!
//! Every operation is total. Each malformed input is refused by name, and no
//! operation panics. The work of one arithmetic operation is bounded by its
//! operands' bit widths and the requested precision.
//!
//! # References
//!
//! - `vault:01a178aa-a419-7ab1-82e7-40a4f95938c6` — lineage: the exact-reals
//!   design, its canonical dyadics with an inline path, its oriented intervals
//!   as runtime approximants, its scoped plan DAG that keeps sharing as edges,
//!   and its firewall from the kernel.

#![no_std]

extern crate alloc;

pub mod codec;
pub mod dyadic;
pub mod interval;
pub mod plan;

pub use crate::codec::DecodeError;
pub use crate::codec::EncodedPlan;
pub use crate::codec::PlanBytes;
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
pub use crate::plan::Cut;
pub use crate::plan::DeBruijn;
pub use crate::plan::Domain;
pub use crate::plan::DomainId;
pub use crate::plan::Edge;
pub use crate::plan::Edges;
pub use crate::plan::Evidence;
pub use crate::plan::EvidenceSlot;
pub use crate::plan::Node;
pub use crate::plan::NodeCount;
pub use crate::plan::NodeId;
pub use crate::plan::Open;
pub use crate::plan::OpenId;
pub use crate::plan::Plan;
pub use crate::plan::PlanBuilder;
pub use crate::plan::PlanError;
pub use crate::plan::Power;
pub use crate::plan::Quantifier;
pub use crate::plan::Real;
pub use crate::plan::RealId;
pub use crate::plan::Root;
pub use crate::plan::Sort;
