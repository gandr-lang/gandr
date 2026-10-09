//! The **conversion-decision seam** between the untrusted convertibility engine
//! and the certified kernel.
//!
//! # Why the seam exists
//!
//! Convertibility is proof search, and the proof is what gets certified. The
//! engine searches and is trusted with nothing; what it emits is a trace of the
//! decisions it made, and the kernel replays that trace with a sequential
//! algorithm that performs no search. A wrong engine therefore costs
//! completeness and never soundness.
//!
//! # The seam names no term type
//!
//! This crate owns no term vocabulary, no storage format, no wire
//! representation, and no replay policy. Its generic identifier parameter keeps
//! those concerns in the consumer that owns the arena, and the constraint is
//! enforced by the generics rather than by review.
//!
//! # The vocabulary covers branches, not heuristics
//!
//! [`ConversionDecision`] records **the side of every reduction and the branch
//! taken at every choice point** — which is the grain a proof search needs,
//! against the grain a heuristic unfolding strategy needs. That is what makes
//! replay search-free: with the recorded choices in hand the rechecker has at
//! most one applicable rule at every step.
//!
//! # The static-dispatch discipline
//!
//! [`TraceSink`] carries an associated [`SinkActivity`] constant, the same
//! discipline the check-memo seam takes. Instantiated at [`NullSink`] a
//! conversion path builds no decision values and holds no recording state, so
//! sink-off conversion is **the same function at a different type parameter**
//! rather than a second implementation. [`TraceLog`] is the recording side,
//! and it is what a differential counts its exercised path through.
//!
//! The crate is `no_std` and depends only on `core`, `alloc` and the
//! specification facade.
//!
//! The papers the crate draws on are in its `README.md`, § References.

#![no_std]

extern crate alloc;

pub mod decision;
pub mod sink;

pub use crate::decision::ConversionDecision;
pub use crate::decision::ConversionSide;
pub use crate::decision::SubgoalPosition;
pub use crate::sink::DecisionCount;
pub use crate::sink::NullSink;
pub use crate::sink::SinkActivity;
pub use crate::sink::TraceLog;
pub use crate::sink::TraceSink;
