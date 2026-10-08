//! **Content-defined chunking** for the storage tier: where a stream of
//! canonical units is cut into chunks, decided by the content rather than by a
//! position counter, under parameters a downstream root commits.
//!
//! # What the crate is for
//!
//! A store that cuts by position shifts every later cut when one byte is
//! inserted, so two versions of a value share nothing past the edit. A store
//! that cuts where the content says moves only the cuts near the edit, so the
//! chunks around it keep their identities and their storage. This crate is
//! that decision and nothing else: it reads no store, hashes no chunk, and
//! names no chunk; it returns where the cuts fall and why.
//!
//! # Two profiles
//!
//! - The **record-safe** profile ([`ChunkerParams`], [`chunk_record_slices`],
//!   [`chunk_spans`]) runs a Gear rolling hash over canonical record bytes and
//!   cuts only between complete records, under byte and record limits.
//! - The **typed** profile ([`TypedChunkerParams`], [`TypedChunker`]) never
//!   sees bytes: a caller walking its own grammar reports a boundary event
//!   wherever a cut is admissible, with the tokens since the previous event and
//!   a residue — a rolling hash of the subtree the event closes. The scanner
//!   cuts when the residue is divisible by kappa or the pending tokens reach
//!   the cap.
//!
//! Both profiles are deterministic, read each input once with no lookahead,
//! and commit their parameters as bytes ([`ParameterCommitment`]) opening with
//! one domain, [`PARAMETER_DOMAIN`], so two writers that disagree on a
//! parameter produce different roots instead of silently different cuts.
//!
//! # Failure
//!
//! Every refusal is a [`ChunkerError`] naming what was refused. No operation
//! panics, no arithmetic wraps where a count or position is concerned, and no
//! operation repairs an input it was handed.
//!
//! The named ideas and their primary references are in this crate's
//! `README.md`.

#![no_std]

extern crate alloc;

pub mod commitment;
pub mod error;
pub mod gear;
pub mod span;
pub mod typed;
pub mod units;

pub use crate::commitment::AlgorithmVersion;
pub use crate::commitment::PARAMETER_DOMAIN;
pub use crate::commitment::ParameterCommitment;
pub use crate::error::ArithmeticOperation;
pub use crate::error::ChunkerError;
pub use crate::error::InvalidParameterReason;
pub use crate::error::ProfileField;
pub use crate::error::RawDiscriminator;
pub use crate::gear::CanonicalBytes;
pub use crate::gear::CanonicalRecords;
pub use crate::gear::ChunkLimits;
pub use crate::gear::ChunkerParams;
pub use crate::gear::GearTableVersion;
pub use crate::gear::NormalizationPolicy;
pub use crate::gear::RecordBoundaryRule;
pub use crate::gear::SeedPolicy;
pub use crate::gear::SeedSalt;
pub use crate::gear::chunk_record_slices;
pub use crate::gear::chunk_spans;
pub use crate::span::BoundaryReason;
pub use crate::span::ByteSpan;
pub use crate::span::ChunkSpan;
pub use crate::span::RecordSpan;
pub use crate::typed::BoundaryEvent;
pub use crate::typed::CutDecision;
pub use crate::typed::Kappa;
pub use crate::typed::TokenCap;
pub use crate::typed::TypedChunker;
pub use crate::typed::TypedChunkerParams;
pub use crate::units::BoundaryResidue;
pub use crate::units::ByteCount;
pub use crate::units::BytePosition;
pub use crate::units::RecordCount;
pub use crate::units::RecordPosition;
pub use crate::units::TokenCount;
