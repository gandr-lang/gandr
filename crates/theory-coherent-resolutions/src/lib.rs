//! Coherent resolution of a cell rewriting system: firing a cell, finding the
//! critical pairs, joining them under replayable certificates, and completing
//! the system until the pairs are exhausted or the budget declines.
//!
//! The modules are one construction read in order. A cell fires
//! ([`rewrite_at`], [`normalize`]); two cells whose left-hand sides unify, or
//! whose right-hand side and left-hand side do, overlap
//! ([`enumerate_overlaps`], [`Overlap`]); a branching that converges is
//! witnessed by a certificate that replays ([`Tracelet`],
//! [`confluence_tracelet`], [`derive_fused`]); and orienting the branchings
//! that diverge until none remains is completion ([`complete`],
//! [`complete_with_overlap_source`]). Overlap enumeration and the certificates
//! depend on each other — a certificate carries the overlap it joins, and the
//! overlap support relates certificates as well as cells — so
//! the crate encloses both.
//!
//! Everything is generic over the substrate's
//! [`CellAlphabet`](gandr_theory_cell_complexes::CellAlphabet) and adds no cell
//! vocabulary. The crate is `no_std` and depends on `alloc`, the substrate and
//! `quenchant-shape`. Its `README.md` carries the design and the references.

#![no_std]

extern crate alloc;

mod boundary;
mod completion;
mod overlap;
mod rewrite;
mod tracelet;

pub use crate::boundary::BatchIndex;
pub use crate::boundary::BudgetExhaustion;
pub use crate::boundary::CertificateIndex;
pub use crate::boundary::CompletionCellBudget;
pub use crate::boundary::CompletionStatus;
pub use crate::boundary::CompletionStepBudget;
pub use crate::boundary::NormalizationBudget;
pub use crate::boundary::OverlapIndex;
pub use crate::boundary::StepIndependence;
pub use crate::boundary::TraceletEquivalence;
pub use crate::boundary::TraceletReplay;
pub use crate::completion::CompletionBudget;
pub use crate::completion::CompletionOutcome;
pub use crate::completion::DeclineReason;
pub use crate::completion::SuppliedOverlapError;
pub use crate::completion::complete;
pub use crate::completion::complete_with_overlap_source;
pub use crate::completion::scheduled_confluence_batches;
pub use crate::overlap::Overlap;
pub use crate::overlap::OverlapKind;
pub use crate::overlap::OverlapRefusal;
pub use crate::overlap::OverlapSupport;
pub use crate::overlap::PeakLegs;
pub use crate::overlap::enumerate_overlaps;
pub use crate::overlap::overlaps_between;
pub use crate::overlap::peak_legs;
pub use crate::rewrite::CellApp;
pub use crate::rewrite::Normalization;
pub use crate::rewrite::Rewrite;
pub use crate::rewrite::apply_once;
pub use crate::rewrite::firing;
pub use crate::rewrite::normalize;
pub use crate::rewrite::redex_search;
pub use crate::rewrite::rewrite_at;
pub use crate::tracelet::ReplayPath;
pub use crate::tracelet::ReplayPathOutcome;
pub use crate::tracelet::ReplayStep;
pub use crate::tracelet::ReplayTrace;
pub use crate::tracelet::StuckStep;
pub use crate::tracelet::Tracelet;
pub use crate::tracelet::confluence_join;
pub use crate::tracelet::confluence_tracelet;
pub use crate::tracelet::derive_fused;
pub use crate::tracelet::replay_equivalent;
