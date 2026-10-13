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
//! `quenchant-shape`.
//!
//! # Executable specifications
//!
//! The item specifications pair executable `#[spec]` predicates with local `#
//! Adequacy` witnesses. Enforced runs check rewrite order and budgets, overlap
//! and certificate support, preserved completion state, and the exact
//! successful replay prefix before a typed refusal. The boundary witnesses
//! include empty schedules and support, interrupted batches, independently
//! failing replay legs, and fusion retries that preserve the store and
//! identifier.
//!
//! The test-only numeral strategy is the sole executable exemption: the pinned
//! attribute cannot name its opaque `impl Strategy` return in a generated
//! predicate signature. The fusion differential independently checks every
//! generated input through borrowed producer views and its size, rejecting
//! metavariables, wrong constructors or arities, and values outside zero
//! through 63 successors. The exemption ends when opaque returns are supported.
//!
//! # References
//!
//! - Donald E. Knuth and Peter B. Bendix. "Simple Word Problems in Universal
//!   Algebras." In _Computational Problems in Abstract Algebra_, Pergamon,
//!   1970, pages 263–297. `doi:10.1016/B978-0-08-012975-4.50028-X` — critical
//!   pairs, orienting a divergent pair by a reduction order, and the completion
//!   loop `complete` runs.
//! - Franz Baader and Tobias Nipkow. _Term Rewriting and All That_. Cambridge
//!   University Press, 1998. `doi:10.1017/CBO9781139172752` — critical pairs
//!   and the critical-pair lemma, completion as an inference system that can
//!   fail or diverge, and overlaps at interior positions, which this enumerator
//!   does not compute.
//! - Craig C. Squier, Friedrich Otto, and Yuji Kobayashi. "A Finiteness
//!   Condition for Rewriting Systems." _Theoretical Computer Science_ 131, 2
//!   (1994), pages 271–294 — the critical branchings of a convergent
//!   presentation, joined, generate its homotopy relations: the reading of a
//!   confluence certificate as a coherence cell.
//! - Dimitri Ara, Albert Burroni, Yves Guiraud, Philippe Malbos, François
//!   Métayer, and Samuel Mimram. _Polygraphs: From Rewriting to Higher
//!   Categories_. London Mathematical Society Lecture Note Series 495,
//!   Cambridge University Press, March 2025. `doi:10.1017/9781009498968`;
//!   preprint `arXiv:2312.00429` — coherent presentations and Squier
//!   completion, which extends Knuth–Bendix completion with a 3-cell for every
//!   critical branching.
//! - Nicolas Behr. "Tracelets and Tracelet Analysis of Compositional Rewriting
//!   Systems." In _Proceedings of Applied Category Theory 2019_, Electronic
//!   Proceedings in Theoretical Computer Science 323 (2020), pages 44–71.
//!   `doi:10.4204/EPTCS.323.4` — tracelets as derivations recorded for
//!   re-execution, sequential composition of rules, and the concurrency theorem
//!   the fused-cell differential adopts as a test.

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
pub use crate::completion::Joinability;
pub use crate::completion::SuppliedOverlapError;
pub use crate::completion::complete;
pub use crate::completion::complete_with_overlap_source;
pub use crate::completion::join_critical_pairs;
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
pub use crate::tracelet::replay_from_peak;
pub use crate::tracelet::replay_path;
