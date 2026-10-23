//! **Hotpath guard**: a commit's failed `hotpath / <benchmark>` checks, filed
//! on one issue per regressed function, `perf: <function>`, whose body is the
//! index of that function's regressions and whose comments are their pull
//! requests' reports, one per pull request.
//!
//! - [`check`] reads a concluded check: a failed one's summary into its
//!   wall-time line, the sites over its policy's threshold and whether it is a
//!   runner shift, a passed one into its benchmark.
//! - [`report`] names the pull request, lists each function's regression per
//!   benchmark, and renders the report a comment carries.
//! - [`index`] reads and rewrites a function's index: its rows, their status
//!   and the issue's standing.
//! - [`github`] lists the commit's checks, its pull request and the
//!   `kind:performance` issues, and keeps each function's issue in step through
//!   `gh`.
//!
//! # Decisions
//!
//! **The check stays non-blocking; the issue is the guard.** hotpath Cloud
//! posts its check after the benchmark upload, so a required check would hold
//! every pull request for it; the guard runs on the check's completion
//! instead, before or after the merge.
//!
//! **One issue per function, not per pull request.** Three pull requests
//! regressing `module::decide` in one afternoon gave three issues, two of
//! them one runner shift, to be claimed together. The issue is the
//! function's, `perf: <function>`; a check naming several functions touches
//! several issues. One issue per pull request, the alternative, scattered a
//! function's history.
//!
//! **The body is the index; each pull request has one comment.** One row per
//! pull request and benchmark, rewritten in place; everything around the
//! table stays as written. A pull request's report is one comment, marked
//! `<!-- hotpath: pr=<n> -->`, that every later run of it edits, so the
//! comments count pull requests, never runs ([`index`]); appending one per
//! run put 36 comments on one issue in one stack's restacks.
//!
//! **The pull request the event names**, else the one the commit heads
//! ([`github::pull`]).
//!
//! **Runner shift.** A timing failure whose wall time and every regressed
//! function moved up together, calls and allocations unchanged, is the
//! runner: its row proposes the policy's false-positive step to the owner
//! and adds no comment ([`check::Failure::shift`]). The summary lists only
//! the functions over threshold, so the wall time stands for the rest.
//!
//! **An accepted growth is the pull request's.** A red check owes a verdict
//! before the queue; a landing whose body carries a settled `accepted` one
//! writes its rows `accepted`, with no comment and no new issue
//! ([`report::PullBody::accepted`]).
//!
//! **Reversal**: hotpath Cloud filing issues itself, or a required hotpath
//! check.
//!
//! See the [crate README](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-hotpath-guard/README.md).

// Module documentation in the lane budget's shape: 1 heading outside the
// vocabulary and 1 decision record. Each allow leaves with the rewrite that
// clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        reason = "module documentation in the lane budget's shape, which predates the shape lint"
    )
)]
pub mod check;
pub mod error;
pub mod github;
pub mod index;
pub mod report;

pub use crate::check::CommitSha;
pub use crate::check::Repository;
pub use crate::check::Unstated;
pub use crate::error::GuardError;
pub use crate::github::Filed;
pub use crate::index::Standing;
pub use crate::report::PullNumber;
pub use crate::report::Report;
