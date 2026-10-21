//! **Hotpath guard**: a commit's failed `hotpath / <benchmark>` checks, filed
//! on one issue per pull request, `perf: #<n> regresses <sites>`, for the
//! triage lane to route to the authoring lane.
//!
//! - [`check`] reads a failed check's summary into its wall-time line and the
//!   sites over its policy's threshold.
//! - [`report`] names the pull request, and renders the title, the labels and
//!   the body with its `## Lint` heading.
//! - [`github`] lists the commit's checks and pull request and keeps the one
//!   issue in step through `gh`.
//!
//! # Decisions
//!
//! **The check stays non-blocking; the issue is the guard.** hotpath Cloud
//! posts its check after the benchmark upload, which can land after the rest
//! of the pipeline, so a required check would hold every pull request for
//! it. The guard runs on the check's completion instead, so the regression is
//! filed whether or not the pull request has merged.
//!
//! **One issue per pull request, every failed benchmark in it.** Each failed
//! check's event reads all of the commit's hotpath checks, so the `gandr`
//! and `gandr-timing` events write the same issue and the later one loses
//! nothing. The title opens `perf: #<n> regresses `, which finds the issue
//! again; a later failed run retitles it. A commit no pull request carries is
//! keyed by its short form. A closed issue stays closed: a regression after
//! the close is a new issue.
//!
//! **The pull request the commit heads.** A stack's lower head is carried by
//! every pull request above it, so the guard names the one whose head is the
//! commit, and the first listed only when none is.
//!
//! **Areas from both ends.** The labels join the pull request's `area:`
//! labels, the authoring lane, with the tiers of the crates the sites live
//! in, where the regression shows.
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
pub mod report;

pub use crate::check::CommitSha;
pub use crate::check::Repository;
pub use crate::error::GuardError;
pub use crate::github::Filed;
pub use crate::report::Report;
pub use crate::report::Standing;
