//! **Lane budget**: each CI lane's median job time over the latest
//! merge-queue and pull-request runs, held against a budget the nightly
//! workflow states, and filed on one issue while a lane is over.
//!
//! - [`budget`] reads the budget table: a job's display name and the whole
//!   seconds its median may take.
//! - [`cone`] names the cone a landing touched: deep when it reaches the kernel
//!   or core stack, surface otherwise.
//! - [`report`] summarises each budgeted lane by the lower median of its
//!   successful jobs, per cone, and renders the Markdown table collapsed under
//!   a summary of its lanes and its verdict.
//! - [`github`] samples the runs and jobs through `gh` and keeps the one issue
//!   in step with the report.
//!
//! # Boundaries
//!
//! The report runs nightly, files an issue and blocks no landing. The budgets
//! live in the workflow beside the jobs they bound, so a change of a lane's
//! shape changes its budget in the same commit.
//!
//! The summary is the lower median of ten runs: a time some job took, ignoring
//! the slowest half of the window. Merge-queue and pull-request runs together
//! sample every landing lane: the test lanes run only in the queue, the
//! obligations lane only on a pull request. A lane only the daily scheduled
//! run holds, such as the nightly mutation run, is a `--daily` budget and is
//! sampled over the scheduled runs alone, in a table of its own; the listing
//! asks for scheduled runs, since a day's landing runs fill any window of the
//! newest hundred. A lane of the nightly workflow, such as the all-features
//! tests, is a `--nightly` budget, sampled over that workflow's scheduled runs
//! in a third table; a dispatch is not a night.
//!
//! A landing that touches the kernel or core stack — a file under
//! `crates/kernel-*` or `crates/core-*`, `Cargo.lock`, `rust-toolchain.toml`
//! or `.cargo/` — is deep and is held to its own budget; a surface landing is
//! held to the other. One issue, found by its exact title, opens or reopens
//! while any lane is over and closes once all are within, so the repository
//! holds one record of the current drift.
//!
//! # References
//!
//! See the [crate README](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-lane-budget/README.md).

pub mod budget;
pub mod cone;
pub mod error;
pub mod github;
pub mod report;

pub use crate::budget::Budget;
pub use crate::budget::RunCount;
pub use crate::cone::Cone;
pub use crate::error::BudgetError;
pub use crate::github::Filed;
pub use crate::github::IssueTitle;
pub use crate::github::Window;
pub use crate::report::Report;
pub use crate::report::Standing;
