//! **Lane budget**: each CI lane's median job time over the latest runs that
//! hold it, held against a budget the nightly workflow states, and filed on
//! one issue while a lane is over.
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
//! - [`workflows`] times each workflow's runs whole, wall time and job time
//!   summed, and holds a workflow given a summed budget to it and its ceiling.
//!
//! # Boundaries
//!
//! The report runs nightly, files an issue and blocks no landing. The budgets
//! live in the workflow beside the jobs they bound, so a change of a lane's
//! shape changes its budget in the same commit.
//!
//! The summary is the lower median of ten runs: a time some job took, ignoring
//! the slowest half of the window. Merge-queue and pull-request runs sample
//! the landing lanes: Clippy and the compiler policy in the queue, the
//! obligations lane on a pull request. A merge group on `landing` skips the
//! test lanes, so an `--integration` budget samples its lane over the CI
//! workflow's dispatches on `integration`, in a table of its own. A push to
//! `main` builds every package and no gate waits on it, so a second table gives
//! the same lanes over those pushes as information: no budget, and no share of
//! the standing. A `--daily` budget samples a lane of the daily scheduled run,
//! such as the mutation run, over those runs alone; the listing asks for them,
//! since a day's landing runs fill any window of the newest hundred. A
//! `--nightly` budget samples a lane of the nightly workflow over its scheduled
//! runs; a dispatch is not a night.
//!
//! A landing that touches the kernel or core stack — a file under
//! `crates/kernel-*` or `crates/core-*`, `Cargo.lock`, `rust-toolchain.toml`
//! or `.cargo/` — is deep and is held to its own budget; a surface landing is
//! held to the other. One issue, found by its exact title, opens or reopens
//! while any lane is over and closes once all are within, so the repository
//! holds one record of the current drift.
//!
//! The hosted budget is a workflow's summed job time per run, the nightly's
//! within 15 minutes and never past 20. A `--summed NAME=BUDGET/CEILING`
//! argument holds a workflow to the two and adds a table of every active
//! workflow's wall and summed times with the cache's usage; a budgeted
//! workflow over keeps the issue open as an over lane does.
//!
//! # References
//!
//! See the [crate README](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-lane-budget/README.md).

pub mod budget;
pub mod cone;
pub mod error;
pub mod github;
pub mod report;
pub mod workflows;

pub use crate::budget::Budget;
pub use crate::budget::RunCount;
pub use crate::cone::Cone;
pub use crate::error::BudgetError;
pub use crate::github::Filed;
pub use crate::github::IssueTitle;
pub use crate::github::Window;
pub use crate::report::Report;
pub use crate::report::Standing;
pub use crate::workflows::Summed;
pub use crate::workflows::Workflows;
