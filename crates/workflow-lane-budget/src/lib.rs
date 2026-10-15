//! **Lane budget**: each CI lane's median job time over the latest
//! merge-queue and pull-request runs, held against a budget the nightly
//! workflow states, and filed on one issue while a lane is over.
//!
//! - [`budget`] reads the budget table: a job's display name and the whole
//!   seconds its median may take.
//! - [`cone`] names the cone a landing touched: deep when it reaches the kernel
//!   or core stack, surface otherwise.
//! - [`report`] summarises each budgeted lane by the lower median of its
//!   successful jobs, per cone, and renders the Markdown table.
//! - [`github`] samples the runs and jobs through `gh` and keeps the one issue
//!   in step with the report.
//!
//! # Decisions
//!
//! **A drift guard, never a gate.** A lane that grows slower is a finding
//! for whoever owns CI, not a reason to refuse an unrelated landing, so the
//! report runs nightly, files an issue and blocks nothing. The budgets live
//! in the workflow beside the jobs they bound, so a change of a lane's shape
//! changes its budget in the same commit.
//!
//! **The lower median over ten runs.** One slow runner or one cold cache
//! moves a mean; the lower median is a time some job took and ignores the
//! slowest half of the window. Merge-queue and pull-request runs together
//! sample every lane: the test lanes run only in the queue, the obligations
//! lane only on a pull request. The alternatives were a mean, which a single
//! cold run drags, and a percentile over a longer window, which reports a
//! regression days late.
//!
//! **Two cones, two budgets.** A landing that touches the kernel or core
//! stack — a file under `crates/kernel-*` or `crates/core-*`, `Cargo.lock`,
//! `rust-toolchain.toml` or `.cargo/` — rebuilds the whole enforcing graph
//! and takes longer than one that touches only the surface. One budget is
//! wrong on both sides: tight enough to miss a surface regression, loose
//! enough to excuse a deep one. Each sampled run is classified by the cone
//! its changed files touched, and each class is held to its own budget.
//!
//! **One issue, found by its exact title.** It opens or reopens while any
//! lane is over and closes once all are within, so the repository holds one
//! record of the current drift, never one issue per night.
//!
//! **Reversal**: a CI provider that reports lane timing against budgets
//! itself, or required checks with timeouts tight enough to be the budget.
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
pub use crate::report::Report;
pub use crate::report::Standing;
