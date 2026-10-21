//! **Coverage guard**: the nightly upload of `main`'s coverage against the
//! upload before it, filed on one issue when the coverage falls by more
//! than a threshold or the upload covers fewer files.
//!
//! - [`codecov`] reads Codecov's public API through `curl`: an upload's totals
//!   once processed, the upload of `main` before it, and each upload's files.
//! - [`measure`] computes a coverage as Codecov states it and the points one
//!   coverage moved from another.
//! - [`report`] compares the two uploads, sums each crate from its files and
//!   renders the Markdown the job summary and the issue carry.
//! - [`github`] keeps the one open drop issue in step through `gh`.
//!
//! # Decisions
//!
//! **The guard computes the drop itself.** Codecov's own project status
//! compares a commit with its parent's upload, and `main`'s parent commits
//! carry none: the upload is nightly, so the status has no base and is not
//! posted. The guard compares the upload with the newest processed upload of
//! `main` before it, which is what a reader of the nightly numbers compares.
//! The threshold is the one `codecov.yml` states for its project status, so
//! a dispatched run's status and the guard agree.
//!
//! **A coverage is rounded down, in hundredths.** Codecov writes coverage
//! with two decimals rounded down (its default `round: down`); the guard
//! computes the same number from the integer totals, so the title quotes the
//! numbers Codecov's page shows and no floating-point comparison decides a
//! filing.
//!
//! **Fewer files is a drop of its own.** A shard or a crate's tests missing
//! from the measurement takes its files out of the upload, and the
//! remaining files' coverage can rise; the file count catches what the
//! percentage hides.
//!
//! **One open issue, found by its title's prefix.** The title names the
//! numbers and the commit, so it changes with every drop; the guard finds
//! the open issue whose title starts with `coverage: main dropped from `,
//! rewrites its title and body, and opens one only when none is open. A
//! closed issue is a resolved drop and stays closed; a steady night touches
//! nothing, because closing is for whoever restored the number.
//!
//! **`curl`, not an HTTP crate.** The guard makes three requests a night on
//! a runner that has `curl`; an HTTP client crate would add a TLS stack to
//! the build for them. The reversal is a host without `curl`, or requests
//! that need streaming or authentication `curl` cannot carry plainly.
//!
//! **Reversal**: Codecov posting a project status on `main` against the
//! previous upload, or a per-pull-request coverage run whose status is a
//! required check.
//!
//! See the [crate README](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-coverage-guard/README.md).

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
pub mod codecov;
pub mod error;
pub mod github;
pub mod measure;
pub mod report;

pub use crate::codecov::CommitSha;
pub use crate::codecov::Repository;
pub use crate::codecov::Wait;
pub use crate::error::GuardError;
pub use crate::github::Filed;
pub use crate::measure::Points;
pub use crate::report::Comparison;
pub use crate::report::Standing;
