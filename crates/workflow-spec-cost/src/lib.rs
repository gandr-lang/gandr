//! **Specification cost**: executable specifications ranked by the time the
//! slowest enforcing tests spend checking them, and each test's enforcing time
//! over its plain time.
//!
//! Enforcement runs every `#[spec]` clause on every call, so a clause that
//! traverses state grown across calls makes the enforced code quadratic. A
//! census of clause shapes cannot tell which of them the tests pay for; a
//! profile can. This crate samples the tests, charges each sample to the
//! specification check on its stack, and ranks the checks. Between profiles,
//! the ratio watches every test on every CI run, so a clause that starts
//! walking shows in the run that lands it.
//!
//! - [`select`] names the tests: given ones, or the slowest enforcing tests of
//!   the merge-queue runs the test-timing store holds.
//! - [`region`] reads the lines of every `#[spec]` attribute in the workspace.
//! - [`profile`] builds the tests for sampling, records each under `perf` and
//!   reads the samples back through [`stack`].
//! - [`ledger`] charges each sample to the outermost check on its stack and
//!   renders the ranking.
//! - [`ratio`] pairs a run's enforcing JUnit report with the plain baseline's
//!   and prints each test's enforcing time over its plain time, flagging the
//!   tests whose checks dominate them: the `spec-cost-ratio` binary.
//!
//! See [how a sample is charged](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-spec-cost/README.md#how-a-sample-is-charged).

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "3 cost-shape sites; #814 lists them"
    )
)]

pub mod error;
pub mod ledger;
pub mod profile;
pub mod ratio;
pub mod region;
pub mod select;
pub mod stack;

pub use crate::error::CostError;
pub use crate::ledger::Charge;
pub use crate::ledger::Frequency;
pub use crate::ledger::Ledger;
pub use crate::ledger::RankLimit;
pub use crate::ledger::Ranking;
pub use crate::ledger::charge;
pub use crate::profile::Suites;
pub use crate::profile::read_samples;
pub use crate::profile::record;
pub use crate::ratio::Baseline;
pub use crate::ratio::Commit;
pub use crate::ratio::Comparison;
pub use crate::ratio::Comparisons;
pub use crate::ratio::Factor;
pub use crate::ratio::Floor;
pub use crate::ratio::Hours;
pub use crate::ratio::Pairing;
pub use crate::ratio::TestCount;
pub use crate::ratio::pair;
pub use crate::region::Regions;
pub use crate::select::Workload;
pub use crate::select::WorkloadCount;
pub use crate::select::slowest_enforcing;
