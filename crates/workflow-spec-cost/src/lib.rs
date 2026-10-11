//! **Specification cost**: executable specifications ranked by the time the
//! slowest enforcing tests spend checking them.
//!
//! Enforcement runs every `#[spec]` clause on every call, so a clause that
//! traverses state grown across calls makes the enforced code quadratic. A
//! census of clause shapes cannot tell which of them the tests pay for; a
//! profile can. This crate samples the tests, charges each sample to the
//! specification check on its stack, and ranks the checks.
//!
//! - [`select`] names the tests: given ones, or the slowest enforcing tests of
//!   the merge-queue runs the test-timing store holds.
//! - [`region`] reads the lines of every `#[spec]` attribute in the workspace.
//! - [`profile`] builds the tests for sampling, records each under `perf` and
//!   reads the samples back through [`stack`].
//! - [`ledger`] charges each sample to the outermost check on its stack and
//!   renders the ranking.
//!
//! See [how a sample is charged](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-spec-cost/README.md#how-a-sample-is-charged).

pub mod error;
pub mod ledger;
pub mod profile;
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
pub use crate::region::Regions;
pub use crate::select::Workload;
pub use crate::select::WorkloadCount;
pub use crate::select::slowest_enforcing;
