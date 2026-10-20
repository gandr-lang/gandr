//! **Test timing**: nextest priority levels proposed from the per-test
//! durations of recent merge-queue runs.
//!
//! nextest starts higher-priority tests first, so a suite whose slowest
//! tests start early finishes sooner on a fixed number of threads. Which
//! tests are slowest changes as the code does; this crate reads what the
//! queue measured and proposes the levels, and a reviewer commits them.
//!
//! - [`fetch`] lists successful merge-queue runs with `gh` and stores each
//!   run's JUnit reports once.
//! - [`report`] reads the reports and summarises each test by the lower median
//!   of its samples in the lane where it takes longest.
//! - [`priority`] reads the priorities `.config/nextest.toml` sets now,
//!   proposes a level per test with a margin either side of each boundary, and
//!   renders the table a reviewer reads and the overrides they commit.
//!
//! See the [levels and their margins](https://github.com/gandr-lang/gandr/blob/main/crates/workflow-test-timing/README.md#levels-and-margins).

#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "3 cost-shape sites; #814 lists them"
    )
)]

pub mod error;
pub mod fetch;
pub mod priority;
pub mod report;

pub use crate::error::ConfigDefect;
pub use crate::error::TestCaseDefect;
pub use crate::error::TimingError;
pub use crate::fetch::Repository;
pub use crate::fetch::RunId;
pub use crate::fetch::RunLimit;
pub use crate::fetch::Stored;
pub use crate::fetch::download;
pub use crate::fetch::read_run;
pub use crate::fetch::recent_runs;
pub use crate::fetch::stored_runs;
pub use crate::priority::ConfigText;
pub use crate::priority::Generated;
pub use crate::priority::Overrides;
pub use crate::priority::Priority;
pub use crate::priority::Proposal;
pub use crate::priority::Table;
pub use crate::priority::proposals;
pub use crate::report::History;
pub use crate::report::Timing;
