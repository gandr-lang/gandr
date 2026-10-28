//! The `conversion` series of the benchmark report: the conversion subject,
//! `corpus/model/conversion`, checked once under the hotpath profiler.
//!
//! | Workload | What it runs | Measured functions |
//! | -------- | ------------ | ------------------ |
//! | `conversion set` | `gandr check` of the conversion subject: closed computations, each a path the conversion settles by running both endpoints | each path's judgement (`decide`), where the conversion runs, and its admission (`admit`), where the kernel replays it |
//!
//! Built with `--features hotpath`, as the `gandr` series is. `mise run
//! ci:hotpath` runs it in GitHub Actions and uploads it as `conversion` and as
//! `conversion-timing`, judged under `hotpath/conversion-policy.toml` and
//! `hotpath/conversion-timing-policy.toml`.

#![expect(
    clippy::expect_used,
    clippy::panic,
    reason = "a measurement binary: a workload that cannot start ends the run"
)]

mod support;

use support::check;
use support::corpus;

/// The subject the conversion set checks, from the driver's manifest
/// directory.
const SUBJECT: &str = "../../corpus/model/conversion";

/// Check every source under [`SUBJECT`], each path settled by a run of its
/// endpoints.
///
/// # Specification
/// trivial.
fn conversion_set()
{
    check(vec![corpus(SUBJECT)]);
}

/// Run the conversion set once under its own measured block.
///
/// # Specification
/// trivial.
#[hotpath::main]
fn main()
{
    hotpath::measure_block!("conversion set", conversion_set());
}
