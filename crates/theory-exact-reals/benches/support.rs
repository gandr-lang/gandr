//! The harness that the crate's measurements share: a timed batch of one
//! operation, its percentiles and its allocations, and one table row.

use std::time::Instant;

/// A count of operations or samples.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Count(pub usize);

/// One row's figures: nanoseconds per operation at the median and at the
/// 99th percentile, and allocations per operation in hundredths.
pub struct Figures
{
    /// The median of the per-operation sample means, in nanoseconds.
    pub median: u128,
    /// The 99th percentile of the per-operation sample means, in
    /// nanoseconds.
    pub tail: u128,
    /// Allocations per operation, in hundredths.
    pub allocations: u128,
}

/// Whether the run prints its figures.
#[derive(Clone, Copy)]
pub enum Output
{
    /// The full measurement prints its table.
    Table,
    /// The short pass prints nothing.
    Silent,
}

impl Output
{
    /// The full table under `cargo bench`, and the short silent pass under
    /// any other runner.
    ///
    /// # Specification
    /// trivial.
    pub fn of_run() -> Self
    {
        return if std::env::args().any(|argument| argument == "--bench") {
            Self::Table
        }
        else {
            Self::Silent
        };
    }
}

/// Time `operation` and count its allocations.
///
/// # Specification
/// trivial.
pub fn measure<Operation>(
    batch: Count,
    samples: Count,
    mut operation: Operation,
) -> Figures
where
    Operation: FnMut(),
{
    for _ in 0 .. batch.0 {
        operation();
    }
    let mut means = Vec::with_capacity(samples.0);
    for _ in 0 .. samples.0 {
        let start = Instant::now();
        for _ in 0 .. batch.0 {
            operation();
        }
        let total = start.elapsed().as_nanos();
        means.push(
            total
                .checked_div(u128::try_from(batch.0).expect("a batch fits"))
                .expect("a nonempty batch"),
        );
    }
    means.sort_unstable();
    let percentile = |hundredths: usize| {
        let index = means
            .len()
            .saturating_sub(1)
            .saturating_mul(hundredths)
            .checked_div(100)
            .expect("a nonzero divisor");
        means.get(index).copied().unwrap_or_default()
    };
    let counted = allocation_counter::measure(|| {
        for _ in 0 .. batch.0 {
            operation();
        }
    });
    let allocations = u128::from(counted.count_total)
        .saturating_mul(100)
        .checked_div(u128::try_from(batch.0).expect("a batch fits"))
        .expect("a nonempty batch");
    return Figures {
        median: percentile(50),
        tail: percentile(99),
        allocations,
    };
}

/// Print one row: its leading cells, then the figures.
///
/// # Specification
/// trivial.
pub fn print_row(
    lead: core::fmt::Arguments<'_>,
    figures: &Figures,
)
{
    let whole = figures
        .allocations
        .checked_div(100)
        .expect("a nonzero divisor");
    let fraction = figures
        .allocations
        .checked_rem(100)
        .expect("a nonzero divisor");
    println!(
        "| {lead} | {} | {} | {whole}.{fraction:02} |",
        figures.median, figures.tail
    );
}
