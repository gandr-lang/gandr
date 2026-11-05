//! The crate's measurement: dyadic and interval operations at four operand
//! widths, with their latency percentiles and their allocations.
//!
//! Each row times one operation on fixed operands. A sample is the mean time
//! of a batch of operations, read with the monotonic clock, and the row
//! reports the median and the 99th percentile of the samples. The
//! allocations are counted over one batch and divided by its size. The
//! widths are 63 bits, the widest inline mantissa, then 64 bits, the
//! narrowest carried one, then 256 and 4096 bits. The precision of every
//! operation is the operand width, so a sum or a product rounds.
//!
//! | Operation | What it times |
//! | --------- | ------------- |
//! | `dyadic add` | [`Dyadic::add`] of two operands 17 bits apart |
//! | `dyadic mul` | [`Dyadic::mul`] |
//! | `dyadic cmp` | [`Ord::cmp`] of two operands with one top bit |
//! | `interval add` | [`NumericInterval::add`] of two proper intervals |
//! | `interval mul, signed` | [`NumericInterval::mul`] of two positive intervals: two products |
//! | `interval mul, mixed` | [`NumericInterval::mul`] of two intervals that straddle zero: four products |
//!
//! `cargo bench` runs the full measurement and prints one table. Under any
//! other runner the binary runs one short pass of every row and prints
//! nothing, so the gates exercise it without timing it.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

use core::hint::black_box;
use core::ops::Add as _;
use core::ops::Neg as _;
use core::ops::Rem as _;
use core::ops::Shl as _;
use std::time::Instant;

use gandr_theory_exact_reals::BitWidth;
use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Precision;
use gandr_theory_exact_reals::Rounding;
use num_bigint::BigInt;

/// The operand widths the full run measures.
const WIDTHS: [u64; 4] = [63, 64, 256, 4096];

/// A count of operations or samples.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Count(usize);

/// One row's figures: nanoseconds per operation at the median and at the
/// 99th percentile, and allocations per operation in hundredths.
struct Figures
{
    /// The median of the per-operation sample means, in nanoseconds.
    median: u128,
    /// The 99th percentile of the per-operation sample means, in
    /// nanoseconds.
    tail: u128,
    /// Allocations per operation, in hundredths.
    allocations: u128,
}

/// A deterministic stream of draws, so every build of the bench measures the
/// same operands.
#[repr(transparent)]
struct Draws(u64);

impl Draws
{
    /// The next 64-bit draw.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> BigInt
    {
        // xorshift64
        self.0 ^= self.0.wrapping_shl(13);
        self.0 ^= self.0.wrapping_shr(7);
        self.0 ^= self.0.wrapping_shl(17);
        return BigInt::from(self.0);
    }

    /// An odd mantissa of exactly `width` bits.
    ///
    /// # Specification
    /// trivial.
    fn mantissa(
        &mut self,
        width: BitWidth,
    ) -> BigInt
    {
        let width = u64::from(width);
        let mut low = BigInt::ZERO;
        for _ in 0 .. width.div_ceil(64) {
            low = low.shl(64_u8).add(self.next());
        }
        let top = BigInt::from(1_u8).shl(width.checked_sub(1).expect("a width of one bit or more"));
        let half = BigInt::from(1_u8).shl(width.saturating_sub(2));
        let odd = low.rem(&half).shl(1_u8).add(1_u8);
        return if width == 1 { top } else { top.add(odd) };
    }
}

/// Time `operation` and count its allocations.
///
/// # Specification
/// trivial.
fn measure<Operation>(
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

/// The closed proper interval between two dyadics in either order.
///
/// # Specification
/// trivial.
fn closed(
    first: Dyadic,
    second: Dyadic,
) -> NumericInterval
{
    let (low, high) = if first <= second {
        (first, second)
    }
    else {
        (second, first)
    };
    return NumericInterval::new(Bound::closed(low), Bound::closed(high), Orientation::Proper)
        .expect("ordered endpoints");
}

/// Measure every row at `width`, printing the rows when `print` asks.
///
/// # Specification
/// trivial.
fn rows(
    width: BitWidth,
    batch: Count,
    samples: Count,
    print: Output,
)
{
    let mut draws = Draws(0x9E37_79B9_7F4A_7C15);
    let precision = Precision::try_from(u32::try_from(u64::from(width)).expect("a width fits"))
        .expect("an admitted precision");
    let zero = Exponent::from(0_i32);
    let gap = Exponent::from(-17_i32);
    let dyadic = |mantissa: BigInt, exponent: Exponent| {
        Dyadic::new(mantissa, exponent).expect("an exponent in range")
    };
    let left = dyadic(draws.mantissa(width), zero);
    let right = dyadic(draws.mantissa(width).neg(), gap);
    let same_top = dyadic(draws.mantissa(width), zero);
    let positive = closed(
        dyadic(draws.mantissa(width), zero),
        dyadic(draws.mantissa(width), zero),
    );
    let other_positive = closed(
        dyadic(draws.mantissa(width), zero),
        dyadic(draws.mantissa(width), zero),
    );
    let mixed = closed(
        dyadic(draws.mantissa(width).neg(), zero),
        dyadic(draws.mantissa(width), zero),
    );
    let other_mixed = closed(
        dyadic(draws.mantissa(width).neg(), zero),
        dyadic(draws.mantissa(width), zero),
    );
    let table: [(&str, Figures); 6] = [
        (
            "dyadic add",
            measure(batch, samples, || {
                black_box(black_box(&left).add(black_box(&right), precision, Rounding::Floor))
                    .expect("in range");
            }),
        ),
        (
            "dyadic mul",
            measure(batch, samples, || {
                black_box(black_box(&left).mul(black_box(&right), precision, Rounding::Floor))
                    .expect("in range");
            }),
        ),
        (
            "dyadic cmp",
            measure(batch, samples, || {
                black_box(black_box(&left).cmp(black_box(&same_top)));
            }),
        ),
        (
            "interval add",
            measure(batch, samples, || {
                black_box(black_box(&positive).add(black_box(&other_positive), precision))
                    .expect("in range");
            }),
        ),
        (
            "interval mul, signed",
            measure(batch, samples, || {
                black_box(black_box(&positive).mul(black_box(&other_positive), precision))
                    .expect("in range");
            }),
        ),
        (
            "interval mul, mixed",
            measure(batch, samples, || {
                black_box(black_box(&mixed).mul(black_box(&other_mixed), precision))
                    .expect("in range");
            }),
        ),
    ];
    if matches!(print, Output::Table) {
        for (name, figures) in table {
            let whole = figures
                .allocations
                .checked_div(100)
                .expect("a nonzero divisor");
            let fraction = figures
                .allocations
                .checked_rem(100)
                .expect("a nonzero divisor");
            println!(
                "| {} | {name} | {} | {} | {whole}.{fraction:02} |",
                u64::from(width),
                figures.median,
                figures.tail
            );
        }
    }
}

/// Whether the run prints its figures.
#[derive(Clone, Copy)]
enum Output
{
    /// The full measurement prints its table.
    Table,
    /// The short pass prints nothing.
    Silent,
}

/// Run the measurement, or the short pass outside `cargo bench`.
///
/// # Specification
/// trivial.
fn main()
{
    if std::env::args().any(|argument| argument == "--bench") {
        println!("| Width | Operation | p50 ns | p99 ns | Allocations |");
        println!("| ----- | --------- | ------ | ------ | ----------- |");
        for width in WIDTHS {
            let samples = if width > 1024 {
                Count(200)
            }
            else {
                Count(1000)
            };
            rows(BitWidth::from(width), Count(256), samples, Output::Table);
        }
    }
    else {
        for width in WIDTHS {
            rows(BitWidth::from(width), Count(2), Count(2), Output::Silent);
        }
    }
}
