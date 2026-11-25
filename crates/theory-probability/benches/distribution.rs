//! The measurement of the finite Giry monad: `bind` and `product` at supports
//! of `2^8` and `2^16` points.
//!
//! Each row starts from the uniform distribution over the `s` points
//! `0 .. s`, at `s = 2^4` and at `s = 2^8`, so each result has `s^2` points
//! before its merge.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `product` | the product with itself: `s^2` pairs, in order with no sort |
//! | `kernels` | the `s` kernel results alone, each a pushforward of `s` points |
//! | `bind, disjoint` | the Kleisli extension along `x ↦ x·s + uniform`: `s` ascending runs that do not overlap, `s^2` points |
//! | `bind, sum` | the Kleisli extension along `x ↦ x + uniform`: `s` overlapping runs merged onto `2s - 1` points |
//!
//! `cargo bench` runs the full measurement and prints one table. Under any
//! other runner the binary runs one short pass of every row and prints
//! nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

#[path = "../../theory-exact-reals/benches/support.rs"]
mod support;

use core::hint::black_box;

use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_probability::Distribution;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// A point of a measured support, and the point a kernel result starts at.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
struct Value(u32);

/// The kernel result that starts at `base`: `factor` moved up by it.
///
/// # Specification
/// trivial.
fn shifted(
    factor: &Distribution<Value>,
    base: Value,
) -> Distribution<Value>
{
    return factor
        .map(|&value| Value(base.0.checked_add(value.0).expect("a small point")))
        .expect("a pushforward");
}

/// Run the measurement, or the short pass outside `cargo bench`.
///
/// # Specification
/// trivial.
fn main()
{
    let output = Output::of_run();
    let (batch, samples) = match output {
        Output::Table => (Count(4), Count(200)),
        Output::Silent => (Count(1), Count(1)),
    };
    if matches!(output, Output::Table) {
        println!(
            "A `u32` point with its weight is {} bytes.",
            size_of::<(Value, Rational)>()
        );
        println!();
        println!("| Row | Points | p50 ns | p99 ns | Allocations |");
        println!("| --- | ------ | ------ | ------ | ----------- |");
    }
    for exponent in [4_u32, 8] {
        let side = 2_u32.checked_pow(exponent).expect("a small side");
        let factor = Distribution::uniform((0 .. side).map(Value)).expect("a uniform distribution");
        let disjoint_base = |point: Value| Value(point.0.checked_mul(side).expect("a small base"));
        let disjoint = factor
            .bind(|&point| Ok(shifted(&factor, disjoint_base(point))))
            .expect("a Kleisli extension");
        assert_eq!(
            disjoint.points().len(),
            usize::try_from(side.checked_mul(side).expect("a small square"))
                .expect("a small count"),
            "the disjoint results keep each point"
        );
        let product = measure(batch, samples, || {
            black_box(black_box(&factor).product(&factor)).expect("a product");
        });
        let kernels = measure(batch, samples, || {
            for point in (0 .. side).map(Value) {
                black_box(shifted(black_box(&factor), disjoint_base(point)));
            }
        });
        let bind_disjoint = measure(batch, samples, || {
            black_box(black_box(&factor).bind(|&point| Ok(shifted(&factor, disjoint_base(point)))))
                .expect("a Kleisli extension");
        });
        let bind_sum = measure(batch, samples, || {
            black_box(black_box(&factor).bind(|&point| Ok(shifted(&factor, point))))
                .expect("a Kleisli extension");
        });
        if matches!(output, Output::Table) {
            for (row, figures) in [
                ("product", &product),
                ("kernels", &kernels),
                ("bind, disjoint", &bind_disjoint),
                ("bind, sum", &bind_sum),
            ] {
                print_row(
                    format_args!("{row} | 2^{}", exponent.saturating_mul(2)),
                    figures,
                );
            }
        }
    }
}
