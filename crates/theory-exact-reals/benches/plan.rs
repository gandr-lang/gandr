//! The measurement of plans: the canonical form, the bytes and their reading
//! back, for the cut of the square root of two and for plans of a thousand
//! distinct nodes.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `finish` | [`PlanBuilder::finish`] of a builder that holds the plan's nodes once |
//! | `finish, unshared` | [`PlanBuilder::finish`] of a builder that holds every node of the plan's tree, each subterm again |
//! | `encode` | [`Plan::encode`] |
//! | `decode` | [`Plan::decode`] of the canonical bytes, with its check that they are canonical |
//!
//! The plan of a thousand nodes sums 500 distinct constants of 63 bits into
//! a chain of 499 sums and compares the sum with zero. Its tree form builds
//! each square of a chain of ten squares again, 2047 nodes for 11 distinct
//! ones, so that row times the walk that finds equal nodes. `cargo bench`
//! runs the full measurement and prints one table. Under any other runner
//! the binary runs one short pass of every row and prints nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

mod support;

use core::hint::black_box;

use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Cut;
use gandr_theory_exact_reals::DeBruijn;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::EncodedPlan;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Plan;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;

use crate::support::Count;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The builder of the cut of the square root of two.
///
/// # Specification
/// trivial.
fn square_root_of_two() -> (PlanBuilder, Root)
{
    let mut builder = PlanBuilder::new();
    let x = builder
        .real(Real::Bound(DeBruijn::from(0)))
        .expect("a node");
    let zero = builder.real(Real::Constant(Dyadic::ZERO)).expect("a node");
    let two = builder
        .real(Real::Constant(Dyadic::from(2_i64)))
        .expect("a node");
    let square = builder.real(Real::Mul(x, x)).expect("a node");
    let negative = builder.open(Open::Less(x, zero)).expect("a node");
    let small = builder.open(Open::Less(square, two)).expect("a node");
    let lower = builder.open(Open::Join(negative, small)).expect("a node");
    let positive = builder.open(Open::Less(zero, x)).expect("a node");
    let large = builder.open(Open::Less(two, square)).expect("a node");
    let upper = builder.open(Open::Meet(positive, large)).expect("a node");
    let hull = NumericInterval::new(
        Bound::closed(Dyadic::ONE),
        Bound::closed(Dyadic::from(2_i64)),
        Orientation::Proper,
    )
    .expect("an ordered hull");
    let cut = builder
        .real(Real::Cut(Cut {
            hull,
            lower,
            upper,
            laws: Evidence::from(0),
        }))
        .expect("a node");
    return (builder, Root::Real(cut));
}

/// The builder of a thousand distinct nodes: a chain of sums of distinct
/// constants, compared with zero.
///
/// # Specification
/// trivial.
fn thousand() -> (PlanBuilder, Root)
{
    let mut builder = PlanBuilder::new();
    let mut draw = 0x9E37_79B9_7F4A_7C15_u64;
    let mut constant = |builder: &mut PlanBuilder| {
        // xorshift64, kept odd and below 2^63 so each constant is inline.
        draw ^= draw.wrapping_shl(13);
        draw ^= draw.wrapping_shr(7);
        draw ^= draw.wrapping_shl(17);
        let mantissa = i64::try_from(draw.wrapping_shr(1) | 1).expect("below 2^63");
        builder
            .real(Real::Constant(Dyadic::from(mantissa)))
            .expect("a node")
    };
    let mut sum: RealId = constant(&mut builder);
    for _ in 1_u32 .. 500 {
        let next = constant(&mut builder);
        sum = builder.real(Real::Add(sum, next)).expect("a node");
    }
    let zero = builder.real(Real::Constant(Dyadic::ZERO)).expect("a node");
    let positive = builder.open(Open::Less(zero, sum)).expect("a node");
    return (builder, Root::Open(positive));
}

/// The builder of a chain of ten squares written as a tree: every operand
/// built again.
///
/// # Specification
/// trivial.
fn unshared() -> (PlanBuilder, Root)
{
    let mut builder = PlanBuilder::new();
    let mut frontier: Vec<RealId> = core::iter::repeat_with(|| {
        builder
            .real(Real::Bound(DeBruijn::from(0)))
            .expect("a node")
    })
    .take(1024)
    .collect();
    while frontier.len() > 1 {
        frontier = frontier
            .chunks(2)
            .map(|operands| {
                let left = operands.first().copied().expect("a left operand");
                let right = operands.get(1).copied().expect("a right operand");
                builder.real(Real::Mul(left, right)).expect("a node")
            })
            .collect();
    }
    let root = frontier.first().copied().expect("one root");
    return (builder, Root::Real(root));
}

/// Measure every row of one plan, printing the rows when `print` asks.
///
/// # Specification
/// trivial.
fn rows(
    name: core::fmt::Arguments<'_>,
    (builder, root): (PlanBuilder, Root),
    batch: Count,
    samples: Count,
    print: Output,
)
{
    let plan = builder.clone().finish(root).expect("a plan");
    let bytes = plan.encode();
    let finish = measure(batch, samples, || {
        black_box(black_box(builder.clone()).finish(root)).expect("a plan");
    });
    let encode = measure(batch, samples, || {
        black_box(black_box(&plan).encode());
    });
    let decode = measure(batch, samples, || {
        black_box(Plan::decode(EncodedPlan::from(black_box(&bytes)))).expect("canonical bytes");
    });
    if matches!(print, Output::Table) {
        let nodes = usize::from(plan.node_count());
        let length = bytes.as_ref().len();
        print_row(
            format_args!("{name} | {nodes} | {length} | finish"),
            &finish,
        );
        print_row(
            format_args!("{name} | {nodes} | {length} | encode"),
            &encode,
        );
        print_row(
            format_args!("{name} | {nodes} | {length} | decode"),
            &decode,
        );
    }
}

/// Run the measurement, or the short pass outside `cargo bench`.
///
/// # Specification
/// trivial.
fn main()
{
    let output = Output::of_run();
    let (batch, samples) = match output {
        Output::Table => (Count(16), Count(400)),
        Output::Silent => (Count(1), Count(1)),
    };
    if matches!(output, Output::Table) {
        println!("| Plan | Nodes | Bytes | Operation | p50 ns | p99 ns | Allocations |");
        println!("| ---- | ----- | ----- | --------- | ------ | ------ | ----------- |");
    }
    rows(
        format_args!("square root of two"),
        square_root_of_two(),
        batch,
        samples,
        output,
    );
    rows(
        format_args!("a thousand nodes"),
        thousand(),
        batch,
        samples,
        output,
    );
    rows(
        format_args!("ten squares, unshared"),
        unshared(),
        batch,
        samples,
        output,
    );
}
