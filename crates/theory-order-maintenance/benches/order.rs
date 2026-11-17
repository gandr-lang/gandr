//! The order's measurement: insertion, removal and comparison from a thousand
//! to a million elements, for each group width.
//!
//! Each figure is the mean over its workload's operations, timed with the
//! monotonic clock. The workloads, each from an empty structure but the last
//! two:
//!
//! | Workload | What it times |
//! | -------- | ------------- |
//! | `append` | `push_back`, `n` times |
//! | `anchor` | `insert_after` the first element, `n` times: every insertion lands where the last one did |
//! | `random` | `insert_after` an element drawn uniformly, `n` times |
//! | `compare` | `cmp` of two elements drawn uniformly, a million times, over the `random` structure |
//! | `remove` | `remove` of every element of the `random` structure in a drawn order |
//! | `churn` | `insert_after` a drawn element and `remove` a drawn one, `n` times, over a structure of `n` |
//!
//! `cargo bench` runs the full measurement and prints one row per width and
//! size, in nanoseconds per operation; under `cargo test` the bench runs one
//! short pass of each workload at the default width and prints nothing, so
//! the gates exercise it without timing it.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

use core::hint::black_box;
use core::time::Duration;
use std::time::Instant;

use gandr_theory_order_maintenance::GroupWidth;
use gandr_theory_order_maintenance::OrderMaintenance;
use gandr_theory_order_maintenance::Pos;

/// The sizes the full run measures.
const SIZES: [usize; 4] = [1_000, 10_000, 100_000, 1_000_000];

/// The group widths the full run measures.
const WIDTHS: [u32; 5] = [8, 12, 16, 24, 31];

/// How many comparisons the full run times per row.
const COMPARISONS: usize = 1_000_000;

/// The size a test-mode pass runs at.
const SMOKE: usize = 64;

/// A count of operations or elements.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Count(usize);

/// The payload each element carries: its insertion's index.
#[repr(transparent)]
struct Element(usize);

/// A deterministic stream of draws, so every width and every build of the
/// bench times the same operations.
#[repr(transparent)]
struct Draws(u64);

impl Draws
{
    /// A draw below `bound`, which is positive.
    ///
    /// # Specification
    /// trivial.
    fn below(
        &mut self,
        bound: Count,
    ) -> Count
    {
        // xorshift64
        self.0 ^= self.0.wrapping_shl(13);
        self.0 ^= self.0.wrapping_shr(7);
        self.0 ^= self.0.wrapping_shl(17);
        let bound = u64::try_from(bound.0).expect("a bound fits a u64");
        let draw = self.0.checked_rem(bound).expect("a positive bound");
        Count(usize::try_from(draw).expect("a draw fits a usize"))
    }
}

/// An empty structure at `width`.
///
/// # Specification
/// trivial.
fn build(width: GroupWidth) -> OrderMaintenance<Element>
{
    OrderMaintenance::with_group_width(width).expect("a structure")
}

/// The mean of `elapsed` over `count` operations.
///
/// # Specification
/// trivial.
fn per(
    elapsed: Duration,
    count: Count,
) -> Duration
{
    elapsed
        .checked_div(u32::try_from(count.0).expect("the count fits a u32"))
        .unwrap_or(elapsed)
}

/// One row: each workload's mean at `width` and `size`.
///
/// # Specification
/// trivial.
fn row(
    width: GroupWidth,
    size: Count,
    comparisons: Count,
) -> [Duration; 6]
{
    let mut draws = Draws(0x9E37_79B9_7F4A_7C15);
    let element = Element;

    let mut order = build(width);
    let start = Instant::now();
    for at in 0 .. size.0 {
        black_box(order.push_back(element(at)).expect("an append"));
    }
    let append = per(start.elapsed(), size);

    let mut order = build(width);
    let anchor = order.push_back(Element(0)).expect("the anchor");
    let start = Instant::now();
    for at in 1 ..= size.0 {
        black_box(
            order
                .insert_after(anchor, element(at))
                .expect("an insertion"),
        );
    }
    let behind = per(start.elapsed(), size);

    let mut order = build(width);
    let mut handles: Vec<Pos> = Vec::with_capacity(size.0);
    handles.push(order.push_back(Element(0)).expect("the first element"));
    let start = Instant::now();
    for at in 1 ..= size.0 {
        let drawn = draws.below(Count(handles.len()));
        let after = *handles.get(drawn.0).expect("a drawn handle");
        handles.push(
            order
                .insert_after(after, element(at))
                .expect("an insertion"),
        );
    }
    let random = per(start.elapsed(), size);

    let start = Instant::now();
    for _ in 0 .. comparisons.0 {
        let left = *handles
            .get(draws.below(Count(handles.len())).0)
            .expect("a drawn handle");
        let right = *handles
            .get(draws.below(Count(handles.len())).0)
            .expect("a drawn handle");
        black_box(order.cmp(left, right));
    }
    let compare = per(start.elapsed(), comparisons);

    let mut churned = build(width);
    let mut standing: Vec<Pos> = (0 .. size.0)
        .map(|at| churned.push_back(element(at)).expect("an append"))
        .collect();
    let start = Instant::now();
    for at in 0 .. size.0 {
        let drawn = draws.below(Count(standing.len()));
        let after = *standing.get(drawn.0).expect("a drawn handle");
        standing.push(
            churned
                .insert_after(after, element(at))
                .expect("an insertion"),
        );
        let gone = standing.swap_remove(draws.below(Count(standing.len())).0);
        black_box(churned.remove(gone).expect("a removal"));
    }
    let churn = per(start.elapsed(), size);

    let removals = Count(handles.len());
    let start = Instant::now();
    while !handles.is_empty() {
        let gone = handles.swap_remove(draws.below(Count(handles.len())).0);
        black_box(order.remove(gone).expect("a removal"));
    }
    let remove = per(start.elapsed(), removals);

    [append, behind, random, compare, remove, churn]
}

/// Runs the measurement.
///
/// # Specification
/// trivial.
fn main()
{
    let full = std::env::args().any(|argument| argument == "--bench");
    if !full {
        black_box(row(GroupWidth::DEFAULT, Count(SMOKE), Count(SMOKE)));
        return;
    }
    println!("ns per operation, mean of each workload's operations");
    println!("| width | elements | append | anchor | random | compare | remove | churn |");
    println!("| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |");
    for bits in WIDTHS {
        let width = GroupWidth::from(bits);
        for size in SIZES {
            let figures = row(width, Count(size), Count(COMPARISONS));
            let [append, behind, random, compare, remove, churn] =
                figures.map(|figure| figure.as_nanos());
            println!(
                "| {bits} | {size} | {append} | {behind} | {random} | {compare} | {remove} | {churn} |"
            );
        }
    }
}
