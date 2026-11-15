//! The store's measurement on a 6400-part graph: the indexed preimage
//! lookup, the insert-and-remove round trip, and the equation check per
//! mutation.
//!
//! The graph is a cycle of 3200 vertices and 3200 edges, both arrows
//! indexed. Each figure is the mean over many operations, timed with the
//! monotonic clock, after one warm-up pass. `cargo bench` runs the full
//! measurement; under `cargo test` the bench runs one short pass of each
//! loop and prints nothing, so the gates exercise it without timing it.
//! Built with the `hotpath` feature, the short pass is the `store` series of
//! the benchmark report: the profiler counts each store operation's calls,
//! time and allocations, and uploads the report when CI asks it to.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

use core::hint::black_box;
use core::time::Duration;
use std::time::Instant;

use gandr_storage_records::TreeParams;
use gandr_storage_schema::Indexing;
use gandr_storage_schema::PartKey;
use gandr_storage_schema::Presentation;
use gandr_storage_schema::Row;
use gandr_storage_schema::Schema;
use gandr_storage_schema::Store;

/// The vertices of the cycle; the edges are as many.
const VERTICES: usize = 3_200;

/// How many operations a full run times per figure.
const FULL: usize = 1_000_000;

/// How many operations a test-mode pass runs per loop.
const SMOKE: usize = 64;

/// The graph with a mark table, whose marks point at an edge and at that
/// edge's source — with the equation that says so, or without it.
///
/// # Specification
/// trivial.
fn schema(with_equation: Equation) -> Schema
{
    let presentation = Presentation::new()
        .object("V")
        .object("E")
        .object("M")
        .arrow("src", "E", "V", Indexing::Indexed)
        .arrow("tgt", "E", "V", Indexing::Indexed)
        .arrow("mark_edge", "M", "E", Indexing::Indexed)
        .arrow("mark_vertex", "M", "V", Indexing::Indexed);
    let presentation = match with_equation {
        Equation::Checked => {
            presentation.equation("mark_agrees", "M", ["mark_edge", "src"], ["mark_vertex"])
        },
        Equation::Absent => presentation,
    };
    Schema::present(&presentation).expect("the bench schema presents")
}

/// Whether the bench schema states the mark equation.
#[derive(Clone, Copy)]
enum Equation
{
    /// The equation is stated, so every mark is checked.
    Checked,
    /// The twin schema without it.
    Absent,
}

/// The cycle: 3200 vertices, and an edge from each to the next.
///
/// # Specification
/// trivial.
fn cycle(with_equation: Equation) -> (Store, Vec<PartKey>, Vec<PartKey>)
{
    let mut store = Store::new(schema(with_equation), TreeParams::default())
        .expect("the parameters are supported");
    let schema = store.schema().clone();
    let vertex = schema.object("V").expect("V");
    let edge = schema.object("E").expect("E");
    let src = schema.arrow("src").expect("src");
    let tgt = schema.arrow("tgt").expect("tgt");

    let vertices: Vec<PartKey> =
        core::iter::repeat_with(|| store.add_part(vertex, &Row::new()).expect("a vertex"))
            .take(VERTICES)
            .collect();
    let edges: Vec<PartKey> = vertices
        .iter()
        .zip(vertices.iter().cycle().skip(1))
        .map(|(&from, &to)| {
            store
                .add_part(edge, &Row::new().arrow(src, from).arrow(tgt, to))
                .expect("an edge")
        })
        .collect();
    (store, vertices, edges)
}

/// Times `count` runs of an operation and returns the mean.
///
/// # Specification
/// trivial.
fn mean<F>(
    count: Count,
    mut operation: F,
) -> Duration
where
    F: FnMut(Count),
{
    for index in 0 .. count.0.min(SMOKE) {
        operation(Count(index));
    }
    let start = Instant::now();
    for index in 0 .. count.0 {
        operation(Count(index));
    }
    let elapsed = start.elapsed();
    elapsed
        .checked_div(u32::try_from(count.0).expect("the count fits a u32"))
        .unwrap_or(elapsed)
}

/// An operation count, or the index of one operation.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Count(usize);

/// Runs the measurement.
///
/// # Specification
/// trivial.
#[cfg_attr(feature = "hotpath", hotpath::main)]
fn main()
{
    let full = std::env::args().any(|argument| argument == "--bench");
    let count = Count(if full { FULL } else { SMOKE });

    let (mut store, vertices, edges) = cycle(Equation::Absent);
    let schema = store.schema().clone();
    let src = schema.arrow("src").expect("src");
    let tgt = schema.arrow("tgt").expect("tgt");
    let edge = schema.object("E").expect("E");
    let parts = vertices.len().saturating_add(edges.len());
    let at = |index: Count| vertices.get(index.0 % VERTICES).copied().expect("a vertex");

    let borrowed = mean(count, |index| {
        black_box(store.preimage(src, at(index)).expect("an indexed preimage"));
    });
    let copied = mean(count, |index| {
        black_box(
            store
                .preimage(src, at(index))
                .expect("an indexed preimage")
                .to_vec(),
        );
    });
    let round_trip = mean(count, |index| {
        let from = at(index);
        let to = at(Count(index.0.saturating_add(1)));
        let added = store
            .add_part(edge, &Row::new().arrow(src, from).arrow(tgt, to))
            .expect("an edge");
        store.delete_part(edge, added).expect("and it goes");
    });

    let mut checked = Vec::new();
    for with_equation in [Equation::Absent, Equation::Checked] {
        let (mut store, _, edges) = cycle(with_equation);
        let schema = store.schema().clone();
        let src = schema.arrow("src").expect("src");
        let mark = schema.object("M").expect("M");
        let mark_edge = schema.arrow("mark_edge").expect("mark_edge");
        let mark_vertex = schema.arrow("mark_vertex").expect("mark_vertex");
        let figure = mean(count, |index| {
            let marked = edges.get(index.0 % VERTICES).copied().expect("an edge");
            let source = store.target(src, marked).expect("its source");
            let added = store
                .add_part(
                    mark,
                    &Row::new()
                        .arrow(mark_edge, marked)
                        .arrow(mark_vertex, source),
                )
                .expect("a mark that agrees");
            store.delete_part(mark, added).expect("and it goes");
        });
        checked.push(figure);
    }

    if full {
        let nanos = |duration: &Duration| duration.as_nanos();
        println!("store of {parts} parts, mean of {} operations", count.0);
        println!("| operation | ns |");
        println!("| --- | ---: |");
        println!("| preimage lookup, borrowed | {} |", nanos(&borrowed));
        println!("| preimage lookup, copied | {} |", nanos(&copied));
        println!("| insert-and-remove round trip | {} |", nanos(&round_trip));
        if let (Some(without), Some(with)) = (checked.first(), checked.get(1)) {
            println!("| mark round trip, no equation | {} |", nanos(without));
            println!("| mark round trip, equation checked | {} |", nanos(with));
        }
    }
}
