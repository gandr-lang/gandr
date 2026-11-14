//! The measurement of a sheaf of entry maps on the circle's level of 32
//! points: its construction, its cochains, its cohomology and its gluing.
//!
//! The level has 32 points and 32 edges, the 64 cells that a sheaf holds.
//! Each stalk has the width that the row names. Each map reads the entries
//! in order. The map from the first point into the last edge reads each
//! entry one place on, so the sheaf is twisted.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `new` | one `Sheaf::new` over a clone of the level's poset |
//! | `cochains` | one `Sheaf::cochains` with the incidences of the circle |
//! | `cohomology` | one `CochainComplex::cohomology`, in 40 samples of 2 operations each, since one elimination at width 8 takes about a tenth of a second |
//! | `glue` | one `Sheaf::glue` of the cover by the 32 points, each section one at each entry |
//!
//! `cargo bench --bench sheaf` runs the full measurement and prints one
//! table. Under any other runner the binary runs one short pass and prints
//! nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

#[path = "../../theory-exact-reals/benches/support.rs"]
mod support;

use core::hint::black_box;

use gandr_theory_cellular_sheaves::Entry;
use gandr_theory_cellular_sheaves::Incidence;
use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_cellular_sheaves::Sheaf;
use gandr_theory_cellular_sheaves::Width;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;

use crate::support::Count;
use crate::support::Figures;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The points of the level, and so its edges.
const POINTS: usize = 32;

/// The stalk widths that the rows measure.
const WIDTHS: [usize; 2] = [1, 8];

/// A point of the level, numbered from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Point(usize);

/// A cell of the level.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Cell
{
    /// A point.
    Vertex(Point),
    /// An edge from its tail to its head.
    Edge(Point, Point),
}

/// The graded poset of the level: its points, then its edges, each edge
/// above its two ends.
///
/// # Specification
/// trivial.
fn level() -> GradedPoset<Cell>
{
    let mut cells: Vec<Cell> = (0 .. POINTS)
        .map(|point| Cell::Vertex(Point(point)))
        .collect();
    cells.extend((0 .. POINTS).map(|tail| {
        let head = tail
            .saturating_add(1)
            .checked_rem(POINTS)
            .expect("the level has points");
        Cell::Edge(Point(tail), Point(head))
    }));
    GradedPoset::new(
        cells,
        |lower, upper| match (*lower, *upper) {
            (Cell::Vertex(point), Cell::Edge(tail, head)) if point == tail || point == head => {
                Comparison::Below
            },
            (Cell::Vertex(_) | Cell::Edge(..), Cell::Vertex(_) | Cell::Edge(..)) => {
                Comparison::NotBelow
            },
        },
        ElementCount::from(POINTS.saturating_mul(2)),
    )
    .expect("64 cells")
}

/// The twisted sheaf on `poset` with stalks of `width` entries: each map
/// reads the entries in order, and the map from the first point into the
/// last edge reads each entry one place on.
///
/// # Specification
/// trivial.
fn twisted(
    poset: GradedPoset<Cell>,
    width: Width,
) -> Sheaf<Cell>
{
    let entries = usize::from(width);
    Sheaf::new(
        poset,
        |_| width,
        move |lower, upper| {
            let shifted = matches!(
                (*lower, *upper),
                (Cell::Vertex(Point(0)), Cell::Edge(Point(tail), _)) if tail == POINTS.saturating_sub(1)
            );
            (0 .. entries).map(move |entry| {
                if shifted {
                    Entry::from(
                        entry
                            .saturating_add(1)
                            .checked_rem(entries)
                            .expect("a stalk has entries"),
                    )
                }
                else {
                    Entry::from(entry)
                }
            })
        },
    )
    .expect("the twisted sheaf")
}

/// The incidence of a point in an edge: positive at its head and negative at
/// its tail.
///
/// # Specification
/// trivial.
fn oriented(
    face: &Cell,
    cell: &Cell,
) -> Incidence
{
    match (*face, *cell) {
        (Cell::Vertex(point), Cell::Edge(_, head)) if point == head => Incidence::Positive,
        (Cell::Vertex(point), Cell::Edge(tail, _)) if point == tail => Incidence::Negative,
        (Cell::Vertex(_) | Cell::Edge(..), Cell::Vertex(_) | Cell::Edge(..)) => Incidence::Zero,
    }
}

/// Runs the measurement, and prints its table under `cargo bench`.
///
/// # Specification
/// trivial.
fn main()
{
    let output = Output::of_run();
    let ((batch, samples), (slow_batch, slow_samples)) = match output {
        Output::Table => ((Count(16), Count(400)), (Count(2), Count(40))),
        Output::Silent => ((Count(1), Count(1)), (Count(1), Count(1))),
    };
    if matches!(output, Output::Table) {
        println!("| Row | Width | p50 ns | p99 ns | Allocations |");
        println!("| --- | ----- | ------ | ------ | ----------- |");
    }
    let poset = level();
    for width in WIDTHS.map(Width::from) {
        let sheaf = twisted(poset.clone(), width);
        let complex = sheaf.cochains(oriented).expect("the circle is a complex");
        let section = vec![Rational::ONE; usize::from(width)];
        let cover: Vec<(Element, &[Rational])> = (0 .. POINTS)
            .map(|point| (Element::from(point), section.as_slice()))
            .collect();
        let new = measure(batch, samples, || {
            black_box(twisted(black_box(poset.clone()), width));
        });
        let cochains = measure(batch, samples, || {
            black_box(black_box(&sheaf).cochains(oriented)).expect("the circle is a complex");
        });
        let cohomology = measure(slow_batch, slow_samples, || {
            black_box(black_box(&complex).cohomology()).expect("the cohomology");
        });
        let glue = measure(batch, samples, || {
            black_box(black_box(&sheaf).glue(black_box(&cover))).expect("a well-formed cover");
        });
        if matches!(output, Output::Table) {
            let rows: [(&str, &Figures); 4] = [
                ("new", &new),
                ("cochains", &cochains),
                ("cohomology", &cohomology),
                ("glue", &glue),
            ];
            for (row, figures) in rows {
                print_row(format_args!("{row} | {}", usize::from(width)), figures);
            }
        }
    }
}
