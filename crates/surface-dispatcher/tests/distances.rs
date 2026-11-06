//! Probe 14 of the presented-spaces frame: distances in the Lawvere quantale,
//! composed along the two-step derivation that each fusion cell replaces.
//!
//! The census fuses each composition overlap of each block, and composes the
//! fused cell's bound through the two steps of its derivation
//! ([`Fusions::Composed`]). This suite reads the census's fusion rows over
//! the corpus, and holds each verdict that the probe found: each fusion
//! replays, and has a composed bound equal to the census reading of its
//! cell.
//!
//! A cell whose right side writes a wire that its left side does not bind
//! writes the wire under a fresh name at each firing. So such a cell, fused
//! with itself, replays: both paths write the wire under the join's name.

use alloc::vec::Vec;
use std::path::Path;
use std::path::PathBuf;

use gandr_surface_dispatcher::Census;
use gandr_surface_dispatcher::CensusStep;
use gandr_surface_dispatcher::FusionRow;
use gandr_surface_dispatcher::FusionVerdict;
use gandr_surface_dispatcher::Fusions;
use gandr_surface_dispatcher::HoleCount;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::HoleName;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_ordered_algebras::Comparison;
use gandr_theory_ordered_algebras::Distance;
use gandr_theory_ordered_algebras::Lawvere;
use gandr_theory_ordered_algebras::OrderedSemiring as _;
use gandr_theory_ordered_algebras::check;
use quenchant_shape::shape::Maybe;

/// The fusion rows of every corpus source, each with the source that writes
/// its block, in path order and then in the census's order.
///
/// # Specification
/// trivial.
fn census() -> Vec<(PathBuf, FusionRow)>
{
    let mut census = Census::new(
        super::coincide::sources().into_iter().collect(),
        Fusions::Composed,
    );
    let mut rows = Vec::new();
    while let Maybe::Present(step) = census.step() {
        if let CensusStep::Source {
            path,
            fusions,
            over,
            ..
        } = step
        {
            assert!(
                over.is_empty(),
                "{}: a block passes the fusion budget",
                path.display()
            );
            rows.extend(fusions.into_iter().map(|row| (path.to_path_buf(), row)));
        }
    }
    rows
}

/// The composed count of the hole named `hole` in `row`.
///
/// # Specification
/// trivial.
fn hole_count(
    row: &FusionRow,
    hole: &HoleName,
) -> HoleCount
{
    row.holes
        .iter()
        .find(|&&(ref var, _)| var.hole() == hole)
        .map(|&(_, count)| count)
        .unwrap_or_default()
}

/// `count` ticks as a distance.
///
/// # Specification
/// trivial.
fn ticks(count: HoleCount) -> Distance
{
    Distance::finite(Dyadic::from(
        i64::try_from(u64::from(count)).expect("a count fits an i64"),
    ))
    .expect("a count is not negative")
}

#[test]
fn each_fusion_cell_s_composed_bound_is_its_census_reading()
{
    let rows = census();
    let quantale = Lawvere::default();
    // Each fusion replays, and has a composed bound equal to the census
    // reading of its cell.
    for &(ref path, ref row) in &rows {
        match row.verdict {
            FusionVerdict::Exact => {},
            ref other @ (FusionVerdict::Looser(_)
            | FusionVerdict::Unsound(_)
            | FusionVerdict::Unread(..)
            | FusionVerdict::Unfused
            | FusionVerdict::Refused(_)
            | FusionVerdict::Outside
            | FusionVerdict::Unreplayed
            | FusionVerdict::Unbound(..)) => {
                panic!("{}:{row}: reads {other:?}", path.display())
            },
        }
    }
    // The circuit rule `cong1`, cell 0, wires `x′` between its two nodes, and
    // its left side does not bind `x′`. Fused with itself, it replays.
    assert!(
        rows.iter().any(|&(ref path, ref row)| {
            path.ends_with(Path::new("model/circuit/circuit-rule-block.gandr"))
                && row.left == CellId::from(0_usize)
                && row.right == row.left
                && row.verdict == FusionVerdict::Exact
        }),
        "`cong1` fused with itself replays"
    );
    // `thrice` writes `t` three times. Fused with itself, it writes `t` nine
    // times in two ticks. Fused with `twice`, it writes `t` six times.
    let shrub = |left: usize, right: usize| {
        rows.iter()
            .find(|&&(ref path, ref row)| {
                path.ends_with(Path::new("model/desc/occurrence-count.gandr"))
                    && row.left == CellId::from(left)
                    && row.right == CellId::from(right)
            })
            .map_or_else(
                || panic!("the shrubs fuse cell {left} into cell {right}"),
                |&(_, ref row)| row,
            )
    };
    let two = ticks(HoleCount::from(2_u64));
    let t = HoleName::from("t");
    for (right, copies) in [(7_usize, 9_u64), (6, 6)] {
        let row = shrub(7, right);
        assert_eq!(row.verdict, FusionVerdict::Exact, "{row}");
        assert_eq!(hole_count(row, &t), HoleCount::from(copies), "{row}");
        assert!(
            quantale.compare(&row.ticks, &two) == Comparison::Below
                && quantale.compare(&two, &row.ticks) == Comparison::Below,
            "two written rules make two ticks: {row}"
        );
    }
    // The quantale's laws hold on every distance a bound takes.
    let distances: std::collections::HashSet<Distance> = rows
        .iter()
        .flat_map(|&(_, ref row)| {
            let scales = row.holes.iter().map(|&(_, count)| ticks(count));
            core::iter::once(row.ticks.clone()).chain(scales)
        })
        .collect();
    assert!(
        check(&Lawvere::generated(distances.into_iter().collect())).is_ok(),
        "the Lawvere laws hold on the bounds' distances"
    );
}
