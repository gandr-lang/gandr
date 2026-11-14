//! The reduction of a sheaf along a matching: the cohomology that a twisted
//! circle keeps, and the pairs and the walks that the reduction refuses.

use gandr_theory_cellular_sheaves::Dimension;
use gandr_theory_cellular_sheaves::Entry;
use gandr_theory_cellular_sheaves::Level;
use gandr_theory_cellular_sheaves::Sheaf;
use gandr_theory_cellular_sheaves::SheafError;
use gandr_theory_cellular_sheaves::Width;
use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::greedy;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_graded_posets::Rank;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;

use crate::towers::Cell;
use crate::towers::LAST_LEVEL;
use crate::towers::Point;
use crate::towers::Space;
use crate::towers::constant;
use crate::towers::oriented;
use crate::towers::poset;

/// Where a sheaf of three entries on the circle turns its entries.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Twist
{
    /// Each map reads each entry at its own place.
    Straight,
    /// The map from the first point to the edge that leaves it turns the
    /// entries one place.
    Once,
    /// The map from the first point to the edge that closes the cycle turns
    /// them one place as well, which undoes the first turn.
    Undone,
}

/// The sheaf on `level` of the circle's tower with a stalk of three entries
/// on each cell, its maps turned as `twist` states.
///
/// # Specification
/// trivial.
fn three_entries(
    level: Level,
    twist: Twist,
) -> Sheaf<Cell>
{
    let first = Cell::Vertex(Point(0));
    Sheaf::new(
        poset(Space::Circle, level).expect("a level the poset holds"),
        |_| Width::from(3_usize),
        move |lower, upper| {
            let leaves = matches!(*upper, Cell::Edge(tail, _) if tail == Point(0));
            let closes =
                matches!(*upper, Cell::Edge(tail, head) if head == Point(0) && tail != Point(0));
            let turned = *lower == first
                && match twist {
                    Twist::Straight => false,
                    Twist::Once => leaves,
                    Twist::Undone => leaves || closes,
                };
            let start = usize::from(turned);
            [0_usize, 1, 2].map(|entry| {
                Entry::from(
                    entry
                        .checked_add(start)
                        .and_then(|turn| turn.checked_rem(3))
                        .expect("an entry of three"),
                )
            })
        },
    )
    .expect("the sheaf")
}

#[test]
fn a_twisted_circle_keeps_its_cohomology_on_its_reduct()
{
    // A cocycle of degree zero reads each point's entries along each edge.
    // Straight, every cochain constant along the cycle is one, so each degree
    // has three dimensions. Turned once, a cocycle must be fixed by the turn,
    // so each degree has one. The turn lies on a pair of the matching, so the
    // reduction reads its inverse; the second turn lies on a face of the
    // critical edge, where it reads the map itself. The two turns cancel only
    // where the inverse reads each entry back.
    for level in (1 ..= LAST_LEVEL).map(Level::from) {
        for (twist, dimension) in [
            (Twist::Straight, 3_usize),
            (Twist::Once, 1_usize),
            (Twist::Undone, 3_usize),
        ] {
            let sheaf = three_entries(level, twist);
            let count = usize::from(sheaf.poset().count());
            let cells: Vec<Element> = (0 .. count).map(Element::from).collect();
            let matching = greedy(&mut sheaf.oriented(oriented), &cells).expect("the level reads");
            let reduced = sheaf
                .reduce(&matching, oriented, Budget::from(count))
                .expect("the matching is compatible");
            assert_eq!(reduced.cells().len(), 2_usize, "{twist:?} at {level:?}");
            let whole = sheaf
                .cochains(oriented)
                .expect("a complex")
                .cohomology()
                .expect("the cohomology");
            let kept = reduced.cochains().cohomology().expect("the cohomology");
            for degree in (0 ..= 1_usize).map(Rank::from) {
                assert_eq!(
                    whole.dimension(degree),
                    Dimension::from(dimension),
                    "{twist:?} at {level:?} in {degree:?}"
                );
                assert_eq!(
                    kept.dimension(degree),
                    Dimension::from(dimension),
                    "{twist:?} at {level:?} in {degree:?}"
                );
            }
        }
    }
}

/// A point below the edge that leaves it, the point's stalk of `width`
/// entries and the edge's of two, the edge reading `reads` from the point.
///
/// # Specification
/// trivial.
fn segment(
    width: Width,
    reads: [Entry; 2],
) -> Sheaf<Cell>
{
    let point = Cell::Vertex(Point(0));
    let edge = Cell::Edge(Point(0), Point(1));
    let poset = GradedPoset::new(
        Vec::from([point, edge]),
        |lower, upper| {
            if *lower == point && *upper == edge {
                Comparison::Below
            }
            else {
                Comparison::NotBelow
            }
        },
        ElementCount::from(2_usize),
    )
    .expect("the segment");
    Sheaf::new(
        poset,
        |cell| {
            if *cell == point {
                width
            }
            else {
                Width::from(2_usize)
            }
        },
        |_, _| reads,
    )
    .expect("the sheaf")
}

#[test]
fn a_matched_map_that_is_not_invertible_is_refused_by_its_pair()
{
    let (point, edge) = (Element::from(0_usize), Element::from(1_usize));
    let refused = Err(SheafError::NotInvertible {
        lower: point,
        upper: edge,
    });
    // The circle's loop: the matching on the poset, where every incidence is
    // one, pairs the point with its loop, but the loop's incidence is zero.
    let sheaf = constant(Space::Circle, Level::from(0_usize));
    let cells = [point, edge];
    let mut complex = sheaf.poset();
    let matching = greedy(&mut complex, &cells).expect("the poset reads");
    assert_eq!(
        sheaf.reduce(&matching, oriented, Budget::from(cells.len())),
        refused
    );
    // A point of one entry below an edge of two, and a point of two entries
    // whose edge reads the first entry twice.
    for (width, reads) in [
        (Width::from(1_usize), [
            Entry::from(0_usize),
            Entry::from(0_usize),
        ]),
        (Width::from(2_usize), [
            Entry::from(0_usize),
            Entry::from(0_usize),
        ]),
    ] {
        let sheaf = segment(width, reads);
        let matching = greedy(&mut sheaf.oriented(oriented), &cells).expect("the segment reads");
        assert_eq!(
            sheaf.reduce(&matching, oriented, Budget::from(cells.len())),
            refused,
            "{width:?}"
        );
    }
    // The same segment with a map that reads each entry once reduces to
    // nothing.
    let sheaf = segment(Width::from(2_usize), [
        Entry::from(1_usize),
        Entry::from(0_usize),
    ]);
    let matching = greedy(&mut sheaf.oriented(oriented), &cells).expect("the segment reads");
    let reduced = sheaf
        .reduce(&matching, oriented, Budget::from(cells.len()))
        .expect("the map is invertible");
    assert_eq!(reduced.cells(), []);
}

#[test]
fn a_walk_past_its_budget_is_refused()
{
    // The circle of four points: the walk from the edge that closes the cycle
    // reaches the three redundant points.
    let sheaf = constant(Space::Circle, Level::from(2_usize));
    let count = usize::from(sheaf.poset().count());
    let cells: Vec<Element> = (0 .. count).map(Element::from).collect();
    let matching = greedy(&mut sheaf.oriented(oriented), &cells).expect("the level reads");
    assert_eq!(
        sheaf
            .reduce(&matching, oriented, Budget::from(2_usize))
            .map(|_| ()),
        Err(SheafError::PastBudget(Budget::from(2_usize)))
    );
    assert!(
        sheaf
            .reduce(&matching, oriented, Budget::from(3_usize))
            .is_ok()
    );
}
