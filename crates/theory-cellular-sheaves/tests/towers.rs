//! Probe 17 of the presented-spaces frame: the cohomology of the interval
//! and the circle through their finite towers.
//!
//! Level `n` of the interval's tower is the path graph on `2ⁿ` points. Level
//! `n` of the circle's tower closes that path into a cycle. Each level is a
//! graded poset whose cells are its points and its edges, an edge above its
//! two ends. The constant sheaf puts a stalk of one entry on each cell, and
//! each map reads that entry. An edge's head has a positive incidence and its
//! tail a negative one, so the coboundary of a cochain of degree zero gives
//! each edge the value at its head less the value at its tail.
//!
//! The bonding map sends level `n + 1` to level `n`: point `j` goes to point
//! `j / 2`. The edge from point `2i` lies inside a pair and collapses into
//! point `i`. The edge from point `2i + 1` joins two pairs and goes onto the
//! edge from point `i`, the circle's loop at level zero among them. The probe
//! checks that the map each bonding map induces on cohomology has full rank,
//! and that the cohomology is the rationals in degree zero, and in degree one
//! for the circle alone.
//!
//! The graded poset holds at most 64 cells, so the tower stops at level 5:
//! 63 cells for the interval and 64 for the circle. Level 6 is refused by its
//! count.

use gandr_theory_cellular_sheaves::Dimension;
use gandr_theory_cellular_sheaves::Entry;
use gandr_theory_cellular_sheaves::Image;
use gandr_theory_cellular_sheaves::Incidence;
use gandr_theory_cellular_sheaves::Level;
use gandr_theory_cellular_sheaves::Sheaf;
use gandr_theory_cellular_sheaves::SheafError;
use gandr_theory_cellular_sheaves::Tower;
use gandr_theory_cellular_sheaves::Width;
use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::greedy;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_graded_posets::Rank;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;

/// The last level the graded poset holds.
pub const LAST_LEVEL: usize = 5;

/// A point of a level, numbered from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Point(pub usize);

/// A cell of a level.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Cell
{
    /// A point.
    Vertex(Point),
    /// An edge from its tail to its head.
    Edge(Point, Point),
}

/// The space a tower presents.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Space
{
    /// The interval: each level a path.
    Interval,
    /// The circle: each level a cycle.
    Circle,
}

/// The number of points of a level.
///
/// # Specification
/// trivial.
fn points(level: Level) -> Point
{
    let shift = u32::try_from(usize::from(level)).expect("a small level");
    Point(1_usize.checked_shl(shift).expect("a small level"))
}

/// The cells of `level` of the tower of `space`: its points, then its edges.
///
/// # Specification
/// trivial.
fn cells(
    space: Space,
    level: Level,
) -> Vec<Cell>
{
    let count = points(level).0;
    let mut out: Vec<Cell> = (0 .. count)
        .map(|point| Cell::Vertex(Point(point)))
        .collect();
    let edges = match space {
        Space::Interval => count.saturating_sub(1),
        Space::Circle => count,
    };
    out.extend((0 .. edges).map(|tail| {
        let head = tail
            .saturating_add(1)
            .checked_rem(count)
            .expect("a level has a point");
        Cell::Edge(Point(tail), Point(head))
    }));
    out
}

/// The graded poset of `level` of the tower of `space`: an edge lies above
/// its two ends.
///
/// # Specification
/// trivial.
pub fn poset(
    space: Space,
    level: Level,
) -> Result<GradedPoset<Cell>, DualityError>
{
    GradedPoset::new(
        cells(space, level),
        |lower, upper| match (*lower, *upper) {
            (Cell::Vertex(point), Cell::Edge(tail, head)) if point == tail || point == head => {
                Comparison::Below
            },
            (Cell::Vertex(_) | Cell::Edge(..), Cell::Vertex(_) | Cell::Edge(..)) => {
                Comparison::NotBelow
            },
        },
        ElementCount::from(128_usize),
    )
}

/// The constant sheaf on `level` of the tower of `space`: one entry on each
/// cell, each map reading it.
///
/// # Specification
/// trivial.
pub fn constant(
    space: Space,
    level: Level,
) -> Sheaf<Cell>
{
    let poset = poset(space, level).expect("a level the poset holds");
    Sheaf::new(
        poset,
        |_| Width::from(1_usize),
        |_, _| [Entry::from(0_usize)],
    )
    .expect("the constant sheaf")
}

/// The incidence of a point in an edge: positive at the head, negative at
/// the tail, and zero at the one end of a loop.
///
/// # Specification
/// trivial.
pub fn oriented(
    face: &Cell,
    cell: &Cell,
) -> Incidence
{
    match (*face, *cell) {
        (Cell::Vertex(point), Cell::Edge(tail, head)) if point == head && point != tail => {
            Incidence::Positive
        },
        (Cell::Vertex(point), Cell::Edge(tail, head)) if point == tail && point != head => {
            Incidence::Negative
        },
        (Cell::Vertex(_) | Cell::Edge(..), Cell::Vertex(_) | Cell::Edge(..)) => Incidence::Zero,
    }
}

/// Where the bonding map onto `coarser` sends a cell of the next level of
/// `space`'s tower.
///
/// # Specification
/// trivial.
fn bonding(
    space: Space,
    coarser: Level,
) -> impl FnMut(&Cell) -> Image<[Entry; 1]>
{
    let below = cells(space, coarser);
    move |cell| {
        let onto = match *cell {
            Cell::Vertex(point) => Cell::Vertex(Point(point.0 >> 1_u32)),
            Cell::Edge(tail, _) if tail.0.checked_rem(2) == Some(0) => return Image::Collapsed,
            Cell::Edge(tail, _) => {
                let edge = below
                    .iter()
                    .find(|&&lower| matches!(lower, Cell::Edge(from, _) if from == Point(tail.0 >> 1_u32)));
                *edge.expect("the image of an edge is an edge")
            },
        };
        let at = below
            .iter()
            .position(|&lower| lower == onto)
            .expect("the image is a cell");
        Image::Onto {
            cell: Element::from(at),
            incidence: Incidence::Positive,
            entries: [Entry::from(0_usize)],
        }
    }
}

/// The tower of `space` through `last`.
///
/// # Specification
/// trivial.
fn tower(
    space: Space,
    last: Level,
) -> Tower<Cell>
{
    let mut tower =
        Tower::new(constant(space, Level::from(0_usize)), oriented).expect("the first level");
    for level in 1 ..= usize::from(last) {
        let coarser = Level::from(level.saturating_sub(1));
        tower
            .push(
                constant(space, Level::from(level)),
                oriented,
                bonding(space, coarser),
            )
            .unwrap_or_else(|error| panic!("{space:?} at level {level}: {error}"));
    }
    tower
}

/// The two towers, by name.
const SPACES: [Space; 2] = [Space::Interval, Space::Circle];

/// The cohomology the space of `space` has in `degree`.
///
/// # Specification
/// trivial.
pub fn expected(
    space: Space,
    degree: Rank,
) -> Dimension
{
    Dimension::from(match usize::from(degree) {
        0 => 1_usize,
        1 => usize::from(space == Space::Circle),
        _ => 0_usize,
    })
}

#[test]
fn the_circles_level_of_four_points_has_the_rationals_in_degrees_zero_and_one()
{
    // Four points and four edges in a cycle. The coboundary takes a value at
    // each point to the four differences around the cycle. A constant is its
    // kernel, so degree zero is the rationals. The four differences sum to
    // zero, so its image has dimension three, and degree one is the
    // rationals.
    let sheaf = constant(Space::Circle, Level::from(2_usize));
    assert_eq!(sheaf.poset().count(), ElementCount::from(8_usize));
    let complex = sheaf.cochains(oriented).expect("a complex");
    let delta = complex
        .coboundary(Rank::from(0_usize))
        .expect("degree zero");
    assert_eq!(
        (delta.rows(), delta.columns()),
        (Dimension::from(4_usize), Dimension::from(4_usize))
    );
    assert_eq!(delta.rank(), Ok(Dimension::from(3_usize)));
    assert_eq!(
        complex.coboundary(Rank::from(1_usize)),
        Err(SheafError::DegreeOutside(Rank::from(1_usize)))
    );
    let cohomology = complex.cohomology().expect("the cohomology");
    for degree in (0 ..= 2_usize).map(Rank::from) {
        assert_eq!(
            cohomology.dimension(degree),
            expected(Space::Circle, degree)
        );
    }
}

#[test]
fn every_level_of_both_towers_has_the_cohomology_of_its_space()
{
    for space in SPACES {
        let tower = tower(space, Level::from(LAST_LEVEL));
        for level in (0 ..= LAST_LEVEL).map(Level::from) {
            let cohomology = tower.cohomology(level).expect("a level of the tower");
            for degree in (0 ..= 1_usize).map(Rank::from) {
                assert_eq!(
                    cohomology.dimension(degree),
                    expected(space, degree),
                    "{space:?} at {level:?} in {degree:?}"
                );
            }
        }
        let past = Level::from(LAST_LEVEL.saturating_add(1));
        assert_eq!(
            tower.cohomology(past).map(|_| ()),
            Err(SheafError::LevelOutside(past))
        );
    }
}

#[test]
fn every_level_of_both_towers_keeps_its_cohomology_on_its_reduct()
{
    // The greedy matching on each oriented level pairs each vertex but the
    // last with the edge that leaves it. The interval keeps one vertex, and
    // the circle keeps one vertex and the edge that closes the cycle.
    for space in SPACES {
        for level in (0 ..= LAST_LEVEL).map(Level::from) {
            let sheaf = constant(space, level);
            let count = usize::from(sheaf.poset().count());
            let cells: Vec<Element> = (0 .. count).map(Element::from).collect();
            let matching = greedy(&mut sheaf.oriented(oriented), &cells).expect("the level reads");
            let reduced = sheaf
                .reduce(&matching, oriented, Budget::from(count))
                .expect("the matching is compatible");
            let critical = match space {
                Space::Interval => 1_usize,
                Space::Circle => 2_usize,
            };
            assert_eq!(reduced.cells().len(), critical, "{space:?} at {level:?}");
            let cohomology = reduced.cochains().cohomology().expect("the cohomology");
            for degree in (0 ..= 1_usize).map(Rank::from) {
                assert_eq!(
                    cohomology.dimension(degree),
                    expected(space, degree),
                    "{space:?} at {level:?} in {degree:?}"
                );
            }
        }
    }
}

#[test]
fn each_bonding_map_induces_an_isomorphism_on_cohomology()
{
    // The cohomology has the same dimension at each level, so an induced map
    // of full rank is an isomorphism.
    for space in SPACES {
        let tower = tower(space, Level::from(LAST_LEVEL));
        for level in (1 ..= LAST_LEVEL).map(Level::from) {
            for degree in (0 ..= 1_usize).map(Rank::from) {
                assert_eq!(
                    tower.induced(level, degree),
                    Ok(expected(space, degree)),
                    "{space:?} at {level:?} in {degree:?}"
                );
            }
        }
        let first = Level::from(0_usize);
        assert_eq!(
            tower.induced(first, Rank::from(0_usize)),
            Err(SheafError::LevelOutside(first))
        );
    }
}

#[test]
fn the_level_past_the_cell_budget_is_refused_by_its_count()
{
    // Level 6 has 64 points: 127 cells for the interval and 128 for the
    // circle. The graded poset holds them, but a sheaf holds each set of cells
    // as one bit row, so it refuses either level by its count.
    let past = Level::from(LAST_LEVEL.saturating_add(1));
    for (space, count) in [(Space::Interval, 127_usize), (Space::Circle, 128_usize)] {
        let poset = poset(space, past).expect("the graded poset holds the level");
        assert_eq!(poset.count(), ElementCount::from(count));
        assert_eq!(
            Sheaf::new(
                poset,
                |_| Width::from(1_usize),
                |_, _| [Entry::from(0_usize)]
            )
            .map(|_| ()),
            Err(SheafError::Poset(DualityError::TooManyElements(
                ElementCount::from(count)
            ))),
            "{space:?}"
        );
    }
}

#[test]
fn a_bonding_map_that_breaks_a_square_is_refused()
{
    // Level 2 of the interval onto level 1, with point 3 sent onto point 0
    // instead of point 1. The edge from point 2 collapses, but its two ends
    // now go to two points, so the pull-back of a cochain of degree zero has
    // a coboundary there that the pulled-back coboundary lacks.
    let mut tower = tower(Space::Interval, Level::from(1_usize));
    let mut bonded = bonding(Space::Interval, Level::from(1_usize));
    let moved = Cell::Vertex(Point(3));
    let result = tower.push(
        constant(Space::Interval, Level::from(2_usize)),
        oriented,
        |cell: &Cell| {
            if *cell == moved {
                return Image::Onto {
                    cell: Element::from(0_usize),
                    incidence: Incidence::Positive,
                    entries: [Entry::from(0_usize)],
                };
            }
            bonded(cell)
        },
    );
    assert_eq!(
        result,
        Err(SheafError::NotACochainMap {
            level: Level::from(2_usize),
            degree: Rank::from(0_usize),
        })
    );
    assert_eq!(
        tower.cohomology(Level::from(2_usize)).map(|_| ()),
        Err(SheafError::LevelOutside(Level::from(2_usize))),
        "a refused level leaves the tower as it was"
    );
}

#[test]
fn an_edge_sent_onto_a_point_is_refused_by_its_rank()
{
    // Every cell of level 1 of the circle sent onto the point of level 0.
    // The two points go onto a point, and the first edge, cell 2, is refused
    // by its rank: it lies on the point instead of collapsing into it.
    let mut tower = tower(Space::Circle, Level::from(0_usize));
    let result = tower.push(
        constant(Space::Circle, Level::from(1_usize)),
        oriented,
        |_: &Cell| Image::Onto {
            cell: Element::from(0_usize),
            incidence: Incidence::Positive,
            entries: [Entry::from(0_usize)],
        },
    );
    assert_eq!(
        result,
        Err(SheafError::ImageRank {
            cell: Element::from(2_usize),
            image: Element::from(0_usize),
        })
    );
}
