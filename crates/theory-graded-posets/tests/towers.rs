//! Probe 17 of the presented-spaces frame: the cohomology of the interval
//! and the circle through their finite towers.
//!
//! Level `n` of the interval's tower is the path graph on `2ⁿ` points. Level
//! `n` of the circle's tower closes that path into a cycle. Each level is a
//! graded poset whose cells are its points and its edges, an edge above its
//! two ends. A constant sheaf over the rationals puts one copy of the
//! rationals on each cell, and each restriction is the identity. Its cochains
//! of degree zero are a value at each point, those of degree one a value at
//! each edge. The coboundary of a cochain of degree zero gives each edge the
//! value at its head less the value at its tail.
//!
//! The bonding map of the tower sends level `n + 1` to level `n`: point `j`
//! goes to point `j / 2`. The edge from point `2i` lies inside a pair and
//! goes to point `i`. The edge from point `2i + 1` joins two pairs and goes
//! to the edge from point `i`, the circle's loop at level zero among them.
//! Its pull-back on cochains commutes with the coboundary, so it
//! induces a map on cohomology. The probe checks that this map is an
//! isomorphism at each level, and that the cohomology is the rationals in
//! degree zero, and in degree one for the circle alone.
//!
//! The graded poset holds at most 64 cells, so the tower stops at level 5:
//! 63 cells for the interval and 64 for the circle. Level 6 is refused by its
//! count.

use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_graded_posets::Rank;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;

/// The last level the graded poset holds.
const LAST_LEVEL: u32 = 5;

/// A point of a level, numbered from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Point(u32);

/// A cell of a level.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Cell
{
    /// A point.
    Vertex(Point),
    /// An edge from its tail to its head.
    Edge(Point, Point),
}

/// The space a tower presents.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Space
{
    /// The interval: each level a path.
    Interval,
    /// The circle: each level a cycle.
    Circle,
}

/// A level of a tower.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Level(u32);

/// The number of points of a level.
///
/// # Specification
/// trivial.
fn points(level: Level) -> Point
{
    Point(1_u32.checked_shl(level.0).expect("a small level"))
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
fn poset(
    space: Space,
    level: Level,
) -> Result<GradedPoset<Cell>, DualityError>
{
    GradedPoset::new(cells(space, level), |lower, upper| match (*lower, *upper) {
        (Cell::Vertex(point), Cell::Edge(tail, head)) if point == tail || point == head => {
            Comparison::Below
        },
        (Cell::Vertex(_) | Cell::Edge(..), Cell::Vertex(_) | Cell::Edge(..)) => {
            Comparison::NotBelow
        },
    })
}

/// A rational entry of a matrix, held as an integer: every entry here is an
/// integer.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Entry(i64);

/// A matrix by its columns, each of `rows` entries.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Matrix
{
    /// The number of rows.
    rows: usize,
    /// The columns.
    columns: Vec<Vec<Entry>>,
}

/// The rank of `matrix` over the rationals, by fraction-free elimination.
///
/// # Specification
/// trivial.
fn rank(matrix: &Matrix) -> Rank
{
    let width = matrix.columns.len();
    let mut rows: Vec<Vec<i128>> = (0 .. matrix.rows)
        .map(|row| {
            matrix
                .columns
                .iter()
                .map(|column| i128::from(column.get(row).copied().unwrap_or_default().0))
                .collect()
        })
        .collect();
    let mut found = 0_usize;
    let mut previous: i128 = 1;
    for column in 0 .. width {
        let Some(pivot) = (found .. matrix.rows).find(|&row| rows[row][column] != 0)
        else {
            continue;
        };
        rows.swap(found, pivot);
        for row in found.saturating_add(1) .. matrix.rows {
            for other in column.saturating_add(1) .. width {
                let value = rows[found][column]
                    .checked_mul(rows[row][other])
                    .and_then(|kept| {
                        kept.checked_sub(rows[row][column].checked_mul(rows[found][other])?)
                    })
                    .and_then(|value| value.checked_div(previous))
                    .expect("the entries stay small");
                rows[row][other] = value;
            }
            rows[row][column] = 0;
        }
        previous = rows[found][column];
        found = found.saturating_add(1);
    }
    Rank::from(found)
}

/// The cells of `poset` of rank `rank`, in cell order.
///
/// # Specification
/// trivial.
fn of_rank(
    poset: &GradedPoset<Cell>,
    rank: Rank,
) -> Vec<Element>
{
    (0 .. usize::from(poset.count()))
        .map(Element::from)
        .filter(|&cell| poset.rank(cell) == Ok(rank))
        .collect()
}

/// The coboundary of the constant sheaf on `poset`, from the cochains of
/// degree zero to those of degree one: one column per point, one row per
/// edge. An edge's faces come from the poset, and the sign of each from the
/// edge's direction.
///
/// # Specification
/// trivial.
fn coboundary(poset: &GradedPoset<Cell>) -> Matrix
{
    let (vertices, edges) = (
        of_rank(poset, Rank::from(0_usize)),
        of_rank(poset, Rank::from(1_usize)),
    );
    let mut column_of: Vec<Option<usize>> = vec![None; usize::from(poset.count())];
    for (column, &vertex) in vertices.iter().enumerate() {
        column_of[usize::from(vertex)] = Some(column);
    }
    let mut columns = vec![vec![Entry::default(); edges.len()]; vertices.len()];
    for (row, &edge) in edges.iter().enumerate() {
        let Some(&Cell::Edge(tail, head)) = poset.cells().get(usize::from(edge))
        else {
            panic!("a cell of rank one is an edge");
        };
        let faces = poset.boundary(edge).expect("a cell of the poset");
        for face in faces.elements() {
            let (Some(&Cell::Vertex(point)), Some(column)) = (
                poset.cells().get(usize::from(face)),
                column_of[usize::from(face)],
            )
            else {
                panic!("a face of an edge is a point");
            };
            let sign = i64::from(point == head).saturating_sub(i64::from(point == tail));
            columns[column][row] = Entry(sign);
        }
    }
    Matrix {
        rows: edges.len(),
        columns,
    }
}

/// The cohomology of the constant sheaf on a level, by degree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Cohomology
{
    /// The dimension in degree zero.
    zero: Rank,
    /// The dimension in degree one.
    one: Rank,
}

/// The cohomology of the constant sheaf on `poset`.
///
/// # Specification
/// trivial.
fn cohomology(poset: &GradedPoset<Cell>) -> Cohomology
{
    let delta = coboundary(poset);
    let image = usize::from(rank(&delta));
    Cohomology {
        zero: Rank::from(delta.columns.len().saturating_sub(image)),
        one: Rank::from(delta.rows.saturating_sub(image)),
    }
}

/// The pull-back along the bonding map from level `upper` to the level below
/// it, of `space`'s tower: in degree zero, one column per point of the lower
/// level and one row per point of the upper; in degree one, the same for the
/// edges. Point `j` goes to point `j / 2`. The edge from an even point goes to
/// a point, and so contributes nothing in degree one. The edge from point
/// `2i + 1` goes to the edge from point `i`.
///
/// # Specification
/// trivial.
fn pull_back(
    space: Space,
    upper: Level,
) -> (Matrix, Matrix)
{
    let lower = Level(upper.0.saturating_sub(1));
    let (above, below) = (cells(space, upper), cells(space, lower));
    let points_above: Vec<Point> = above
        .iter()
        .filter_map(|cell| match *cell {
            Cell::Vertex(point) => Some(point),
            Cell::Edge(..) => None,
        })
        .collect();
    let edges_above: Vec<(Point, Point)> = above
        .iter()
        .filter_map(|cell| match *cell {
            Cell::Edge(tail, head) => Some((tail, head)),
            Cell::Vertex(_) => None,
        })
        .collect();
    let edges_below: Vec<(Point, Point)> = below
        .iter()
        .filter_map(|cell| match *cell {
            Cell::Edge(tail, head) => Some((tail, head)),
            Cell::Vertex(_) => None,
        })
        .collect();
    let count_below = usize::try_from(points(lower).0).expect("a small level");
    let half = |point: Point| Point(point.0 >> 1_u32);
    let mut zero = Matrix {
        rows: points_above.len(),
        columns: vec![vec![Entry::default(); points_above.len()]; count_below],
    };
    for (row, &point) in points_above.iter().enumerate() {
        let column = usize::try_from(half(point).0).expect("a small level");
        zero.columns[column][row] = Entry(1);
    }
    let mut one = Matrix {
        rows: edges_above.len(),
        columns: vec![vec![Entry::default(); edges_above.len()]; edges_below.len()],
    };
    for (row, &(tail, head)) in edges_above.iter().enumerate() {
        if tail.0 % 2 == 0 {
            continue;
        }
        let image = (half(tail), half(head));
        let column = edges_below
            .binary_search_by_key(&image.0.0, |&(below_tail, _)| below_tail.0)
            .expect("the image of an edge is an edge");
        assert_eq!(
            edges_below[column], image,
            "the image of {tail:?} to {head:?}"
        );
        one.columns[column][row] = Entry(1);
    }
    (zero, one)
}

/// The product of two matrices.
///
/// # Specification
/// trivial.
fn product(
    left: &Matrix,
    right: &Matrix,
) -> Matrix
{
    Matrix {
        rows: left.rows,
        columns: right
            .columns
            .iter()
            .map(|column| {
                (0 .. left.rows)
                    .map(|row| {
                        Entry(
                            left.columns
                                .iter()
                                .zip(column)
                                .map(|(through, scale)| through[row].0.saturating_mul(scale.0))
                                .fold(0_i64, i64::saturating_add),
                        )
                    })
                    .collect()
            })
            .collect(),
    }
}

/// The two towers, by name.
const SPACES: [Space; 2] = [Space::Interval, Space::Circle];

#[test]
fn the_circles_level_of_four_points_has_the_rationals_in_degrees_zero_and_one()
{
    // Four points and four edges in a cycle. The coboundary takes a value at
    // each point to the four differences around the cycle. A constant is its
    // kernel, so degree zero is the rationals. The four differences sum to
    // zero, so its image has dimension three, and degree one is the
    // rationals.
    let poset = poset(Space::Circle, Level(2)).expect("eight cells");
    assert_eq!(poset.count(), ElementCount::from(8_usize));
    let delta = coboundary(&poset);
    assert_eq!((delta.rows, delta.columns.len()), (4, 4));
    assert_eq!(usize::from(rank(&delta)), 3);
    assert_eq!(cohomology(&poset), Cohomology {
        zero: Rank::from(1_usize),
        one: Rank::from(1_usize),
    });
}

#[test]
fn every_level_of_both_towers_has_the_cohomology_of_its_space()
{
    for space in SPACES {
        for level in 0 ..= LAST_LEVEL {
            let poset = poset(space, Level(level)).expect("a level the poset holds");
            let expected = Cohomology {
                zero: Rank::from(1_usize),
                one: Rank::from(usize::from(space == Space::Circle)),
            };
            assert_eq!(cohomology(&poset), expected, "{space:?} at level {level}");
        }
    }
}

#[test]
fn each_bonding_map_induces_an_isomorphism_on_cohomology()
{
    for space in SPACES {
        for level in 1 ..= LAST_LEVEL {
            let (upper, lower) = (
                poset(space, Level(level)).expect("the upper level"),
                poset(space, Level(level.saturating_sub(1))).expect("the lower level"),
            );
            let (zero, one) = pull_back(space, Level(level));
            let (delta_upper, delta_lower) = (coboundary(&upper), coboundary(&lower));
            assert_eq!(
                product(&delta_upper, &zero),
                product(&one, &delta_lower),
                "{space:?} at level {level}: the pull-back commutes with the coboundary"
            );
            assert_eq!(
                cohomology(&upper),
                cohomology(&lower),
                "{space:?} at level {level}: the dimensions agree"
            );
            // Degree zero: the pull-back is one to one on the points, so on
            // the constants.
            assert_eq!(
                usize::from(rank(&zero)),
                zero.columns.len(),
                "{space:?} at level {level}"
            );
            // Degree one: the image of the pull-back with the coboundaries
            // spans every cochain, so the map onto the upper cohomology is
            // onto, and with equal dimensions it is one to one.
            let spanned = Matrix {
                rows: one.rows,
                columns: delta_upper
                    .columns
                    .iter()
                    .chain(&one.columns)
                    .cloned()
                    .collect(),
            };
            assert_eq!(
                usize::from(rank(&spanned)),
                one.rows,
                "{space:?} at level {level}"
            );
        }
    }
}

#[test]
fn the_level_past_the_cell_budget_is_refused_by_its_count()
{
    // Level 6 has 64 points: 127 cells for the interval and 128 for the
    // circle, past the poset's 64.
    assert_eq!(
        poset(Space::Interval, Level(LAST_LEVEL + 1)).map(|poset| poset.count()),
        Err(DualityError::TooManyElements(ElementCount::from(127_usize)))
    );
    assert_eq!(
        poset(Space::Circle, Level(LAST_LEVEL + 1)).map(|poset| poset.count()),
        Err(DualityError::TooManyElements(ElementCount::from(128_usize)))
    );
}
