//! Sheaves of linear maps: the projective line's twist by minus two through
//! matrices, a gluing through a twist by one half, and the refusals of a
//! matrix of another shape and of maps that do not compose.

use gandr_theory_cellular_sheaves::CoverIndex;
use gandr_theory_cellular_sheaves::Dimension;
use gandr_theory_cellular_sheaves::Entry;
use gandr_theory_cellular_sheaves::Gluing;
use gandr_theory_cellular_sheaves::Incidence;
use gandr_theory_cellular_sheaves::LinearMaps;
use gandr_theory_cellular_sheaves::Matrix;
use gandr_theory_cellular_sheaves::Obstruction;
use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_cellular_sheaves::Restriction;
use gandr_theory_cellular_sheaves::Sheaf;
use gandr_theory_cellular_sheaves::SheafError;
use gandr_theory_cellular_sheaves::Width;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_graded_posets::Rank;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;

/// A cell of the projective line's cover: one of its two charts, or their
/// overlap.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Chart
{
    /// The chart where the first coordinate is not zero, with the coordinate
    /// `x`.
    First,
    /// The chart where the second coordinate is not zero, with the coordinate
    /// `y`, which is `x⁻¹` on the overlap.
    Second,
    /// The overlap of the two charts.
    Overlap,
}

/// A cell of a chain of three cells, each below the next.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Flag
{
    /// The lowest cell.
    Point,
    /// The middle cell.
    Edge,
    /// The highest cell.
    Face,
}

/// A cell of the circle of three points: a point, or the edge from its tail
/// to its head, the next point.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Round
{
    /// A point, numbered from zero.
    Point(usize),
    /// The edge from the first point to the second.
    Edge(usize, usize),
}

/// One nonzero entry of a matrix.
#[derive(Clone, Copy, Debug)]
struct Term
{
    /// The row: an entry of the upper stalk.
    row: Entry,
    /// The column: an entry of the lower stalk.
    column: Entry,
    /// The value at the row and the column.
    value: Rational,
}

/// The matrix of `rows` rows and `columns` columns with each of `terms`, and
/// zeros elsewhere.
///
/// # Specification
/// trivial.
fn filled(
    rows: Dimension,
    columns: Dimension,
    terms: &[Term],
) -> Matrix
{
    let values = (0 .. usize::from(rows)).flat_map(|row| {
        (0 .. usize::from(columns)).map(move |column| {
            terms
                .iter()
                .find(|term| usize::from(term.row) == row && usize::from(term.column) == column)
                .map_or(Rational::ZERO, |term| term.value)
        })
    });
    Matrix::new(rows, columns, values).expect("a matrix of its shape")
}

/// The matrix of `$rows` rows and `$columns` columns with the value `$value`
/// at each `($row, $column, $value)`, and zeros elsewhere.
macro_rules! matrix {
    ($rows:expr, $columns:expr; $(($row:expr, $column:expr, $value:expr)),* $(,)?) => {{
        let rows: usize = $rows;
        let columns: usize = $columns;
        let terms: Vec<Term> = vec![$({
            let row: usize = $row;
            let column: usize = $column;
            Term {
                row: Entry::from(row),
                column: Entry::from(column),
                value: $value,
            }
        }),*];
        filled(Dimension::from(rows), Dimension::from(columns), &terms)
    }};
}

/// The projective line's cover: the two charts, cells 0 and 1, below their
/// overlap, cell 2.
///
/// # Specification
/// trivial.
fn charts() -> GradedPoset<Chart>
{
    GradedPoset::new(
        vec![Chart::First, Chart::Second, Chart::Overlap],
        |lower, upper| match (*lower, *upper) {
            (Chart::First | Chart::Second, Chart::Overlap) => Comparison::Below,
            (
                Chart::First | Chart::Second | Chart::Overlap,
                Chart::First | Chart::Second | Chart::Overlap,
            ) => Comparison::NotBelow,
        },
        ElementCount::from(3_usize),
    )
    .expect("three cells")
}

/// The width of a chart's stalk, two, and of the overlap's stalk, five: the
/// polynomials of each chart cut at degree one, and the Laurent monomials
/// from `x⁻³` to `x` on the overlap.
///
/// # Specification
/// trivial.
fn cut(cell: Chart) -> Width
{
    match cell {
        Chart::First | Chart::Second => Width::from(2_usize),
        Chart::Overlap => Width::from(5_usize),
    }
}

/// The twist by minus two of the projective line, `O(−2)`, on its two charts.
/// The first chart's stalk holds `1` and `x`, the second chart's `1` and `y`,
/// and the overlap's `x⁻³`, `x⁻²`, `x⁻¹`, `1` and `x`, in that order. The
/// first chart includes each monomial. The second sends `yᵏ` to `x⁻²⁻ᵏ`, the
/// transition of the twist. Neither map reads anything at `x⁻¹`, so no entry
/// map states them.
///
/// # Specification
/// trivial.
fn twisted() -> Sheaf<Chart, LinearMaps>
{
    let one = Rational::ONE;
    Sheaf::linear(
        charts(),
        |cell| cut(*cell),
        |lower, _| {
            Restriction::<Vec<Entry>>::Matrix(if *lower == Chart::Second {
                matrix!(5, 2; (1, 0, one), (0, 1, one))
            }
            else {
                matrix!(5, 2; (3, 0, one), (4, 1, one))
            })
        },
    )
    .expect("the twist's maps compose")
}

/// The first chart positive and the second negative in the overlap.
///
/// # Specification
/// trivial.
fn across(face: Chart) -> Incidence
{
    if face == Chart::First {
        Incidence::Positive
    }
    else {
        Incidence::Negative
    }
}

/// The chain of a point, an edge and a face, each below the next.
///
/// # Specification
/// trivial.
fn chain() -> GradedPoset<Flag>
{
    GradedPoset::new(
        vec![Flag::Point, Flag::Edge, Flag::Face],
        |lower, upper| match (*lower, *upper) {
            (Flag::Point, Flag::Edge | Flag::Face) | (Flag::Edge, Flag::Face) => Comparison::Below,
            (Flag::Point | Flag::Edge | Flag::Face, Flag::Point | Flag::Edge | Flag::Face) => {
                Comparison::NotBelow
            },
        },
        ElementCount::from(3_usize),
    )
    .expect("three cells")
}

/// The sheaf on the chain, each stalk of width two. The map from the point to
/// the edge is the matrix that doubles the first entry, and the map from the
/// edge to the face the entry map that swaps the two entries. The map from
/// the point to the face is `direct`.
///
/// # Specification
/// trivial.
fn flag(direct: &Matrix) -> Result<Sheaf<Flag, LinearMaps>, SheafError>
{
    let poset = chain();
    let one = Rational::ONE;
    let two = rational!(2, 1);
    Sheaf::linear(
        poset,
        |_| Width::from(2_usize),
        |lower, upper| match (*lower, *upper) {
            (Flag::Point, Flag::Edge) => {
                Restriction::Matrix(matrix!(2, 2; (0, 0, two), (1, 1, one)))
            },
            (Flag::Point, Flag::Point | Flag::Face) => Restriction::Matrix(direct.clone()),
            (Flag::Edge | Flag::Face, Flag::Point | Flag::Edge | Flag::Face) => {
                Restriction::Entries(vec![Entry::from(1_usize), Entry::from(0_usize)])
            },
        },
    )
}

#[test]
fn the_projective_line_s_twist_by_minus_two_has_one_class_in_degree_one()
{
    // `H⁰(P¹, O(−2)) = 0` and `H¹(P¹, O(−2))` has rank one. The four chart
    // monomials reach four distinct overlap monomials, so the coboundary from
    // degree zero has rank four on five rows.
    let complex = twisted()
        .cochains(|face, _| across(*face))
        .expect("the cover is a complex");
    let cohomology = complex.cohomology().expect("the cohomology");
    assert_eq!(
        [0_usize, 1].map(|degree| cohomology.dimension(Rank::from(degree))),
        [0_usize, 1].map(Dimension::from)
    );
    // The coboundary holds each chart's matrix with the sign of its
    // incidence: its columns are the first chart's `1` and `x`, then the
    // second chart's `1` and `y`.
    let (one, minus) = (Rational::ONE, rational!(-1, 1));
    let coboundary = matrix!(5, 4; (0, 3, minus), (1, 2, minus), (3, 0, one), (4, 1, one));
    assert_eq!(
        complex
            .coboundary(Rank::from(0_usize))
            .expect("degree zero"),
        &coboundary
    );
    // The class is `x⁻¹`, the cocycle `1/(X₀X₁)`; in the second chart's
    // frame it reads `y⁻¹`, which is `x`. Its column raises the rank, so no
    // section of the charts reaches it. The column of `1` does not, since
    // the first chart's `1` reaches it.
    let inverse =
        matrix!(5, 5; (0, 3, minus), (1, 2, minus), (3, 0, one), (4, 1, one), (2, 4, one));
    let unit = matrix!(5, 5; (0, 3, minus), (1, 2, minus), (3, 0, one), (4, 1, one), (3, 4, one));
    assert_eq!(
        (inverse.rank(), unit.rank()),
        (Ok(Dimension::from(5_usize)), Ok(Dimension::from(4_usize)))
    );
}

#[test]
fn a_matrix_of_another_number_of_entries_is_refused()
{
    let refused = Err(SheafError::MatrixEntries {
        rows: Dimension::from(2_usize),
        columns: Dimension::from(2_usize),
    });
    for count in [3_usize, 5] {
        let entries = core::iter::repeat_n(Rational::ONE, count);
        let made = Matrix::new(Dimension::from(2_usize), Dimension::from(2_usize), entries);
        assert_eq!(made, refused);
    }
}

#[test]
fn a_matrix_of_another_shape_is_refused()
{
    // The first pair is the first chart below the overlap, whose stalks have
    // two entries and five.
    let (first, overlap) = (Element::from(0_usize), Element::from(2_usize));
    let short = Sheaf::linear(
        charts(),
        |cell| cut(*cell),
        |_, _| Restriction::<Vec<Entry>>::Matrix(matrix!(4, 2;)),
    );
    assert_eq!(
        short.map(|_| ()),
        Err(SheafError::RestrictionWidth {
            lower: first,
            upper: overlap,
            width: Width::from(4_usize),
        })
    );
    let wide = Sheaf::linear(
        charts(),
        |cell| cut(*cell),
        |_, _| Restriction::<Vec<Entry>>::Matrix(matrix!(5, 3;)),
    );
    assert_eq!(
        wide.map(|_| ()),
        Err(SheafError::RestrictionColumns {
            lower: first,
            upper: overlap,
            columns: Dimension::from(3_usize),
        })
    );
}

#[test]
fn matrices_that_do_not_compose_are_refused()
{
    // Through the edge, the point's first entry doubles and the two entries
    // swap: the composite sends the point's `(a, b)` to `(b, 2a)`.
    let one = Rational::ONE;
    let composite = matrix!(2, 2; (0, 1, one), (1, 0, rational!(2, 1)));
    assert!(flag(&composite).is_ok());
    // A direct map that doubles the composite's entry of the second row
    // differs from it at the face's second entry.
    let doubled = matrix!(2, 2; (0, 1, one), (1, 0, rational!(4, 1)));
    assert_eq!(
        flag(&doubled).map(|_| ()),
        Err(SheafError::NotFunctorial {
            lower: Element::from(0_usize),
            middle: Element::from(1_usize),
            upper: Element::from(2_usize),
            entry: Entry::from(1_usize),
        })
    );
}

#[test]
fn a_section_glues_through_a_matrix_where_its_scaled_values_agree()
{
    // The second chart reaches the overlap through a twist by one half, and
    // the first through the entry map that keeps its one entry.
    let sheaf = Sheaf::linear(
        charts(),
        |_| Width::from(1_usize),
        |lower, _| {
            if *lower == Chart::Second {
                Restriction::Matrix(matrix!(1, 1; (0, 0, rational!(1, 2))))
            }
            else {
                Restriction::Entries(vec![Entry::from(0_usize)])
            }
        },
    )
    .expect("one map into the overlap from each chart");
    let (first, second, overlap) = (
        Element::from(0_usize),
        Element::from(1_usize),
        Element::from(2_usize),
    );
    let (six, three, four) = ([rational!(6, 1)], [rational!(3, 1)], [rational!(4, 1)]);
    // Six halved is three, so the charts glue. The second chart comes first,
    // so the overlap holds its halved value.
    let glued = sheaf
        .glue(&[(second, &six[..]), (first, &three[..])])
        .expect("a cover of the two charts");
    let Gluing::Glued(ref section) = glued
    else {
        panic!("six halved is three, yet the charts are obstructed: {glued:?}");
    };
    assert_eq!(section.at(overlap).expect("the overlap"), &three);
    assert_eq!(section.at(second).expect("the second chart"), &six);
    // Six halved is not four, so the charts part at the overlap's one entry.
    let parted = sheaf
        .glue(&[(second, &six[..]), (first, &four[..])])
        .expect("a cover of the two charts");
    assert_eq!(
        parted,
        Gluing::Obstructed(vec![Obstruction {
            members: (CoverIndex::from(0_usize), CoverIndex::from(1_usize)),
            overlap,
            entry: Entry::from(0_usize),
        }])
    );
}

/// The circle of three points and three edges, the points first.
///
/// # Specification
/// trivial.
fn circle() -> GradedPoset<Round>
{
    let edges = [Round::Edge(0, 1), Round::Edge(1, 2), Round::Edge(2, 0)];
    let cells: Vec<Round> = (0 .. 3).map(Round::Point).chain(edges).collect();
    GradedPoset::new(
        cells,
        |lower, upper| match (*lower, *upper) {
            (Round::Point(point), Round::Edge(tail, head)) if point == tail || point == head => {
                Comparison::Below
            },
            (Round::Point(_) | Round::Edge(..), Round::Point(_) | Round::Edge(..)) => {
                Comparison::NotBelow
            },
        },
        ElementCount::from(6_usize),
    )
    .expect("six cells")
}

/// The entry map from `lower` into `upper` of the twisted circle: the first
/// point's two entries swap into the last edge, and every other map keeps
/// them.
///
/// # Specification
/// trivial.
fn twist(
    lower: &Round,
    upper: &Round,
) -> [Entry; 2]
{
    if *lower == Round::Point(0) && *upper == Round::Edge(2, 0) {
        [Entry::from(1_usize), Entry::from(0_usize)]
    }
    else {
        [Entry::from(0_usize), Entry::from(1_usize)]
    }
}

/// The matrix of the entry map `map` between two stalks of two entries: a one
/// at the row of each entry and the column of the entry it reads.
///
/// # Specification
/// trivial.
fn as_matrix(map: [Entry; 2]) -> Matrix
{
    let ones: Vec<Term> = map
        .iter()
        .enumerate()
        .map(|(row, &read)| Term {
            row: Entry::from(row),
            column: read,
            value: Rational::ONE,
        })
        .collect();
    filled(Dimension::from(2_usize), Dimension::from(2_usize), &ones)
}

/// The incidence of a point in an edge: positive at its head and negative at
/// its tail.
///
/// # Specification
/// trivial.
fn around(
    face: &Round,
    cell: &Round,
) -> Incidence
{
    match (*face, *cell) {
        (Round::Point(point), Round::Edge(_, head)) if point == head => Incidence::Positive,
        (Round::Point(_), Round::Edge(..)) => Incidence::Negative,
        (Round::Point(_) | Round::Edge(..), Round::Point(_) | Round::Edge(..)) => Incidence::Zero,
    }
}

#[test]
fn each_entry_map_and_its_matrix_give_one_coboundary()
{
    // The circle of three points with stalks of two entries, twisted once.
    // Its entry maps, the same maps as matrices, and the same entry maps in a
    // sheaf of linear maps give one cochain complex. A section keeps its two
    // entries equal, so each degree has one class.
    let width = |_: &Round| Width::from(2_usize);
    let entries = Sheaf::new(circle(), width, twist).expect("the entry maps compose");
    let matrices = Sheaf::linear(circle(), width, |lower, upper| {
        Restriction::<Vec<Entry>>::Matrix(as_matrix(twist(lower, upper)))
    })
    .expect("the matrices compose");
    let read = Sheaf::linear(circle(), width, |lower, upper| {
        Restriction::Entries(twist(lower, upper))
    })
    .expect("the entry maps compose");
    let complex = entries.cochains(around).expect("the circle is a complex");
    assert_eq!(matrices.cochains(around), Ok(complex.clone()));
    assert_eq!(read.cochains(around), Ok(complex.clone()));
    let cohomology = complex.cohomology().expect("the cohomology");
    assert_eq!(
        [0_usize, 1].map(|degree| cohomology.dimension(Rank::from(degree))),
        [1_usize, 1].map(Dimension::from)
    );
}
