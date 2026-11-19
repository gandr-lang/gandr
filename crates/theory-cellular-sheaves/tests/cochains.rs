//! The cochain complex of a filled square: its incidences admitted as a
//! complex or refused.

use gandr_theory_cellular_sheaves::Dimension;
use gandr_theory_cellular_sheaves::Entry;
use gandr_theory_cellular_sheaves::Incidence;
use gandr_theory_cellular_sheaves::Sheaf;
use gandr_theory_cellular_sheaves::SheafError;
use gandr_theory_cellular_sheaves::Width;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_graded_posets::Rank;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::ElementCount;

/// A cell of the filled square: a corner, a side from its tail to its head,
/// or the square itself.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Cell
{
    /// A corner, numbered around the square.
    Corner(usize),
    /// A side from the first corner to the second.
    Side(usize, usize),
    /// The square.
    Square,
}

/// The constant sheaf on the filled square: four corners, four sides around
/// them and the square above all of them.
///
/// # Specification
/// trivial.
fn square() -> Sheaf<Cell>
{
    let mut cells: Vec<Cell> = (0 .. 4).map(Cell::Corner).collect();
    cells.extend((0 .. 4_usize).map(|tail| {
        let head = tail.saturating_add(1).checked_rem(4).expect("four corners");
        Cell::Side(tail, head)
    }));
    cells.push(Cell::Square);
    let poset = GradedPoset::new(
        cells,
        |lower, upper| match (*lower, *upper) {
            (Cell::Corner(corner), Cell::Side(tail, head)) if corner == tail || corner == head => {
                Comparison::Below
            },
            (Cell::Corner(_) | Cell::Side(..), Cell::Square) => Comparison::Below,
            (
                Cell::Corner(_) | Cell::Side(..) | Cell::Square,
                Cell::Corner(_) | Cell::Side(..) | Cell::Square,
            ) => Comparison::NotBelow,
        },
        ElementCount::from(9_usize),
    )
    .expect("nine cells");
    Sheaf::new(
        poset,
        |_| Width::from(1_usize),
        |_, _| [Entry::from(0_usize)],
    )
    .expect("the constant sheaf")
}

/// The incidences of the square's boundary: a corner positive at the head of
/// a side and negative at its tail, and each side positive in the square,
/// as the sides run around it.
///
/// # Specification
/// trivial.
fn boundary(
    face: &Cell,
    cell: &Cell,
) -> Incidence
{
    match (*face, *cell) {
        (Cell::Corner(corner), Cell::Side(_, head)) if corner == head => Incidence::Positive,
        (Cell::Corner(_), Cell::Side(..)) => Incidence::Negative,
        (Cell::Side(..), Cell::Square) => Incidence::Positive,
        (
            Cell::Corner(_) | Cell::Side(..) | Cell::Square,
            Cell::Corner(_) | Cell::Side(..) | Cell::Square,
        ) => Incidence::Zero,
    }
}

#[test]
fn a_square_oriented_as_a_complex_is_contractible()
{
    // The filled square is contractible: the rationals in degree zero, and
    // nothing in degrees one and two.
    let complex = square()
        .cochains(boundary)
        .expect("the square's boundary is a complex");
    let cohomology = complex.cohomology().expect("the cohomology");
    let dimensions: Vec<Dimension> = (0 ..= 2_usize)
        .map(|degree| cohomology.dimension(Rank::from(degree)))
        .collect();
    assert_eq!(dimensions, [1_usize, 0, 0].map(Dimension::from));
    let into_square = complex.coboundary(Rank::from(1_usize)).expect("degree one");
    assert_eq!(
        (into_square.rows(), into_square.columns()),
        (Dimension::from(1_usize), Dimension::from(4_usize))
    );
}

#[test]
fn a_square_with_every_incidence_positive_is_refused()
{
    // With every incidence positive, a corner reaches the square through its
    // two sides with the same sign, so the two coboundaries from degree zero
    // compose to twice that corner's value.
    let refused = square().cochains(|_: &Cell, _: &Cell| Incidence::Positive);
    assert_eq!(
        refused.map(|_| ()),
        Err(SheafError::NotAComplex(Rank::from(0_usize)))
    );
}
