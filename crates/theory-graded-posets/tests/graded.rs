//! The graded poset's own refusals, ranks and boundaries.

use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_graded_posets::Rank;
use gandr_theory_stone_duality::Budget;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::ElementSet;

use crate::faces::Points;
use crate::faces::face_poset;
use crate::faces::square;

#[test]
fn a_square_ranks_its_cells_by_their_longest_chain()
{
    // In mask order over `bl, br, tl, tr`: the bottom side, the corner `tl`,
    // the left side, the right side, the top side and the whole square. The
    // left and top sides hold the corner, so they rank one. The bottom and
    // right sides hold no cell and rank zero, so the whole square covers cells
    // of two ranks.
    let square = square();
    let poset = face_poset(square.carrier, &square.faces);
    let cells: Vec<u64> = poset.cells().iter().map(|cell| cell.0).collect();
    assert_eq!(cells, [0b0011, 0b0100, 0b0101, 0b1010, 0b1100, 0b1111]);
    let ranks: Vec<Rank> = (0 .. 6_usize)
        .map(|cell| poset.rank(Element::from(cell)).expect("a cell"))
        .collect();
    assert_eq!(ranks, [0_usize, 0, 1, 0, 1, 2].map(Rank::from));
    let boundaries: Vec<u64> = (0 .. 6_usize)
        .map(|cell| u64::from(poset.boundary(Element::from(cell)).expect("a cell")))
        .collect();
    assert_eq!(
        boundaries,
        [0b0_0000, 0b0_0000, 0b0_0010, 0b0_0000, 0b0_0010, 0b1_1111],
        "a side holds the corner or nothing, and the whole holds every other cell"
    );
    assert_eq!(
        poset.rank(Element::from(6_usize)),
        Err(DualityError::ElementOutside(Element::from(6_usize)))
    );
}

#[test]
fn a_poset_past_the_cell_budget_is_refused_uncomputed()
{
    let mut calls = 0_usize;
    let refused = GradedPoset::new(vec![(); 65], |&(), &()| {
        calls = calls.saturating_add(1);
        Comparison::NotBelow
    });
    assert_eq!(
        refused,
        Err(DualityError::TooManyElements(ElementCount::from(65_usize)))
    );
    assert_eq!(calls, 0, "no order is computed past the budget");
    let widest =
        GradedPoset::new(vec![(); 64], |&(), &()| Comparison::NotBelow).expect("64 cells fit");
    assert_eq!(widest.count(), ElementCount::from(64_usize));
}

#[test]
fn two_cells_each_below_the_other_are_refused()
{
    let face = Points(0b01);
    assert_eq!(
        GradedPoset::new(vec![face, Points(0b10), face], |lower, upper| lower
            .within(*upper)),
        Err(DualityError::Cycle(
            Element::from(0_usize),
            Element::from(2_usize)
        ))
    );
}

#[test]
fn a_lattice_past_its_budget_is_refused()
{
    let square = square();
    let poset = face_poset(square.carrier, &square.faces);
    assert_eq!(
        poset.subcomplexes(Budget::from(20_usize)),
        Err(DualityError::PastBudget(Budget::from(20_usize)))
    );
    assert_eq!(
        poset.read_back(Budget::from(20_usize)),
        Err(DualityError::PastBudget(Budget::from(20_usize)))
    );
    let lattice = poset
        .subcomplexes(Budget::from(21_usize))
        .expect("21 subcomplexes fit a budget of 21");
    assert_eq!(lattice.members().len(), 21);
    assert_eq!(lattice.members().first(), Some(&ElementSet::EMPTY));
}
