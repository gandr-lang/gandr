//! The check of a scheme as an acyclic matching: the critical cells it keeps,
//! each fault it counts, its budget, and the scheme's own fault.

use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Count;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::MorseError;
use gandr_theory_discrete_morse::collapse;

use crate::simplices::A;
use crate::simplices::AB;
use crate::simplices::ABC;
use crate::simplices::AC;
use crate::simplices::B;
use crate::simplices::BC;
use crate::simplices::C;
use crate::simplices::FILLED;
use crate::simplices::HOLLOW;
use crate::simplices::Refused;
use crate::simplices::Simplex;
use crate::simplices::Triangle;

/// A budget that every walk of the triangle stays within.
const ROOM: usize = 16;

/// The faults with `count` in the field `set` picks and zero elsewhere.
///
/// # Specification
/// trivial.
fn only<Set>(set: Set) -> Faults
where
    Set: FnOnce(&mut Faults),
{
    let mut faults = Faults::default();
    set(&mut faults);
    faults
}

/// The filled triangle matched onto its vertex `a`: `b` with the edge `ab`,
/// `c` with the edge `ac`, and the edge `bc` with the whole triangle.
///
/// # Specification
/// trivial.
fn contracted() -> Triangle
{
    Triangle::matched(&[(B, AB), (C, AC), (BC, ABC)])
}

#[test]
fn the_matching_of_a_triangle_collapses_onto_one_vertex()
{
    let mut scheme = contracted();
    let done = collapse(&mut scheme, &FILLED, Budget::from(ROOM)).expect("the triangle reads");
    assert_eq!(done.critical(), [A]);
    assert_eq!(done.faults(), Faults::default());
    // The walk reaches the three redundant cells and no other.
    assert_eq!(done.visited(), Count::from(3));
}

#[test]
fn a_partner_that_names_another_cell_is_unpaired()
{
    // `b` names `ab`, but `ab` names `a` back, and `a` names nothing. The
    // walk from `b` and the read of `ab` each count one.
    let mut scheme = Triangle::matched(&[(B, AB)]);
    let _was = scheme.classes.insert(AB, Class::Collapsible(A));
    let done = collapse(&mut scheme, &FILLED, Budget::from(ROOM)).expect("the triangle reads");
    assert_eq!(
        done.faults(),
        only(|faults| faults.unpaired = Count::from(2))
    );
}

#[test]
fn a_partner_outside_the_complex_is_counted()
{
    // `b` names a cell over a fourth vertex, which the triangle does not
    // hold. That cell names nothing back either.
    let outside = Simplex(0b1010);
    let mut scheme = Triangle::matched(&[]);
    let _was = scheme.classes.insert(B, Class::Redundant(outside));
    let done = collapse(&mut scheme, &FILLED, Budget::from(ROOM)).expect("the triangle reads");
    assert_eq!(
        done.faults(),
        only(|faults| {
            faults.outside = Count::from(1);
            faults.unpaired = Count::from(1);
        })
    );
}

#[test]
fn an_incidence_of_two_pairs_no_cells()
{
    let mut scheme = Triangle::matched(&[(B, AB)]);
    scheme.weight = 2;
    let done = collapse(&mut scheme, &FILLED, Budget::from(ROOM)).expect("the triangle reads");
    assert_eq!(
        done.faults(),
        only(|faults| faults.uninvertible = Count::from(1))
    );
}

#[test]
fn a_scheme_whose_gradient_turns_back_closes_a_cycle()
{
    // Each vertex pairs with the edge that leaves it, so the gradient runs
    // from `a` to `b` to `c` and back to `a`.
    let mut scheme = Triangle::matched(&[(A, AB), (B, BC), (C, AC)]);
    let done = collapse(&mut scheme, &HOLLOW, Budget::from(ROOM)).expect("the triangle reads");
    assert!(done.critical().is_empty(), "{done:?}");
    assert_eq!(done.faults(), only(|faults| faults.cycles = Count::from(1)));
    // The same pairs less one close no cycle.
    let mut opened = Triangle::matched(&[(A, AB), (B, BC)]);
    let done = collapse(&mut opened, &HOLLOW, Budget::from(ROOM)).expect("the triangle reads");
    assert_eq!(done.critical(), [C, AC]);
    assert_eq!(done.faults(), Faults::default());
}

#[test]
fn a_walk_past_its_budget_is_refused()
{
    let mut scheme = contracted();
    assert_eq!(
        collapse(&mut scheme, &FILLED, Budget::from(2)),
        Err(MorseError::PastBudget(Budget::from(2)))
    );
    let done = collapse(&mut scheme, &FILLED, Budget::from(3)).expect("three cells fit");
    assert_eq!(done.visited(), Count::from(3));
}

#[test]
fn the_walk_goes_past_the_given_cells()
{
    // Given only `b`, the walk goes up to `ab`. Its other face `a` is
    // redundant here, so the walk reaches it too.
    let mut scheme = Triangle::matched(&[(B, AB), (A, AC)]);
    let done = collapse(&mut scheme, &[B], Budget::from(ROOM)).expect("the triangle reads");
    assert_eq!(done.visited(), Count::from(2));
    assert_eq!(done.faults(), Faults::default());
}

#[test]
fn a_fault_of_the_scheme_is_given_back_as_its_own()
{
    let mut scheme = contracted();
    scheme.refuses.push(C);
    assert_eq!(
        collapse(&mut scheme, &FILLED, Budget::from(ROOM)),
        Err(MorseError::Complex(Refused(C)))
    );
}
