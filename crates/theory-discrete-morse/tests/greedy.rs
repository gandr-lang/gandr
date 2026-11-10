//! The greedy matching on the triangle: the pairs it keeps, the pairs it
//! refuses because they close a cycle, and the faces it cannot pair.

use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::collapse;
use gandr_theory_discrete_morse::greedy;

use crate::simplices::A;
use crate::simplices::AB;
use crate::simplices::ABC;
use crate::simplices::AC;
use crate::simplices::B;
use crate::simplices::BC;
use crate::simplices::C;
use crate::simplices::FILLED;
use crate::simplices::HOLLOW;
use crate::simplices::Simplex;
use crate::simplices::Triangle;

#[test]
fn the_triangle_matches_onto_one_vertex()
{
    let mut complex = Triangle::default();
    let matching = greedy(&mut complex, &FILLED).expect("the triangle reads");
    // `a` pairs with `ab` and `b` with `bc`. The pair of `c` and `ac` would
    // close a cycle through `a` and `b`, so `ac` pairs with the triangle.
    assert_eq!(matching.classes(), [
        Class::Redundant(AB),
        Class::Redundant(BC),
        Class::Critical,
        Class::Collapsible(A),
        Class::Redundant(ABC),
        Class::Collapsible(B),
        Class::Collapsible(AC),
    ]);
    assert_eq!(matching.critical().copied().collect::<Vec<_>>(), [C]);
    let checked = collapse(
        &mut matching.on(&mut complex),
        &FILLED,
        Budget::from(FILLED.len()),
    )
    .expect("the triangle reads");
    assert_eq!(checked.faults(), Faults::default());
    assert_eq!(checked.critical(), [C]);
}

#[test]
fn the_hollow_triangle_keeps_one_vertex_and_one_edge_critical()
{
    let mut complex = Triangle::default();
    let matching = greedy(&mut complex, &HOLLOW).expect("the triangle reads");
    // The circle has one vertex and one edge that no acyclic matching pairs.
    assert_eq!(matching.critical().copied().collect::<Vec<_>>(), [C, AC]);
    let checked = collapse(
        &mut matching.on(&mut complex),
        &HOLLOW,
        Budget::from(HOLLOW.len()),
    )
    .expect("the triangle reads");
    assert_eq!(checked.faults(), Faults::default());
}

#[test]
fn a_face_at_the_incidence_two_stays_unpaired()
{
    let mut complex = Triangle { weight: 2 };
    let matching = greedy(&mut complex, &FILLED).expect("the triangle reads");
    assert_eq!(
        matching.critical().copied().collect::<Vec<_>>(),
        FILLED.to_vec()
    );
}

#[test]
fn a_cell_the_list_does_not_hold_is_critical()
{
    let mut complex = Triangle::default();
    let matching = greedy(&mut complex, &HOLLOW).expect("the triangle reads");
    assert_eq!(matching.class(&A), Class::Redundant(AB));
    assert_eq!(matching.class(&AB), Class::Collapsible(A));
    assert_eq!(matching.class(&ABC), Class::Critical);
    assert_eq!(matching.class(&Simplex(0b1000)), Class::Critical);
}
