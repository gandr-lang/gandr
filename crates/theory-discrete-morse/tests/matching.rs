//! A matching that a caller states pair by pair, read over the triangle.

use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Count;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::Matching;
use gandr_theory_discrete_morse::collapse;

use crate::simplices::A;
use crate::simplices::AB;
use crate::simplices::ABC;
use crate::simplices::FILLED;
use crate::simplices::Triangle;

#[test]
fn a_cell_that_two_stated_pairs_name_keeps_the_last_class()
{
    // `ab` is first the partner of `a`, then the redundant cell of `abc`.
    let matching = Matching::stated([(A, AB), (AB, ABC)]);
    assert_eq!(matching.cells(), [A, AB, ABC]);
    assert_eq!(matching.classes(), [
        Class::Redundant(AB),
        Class::Redundant(ABC),
        Class::Collapsible(AB),
    ]);
    // `a` names `ab` as its partner, and `ab` does not name `a` back.
    let mut complex = Triangle::default();
    let checked = collapse(
        &mut matching.on(&mut complex),
        &FILLED,
        Budget::from(FILLED.len()),
    )
    .expect("the triangle reads");
    assert_eq!(checked.faults(), Faults {
        unpaired: Count::from(1),
        ..Faults::default()
    });
}
