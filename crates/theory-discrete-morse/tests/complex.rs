//! The incidence of a face: which integers a matching can pair along.

use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::Invertibility;

#[test]
fn only_one_and_minus_one_are_invertible()
{
    let read = [1_i64, -1, 0, 2, -2].map(|value| Incidence::from(value).invertibility());
    assert_eq!(read, [
        Invertibility::Invertible,
        Invertibility::Invertible,
        Invertibility::NotInvertible,
        Invertibility::NotInvertible,
        Invertibility::NotInvertible,
    ]);
}
