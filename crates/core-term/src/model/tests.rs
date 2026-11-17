use alloc::vec::Vec;

use super::Beyond;
use super::CandidatePlace;
use super::Survivors;

#[test]
fn survivors_name_each_place_once_and_count_the_rest()
{
    // Places 0 and 2 named, 2 named twice, and two places past the named
    // ones: the set names 0 and 2 once each, ascending, and counts two
    // beyond.
    let last = usize::from(Survivors::NAMED);
    let survivors = [2_usize, 0, 2, last, last.saturating_add(5)]
        .into_iter()
        .map(CandidatePlace::from)
        .fold(Survivors::default(), Survivors::with);
    assert_eq!(
        survivors.places().map(usize::from).collect::<Vec<_>>(),
        [0, 2],
        "each place below the named ones is held once, ascending"
    );
    assert_eq!(
        survivors.beyond(),
        Beyond::from(2_u32),
        "each place at or past the named ones is counted"
    );
    let below = CandidatePlace::from(last.saturating_sub(1));
    assert_eq!(
        Survivors::default()
            .with(below)
            .places()
            .collect::<Vec<_>>(),
        [below],
        "the last named place is held, not counted"
    );
}
