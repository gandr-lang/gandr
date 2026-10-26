use alloc::string::ToString as _;

use super::Tactic;
use super::TooManyIntros;

#[test]
fn intro_counts_up_to_the_limit()
{
    let once = Tactic::ASSUMPTION
        .intro()
        .expect("one introduction is admitted");
    assert_eq!(u8::from(once), 1);
    assert_eq!(once.body(), Some(Tactic::ASSUMPTION));
    assert_eq!(
        Tactic::ASSUMPTION.body(),
        None,
        "assumption introduces nothing"
    );
    let last = Tactic::try_from(Tactic::INTROS - 1).expect("the last count is admitted");
    assert_eq!(last.intro(), None, "the count past the limit is refused");
    assert_eq!(Tactic::try_from(Tactic::INTROS), Err(TooManyIntros));
    assert_eq!(once.to_string(), "intro(assumption)");
    assert_eq!(Tactic::ASSUMPTION.to_string(), "assumption");
}
