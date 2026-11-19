//! Directed alpha-variant and bounded language-enlargement witnesses.
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_nominal_automata::handle::Arity;
use gandr_theory_nominal_automata::handle::Control;
use gandr_theory_nominal_automata::handle::Membership;
use gandr_theory_nominal_automata::handle::Register;
use gandr_theory_nominal_automata::handle::Transfer;
use gandr_theory_nominal_automata::letter::Letter;
use gandr_theory_nominal_automata::nda::Nda;
use gandr_theory_nominal_automata::nda::Rule;
use gandr_theory_nominal_automata::nda::RuleKind;
use gandr_theory_nominal_automata::nda::name_dropping;

use super::Name;
use super::nda;

/// Remember the administrator, then allocate and use a participant.
///
/// # Specification
/// trivial.
fn witness() -> Nda<Name>
{
    let q0 = Control::ZERO;
    let q1 = Control::from(1);
    let q2 = Control::from(2);
    Nda::new(
        vec![Arity::from(1), Arity::from(2), Arity::from(1)],
        nda::initial(),
        BTreeSet::from([q2]),
        vec![
            Rule::open(q0, q1, vec![
                Transfer::Keep(Register::ZERO),
                Transfer::Allocated,
            ]),
            Rule::free(q1, Register::from(1), q2, vec![Transfer::Keep(
                Register::ZERO,
            )]),
        ],
    )
    .expect("valid witness")
}
#[test]
fn literal_language_is_not_alpha_closed_before_dropping()
{
    let automaton = witness();
    assert_eq!(
        automaton.accepts(&[Letter::Open(Name::User), Letter::Free(Name::User)]),
        Membership::Accepted
    );
    assert_eq!(
        automaton.accepts(&[Letter::Open(Name::Admin), Letter::Free(Name::Admin)]),
        Membership::Rejected
    );
}
#[test]
fn name_dropping_closes_language_under_alpha()
{
    let automaton = name_dropping(&witness());
    for name in [Name::Admin, Name::User] {
        assert_eq!(
            automaton.accepts(&[Letter::Open(name), Letter::Free(name)]),
            Membership::Accepted
        );
    }
    assert_eq!(
        automaton.accepts(&[Letter::Open(Name::Admin), Letter::Free(Name::User)]),
        Membership::Rejected
    );
}
#[test]
fn name_dropping_adds_one_drop_rule_per_register()
{
    let donor = witness();
    let dropped = name_dropping(&donor);
    assert_eq!(dropped.degree(), donor.degree());
    let expected = [
        Rule::forget(Control::ZERO, Register::ZERO, Control::ZERO, vec![
            Transfer::Empty,
        ]),
        Rule::forget(Control::from(1), Register::ZERO, Control::from(1), vec![
            Transfer::Empty,
            Transfer::Keep(Register::from(1)),
        ]),
        Rule::forget(Control::from(1), Register::from(1), Control::from(1), vec![
            Transfer::Keep(Register::ZERO),
            Transfer::Empty,
        ]),
        Rule::forget(Control::from(2), Register::ZERO, Control::from(2), vec![
            Transfer::Empty,
        ]),
    ];
    assert_eq!(&dropped.rules()[donor.rules().len() ..], &expected);
    assert!(
        expected
            .iter()
            .all(|rule| matches!(rule.kind(), RuleKind::Drop { .. })),
        "all additions erase without input"
    );
}
#[test]
fn name_dropping_only_enlarges_the_language()
{
    let monitor = nda::session_monitor();
    let dropped = name_dropping(&monitor);
    let alphabet = [
        Letter::Free(Name::Admin),
        Letter::Open(Name::Admin),
        Letter::Close(Name::Admin),
        Letter::OpenClose(Name::Admin),
        Letter::Free(Name::User),
        Letter::Open(Name::User),
        Letter::Close(Name::User),
        Letter::OpenClose(Name::User),
    ];
    for length in 0_u32 ..= 7 {
        let count = 8_usize
            .checked_pow(length)
            .expect("the seven-letter bound fits");
        let mut word: Vec<Letter<Name>> =
            vec![alphabet[0]; usize::try_from(length).expect("bounded length")];
        for encoded in 0 .. count {
            let mut digits = encoded;
            for letter in &mut word {
                *letter = alphabet[digits & 7];
                digits >>= 3_u32;
            }
            if monitor.accepts(&word) == Membership::Accepted {
                assert_eq!(dropped.accepts(&word), Membership::Accepted);
            }
        }
    }
}
