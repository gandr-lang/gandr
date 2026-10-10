//! Word-automaton floor over the public API.
use alloc::collections::BTreeSet;
use alloc::vec;

use gandr_theory_nominal_automata::handle::Arity;
use gandr_theory_nominal_automata::handle::AutomatonError;
use gandr_theory_nominal_automata::handle::Configuration;
use gandr_theory_nominal_automata::handle::Control;
use gandr_theory_nominal_automata::handle::Controls;
use gandr_theory_nominal_automata::handle::Membership;
use gandr_theory_nominal_automata::handle::Register;
use gandr_theory_nominal_automata::handle::Store;
use gandr_theory_nominal_automata::handle::Transfer;
use gandr_theory_nominal_automata::letter::Letter;
use gandr_theory_nominal_automata::nda::Nda;
use gandr_theory_nominal_automata::nda::Rule;
use quenchant_shape::shape::Maybe::Present;

use super::Name;

/// A monitor accepting exactly drained one-user lifecycle logs.
///
/// # Specification
/// trivial.
pub fn session_monitor() -> Nda<Name>
{
    let q0 = Control::ZERO;
    let q1 = Control::from(1);
    let admin = Register::ZERO;
    let user = Register::from(1);
    Nda::new(
        vec![Arity::from(1), Arity::from(2)],
        initial(),
        BTreeSet::from([q0]),
        vec![
            Rule::open(q0, q1, vec![Transfer::Keep(admin), Transfer::Allocated]),
            Rule::close(q1, user, q0, vec![Transfer::Keep(admin)]),
            Rule::free(q0, admin, q0, vec![Transfer::Keep(admin)]),
            Rule::free(q1, admin, q1, vec![
                Transfer::Keep(admin),
                Transfer::Keep(user),
            ]),
        ],
    )
    .expect("valid lifecycle monitor")
}
/// The administrator-only initial configuration.
///
/// # Specification
/// trivial.
pub fn initial() -> Configuration<Name>
{
    Configuration::new(
        Control::ZERO,
        Store::try_new(vec![Present(Name::Admin)]).expect("injective"),
    )
}
#[test]
fn session_monitor_accepts_drained_log()
{
    let monitor = session_monitor();
    assert_eq!(monitor.accepts(&[]), Membership::Accepted);
    assert_eq!(
        monitor.accepts(&[
            Letter::Open(Name::User),
            Letter::Free(Name::Admin),
            Letter::Close(Name::User),
            Letter::Free(Name::Admin)
        ]),
        Membership::Accepted
    );
    assert_eq!(
        monitor.accepts(&[
            Letter::Open(Name::User),
            Letter::Close(Name::User),
            Letter::Open(Name::User),
            Letter::Close(Name::User)
        ]),
        Membership::Accepted
    );
}
#[test]
fn session_monitor_rejects_leaked_login()
{
    assert_eq!(
        session_monitor().accepts(&[Letter::Open(Name::User), Letter::Free(Name::Admin)]),
        Membership::Rejected
    );
}
#[test]
fn session_monitor_rejects_logout_without_login()
{
    assert_eq!(
        session_monitor().accepts(&[Letter::Close(Name::User)]),
        Membership::Rejected
    );
}
#[test]
fn session_monitor_rejects_unknown_actor()
{
    assert_eq!(
        session_monitor().accepts(&[Letter::Free(Name::User)]),
        Membership::Rejected
    );
}
#[test]
fn session_monitor_bounds_concurrent_logins()
{
    assert_eq!(
        session_monitor().accepts(&[Letter::Open(Name::User), Letter::Open(Name::Other)]),
        Membership::Rejected
    );
}
#[test]
fn session_monitor_degree_is_maximum_arity()
{
    assert_eq!(usize::from(session_monitor().degree()), 2);
}
#[test]
fn construction_rejects_invalid_control()
{
    let invalid = Control::from(7);
    let error = AutomatonError::InvalidControl {
        control: invalid,
        controls: Controls::from(1),
    };
    for rules in [vec![Rule::open(invalid, Control::ZERO, vec![])], vec![
        Rule::open(Control::ZERO, invalid, vec![]),
    ]] {
        assert_eq!(
            Nda::new(vec![Arity::from(1)], initial(), BTreeSet::new(), rules),
            Err(error)
        );
    }
    assert_eq!(
        Nda::new(
            vec![Arity::from(1)],
            initial(),
            BTreeSet::from([invalid]),
            vec![]
        ),
        Err(error)
    );
    assert_eq!(
        Nda::new(
            vec![Arity::from(1)],
            Configuration::new(invalid, Store::<Name>::empty(Arity::ZERO)),
            BTreeSet::new(),
            vec![]
        ),
        Err(error)
    );
}
#[test]
fn construction_rejects_arity_mismatch()
{
    let error = AutomatonError::ArityMismatch {
        control: Control::ZERO,
        expected: Arity::from(1),
        actual: Arity::ZERO,
    };
    assert_eq!(
        Nda::new(
            vec![Arity::from(1)],
            Configuration::new(Control::ZERO, Store::<Name>::empty(Arity::ZERO)),
            BTreeSet::new(),
            vec![]
        ),
        Err(error)
    );
    assert_eq!(
        Nda::new(vec![Arity::from(1)], initial(), BTreeSet::new(), vec![
            Rule::free(Control::ZERO, Register::ZERO, Control::ZERO, vec![])
        ]),
        Err(error)
    );
}
#[test]
fn construction_rejects_unknown_register()
{
    assert_eq!(
        Nda::new(vec![Arity::from(1)], initial(), BTreeSet::new(), vec![
            Rule::close(Control::ZERO, Register::from(3), Control::ZERO, vec![
                Transfer::Empty
            ])
        ]),
        Err(AutomatonError::UnknownRegister {
            control: Control::ZERO,
            register: Register::from(3)
        })
    );
}
#[test]
fn construction_rejects_misplaced_allocated_name()
{
    assert_eq!(
        Nda::new(vec![Arity::from(1)], initial(), BTreeSet::new(), vec![
            Rule::open_close(Control::ZERO, Control::ZERO, vec![Transfer::Allocated])
        ]),
        Err(AutomatonError::MisplacedAllocatedName {
            control: Control::ZERO
        })
    );
}
#[test]
fn construction_rejects_kept_deallocated_name()
{
    for rule in [
        Rule::close(Control::ZERO, Register::ZERO, Control::ZERO, vec![
            Transfer::Keep(Register::ZERO),
        ]),
        Rule::forget(Control::ZERO, Register::ZERO, Control::ZERO, vec![
            Transfer::Keep(Register::ZERO),
        ]),
    ] {
        assert_eq!(
            Nda::new(vec![Arity::from(1)], initial(), BTreeSet::new(), vec![rule]),
            Err(AutomatonError::KeptDeallocatedName {
                control: Control::ZERO,
                register: Register::ZERO
            })
        );
    }
}
#[test]
fn open_close_allocates_and_immediately_forgets()
{
    let monitor = Nda::new(
        vec![Arity::from(1)],
        initial(),
        BTreeSet::from([Control::ZERO]),
        vec![
            Rule::open_close(Control::ZERO, Control::ZERO, vec![Transfer::Keep(
                Register::ZERO,
            )]),
            Rule::free(Control::ZERO, Register::ZERO, Control::ZERO, vec![
                Transfer::Keep(Register::ZERO),
            ]),
        ],
    )
    .expect("valid monitor");
    assert_eq!(
        monitor.accepts(&[Letter::OpenClose(Name::User), Letter::Free(Name::Admin)]),
        Membership::Accepted
    );
    assert_eq!(
        monitor.accepts(&[Letter::OpenClose(Name::Admin)]),
        Membership::Rejected
    );
    assert_eq!(
        monitor.accepts(&[Letter::OpenClose(Name::User), Letter::Free(Name::User)]),
        Membership::Rejected
    );
}
