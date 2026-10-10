//! Run a finite resource-lifecycle monitor through the public API.
extern crate alloc;

use alloc::collections::BTreeSet;

use anodized::spec;
use gandr_theory_nominal_automata::handle::Arity;
use gandr_theory_nominal_automata::handle::AutomatonError;
use gandr_theory_nominal_automata::handle::Configuration;
use gandr_theory_nominal_automata::handle::Control;
use gandr_theory_nominal_automata::handle::Membership;
use gandr_theory_nominal_automata::handle::Register;
use gandr_theory_nominal_automata::handle::Store;
use gandr_theory_nominal_automata::handle::Transfer;
use gandr_theory_nominal_automata::letter::Letter;
use gandr_theory_nominal_automata::nda::Nda;
use gandr_theory_nominal_automata::nda::Rule;

/// A caller-owned endpoint identity.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Endpoint
{
    /// The endpoint observed by this example.
    Channel,
}

/// Check drained, leaked and unmatched-release traces.
///
/// # Specification
/// - ensures: success means all three literal membership answers matched.
/// - fails: reports an invalid automaton handle.
/// - panics: if a membership answer disagrees with the lifecycle example.
///
/// # Errors
/// Returns the structural automaton error if the example handle is invalid.
///
/// # Adequacy
/// - hypothesis: L3 the public lifecycle suite distinguishes final-state,
///   matching-release and remembered-name violations.
/// - witness: `tests::nda::session_monitor_accepts_drained_log`
/// - witness: `tests::nda::session_monitor_rejects_leaked_login`
/// - witness: `tests::nda::session_monitor_rejects_logout_without_login`
#[spec(ensures: |result| result.is_ok())]
fn main() -> Result<(), AutomatonError>
{
    let empty = Control::ZERO;
    let live = Control::from(1);
    let monitor = Nda::new(
        vec![Arity::ZERO, Arity::from(1)],
        Configuration::new(empty, Store::<Endpoint>::empty(Arity::ZERO)),
        BTreeSet::from([empty]),
        vec![
            Rule::open(empty, live, vec![Transfer::Allocated]),
            Rule::close(live, Register::ZERO, empty, vec![]),
        ],
    )?;
    assert_eq!(
        monitor.accepts(&[
            Letter::Open(Endpoint::Channel),
            Letter::Close(Endpoint::Channel)
        ]),
        Membership::Accepted,
        "a released endpoint leaves a drained trace"
    );
    assert_eq!(
        monitor.accepts(&[Letter::Open(Endpoint::Channel)]),
        Membership::Rejected,
        "a live endpoint is a leak"
    );
    assert_eq!(
        monitor.accepts(&[Letter::Close(Endpoint::Channel)]),
        Membership::Rejected,
        "release requires a remembered endpoint"
    );
    Ok(())
}
