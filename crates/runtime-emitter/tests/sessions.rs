//! Sessions run on the run's own scheduler: forked tasks take turns on its
//! thread, a receive or an offer with nothing sent parks its task, and a run
//! whose tasks all wait is stuck at their actions.

use gandr_core_sequent::CommandNode;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::read_back_value;
use gandr_core_term::CertificateEquality;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::session::SessionAction;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_runtime_emitter::evaluate_on;

use crate::world::Digits;
use crate::world::budget;
use crate::world::focused;
use crate::world::integer;
use crate::world::tiers;

/// A linear de Bruijn index.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Linear(u32);

/// The linear index `index`.
///
/// # Specification
/// trivial.
fn end(index: Linear) -> DeBruijnIndex
{
    DeBruijnIndex::from(index.0)
}

/// `first ; rest`, the unit `first` returns bound and unread.
///
/// # Specification
/// trivial.
fn then(
    core: &mut CoreArena,
    first: SessionAction,
    rest: ComputationId,
) -> ComputationId
{
    let first = core.computation_session(first);
    core.computation_bind(first, rest)
}

/// What an echoing child does between its receive and its echo.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
enum Echoed
{
    /// Nothing.
    Plainly,
    /// Select the label.
    Selecting(FieldLabel),
}

/// `recv(c) as x ; send(c, x) ; close(c)` with `c` the innermost linear
/// binder, `select(c, l)` before the send when `echoed` selects `l`.
///
/// # Specification
/// trivial.
fn echo(
    core: &mut CoreArena,
    echoed: Echoed,
) -> ComputationId
{
    let closed = core.computation_session(SessionAction::Close {
        endpoint: end(Linear(1)),
    });
    let payload = core.value_variable(Zone::Linear, end(Linear(0)));
    let mut body = then(
        core,
        SessionAction::Send {
            endpoint: end(Linear(1)),
            payload,
        },
        closed,
    );
    match echoed {
        Echoed::Plainly => {},
        Echoed::Selecting(label) => {
            body = then(
                core,
                SessionAction::Select {
                    endpoint: end(Linear(1)),
                    label,
                },
                body,
            );
        },
    }
    core.computation_session(SessionAction::Receive {
        endpoint: end(Linear(0)),
        body,
    })
}

/// Two children, forked in turn, each echo what it is sent; the second
/// selects `right` first. The root sends `1` to the first and `2` to the
/// second, then offers on the second's channel before either child has run,
/// so it waits; the first child runs, its echo queued, then the second,
/// whose selection readies the root, which takes `right`, receives `2`, then
/// the `1` queued from the first, and answers `(2, 1)` on every tier. A
/// root resumed at the wrong frame, a child entered without its end, or a
/// message handed to the wrong end changes the answer or stops the run.
#[test]
fn forked_tasks_exchange_alike_on_both_tiers()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let zero = integer(&mut core, Digits("0"));
    let left = FieldLabel::from(String::from("left"));
    let right = FieldLabel::from(String::from("right"));
    let protocol = core.value_type_unit();
    // The `right` arm, under `[b', a']`, then each receive's payload.
    let v = core.value_variable(Zone::Linear, end(Linear(1)));
    let w = core.value_variable(Zone::Linear, end(Linear(0)));
    let pair = core.value_tuple(&[v, w]);
    let answered = core.computation_return(pair);
    let closed = then(
        &mut core,
        SessionAction::Close {
            endpoint: end(Linear(3)),
        },
        answered,
    );
    let closed = then(
        &mut core,
        SessionAction::Close {
            endpoint: end(Linear(2)),
        },
        closed,
    );
    let from_first = core.computation_session(SessionAction::Receive {
        endpoint: end(Linear(2)),
        body: closed,
    });
    let taken = core.computation_session(SessionAction::Receive {
        endpoint: end(Linear(0)),
        body: from_first,
    });
    let zeros = core.value_tuple(&[zero, zero]);
    let refused = core.computation_return(zeros);
    let offered = core.computation_session(SessionAction::Offer {
        endpoint: end(Linear(0)),
        arms: [(left, refused), (right.clone(), taken)].into(),
    });
    let sent = then(
        &mut core,
        SessionAction::Send {
            endpoint: end(Linear(0)),
            payload: two,
        },
        offered,
    );
    let sent = then(
        &mut core,
        SessionAction::Send {
            endpoint: end(Linear(1)),
            payload: one,
        },
        sent,
    );
    let second = echo(&mut core, Echoed::Selecting(right));
    let inner = core.computation_session(SessionAction::Fork {
        protocol,
        child: second,
        parent: sent,
    });
    let first = echo(&mut core, Echoed::Plainly);
    let program = core.computation_session(SessionAction::Fork {
        protocol,
        child: first,
        parent: inner,
    });
    let expected = core.value_tuple(&[two, one]);
    let (arena, root) = focused(&core, program);
    for &tier in tiers() {
        let mut store = Store::new();
        let outcome = evaluate_on(
            tier,
            &arena,
            &Definitions::new(),
            root,
            budget(),
            &mut store,
        );
        let Ok(Outcome::Halted(answer)) = outcome
        else {
            panic!("the run halts on {tier:?}: {outcome:?}");
        };
        let read =
            read_back_value(&arena, &store, answer, &mut core).expect("the answer reads back");
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(&core, read, expected),
            "the root answers what each child echoed on {tier:?}"
        );
    }
}

/// A root and its child each receive first on their channel: the root
/// waits, the child runs and waits, and no task is ready, so the run is
/// stuck at the root's receive, then the child's, on every tier.
#[test]
fn a_run_whose_tasks_all_wait_is_stuck_at_their_actions()
{
    let mut core = CoreArena::new();
    let protocol = core.value_type_unit();
    let closed = core.computation_session(SessionAction::Close {
        endpoint: end(Linear(1)),
    });
    let child = core.computation_session(SessionAction::Receive {
        endpoint: end(Linear(0)),
        body: closed,
    });
    let y = core.value_variable(Zone::Linear, end(Linear(0)));
    let answered = core.computation_return(y);
    let closed = then(
        &mut core,
        SessionAction::Close {
            endpoint: end(Linear(1)),
        },
        answered,
    );
    let parent = core.computation_session(SessionAction::Receive {
        endpoint: end(Linear(0)),
        body: closed,
    });
    let program = core.computation_session(SessionAction::Fork {
        protocol,
        child,
        parent,
    });
    let (arena, root) = focused(&core, program);
    let Some(&CommandNode::Session {
        action: SessionAction::Fork { child, parent, .. },
        ..
    }) = arena.command(root)
    else {
        panic!("the program focuses to its fork");
    };
    for &tier in tiers() {
        let mut store = Store::new();
        let outcome = evaluate_on(
            tier,
            &arena,
            &Definitions::new(),
            root,
            budget(),
            &mut store,
        );
        assert_eq!(
            Ok(Outcome::Stuck(Stuck::Deadlock(vec![parent, child]))),
            outcome,
            "the run is stuck at both receives on {tier:?}"
        );
    }
}
