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
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::session::Endpoint;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::SessionAction;
use gandr_core_term::session::WebPiece;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_runtime_emitter::Carried;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostOutcome;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_runtime_emitter::Play;
use gandr_runtime_emitter::TaskNumber;
use gandr_runtime_emitter::Trace;
use gandr_runtime_emitter::evaluate_on;
use gandr_runtime_emitter::evaluate_traced_with_host;

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
/// the `1` queued from the first, closes both and answers `(2, 1)`: the
/// program and its answer.
///
/// # Specification
/// trivial.
fn exchange(core: &mut CoreArena) -> (ComputationId, ValueId)
{
    let one = integer(core, Digits("1"));
    let two = integer(core, Digits("2"));
    let zero = integer(core, Digits("0"));
    let left = FieldLabel::from(String::from("left"));
    let right = FieldLabel::from(String::from("right"));
    let protocol = core.value_type_unit();
    // The `right` arm, under `[b', a']`, then each receive's payload.
    let v = core.value_variable(Zone::Linear, end(Linear(1)));
    let w = core.value_variable(Zone::Linear, end(Linear(0)));
    let pair = core.value_tuple(&[v, w]);
    let answered = core.computation_return(pair);
    let closed = then(
        core,
        SessionAction::Close {
            endpoint: end(Linear(3)),
        },
        answered,
    );
    let closed = then(
        core,
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
        core,
        SessionAction::Send {
            endpoint: end(Linear(0)),
            payload: two,
        },
        offered,
    );
    let sent = then(
        core,
        SessionAction::Send {
            endpoint: end(Linear(1)),
            payload: one,
        },
        sent,
    );
    let second = echo(core, Echoed::Selecting(right));
    let inner = core.computation_session(SessionAction::Fork {
        protocol,
        child: second,
        parent: sent,
    });
    let first = echo(core, Echoed::Plainly);
    let program = core.computation_session(SessionAction::Fork {
        protocol,
        child: first,
        parent: inner,
    });
    (program, core.value_tuple(&[two, one]))
}

/// [`exchange`] answers `(2, 1)` on every tier. A root resumed at the wrong
/// frame, a child entered without its end, or a message handed to the wrong
/// end changes the answer or stops the run.
#[test]
fn forked_tasks_exchange_alike_on_both_tiers()
{
    let mut core = CoreArena::new();
    let (program, expected) = exchange(&mut core);
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

/// A host that declines every operation.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Declining;

impl HostHandler for Declining
{
    type Abort = ();

    /// Decline.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        _request: HostRequest<'_>,
        _values: &mut HostValues<'_>,
    ) -> HostReply<()>
    {
        HostReply::Decline
    }
}

/// [`exchange`], traced, plays one dialogue per channel in the order its
/// fork ran. The first channel, `a`, plays `R: send 1`, `L: receive, send,
/// close`, `R: receive, close`: the root's send before the child's receipt,
/// the child's echo before the root's, its close beside the root's tail —
/// `series(R0, L0, L1, parallel(L2, series(R1, R2)))`. The second, `b`,
/// adds the selection before the echo: the child's echo `L2` comes before the
/// root's receipt `R2` but beside its offer `R1`, and its close `L3` beside
/// the root's whole tail — `series(R0, L0, L1, prime(L2, L3, R1, series(R2,
/// R3)))`. Each receipt takes what its send carried, by the task the message
/// reached. A send, receipt, selection or close left unrecorded, or recorded
/// at the wrong end, changes a web.
#[test]
fn a_traced_run_plays_each_channel_as_its_dialogue()
{
    let mut core = CoreArena::new();
    let (program, expected) = exchange(&mut core);
    let (arena, root) = focused(&core, program);
    let mut store = Store::new();
    let mut trace = Trace::default();
    let outcome = evaluate_traced_with_host(
        (&arena, &Definitions::new(), root),
        (budget(), &mut store),
        &mut Declining,
        &mut trace,
    );
    let Ok(HostOutcome::Completed(Outcome::Halted(answer))) = outcome
    else {
        panic!("the traced run halts: {outcome:?}");
    };
    let read = read_back_value(&arena, &store, answer, &mut core).expect("the answer reads back");
    assert_eq!(
        CertificateEquality::Equal,
        equal_certificate_syntax(&core, read, expected),
        "tracing leaves the answer as it was"
    );
    let &[ref a, ref b] = trace.plays.as_slice()
    else {
        panic!("one play per fork: {trace:?}");
    };
    assert_ne!(a.fork, b.fork, "each play names its own fork");
    let (left, right) = (Endpoint::Left, Endpoint::Right);
    let event = |endpoint, index| WebPiece::Event { endpoint, index };
    assert_eq!(
        Ok([
            WebPiece::Series(4),
            event(right, 0),
            event(left, 0),
            event(left, 1),
            WebPiece::Parallel(2),
            event(left, 2),
            WebPiece::Series(2),
            event(right, 1),
            event(right, 2),
        ]
        .as_slice()),
        a.web().decompose().as_deref(),
        "the first channel: {a:?}"
    );
    assert_eq!(
        Ok([
            WebPiece::Series(4),
            event(right, 0),
            event(left, 0),
            event(left, 1),
            WebPiece::Prime(4),
            event(left, 2),
            event(left, 3),
            event(right, 1),
            WebPiece::Series(2),
            event(right, 2),
            event(right, 3),
        ]
        .as_slice()),
        b.web().decompose().as_deref(),
        "the second channel: {b:?}"
    );
    for play in [a, b] {
        let sent = play
            .moves
            .iter()
            .filter_map(|played| match played.movement {
                RecordedMove::Sent(carried) => Some((played.side, carried)),
                RecordedMove::Received(_)
                | RecordedMove::Selected(_)
                | RecordedMove::Offered(_)
                | RecordedMove::Closed => None,
            });
        let received = play
            .moves
            .iter()
            .filter_map(|played| match played.movement {
                RecordedMove::Received(carried) => Some((played.side, carried)),
                RecordedMove::Sent(_)
                | RecordedMove::Selected(_)
                | RecordedMove::Offered(_)
                | RecordedMove::Closed => None,
            });
        for ((from, carried), (to, took)) in sent.zip(received) {
            assert_ne!(from, to, "a message crosses the channel: {play:?}");
            assert_eq!(
                carried, took,
                "a receipt takes what its send carried: {play:?}"
            );
            assert!(
                matches!(carried, Carried::Value(_)),
                "an integer moves into the store"
            );
        }
    }
    let tasks = |play: &Play, side| {
        play.moves
            .iter()
            .filter(|played| played.side == side)
            .map(|played| played.task)
            .collect::<Vec<_>>()
    };
    assert_eq!(
        vec![TaskNumber(1); 3],
        tasks(a, left),
        "the first child plays `a`'s left"
    );
    assert_eq!(
        vec![TaskNumber(0); 3],
        tasks(a, right),
        "the root plays `a`'s right"
    );
    assert_eq!(
        vec![TaskNumber(2); 4],
        tasks(b, left),
        "the second plays `b`'s left"
    );
    assert_eq!(
        vec![TaskNumber(0); 4],
        tasks(b, right),
        "the root plays `b`'s right"
    );
    assert_eq!(
        Some(&RecordedMove::Offered(FieldLabel::from(String::from(
            "right"
        )))),
        b.moves
            .iter()
            .filter(|played| played.side == right)
            .nth(1)
            .map(|played| &played.movement),
        "the selection reaches the parked root as its offer"
    );
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
