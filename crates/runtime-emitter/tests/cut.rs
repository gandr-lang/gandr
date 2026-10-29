//! A cut forked: its writer run closed over its own store and its reader run
//! with a host, joined on a fork, the reader reading the writer's answer
//! through the cell, on each tier, on the serial fork and on a fork that
//! starts the reader first. A writer focus names apart runs on the sequential
//! schedule to its fused bind's answer.

use core::convert::Infallible;
use core::fmt;
use core::time::Duration;
use std::sync::Mutex;
use std::sync::mpsc;

use gandr_core_fork::Fork;
use gandr_core_fork::Serial;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::Environment;
use gandr_core_sequent::FreeSet;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::Writers;
use gandr_core_sequent::check_command;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::read_back_value;
use gandr_core_sequent::render_command;
use gandr_core_term::CertificateEquality;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::equal_certificate_syntax;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::CELL;
use gandr_runtime_emitter::Forked;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostOutcome;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::READ;
use gandr_runtime_emitter::Reader;
use gandr_runtime_emitter::RunInputs;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::Writer;
use gandr_runtime_emitter::evaluate_cut_on;
use gandr_runtime_emitter::evaluate_on;

/// The decimal digits of a test literal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Digits(&'static str);

/// The jumps a run may take: no test program comes near.
///
/// # Specification
/// trivial.
fn budget() -> Fuel
{
    Fuel::from(1_usize << 20)
}

/// The tiers this host runs: native where a patcher exists, the executor
/// everywhere.
///
/// # Specification
/// trivial.
fn tiers() -> &'static [Tier]
{
    if PATCHER {
        &[Tier::Native, Tier::Executor]
    }
    else {
        &[Tier::Executor]
    }
}

/// The non-negative integer literal `digits` in `core`.
///
/// # Specification
/// trivial.
fn integer(
    core: &mut CoreArena,
    digits: Digits,
) -> ValueId
{
    let magnitude = Magnitude::from_decimal_text(digits.0.into()).expect("decimal digits");
    core.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        magnitude,
    )))
}

/// The interface `E` of one operation `op` from an integer to an integer.
///
/// # Specification
/// trivial.
fn asked(core: &mut CoreArena) -> EffectSig
{
    let integer = core.value_type_base(BaseType::Integer);
    EffectSig::new("E".into(), [EffectOp {
        name: "op".into(),
        payload: integer,
        reply: integer,
    }])
    .expect("one operation")
}

/// The cell's interface, its read replying with a value of type `answer`.
///
/// # Specification
/// trivial.
fn cell(
    core: &mut CoreArena,
    answer: ValueTypeId,
) -> EffectSig
{
    let unit = core.value_type_unit();
    EffectSig::new(CELL.into(), [EffectOp {
        name: READ.into(),
        payload: unit,
        reply: answer,
    }])
    .expect("one operation")
}

/// `program` focused into `arena`, closed.
///
/// # Specification
/// trivial.
fn focused(
    core: &CoreArena,
    program: ComputationId,
    arena: &mut CommandArena,
) -> CommandId
{
    let root = focus_computation(core, program, arena, &mut Provenance::new(), &Writers::NONE)
        .expect("the program focuses");
    assert_eq!(Ok(FreeSet::default()), check_command(arena, root));
    root
}

/// The thunk `root` answers on `tier`, as its body and its environment in
/// `store`.
///
/// # Specification
/// trivial.
fn suspended(
    tier: Tier,
    (arena, root): (&CommandArena, CommandId),
    store: &mut Store,
) -> (CommandId, Environment)
{
    let outcome = evaluate_on(
        tier,
        arena,
        &Definitions::new(),
        root,
        budget(),
        RunInputs::new(store),
    );
    let Ok(Outcome::Halted(thunk)) = outcome
    else {
        panic!("the writer's program answers on {tier:?}: {outcome:?}");
    };
    let Some(&HeapValue::Thunk { body, environment }) = store.value(thunk)
    else {
        panic!("the writer's program answers a thunk on {tier:?}");
    };
    (body, environment)
}

/// The caller's host: it answers `E.op` with seven and signals the fork that
/// the reader reached it.
#[repr(transparent)]
#[derive(Debug)]
struct Signalling
{
    /// Where the host signals that the reader reached `E.op`.
    reached: mpsc::Sender<()>,
}

impl HostHandler for Signalling
{
    type Abort = Infallible;

    /// Answer `E.op` with seven; no other operation reaches this host.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>
    {
        assert_eq!(
            (
                request.signature.name().as_ref(),
                request.operation.as_ref()
            ),
            ("E", "op"),
            "only the reader's other operation reaches the caller's host"
        );
        let _sent = self.reached.send(());
        let seven = HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::from_decimal_text("7".into()).expect("decimal reply"),
        )));
        HostReply::Resume(values.allocate(seven).expect("the reply fits"))
    }
}

/// A fork that starts the reader first: the right half runs on a thread of
/// its own, and the left half begins on this thread once the reader reaches
/// the operation before its read, so the read finds its cell empty.
#[repr(transparent)]
#[derive(Debug)]
struct ReaderFirst
{
    /// Where the caller's host signals that the reader reached `E.op`.
    reached: Mutex<mpsc::Receiver<()>>,
}

impl Fork for ReaderFirst
{
    /// Every item on this thread, as the serial fork runs them.
    ///
    /// # Specification
    /// trivial.
    fn each<Item, State, Start, Job>(
        &self,
        items: &mut [Item],
        start: Start,
        job: Job,
    ) where
        Item: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
    {
        Serial.each(items, start, job);
    }

    /// The right half on a thread of its own, then the left half here once
    /// the right one signals.
    ///
    /// # Specification
    /// trivial.
    fn join<Left, Right, LeftOutput, RightOutput>(
        &self,
        left: Left,
        right: Right,
    ) -> (LeftOutput, RightOutput)
    where
        Left: FnOnce() -> LeftOutput + Send,
        Right: FnOnce() -> RightOutput + Send,
        LeftOutput: Send,
        RightOutput: Send,
    {
        std::thread::scope(|scope| {
            let right = scope.spawn(right);
            let _reached = self
                .reached
                .lock()
                .expect("one join at a time")
                .recv_timeout(Duration::from_secs(60));
            let left = left();
            (left, right.join().expect("the reader's thread joins"))
        })
    }
}

/// The two halves of a cut in one arena: the writer's program, which answers
/// the suspended writer, and the reader's root.
#[derive(Debug)]
struct Cut
{
    /// The arena both halves belong to.
    arena: CommandArena,
    /// The program answering the writer's thunk.
    writer: CommandId,
    /// The reader's root.
    reader: CommandId,
}

/// The reader `bind(E.op(1), x. bind(?cell.read(()), y. return (x, y)))`
/// beside the writer `program`, its read replying with type `answer`.
///
/// # Specification
/// trivial.
fn cut(
    core: &mut CoreArena,
    program: ComputationId,
    answer: ValueTypeId,
) -> Cut
{
    let one = integer(core, Digits("1"));
    let unit = core.value_unit();
    let asked = asked(core);
    let cell = cell(core, answer);
    let ask = core.computation_perform(asked, "op".into(), one);
    let read = core.computation_perform(cell, READ.into(), unit);
    let fields = [
        core.value_variable(Zone::Intuitionistic, 1_u32.into()),
        core.value_variable(Zone::Intuitionistic, 0_u32.into()),
    ];
    let pair = core.value_tuple(&fields);
    let paired = core.computation_return(pair);
    let then = core.computation_bind(read, paired);
    let reader = core.computation_bind(ask, then);
    let mut arena = CommandArena::new();
    let writer = focused(core, program, &mut arena);
    let reader = focused(core, reader, &mut arena);
    Cut {
        arena,
        writer,
        reader,
    }
}

/// `cut`'s halves joined on `fork` on `tier`: the writer's outcome, the
/// reader's, and the reader's store.
///
/// # Specification
/// trivial.
fn forked<Forking>(
    (fork, reached): (&Forking, mpsc::Sender<()>),
    tier: Tier,
    cut: &Cut,
    read_into: &mut Store,
) -> Forked<Infallible>
where
    Forking: Fork,
{
    let mut written = Store::new();
    let (body, environment) = suspended(tier, (&cut.arena, cut.writer), &mut written);
    let mut host = Signalling { reached };
    evaluate_cut_on(
        fork,
        tier,
        (&cut.arena, &Definitions::new()),
        (
            Writer {
                body,
                environment,
                store: &mut written,
            },
            Reader {
                root: cut.reader,
                store: read_into,
                host: &mut host,
            },
        ),
        budget(),
    )
}

/// Run `check` on `cut`'s halves joined on each tier, on the serial fork and
/// on a fork that starts the reader first.
///
/// # Specification
/// trivial.
fn on_each_fork(
    cut: &Cut,
    mut check: impl FnMut(fmt::Arguments<'_>, Forked<Infallible>, &Store),
)
{
    for &tier in tiers() {
        let (reached, _unread) = mpsc::channel();
        let mut store = Store::new();
        let serial = forked((&Serial, reached), tier, cut, &mut store);
        check(format_args!("serial on {tier:?}"), serial, &store);
        let (reached, signals) = mpsc::channel();
        let first = ReaderFirst {
            reached: Mutex::new(signals),
        };
        let mut store = Store::new();
        let reader_first = forked((&first, reached), tier, cut, &mut store);
        check(
            format_args!("reader first on {tier:?}"),
            reader_first,
            &store,
        );
    }
}

/// A writer over a capture answers a pair; its reader asks the caller's host
/// for seven, then reads the cell. On each tier and each fork the reader
/// answers seven beside the writer's pair, crossed into its own store.
#[test]
fn a_read_answers_what_its_writer_halts_with()
{
    let mut core = CoreArena::new();
    let (five, nine) = (
        integer(&mut core, Digits("5")),
        integer(&mut core, Digits("9")),
    );
    let captured = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let pair = core.value_tuple(&[captured, nine]);
    let answered = core.computation_return(pair);
    let thunk = core.value_thunk(answered);
    let suspended = core.computation_return(thunk);
    let bound = core.computation_return(five);
    let program = core.computation_bind(bound, suspended);
    let integer_type = core.value_type_base(BaseType::Integer);
    let answer = core.value_type_product(&[integer_type, integer_type]);
    let cut = cut(&mut core, program, answer);
    let seven = integer(&mut core, Digits("7"));
    let written = core.value_tuple(&[five, nine]);
    let expected = core.value_tuple(&[seven, written]);
    on_each_fork(&cut, |fork, forked, store| {
        assert!(
            matches!(forked.writer, Ok(Outcome::Halted(_))),
            "the writer halts, {fork}: {:?}",
            forked.writer
        );
        let Ok(HostOutcome::Completed(Outcome::Halted(value))) = forked.reader
        else {
            panic!("the reader halts, {fork}: {:?}", forked.reader);
        };
        let actual =
            read_back_value(&cut.arena, store, value, &mut core).expect("the answer reads back");
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(&core, actual, expected),
            "the reader answers seven beside the writer's pair, {fork}"
        );
    });
}

/// The program `x ← return 5; y ← return (x, 9); return (y, x)`, focused with
/// its writers fused and with both named, answers `((5, 9), 5)` on each tier.
/// A run that ignores the marks answers as the sequential schedule, and the
/// named second writer reads the outer binder from under its own `μα`.
#[test]
fn a_named_writer_runs_as_its_fused_bind()
{
    let mut core = CoreArena::new();
    let (five, nine) = (
        integer(&mut core, Digits("5")),
        integer(&mut core, Digits("9")),
    );
    let first = core.computation_return(five);
    let outer = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let pair = core.value_tuple(&[outer, nine]);
    let second = core.computation_return(pair);
    let fields = [
        core.value_variable(Zone::Intuitionistic, 0_u32.into()),
        core.value_variable(Zone::Intuitionistic, 1_u32.into()),
    ];
    let answered = core.value_tuple(&fields);
    let tail = core.computation_return(answered);
    let inner = core.computation_bind(second, tail);
    let program = core.computation_bind(first, inner);
    let written = core.value_tuple(&[five, nine]);
    let expected = core.value_tuple(&[written, five]);
    let mut run = |writers: &Writers| {
        let mut arena = CommandArena::new();
        let root = focus_computation(&core, program, &mut arena, &mut Provenance::new(), writers)
            .expect("the program focuses");
        assert_eq!(Ok(FreeSet::default()), check_command(&arena, root));
        for &tier in tiers() {
            let mut store = Store::new();
            let outcome = evaluate_on(
                tier,
                &arena,
                &Definitions::new(),
                root,
                budget(),
                RunInputs::new(&mut store),
            );
            let Ok(Outcome::Halted(value)) = outcome
            else {
                panic!("the program halts on {tier:?}: {outcome:?}");
            };
            let actual =
                read_back_value(&arena, &store, value, &mut core).expect("the answer reads back");
            assert_eq!(
                CertificateEquality::Equal,
                equal_certificate_syntax(&core, actual, expected),
                "the program answers `((5, 9), 5)` on {tier:?}"
            );
        }
        render_command(&arena, root)
    };
    let fused = run(&Writers::NONE);
    let named = run(&[first, second].into_iter().collect());
    assert_ne!(fused, named, "the named writers focus apart");
}

/// A writer stuck at an operation it has no host for ends with no answer, and
/// its reader stops stuck at the read, on each tier and each fork.
#[test]
fn a_writer_with_no_answer_leaves_its_read_stuck()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let asked = asked(&mut core);
    let stuck = core.computation_perform(asked, "op".into(), one);
    let thunk = core.value_thunk(stuck);
    let program = core.computation_return(thunk);
    let answer = core.value_type_base(BaseType::Integer);
    let cut = cut(&mut core, program, answer);
    on_each_fork(&cut, |fork, forked, _store| {
        assert!(
            matches!(
                forked.writer,
                Ok(Outcome::Stuck(Stuck::PerformNoHandler(_)))
            ),
            "the writer stops at its operation, {fork}: {:?}",
            forked.writer
        );
        let Ok(HostOutcome::Completed(Outcome::Stuck(Stuck::PerformNoHandler(at)))) = forked.reader
        else {
            panic!("the reader stops stuck, {fork}: {:?}", forked.reader);
        };
        let Some(&CommandNode::Perform {
            ref signature,
            ref operation,
            ..
        }) = cut.arena.command(at)
        else {
            panic!("the reader stops at a perform, {fork}");
        };
        assert_eq!(
            (signature.name().as_ref(), operation.as_ref()),
            (CELL, READ),
            "the reader stops at its read, {fork}"
        );
    });
}
