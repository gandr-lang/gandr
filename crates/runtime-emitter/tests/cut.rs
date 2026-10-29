//! A run whose independent cuts are scheduled: each marked writer spawned on
//! the serial fork, run over a store of its own, and read where its binder is
//! first needed, on each tier, against the sequential schedule of the same
//! program.

use core::convert::Infallible;

use gandr_core_fork::Serial;
use gandr_core_sequent::CELL;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::FreeSet;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::READ;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::Writers;
use gandr_core_sequent::check_command;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::read_back_value;
use gandr_core_sequent::spawn_independent;
use gandr_core_term::CertificateEquality;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::equal_certificate_syntax;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::Summand;
use gandr_runtime_emitter::Choice;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostOutcome;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::RunInputs;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate_on_with_host;
use gandr_runtime_emitter::evaluate_scheduled_on;

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

/// A de Bruijn index: the number of binders out a variable names.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Outward(u32);

/// The variable `index` binders out.
///
/// # Specification
/// trivial.
fn variable(
    core: &mut CoreArena,
    index: Outward,
) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, index.0.into())
}

/// `E.op(1)`, where `E` has one operation `op` from an integer to an integer.
///
/// # Specification
/// trivial.
fn ask(core: &mut CoreArena) -> ComputationId
{
    let integer_type = core.value_type_base(BaseType::Integer);
    let asked = EffectSig::new("E".into(), [EffectOp {
        name: "op".into(),
        payload: integer_type,
        reply: integer_type,
    }])
    .expect("one operation");
    let one = integer(core, Digits("1"));
    core.computation_perform(asked, "op".into(), one)
}

/// The caller's host: it answers `E.op` with seven.
#[derive(Clone, Copy, Debug)]
struct Answering;

impl HostHandler for Answering
{
    type Abort = Infallible;

    /// Answer `E.op` with seven, and decline any other operation.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Infallible>
    {
        if request.signature.name().as_ref() != "E" || request.operation.as_ref() != "op" {
            return HostReply::Decline;
        }
        let magnitude = Magnitude::from_decimal_text("7".into()).expect("decimal digits");
        let seven = gandr_core_sequent::HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            magnitude,
        )));
        values
            .allocate(seven)
            .map_or(HostReply::Decline, HostReply::Resume)
    }
}

/// A program focused into one arena twice: as written, and with `writers`
/// named and scheduled.
#[derive(Debug)]
struct Scheduled
{
    /// The arena both roots belong to.
    arena: CommandArena,
    /// The program as written: every writer fused with its binder.
    sequential: CommandId,
    /// The program with its named writers spawned.
    spawning: CommandId,
    /// The definitions the scheduled root unfolds.
    definitions: Definitions,
}

/// `program` focused as written and with `writers` named, the latter
/// scheduled, over `definitions`.
///
/// # Specification
/// trivial.
fn scheduled(
    core: &CoreArena,
    program: ComputationId,
    writers: &Writers,
    definitions: &Definitions,
) -> Scheduled
{
    let mut arena = CommandArena::new();
    let sequential = focus_computation(
        core,
        program,
        &mut arena,
        &mut Provenance::new(),
        &Writers::NONE,
    )
    .expect("the program focuses");
    let named = focus_computation(core, program, &mut arena, &mut Provenance::new(), writers)
        .expect("the program focuses with its writers named");
    let (spawning, definitions) =
        spawn_independent(&mut arena, (named, definitions)).expect("the program schedules");
    assert_eq!(Ok(FreeSet::default()), check_command(&arena, spawning));
    assert_ne!(
        sequential, spawning,
        "the named writers are scheduled apart"
    );
    Scheduled {
        arena,
        sequential,
        spawning,
        definitions,
    }
}

/// The value `program` answers on `tier` on each schedule, read back into
/// `core`: the sequential one first, then the scheduled one on the serial
/// fork, each offering its other operations to `host`.
///
/// # Specification
/// trivial.
fn answers<Host>(
    core: &mut CoreArena,
    program: &Scheduled,
    tier: Tier,
    host: &mut Host,
) -> (ValueId, ValueId)
where
    Host: HostHandler<Abort = Infallible> + Send,
{
    let mut store = Store::new();
    let outcome = evaluate_on_with_host(
        tier,
        (&program.arena, &program.definitions, program.sequential),
        (budget(), RunInputs::new(&mut store)),
        host,
    );
    let Ok(HostOutcome::Completed(Outcome::Halted(value))) = outcome
    else {
        panic!("the sequential schedule halts on {tier:?}: {outcome:?}");
    };
    let sequential =
        read_back_value(&program.arena, &store, value, core).expect("the answer reads back");
    let mut store = Store::new();
    let outcome = evaluate_scheduled_on(
        &Serial,
        Choice::Tier(tier),
        (&program.arena, &program.definitions, program.spawning),
        (budget(), &mut store),
        host,
    );
    let Ok(HostOutcome::Completed(Outcome::Halted(value))) = outcome
    else {
        panic!("the scheduled run halts on {tier:?}: {outcome:?}");
    };
    let scheduled =
        read_back_value(&program.arena, &store, value, core).expect("the answer reads back");
    (sequential, scheduled)
}

/// `c ← return 5; x ← return (c, 9); y ← E.op(1); return (y, x)`, its second
/// writer named, spawns a writer over the capture `c`. The reader asks the
/// caller's host for seven before it reads `x`, and answers `(7, (5, 9))` on
/// each tier, as the sequential schedule does.
#[test]
fn a_read_answers_what_its_writer_halts_with()
{
    let mut core = CoreArena::new();
    let (five, nine) = (
        integer(&mut core, Digits("5")),
        integer(&mut core, Digits("9")),
    );
    let bound = core.computation_return(five);
    let captured = variable(&mut core, Outward(0));
    let pair = core.value_tuple(&[captured, nine]);
    let writer = core.computation_return(pair);
    let asked = ask(&mut core);
    let fields = [
        variable(&mut core, Outward(0)),
        variable(&mut core, Outward(1)),
    ];
    let answer = core.value_tuple(&fields);
    let returned = core.computation_return(answer);
    let then = core.computation_bind(asked, returned);
    let read = core.computation_bind(writer, then);
    let program = core.computation_bind(bound, read);
    let program = scheduled(
        &core,
        program,
        &core::iter::once(writer).collect(),
        &Definitions::new(),
    );
    let seven = integer(&mut core, Digits("7"));
    let written = core.value_tuple(&[five, nine]);
    let expected = core.value_tuple(&[seven, written]);
    for &tier in tiers() {
        let (sequential, scheduled) = answers(&mut core, &program, tier, &mut Answering);
        for (schedule, actual) in [("sequential", sequential), ("scheduled", scheduled)] {
            assert_eq!(
                CertificateEquality::Equal,
                equal_certificate_syntax(&core, actual, expected),
                "the {schedule} run answers seven beside the writer's pair on {tier:?}"
            );
        }
    }
}

/// `x ← (a ← return 5; b ← return 9; return (a, b)); y ← return (x, 3);
/// return (y, x)`, every writer named: the first writer spawns writers of its
/// own, and the last reads `x` before its spawn. On each tier the run answers
/// `(((5, 9), 3), (5, 9))`, as the sequential schedule does.
#[test]
fn nested_writers_answer_as_their_sequential_schedule()
{
    let mut core = CoreArena::new();
    let (five, nine, three) = (
        integer(&mut core, Digits("5")),
        integer(&mut core, Digits("9")),
        integer(&mut core, Digits("3")),
    );
    let first = core.computation_return(five);
    let second = core.computation_return(nine);
    let fields = [
        variable(&mut core, Outward(1)),
        variable(&mut core, Outward(0)),
    ];
    let inner_pair = core.value_tuple(&fields);
    let inner_returned = core.computation_return(inner_pair);
    let inner_then = core.computation_bind(second, inner_returned);
    let outer = core.computation_bind(first, inner_then);
    let x = variable(&mut core, Outward(0));
    let dependent_pair = core.value_tuple(&[x, three]);
    let dependent = core.computation_return(dependent_pair);
    let fields = [
        variable(&mut core, Outward(0)),
        variable(&mut core, Outward(1)),
    ];
    let answer = core.value_tuple(&fields);
    let returned = core.computation_return(answer);
    let then = core.computation_bind(dependent, returned);
    let program = core.computation_bind(outer, then);
    let program = scheduled(
        &core,
        program,
        &[outer, first, second, dependent].into_iter().collect(),
        &Definitions::new(),
    );
    let written = core.value_tuple(&[five, nine]);
    let depending = core.value_tuple(&[written, three]);
    let expected = core.value_tuple(&[depending, written]);
    for &tier in tiers() {
        let (sequential, scheduled) = answers(&mut core, &program, tier, &mut Answering);
        for (schedule, actual) in [("sequential", sequential), ("scheduled", scheduled)] {
            assert_eq!(
                CertificateEquality::Equal,
                equal_certificate_syntax(&core, actual, expected),
                "the {schedule} run answers `(((5, 9), 3), (5, 9))` on {tier:?}"
            );
        }
    }
}

/// `x ← E.op(1); return x`, its writer named against the mark's claim: the
/// writer's own host declines `E.op`, so the writer ends with no answer, and
/// the reader stops stuck at its read, on each tier.
#[test]
fn a_writer_with_no_answer_leaves_its_read_stuck()
{
    let mut core = CoreArena::new();
    let asked = ask(&mut core);
    let x = variable(&mut core, Outward(0));
    let returned = core.computation_return(x);
    let program = core.computation_bind(asked, returned);
    let program = scheduled(
        &core,
        program,
        &core::iter::once(asked).collect(),
        &Definitions::new(),
    );
    for &tier in tiers() {
        let mut store = Store::new();
        let outcome = evaluate_scheduled_on(
            &Serial,
            Choice::Tier(tier),
            (&program.arena, &program.definitions, program.spawning),
            (budget(), &mut store),
            &mut Answering,
        );
        let Ok(HostOutcome::Completed(Outcome::Stuck(Stuck::PerformNoHandler(at)))) = outcome
        else {
            panic!("the reader stops stuck on {tier:?}: {outcome:?}");
        };
        let Some(&CommandNode::Perform {
            ref signature,
            ref operation,
            ..
        }) = program.arena.command(at)
        else {
            panic!("the reader stops at a perform on {tier:?}");
        };
        assert_eq!(
            (signature.name().as_ref(), operation.as_ref()),
            (CELL, READ),
            "the reader stops at its read on {tier:?}"
        );
    }
}

/// `c ← return k; x ← return (c, 9); return x`, its second writer named,
/// where `k` is an opaque constant: the writer's thunk captures it, and the
/// copy carries it into the writer's store. On each tier the run answers
/// `(k, 9)`, as the sequential schedule does.
#[test]
fn a_writer_over_an_opaque_constant_answers_as_its_sequential_schedule()
{
    let mut core = CoreArena::new();
    let mut definitions = Definitions::new();
    let opaque = definitions.push(Definition::Opaque);
    let constant = core.value_constant(opaque);
    let nine = integer(&mut core, Digits("9"));
    let bound = core.computation_return(constant);
    let captured = variable(&mut core, Outward(0));
    let pair = core.value_tuple(&[captured, nine]);
    let writer = core.computation_return(pair);
    let x = variable(&mut core, Outward(0));
    let returned = core.computation_return(x);
    let read = core.computation_bind(writer, returned);
    let program = core.computation_bind(bound, read);
    let program = scheduled(
        &core,
        program,
        &core::iter::once(writer).collect(),
        &definitions,
    );
    let expected = core.value_tuple(&[constant, nine]);
    for &tier in tiers() {
        let (sequential, scheduled) = answers(&mut core, &program, tier, &mut Answering);
        for (schedule, actual) in [("sequential", sequential), ("scheduled", scheduled)] {
            assert_eq!(
                CertificateEquality::Equal,
                equal_certificate_syntax(&core, actual, expected),
                "the {schedule} run answers the constant beside nine on {tier:?}"
            );
        }
    }
}

/// `(λf. x ← (force f) 7; return (x, 9)) (thunk { λy. return y })`, its
/// writer `(force f) 7` named: the writer's capture is a function, which the
/// copy carries as code. On each tier the run answers `(7, 9)`, as the
/// sequential schedule does.
#[test]
fn a_writer_over_a_captured_function_answers_as_its_sequential_schedule()
{
    let mut core = CoreArena::new();
    let (seven, nine) = (
        integer(&mut core, Digits("7")),
        integer(&mut core, Digits("9")),
    );
    let y = variable(&mut core, Outward(0));
    let identity = core.computation_return(y);
    let identity = core.computation_lambda(identity);
    let identity = core.value_thunk(identity);
    let f = variable(&mut core, Outward(0));
    let forced = core.computation_force(f);
    let writer = core.computation_application(forced, seven);
    let x = variable(&mut core, Outward(0));
    let pair = core.value_tuple(&[x, nine]);
    let returned = core.computation_return(pair);
    let read = core.computation_bind(writer, returned);
    let function = core.computation_lambda(read);
    let program = core.computation_application(function, identity);
    let program = scheduled(
        &core,
        program,
        &core::iter::once(writer).collect(),
        &Definitions::new(),
    );
    let expected = core.value_tuple(&[seven, nine]);
    for &tier in tiers() {
        let (sequential, scheduled) = answers(&mut core, &program, tier, &mut Answering);
        for (schedule, actual) in [("sequential", sequential), ("scheduled", scheduled)] {
            assert_eq!(
                CertificateEquality::Equal,
                equal_certificate_syntax(&core, actual, expected),
                "the {schedule} run answers what the function answers beside nine on {tier:?}"
            );
        }
    }
}

/// `(fix self. λb. case b of inl _ ⇒ x ← (force self) (inr ()); return (x, 1)
/// | inr _ ⇒ return 7) (inl ())`, its writer `(force self) (inr ())` named:
/// the writer captures the fixpoint it runs in. The crossing refused that
/// fixpoint, so the read stuck where the sequential run answers. On each tier
/// the run answers `(7, 1)`, as the sequential schedule does.
#[test]
fn a_recursive_writer_capturing_its_own_fixpoint_answers_2954()
{
    let mut core = CoreArena::new();
    let (one, seven) = (
        integer(&mut core, Digits("1")),
        integer(&mut core, Digits("7")),
    );
    let unit = core.value_unit();
    let left = core.value_injection(Summand::from(0_usize), unit);
    let right = core.value_injection(Summand::from(1_usize), unit);
    // Under `self, b, _`: the recursive call, then the pair it answers into.
    let own = variable(&mut core, Outward(2));
    let forced = core.computation_force(own);
    let writer = core.computation_application(forced, right);
    let x = variable(&mut core, Outward(0));
    let pair = core.value_tuple(&[x, one]);
    let returned = core.computation_return(pair);
    let recursing = core.computation_bind(writer, returned);
    let ending = core.computation_return(seven);
    let b = variable(&mut core, Outward(0));
    let case = core.computation_case(b, &[recursing, ending]);
    let function = core.computation_lambda(case);
    let fixpoint = core.computation_fixpoint(function, FixpointEvidence::Partial);
    let program = core.computation_application(fixpoint, left);
    let program = scheduled(
        &core,
        program,
        &core::iter::once(writer).collect(),
        &Definitions::new(),
    );
    let expected = core.value_tuple(&[seven, one]);
    for &tier in tiers() {
        let (sequential, scheduled) = answers(&mut core, &program, tier, &mut Answering);
        for (schedule, actual) in [("sequential", sequential), ("scheduled", scheduled)] {
            assert_eq!(
                CertificateEquality::Equal,
                equal_certificate_syntax(&core, actual, expected),
                "the {schedule} run answers seven beside one on {tier:?}"
            );
        }
    }
}
