//! Focused commands run on the runtime's two tiers: emitted native code
//! where this host has a patcher, the portable executor everywhere. Every
//! run is made on each tier and the tiers' answers compared by structure;
//! each test then states the answer it expects — a reading of the halted
//! value, or the reason the run stopped stuck.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ConstructorResolver;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::CovariableIndex;
use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::Environment;
use gandr_core_sequent::FreeSet;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::PatternArm;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::ReadbackRefusal;
use gandr_core_sequent::Selector;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::check_command;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::focus_value;
use gandr_core_sequent::read_back_terminal;
use gandr_core_sequent::read_back_value;
use gandr_core_sequent::reify_command;
use gandr_core_sequent::render_command;
use gandr_core_sequent::unfocus_command;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::memory::MemoryForm;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Form;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::Status;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::TransferRefusal;
use gandr_runtime_emitter::evaluate_on;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::Sym;

/// The decimal digits of a test literal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Digits(&'static str);

/// The jumps a run may take: no test term comes near.
///
/// # Specification
/// trivial.
fn budget() -> Fuel
{
    Fuel::from(1_usize << 20)
}

/// A run's outcome and the store its values were moved into.
struct Ran
{
    /// How the run ended.
    outcome: Outcome,
    /// The caller's store.
    store: Store,
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

/// One step of spelling a value: name its children first, then spell it
/// from theirs.
#[derive(Clone, Copy, Debug)]
enum Spell
{
    /// Queue the value's children before it.
    Enter(HeapValueId),
    /// Spell the value; its children are spelled.
    Write(HeapValueId),
}

/// The values `value` names directly: a constructed value's fields and a
/// closure's bound values.
///
/// # Specification
/// trivial.
fn named(
    store: &Store,
    value: HeapValueId,
) -> Vec<HeapValueId>
{
    match store.value(value) {
        Some(&HeapValue::Constructed { ref fields, .. }) => fields.to_vec(),
        Some(
            &HeapValue::Thunk { environment, .. }
            | &HeapValue::Fixpoint { environment, .. }
            | &HeapValue::Closure { environment, .. },
        ) => store.bound_values(environment).collect(),
        None
        | Some(
            &HeapValue::Literal(_)
            | &HeapValue::Opaque(_)
            | &HeapValue::Capability
            | &HeapValue::Stack { .. },
        ) => Vec::new(),
    }
}

/// The value `value` of `store`, spelled from its children's `spellings`.
///
/// # Specification
/// trivial.
fn spelled_from(
    store: &Store,
    value: HeapValueId,
    spellings: &BTreeMap<HeapValueId, String>,
) -> String
{
    let child = |held: HeapValueId| spellings.get(&held).cloned().unwrap_or_default();
    let bound = |environment: Environment| {
        store
            .bound_values(environment)
            .map(child)
            .collect::<Vec<_>>()
            .join(", ")
    };
    match store.value(value) {
        None => String::from("dangling"),
        Some(&HeapValue::Literal(ref literal)) => format!("{literal:?}"),
        Some(&HeapValue::Constructed {
            ref tag,
            ref fields,
        }) => {
            let fields: Vec<String> = fields.iter().map(|&field| child(field)).collect();
            format!("{tag:?}({})", fields.join(", "))
        },
        Some(&HeapValue::Thunk {
            body, environment, ..
        }) => format!("thunk {body:?} [{}]", bound(environment)),
        Some(&HeapValue::Fixpoint {
            body, environment, ..
        }) => format!("fixpoint {body:?} [{}]", bound(environment)),
        Some(&HeapValue::Closure {
            producer,
            environment,
        }) => format!("closure {producer:?} [{}]", bound(environment)),
        Some(
            held @ (&HeapValue::Opaque(_) | &HeapValue::Capability | &HeapValue::Stack { .. }),
        ) => {
            format!("{held:?}")
        },
    }
}

/// The value `value` of `store`, spelled by structure, never by address.
///
/// # Specification
/// trivial.
fn spelled(
    store: &Store,
    value: HeapValueId,
) -> String
{
    let mut spellings: BTreeMap<HeapValueId, String> = BTreeMap::new();
    let mut work = Vec::from([Spell::Enter(value)]);
    while let Some(step) = work.pop() {
        match step {
            Spell::Enter(held) if !spellings.contains_key(&held) => {
                work.push(Spell::Write(held));
                work.extend(named(store, held).into_iter().map(Spell::Enter));
            },
            Spell::Write(held) => {
                let spelling = spelled_from(store, held, &spellings);
                spellings.insert(held, spelling);
            },
            Spell::Enter(_) => {},
        }
    }
    spellings.remove(&value).unwrap_or_default()
}

/// What a run answered, spelled so two stores' answers compare.
///
/// # Specification
/// trivial.
fn fingerprint(run: &Result<Ran, Declined>) -> String
{
    let (outcome, store) = match *run {
        Err(ref declined) => return format!("declined {declined:?}"),
        Ok(Ran {
            ref outcome,
            ref store,
        }) => (outcome, store),
    };
    match *outcome {
        Outcome::Halted(value) => format!("halted {}", spelled(store, value)),
        Outcome::Stuck(ref stuck) => {
            let held = match *stuck {
                Stuck::Unobservable { value, .. }
                | Stuck::Unmatched { value, .. }
                | Stuck::NonScalar(value)
                | Stuck::ResumedNonStack { value, .. } => spelled(store, value),
                Stuck::PerformNoHandler(_)
                | Stuck::ShiftNoReset(_)
                | Stuck::Primitive(_)
                | Stuck::UndefinedConstant(_)
                | Stuck::CyclicConstant(_)
                | Stuck::Unended(_) => String::new(),
            };
            format!("stuck {stuck:?}: {held}")
        },
    }
}

/// Run `root` on every tier this host has, assert the tiers' answers equal,
/// and answer the executor's run.
///
/// # Specification
/// trivial.
fn ran(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    fuel: Fuel,
) -> Result<Ran, Declined>
{
    let mut runs: Vec<(Tier, Result<Ran, Declined>)> = tiers()
        .iter()
        .map(|&tier| {
            let mut store = Store::new();
            let outcome = evaluate_on(tier, arena, definitions, root, fuel, &mut store);
            (tier, outcome.map(|outcome| Ran { outcome, store }))
        })
        .collect();
    let (_, executor) = runs.pop().expect("the executor runs on every host");
    let expected = fingerprint(&executor);
    for &(tier, ref run) in &runs {
        assert_eq!(
            expected,
            fingerprint(run),
            "{tier:?} and the executor differ"
        );
    }
    executor
}

/// Run `root` and answer the value it halted with and the store holding it.
///
/// # Specification
/// trivial.
fn halted(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
) -> (Store, HeapValueId)
{
    let Ran { outcome, store } = ran(arena, definitions, root, budget())
        .unwrap_or_else(|declined| panic!("the run declined: {declined}"));
    let Outcome::Halted(value) = outcome
    else {
        panic!("the run halts: {outcome:?}");
    };
    (store, value)
}

/// Run `root` and answer how it stopped stuck.
///
/// # Specification
/// trivial.
fn stuck(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
) -> (Store, Stuck)
{
    let Ran { outcome, store } = ran(arena, definitions, root, budget())
        .unwrap_or_else(|declined| panic!("the run declined: {declined}"));
    let Outcome::Stuck(stuck) = outcome
    else {
        panic!("the run sticks: {outcome:?}");
    };
    (store, stuck)
}

/// The partial application of `sub` to 19 halts with a function, which read
/// back and applied to 7 answers 12.
#[test]
fn native_arithmetic_and_partial_application()
{
    let mut core = CoreArena::new();
    let sub = gandr_core_term::primitive::PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "sub")
        .expect("native sub");
    let value = sub.thunk(&mut core);
    let forced = core.computation_force(value);
    let first = integer(&mut core, Digits("19"));
    let partial = core.computation_application(forced, first);
    let mut arena = CommandArena::new();
    let command = focus_computation(&core, partial, &mut arena, &mut Provenance::new())
        .expect("a closed term focuses");
    let (store, value) = halted(&arena, &Definitions::new(), command);
    let partial =
        read_back_terminal(&arena, &store, value, &mut core).expect("a function reads back");
    let second = integer(&mut core, Digits("7"));
    let saturated = core.computation_application(partial, second);
    assert_eq!(evaluated(&mut core, saturated), "⟨12 |+ ★⟩");
}

/// A prelude spelling used by a native fixture.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct NativeName(&'static str);

/// Apply the prelude primitive `name` to `arguments`.
///
/// # Specification
/// trivial.
fn native(
    core: &mut CoreArena,
    name: NativeName,
    arguments: &[ValueId],
) -> ComputationId
{
    let primitive = gandr_core_term::primitive::PRELUDE
        .iter()
        .find(|row| row.name().as_ref() == name.0)
        .expect("a named prelude primitive");
    let thunk = primitive.thunk(core);
    let mut term = core.computation_force(thunk);
    for &argument in arguments {
        term = core.computation_application(term, argument);
    }
    term
}

/// Native identity preserves its integer argument.
#[test]
fn identity_applied_returns_its_argument()
{
    let mut core = CoreArena::new();
    let argument = integer(&mut core, Digits("5"));
    let term = native(&mut core, NativeName("prim.id"), &[argument]);
    assert_eq!(evaluated(&mut core, term), "⟨5 |+ ★⟩");
}

/// Native constant keeps the first of two distinct arguments.
#[test]
fn const_applied_returns_its_first_argument()
{
    let mut core = CoreArena::new();
    let first = integer(&mut core, Digits("7"));
    let second = integer(&mut core, Digits("9"));
    let term = native(&mut core, NativeName("prim.const"), &[first, second]);
    assert_eq!(evaluated(&mut core, term), "⟨7 |+ ★⟩");
}

/// Saturated native addition returns the exact sum.
#[test]
fn native_integer_addition_returns_sum()
{
    let mut core = CoreArena::new();
    let first = integer(&mut core, Digits("1"));
    let second = integer(&mut core, Digits("2"));
    let term = native(&mut core, NativeName("add"), &[first, second]);
    assert_eq!(evaluated(&mut core, term), "⟨3 |+ ★⟩");
}

/// Native comparison returns the true injection for increasing integers.
#[test]
fn native_integer_less_than_returns_true()
{
    let mut core = CoreArena::new();
    let first = integer(&mut core, Digits("1"));
    let second = integer(&mut core, Digits("2"));
    let term = native(&mut core, NativeName("lt"), &[first, second]);
    let unit = core.value_unit();
    let truth = core.value_injection(Side::Left.into(), unit);
    let expected = core.computation_return(truth);
    assert_eq!(evaluated(&mut core, term), shown(&core, expected));
}

/// Native conjunction selects false from true and false.
#[test]
fn native_boolean_and_returns_false()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let truth = core.value_injection(Side::Left.into(), unit);
    let falsity = core.value_injection(Side::Right.into(), unit);
    let term = native(&mut core, NativeName("and"), &[truth, falsity]);
    let expected = core.computation_return(falsity);
    assert_eq!(evaluated(&mut core, term), shown(&core, expected));
}

/// A prelude thunk admitted as a constant unfolds where it is forced.
#[test]
fn a_forced_prelude_name_resolves_to_its_builtin()
{
    let mut core = CoreArena::new();
    let primitive = gandr_core_term::primitive::PRELUDE
        .iter()
        .find(|row| row.name().as_ref() == "prim.id")
        .expect("the identity prelude binding");
    let thunk = primitive.thunk(&mut core);
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let binding = focus_value(&core, thunk, &mut arena, &mut provenance).expect("a thunk focuses");
    let mut definitions = Definitions::new();
    let constant = definitions.push(Definition::Transparent(binding));
    let reference = core.value_constant(constant);
    let forced = core.computation_force(reference);
    let argument = integer(&mut core, Digits("5"));
    let term = core.computation_application(forced, argument);
    let root =
        focus_computation(&core, term, &mut arena, &mut provenance).expect("a closed term focuses");
    let (store, value) = halted(&arena, &definitions, root);
    let read = read_back_terminal(&arena, &store, value, &mut core).expect("the answer reads back");
    assert_eq!(shown(&core, read), "⟨5 |+ ★⟩");
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
    let magnitude = Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits");
    core.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        magnitude,
    )))
}

/// A core computation as the IL renders its focusing.
///
/// # Specification
/// trivial.
fn shown(
    core: &CoreArena,
    computation: ComputationId,
) -> String
{
    let mut arena = CommandArena::new();
    let command = focus_computation(core, computation, &mut arena, &mut Provenance::new())
        .expect("a read-back term focuses");
    render_command(&arena, command)
}

/// Focus a closed computation, run it with no definitions, and show its
/// terminal's reading.
///
/// # Specification
/// trivial.
fn evaluated(
    core: &mut CoreArena,
    computation: ComputationId,
) -> String
{
    let mut arena = CommandArena::new();
    let command = focus_computation(core, computation, &mut arena, &mut Provenance::new())
        .expect("a closed term focuses");
    let (store, value) = halted(&arena, &Definitions::new(), command);
    let back = read_back_terminal(&arena, &store, value, core).expect("the terminal reads back");
    shown(core, back)
}

/// An independently specified observable control result.
enum ControlExpectation
{
    /// A returned value, compared structurally after readback.
    Value(ValueId),
    /// An unhandled request, retaining both parts of its qualified name.
    Perform(&'static str, &'static str),
    /// A shift with no reachable reset.
    Shift,
}

/// Focus `program`, check it is closed, run it on the tiers, and check its
/// outcome against `expected`.
///
/// # Specification
/// trivial.
fn assert_control(
    core: &mut CoreArena,
    program: ComputationId,
    expected: ControlExpectation,
)
{
    let mut arena = CommandArena::new();
    let root = focus_computation(core, program, &mut arena, &mut Provenance::new())
        .expect("control focuses");
    assert_eq!(Ok(FreeSet::default()), check_command(&arena, root));
    let Ran { outcome, store } = ran(&arena, &Definitions::new(), root, budget())
        .unwrap_or_else(|declined| panic!("the run declined: {declined}"));
    match (outcome, expected) {
        (Outcome::Halted(value), ControlExpectation::Value(expected)) => {
            let actual =
                read_back_value(&arena, &store, value, core).expect("literal result reads back");
            assert_eq!(
                gandr_core_term::CertificateEquality::Equal,
                gandr_core_term::equal_certificate_syntax(core, actual, expected)
            );
        },
        (
            Outcome::Stuck(Stuck::PerformNoHandler(at)),
            ControlExpectation::Perform(name, operation),
        ) => {
            let CommandNode::Perform {
                ref signature,
                operation: ref found,
                ..
            } = *arena.command(at).expect("perform instruction")
            else {
                panic!("blame must name the Perform instruction");
            };
            assert_eq!(
                (name, operation),
                (signature.name().as_ref(), found.as_ref())
            );
        },
        (Outcome::Stuck(Stuck::ShiftNoReset(at)), ControlExpectation::Shift) => {
            assert!(matches!(arena.command(at), Some(CommandNode::Shift { .. })));
        },
        (outcome, _) => panic!("unexpected control outcome: {outcome:?}"),
    }
}

/// One integer operation for control fixtures.
///
/// # Specification
/// trivial.
fn effect(
    core: &mut CoreArena,
    name: gandr_core_term::effect::EffectName,
    operation: gandr_core_term::effect::OperationName,
) -> gandr_core_term::effect::EffectSig
{
    let integer = core.value_type_base(gandr_kernel_term::BaseType::Integer);
    gandr_core_term::effect::EffectSig::new(name, [gandr_core_term::effect::EffectOp {
        name: operation,
        payload: integer,
        reply: integer,
    }])
    .expect("one operation")
}

/// A one-operation handler, retaining the signature's operation name.
///
/// # Specification
/// trivial.
fn handler(
    core: &mut CoreArena,
    signature: gandr_core_term::effect::EffectSig,
    subject: ComputationId,
    on_return: ComputationId,
    body: ComputationId,
) -> ComputationId
{
    let operation = signature
        .operations()
        .next()
        .expect("one-operation fixture")
        .name
        .clone();
    core.computation_handle(
        signature,
        subject,
        on_return,
        alloc::sync::Arc::from([gandr_core_term::control::EffectClause { operation, body }]),
    )
}

#[test]
fn handler_resumption_under_projection_uses_the_ambient_continuation_once()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let seven = integer(&mut core, Digits("7"));
    let five_ret = core.computation_return(five);
    let seven_ret = core.computation_return(seven);
    let continuation = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let signature = effect(&mut core, "E".into(), "op".into());
    let performed = core.computation_perform(signature.clone(), "op".into(), five);
    let on_return = core.computation_with(five_ret, seven_ret);
    let clause = core.computation_resume(continuation, five_ret);
    let handled = handler(&mut core, signature, performed, on_return, clause);
    let projected = core.computation_project(Side::Right, handled);
    assert_control(&mut core, projected, ControlExpectation::Value(seven));
}

#[test]
fn hand_built_effect_cases_agree()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let seven = integer(&mut core, Digits("7"));
    let nine = integer(&mut core, Digits("9"));
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let identity = core.computation_return(zero);
    let payload = core.computation_return(outer);
    let ret_seven = core.computation_return(seven);
    let ret_nine = core.computation_return(nine);
    let ret_one = core.computation_return(one);
    let ret_two = core.computation_return(two);
    let signature = effect(&mut core, "E".into(), "op".into());
    let perform = core.computation_perform(signature.clone(), "op".into(), five);
    assert_control(&mut core, perform, ControlExpectation::Perform("E", "op"));
    let buried = core.computation_bind(perform, identity);
    assert_control(&mut core, buried, ControlExpectation::Perform("E", "op"));
    let doubled = core.value_tuple(&[zero, zero]);
    let double_return = core.computation_return(doubled);
    let discard = handler(
        &mut core,
        signature.clone(),
        perform,
        double_return,
        ret_nine,
    );
    assert_control(&mut core, discard, ControlExpectation::Value(nine));
    let resume_seven = core.computation_resume(zero, ret_seven);
    let resumed = handler(
        &mut core,
        signature.clone(),
        perform,
        identity,
        resume_seven,
    );
    assert_control(&mut core, resumed, ControlExpectation::Value(seven));
    let resume_payload = core.computation_resume(zero, payload);
    let payload_flow = handler(
        &mut core,
        signature.clone(),
        perform,
        identity,
        resume_payload,
    );
    assert_control(&mut core, payload_flow, ControlExpectation::Value(five));
    let doubled_seven = core.value_tuple(&[seven, seven]);
    let returned = handler(
        &mut core,
        signature.clone(),
        ret_seven,
        double_return,
        ret_nine,
    );
    assert_control(
        &mut core,
        returned,
        ControlExpectation::Value(doubled_seven),
    );
    let buried_handled = handler(&mut core, signature.clone(), buried, identity, resume_seven);
    assert_control(&mut core, buried_handled, ControlExpectation::Value(seven));
    let pair = core.value_tuple(&[outer, zero]);
    let pair_return = core.computation_return(pair);
    let second = core.computation_bind(perform, pair_return);
    let first = core.computation_bind(perform, second);
    let resume_one = core.computation_resume(zero, ret_one);
    let deep = handler(&mut core, signature.clone(), first, identity, resume_one);
    let both_one = core.value_tuple(&[one, one]);
    assert_control(&mut core, deep, ControlExpectation::Value(both_one));
    let other = effect(&mut core, "Other".into(), "other".into());
    let other_perform = core.computation_perform(other.clone(), "other".into(), five);
    let inner = handler(
        &mut core,
        other.clone(),
        other_perform,
        identity,
        resume_seven,
    );
    let nested = handler(&mut core, signature.clone(), inner, identity, resume_one);
    assert_control(&mut core, nested, ControlExpectation::Value(seven));
    let barrier = handler(&mut core, other, perform, identity, ret_nine);
    let blocked = handler(&mut core, signature.clone(), barrier, identity, resume_one);
    assert_control(&mut core, blocked, ControlExpectation::Perform("E", "op"));
    let reset = core.computation_reset(ret_seven);
    assert_control(&mut core, reset, ControlExpectation::Value(seven));
    let reset_perform = core.computation_reset(perform);
    let blocked = handler(
        &mut core,
        signature.clone(),
        reset_perform,
        identity,
        resume_one,
    );
    assert_control(&mut core, blocked, ControlExpectation::Perform("E", "op"));
    let thunk = core.value_thunk(perform);
    let force = core.computation_force(thunk);
    let forced = handler(&mut core, signature.clone(), force, identity, resume_seven);
    assert_control(&mut core, forced, ControlExpectation::Value(seven));
    let resume_two = core.computation_resume(outer, ret_two);
    let twice = core.computation_bind(resume_one, resume_two);
    let multishot_force = handler(&mut core, signature, force, identity, twice);
    assert_control(&mut core, multishot_force, ControlExpectation::Value(two));
    let same_operation = effect(&mut core, "Different".into(), "op".into());
    let wrong_interface = handler(&mut core, same_operation, perform, identity, ret_nine);
    assert_control(
        &mut core,
        wrong_interface,
        ControlExpectation::Perform("E", "op"),
    );
}

#[test]
fn hand_built_shift_cases_agree()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let three = integer(&mut core, Digits("3"));
    let four = integer(&mut core, Digits("4"));
    let seven = integer(&mut core, Digits("7"));
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let ret_one = core.computation_return(one);
    let ret_two = core.computation_return(two);
    let ret_three = core.computation_return(three);
    let identity = core.computation_return(zero);
    let pair = core.value_tuple(&[zero, zero]);
    let pair_return = core.computation_return(pair);
    let discard = core.computation_shift(ret_one);
    let simple = core.computation_reset(discard);
    assert_control(&mut core, simple, ControlExpectation::Value(one));
    let discard_bound = core.computation_bind(discard, pair_return);
    let reset = core.computation_reset(discard_bound);
    assert_control(&mut core, reset, ControlExpectation::Value(one));
    let resumed = core.computation_resume(zero, ret_three);
    let shifted = core.computation_shift(resumed);
    let bound = core.computation_bind(shifted, pair_return);
    let reset = core.computation_reset(bound);
    let pair_three = core.value_tuple(&[three, three]);
    assert_control(&mut core, reset, ControlExpectation::Value(pair_three));
    let add = gandr_core_term::primitive::PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "add")
        .expect("native add");
    let added = core.computation_primitive(
        add,
        gandr_core_term::primitive::Arguments::Binary([zero, four]),
    );
    let work = core.computation_bind(shifted, added);
    let reset = core.computation_reset(work);
    assert_control(&mut core, reset, ControlExpectation::Value(seven));
    let first = core.computation_resume(zero, ret_one);
    let second = core.computation_resume(outer, ret_two);
    let twice = core.computation_bind(first, second);
    let shifted_twice = core.computation_shift(twice);
    let bound = core.computation_bind(shifted_twice, identity);
    let reset = core.computation_reset(bound);
    assert_control(&mut core, reset, ControlExpectation::Value(two));
    let nested = core.computation_reset(reset);
    assert_control(&mut core, nested, ControlExpectation::Value(two));
    assert_control(&mut core, discard, ControlExpectation::Shift);
    assert_control(&mut core, discard_bound, ControlExpectation::Shift);
}

#[test]
fn a_shift_unwinds_the_handlers_above_its_reset()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let nine = integer(&mut core, Digits("9"));
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let ret_one = core.computation_return(one);
    let ret_nine = core.computation_return(nine);
    let pair = core.value_tuple(&[zero, zero]);
    let pair_return = core.computation_return(pair);
    let discard = core.computation_shift(ret_one);
    let signature = effect(&mut core, "Unwound".into(), "op".into());
    let handled = handler(&mut core, signature.clone(), discard, pair_return, ret_nine);
    let reset = core.computation_reset(handled);
    assert_control(&mut core, reset, ControlExpectation::Value(one));
    let inner = handler(&mut core, signature.clone(), discard, pair_return, ret_nine);
    let outer = handler(&mut core, signature, inner, pair_return, ret_nine);
    let bound = core.computation_bind(outer, pair_return);
    let reset = core.computation_reset(bound);
    assert_control(&mut core, reset, ControlExpectation::Value(one));
    assert_control(&mut core, handled, ControlExpectation::Shift);
}

/// A counter held at zero: an access that increments through its view
/// and resumes writes one back, a second that increments and aborts
/// writes nothing though it answers its own sum, an aborted access runs
/// its unwind and a resumed one does not, and an access whose body a
/// handler outside the hold resumes still writes back through the frame
/// the resumption replays.
#[test]
fn a_counter_observes_write_back_on_resume_and_none_on_abort()
{
    let mut core = CoreArena::new();
    let zero = integer(&mut core, Digits("0"));
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let ten = integer(&mut core, Digits("10"));
    let resident = core.value_variable(Zone::Linear, 0_u32.into());
    let innermost = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let unit = core.value_unit();
    let ret_unit = core.computation_return(unit);
    let ret_outer = core.computation_return(outer);
    let ret_resident = core.computation_return(resident);
    let add = gandr_core_term::primitive::PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "add")
        .expect("native add");
    let successor = core.computation_primitive(
        add,
        gandr_core_term::primitive::Arguments::Binary([resident, one]),
    );
    let view = DeBruijnIndex::from(0_u32);
    let resume = core.computation_memory(MemoryForm::Resume {
        view,
        value: innermost,
    });
    let abort = core.computation_memory(MemoryForm::Abort { view });
    // n <- v + 1 ; _ <- resume(v, n) ; return n
    let resumed = core.computation_bind(resume, ret_outer);
    let resuming = core.computation_bind(successor, resumed);
    // n <- v + 1 ; _ <- abort(v) ; return n
    let aborted = core.computation_bind(abort, ret_outer);
    let aborting = core.computation_bind(successor, aborted);
    let access = |core: &mut CoreArena, body, unwind| {
        core.computation_memory(MemoryForm::Access {
            held: view,
            body,
            unwind,
        })
    };
    let first = access(&mut core, resuming, ret_unit);
    let second = access(&mut core, aborting, ret_unit);
    let triple = core.value_tuple(&[resident, outer, innermost]);
    let ret_triple = core.computation_return(triple);
    let rest = core.computation_bind(second, ret_triple);
    let body = core.computation_bind(first, rest);
    let counter = core.computation_memory(MemoryForm::Hold { value: zero, body });
    let observed = core.value_tuple(&[one, one, two]);
    assert_control(&mut core, counter, ControlExpectation::Value(observed));

    let signature = effect(&mut core, "Probe".into(), "op".into());
    let probe = core.computation_perform(signature.clone(), "op".into(), zero);
    for (body, expected) in [
        (resuming, ControlExpectation::Value(one)),
        (aborting, ControlExpectation::Perform("Probe", "op")),
    ] {
        let probed = access(&mut core, body, probe);
        let then = core.computation_bind(probed, ret_resident);
        let held = core.computation_memory(MemoryForm::Hold {
            value: zero,
            body: then,
        });
        assert_control(&mut core, held, expected);
    }

    // n <- perform op(v) ; _ <- resume(v, n) ; return n, under a handler
    // outside the hold whose clause resumes with the payload plus ten.
    let performed = core.computation_perform(signature.clone(), "op".into(), resident);
    let asked = core.computation_bind(performed, resumed);
    let asking = access(&mut core, asked, ret_unit);
    let then = core.computation_bind(asking, ret_resident);
    let held = core.computation_memory(MemoryForm::Hold {
        value: zero,
        body: then,
    });
    let payload = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let raised = core.computation_primitive(
        add,
        gandr_core_term::primitive::Arguments::Binary([payload, ten]),
    );
    let resumption = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let ret_innermost = core.computation_return(innermost);
    let replayed = core.computation_resume(resumption, ret_innermost);
    let clause = core.computation_bind(raised, replayed);
    let handled = handler(&mut core, signature, held, ret_innermost, clause);
    assert_control(&mut core, handled, ControlExpectation::Value(ten));
}

#[test]
fn an_exercise_reaches_the_scope_that_introduced_its_capability()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let seven = integer(&mut core, Digits("7"));
    let nine = integer(&mut core, Digits("9"));
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let identity = core.computation_return(zero);
    let ret_seven = core.computation_return(seven);
    let ret_nine = core.computation_return(nine);
    let signature = effect(&mut core, "E".into(), "op".into());
    let scope = |core: &mut CoreArena, subject, body| {
        core.computation_scope(
            signature.clone(),
            subject,
            identity,
            alloc::sync::Arc::from([gandr_core_term::control::EffectClause {
                operation: "op".into(),
                body,
            }]),
        )
    };
    let through_outer = core.computation_exercise(outer, signature.clone(), "op".into(), five);
    let inner = scope(&mut core, through_outer, ret_nine);
    let past = scope(&mut core, inner, ret_seven);
    assert_control(&mut core, past, ControlExpectation::Value(seven));
    let through_inner = core.computation_exercise(zero, signature.clone(), "op".into(), five);
    let inner = scope(&mut core, through_inner, ret_nine);
    let nearest = scope(&mut core, inner, ret_seven);
    assert_control(&mut core, nearest, ControlExpectation::Value(nine));
    let inner = handler(
        &mut core,
        signature.clone(),
        through_inner,
        identity,
        ret_nine,
    );
    let crossed = scope(&mut core, inner, ret_seven);
    assert_control(&mut core, crossed, ControlExpectation::Value(seven));
    let lifted = core.computation_bind(through_inner, identity);
    let reply = core.computation_return(outer);
    let replied = core.computation_resume(zero, reply);
    let resuming = scope(&mut core, lifted, replied);
    assert_control(&mut core, resuming, ControlExpectation::Value(five));
}

/// Fold an integer list with a comparison and a Boolean combiner.
///
/// # Specification
/// trivial.
fn fold_predicate(
    core: &mut CoreArena,
    list: ValueId,
    threshold: ValueId,
    combine: gandr_core_term::primitive::Primitive,
    base: ValueId,
) -> ComputationId
{
    let element = core.value_type_base(gandr_kernel_term::BaseType::Integer);
    let unit = core.value_type_unit();
    let result = core.value_type_sum(&[unit, unit]);
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let one = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let greater = gandr_core_term::primitive::PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "gt")
        .expect("native comparison");
    let predicate = core.computation_primitive(
        greater,
        gandr_core_term::primitive::Arguments::Binary([one, threshold]),
    );
    let combine = core.computation_primitive(
        combine,
        gandr_core_term::primitive::Arguments::Binary([zero, one]),
    );
    let on_cons = core.computation_bind(predicate, combine);
    let on_nil = core.computation_return(base);
    core.computation_list_fold(element, result, list, on_nil, on_cons)
}

/// Handle successful assertions deeply and stop at the first failure.
///
/// # Specification
/// trivial.
fn assertions(
    core: &mut CoreArena,
    signature: gandr_core_term::effect::EffectSig,
    body: ComputationId,
) -> ComputationId
{
    let unit = core.value_unit();
    let yes = core.value_injection(Side::Left.into(), unit);
    let no = core.value_injection(Side::Right.into(), unit);
    let on_return = core.computation_return(yes);
    let failed = core.computation_return(no);
    let reply = core.computation_return(unit);
    let payload = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let shifted_continuation = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let passed = core.computation_resume(shifted_continuation, reply);
    let clause = core.computation_case(payload, &[passed, failed]);
    handler(core, signature, body, on_return, clause)
}

#[test]
fn the_assert_handler_runs_combinator_assertions()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let yes = core.value_injection(Side::Left.into(), unit);
    let no = core.value_injection(Side::Right.into(), unit);
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let three = integer(&mut core, Digits("3"));
    let zero = integer(&mut core, Digits("0"));
    let nil = core.value_list_nil();
    let tail = core.value_list_cons(three, nil);
    let tail = core.value_list_cons(two, tail);
    let list = core.value_list_cons(one, tail);
    let unit_type = core.value_type_unit();
    let boolean = core.value_type_sum(&[unit_type, unit_type]);
    let signature = gandr_core_term::effect::EffectSig::new("Assert".into(), [
        gandr_core_term::effect::EffectOp {
            name: "assert".into(),
            payload: boolean,
            reply: unit_type,
        },
    ])
    .expect("assert interface");
    let and = gandr_core_term::primitive::PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "and")
        .expect("native conjunction");
    let or = gandr_core_term::primitive::PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "or")
        .expect("native disjunction");
    let all = fold_predicate(&mut core, list, zero, and, yes);
    let any = fold_predicate(&mut core, list, two, or, no);
    let result = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let assert = core.computation_perform(signature.clone(), "assert".into(), result);
    let first = core.computation_bind(all, assert);
    let second = core.computation_bind(any, assert);
    let both = core.computation_bind(first, second);
    let program = assertions(&mut core, signature, both);
    assert_control(&mut core, program, ControlExpectation::Value(yes));
}

#[test]
fn the_assert_handler_reports_a_failure()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let yes = core.value_injection(Side::Left.into(), unit);
    let no = core.value_injection(Side::Right.into(), unit);
    let one = integer(&mut core, Digits("1"));
    let five = integer(&mut core, Digits("5"));
    let nil = core.value_list_nil();
    let list = core.value_list_cons(one, nil);
    let unit_type = core.value_type_unit();
    let boolean = core.value_type_sum(&[unit_type, unit_type]);
    let signature = gandr_core_term::effect::EffectSig::new("Assert".into(), [
        gandr_core_term::effect::EffectOp {
            name: "assert".into(),
            payload: boolean,
            reply: unit_type,
        },
    ])
    .expect("assert interface");
    let and = gandr_core_term::primitive::PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "and")
        .expect("native conjunction");
    let all = fold_predicate(&mut core, list, five, and, yes);
    let result = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let assert = core.computation_perform(signature.clone(), "assert".into(), result);
    let checked = core.computation_bind(all, assert);
    let unreachable_signature = effect(&mut core, "Unreachable".into(), "op".into());
    let unreachable = core.computation_perform(unreachable_signature, "op".into(), one);
    let body = core.computation_bind(checked, unreachable);
    let program = assertions(&mut core, signature, body);
    assert_control(&mut core, program, ControlExpectation::Value(no));
}

#[test]
fn a_mock_exec_handler_replaces_a_real_command()
{
    let mut core = CoreArena::new();
    let host =
        gandr_core_term::effect::host::HostSignatures::new(&mut core).expect("host interfaces");
    let program_name = core.value_literal(Literal::Text(gandr_kernel_term::StringLiteral::new(
        "ls".into(),
    )));
    let mode = core.value_literal(Literal::Text(gandr_kernel_term::StringLiteral::new(
        "capture".into(),
    )));
    let arguments = core.value_list_nil();
    let args_mode = core.value_tuple(&[arguments, mode]);
    let payload = core.value_tuple(&[program_name, args_mode]);
    let stdout = core.value_literal(Literal::Text(gandr_kernel_term::StringLiteral::new(
        "mocked-output".into(),
    )));
    let stderr = core.value_literal(Literal::Text(gandr_kernel_term::StringLiteral::new(
        String::new(),
    )));
    let status = integer(&mut core, Digits("0"));
    let error_status = core.value_tuple(&[stderr, status]);
    let output = core.value_tuple(&[stdout, error_status]);
    let reply = core.computation_return(output);
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let on_return = core.computation_return(zero);
    let clause = core.computation_resume(zero, reply);
    let perform = core.computation_perform(host.exec.clone(), "exec".into(), payload);
    let program = handler(&mut core, host.exec, perform, on_return, clause);
    assert_control(&mut core, program, ControlExpectation::Value(output));
}

#[test]
fn literal_stacks_close_flat_frame_scopes_and_resume_in_order()
{
    use gandr_core_term::control::StackFrame;
    let mut core = CoreArena::new();
    let seven = integer(&mut core, Digits("7"));
    let eleven = integer(&mut core, Digits("11"));
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let one = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let pair = core.value_tuple(&[zero, one]);
    let pair_return = core.computation_return(pair);
    let lambda = core.computation_lambda(pair_return);
    let ignored = core.computation_return(seven);
    let bind_body = core.computation_with(ignored, lambda);
    let frames = [
        StackFrame::Apply(seven),
        StackFrame::Bind(bind_body),
        StackFrame::Project(Side::Right),
        StackFrame::Apply(zero),
    ];
    let stack = core.value_reify(alloc::sync::Arc::from(frames));
    let stack_return = core.computation_return(stack);
    let close = core.computation_lambda(stack_return);
    let closed = core.computation_application(close, eleven);
    let expected_stack = core.value_reify(alloc::sync::Arc::from([
        StackFrame::Apply(seven),
        StackFrame::Bind(bind_body),
        StackFrame::Project(Side::Right),
        StackFrame::Apply(eleven),
    ]));
    assert_control(&mut core, closed, ControlExpectation::Value(expected_stack));
    let identity = core.computation_return(zero);
    let fed = core.computation_lambda(identity);
    let resumed = core.computation_resume(stack, fed);
    let close = core.computation_lambda(resumed);
    let program = core.computation_application(close, eleven);
    let expected = core.value_tuple(&[eleven, seven]);
    assert_control(&mut core, program, ControlExpectation::Value(expected));
}

/// A run whose answer holds a captured stack declines moving it into the
/// store: a captured stack is the run's own frames, which no store value
/// spells.
#[test]
fn a_captured_stack_in_an_answer_declines_its_move()
{
    let mut core = CoreArena::new();
    let zero = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let returned = core.computation_return(zero);
    let shifted = core.computation_shift(returned);
    let program = core.computation_reset(shifted);
    let mut arena = CommandArena::new();
    let root = focus_computation(&core, program, &mut arena, &mut Provenance::new())
        .expect("control focuses");
    assert!(matches!(
        ran(&arena, &Definitions::new(), root, budget()),
        Err(Declined::Transfer(TransferRefusal::HostObject(_)))
    ));
}

#[test]
fn native_list_fold_preserves_order_and_outer_scope()
{
    use gandr_core_term::Computation;
    use gandr_core_term::Value;
    use gandr_core_term::ValueType;
    let mut source = CoreArena::new();
    let integer_type = source.value_type_base(gandr_kernel_term::BaseType::Integer);
    let pair_type = source.value_type_product(&[integer_type, integer_type]);
    let result_type = source.value_type_list(pair_type);
    let nil = source.value_list_nil();
    let two = integer(&mut source, Digits("2"));
    let seven = integer(&mut source, Digits("7"));
    let eleven = integer(&mut source, Digits("11"));
    let tail = source.value_list_cons(seven, nil);
    let list = source.value_list_cons(two, tail);
    let head = source.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let result = source.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outer = source.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let paired = source.value_tuple(&[head, outer]);
    let cell = source.value_list_cons(paired, result);
    let on_nil = source.computation_return(nil);
    let on_cons = source.computation_return(cell);
    let fold = source.computation_list_fold(integer_type, result_type, list, on_nil, on_cons);
    let lambda = source.computation_lambda(fold);
    let program = source.computation_application(lambda, eleven);
    let mut focused = CommandArena::new();
    let mut provenance = Provenance::new();
    let root =
        focus_computation(&source, program, &mut focused, &mut provenance).expect("fold focuses");
    let mut target = CoreArena::new();
    let _unrelated = target.value_type_unit();
    let decoded =
        unfocus_command(&focused, root, &mut target).expect("fold annotations travel with the IL");
    let &Computation::Application(lambda, _) = target.computation(decoded).expect("application")
    else {
        panic!("application");
    };
    let &Computation::Lambda(fold) = target.computation(lambda).expect("lambda")
    else {
        panic!("lambda");
    };
    let &Computation::ListFold {
        element, result, ..
    } = target.computation(fold).expect("fold")
    else {
        panic!("native fold");
    };
    assert_eq!(
        target.value_type(element),
        Some(&ValueType::Base(gandr_kernel_term::BaseType::Integer))
    );
    let &ValueType::List(pair) = target.value_type(result).expect("result type")
    else {
        panic!("native List result");
    };
    assert_eq!(
        target.value_type(pair),
        Some(&ValueType::Product([element, element].into()))
    );
    for (mut core, program) in [(source, program), (target, decoded)] {
        let mut arena = CommandArena::new();
        let root = focus_computation(&core, program, &mut arena, &mut Provenance::new())
            .expect("closed fold");
        let (store, value) = halted(&arena, &Definitions::new(), root);
        let back =
            read_back_terminal(&arena, &store, value, &mut core).expect("native list readback");
        let &Computation::Return(mut cursor) = core.computation(back).expect("returned list")
        else {
            panic!("return");
        };
        for expected in ["2", "7"] {
            let &Value::ListCons(pair, tail) = core.value(cursor).expect("cell")
            else {
                panic!("native cell");
            };
            let &[head, outer] = core.value(pair).and_then(Value::components).expect("pair")
            else {
                panic!("paired head");
            };
            let wanted_head = integer(&mut core, Digits(expected));
            let wanted_outer = integer(&mut core, Digits("11"));
            assert_eq!(core.value(head), core.value(wanted_head));
            assert_eq!(core.value(outer), core.value(wanted_outer));
            cursor = tail;
        }
        assert_eq!(core.value(cursor), Some(&Value::ListNil));
    }
}

/// `return 1` halts with `1`.
#[test]
fn ret_is_a_terminal_value()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let returned = core.computation_return(one);
    assert_eq!(
        "⟨1 |+ ★⟩",
        evaluated(&mut core, returned),
        "the returned value"
    );
}

/// `x ← return 7; return x` binds and returns the value.
#[test]
fn bind_threads_a_value()
{
    let mut core = CoreArena::new();
    let seven = integer(&mut core, Digits("7"));
    let head = core.computation_return(seven);
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let body = core.computation_return(bound);
    let program = core.computation_bind(head, body);
    assert_eq!("⟨7 |+ ★⟩", evaluated(&mut core, program), "the bound value");
}

/// `force (thunk (return 2))` runs the body.
#[test]
fn force_runs_a_thunk_body()
{
    let mut core = CoreArena::new();
    let two = integer(&mut core, Digits("2"));
    let body = core.computation_return(two);
    let thunk = core.value_thunk(body);
    let program = core.computation_force(thunk);
    assert_eq!(
        "⟨2 |+ ★⟩",
        evaluated(&mut core, program),
        "the body's value"
    );
}

/// A match on an injection runs the arm of its side with the payload
/// bound.
#[test]
fn case_selects_the_matching_arm()
{
    for (side, expected) in [(Side::Left, "⟨3 |+ ★⟩"), (Side::Right, "⟨0 |+ ★⟩")] {
        let mut core = CoreArena::new();
        let three = integer(&mut core, Digits("3"));
        let scrutinee = core.value_injection(side.into(), three);
        let payload = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let on_left = core.computation_return(payload);
        let zero = integer(&mut core, Digits("0"));
        let on_right = core.computation_return(zero);
        let program = core.computation_case(scrutinee, &[on_left, on_right]);
        assert_eq!(
            expected,
            evaluated(&mut core, program),
            "the arm of {side:?}"
        );
    }
}

/// A nominal match over three constructors runs the branch of its
/// value's ordinal with the fields applied in order: `ctor[0]()` takes the
/// fieldless branch, `ctor[1](5)` returns its field, and `ctor[2](3, 4)`
/// returns its first.
#[test]
fn data_case_selects_arm_returns_three()
{
    for (ordinal, expected) in [
        (0_usize, "⟨0 |+ ★⟩"),
        (1_usize, "⟨5 |+ ★⟩"),
        (2_usize, "⟨3 |+ ★⟩"),
    ] {
        let mut core = CoreArena::new();
        let datatype = core.value_type_unknown();
        let fields = match ordinal {
            0 => alloc::vec![],
            1 => alloc::vec![integer(&mut core, Digits("5"))],
            _ => alloc::vec![
                integer(&mut core, Digits("3")),
                integer(&mut core, Digits("4"))
            ],
        };
        let scrutinee = core.value_constructor(datatype, ordinal.into(), fields);
        let zero = integer(&mut core, Digits("0"));
        let fieldless = core.computation_return(zero);
        let own = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let own_returned = core.computation_return(own);
        let single = core.computation_lambda(own_returned);
        let first = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let first_returned = core.computation_return(first);
        let inner = core.computation_lambda(first_returned);
        let double = core.computation_lambda(inner);
        let motive = core.comp_type_unknown();
        let program =
            core.computation_data_case(scrutinee, motive, alloc::vec![fieldless, single, double]);
        assert_eq!(
            expected,
            evaluated(&mut core, program),
            "the branch of ordinal {ordinal}"
        );
    }
}

/// A nominal match is stuck by name on a literal, on a structural
/// constructor and on an ordinal it has no branch for.
#[test]
fn data_case_on_non_ctor_is_stuck()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let unit = core.value_unit();
    let injected = core.value_injection(Side::Left.into(), unit);
    let datatype = core.value_type_unknown();
    let beyond = core.value_constructor(datatype, 1_usize.into(), alloc::vec![five]);
    let own = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = core.computation_return(own);
    let branch = core.computation_lambda(returned);
    let motive = core.comp_type_unknown();
    for scrutinee in [five, injected, beyond] {
        let program = core.computation_data_case(scrutinee, motive, alloc::vec![branch]);
        let mut arena = CommandArena::new();
        let command = focus_computation(&core, program, &mut arena, &mut Provenance::new())
            .expect("a closed term focuses");
        let (_, stuck) = stuck(&arena, &Definitions::new(), command);
        assert!(
            matches!(stuck, Stuck::Unmatched { .. }),
            "the match is stuck unmatched: {stuck:?}"
        );
    }
}

/// A selection reads the width of the value it meets: the middle
/// component of a triple and of a quadruple, and the label `s` of records
/// of one and three labels holding it first, second and last, each deliver
/// that field to the continuation the selection carries, whether the
/// selection meets the value in a cut or is loaded as a frame a captured
/// command's value pops into; a record returned whole reads back with its
/// labels. A component past the width, an absent label, a label of a
/// tuple, a component of a record and a selection of a literal are each
/// stuck unmatched at the selection.
#[test]
fn a_selection_reads_the_width_of_the_value_it_meets()
{
    let mut core = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(String::from(name));
    let [zero, one, two, three] =
        ["0", "1", "2", "3"].map(|digits| integer(&mut core, Digits(digits)));
    let triple = core.value_tuple(&[zero, one, two]);
    let quadruple = core.value_tuple(&[zero, one, two, three]);
    let alone = core.value_record(alloc::collections::BTreeMap::from([(label("s"), one)]));
    let second = core.value_record(alloc::collections::BTreeMap::from([
        (label("a"), zero),
        (label("s"), two),
        (label("z"), three),
    ]));
    let last = core.value_record(alloc::collections::BTreeMap::from([
        (label("a"), zero),
        (label("b"), one),
        (label("s"), three),
    ]));
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let rebound = core.computation_return(bound);
    let middle = core.computation_tuple_projection(quadruple, 1_usize.into());
    let delivered = [
        (
            core.computation_tuple_projection(triple, 1_usize.into()),
            "⟨1 |+ ★⟩",
        ),
        (
            core.computation_tuple_projection(quadruple, 2_usize.into()),
            "⟨2 |+ ★⟩",
        ),
        (core.computation_bind(middle, rebound), "⟨1 |+ ★⟩"),
        (
            core.computation_record_projection(alone, label("s")),
            "⟨1 |+ ★⟩",
        ),
        (
            core.computation_record_projection(second, label("s")),
            "⟨2 |+ ★⟩",
        ),
        (
            core.computation_record_projection(last, label("s")),
            "⟨3 |+ ★⟩",
        ),
        (
            core.computation_return(second),
            "⟨record{a, s, z}(0, 2, 3) |+ ★⟩",
        ),
    ];
    for (program, expected) in delivered {
        assert_eq!(
            expected,
            evaluated(&mut core, program),
            "the selected field"
        );
    }

    let five = integer(&mut core, Digits("5"));
    let unmatched = [
        core.computation_tuple_projection(triple, 3_usize.into()),
        core.computation_record_projection(second, label("b")),
        core.computation_record_projection(triple, label("s")),
        core.computation_tuple_projection(alone, 0_usize.into()),
        core.computation_tuple_projection(five, 0_usize.into()),
    ];
    for program in unmatched {
        let mut arena = CommandArena::new();
        let command = focus_computation(&core, program, &mut arena, &mut Provenance::new())
            .expect("a closed projection focuses");
        let (_, stuck) = stuck(&arena, &Definitions::new(), command);
        assert!(
            matches!(stuck, Stuck::Unmatched { arms, .. }
                    if matches!(arena.consumer(arms), Some(&ConsumerNode::Select { .. }))),
            "the selection is stuck unmatched: {stuck:?}"
        );
    }

    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let held = focus_value(&core, quadruple, &mut arena, &mut provenance).expect("a tuple focuses");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("a leaf");
    let named = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("a leaf");
    let returned = arena
        .mint_cut(Polarity::Positive, held, named)
        .expect("live children");
    let captured = arena
        .mint_producer(ProducerNode::Mu { body: returned })
        .expect("a live body");
    let select = arena
        .mint_consumer(ConsumerNode::Select {
            selector: Selector::Component(2_usize.into()),
            then: top,
        })
        .expect("a live continuation");
    let root = arena
        .mint_cut(Polarity::Positive, captured, select)
        .expect("live children");
    let (store, value) = halted(&arena, &Definitions::new(), root);
    let back = read_back_value(&arena, &store, value, &mut core).expect("a literal reads back");
    assert_eq!(
        core.value(two),
        core.value(back),
        "the loaded selection delivers"
    );
}

/// `(fix self. λn. case n {zero ⇒ return zero | succ k ⇒ r ← force self k;
/// return succ (succ r)}) 2` doubles through its own binding to `4`.
#[test]
fn a_recursive_thunk_computes_through_its_own_binding()
{
    let mut core = CoreArena::new();
    let nat = core.value_type_unknown();
    let zero = core.value_constructor(nat, 0_usize.into(), alloc::vec![]);
    let one = core.value_constructor(nat, 1_usize.into(), alloc::vec![zero]);
    let two = core.value_constructor(nat, 1_usize.into(), alloc::vec![one]);
    let base = core.computation_return(zero);
    let own = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let predecessor = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let recurse = core.computation_force(own);
    let descent = core.computation_application(recurse, predecessor);
    let result = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let once = core.value_constructor(nat, 1_usize.into(), alloc::vec![result]);
    let twice = core.value_constructor(nat, 1_usize.into(), alloc::vec![once]);
    let rebuilt = core.computation_return(twice);
    let bound = core.computation_bind(descent, rebuilt);
    let step = core.computation_lambda(bound);
    let argument = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let motive = core.comp_type_unknown();
    let matched = core.computation_data_case(argument, motive, alloc::vec![base, step]);
    let function = core.computation_lambda(matched);
    let recursive = core.computation_fixpoint(
        function,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let program = core.computation_application(recursive, two);
    assert_eq!(
        "⟨ctor[1](ctor[1](ctor[1](ctor[1](ctor[0]())))) |+ ★⟩",
        evaluated(&mut core, program),
        "two doubled"
    );
}

/// Three loops that never end run until their heap fills, each pass
/// allocating its window, without filling the frame region: `fix x. force
/// x`; `fix o. fix i. force o`, an inner loop left for the outer one, as a
/// `break` commuted to the outer `continue` leaves it; and `(fix f. λn. fix
/// k. (force f) n) ()`, a function tail-calling itself from inside a loop.
/// The contrast `fix x. (y ← force x; return y)` holds one frame a pass and
/// fills the frame region first, so a held frame outruns the first loop's
/// window. The nested loop and the tail call allocate more a pass than a
/// held frame adds — each, holding one, still fills the heap first — so
/// their rows pin only that they run to an exhausted region other than the
/// frames.
#[test]
fn a_loop_holds_no_frame_across_its_iterations()
{
    let mut core = CoreArena::new();
    let itself = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let reentry = core.computation_force(itself);
    let plain = core.computation_fixpoint(reentry, gandr_kernel_term::FixpointEvidence::Partial);
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let answered = core.computation_return(bound);
    let held = core.computation_bind(reentry, answered);
    let holding = core.computation_fixpoint(held, gandr_kernel_term::FixpointEvidence::Partial);
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let continued = core.computation_force(outer);
    let inner = core.computation_fixpoint(continued, gandr_kernel_term::FixpointEvidence::Partial);
    let nested = core.computation_fixpoint(inner, gandr_kernel_term::FixpointEvidence::Partial);
    let own = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let argument = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let forced = core.computation_force(own);
    let call = core.computation_application(forced, argument);
    let looping = core.computation_fixpoint(call, gandr_kernel_term::FixpointEvidence::Partial);
    let function = core.computation_lambda(looping);
    let recursive = core.computation_fixpoint(
        function,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let unit = core.value_unit();
    let calling = core.computation_application(recursive, unit);
    for (program, shape, frames_fill) in [
        (plain, "a loop", false),
        (holding, "a loop holding a frame", true),
        (nested, "a nested loop", false),
        (calling, "a tail call inside a loop", false),
    ] {
        let mut arena = CommandArena::new();
        let command = focus_computation(&core, program, &mut arena, &mut Provenance::new())
            .expect("a closed term focuses");
        let run = ran(
            &arena,
            &Definitions::new(),
            command,
            Fuel::from(1_usize << 28_u32),
        );
        assert_eq!(
            frames_fill,
            matches!(run, Err(Declined::Exhausted(Status::FramesExhausted))),
            "{shape}: {}",
            fingerprint(&run)
        );
        assert!(
            matches!(run, Err(Declined::Exhausted(_))),
            "{shape} never ends: {}",
            fingerprint(&run)
        );
    }
}

/// `((λ. λ. return x1) 1) 2` binds each argument at its own binder.
#[test]
fn application_binds_the_argument()
{
    let mut core = CoreArena::new();
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let body = core.computation_return(outer);
    let inner = core.computation_lambda(body);
    let function = core.computation_lambda(inner);
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let once = core.computation_application(function, one);
    let program = core.computation_application(once, two);
    assert_eq!(
        "⟨1 |+ ★⟩",
        evaluated(&mut core, program),
        "x1 is the first argument"
    );
}

/// A transparent constant unfolds where it is read, an opaque one reads
/// back as itself, and a cyclic one and an undefined one stop the run at
/// the read.
#[test]
fn constants_unfold_once_and_opaque_ones_stay_opaque()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let five_body = core.computation_return(five);
    let suspended = core.value_thunk(five_body);
    let first = core.value_constant(ConstantIndex::from(0_usize));
    let opaque = core.value_constant(ConstantIndex::from(1_usize));
    let cyclic = core.value_constant(ConstantIndex::from(2_usize));
    let undefined = core.value_constant(ConstantIndex::from(9_usize));

    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let mut definitions = Definitions::new();
    let body = focus_value(&core, suspended, &mut arena, &mut provenance).expect("a thunk focuses");
    definitions.push(Definition::Transparent(body));
    definitions.push(Definition::Opaque);
    let loops =
        focus_value(&core, cyclic, &mut arena, &mut provenance).expect("a constant focuses");
    definitions.push(Definition::Transparent(loops));

    let forced = core.computation_force(first);
    let again = core.computation_force(first);
    let pair = core.value_tuple(&[opaque, first]);
    let returned = core.computation_return(pair);
    let tail = core.computation_bind(again, returned);
    let program = core.computation_bind(forced, tail);
    let command = focus_computation(&core, program, &mut arena, &mut provenance)
        .expect("a closed term focuses");
    let looping_return = core.computation_return(cyclic);
    let looping =
        focus_computation(&core, looping_return, &mut arena, &mut provenance).expect("focuses");
    let undefined_return = core.computation_return(undefined);
    let missing =
        focus_computation(&core, undefined_return, &mut arena, &mut provenance).expect("focuses");

    let (store, value) = halted(&arena, &definitions, command);
    let back =
        read_back_terminal(&arena, &store, value, &mut core).expect("the terminal reads back");
    assert_eq!(
        "⟨pair(c1, {force(α) ⇒ ⟨5 |+ α0⟩}) |+ ★⟩",
        shown(&core, back),
        "the opaque constant stays itself and the transparent one unfolds"
    );
    let (_, cycle) = stuck(&arena, &definitions, looping);
    assert_eq!(
        Stuck::CyclicConstant(ConstantIndex::from(2_usize)),
        cycle,
        "a definition needing its own value stops the run"
    );
    let (_, absent) = stuck(&arena, &definitions, missing);
    assert_eq!(
        Stuck::UndefinedConstant(ConstantIndex::from(9_usize)),
        absent,
        "a position never admitted stops the run"
    );
}

/// `t ← return thunk { return 1 }; force t` halts once its fuel covers its
/// jumps; every smaller budget declines exhausted rather than answering.
#[test]
fn the_step_budget_bounds_a_run()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let body = core.computation_return(one);
    let suspended = core.value_thunk(body);
    let returned = core.computation_return(suspended);
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = core.computation_force(bound);
    let program = core.computation_bind(returned, forced);
    let mut arena = CommandArena::new();
    let command = focus_computation(&core, program, &mut arena, &mut Provenance::new())
        .expect("a closed term focuses");
    let definitions = Definitions::new();
    let run = |jumps| ran(&arena, &definitions, command, Fuel::from(jumps));
    let least = (0_usize ..= 64_usize)
        .find(|&jumps| run(jumps).is_ok())
        .expect("a bounded run halts");
    assert!(least > 0, "a run spends fuel");
    for jumps in 0 .. least {
        assert!(
            matches!(run(jumps), Err(Declined::Exhausted(Status::FuelExhausted))),
            "{jumps} jumps are short of {least}"
        );
    }
    assert!(
        matches!(
            run(least),
            Ok(Ran {
                outcome: Outcome::Halted(_),
                ..
            })
        ),
        "{least} jumps halt"
    );
}

/// `x ← return 4; λ. return x1` halts with a function closed over `x`.
#[test]
fn a_function_terminal_reads_back_closed_over_its_environment()
{
    let mut core = CoreArena::new();
    let four = integer(&mut core, Digits("4"));
    let head = core.computation_return(four);
    let captured = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let body = core.computation_return(captured);
    let function = core.computation_lambda(body);
    let program = core.computation_bind(head, function);
    assert_eq!(
        "⟨cocase {apply(x; α) ⇒ ⟨4 |+ α0⟩} |− ★⟩",
        evaluated(&mut core, program),
        "the function with its captured variable substituted"
    );
}

/// `x ← return 4; return (thunk (return x))` halts with a thunk closed
/// over `x`.
#[test]
fn a_thunk_reads_back_closed_over_its_environment()
{
    let mut core = CoreArena::new();
    let four = integer(&mut core, Digits("4"));
    let head = core.computation_return(four);
    let captured = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let body = core.computation_return(captured);
    let thunk = core.value_thunk(body);
    let returned = core.computation_return(thunk);
    let program = core.computation_bind(head, returned);
    assert_eq!(
        "⟨{force(α) ⇒ ⟨4 |+ α0⟩} |+ ★⟩",
        evaluated(&mut core, program),
        "the thunk with its captured variable substituted"
    );

    let mut arena = CommandArena::new();
    let command = focus_computation(&core, program, &mut arena, &mut Provenance::new())
        .expect("a closed term focuses");
    let (store, value) = halted(&arena, &Definitions::new(), command);
    let read = read_back_value(&arena, &store, value, &mut core).expect("a thunk is a value");
    let wrapped = core.computation_return(read);
    assert_eq!(
        "⟨{force(α) ⇒ ⟨4 |+ α0⟩} |+ ★⟩",
        shown(&core, wrapped),
        "the value readback is the thunk itself"
    );
    assert!(
        matches!(core.computation(wrapped), Some(&Computation::Return(_))),
        "and the terminal readback only wraps it"
    );
}

/// `x ← return 4; y ← return 5; z ← return 6; return (thunk (return (x, z)))`
/// halts on every tier with a thunk whose environment binds exactly `z` and
/// `x`, innermost first: `y` is in scope where the thunk is created, but
/// nothing in the thunk names it, so it is never moved into the store, and
/// the thunk still reads back closed over the two it names.
#[test]
fn a_captured_environment_holds_exactly_its_support()
{
    let mut core = CoreArena::new();
    let four = integer(&mut core, Digits("4"));
    let five = integer(&mut core, Digits("5"));
    let six = integer(&mut core, Digits("6"));
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let inner = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let pair = core.value_tuple(&[outer, inner]);
    let body = core.computation_return(pair);
    let thunk = core.value_thunk(body);
    let mut program = core.computation_return(thunk);
    for bound in [six, five, four] {
        let head = core.computation_return(bound);
        program = core.computation_bind(head, program);
    }
    let mut arena = CommandArena::new();
    let command = focus_computation(&core, program, &mut arena, &mut Provenance::new())
        .expect("a closed term focuses");
    let (store, value) = halted(&arena, &Definitions::new(), command);
    let Some(&HeapValue::Thunk { environment, .. }) = store.value(value)
    else {
        panic!("the run halts with a thunk");
    };
    let mut captured = Vec::new();
    for bound in store.bound_values(environment) {
        let read = read_back_value(&arena, &store, bound, &mut core).expect("a literal reads back");
        captured.push(core.value(read).cloned());
    }
    assert_eq!(
        alloc::vec![core.value(six).cloned(), core.value(four).cloned()],
        captured,
        "the environment binds z then x, and not y"
    );
    let read = read_back_value(&arena, &store, value, &mut core).expect("a thunk is a value");
    let wrapped = core.computation_return(read);
    assert_eq!(
        "⟨{force(α) ⇒ ⟨pair(4, 6) |+ α0⟩} |+ ★⟩",
        shown(&core, wrapped),
        "the thunk reads back closed over the two it names"
    );
}

/// `⟨pair(μα. ⟨() |+ α0⟩, ()) |+ ★⟩` halts with a suspended capture as a
/// field, which has no core reading; the core arena is left at its mark.
#[test]
fn a_suspended_capture_has_no_reading()
{
    let mut arena = CommandArena::new();
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints");
    let inner_return = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("a leaf mints");
    let body = arena
        .mint_cut(Polarity::Positive, unit, inner_return)
        .expect("children resolve");
    let capture = arena
        .mint_producer(ProducerNode::Mu { body })
        .expect("the body resolves");
    let pair = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            producers: Box::from([capture, unit]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let command = arena
        .mint_cut(Polarity::Positive, pair, top)
        .expect("children resolve");

    let (store, value) = halted(&arena, &Definitions::new(), command);
    let mut core = CoreArena::new();
    let kept = core.value_unit();
    let mark = core.watermark();
    let refused = read_back_terminal(&arena, &store, value, &mut core);
    assert!(
        matches!(refused, Err(ReadbackRefusal::Unreadable(_))),
        "the capture has no reading: {refused:?}"
    );
    assert_eq!(mark, core.watermark(), "the core arena is back at its mark");
    assert!(core.value(kept).is_some(), "earlier nodes are kept");
}

/// Polarity delays a capture only against a binder, and later use resumes
/// it.
#[test]
fn polarity_decides_whether_a_capture_is_evaluated()
{
    let mut arena = CommandArena::new();
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let back = arena
        .mint_consumer(ConsumerNode::Covariable(0_u32.into()))
        .expect("leaf");
    let force = arena
        .mint_consumer(ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([back]),
        })
        .expect("continuation resolves");
    let body = arena
        .mint_cut(Polarity::Positive, unit, force)
        .expect("children resolve");
    let capture = arena
        .mint_producer(ProducerNode::Mu { body })
        .expect("body resolves");
    let ignored_body = arena
        .mint_cut(Polarity::Positive, unit, top)
        .expect("children resolve");
    let ignoring = arena
        .mint_consumer(ConsumerNode::MuTilde { body: ignored_body })
        .expect("body resolves");
    let variable = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: 0_u32.into(),
        })
        .expect("leaf");
    let used_body = arena
        .mint_cut(Polarity::Positive, variable, top)
        .expect("children resolve");
    let using = arena
        .mint_consumer(ConsumerNode::MuTilde { body: used_body })
        .expect("body resolves");
    let positive = arena
        .mint_cut(Polarity::Positive, capture, ignoring)
        .expect("children resolve");
    let negative = arena
        .mint_cut(Polarity::Negative, capture, ignoring)
        .expect("children resolve");
    let resumed = arena
        .mint_cut(Polarity::Negative, capture, using)
        .expect("children resolve");
    let unit_value = HeapValue::Constructed {
        tag: ConstructorTag::Tuple(ProducerArity::ZERO),
        fields: Box::from([]),
    };
    let definitions = Definitions::new();
    let (store, strict) = stuck(&arena, &definitions, positive);
    let Stuck::Unobservable {
        value: strict,
        head: DestructorTag::Force,
    } = strict
    else {
        panic!("positive cut runs the capture: {strict:?}");
    };
    assert_eq!(Some(&unit_value), store.value(strict));
    let (store, delayed) = halted(&arena, &definitions, negative);
    assert_eq!(
        Some(&unit_value),
        store.value(delayed),
        "negative cut leaves an ignored capture suspended"
    );
    let (store, forced) = stuck(&arena, &definitions, resumed);
    let Stuck::Unobservable {
        value: forced,
        head: DestructorTag::Force,
    } = forced
    else {
        panic!("using the suspended capture resumes its body: {forced:?}");
    };
    assert_eq!(Some(&unit_value), store.value(forced));
}

/// A command the tiers cannot lay out declines naming its form: a root the
/// arena does not hold, a constructor with consumer fields, a variable of
/// either zone and a covariable bound by nothing, and a destructor of no
/// continuation. A well-formed command meeting the wrong eliminator sticks
/// naming the value: unit under an empty match and under `force`, a thunk
/// and a recursive thunk under `apply`.
#[test]
fn transition_refusals_name_the_first_invalid_endpoint()
{
    let mut arena = CommandArena::new();
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("leaf");
    let intuitionistic = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: 0_u32.into(),
        })
        .expect("leaf");
    let linear = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Linear,
            index: 0_u32.into(),
        })
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let unbound = arena
        .mint_consumer(ConsumerNode::Covariable(0_u32.into()))
        .expect("leaf");
    let malformed = arena
        .mint_consumer(ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("empty children");
    let non_value = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([top]),
        })
        .expect("children resolve");
    let linear_body = arena
        .mint_cut(Polarity::Positive, linear, top)
        .expect("children resolve");
    let binds_one_zone = arena
        .mint_consumer(ConsumerNode::MuTilde { body: linear_body })
        .expect("body resolves");
    let definitions = Definitions::new();
    let declined = [
        (CommandId::from(u32::MAX), Form::Dangling),
        (
            arena
                .mint_cut(Polarity::Positive, non_value, top)
                .expect("children resolve"),
            Form::ConsumerFields,
        ),
        (
            arena
                .mint_cut(Polarity::Positive, intuitionistic, top)
                .expect("children resolve"),
            Form::Unbound,
        ),
        (
            arena
                .mint_cut(Polarity::Positive, unit, binds_one_zone)
                .expect("children resolve"),
            Form::Unbound,
        ),
        (
            arena
                .mint_cut(Polarity::Positive, unit, unbound)
                .expect("children resolve"),
            Form::Unbound,
        ),
        (
            arena
                .mint_cut(Polarity::Positive, unit, malformed)
                .expect("children resolve"),
            Form::Destructor,
        ),
    ];
    for (root, form) in declined {
        assert!(
            matches!(
                ran(&arena, &definitions, root, budget()),
                Err(Declined::Lowering(found)) if found == form
            ),
            "{root:?} declines as {form:?}"
        );
    }

    let unit_value = HeapValue::Constructed {
        tag: ConstructorTag::Tuple(ProducerArity::ZERO),
        fields: Box::from([]),
    };
    let choices = arena
        .mint_consumer(ConsumerNode::Case {
            arms: Box::from([]),
        })
        .expect("empty arms");
    let unmatched = arena
        .mint_cut(Polarity::Positive, unit, choices)
        .expect("children resolve");
    let (store, refused) = stuck(&arena, &definitions, unmatched);
    let Stuck::Unmatched { value, arms } = refused
    else {
        panic!("an empty match sticks unmatched: {refused:?}");
    };
    assert_eq!((Some(&unit_value), choices), (store.value(value), arms));
    let force = arena
        .mint_consumer(ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([top]),
        })
        .expect("continuation resolves");
    let forced = arena
        .mint_cut(Polarity::Positive, unit, force)
        .expect("children resolve");
    let (store, refused) = stuck(&arena, &definitions, forced);
    let Stuck::Unobservable {
        value,
        head: DestructorTag::Force,
    } = refused
    else {
        panic!("a forced unit is unobservable: {refused:?}");
    };
    assert_eq!(Some(&unit_value), store.value(value));

    let returns = arena
        .mint_consumer(ConsumerNode::Covariable(0_u32.into()))
        .expect("leaf");
    let suspended = arena
        .mint_cut(Polarity::Positive, unit, returns)
        .expect("children resolve");
    let apply = arena
        .mint_consumer(ConsumerNode::Destructor {
            tag: DestructorTag::Apply,
            producers: Box::from([unit]),
            consumers: Box::from([top]),
        })
        .expect("children resolve");
    let suspensions = [
        ProducerNode::Thunk { body: suspended },
        ProducerNode::Fixpoint {
            body: suspended,
            evidence: gandr_kernel_term::FixpointEvidence::Partial,
        },
    ];
    for suspension in suspensions {
        let suspension = arena.mint_producer(suspension).expect("body resolves");
        let applied = arena
            .mint_cut(Polarity::Negative, suspension, apply)
            .expect("children resolve");
        let (_, refused) = stuck(&arena, &definitions, applied);
        assert!(
            matches!(refused, Stuck::Unobservable {
                head: DestructorTag::Apply,
                ..
            }),
            "a suspension answers only force: {refused:?}"
        );
    }
}

/// A two-field pattern binds the last field innermost without losing source
/// order.
#[test]
fn pattern_fields_bind_last_innermost()
{
    let mut core = CoreArena::new();
    let first_source = integer(&mut core, Digits("2"));
    let last_source = integer(&mut core, Digits("3"));
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let first = focus_value(&core, first_source, &mut arena, &mut provenance).expect("literal");
    let last = focus_value(&core, last_source, &mut arena, &mut provenance).expect("literal");
    let outer = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: 1_u32.into(),
        })
        .expect("leaf");
    let inner = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: 0_u32.into(),
        })
        .expect("leaf");
    let result = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            producers: Box::from([outer, inner]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let body = arena
        .mint_cut(Polarity::Positive, result, top)
        .expect("children resolve");
    let matched = arena
        .mint_consumer(ConsumerNode::Case {
            arms: Box::from([PatternArm {
                constructor: ConstructorTag::Tuple(ProducerArity::TWO),
                body,
            }]),
        })
        .expect("body resolves");
    let pair = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            producers: Box::from([first, last]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    let root = arena
        .mint_cut(Polarity::Positive, pair, matched)
        .expect("children resolve");
    let (store, value) = halted(&arena, &Definitions::new(), root);
    let read = read_back_value(&arena, &store, value, &mut core).expect("positive pair");
    let Some(&[first_read, last_read]) = core
        .value(read)
        .and_then(gandr_core_term::Value::components)
    else {
        panic!("pair reading");
    };
    assert_eq!(core.value(first_source), core.value(first_read));
    assert_eq!(core.value(last_source), core.value(last_read));
}

/// A nested unfolding that fails sticks the same way on every run: a
/// constant left mid-unfolding by one run is never a false cycle in the next.
#[test]
fn failed_unfolding_resets_every_active_constant()
{
    let mut arena = CommandArena::new();
    let root = arena
        .mint_producer(ProducerNode::Constant(0_usize.into()))
        .expect("leaf");
    let first_body = arena
        .mint_producer(ProducerNode::Constant(1_usize.into()))
        .expect("leaf");
    let second_body = arena
        .mint_producer(ProducerNode::Constant(2_usize.into()))
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let command = arena
        .mint_cut(Polarity::Positive, root, top)
        .expect("children resolve");
    let mut definitions = Definitions::new();
    definitions.push(Definition::Transparent(first_body));
    definitions.push(Definition::Transparent(second_body));
    for attempt in ["first", "retried"] {
        let (_, refused) = stuck(&arena, &definitions, command);
        assert_eq!(
            Stuck::UndefinedConstant(2_usize.into()),
            refused,
            "the {attempt} run meets the missing definition"
        );
    }
}

/// `thunk (λx. return o)`, `o` built over the bound variable by `body`.
///
/// # Specification
/// trivial.
fn translator(
    core: &mut CoreArena,
    body: fn(&mut CoreArena, ValueId) -> ValueId,
) -> ValueId
{
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let built = body(core, bound);
    let returned = core.computation_return(built);
    let lambda = core.computation_lambda(returned);
    core.value_thunk(lambda)
}

/// `x ↦ (x, unit)`.
///
/// # Specification
/// trivial.
fn paired(
    core: &mut CoreArena,
    bound: ValueId,
) -> ValueId
{
    let unit = core.value_unit();
    core.value_tuple(&[bound, unit])
}

/// `x ↦ inl(x)`.
///
/// # Specification
/// trivial.
fn injected_left(
    core: &mut CoreArena,
    bound: ValueId,
) -> ValueId
{
    core.value_injection(Side::Left.into(), bound)
}

/// `x ↦ inr(x)`.
///
/// # Specification
/// trivial.
fn injected_right(
    core: &mut CoreArena,
    bound: ValueId,
) -> ValueId
{
    core.value_injection(Side::Right.into(), bound)
}

/// The motive `y. El y`: the decode of the moving code.
///
/// # Specification
/// trivial.
fn decoded(core: &mut CoreArena) -> gandr_core_term::ValueTypeId
{
    let code = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    core.value_type_element(code, gandr_kernel_strata::Level::zero())
}

/// What `return value` runs to, for comparison with a ride's result.
///
/// # Specification
/// trivial.
fn returned(
    core: &mut CoreArena,
    value: ValueId,
) -> String
{
    let computation = core.computation_return(value);
    evaluated(core, computation)
}

/// A ride runs as the motive's action on the flow's translator: `stay`
/// as the identity, a forward flow as its translator at the decode, a
/// composite as its legs in order, and product, sum and list motives
/// constructorwise.
#[test]
fn rides_run_by_the_motives_action()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let six = integer(&mut core, Digits("6"));
    let unit = core.value_unit();
    let integer_type = core.value_type_base(gandr_kernel_term::BaseType::Integer);
    let unit_type = core.value_type_unit();
    let identity = decoded(&mut core);
    let pairing = translator(&mut core, paired);
    let injecting = translator(&mut core, injected_left);
    let forward = core.value_forward(pairing);
    let other = core.value_forward(injecting);
    let code = core.value_quote(integer_type);
    let kept = core.value_stay(code);

    let rode = core.computation_ride(identity, kept, five);
    let expected = returned(&mut core, five);
    assert_eq!(
        evaluated(&mut core, rode),
        expected,
        "stay runs as the identity"
    );
    let rode = core.computation_ride(integer_type, forward, five);
    assert_eq!(
        evaluated(&mut core, rode),
        expected,
        "a constant motive keeps the value"
    );

    let rode = core.computation_ride(identity, forward, five);
    let image = core.value_tuple(&[five, unit]);
    assert_eq!(
        evaluated(&mut core, rode),
        returned(&mut core, image),
        "a forward flow runs its translator at the decode"
    );

    let composite = core.value_then(forward, other);
    let rode = core.computation_ride(identity, composite, five);
    let image = core.value_tuple(&[five, unit]);
    let image = core.value_injection(Side::Left.into(), image);
    assert_eq!(
        evaluated(&mut core, rode),
        returned(&mut core, image),
        "a composite runs its first leg, then its second"
    );

    let product = core.value_type_product(&[identity, integer_type]);
    let pair = core.value_tuple(&[five, six]);
    let rode = core.computation_ride(product, other, pair);
    let moved = core.value_injection(Side::Left.into(), five);
    let image = core.value_tuple(&[moved, six]);
    assert_eq!(
        evaluated(&mut core, rode),
        returned(&mut core, image),
        "a product motive acts componentwise"
    );

    let sum = core.value_type_sum(&[unit_type, identity]);
    let injected = core.value_injection(Side::Right.into(), five);
    let rode = core.computation_ride(sum, other, injected);
    let inner = core.value_injection(Side::Left.into(), five);
    let image = core.value_injection(Side::Right.into(), inner);
    assert_eq!(
        evaluated(&mut core, rode),
        returned(&mut core, image),
        "a sum motive acts on the payload of its own summand"
    );

    let list = core.value_type_list(identity);
    let nil = core.value_list_nil();
    let tail = core.value_list_cons(six, nil);
    let cell = core.value_list_cons(five, tail);
    let rode = core.computation_ride(list, other, cell);
    let first = core.value_injection(Side::Left.into(), five);
    let second = core.value_injection(Side::Left.into(), six);
    let tail = core.value_list_cons(second, nil);
    let image = core.value_list_cons(first, tail);
    assert_eq!(
        evaluated(&mut core, rode),
        returned(&mut core, image),
        "a list motive acts on every cell in order"
    );
}

/// A function ridden along a function flow runs its argument along the
/// domain flow, then itself, then its result along the codomain flow.
#[test]
fn a_function_flow_runs_in_variance_order()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let unit = core.value_unit();
    let identity = decoded(&mut core);
    let pairing = translator(&mut core, paired);
    let lefting = translator(&mut core, injected_left);
    let righting = translator(&mut core, injected_right);
    let domain_flow = core.value_forward(pairing);
    let codomain_flow = core.value_forward(righting);
    let applied = |core: &mut CoreArena, flow: ValueId| {
        let rode = core.computation_ride(identity, flow, lefting);
        let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let forced = core.computation_force(bound);
        let applied = core.computation_application(forced, five);
        core.computation_bind(rode, applied)
    };
    let function = core.value_function_flow(domain_flow, codomain_flow);
    let ran = applied(&mut core, function);
    let argument = core.value_tuple(&[five, unit]);
    let result = core.value_injection(Side::Left.into(), argument);
    let image = core.value_injection(Side::Right.into(), result);
    let expected = returned(&mut core, image);
    assert_eq!(
        evaluated(&mut core, ran),
        expected,
        "the argument rides the domain flow, the function runs, the result rides the codomain flow"
    );
    let swapped = core.value_function_flow(codomain_flow, domain_flow);
    let ran = applied(&mut core, swapped);
    assert_ne!(
        evaluated(&mut core, ran),
        expected,
        "swapping the boundaries is another function"
    );
}

/// A pair ridden along a flow product runs its left component along the
/// first flow and its right along the second, in place.
#[test]
fn a_flow_product_runs_componentwise()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Digits("5"));
    let six = integer(&mut core, Digits("6"));
    let unit = core.value_unit();
    let identity = decoded(&mut core);
    let pairing = translator(&mut core, paired);
    let lefting = translator(&mut core, injected_left);
    let first = core.value_forward(pairing);
    let second = core.value_forward(lefting);
    let pair = core.value_tuple(&[five, six]);
    let product = core.value_flow_product(first, second);
    let rode = core.computation_ride(identity, product, pair);
    let left = core.value_tuple(&[five, unit]);
    let right = core.value_injection(Side::Left.into(), six);
    let image = core.value_tuple(&[left, right]);
    let expected = returned(&mut core, image);
    assert_eq!(
        evaluated(&mut core, rode),
        expected,
        "each component rides its own flow"
    );
    let swapped = core.value_flow_product(second, first);
    let rode = core.computation_ride(identity, swapped, pair);
    assert_ne!(
        evaluated(&mut core, rode),
        expected,
        "the first flow moves the left component"
    );
}

/// The core's own constructors under the names a reified pattern uses, and
/// `Lift` at level zero.
///
/// # Specification
/// trivial.
fn resolver() -> ConstructorResolver
{
    let mut resolver = ConstructorResolver::new();
    resolver.insert(Sym::new("Unit"), ConstructorTag::Tuple(ProducerArity::ZERO));
    resolver.insert(Sym::new("Pair"), ConstructorTag::Tuple(ProducerArity::TWO));
    resolver.insert(
        Sym::new("Inl"),
        ConstructorTag::Injection(Side::Left.into()),
    );
    resolver.insert(
        Sym::new("Inr"),
        ConstructorTag::Injection(Side::Right.into()),
    );
    resolver.insert(
        Sym::new("Lift"),
        ConstructorTag::Lift(gandr_kernel_strata::Level::zero()),
    );
    resolver
}

/// `⟨Unit |+ Inl⁻(★)⟩`, reified, runs to the value its frame re-wraps.
#[test]
fn a_reified_return_frame_runs_to_the_rewrapped_value()
{
    let pattern = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Unit", []),
        ConsPat::frame("Inl", ConsPat::top()),
    );
    let mut arena = CommandArena::new();
    let command = reify_command(&mut arena, &pattern, &resolver()).expect("a unary frame");
    let (store, value) = halted(&arena, &Definitions::new(), command);
    let mut core = CoreArena::new();
    let back = read_back_terminal(&arena, &store, value, &mut core).expect("the value reads back");
    assert_eq!(
        "⟨inl(()) |+ ★⟩",
        shown(&core, back),
        "the frame re-wrapped the value"
    );
}

/// `⟨Pair(Lift(Inr(Unit)), Inl(Unit)) |+ Inl⁻(Inr⁻(★))⟩`, reified, runs
/// its frames innermost first over every constructor head:
/// `inr(inl(pair(lift(inr(())), inl(()))))`.
#[test]
fn reified_nested_frames_run_in_order()
{
    use gandr_core_term::Value;

    let pattern = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Pair", [
            ProdPat::ctor("Lift", [ProdPat::ctor("Inr", [ProdPat::ctor("Unit", [])])]),
            ProdPat::ctor("Inl", [ProdPat::ctor("Unit", [])]),
        ]),
        ConsPat::frame("Inl", ConsPat::frame("Inr", ConsPat::top())),
    );
    let mut arena = CommandArena::new();
    let command = reify_command(&mut arena, &pattern, &resolver()).expect("ground pattern");
    let (store, value) = halted(&arena, &Definitions::new(), command);
    let mut core = CoreArena::new();
    let read = read_back_value(&arena, &store, value, &mut core).expect("positive result");
    let Some(&Value::Injection(last, outer)) = core.value(read)
    else {
        panic!("the last frame wraps last");
    };
    assert_eq!(last, Side::Right.into());
    let Some(&Value::Injection(first, pair)) = core.value(outer)
    else {
        panic!("the first frame wraps first");
    };
    assert_eq!(first, Side::Left.into());
    let Some(&[lift, right]) = core.value(pair).and_then(Value::components)
    else {
        panic!("pair head survives");
    };
    let Some(&Value::Lift { ref target, body }) = core.value(lift)
    else {
        panic!("first field is lifted");
    };
    assert_eq!(&gandr_kernel_strata::Level::zero(), target);
    let Some(&Value::Injection(lifted, first_unit)) = core.value(body)
    else {
        panic!("right injection survives under lift");
    };
    assert_eq!(lifted, Side::Right.into());
    let Some(&Value::Injection(second, last_unit)) = core.value(right)
    else {
        panic!("left injection remains the second field");
    };
    assert_eq!(second, Side::Left.into());
    assert_eq!(Some(&Value::unit()), core.value(first_unit));
    assert_eq!(Some(&Value::unit()), core.value(last_unit));
}
