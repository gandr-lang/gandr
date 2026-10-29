//! A command closed over a store's values: a thunk a run answered with, run
//! from the store by `evaluate_closed_on` on each tier, on this thread and on
//! another, against forcing it in place.

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::Environment;
use gandr_core_sequent::FreeSet;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::check_command;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::read_back_value;
use gandr_core_term::CertificateEquality;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::RunInputs;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate_closed_on;
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

/// How many producer binders out a variable reaches: zero names the
/// innermost.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Outward(u32);

/// The producer variable `outward` binders out.
///
/// # Specification
/// trivial.
fn variable(
    core: &mut CoreArena,
    outward: Outward,
) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, outward.0.into())
}

/// `program` focused into an arena of its own, closed.
///
/// # Specification
/// trivial.
fn focused(
    core: &CoreArena,
    program: ComputationId,
) -> (CommandArena, CommandId)
{
    let mut arena = CommandArena::new();
    let root = focus_computation(
        core,
        program,
        &mut arena,
        &mut Provenance::new(),
        &gandr_core_sequent::Writers::NONE,
    )
    .expect("the program focuses");
    assert_eq!(Ok(FreeSet::default()), check_command(&arena, root));
    (arena, root)
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
        panic!("the program answers on {tier:?}: {outcome:?}");
    };
    let Some(&HeapValue::Thunk { body, environment }) = store.value(thunk)
    else {
        panic!("the program answers a thunk on {tier:?}");
    };
    (body, environment)
}

/// The value `outcome` halts with, read back into `core`.
///
/// # Specification
/// trivial.
fn answer(
    (arena, store): (&CommandArena, &Store),
    outcome: &Result<Outcome, Declined>,
    core: &mut CoreArena,
) -> ValueId
{
    let &Ok(Outcome::Halted(value)) = outcome
    else {
        panic!("the run halts: {outcome:?}");
    };
    read_back_value(arena, store, value, core).expect("the answer reads back")
}

/// `program` answers a thunk; on each tier the thunk run from the store, on
/// this thread and on another, and the thunk forced in place each answer
/// `expected`.
///
/// # Specification
/// trivial.
fn assert_closed(
    core: &mut CoreArena,
    program: ComputationId,
    expected: ValueId,
)
{
    let thunk = variable(core, Outward(0));
    let forced = core.computation_force(thunk);
    let in_place = core.computation_bind(program, forced);
    let (arena, root) = focused(core, program);
    let (forcing, forced) = focused(core, in_place);
    let definitions = Definitions::new();
    for &tier in tiers() {
        let mut here = Store::new();
        let outcome = evaluate_on(
            tier,
            &forcing,
            &definitions,
            forced,
            budget(),
            RunInputs::new(&mut here),
        );
        let actual = answer((&forcing, &here), &outcome, core);
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(core, actual, expected),
            "forced in place on {tier:?}"
        );
        let mut store = Store::new();
        let (body, environment) = suspended(tier, (&arena, root), &mut store);
        let outcome = evaluate_closed_on(
            tier,
            (&arena, &definitions),
            (body, environment),
            (budget(), RunInputs::new(&mut store)),
        );
        let actual = answer((&arena, &store), &outcome, core);
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(core, actual, expected),
            "run from the store on {tier:?}"
        );
        // The writer's own store, filled on this thread and moved to another.
        let mut apart = Store::new();
        let (body, environment) = suspended(tier, (&arena, root), &mut apart);
        let outcome = std::thread::scope(|scope| {
            scope
                .spawn(|| {
                    evaluate_closed_on(
                        tier,
                        (&arena, &definitions),
                        (body, environment),
                        (budget(), RunInputs::new(&mut apart)),
                    )
                })
                .join()
                .expect("the writer's thread joins")
        });
        let actual = answer((&arena, &apart), &outcome, core);
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(core, actual, expected),
            "run from the store on another thread on {tier:?}"
        );
    }
}

/// A thunk over no capture, one and two runs from the store as forcing it
/// in place runs it: `return thunk { return 7 }`,
/// `(λx. return thunk { return x }) 7` and
/// `(λx. λy. return thunk { return (x, y) }) 7 9`, whose answer `(7, 9)` a
/// swapped capture slot would turn.
#[test]
fn a_thunk_runs_from_the_store_as_it_runs_in_place()
{
    let mut core = CoreArena::new();
    let seven = integer(&mut core, Digits("7"));
    let nine = integer(&mut core, Digits("9"));
    let body = core.computation_return(seven);
    let thunk = core.value_thunk(body);
    let program = core.computation_return(thunk);
    assert_closed(&mut core, program, seven);

    let x = variable(&mut core, Outward(0));
    let body = core.computation_return(x);
    let thunk = core.value_thunk(body);
    let returned = core.computation_return(thunk);
    let function = core.computation_lambda(returned);
    let program = core.computation_application(function, seven);
    assert_closed(&mut core, program, seven);

    let x = variable(&mut core, Outward(1));
    let y = variable(&mut core, Outward(0));
    let pair = core.value_tuple(&[x, y]);
    let body = core.computation_return(pair);
    let thunk = core.value_thunk(body);
    let returned = core.computation_return(thunk);
    let inner = core.computation_lambda(returned);
    let function = core.computation_lambda(inner);
    let applied = core.computation_application(function, seven);
    let program = core.computation_application(applied, nine);
    let expected = core.value_tuple(&[seven, nine]);
    assert_closed(&mut core, program, expected);
}

/// Two captures bound to one store value are one object counted twice:
/// `(λx. (λy. return thunk { split x as (a, b) in return (y, (3, 4)) }) x)
/// (1, 2)` answers `((1, 2), (3, 4))`. The split drops `x`'s holder while
/// `y`'s still holds the pair, so a pair counted once is freed and `(3, 4)`
/// takes its block.
#[test]
fn a_shared_capture_is_laid_out_once_and_counted_twice()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let three = integer(&mut core, Digits("3"));
    let four = integer(&mut core, Digits("4"));
    let shared = core.value_tuple(&[one, two]);
    let fresh = core.value_tuple(&[three, four]);
    let y = variable(&mut core, Outward(2));
    let answered = core.value_tuple(&[y, fresh]);
    let returned = core.computation_return(answered);
    let x = variable(&mut core, Outward(1));
    let split = core.computation_split(x, ComponentCount::from(2_usize), returned);
    let thunk = core.value_thunk(split);
    let suspended = core.computation_return(thunk);
    let inner = core.computation_lambda(suspended);
    let x = variable(&mut core, Outward(0));
    let rebound = core.computation_application(inner, x);
    let function = core.computation_lambda(rebound);
    let program = core.computation_application(function, shared);
    let expected = core.value_tuple(&[shared, fresh]);
    assert_closed(&mut core, program, expected);
}

/// An environment binding one value fewer or one more than the body's
/// captures declines, and a captured function, which only its own run can
/// hold, declines naming it: `(λx. return thunk { return x }) 7` and
/// `(λf. return thunk { (force f) 7 }) (thunk { λx. return x })`.
#[test]
fn an_environment_other_than_the_captures_declines()
{
    let mut core = CoreArena::new();
    let seven = integer(&mut core, Digits("7"));
    let x = variable(&mut core, Outward(0));
    let body = core.computation_return(x);
    let thunk = core.value_thunk(body);
    let returned = core.computation_return(thunk);
    let function = core.computation_lambda(returned);
    let program = core.computation_application(function, seven);
    let (arena, root) = focused(&core, program);

    let x = variable(&mut core, Outward(0));
    let identity = core.computation_return(x);
    let identity = core.computation_lambda(identity);
    let identity = core.value_thunk(identity);
    let f = variable(&mut core, Outward(0));
    let forced = core.computation_force(f);
    let applied = core.computation_application(forced, seven);
    let thunk = core.value_thunk(applied);
    let returned = core.computation_return(thunk);
    let function = core.computation_lambda(returned);
    let program = core.computation_application(function, identity);
    let (functional, captures) = focused(&core, program);

    let definitions = Definitions::new();
    for &tier in tiers() {
        let mut store = Store::new();
        let (body, environment) = suspended(tier, (&arena, root), &mut store);
        let bound = store.bound_values(environment).next().expect("one capture");
        let over = store.bind_value(environment, bound).expect("room");
        for wrong in [Environment::EMPTY, over] {
            assert_eq!(
                Err(Declined::Environment),
                evaluate_closed_on(
                    tier,
                    (&arena, &definitions),
                    (body, wrong),
                    (budget(), RunInputs::new(&mut store)),
                ),
                "on {tier:?}"
            );
        }
        let (body, environment) = suspended(tier, (&functional, captures), &mut store);
        let captured = store.bound_values(environment).next().expect("one capture");
        assert_eq!(
            Err(Declined::Capture(captured)),
            evaluate_closed_on(
                tier,
                (&functional, &definitions),
                (body, environment),
                (budget(), RunInputs::new(&mut store)),
            ),
            "on {tier:?}"
        );
    }
}
