//! A command open over free variables: `evaluate_open_on` binds each to an
//! accumulator on each tier, and an observation of one answers the spine it
//! grows, which the readback reads as the neutral it spells.

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::read_back_value;
use gandr_core_term::CertificateEquality;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Form;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::RunInputs;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate_open_on;

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

/// How many producer binders out a variable reaches: zero names the
/// innermost.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Outward(u32);

/// The intuitionistic producer variable `outward` binders out.
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

/// `program` focused into an arena of its own, open over its context.
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
    (arena, root)
}

/// On each tier, `program` runs open and halts with a value that reads back
/// as `expected`.
///
/// # Specification
/// trivial.
fn assert_open(
    core: &mut CoreArena,
    program: ComputationId,
    expected: ValueId,
)
{
    let (arena, root) = focused(core, program);
    let definitions = Definitions::new();
    for &tier in tiers() {
        let mut store = Store::new();
        let outcome = evaluate_open_on(
            tier,
            (&arena, &definitions),
            root,
            (budget(), RunInputs::new(&mut store)),
        );
        let Ok(Outcome::Halted(value)) = outcome
        else {
            panic!("the run halts on {tier:?}: {outcome:?}");
        };
        let actual = read_back_value(&arena, &store, value, core).expect("the answer reads back");
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(core, actual, expected),
            "on {tier:?}"
        );
    }
}

/// A free function forced, forced and applied, and applied to its own
/// application reads back as the spine each grows, over `f` and `z`:
/// `force f`, `(force f) z` and `x ← (force f) z; (force f) x`, the last
/// `return ((force f) (return ((force f) z)))`.
#[test]
fn a_free_function_applied_reads_back_as_its_spine_3557()
{
    let mut core = CoreArena::new();
    let f = variable(&mut core, Outward(1));
    let z = variable(&mut core, Outward(0));
    let forced = core.computation_force(f);
    let expected = core.value_returned(forced);
    assert_open(&mut core, forced, expected);

    let applied = core.computation_application(forced, z);
    let once = core.value_returned(applied);
    assert_open(&mut core, applied, once);

    let inner_f = variable(&mut core, Outward(2));
    let x = variable(&mut core, Outward(0));
    let inner_forced = core.computation_force(inner_f);
    let again = core.computation_application(inner_forced, x);
    let program = core.computation_bind(applied, again);
    let twice = core.computation_application(forced, once);
    let expected = core.value_returned(twice);
    assert_open(&mut core, program, expected);
}

/// Captures apart in the context keep their indices, over `f`, `y` and `z`
/// with `y` unread: `return (f, z)` answers `(f, z)`, and `(force z) f`
/// reads back with `z` at its head, which a swapped capture slot would turn.
#[test]
fn two_free_variables_keep_their_names_3557()
{
    let mut core = CoreArena::new();
    let f = variable(&mut core, Outward(2));
    let z = variable(&mut core, Outward(0));
    let pair = core.value_tuple(&[f, z]);
    let program = core.computation_return(pair);
    assert_open(&mut core, program, pair);

    let forced = core.computation_force(z);
    let program = core.computation_application(forced, f);
    let expected = core.value_returned(program);
    assert_open(&mut core, program, expected);
}

/// A linear free variable declines: no accumulator stands for a value a run
/// must consume once.
#[test]
fn a_linear_free_variable_declines_3557()
{
    let mut core = CoreArena::new();
    let x = core.value_variable(Zone::Linear, 0_u32.into());
    let program = core.computation_return(x);
    let (arena, root) = focused(&core, program);
    let definitions = Definitions::new();
    for &tier in tiers() {
        let mut store = Store::new();
        assert_eq!(
            Err(Declined::Lowering(Form::Unbound)),
            evaluate_open_on(
                tier,
                (&arena, &definitions),
                root,
                (budget(), RunInputs::new(&mut store)),
            ),
            "on {tier:?}"
        );
    }
}
