//! A migration run in one process: its body at its world on a thread and
//! over a store of its own, what it takes and answers crossing by content.

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::FreeSet;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::check_command;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::read_back_value;
use gandr_core_term::CertificateEquality;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CharacterLiteral;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FixedInteger;
use gandr_kernel_term::Float64Literal;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::Summand;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate_on;

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

/// The decimal digits of a test literal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Digits(&'static str);

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

/// The innermost producer variable.
///
/// # Specification
/// trivial.
fn innermost(core: &mut CoreArena) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, 0_u32.into())
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
    let root = focus_computation(core, program, &mut arena, &mut Provenance::new())
        .expect("the program focuses");
    assert_eq!(Ok(FreeSet::default()), check_command(&arena, root));
    (arena, root)
}

/// The two fields of the pair `store` binds at `answer`.
///
/// # Specification
/// trivial.
fn fields(
    store: &Store,
    answer: HeapValueId,
) -> [HeapValueId; 2]
{
    let Some(&HeapValue::Constructed { ref fields, .. }) = store.value(answer)
    else {
        panic!("the run answers a constructor");
    };
    <[HeapValueId; 2]>::try_from(&**fields).expect("a pair")
}

/// The pair answered by `program` on `tier`, read back into `core`, and its
/// two fields in the store it was moved into.
///
/// # Specification
/// trivial.
fn ran(
    tier: Tier,
    core: &mut CoreArena,
    program: ComputationId,
) -> (ValueId, [HeapValueId; 2])
{
    let (arena, root) = focused(core, program);
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
    let read = read_back_value(&arena, &store, answer, core).expect("the answer reads back");
    (read, fields(&store, answer))
}

/// `migrate [host] { return value }`, run on each tier, reads back `value`.
///
/// # Specification
/// trivial.
fn comes_back(
    core: &mut CoreArena,
    value: ValueId,
)
{
    let body = core.computation_return(value);
    let program = core.computation_world(WorldForm::Migrate {
        world: World::Host,
        body,
    });
    let (arena, root) = focused(core, program);
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
        let read = read_back_value(&arena, &store, answer, core).expect("the answer reads back");
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(core, read, value),
            "on {tier:?}"
        );
    }
}

/// `hold (1, 2)` opened by `leta y` and answered as `(y, y)`, in place and
/// inside `migrate [host] { … }`: both read back `((1, 2), (1, 2))` on each
/// tier, but where the pair in place is one store value held twice, the pair
/// a migration answers crossed back by content, its sharing unfolded, so the
/// caller reads two equal values laid out fresh in its own store.
#[test]
fn a_migration_crosses_its_capture_in_and_its_answer_back()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let inner = core.value_tuple(&[one, two]);
    let expected = core.value_tuple(&[inner, inner]);
    let held = core.computation_world(WorldForm::Hold { value: inner });
    let program = |core: &mut CoreArena, migrated: Option<World>| {
        let y = innermost(core);
        let twice = core.value_tuple(&[y, y]);
        let mut body = core.computation_return(twice);
        if let Some(world) = migrated {
            body = core.computation_world(WorldForm::Migrate { world, body });
        }
        let handle = innermost(core);
        let opened = core.computation_world(WorldForm::Leta {
            value: handle,
            body,
        });
        core.computation_bind(held, opened)
    };
    let in_place = program(&mut core, None);
    let migrated = program(&mut core, Some(World::Host));
    for &tier in tiers() {
        let (read, [first, second]) = ran(tier, &mut core, in_place);
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(&core, read, expected),
            "in place on {tier:?}"
        );
        assert_eq!(
            first, second,
            "in place the pair holds one value on {tier:?}"
        );
        let (read, [first, second]) = ran(tier, &mut core, migrated);
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(&core, read, expected),
            "migrated on {tier:?}"
        );
        assert_ne!(
            first, second,
            "a migration's answer crossed unfolded on {tier:?}"
        );
    }
}

/// A capture that does not cross declines the run at its migration: a thunk
/// literal of the caller's the world's code holds no site for,
/// `(λf. migrate [host] { (force f) 7 }) (thunk { λx. return x })`, which the
/// checker refuses, since a thunk reached through a variable carries no image.
#[test]
fn a_capture_that_does_not_cross_declines_at_its_migration()
{
    let mut core = CoreArena::new();
    let seven = integer(&mut core, Digits("7"));
    let x = innermost(&mut core);
    let identity = core.computation_return(x);
    let identity = core.computation_lambda(identity);
    let identity = core.value_thunk(identity);
    let f = innermost(&mut core);
    let forced = core.computation_force(f);
    let applied = core.computation_application(forced, seven);
    let migrated = core.computation_world(WorldForm::Migrate {
        world: World::Host,
        body: applied,
    });
    let function = core.computation_lambda(migrated);
    let program = core.computation_application(function, identity);
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
        assert!(
            matches!(outcome, Err(Declined::Migration(_))),
            "on {tier:?}: {outcome:?}"
        );
    }
}

/// A record built only at the world comes back to a caller whose own code
/// builds none: `migrate [host] { return #{x = 1, y = 2} }` reads back
/// `#{x = 1, y = 2}` on each tier, the record's head joining the caller's
/// table as the answer is laid out on its heap.
#[test]
fn a_record_built_only_at_the_world_comes_back()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let record = core.value_record(
        [("x", one), ("y", two)]
            .map(|(label, field)| (FieldLabel::from(String::from(label)), field))
            .into(),
    );
    comes_back(&mut core, record);
}

/// A thunk a migration answers runs at its caller as it runs in place:
/// `bind (migrate [host] { bind (return 1) (bind (return 2) (return thunk
/// { return (m, n) })) }) (force t)` reads back `(1, 2)` on each tier, the
/// thunk laid out at the caller's site for its body and its two captures in
/// their order, as the same program without the migration does (#3265).
#[test]
fn a_thunk_a_migration_returns_runs_at_the_caller_3265()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let expected = core.value_tuple(&[one, two]);
    let program = |core: &mut CoreArena, migrated: Option<World>| {
        let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
        let inner = innermost(core);
        let pair = core.value_tuple(&[outer, inner]);
        let suspended = core.computation_return(pair);
        let thunk = core.value_thunk(suspended);
        let returned = core.computation_return(thunk);
        let second = core.computation_return(two);
        let bound = core.computation_bind(second, returned);
        let first = core.computation_return(one);
        let mut body = core.computation_bind(first, bound);
        if let Some(world) = migrated {
            body = core.computation_world(WorldForm::Migrate { world, body });
        }
        let t = innermost(core);
        let forced = core.computation_force(t);
        core.computation_bind(body, forced)
    };
    for migrated in [None, Some(World::Host)] {
        let program = program(&mut core, migrated);
        for &tier in tiers() {
            let (read, _) = ran(tier, &mut core, program);
            assert_eq!(
                CertificateEquality::Equal,
                equal_certificate_syntax(&core, read, expected),
                "{migrated:?} on {tier:?}"
            );
        }
    }
}

/// A field of a record a migration answers reads as the same field of the
/// record built in place: `bind (migrate [host] { return #{x = 1, y = 2} })
/// (bind r.y (bind r.x (return (y, x))))` reads back `(2, 1)` on each tier,
/// as the same program without the migration does, though only the world's
/// body builds the record (#3275).
#[test]
fn a_field_of_a_record_a_migration_answers_projects_3275()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let two = integer(&mut core, Digits("2"));
    let expected = core.value_tuple(&[two, one]);
    let label = |label: &str| FieldLabel::from(String::from(label));
    let program = |core: &mut CoreArena, migrated: Option<World>| {
        let record = core.value_record(
            [("x", one), ("y", two)]
                .map(|(at, field)| (label(at), field))
                .into(),
        );
        let mut body = core.computation_return(record);
        if let Some(world) = migrated {
            body = core.computation_world(WorldForm::Migrate { world, body });
        }
        let r = innermost(core);
        let second = core.computation_record_projection(r, label("y"));
        let r = core.value_variable(Zone::Intuitionistic, 1_u32.into());
        let first = core.computation_record_projection(r, label("x"));
        let y = core.value_variable(Zone::Intuitionistic, 1_u32.into());
        let x = innermost(core);
        let pair = core.value_tuple(&[y, x]);
        let paired = core.computation_return(pair);
        let read = core.computation_bind(first, paired);
        let read = core.computation_bind(second, read);
        core.computation_bind(body, read)
    };
    for migrated in [None, Some(World::Host)] {
        let program = program(&mut core, migrated);
        for &tier in tiers() {
            let (read, _) = ran(tier, &mut core, program);
            assert_eq!(
                CertificateEquality::Equal,
                equal_certificate_syntax(&core, read, expected),
                "{migrated:?} on {tier:?}"
            );
        }
    }
}

/// The other heads a value the checker lets cross can hold come back from the
/// world as they went: the unit, a character, a float, a fixed width, an
/// injection, a list and a lift, in one tuple built only at the world.
#[test]
fn every_head_a_crossing_value_holds_comes_back()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, Digits("1"));
    let unit = core.value_unit();
    let character = core.value_literal(Literal::Character(CharacterLiteral::from('é')));
    let float = core.value_literal(Literal::Float64(Float64Literal::from(0.5_f64)));
    let fixed = core.value_literal(Literal::Fixed(FixedInteger::I64(i64::MIN)));
    let injected = core.value_injection(Summand::from(1_usize), one);
    let nil = core.value_list_nil();
    let list = core.value_list_cons(one, nil);
    let lifted = core.value_lift(Level::zero(), one);
    let every = core.value_tuple(&[unit, character, float, fixed, injected, list, lifted]);
    comes_back(&mut core, every);
}
