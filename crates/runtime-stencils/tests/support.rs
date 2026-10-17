//! What the agreement suites share: the named programs, a deterministic
//! generator of closed positive-core programs, and the comparison of a
//! tier's answer with the L machine's, value by value across two stores.
//!
//! The emitter's suite includes this file too, so both packages hold their
//! tiers to one oracle.

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Machine;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::StepCount;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::read_back_terminal;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate_on;

/// The steps the machine and the jumps a tier may take: the dispatcher's
/// run budget.
pub const BUDGET: usize = 1 << 24;

/// An integer a test program is built from.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Integer(pub i64);

/// The literal `value` in `core`.
///
/// # Specification
/// trivial.
pub fn integer(
    core: &mut CoreArena,
    value: Integer,
) -> ValueId
{
    let magnitude =
        Magnitude::from_decimal_text(value.0.unsigned_abs().to_string()).expect("decimal digits");
    let sign = if value.0 < 0 {
        Sign::Negative
    }
    else {
        Sign::NonNegative
    };
    core.value_literal(Literal::Integer(IntegerLiteral::new(sign, magnitude)))
}

/// A closed program and what it shows.
pub struct Program
{
    /// What the program is, for a failure's message.
    pub name: &'static str,
    /// The arena holding it.
    pub core: CoreArena,
    /// The closed computation.
    pub root: ComputationId,
}

/// The variable at de Bruijn index zero.
///
/// # Specification
/// trivial.
fn innermost(core: &mut CoreArena) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, 0_u32.into())
}

/// The named programs: the five positive-core programs a return, a bind, a
/// case, a constructor and their composition answer, and three whose answer
/// suspends a computation — a function, a thunk and a pair holding one — so
/// a closure's site, captures and environment are compared too.
///
/// # Specification
/// trivial.
pub fn named() -> Vec<Program>
{
    let mut programs = Vec::new();
    let mut core = CoreArena::new();
    let five = integer(&mut core, Integer(5));
    let root = core.computation_return(five);
    programs.push(Program {
        name: "return 5",
        core,
        root,
    });

    let mut core = CoreArena::new();
    let seven = integer(&mut core, Integer(7));
    let bound = core.computation_return(seven);
    let variable = innermost(&mut core);
    let body = core.computation_return(variable);
    let root = core.computation_bind(bound, body);
    programs.push(Program {
        name: "x <- return 7; return x",
        core,
        root,
    });

    let mut core = CoreArena::new();
    let three = integer(&mut core, Integer(-3));
    let scrutinee = core.value_injection(Side::Left.into(), three);
    let variable = innermost(&mut core);
    let arm = core.computation_return(variable);
    let root = core.computation_case(scrutinee, &[arm, arm]);
    programs.push(Program {
        name: "case inl -3",
        core,
        root,
    });

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let pair = core.value_tuple(&[one, two]);
    let root = core.computation_return(pair);
    programs.push(Program {
        name: "return (1, 2)",
        core,
        root,
    });

    let mut core = CoreArena::new();
    let eight = integer(&mut core, Integer(8));
    let injection = core.value_injection(Side::Right.into(), eight);
    let bound = core.computation_return(injection);
    let variable = innermost(&mut core);
    let arm = core.computation_return(variable);
    let body = core.computation_case(variable, &[arm, arm]);
    let root = core.computation_bind(bound, body);
    programs.push(Program {
        name: "x <- return inr 8; case x",
        core,
        root,
    });

    let mut core = CoreArena::new();
    let nine = integer(&mut core, Integer(9));
    let bound = core.computation_return(nine);
    let variable = innermost(&mut core);
    let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let pair = core.value_tuple(&[variable, outer]);
    let returned = core.computation_return(pair);
    let function = core.computation_lambda(returned);
    let root = core.computation_bind(bound, function);
    programs.push(Program {
        name: "y <- return 9; fn x. return (x, y)",
        core,
        root,
    });

    let mut core = CoreArena::new();
    let four = integer(&mut core, Integer(4));
    let bound = core.computation_return(four);
    let variable = innermost(&mut core);
    let suspended = core.computation_return(variable);
    let thunk = core.value_thunk(suspended);
    let body = core.computation_return(thunk);
    let root = core.computation_bind(bound, body);
    programs.push(Program {
        name: "y <- return 4; return thunk { return y }",
        core,
        root,
    });

    let mut core = CoreArena::new();
    let six = integer(&mut core, Integer(6));
    let identity_body = innermost(&mut core);
    let identity_return = core.computation_return(identity_body);
    let identity = core.computation_lambda(identity_return);
    let applied = core.computation_application(identity, six);
    let thunk = core.value_thunk(applied);
    let unit = core.value_unit();
    let pair = core.value_tuple(&[thunk, unit]);
    let root = core.computation_return(pair);
    programs.push(Program {
        name: "return (thunk { (fn x. return x) 6 }, ())",
        core,
        root,
    });

    let mut core = CoreArena::new();
    let ten = integer(&mut core, Integer(10));
    let identity_body = innermost(&mut core);
    let identity_return = core.computation_return(identity_body);
    let identity = core.computation_lambda(identity_return);
    let root = core.computation_application(identity, ten);
    programs.push(Program {
        name: "(fn x. return x) 10",
        core,
        root,
    });
    programs
}

/// Focus `program` into a fresh command arena.
///
/// # Specification
/// trivial.
pub fn focus(program: &Program) -> (CommandArena, CommandId)
{
    let mut commands = CommandArena::new();
    let root = focus_computation(
        &program.core,
        program.root,
        &mut commands,
        &mut Provenance::new(),
    )
    .unwrap_or_else(|refusal| panic!("{}: focusing refused: {refusal:?}", program.name));
    (commands, root)
}

/// What a comparison is of, for a failure's message.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Label<'name>(pub &'name str);

/// How a tier answered against the machine.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Verdict
{
    /// The tier halted with the machine's answer.
    Agreed,
    /// Both stuck at a constructor no arm answers.
    BothUnmatched,
    /// The tier declined a form the machine runs.
    Declined(Declined),
}

/// Run `root` on the machine and on `tier`, and compare.
///
/// # Specification
/// - ensures: as [`agree_with`], the tier's run being `evaluate_on`.
/// - executable: none — the comparison is the suite's oracle; a predicate over
///   it would be the walk itself.
///
/// # Adequacy
/// - hypothesis: L2 — every named program agrees on each tier, and a difference
///   of literal, head, field or presence is named.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::support::a_differing_answer_is_named`
pub fn agree(
    name: Label<'_>,
    commands: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    tier: Tier,
) -> Verdict
{
    agree_with(
        Label(&format!("{} on {tier:?}", name.0)),
        commands,
        definitions,
        root,
        |store| evaluate_on(tier, commands, definitions, root, Fuel::from(BUDGET), store),
    )
}

/// Run `root` on the machine and through `run`, and compare.
///
/// # Specification
/// - ensures: [`Verdict::Agreed`] when both halt and the answers are equal
///   value by value, readback succeeding for the run's exactly when it succeeds
///   for the machine's; [`Verdict::BothUnmatched`] when both stick at an
///   unmatched constructor; [`Verdict::Declined`] for a form the lowering
///   refuses; a panic naming the difference otherwise.
/// - executable: none — the comparison is the suite's oracle; a predicate over
///   it would be the walk itself.
///
/// # Adequacy
/// - hypothesis: L2 — every named program agrees on each tier and under the
///   policy, and a difference of literal, head, field or presence is named.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::support::a_differing_answer_is_named`
pub fn agree_with(
    name: Label<'_>,
    commands: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    run: impl FnOnce(&mut Store) -> Result<HeapValueId, Declined>,
) -> Verdict
{
    let Label(name) = name;
    let mut machine = Machine::new(commands, definitions);
    let outcome = machine
        .run(root, StepCount::from(BUDGET))
        .unwrap_or_else(|fault| panic!("{name}: the machine faulted: {fault:?}"));
    let mut store = Store::new();
    match (outcome, run(&mut store)) {
        (Outcome::Halted(expected), Ok(answer)) => {
            if let Err(difference) = same_value(machine.store(), expected, &store, answer) {
                panic!("{name}: the answers differ at {difference}");
            }
            let mut left = CoreArena::new();
            let mut right = CoreArena::new();
            assert_eq!(
                read_back_terminal(commands, machine.store(), expected, &mut left).is_ok(),
                read_back_terminal(commands, &store, answer, &mut right).is_ok(),
                "{name}: one answer reads back and the other does not"
            );
            Verdict::Agreed
        },
        (Outcome::Stuck(Stuck::Unmatched { .. }), Err(Declined::Unmatched)) => {
            Verdict::BothUnmatched
        },
        (_, Err(declined @ Declined::Lowering(_))) => Verdict::Declined(declined),
        (outcome, ran) => panic!("{name}: the machine gave {outcome:?}, the run {ran:?}"),
    }
}

/// One pending pair of values.
type Pair = (HeapValueId, HeapValueId);

/// Whether the value `left` of `left_store` and `right` of `right_store`
/// are equal: the same literal, the same head over equal fields, or the same
/// suspended code over equal environments.
///
/// # Specification
/// - ensures: `Ok` exactly when every pair the walk reaches agrees; memo cells,
///   which record evaluation order, are not compared.
/// - executable: none — the walk is the comparison; a predicate would walk
///   again.
///
/// # Errors
/// A description of the first pair that differs.
///
/// # Adequacy
/// - hypothesis: L2 — equal literals and constructions agree, and a difference
///   of literal, head, field or presence is named.
/// - witness: `tests::support::a_differing_answer_is_named`
pub fn same_value(
    left_store: &Store,
    left: HeapValueId,
    right_store: &Store,
    right: HeapValueId,
) -> Result<(), String>
{
    let mut pending: Vec<Pair> = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        let held = (left_store.value(left), right_store.value(right));
        let (Some(first), Some(second)) = held
        else {
            return Err(format!("{left:?} or {right:?} dangles"));
        };
        let environments = match (first, second) {
            (&HeapValue::Literal(ref first), &HeapValue::Literal(ref second))
                if first == second =>
            {
                None
            },
            (
                &HeapValue::Constructed {
                    ref tag,
                    ref fields,
                },
                &HeapValue::Constructed {
                    tag: ref other,
                    fields: ref others,
                },
            ) if tag == other && fields.len() == others.len() => {
                pending.extend(fields.iter().copied().zip(others.iter().copied()));
                None
            },
            (
                &HeapValue::Thunk {
                    body, environment, ..
                },
                &HeapValue::Thunk {
                    body: other,
                    environment: others,
                    ..
                },
            ) if body == other => Some((environment, others)),
            (
                &HeapValue::Fixpoint {
                    body,
                    environment,
                    evidence,
                    ..
                },
                &HeapValue::Fixpoint {
                    body: other,
                    environment: others,
                    evidence: claimed,
                    ..
                },
            ) if body == other && evidence == claimed => Some((environment, others)),
            (
                &HeapValue::Closure {
                    producer,
                    environment,
                },
                &HeapValue::Closure {
                    producer: other,
                    environment: others,
                },
            ) if producer == other => Some((environment, others)),
            _ => return Err(format!("{first:?} against {second:?}")),
        };
        if let Some((first, second)) = environments {
            let firsts: Vec<_> = left_store.bound_values(first).collect();
            let seconds: Vec<_> = right_store.bound_values(second).collect();
            if firsts.len() != seconds.len() {
                return Err(format!(
                    "environments of {} and {} bindings",
                    firsts.len(),
                    seconds.len()
                ));
            }
            pending.extend(firsts.into_iter().zip(seconds));
        }
    }
    Ok(())
}

/// The comparison names a difference wherever one lies: a literal, a head,
/// a field beneath a constructor, or a value one store lacks.
#[test]
fn a_differing_answer_is_named()
{
    let literal = |value: u8| {
        let magnitude = Magnitude::from_decimal_text(value.to_string()).expect("decimal digits");
        HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            magnitude,
        )))
    };
    let construct = |side: Side, field: HeapValueId| HeapValue::Constructed {
        tag: ConstructorTag::Injection(side.into()),
        fields: Box::from([field]),
    };
    let mut left = Store::new();
    let mut right = Store::new();
    let allocate = |store: &mut Store, value: HeapValue| store.allocate(value).expect("room");
    let one = allocate(&mut left, literal(1));
    let other_one = allocate(&mut right, literal(1));
    let two = allocate(&mut right, literal(2));
    let boxed_one = allocate(&mut left, construct(Side::Left, one));
    let other_boxed_one = allocate(&mut right, construct(Side::Left, other_one));
    let boxed_two = allocate(&mut right, construct(Side::Left, two));
    let other_head = allocate(&mut right, construct(Side::Right, other_one));
    assert_eq!(
        Ok(()),
        same_value(&left, one, &right, other_one),
        "equal literals agree"
    );
    assert_eq!(
        Ok(()),
        same_value(&left, boxed_one, &right, other_boxed_one),
        "equal constructions agree"
    );
    for (first, second, what) in [
        (one, two, "a literal"),
        (boxed_one, boxed_two, "a field beneath a constructor"),
        (boxed_one, other_head, "a head"),
        (one, other_boxed_one, "a literal against a construction"),
    ] {
        assert!(
            same_value(&left, first, &right, second).is_err(),
            "{what} differs"
        );
    }
    assert!(
        same_value(&left, one, &Store::new(), one).is_err(),
        "a value one store lacks"
    );
}
