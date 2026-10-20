//! What the agreement suites share: the named programs and the answers they
//! state, a deterministic generator of closed positive-core programs, and the
//! comparison of native code's run with the portable executor's, value by
//! value across two stores.
//!
//! The emitter's suite includes this file too, so both packages hold their
//! tiers to one oracle.

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::read_back_terminal;
use gandr_core_sequent::render_command;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::control::StackFrame;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::PRELUDE;
use gandr_kernel_term::Component;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate_on;

/// The jumps a tier may take: the dispatcher's run budget.
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

/// A closed program.
pub struct Program
{
    /// What the program is, for a failure's message.
    pub name: &'static str,
    /// The arena holding it.
    pub core: CoreArena,
    /// The closed computation.
    pub root: ComputationId,
}

/// A closed program and the answer it states: the focused rendering of its
/// answer's reading.
pub struct Named
{
    /// The program.
    pub program: Program,
    /// What its answer reads back as.
    pub shows: &'static str,
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
/// case, a constructor and their composition answer; three whose answer
/// suspends a computation — a function, a thunk and a pair holding one — so
/// a closure's site, captures and environment are compared too; three
/// primitive calls, answering an integer, an integer past 64 bits and a
/// boolean; a reified stack resumed, its application frame and its bind
/// frame, which reads a variable bound outside the stack; and a lazy product
/// projected where it is built and after it was suspended, so an object
/// answers the projection it is entered with.
///
/// # Specification
/// trivial.
pub fn named() -> Vec<Named>
{
    let mut programs = Vec::new();
    let mut push = |name, shows, core, root| {
        programs.push(Named {
            program: Program { name, core, root },
            shows,
        });
    };
    let mut core = CoreArena::new();
    let five = integer(&mut core, Integer(5));
    let root = core.computation_return(five);
    push("return 5", "⟨5 |+ ★⟩", core, root);

    let mut core = CoreArena::new();
    let seven = integer(&mut core, Integer(7));
    let bound = core.computation_return(seven);
    let variable = innermost(&mut core);
    let body = core.computation_return(variable);
    let root = core.computation_bind(bound, body);
    push("x <- return 7; return x", "⟨7 |+ ★⟩", core, root);

    let mut core = CoreArena::new();
    let three = integer(&mut core, Integer(-3));
    let scrutinee = core.value_injection(Side::Left.into(), three);
    let variable = innermost(&mut core);
    let arm = core.computation_return(variable);
    let root = core.computation_case(scrutinee, &[arm, arm]);
    push("case inl -3", "⟨-3 |+ ★⟩", core, root);

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let pair = core.value_tuple(&[one, two]);
    let root = core.computation_return(pair);
    push("return (1, 2)", "⟨pair(1, 2) |+ ★⟩", core, root);

    let mut core = CoreArena::new();
    let eight = integer(&mut core, Integer(8));
    let injection = core.value_injection(Side::Right.into(), eight);
    let bound = core.computation_return(injection);
    let variable = innermost(&mut core);
    let arm = core.computation_return(variable);
    let body = core.computation_case(variable, &[arm, arm]);
    let root = core.computation_bind(bound, body);
    push("x <- return inr 8; case x", "⟨8 |+ ★⟩", core, root);

    let mut core = CoreArena::new();
    let nine = integer(&mut core, Integer(9));
    let bound = core.computation_return(nine);
    let variable = innermost(&mut core);
    let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let pair = core.value_tuple(&[variable, outer]);
    let returned = core.computation_return(pair);
    let function = core.computation_lambda(returned);
    let root = core.computation_bind(bound, function);
    push(
        "y <- return 9; fn x. return (x, y)",
        "⟨cocase {apply(x; α) ⇒ ⟨pair(x0, 9) |+ α0⟩} |− ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let four = integer(&mut core, Integer(4));
    let bound = core.computation_return(four);
    let variable = innermost(&mut core);
    let suspended = core.computation_return(variable);
    let thunk = core.value_thunk(suspended);
    let body = core.computation_return(thunk);
    let root = core.computation_bind(bound, body);
    push(
        "y <- return 4; return thunk { return y }",
        "⟨{force(α) ⇒ ⟨4 |+ α0⟩} |+ ★⟩",
        core,
        root,
    );

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
    push(
        "return (thunk { (fn x. return x) 6 }, ())",
        "⟨pair({force(α) ⇒ ⟨cocase {apply(x; α) ⇒ ⟨x0 |+ α0⟩} |− apply(6; α0)⟩}, ()) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let ten = integer(&mut core, Integer(10));
    let identity_body = innermost(&mut core);
    let identity_return = core.computation_return(identity_body);
    let identity = core.computation_lambda(identity_return);
    let root = core.computation_application(identity, ten);
    push("(fn x. return x) 10", "⟨10 |+ ★⟩", core, root);
    for (name, shows, primitive, left, right) in [
        ("add 2 3", "⟨5 |+ ★⟩", "add", 2_i64, 3_i64),
        (
            "mul 2^62 4",
            "⟨18446744073709551616 |+ ★⟩",
            "mul",
            0x4000_0000_0000_0000_i64,
            4_i64,
        ),
        ("lt 1 2", "⟨inl(()) |+ ★⟩", "lt", 1_i64, 2_i64),
    ] {
        let mut core = CoreArena::new();
        let left = integer(&mut core, Integer(left));
        let right = integer(&mut core, Integer(right));
        let row = *PRELUDE
            .iter()
            .find(|row| row.name().as_ref() == primitive)
            .expect("a prelude row");
        let root = core.computation_primitive(row, Arguments::Binary([left, right]));
        push(name, shows, core, root);
    }

    let mut core = CoreArena::new();
    let two = integer(&mut core, Integer(2));
    let three = integer(&mut core, Integer(3));
    let bound = core.computation_return(two);
    let head = innermost(&mut core);
    let outer = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let pair = core.value_tuple(&[head, outer]);
    let bind = core.computation_return(pair);
    let stack = core.value_reify(
        [
            gandr_core_term::control::StackFrame::Apply(three),
            gandr_core_term::control::StackFrame::Bind(bind),
        ]
        .into(),
    );
    let argument = innermost(&mut core);
    let identity_return = core.computation_return(argument);
    let identity = core.computation_lambda(identity_return);
    let resumed = core.computation_resume(stack, identity);
    let root = core.computation_bind(bound, resumed);
    push(
        "y <- return 2; resume [apply 3, bind x. return (x, y)] { fn z. return z }",
        "⟨pair(3, 2) |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let three = integer(&mut core, Integer(3));
    let first = core.computation_return(one);
    let second = core.computation_return(two);
    let third = core.computation_return(three);
    let lazy = core.computation_with(&[first, second, third]);
    let root = core.computation_project(Component::from(2_usize), lazy);
    push(
        "project 2 (with { return 1 } { return 2 } { return 3 })",
        "⟨3 |+ ★⟩",
        core,
        root,
    );

    let mut core = CoreArena::new();
    let one = integer(&mut core, Integer(1));
    let two = integer(&mut core, Integer(2));
    let three = integer(&mut core, Integer(3));
    let first = core.computation_return(one);
    let second = core.computation_return(two);
    let third = core.computation_return(three);
    let lazy = core.computation_with(&[first, second, third]);
    let suspended = core.value_thunk(lazy);
    let bound = core.computation_return(suspended);
    let variable = innermost(&mut core);
    let forced = core.computation_force(variable);
    let projected = core.computation_project(Component::from(1_usize), forced);
    let root = core.computation_bind(bound, projected);
    push(
        "t <- return thunk { with { return 1 } { return 2 } { return 3 } }; project 1 (force t)",
        "⟨2 |+ ★⟩",
        core,
        root,
    );
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

/// The tier a run is compared on: native code where this host has a
/// patcher; elsewhere the executor, against a second run of itself.
pub const COMPARED: Tier = if PATCHER {
    Tier::Native
}
else {
    Tier::Executor
};

/// What the tiers answered, once they agreed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Verdict
{
    /// Both halted with equal answers, reading back as this rendering, or
    /// both with no reading.
    Halted(Option<String>),
    /// Both stopped stuck the same way; the executor's stop.
    Stuck(Stuck),
    /// Both declined for the same reason.
    Declined(Declined),
}

/// Run `root` on the executor and on [`COMPARED`], and compare.
///
/// # Specification
/// - ensures: as [`agree_with`], the compared run being [`COMPARED`]'s.
/// - executable: none — the comparison is the suite's oracle; a predicate over
///   it would be the walk itself.
///
/// # Adequacy
/// - hypothesis: L2 — every named program agrees across the tiers and states
///   its answer, and a difference of literal, head, field or presence is named.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::support::a_differing_answer_is_named`
pub fn agree(
    name: Label<'_>,
    commands: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
) -> Verdict
{
    agree_with(
        Label(&format!("{} on {COMPARED:?}", name.0)),
        commands,
        definitions,
        root,
        |store| {
            evaluate_on(
                COMPARED,
                commands,
                definitions,
                root,
                Fuel::from(BUDGET),
                store,
            )
        },
    )
}

/// Run `root` on the executor and through `run`, and compare.
///
/// # Specification
/// - ensures: the two runs halt with answers equal value by value and reading
///   back alike, stop stuck the same way over equal values, or decline for the
///   same reason, and the executor's outcome is the verdict; a panic naming the
///   difference otherwise.
/// - executable: none — the comparison is the suite's oracle; a predicate over
///   it would be the walk itself.
///
/// # Adequacy
/// - hypothesis: L2 — every named program agrees across the tiers and under the
///   policy, and a difference of literal, head, field or presence is named.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::support::a_differing_answer_is_named`
pub fn agree_with(
    name: Label<'_>,
    commands: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    run: impl FnOnce(&mut Store) -> Result<Outcome, Declined>,
) -> Verdict
{
    let Label(name) = name;
    let mut expected_store = Store::new();
    let expected = evaluate_on(
        Tier::Executor,
        commands,
        definitions,
        root,
        Fuel::from(BUDGET),
        &mut expected_store,
    );
    let mut store = Store::new();
    let ran = run(&mut store);
    if let Err(difference) = same_outcome(&expected_store, &expected, &store, &ran) {
        panic!("{name}: the runs differ at {difference}");
    }
    match (expected, ran) {
        (Ok(Outcome::Halted(expected)), Ok(Outcome::Halted(answer))) => {
            let reading = reading(commands, &expected_store, expected);
            assert_eq!(
                reading,
                self::reading(commands, &store, answer),
                "{name}: the answers read back differently"
            );
            Verdict::Halted(reading)
        },
        (Ok(Outcome::Stuck(stuck)), _) => Verdict::Stuck(stuck),
        (Err(declined), _) => Verdict::Declined(declined),
        (Ok(Outcome::Halted(_)), other) => panic!("{name}: halted against {other:?}"),
    }
}

/// The focused rendering of the reading of `value`, or nothing when it has
/// none.
///
/// # Specification
/// trivial.
fn reading(
    commands: &CommandArena,
    store: &Store,
    value: HeapValueId,
) -> Option<String>
{
    let mut core = CoreArena::new();
    let back = read_back_terminal(commands, store, value, &mut core).ok()?;
    let mut focused = CommandArena::new();
    let root = focus_computation(&core, back, &mut focused, &mut Provenance::new())
        .expect("a reading focuses");
    Some(render_command(&focused, root))
}

/// Whether two runs' outcomes agree: equal answers, the same stop over equal
/// values, or the same decline.
///
/// # Specification
/// - ensures: `Ok` exactly when both halt with answers [`same_value`] accepts,
///   both stop stuck as [`same_stuck`] accepts, or both decline equally.
/// - executable: none — the walk is the comparison; a predicate would walk
///   again.
///
/// # Errors
/// A description of the difference.
///
/// # Adequacy
/// - hypothesis: L2 — equal outcomes agree, and a difference of kind is named.
/// - witness: `tests::support::a_differing_answer_is_named`
fn same_outcome(
    left_store: &Store,
    left: &Result<Outcome, Declined>,
    right_store: &Store,
    right: &Result<Outcome, Declined>,
) -> Result<(), String>
{
    match (left, right) {
        (&Ok(Outcome::Halted(first)), &Ok(Outcome::Halted(second))) => {
            same_value(left_store, first, right_store, second)
        },
        (&Ok(Outcome::Stuck(ref first)), &Ok(Outcome::Stuck(ref second))) => {
            same_stuck(left_store, first, right_store, second)
        },
        (&Err(first), &Err(second)) if first == second => Ok(()),
        (first, second) => Err(format!("{first:?} against {second:?}")),
    }
}

/// Whether two stops are the same: the same reason at the same site, over
/// equal values.
///
/// # Specification
/// - ensures: `Ok` exactly when both name the same reason and site and every
///   value they hold agrees under [`same_value`].
/// - executable: none — the walk is the comparison; a predicate would walk
///   again.
///
/// # Errors
/// A description of the difference.
///
/// # Adequacy
/// - hypothesis: L2 — equal stops agree, and a difference of reason, site or
///   held value is named.
/// - witness: `tests::support::a_differing_answer_is_named`
fn same_stuck(
    left_store: &Store,
    left: &Stuck,
    right_store: &Store,
    right: &Stuck,
) -> Result<(), String>
{
    match (left, right) {
        (
            &Stuck::Unobservable { value, head },
            &Stuck::Unobservable {
                value: other,
                head: also,
            },
        ) if head == also => same_value(left_store, value, right_store, other),
        (
            &Stuck::Unmatched { value, arms },
            &Stuck::Unmatched {
                value: other,
                arms: also,
            },
        ) if arms == also => same_value(left_store, value, right_store, other),
        (&Stuck::NonScalar(value), &Stuck::NonScalar(other)) => {
            same_value(left_store, value, right_store, other)
        },
        (
            &Stuck::ResumedNonStack { at, value },
            &Stuck::ResumedNonStack {
                at: also,
                value: other,
            },
        ) if at == also => same_value(left_store, value, right_store, other),
        (first, second) if first == second => Ok(()),
        (first, second) => Err(format!("{first:?} against {second:?}")),
    }
}

/// One pending pair of values.
type Pair = (HeapValueId, HeapValueId);

/// Whether the value `left` of `left_store` and `right` of `right_store`
/// are equal: the same literal or constant, the same head over equal fields,
/// the same frames over equal values, or the same suspended code over equal
/// environments.
///
/// # Specification
/// - ensures: `Ok` exactly when every pair the walk reaches agrees; two
///   capabilities agree, their identity being their address in each store.
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
        let mut environments = Vec::new();
        match (first, second) {
            (&HeapValue::Literal(ref first), &HeapValue::Literal(ref second))
                if first == second => {},
            (&HeapValue::Opaque(first), &HeapValue::Opaque(second)) if first == second => {},
            (&HeapValue::Capability, &HeapValue::Capability) => {},
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
            },
            (&HeapValue::Stack { ref frames }, &HeapValue::Stack { frames: ref others })
                if frames.len() == others.len() =>
            {
                for (frame, other) in frames.iter().zip(others.iter()) {
                    match (*frame, *other) {
                        (StackFrame::Apply(argument), StackFrame::Apply(another)) => {
                            pending.push((argument, another));
                        },
                        (StackFrame::Project(side), StackFrame::Project(another))
                            if side == another => {},
                        (StackFrame::Bind(closed), StackFrame::Bind(another))
                            if closed.body == another.body =>
                        {
                            environments.push((closed.environment, another.environment));
                        },
                        (frame, other) => return Err(format!("{frame:?} against {other:?}")),
                    }
                }
            },
            (
                &HeapValue::Thunk { body, environment },
                &HeapValue::Thunk {
                    body: other,
                    environment: others,
                },
            ) if body == other => environments.push((environment, others)),
            (
                &HeapValue::Fixpoint {
                    body,
                    environment,
                    evidence,
                },
                &HeapValue::Fixpoint {
                    body: other,
                    environment: others,
                    evidence: claimed,
                },
            ) if body == other && evidence == claimed => environments.push((environment, others)),
            (
                &HeapValue::Closure {
                    producer,
                    environment,
                },
                &HeapValue::Closure {
                    producer: other,
                    environment: others,
                },
            ) if producer == other => environments.push((environment, others)),
            _ => return Err(format!("{first:?} against {second:?}")),
        }
        for (first, second) in environments {
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
/// a field beneath a constructor, a value one store lacks, the value or the
/// head a stop holds, and a halt against a decline.
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
    let unobservable = |value, head| Ok(Outcome::Stuck(Stuck::Unobservable { value, head }));
    let force = gandr_core_sequent::DestructorTag::Force;
    let apply = gandr_core_sequent::DestructorTag::Apply;
    assert_eq!(
        Ok(()),
        same_outcome(
            &left,
            &unobservable(boxed_one, force),
            &right,
            &unobservable(other_boxed_one, force)
        ),
        "equal stops agree"
    );
    let exhausted = Err(Declined::Exhausted(
        gandr_runtime_emitter::Status::FuelExhausted,
    ));
    assert_eq!(
        Ok(()),
        same_outcome(&left, &exhausted, &right, &exhausted),
        "equal declines agree"
    );
    for (first, second, what) in [
        (
            unobservable(boxed_one, force),
            unobservable(boxed_two, force),
            "a stop's value",
        ),
        (
            unobservable(boxed_one, force),
            unobservable(other_boxed_one, apply),
            "a stop's head",
        ),
        (
            Ok(Outcome::Halted(one)),
            exhausted,
            "a halt against a decline",
        ),
    ] {
        assert!(
            same_outcome(&left, &first, &right, &second).is_err(),
            "{what} differs"
        );
    }
}
