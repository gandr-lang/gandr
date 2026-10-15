use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::memory::MemoryForm;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;

use crate::CheckBudget;
use crate::CheckingContext;
use crate::access::AccessDefect;
use crate::check_comp;
use crate::fixture::integer_literal;
use crate::form_comp_type;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::session::Capture;
use crate::synthesise_comp;

/// The innermost linear slot, `l0`.
///
/// # Specification
/// trivial.
fn l0() -> DeBruijnIndex
{
    DeBruijnIndex::from(0_u32)
}

/// The linear slot one out, `l1`.
///
/// # Specification
/// trivial.
fn l1() -> DeBruijnIndex
{
    DeBruijnIndex::from(1_u32)
}

/// The linear variable `index` and a read of it that synthesises:
/// `(lN,).0`.
///
/// # Specification
/// trivial.
fn copied(
    arena: &mut CoreArena,
    index: DeBruijnIndex,
) -> (ValueId, ComputationId)
{
    let variable = arena.value_variable(Zone::Linear, index);
    let single = arena.value_tuple(&[variable]);
    let projected =
        arena.computation_tuple_projection(single, gandr_kernel_term::Component::from(0_usize));
    (variable, projected)
}

/// `hold x = 0; body`.
///
/// # Specification
/// trivial.
fn hold(
    arena: &mut CoreArena,
    body: ComputationId,
) -> ComputationId
{
    let value = arena.value_literal(integer_literal());
    arena.computation_memory(MemoryForm::Hold { value, body })
}

/// `access lN as v { body } unwind { unwind }`.
///
/// # Specification
/// trivial.
fn access(
    arena: &mut CoreArena,
    held: DeBruijnIndex,
    body: ComputationId,
    unwind: ComputationId,
) -> ComputationId
{
    arena.computation_memory(MemoryForm::Access { held, body, unwind })
}

/// `resume(lN, value)`.
///
/// # Specification
/// trivial.
fn resume(
    arena: &mut CoreArena,
    view: DeBruijnIndex,
    value: ValueId,
) -> ComputationId
{
    arena.computation_memory(MemoryForm::Resume { view, value })
}

/// `abort(lN)`.
///
/// # Specification
/// trivial.
fn abort(
    arena: &mut CoreArena,
    view: DeBruijnIndex,
) -> ComputationId
{
    arena.computation_memory(MemoryForm::Abort { view })
}

/// `return ()`.
///
/// # Specification
/// trivial.
fn done(arena: &mut CoreArena) -> ComputationId
{
    let unit = arena.value_unit();
    arena.computation_return(unit)
}

/// The pure returner of the integers.
///
/// # Specification
/// trivial.
fn integers(arena: &mut CoreArena) -> CompTypeId
{
    let integer = arena.value_type_base(BaseType::Integer);
    arena.comp_type_returner(integer)
}

/// The pure returner of the unit.
///
/// # Specification
/// trivial.
fn units(arena: &mut CoreArena) -> CompTypeId
{
    let unit = arena.value_type_unit();
    arena.comp_type_returner(unit)
}

/// The one interface `Probe` with the operation `poke : () -> ()`.
///
/// # Specification
/// trivial.
fn probe(arena: &mut CoreArena) -> EffectSig
{
    let unit = arena.value_type_unit();
    EffectSig::new("Probe".into(), [EffectOp {
        name: "poke".into(),
        payload: unit,
        reply: unit,
    }])
    .expect("one operation")
}

/// `term` judged in both modes: synthesised, then checked against
/// `expected`, each from an empty context that it leaves empty.
///
/// # Specification
/// trivial.
fn both(
    arena: &mut CoreArena,
    term: ComputationId,
    expected: CompTypeId,
) -> [Result<(), CheckRefusal>; 2]
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    let synthesised = synthesise_comp(&mut context, term).map(|_| ());
    assert_eq!(
        context.depth(Zone::Linear),
        gandr_core_term::BinderDepth::default(),
        "a synthesis leaves the linear zone as it found it"
    );
    let checked = form_comp_type(&mut context, expected)
        .and_then(|expected| check_comp(&mut context, term, expected).map(|_| ()));
    assert_eq!(
        context.depth(Zone::Linear),
        gandr_core_term::BinderDepth::default(),
        "a check leaves the linear zone as it found it"
    );
    [synthesised, checked]
}

/// `access c as v { body } unwind {}` in the hold `c = 0`.
///
/// # Specification
/// trivial.
fn in_view(
    arena: &mut CoreArena,
    body: ComputationId,
) -> ComputationId
{
    let unwind = done(arena);
    let accessed = access(arena, l0(), body, unwind);
    hold(arena, accessed)
}

/// A refusal of `defect` at the computation `at`.
///
/// # Specification
/// trivial.
const fn at(
    at: ComputationId,
    defect: AccessDefect,
) -> CheckRefusal
{
    CheckRefusal::Access {
        at: CoreNode::Term(TermNode::Computation(at)),
        defect,
    }
}

#[test]
fn a_counter_observes_write_back_on_resume_and_none_on_abort()
{
    let mut arena = CoreArena::new();
    // hold c = 0;
    //   access c as v { resume(v, 0) } unwind {};
    //   access c as v { abort(v) } unwind {};
    //   (c,).0
    let zero = arena.value_literal(integer_literal());
    let resumed = resume(&mut arena, l0(), zero);
    let unwind = done(&mut arena);
    let first = access(&mut arena, l0(), resumed, unwind);
    let aborted = abort(&mut arena, l0());
    let second = access(&mut arena, l0(), aborted, unwind);
    let (_held, read) = copied(&mut arena, l0());
    let rest = arena.computation_bind(second, read);
    let scope = arena.computation_bind(first, rest);
    let counter = hold(&mut arena, scope);
    let integers = integers(&mut arena);
    assert_eq!(
        both(&mut arena, counter, integers),
        [Ok(()), Ok(())],
        "two accesses lend the held value in turn and a read after them copies it"
    );
    // hold c = 0; access c as v { let x = (v,).0; resume(v, x) } unwind {}
    let (_viewed, read) = copied(&mut arena, l0());
    let copy = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let written = resume(&mut arena, l0(), copy);
    let body = arena.computation_bind(read, written);
    let direct = in_view(&mut arena, body);
    let units = units(&mut arena);
    assert_eq!(
        both(&mut arena, direct, units),
        [Ok(()), Ok(())],
        "an access checked in place reads its view and writes the read back"
    );
}

#[test]
fn an_abort_clause_performing_an_effect_is_refused()
{
    let mut arena = CoreArena::new();
    let probe = probe(&mut arena);
    let unit = arena.value_unit();
    let poked = arena.computation_perform(probe, "poke".into(), unit);
    let units = units(&mut arena);
    let aborted = abort(&mut arena, l0());
    let effectful = access(&mut arena, l0(), aborted, poked);
    let effectful = hold(&mut arena, effectful);
    assert_eq!(
        both(&mut arena, effectful, units),
        [Err(at(poked, AccessDefect::UnwindEffect)); 2],
        "an unwind runs under the empty row"
    );
    let finished = done(&mut arena);
    let then = arena.computation_bind(poked, finished);
    let bound = access(&mut arena, l0(), aborted, then);
    let bound = hold(&mut arena, bound);
    let [synthesised, checked] = both(&mut arena, bound, units);
    assert!(
        matches!(
            (synthesised, checked),
            (
                Err(CheckRefusal::Access {
                    defect: AccessDefect::UnwindEffect,
                    ..
                }),
                Err(CheckRefusal::Access {
                    defect: AccessDefect::UnwindEffect,
                    ..
                })
            )
        ),
        "an effect before the unwind's answer is refused by name: {synthesised:?} {checked:?}"
    );
    let pure = done(&mut arena);
    let quiet = access(&mut arena, l0(), aborted, pure);
    let quiet = hold(&mut arena, quiet);
    assert_eq!(
        both(&mut arena, quiet, units),
        [Ok(()), Ok(())],
        "a pure unwind checks"
    );
    let zero = arena.value_literal(integer_literal());
    let answer = arena.computation_return(zero);
    let mistyped = access(&mut arena, l0(), aborted, answer);
    let mistyped = hold(&mut arena, mistyped);
    let [synthesised, checked] = both(&mut arena, mistyped, units);
    assert!(
        !matches!(synthesised, Err(CheckRefusal::Access { .. }) | Ok(()))
            && !matches!(checked, Err(CheckRefusal::Access { .. }) | Ok(())),
        "a pure unwind answering another type is no effect: {synthesised:?} {checked:?}"
    );
}

#[test]
fn a_view_escaping_its_access_is_refused()
{
    let mut arena = CoreArena::new();
    let units = units(&mut arena);
    let zero = arena.value_literal(integer_literal());
    let resumed = resume(&mut arena, l0(), zero);
    let suspended = arena.value_thunk(resumed);
    let forced = arena.computation_force(suspended);
    let escaping = in_view(&mut arena, forced);
    assert_eq!(
        both(&mut arena, escaping, units),
        [Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Value(suspended)),
            defect: AccessDefect::Escaped { by: Capture::Thunk },
        }); 2],
        "a thunk may be forced after its access ends"
    );
    let direct = in_view(&mut arena, resumed);
    assert_eq!(
        both(&mut arena, direct, units),
        [Ok(()), Ok(())],
        "the same resume outside the thunk checks"
    );
    let (_held, read) = copied(&mut arena, l0());
    let suspended = arena.value_thunk(read);
    let forced = arena.computation_force(suspended);
    let captured = hold(&mut arena, forced);
    let integers = integers(&mut arena);
    assert_eq!(
        both(&mut arena, captured, integers),
        [Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Value(suspended)),
            defect: AccessDefect::HeldCaptured { by: Capture::Thunk },
        }); 2],
        "a thunk may be forced after its hold ends"
    );
}

#[test]
fn a_view_resumed_twice_is_refused()
{
    let mut arena = CoreArena::new();
    let units = units(&mut arena);
    let zero = arena.value_literal(integer_literal());
    let resumed = resume(&mut arena, l0(), zero);
    let again = abort(&mut arena, l0());
    let twice = arena.computation_bind(resumed, again);
    let twice = in_view(&mut arena, twice);
    assert_eq!(
        both(&mut arena, twice, units),
        [Err(at(again, AccessDefect::Spent)); 2],
        "a view ends once"
    );
    let (viewed, read) = copied(&mut arena, l0());
    let after = arena.computation_bind(resumed, read);
    let after = in_view(&mut arena, after);
    let integers = integers(&mut arena);
    assert_eq!(
        both(&mut arena, after, integers),
        [Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Value(viewed)),
            defect: AccessDefect::Spent,
        }); 2],
        "a view is not read after it ends"
    );
}

#[test]
fn a_view_left_live_is_refused()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    let (_viewed, body) = copied(&mut arena, l0());
    let unwind = done(&mut arena);
    let live = access(&mut arena, l0(), body, unwind);
    let held = hold(&mut arena, live);
    assert_eq!(
        both(&mut arena, held, integers),
        [Err(at(live, AccessDefect::Unended)); 2],
        "a body ends its view"
    );
}

#[test]
fn a_held_value_lent_or_misnamed_is_refused()
{
    let mut arena = CoreArena::new();
    let units = units(&mut arena);
    let integers = integers(&mut arena);
    let zero = arena.value_literal(integer_literal());
    let unwind = done(&mut arena);
    // access c as v { access c as w { … } }: c is lent to v.
    let inner_body = resume(&mut arena, l0(), zero);
    let inner = access(&mut arena, l1(), inner_body, unwind);
    let nested = in_view(&mut arena, inner);
    assert_eq!(
        both(&mut arena, nested, units),
        [Err(at(inner, AccessDefect::Lent)); 2],
        "a held value lends once"
    );
    // access c as v { let _ = (c,).0; … }
    let (held, read) = copied(&mut arena, l1());
    let resumed = resume(&mut arena, l0(), zero);
    let reading = arena.computation_bind(read, resumed);
    let reading = in_view(&mut arena, reading);
    assert_eq!(
        both(&mut arena, reading, units),
        [Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Value(held)),
            defect: AccessDefect::Lent,
        }); 2],
        "a lent value is read through its view"
    );
    // access c as v { access v as w { … } }
    let of_view = access(&mut arena, l0(), inner_body, unwind);
    let viewing = in_view(&mut arena, of_view);
    assert_eq!(
        both(&mut arena, viewing, units),
        [Err(at(of_view, AccessDefect::NotHeld)); 2],
        "a view holds nothing"
    );
    // hold c = 0; resume(c, 0)
    let misnamed = resume(&mut arena, l0(), zero);
    let misnamed_hold = hold(&mut arena, misnamed);
    assert_eq!(
        both(&mut arena, misnamed_hold, units),
        [Err(at(misnamed, AccessDefect::NotAView)); 2],
        "a held value is no view"
    );
    // hold c = 0; (c,).0, checked under the row `Probe`
    let probe = probe(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let effectful = arena.comp_type_returner_with_effects(integer, EffectRow::singleton(probe));
    let (_held, read) = copied(&mut arena, l0());
    let read_hold = hold(&mut arena, read);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_comp_type(&mut context, effectful).expect("an effectful returner");
    assert_eq!(
        check_comp(&mut context, read_hold, expected).map(|_| ()),
        Err(at(read_hold, AccessDefect::HeldCaptured {
            by: Capture::Continuation
        })),
        "an operation in a hold's scope could be resumed twice"
    );
    assert_eq!(
        both(&mut arena, read_hold, integers),
        [Ok(()), Ok(())],
        "the same hold at the pure returner checks"
    );
}
