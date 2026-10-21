use alloc::sync::Arc;

use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::control::EffectClause;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionDepth;
use gandr_core_term::effect::host::HostSignatures;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
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
    arena.computation_memory(MemoryForm::Hold {
        value,
        body,
        grade: HoldGrade::Many,
    })
}

/// `hold[1] x = 0; body`.
///
/// # Specification
/// trivial.
fn hold_one(
    arena: &mut CoreArena,
    body: ComputationId,
) -> ComputationId
{
    let value = arena.value_literal(integer_literal());
    arena.computation_memory(MemoryForm::Hold {
        value,
        body,
        grade: HoldGrade::One,
    })
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
    arena.computation_memory(MemoryForm::Access {
        mode: AccessMode::Exclusive { unwind },
        held,
        place: Place::Whole,
        body,
    })
}

/// `access shared lN as v { body }`.
///
/// # Specification
/// trivial.
fn shared(
    arena: &mut CoreArena,
    held: DeBruijnIndex,
    body: ComputationId,
) -> ComputationId
{
    arena.computation_memory(MemoryForm::Access {
        mode: AccessMode::Shared,
        held,
        place: Place::Whole,
        body,
    })
}

/// `x <- (return [0] : F (List Integer)); hold xs = x; body`: a list value
/// only checks, so it is ascribed before it is held.
///
/// # Specification
/// trivial.
fn listed(
    arena: &mut CoreArena,
    body: ComputationId,
) -> ComputationId
{
    let zero = arena.value_literal(integer_literal());
    let nil = arena.value_list_nil();
    let cons = arena.value_list_cons(zero, nil);
    let returned = arena.computation_return(cons);
    let integer = arena.value_type_base(BaseType::Integer);
    let list = arena.value_type_list(integer);
    let lists = arena.comp_type_returner(list);
    let ascribed = arena.computation_ascribe(returned, lists);
    let value = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let held = arena.computation_memory(MemoryForm::Hold {
        value,
        body,
        grade: HoldGrade::Many,
    });
    arena.computation_bind(ascribed, held)
}

/// `access lN[index] as v { body } unwind { unwind }`.
///
/// # Specification
/// trivial.
fn access_at(
    arena: &mut CoreArena,
    held: DeBruijnIndex,
    index: ValueId,
    body: ComputationId,
    unwind: ComputationId,
) -> ComputationId
{
    arena.computation_memory(MemoryForm::Access {
        mode: AccessMode::Exclusive { unwind },
        held,
        place: Place::At { index },
        body,
    })
}

/// `access shared lN[index] as v { body }`.
///
/// # Specification
/// trivial.
fn shared_at(
    arena: &mut CoreArena,
    held: DeBruijnIndex,
    index: ValueId,
    body: ComputationId,
) -> ComputationId
{
    arena.computation_memory(MemoryForm::Access {
        mode: AccessMode::Shared,
        held,
        place: Place::At { index },
        body,
    })
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

/// `hold[1] c = 0; access c as v { body } unwind {}`.
///
/// # Specification
/// trivial.
fn in_unique_view(
    arena: &mut CoreArena,
    body: ComputationId,
) -> ComputationId
{
    let unwind = done(arena);
    let accessed = access(arena, l0(), body, unwind);
    hold_one(arena, accessed)
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

/// An unwind runs to completion under the empty row, which carries no
/// abandonment: an `abandon` written in one is refused at the abandonment,
/// before the stack it names is read (#1334).
#[test]
fn an_unwind_abandons_nothing_1334()
{
    let mut arena = CoreArena::new();
    let units = units(&mut arena);
    let unit = arena.value_unit();
    let abandoned = arena.computation_abandon(unit);
    let aborted = abort(&mut arena, l0());
    let unwinding = access(&mut arena, l0(), aborted, abandoned);
    let unwinding = hold(&mut arena, unwinding);
    assert_eq!(
        both(&mut arena, unwinding, units),
        [Err(at(abandoned, AccessDefect::UnwindEffect)); 2],
        "no cancellation reaches inside a running unwind"
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
    // hold c = 0; poke(); (c,).0, checked under the row `Probe`: the clause
    // answering `poke` receives the rest of the hold, its end with it.
    let probe = probe(&mut arena);
    let unit = arena.value_unit();
    let poked = arena.computation_perform(probe.clone(), "poke".into(), unit);
    let (_held, read) = copied(&mut arena, l0());
    let then = arena.computation_bind(poked, read);
    let performing = hold(&mut arena, then);
    let integer = arena.value_type_base(BaseType::Integer);
    let effectful = arena.comp_type_returner_with_effects(integer, EffectRow::singleton(probe));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_comp_type(&mut context, effectful).expect("an effectful returner");
    assert_eq!(
        check_comp(&mut context, performing, expected).map(|_| ()),
        Err(at(poked, AccessDefect::HeldCaptured {
            by: Capture::Continuation
        })),
        "an operation in a hold's scope could be resumed twice"
    );
    // hold c = 0; (c,).0, checked under the row `Probe`
    let (_held, read) = copied(&mut arena, l0());
    let read_hold = hold(&mut arena, read);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_comp_type(&mut context, effectful).expect("an effectful returner");
    assert_eq!(
        check_comp(&mut context, read_hold, expected).map(|_| ()),
        Ok(()),
        "a hold performing nothing checks under any row"
    );
    assert_eq!(
        both(&mut arena, read_hold, integers),
        [Ok(()), Ok(())],
        "the same hold at the pure returner checks"
    );
}

#[test]
fn a_shared_view_reads_beside_its_held_value_and_ends_with_its_body()
{
    let mut arena = CoreArena::new();
    let units = units(&mut arena);
    let integers = integers(&mut arena);
    let zero = arena.value_literal(integer_literal());
    let unwind = done(&mut arena);
    // hold c = 0; access shared c as v { access shared c as w { (c,).0; (v,).0;
    // (w,).0 } }
    let (_held, held_read) = copied(&mut arena, DeBruijnIndex::from(2_u32));
    let (_outer, outer_read) = copied(&mut arena, l1());
    let (_inner, inner_read) = copied(&mut arena, l0());
    let views = arena.computation_bind(outer_read, inner_read);
    let reads = arena.computation_bind(held_read, views);
    let inner = shared(&mut arena, l1(), reads);
    let outer = shared(&mut arena, l0(), inner);
    let nested = hold(&mut arena, outer);
    assert_eq!(
        both(&mut arena, nested, integers),
        [Ok(()), Ok(())],
        "two shared views of one held value nest, and the value stays readable"
    );
    // hold c = 0; access shared c as v { (v,).0 }; access c as w { resume(w, 0) }
    // unwind {}; (c,).0
    let (_viewed, viewed) = copied(&mut arena, l0());
    let first = shared(&mut arena, l0(), viewed);
    let resumed = resume(&mut arena, l0(), zero);
    let second = access(&mut arena, l0(), resumed, unwind);
    let (_held, read) = copied(&mut arena, l0());
    let rest = arena.computation_bind(second, read);
    let scope = arena.computation_bind(first, rest);
    let in_turn = hold(&mut arena, scope);
    assert_eq!(
        both(&mut arena, in_turn, integers),
        [Ok(()), Ok(())],
        "a shared access ends with its body, so an exclusive one follows it"
    );
    // hold c = 0; access shared c as v { access c as w { resume(w, 0) } unwind {} }
    let exclusive = access(&mut arena, l1(), resumed, unwind);
    let frozen = shared(&mut arena, l0(), exclusive);
    let frozen = hold(&mut arena, frozen);
    assert_eq!(
        both(&mut arena, frozen, units),
        [Err(at(exclusive, AccessDefect::Lent)); 2],
        "a value lent shared is frozen for the shared access's extent"
    );
    // access c as v { access shared c as w { (w,).0 }; resume(v, 0) } unwind {}
    let (_inner, inner_read) = copied(&mut arena, l0());
    let inside = shared(&mut arena, l1(), inner_read);
    let written = resume(&mut arena, l0(), zero);
    let body = arena.computation_bind(inside, written);
    let beside = in_view(&mut arena, body);
    assert_eq!(
        both(&mut arena, beside, units),
        [Err(at(inside, AccessDefect::Lent)); 2],
        "nothing is lent beside an exclusive access"
    );
    // hold c = 0; access shared c as v { resume(v, 0) }, and the same with abort(v)
    let aborted = abort(&mut arena, l0());
    for eliminator in [resumed, aborted] {
        let read_only = shared(&mut arena, l0(), eliminator);
        let read_only = hold(&mut arena, read_only);
        assert_eq!(
            both(&mut arena, read_only, units),
            [Err(at(eliminator, AccessDefect::ReadOnly)); 2],
            "a shared view is read-only and ends with its body"
        );
    }
}

#[test]
fn a_value_held_at_grade_one_is_never_copied()
{
    let mut arena = CoreArena::new();
    let units = units(&mut arena);
    let integers = integers(&mut arena);
    let zero = arena.value_literal(integer_literal());
    let x = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    // hold[1] c = 0; access c as v { let x = (v,).0; resume(v, x) } unwind {}
    let (_moved, read) = copied(&mut arena, l0());
    let written = resume(&mut arena, l0(), x);
    let body = arena.computation_bind(read, written);
    let moved = in_unique_view(&mut arena, body);
    assert_eq!(
        both(&mut arena, moved, units),
        [Ok(()), Ok(())],
        "the exclusive view reads the value out once and writes it back"
    );
    // hold[1] c = 0; access c as v { abort(v) } unwind {}
    let aborted = abort(&mut arena, l0());
    let untouched = in_unique_view(&mut arena, aborted);
    assert_eq!(
        both(&mut arena, untouched, units),
        [Ok(()), Ok(())],
        "an abort before any read leaves the held value where it was"
    );
    // access c as v { let x = (v,).0; let y = (v,).0; resume(v, x) }
    let (_first, first) = copied(&mut arena, l0());
    let (second, again) = copied(&mut arena, l0());
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let written = resume(&mut arena, l0(), outer);
    let rest = arena.computation_bind(again, written);
    let body = arena.computation_bind(first, rest);
    let twice = in_unique_view(&mut arena, body);
    assert_eq!(
        both(&mut arena, twice, units),
        [Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Value(second)),
            defect: AccessDefect::HeldCopied,
        }); 2],
        "a second read of the view copies the value"
    );
    // hold[1] c = 0; (c,).0
    let (held, read) = copied(&mut arena, l0());
    let direct = hold_one(&mut arena, read);
    assert_eq!(
        both(&mut arena, direct, integers),
        [Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Value(held)),
            defect: AccessDefect::HeldCopied,
        }); 2],
        "a read of the held slot copies the value"
    );
    // hold[1] c = 0; access shared c as v { (v,).0 }
    let (viewed, read) = copied(&mut arena, l0());
    let lent = shared(&mut arena, l0(), read);
    let frozen = hold_one(&mut arena, lent);
    assert_eq!(
        both(&mut arena, frozen, integers),
        [Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Value(viewed)),
            defect: AccessDefect::HeldCopied,
        }); 2],
        "a read of a shared view copies the value"
    );
    // access c as v { let x = (v,).0; abort(v) }
    let (_moved, read) = copied(&mut arena, l0());
    let late = abort(&mut arena, l0());
    let body = arena.computation_bind(read, late);
    let lost = in_unique_view(&mut arena, body);
    assert_eq!(
        both(&mut arena, lost, units),
        [Err(at(late, AccessDefect::Moved)); 2],
        "an abort after the read would keep a value the read took"
    );
    // access c as v { (v,).0 } unwind {}
    let (_moved, read) = copied(&mut arena, l0());
    let unwind = done(&mut arena);
    let kept = access(&mut arena, l0(), read, unwind);
    let unended = hold_one(&mut arena, kept);
    assert_eq!(
        both(&mut arena, unended, integers),
        [Err(at(kept, AccessDefect::Unended)); 2],
        "a body that moves the value out writes one back"
    );
    // x <- (return 0 : F Integer); hold[1] c = x; return ()
    let returned = arena.computation_return(zero);
    let returned = arena.computation_ascribe(returned, integers);
    let empty = done(&mut arena);
    let entered = arena.computation_memory(MemoryForm::Hold {
        value: x,
        body: empty,
        grade: HoldGrade::One,
    });
    let bound = arena.computation_bind(returned, entered);
    assert_eq!(
        both(&mut arena, bound, units),
        [Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Value(x)),
            defect: AccessDefect::HeldShared,
        }); 2],
        "a value a computation returned may have another holder"
    );
}

#[test]
fn a_place_of_a_held_list_is_lent_at_its_index()
{
    let mut arena = CoreArena::new();
    let units = units(&mut arena);
    let integers = integers(&mut arena);
    let zero = arena.value_literal(integer_literal());
    let unwind = done(&mut arena);
    // hold xs = [0]; access xs[0] as v { let x = (v,).0; resume(v, x) } unwind {}
    let (_viewed, read) = copied(&mut arena, l0());
    let copy = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let written = resume(&mut arena, l0(), copy);
    let body = arena.computation_bind(read, written);
    let exclusive = access_at(&mut arena, l0(), zero, body, unwind);
    let exclusive = listed(&mut arena, exclusive);
    assert_eq!(
        both(&mut arena, exclusive, units),
        [Ok(()), Ok(())],
        "an exclusive view of a held list's element reads it and writes an element back"
    );
    // hold xs = [0]; access shared xs[0] as v { (v,).0 }
    let (_viewed, viewed) = copied(&mut arena, l0());
    let element = shared_at(&mut arena, l0(), zero, viewed);
    let element = listed(&mut arena, element);
    assert_eq!(
        both(&mut arena, element, integers),
        [Ok(()), Ok(())],
        "a shared view of a held list's element reads it at the element type"
    );
    // hold c = 0; access shared c[0] as v { (v,).0 }
    let unindexed = shared_at(&mut arena, l0(), zero, viewed);
    let unindexed_hold = hold(&mut arena, unindexed);
    assert_eq!(
        both(&mut arena, unindexed_hold, integers),
        [Err(at(unindexed, AccessDefect::Unindexed)); 2],
        "a held integer has no element at an index"
    );
    // hold i = 0; hold xs = [0]; access shared xs[i] as v { (i,).0 }; (i,).0
    let index = arena.value_variable(Zone::Linear, l1());
    let (_index, index_read) = copied(&mut arena, DeBruijnIndex::from(2_u32));
    let reading = shared_at(&mut arena, l0(), index, index_read);
    let (_after, after) = copied(&mut arena, l1());
    let scope = arena.computation_bind(reading, after);
    let scope = listed(&mut arena, scope);
    let indexed = hold(&mut arena, scope);
    assert_eq!(
        both(&mut arena, indexed, integers),
        [Ok(()), Ok(())],
        "a held index reads beside its lend and again once the access ends"
    );
    // hold i = 0; hold xs = [0];
    //   access shared xs[i] as v { access i as w { resume(w, 0) } unwind {} }
    let resumed = resume(&mut arena, l0(), zero);
    let inner = access(&mut arena, DeBruijnIndex::from(2_u32), resumed, unwind);
    let frozen = shared_at(&mut arena, l0(), index, inner);
    let frozen = listed(&mut arena, frozen);
    let frozen = hold(&mut arena, frozen);
    assert_eq!(
        both(&mut arena, frozen, units),
        [Err(at(inner, AccessDefect::Lent)); 2],
        "an index is lent shared with its place, so it is frozen for the access"
    );
}

/// `term` checked against `expected` from an empty context that it leaves
/// empty.
///
/// # Specification
/// trivial.
fn checked(
    arena: &mut CoreArena,
    term: ComputationId,
    expected: CompTypeId,
) -> Result<(), CheckRefusal>
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    let checked = form_comp_type(&mut context, expected)
        .and_then(|expected| check_comp(&mut context, term, expected).map(|_| ()));
    assert_eq!(
        context.depth(Zone::Linear),
        gandr_core_term::BinderDepth::default(),
        "a check leaves the linear zone as it found it"
    );
    checked
}

#[test]
fn a_view_kept_in_a_region_lives_as_long_as_its_scope()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let units = units(&mut arena);
    let integers = integers(&mut arena);
    let suspended = arena.value_type_thunk(integers);
    // The hold around the scope opens the first region and the scope the
    // second: one sort of regions, counted outermost first.
    let kept = arena.value_type_kept(suspended, Region::Scoped(RegionDepth::from(2_u32)));
    let keeps = arena.comp_type_returner(kept);
    let suspends = arena.comp_type_returner(suspended);
    let zero = arena.value_literal(integer_literal());
    let returned = done(&mut arena);
    let answered = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let passes = arena.computation_return(answered);
    let unwind = done(&mut arena);
    let scope = |arena: &mut CoreArena, subject| {
        let clauses: Arc<[EffectClause]> = [EffectClause {
            operation: "exit".into(),
            body: returned,
        }]
        .into();
        arena.computation_scope(host.proc.clone(), subject, passes, clauses)
    };
    // x <- (return thunk { (w,).0 } : F (U F Integer at ρ)), with `w` the view
    // and ρ the scope's region.
    let (_viewed, read) = copied(&mut arena, l0());
    let thunk = arena.value_thunk(read);
    let suspend = arena.computation_return(thunk);
    let kept_bind = arena.computation_ascribe(suspend, keeps);
    let plain_bind = arena.computation_ascribe(suspend, suspends);
    // hold s = 0; scope Proc (c) { access shared s as w { x <- …; force x };
    // body } with { return(r) => r; exit(_, _) => () }
    let forced = arena.computation_force(answered);
    let kept_body = arena.computation_bind(kept_bind, forced);
    let kept_access = shared(&mut arena, l0(), kept_body);
    let in_region = |arena: &mut CoreArena, access, after| {
        let subject = arena.computation_bind(access, after);
        let scoped = scope(arena, subject);
        (scoped, hold(arena, scoped))
    };
    let resumed = resume(&mut arena, l0(), zero);
    let exclusive = access(&mut arena, l0(), resumed, unwind);
    let (released_scope, _) = in_region(&mut arena, kept_access, returned);
    let ascribed = arena.computation_ascribe(released_scope, units);
    let released = arena.computation_bind(ascribed, exclusive);
    let released = hold(&mut arena, released);
    assert_eq!(
        checked(&mut arena, released, units),
        Ok(()),
        "a thunk kept in the scope's region keeps the shared view, forces as \
         the thunk it keeps, and the held value is lent exclusively once the \
         scope ends"
    );
    let frozen_after = access(&mut arena, l0(), resumed, unwind);
    let (_, frozen) = in_region(&mut arena, kept_access, frozen_after);
    assert_eq!(
        checked(&mut arena, frozen, units),
        Err(at(frozen_after, AccessDefect::Kept)),
        "a slot a live region keeps a view of is frozen against an exclusive access"
    );
    let plain_body = arena.computation_bind(plain_bind, forced);
    let plain_access = shared(&mut arena, l0(), plain_body);
    let (_, escaping) = in_region(&mut arena, plain_access, returned);
    assert_eq!(
        checked(&mut arena, escaping, units),
        Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Value(thunk)),
            defect: AccessDefect::Escaped { by: Capture::Thunk },
        }),
        "a thunk kept in no region captures no view"
    );
    // scope Proc (c) { () } checked at F (U F Integer at ρ), ρ its own region,
    // the first with no hold around it.
    let answering_scope = scope(&mut arena, returned);
    let own = arena.value_type_kept(suspended, Region::Scoped(RegionDepth::from(1_u32)));
    let own_keeps = arena.comp_type_returner(own);
    assert_eq!(
        checked(&mut arena, answering_scope, own_keeps),
        Err(at(answering_scope, AccessDefect::KeptEscaped)),
        "a scope answers nothing kept in its own region"
    );
    // x <- …; z <- (return thunk { force x } : F (U F Integer [at ρ])); force z
    let outer_force = arena.computation_force(answered);
    let wrapper = arena.value_thunk(outer_force);
    let rewrapped = arena.computation_return(wrapper);
    for (wrapped, outcome) in [
        (
            suspends,
            Err(CheckRefusal::Access {
                at: CoreNode::Term(TermNode::Value(wrapper)),
                defect: AccessDefect::KeptEscaped,
            }),
        ),
        (keeps, Ok(())),
    ] {
        let wrapping = arena.computation_ascribe(rewrapped, wrapped);
        let rest = arena.computation_bind(wrapping, outer_force);
        let body = arena.computation_bind(kept_bind, rest);
        let accessed = shared(&mut arena, l0(), body);
        let (_, program) = in_region(&mut arena, accessed, returned);
        assert_eq!(
            checked(&mut arena, program, units),
            outcome,
            "a thunk names a variable kept in a region only at a type kept there"
        );
    }
    // x <- …; y <- (return x : F (U F Integer at ρ)); force y: a value kept in
    // a region is bound again at the type that keeps it.
    let again = arena.computation_return(answered);
    let again = arena.computation_ascribe(again, keeps);
    let rest = arena.computation_bind(again, forced);
    let body = arena.computation_bind(kept_bind, rest);
    let accessed = shared(&mut arena, l0(), body);
    let (_, program) = in_region(&mut arena, accessed, returned);
    assert_eq!(
        checked(&mut arena, program, units),
        Ok(()),
        "a value kept in a region stays kept at the type that keeps it"
    );
    // scope Proc (c) { y <- (return thunk { hold s = 0; access shared s as w {
    // x <- …; force x } } : F (U F Integer)); () }, x kept in the scope's region,
    // the first: a hold stands in a scope only where its type is pure, inside a
    // thunk.
    let scope_kept = arena.value_type_kept(suspended, Region::Scoped(RegionDepth::from(1_u32)));
    let scope_keeps = arena.comp_type_returner(scope_kept);
    let scope_bind = arena.computation_ascribe(suspend, scope_keeps);
    let inner_body = arena.computation_bind(scope_bind, forced);
    let inner_access = shared(&mut arena, l0(), inner_body);
    let inner_hold = hold(&mut arena, inner_access);
    let holding = arena.value_thunk(inner_hold);
    let suspended_hold = arena.computation_return(holding);
    let ascribed_hold = arena.computation_ascribe(suspended_hold, suspends);
    let inner_subject = arena.computation_bind(ascribed_hold, returned);
    let held_inside = scope(&mut arena, inner_subject);
    assert_eq!(
        checked(&mut arena, held_inside, units),
        Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Value(thunk)),
            defect: AccessDefect::Escaped { by: Capture::Thunk },
        }),
        "a value held inside the scope does not outlive its region, so no view \
         of it is kept there"
    );
}

#[test]
fn a_view_kept_in_a_hold_lives_as_long_as_the_hold()
{
    let mut arena = CoreArena::new();
    let units = units(&mut arena);
    let integers = integers(&mut arena);
    let suspended = arena.value_type_thunk(integers);
    let zero = arena.value_literal(integer_literal());
    let returned = done(&mut arena);
    let unwind = done(&mut arena);
    let answered = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(answered);
    // x <- (return thunk { (w,).0 } : F (U F Integer at ρ)); force x, with `w`
    // the view and ρ the region at `depth`.
    let kept_force = |arena: &mut CoreArena, depth: u32| {
        let kept = arena.value_type_kept(suspended, Region::Scoped(RegionDepth::from(depth)));
        let keeps = arena.comp_type_returner(kept);
        let (_viewed, read) = copied(arena, l0());
        let thunk = arena.value_thunk(read);
        let suspend = arena.computation_return(thunk);
        let bound = arena.computation_ascribe(suspend, keeps);
        (arena.computation_bind(bound, forced), keeps)
    };
    // hold s = 0; access shared s as w { x : … at s <- …; force x }; ()
    let (own, own_keeps) = kept_force(&mut arena, 1_u32);
    let own_access = shared(&mut arena, l0(), own);
    let own_then = arena.computation_bind(own_access, returned);
    let own_hold = hold(&mut arena, own_then);
    assert_eq!(
        checked(&mut arena, own_hold, units),
        Ok(()),
        "a view of a held value is kept in its own hold's region"
    );
    // … ; access s as v { resume(v, 0) }: the hold's region keeps the view.
    let resumed = resume(&mut arena, l0(), zero);
    let exclusive = access(&mut arena, l0(), resumed, unwind);
    let frozen_then = arena.computation_bind(own_access, exclusive);
    let frozen = hold(&mut arena, frozen_then);
    assert_eq!(
        checked(&mut arena, frozen, units),
        Err(at(exclusive, AccessDefect::Kept)),
        "a held value is frozen while its own hold's region keeps a view"
    );
    // hold s = 0; access shared s as w { x : … at s <- …; force x }, answered.
    let answering = hold(&mut arena, own_access);
    assert_eq!(
        checked(&mut arena, answering, own_keeps),
        Err(at(answering, AccessDefect::KeptEscaped)),
        "a hold answers nothing kept in its own region"
    );
    // hold s = 0; (hold r = 0; access shared s as w { x : … at r <- …; force
    // x }; ()); access s as v { resume(v, 0) }: a view of the outer hold kept
    // in the inner one's region, released when the inner hold ends.
    let (inner, _inner_keeps) = kept_force(&mut arena, 2_u32);
    let inner_access = shared(&mut arena, l1(), inner);
    let inner_then = arena.computation_bind(inner_access, returned);
    let inner_hold = hold(&mut arena, inner_then);
    let inner_ascribed = arena.computation_ascribe(inner_hold, units);
    let released_then = arena.computation_bind(inner_ascribed, exclusive);
    let released = hold(&mut arena, released_then);
    assert_eq!(
        checked(&mut arena, released, units),
        Ok(()),
        "a view kept in an inner hold's region frees the outer held value when \
         the inner hold ends"
    );
}

/// A definition over a region binder holds nothing and opens no scope, yet a
/// thunk it builds may not outlive the binder's region: the fence runs for
/// the abstracted type alone (#1221).
#[test]
fn a_thunk_naming_a_value_kept_at_a_region_binder_is_kept_there_1221()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    let suspended = arena.value_type_thunk(integers);
    let bound = Region::Bound(gandr_core_term::effect::capability::RegionBinder::from(
        0_u32,
    ));
    let lent = arena.value_type_kept(suspended, bound);
    let lent_back = arena.comp_type_returner(lent);
    let unkept = arena.comp_type_returner(suspended);
    let [reads, hands_back, stashes] =
        [integers, lent_back, unkept].map(|codomain| arena.comp_type_arrow(lent, codomain));
    let k = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    // λk. force k : (U F Integer at r) -> F Integer
    let forced = arena.computation_force(k);
    let read = arena.computation_lambda(forced);
    // λk. return k : (U F Integer at r) -> F (U F Integer at r)
    let returned = arena.computation_return(k);
    let handed_back = arena.computation_lambda(returned);
    // λk. return thunk { force k } : (U F Integer at r) -> F (U F Integer)
    let wrapper = arena.value_thunk(forced);
    let wrapped = arena.computation_return(wrapper);
    let stash = arena.computation_lambda(wrapped);
    assert_eq!(
        [(read, reads), (handed_back, hands_back), (stash, stashes)]
            .map(|(term, expected)| checked(&mut arena, term, expected)),
        [
            Ok(()),
            Ok(()),
            Err(CheckRefusal::Access {
                at: CoreNode::Term(TermNode::Value(wrapper)),
                defect: AccessDefect::KeptEscaped,
            })
        ],
        "a lent value is read and handed back at its region, and a thunk naming it \
         kept in no region is refused"
    );
}

/// `consume(lN)`.
///
/// # Specification
/// trivial.
fn consume(
    arena: &mut CoreArena,
    held: DeBruijnIndex,
) -> ComputationId
{
    arena.computation_memory(MemoryForm::Consume { held })
}

#[test]
fn a_consume_ends_its_hold_and_answers_the_held_value()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    // hold c = 0; consume(c)
    let taken = consume(&mut arena, l0());
    let ended = hold(&mut arena, taken);
    assert_eq!(
        both(&mut arena, ended, integers),
        [Ok(()), Ok(())],
        "a consume answers the held value at the slot's type"
    );
    // hold[1] c = 0; consume(c): the one holder hands the value on.
    let taken = consume(&mut arena, l0());
    let unique = hold_one(&mut arena, taken);
    assert_eq!(
        both(&mut arena, unique, integers),
        [Ok(()), Ok(())],
        "a consume moves a value held at grade one without copying it"
    );
    // hold c = 0; x <- consume(c); return x
    let taken = consume(&mut arena, l0());
    let x = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(x);
    let bound = arena.computation_bind(taken, returned);
    let rest = hold(&mut arena, bound);
    assert_eq!(
        both(&mut arena, rest, integers),
        [Ok(()), Ok(())],
        "the rest of the hold runs with the slot spent"
    );
}

#[test]
fn a_consumed_hold_is_read_lent_or_consumed_no_more()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    // hold c = 0; _ <- consume(c); (c,).0
    let taken = consume(&mut arena, l0());
    let (read, reading) = copied(&mut arena, l0());
    let bound = arena.computation_bind(taken, reading);
    let reread = hold(&mut arena, bound);
    assert_eq!(
        both(&mut arena, reread, integers),
        [Err(CheckRefusal::Access {
            at: CoreNode::Term(TermNode::Value(read)),
            defect: AccessDefect::Consumed,
        }); 2],
        "a read after the consume finds the value gone"
    );
    // hold c = 0; _ <- consume(c); consume(c)
    let taken = consume(&mut arena, l0());
    let again = consume(&mut arena, l0());
    let bound = arena.computation_bind(taken, again);
    let twice = hold(&mut arena, bound);
    assert_eq!(
        both(&mut arena, twice, integers),
        [Err(at(again, AccessDefect::Consumed)); 2],
        "a second consume finds the value gone"
    );
    // hold c = 0; _ <- consume(c); access shared c as v { (v,).0 }
    let taken = consume(&mut arena, l0());
    let (_viewed, viewing) = copied(&mut arena, l0());
    let lent = shared(&mut arena, l0(), viewing);
    let bound = arena.computation_bind(taken, lent);
    let relent = hold(&mut arena, bound);
    assert_eq!(
        both(&mut arena, relent, integers),
        [Err(at(lent, AccessDefect::Consumed)); 2],
        "an access after the consume finds the value gone"
    );
    // hold c = 0; access shared c as v { consume(c) }
    let inner = consume(&mut arena, l1());
    let lent = shared(&mut arena, l0(), inner);
    let frozen = hold(&mut arena, lent);
    assert_eq!(
        both(&mut arena, frozen, integers),
        [Err(at(inner, AccessDefect::Lent)); 2],
        "a value lent shared is frozen, so nothing takes it"
    );
}

#[test]
fn a_branch_reads_a_hold_but_consumes_none()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let list = arena.value_type_list(integer);
    let lists = arena.comp_type_returner(list);
    let branched = |arena: &mut CoreArena, on_nil, on_cons| {
        // hold c = 0; xs <- (return [0] : F (List Integer)); case xs { … }
        let zero = arena.value_literal(integer_literal());
        let nil = arena.value_list_nil();
        let cons = arena.value_list_cons(zero, nil);
        let returned = arena.computation_return(cons);
        let ascribed = arena.computation_ascribe(returned, lists);
        let xs = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_list_case(xs, on_nil, on_cons);
        let bound = arena.computation_bind(ascribed, case);
        (case, hold(arena, bound))
    };
    let (_read, on_nil) = copied(&mut arena, l0());
    let (_read, on_cons) = copied(&mut arena, l0());
    let (_case, reads) = branched(&mut arena, on_nil, on_cons);
    // A case on a list only checks.
    assert_eq!(
        checked(&mut arena, reads, integers),
        Ok(()),
        "each branch reads the held value by copy"
    );
    let on_nil = consume(&mut arena, l0());
    let on_cons = consume(&mut arena, l0());
    let (case, consumes) = branched(&mut arena, on_nil, on_cons);
    assert_eq!(
        checked(&mut arena, consumes, integers),
        Err(at(case, AccessDefect::HeldCaptured {
            by: Capture::Branch
        })),
        "a branch would end the hold on its own paths alone"
    );
}
