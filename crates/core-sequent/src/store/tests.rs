use alloc::string::String;

use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;

use super::*;

/// The decimal digits a test literal is spelled with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Digits(&'static str);

/// The non-negative integer value spelled by `digits`.
///
/// # Specification
/// - requires: digits is a nonempty unsigned decimal spelling.
/// - ensures: that nonnegative integer as a literal heap value, with leading
///   zeroes removed except for zero itself.
/// - provides: numeric fixture values independent of their heap address.
/// - panics: on a malformed decimal spelling.
///
/// # Adequacy
/// - hypothesis: L3 — valid decimal fixtures used by heap identity and
///   shared-cache scenarios have their canonical payload checked under
///   enforcement. These distinguish the wrong literal kind, sign or value;
///   malformed spellings are outside the fixture domain.
/// - witness: `store::tests::cell_write_back_is_shared_and_nominal`
/// - witness: `store::tests::heap_reads_preserve_identity_at_the_end`
#[spec(
        requires: !digits.0.is_empty() && digits.0.bytes().all(|byte| byte.is_ascii_digit()),
        ensures: |ref ret| match *ret {
            | HeapValue::Literal(Literal::Integer(ref integer)) => {
                let significant = digits.0.trim_start_matches('0');
                let expected = if significant.is_empty() { "0" } else { significant };
                let actual: &str = integer.magnitude().as_ref();
                integer.sign() == Sign::NonNegative && actual == expected
            },
            | _ => false,
        },
    )]
fn integer(digits: Digits) -> HeapValue
{
    HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits"),
    )))
}

/// A write-back through one address is what every holder of that address
/// reads, and a second cell — even one a thunk of equal content would own
/// — is untouched: identity is the address, not the content.
#[test]
fn cell_write_back_is_shared_and_nominal()
{
    let mut store = Store::new();
    let shared = store.allocate_cell().expect("room");
    let other = store.allocate_cell().expect("room");
    assert_ne!(shared, other, "two allocations are two cells");
    let alias = shared;

    assert_eq!(
        Ok(ForceEntry::Opened),
        store.begin_force(shared),
        "an unforced cell opens"
    );
    assert_eq!(
        Ok(ForceEntry::Reentrant),
        store.begin_force(alias),
        "the alias sees the black hole"
    );
    let value = store.allocate(integer(Digits("9"))).expect("room");
    assert_eq!(
        Ok(()),
        store.write_back(shared, value),
        "the opener writes back"
    );

    assert_eq!(
        Ok(ForceEntry::Cached(value)),
        store.begin_force(alias),
        "the alias reads the exact value written"
    );
    assert_eq!(
        Some(MemoState::Unforced),
        store.cell(other),
        "the other cell is untouched"
    );
    assert_eq!(
        Err(StoreFault::CellNotInProgress {
            cell: shared,
            found: MemoState::Forced(value),
        }),
        store.write_back(shared, value),
        "a forced cell takes no second write-back"
    );
    assert_eq!(
        Err(StoreFault::CellNotInProgress {
            cell: other,
            found: MemoState::Unforced,
        }),
        store.decline(other),
        "an unforced cell cannot be declined"
    );
}

/// A covariable's mark shrinks the region to its height and declines the
/// update frames it drops; a mark over a popped and re-pushed height is
/// stale.
#[test]
fn frames_shrink_to_a_mark()
{
    let mut store = Store::new();
    let cell = store.allocate_cell().expect("room");
    store
        .push_frame(Frame::Destructor {
            tag: DestructorTag::Force,
            arguments: crate::store::ObservationArguments::Nullary,
        })
        .expect("room");
    let mark = store.mark();
    assert_eq!(
        Ok(ForceEntry::Opened),
        store.begin_force(cell),
        "the cell opens"
    );
    store.push_frame(Frame::Update { cell }).expect("room");
    store
        .push_frame(Frame::Destructor {
            tag: DestructorTag::Force,
            arguments: crate::store::ObservationArguments::Nullary,
        })
        .expect("room");
    assert_eq!(
        FrameHeight::from(3_usize),
        store.frame_height(),
        "three frames"
    );

    assert_eq!(Ok(()), store.shrink_to(mark), "a live mark shrinks");
    assert_eq!(
        FrameHeight::from(1_usize),
        store.frame_height(),
        "back at the mark"
    );
    assert_eq!(
        FrameHeight::from(3_usize),
        store.peak_height(),
        "the peak keeps the highest the region stood"
    );
    assert_eq!(
        Some(MemoState::Unforced),
        store.cell(cell),
        "the dropped update declined its cell"
    );

    let popped = store.pop_frame();
    assert!(popped.is_some(), "the marked frame pops");
    store
        .push_frame(Frame::Destructor {
            tag: DestructorTag::Force,
            arguments: crate::store::ObservationArguments::Nullary,
        })
        .expect("room");
    assert_eq!(
        Err(StoreFault::StaleMark(mark)),
        store.shrink_to(mark),
        "the height is re-pushed under another serial"
    );
    assert_eq!(
        Ok(()),
        store.shrink_to(ContinuationMark::BASE),
        "the base is always live"
    );
    assert_eq!(
        FrameHeight::ZERO,
        store.frame_height(),
        "the region is empty"
    );
}

/// Bindings are read innermost first, in each chain independently.
#[test]
fn environments_bind_innermost_first()
{
    let mut store = Store::new();
    let first = store.allocate(integer(Digits("1"))).expect("room");
    let second = store.allocate(integer(Digits("2"))).expect("room");
    let outer = store.bind_value(Environment::EMPTY, first).expect("room");
    let inner = store.bind_value(outer, second).expect("room");
    let index = |raw: u32| DeBruijnIndex::from(raw);
    assert_eq!(
        Some(second),
        store.lookup_value(inner, index(0)),
        "index 0 is the innermost"
    );
    assert_eq!(
        Some(first),
        store.lookup_value(inner, index(1)),
        "index 1 is the next out"
    );
    assert_eq!(
        None,
        store.lookup_value(inner, index(2)),
        "past the chain is unbound"
    );
    assert_eq!(
        None,
        store.lookup_covalue(inner, CovariableIndex::from(0_u32)),
        "no covariable is bound"
    );

    let marked = store
        .bind_covalue(inner, crate::store::Covalue::Pinned(ContinuationMark::BASE))
        .expect("room");
    assert_eq!(
        Some(crate::store::Covalue::Pinned(ContinuationMark::BASE)),
        store.lookup_covalue(marked, CovariableIndex::from(0_u32)),
        "the covalue chain reads its binding"
    );
    assert_eq!(
        Some(second),
        store.lookup_value(marked, index(0)),
        "the producer chain is unchanged"
    );
    assert_eq!(
        alloc::vec![second, first],
        store.bound_values(marked).collect::<alloc::vec::Vec<_>>(),
        "the walk reads the chain innermost first, as the lookups do"
    );
}

/// Heap and memo families retain exact identities at their allocation
/// boundaries.
#[test]
fn heap_reads_preserve_identity_at_the_end()
{
    let mut store = Store::new();
    assert_eq!(None, store.value(HeapValueId::from(0_u32)));
    assert_eq!(None, store.cell(CellId::from(0_u32)));
    let first = store.allocate(integer(Digits("11"))).expect("room");
    let last = store.allocate(integer(Digits("29"))).expect("room");
    assert_eq!(HeapValueId::from(0_u32), first);
    assert_eq!(HeapValueId::from(1_u32), last);
    assert_eq!(Some(&integer(Digits("11"))), store.value(first));
    assert_eq!(Some(&integer(Digits("29"))), store.value(last));
    assert_eq!(None, store.value(HeapValueId::from(2_u32)));
    let cell = store.allocate_cell().expect("room");
    assert_eq!(CellId::from(0_u32), cell);
    assert_eq!(Some(MemoState::Unforced), store.cell(cell));
    assert_eq!(None, store.cell(CellId::from(1_u32)));
}

/// Every memo refusal preserves its target, including competing missing
/// addresses.
#[test]
fn cell_refusals_preserve_state_and_error_precedence()
{
    let mut store = Store::new();
    let value = store.allocate(integer(Digits("7"))).expect("room");
    let cell = store.allocate_cell().expect("room");
    let missing_cell = CellId::from(1_u32);
    let missing_value = HeapValueId::from(1_u32);
    assert_eq!(
        Err(StoreFault::DanglingCell(missing_cell)),
        store.begin_force(missing_cell)
    );
    assert_eq!(
        Err(StoreFault::DanglingCell(missing_cell)),
        store.decline(missing_cell)
    );
    assert_eq!(
        Err(StoreFault::DanglingValue(missing_value)),
        store.write_back(missing_cell, missing_value)
    );
    assert_eq!(
        Err(StoreFault::DanglingCell(missing_cell)),
        store.write_back(missing_cell, value)
    );
    for state in [
        MemoState::Unforced,
        MemoState::InProgress,
        MemoState::Forced(value),
    ] {
        match state {
            MemoState::Unforced => {},
            MemoState::InProgress => {
                store.begin_force(cell).expect("live cell");
            },
            MemoState::Forced(cached) => {
                store.begin_force(cell).expect("live cell");
                store.write_back(cell, cached).expect("in progress");
            },
        }
        assert_eq!(
            Err(StoreFault::DanglingValue(missing_value)),
            store.write_back(cell, missing_value)
        );
        assert_eq!(Some(state), store.cell(cell));
        if state == MemoState::InProgress {
            assert_eq!(Ok(()), store.decline(cell));
            assert_eq!(Some(MemoState::Unforced), store.cell(cell));
        }
        else {
            let refusal = StoreFault::CellNotInProgress { cell, found: state };
            assert_eq!(Err(refusal), store.write_back(cell, value));
            assert_eq!(Err(refusal), store.decline(cell));
            assert_eq!(Some(state), store.cell(cell));
        }
    }
}

/// Producer and covalue chains shift independently and stop at missing
/// links.
#[test]
fn both_binding_chains_preserve_outer_and_opposite_scopes()
{
    let mut store = Store::new();
    let first = store.allocate(integer(Digits("1"))).expect("room");
    let second = store.allocate(integer(Digits("2"))).expect("room");
    let empty = Environment::EMPTY;
    assert_eq!(None, store.lookup_value(empty, DeBruijnIndex::from(0_u32)));
    assert_eq!(
        None,
        store.lookup_covalue(empty, CovariableIndex::from(0_u32))
    );
    assert_eq!(None, store.bound_values(empty).next());
    let initial = store.bind_value(empty, first).expect("room");
    let initial = store
        .bind_covalue(
            initial,
            crate::store::Covalue::Pinned(ContinuationMark::BASE),
        )
        .expect("room");
    store
        .push_frame(Frame::Destructor {
            tag: DestructorTag::Force,
            arguments: crate::store::ObservationArguments::Nullary,
        })
        .expect("room");
    let mark = store.mark();
    let extended = store
        .bind_covalue(initial, crate::store::Covalue::Pinned(mark))
        .expect("room");
    let extended = store.bind_value(extended, second).expect("room");
    for (index, value, covalue) in [
        (
            0_u32,
            Some(second),
            Some(crate::store::Covalue::Pinned(mark)),
        ),
        (
            1,
            Some(first),
            Some(crate::store::Covalue::Pinned(ContinuationMark::BASE)),
        ),
        (2, None, None),
    ] {
        assert_eq!(
            value,
            store.lookup_value(extended, DeBruijnIndex::from(index))
        );
        assert_eq!(
            covalue,
            store.lookup_covalue(extended, CovariableIndex::from(index))
        );
    }
    assert_eq!(
        Some(first),
        store.lookup_value(initial, DeBruijnIndex::from(0_u32))
    );
    assert_eq!(
        Some(crate::store::Covalue::Pinned(ContinuationMark::BASE)),
        store.lookup_covalue(initial, CovariableIndex::from(0_u32))
    );
    assert_eq!(
        alloc::vec![second, first],
        store.bound_values(extended).collect::<Vec<_>>()
    );
    let dangling = Environment {
        values: ValueScope::Innermost(ValueBindingId::from(u32::MAX)),
        linears: ValueScope::Innermost(ValueBindingId::from(u32::MAX)),
        covalues: CovalueScope::Innermost(CovalueBindingId::from(u32::MAX)),
    };
    assert_eq!(
        None,
        store.lookup_value(dangling, DeBruijnIndex::from(0_u32))
    );
    assert_eq!(
        None,
        store.lookup_covalue(dangling, CovariableIndex::from(0_u32))
    );
    assert_eq!(None, store.bound_values(dangling).next());
}

/// A linear binding is read at its own index past an intuitionistic one,
/// and a write through it is read back while the other chain is
/// unchanged.
#[test]
fn a_linear_binding_is_written_in_place()
{
    let mut store = Store::new();
    let zero = store.allocate(integer(Digits("0"))).expect("room");
    let one = store.allocate(integer(Digits("1"))).expect("room");
    let (held, cell) = store.bind_linear(Environment::EMPTY, zero).expect("room");
    let inner = store.bind_value(held, one).expect("room");
    assert_eq!(
        Some(cell),
        store.lookup_linear(inner, DeBruijnIndex::from(0_u32)),
        "an intuitionistic binding does not shift the linear chain"
    );
    assert_eq!(
        None,
        store.lookup_linear(inner, DeBruijnIndex::from(1_u32)),
        "past the linear chain"
    );
    store.write_linear(cell, one).expect("live binding");
    let read = |store: &Store, environment| {
        let id = store.lookup_linear(environment, DeBruijnIndex::from(0_u32))?;
        store.linear(id)
    };
    assert_eq!(
        (Some(one), Some(one)),
        (read(&store, held), read(&store, inner)),
        "the write is read through every environment sharing the binding"
    );
    assert_eq!(
        None,
        store.lookup_value(held, DeBruijnIndex::from(0_u32)),
        "the producer chain binds nothing of the linear one"
    );
    assert_eq!(
        Err(StoreFault::DanglingBinding(ValueBindingId::from(u32::MAX))),
        store.write_linear(ValueBindingId::from(u32::MAX), one)
    );
}

/// A view ends once, on its own access's frame: a second ending and an
/// ending with no frame are refused by name.
#[test]
fn a_view_ends_once_on_its_own_frame()
{
    let mut store = Store::new();
    let zero = store.allocate(integer(Digits("0"))).expect("room");
    let (held, cell) = store.bind_linear(Environment::EMPTY, zero).expect("room");
    let (_, outer) = store.bind_linear(held, zero).expect("room");
    let (_, inner) = store.bind_linear(held, zero).expect("room");
    let unwind = CommandId::from(0_u32);
    for view in [outer, inner] {
        store
            .push_frame(Frame::Access {
                held: cell,
                view,
                unwind,
                environment: held,
                ending: Ending::Open,
            })
            .expect("room");
    }
    assert_eq!(
        Ok(FrameHeight::from(0_usize)),
        store.settle(outer, Ending::Aborted),
        "the outer view ends the lower frame"
    );
    assert_eq!(
        Err(StoreFault::Ended {
            view: outer,
            found: Ending::Aborted,
        }),
        store.settle(outer, Ending::Resumed(zero)),
        "a view ends once"
    );
    assert_eq!(
        Ok(FrameHeight::from(1_usize)),
        store.settle(inner, Ending::Resumed(zero)),
        "the inner view ends the upper frame"
    );
    assert_eq!(
        Some(Frame::Access {
            held: cell,
            view: inner,
            unwind,
            environment: held,
            ending: Ending::Resumed(zero),
        }),
        store.pop_frame(),
        "each view ends its own frame"
    );
    store.pop_frame().expect("outer frame");
    assert_eq!(
        Err(StoreFault::NoAccess(outer)),
        store.settle(outer, Ending::Aborted),
        "a view whose access has ended names no frame"
    );
}

/// Exhausting serials refuses a push without popping or reusing a frame.
#[test]
fn frame_serial_exhaustion_preserves_the_region()
{
    let mut store = Store::new();
    let force = Frame::Destructor {
        tag: DestructorTag::Force,
        arguments: crate::store::ObservationArguments::Nullary,
    };
    let apply = Frame::Destructor {
        tag: DestructorTag::Apply,
        arguments: crate::store::ObservationArguments::Nullary,
    };
    store.push_frame(force).expect("room");
    let first = store.mark();
    store.last_serial = FrameSerial::from(usize::MAX.saturating_sub(1));
    store.push_frame(apply).expect("last representable serial");
    let last = store.mark();
    assert_eq!(FrameSerial::from(usize::MAX), last.serial);
    assert_eq!(FrameHeight::from(2_usize), last.height);
    assert_eq!(Err(StoreFault::SerialsExhausted), store.push_frame(force));
    assert_eq!(last, store.mark());
    assert_eq!(Some(apply), store.pop_frame());
    assert_eq!(first, store.mark());
    assert_eq!(Some(force), store.pop_frame());
    assert_eq!(None, store.pop_frame());
    assert_eq!(ContinuationMark::BASE, store.mark());
    assert_eq!(Err(StoreFault::SerialsExhausted), store.push_frame(force));
    assert_eq!(ContinuationMark::BASE, store.mark());
}

/// Stale marks preserve the region; a faulty dropped update is reported
/// after its pop.
#[test]
fn shrinking_rejects_stale_marks_and_reports_dropped_update_faults()
{
    let mut store = Store::new();
    let force = Frame::Destructor {
        tag: DestructorTag::Force,
        arguments: crate::store::ObservationArguments::Nullary,
    };
    store.push_frame(force).expect("room");
    let old = store.mark();
    assert_eq!(Some(force), store.pop_frame());
    assert_eq!(Err(StoreFault::StaleMark(old)), store.shrink_to(old));
    assert_eq!(ContinuationMark::BASE, store.mark());
    store.push_frame(force).expect("room");
    let live = store.mark();
    assert_eq!(Err(StoreFault::StaleMark(old)), store.shrink_to(old));
    assert_eq!(live, store.mark());
    let cell = store.allocate_cell().expect("room");
    store.push_frame(Frame::Update { cell }).expect("room");
    assert_eq!(
        Err(StoreFault::CellNotInProgress {
            cell,
            found: MemoState::Unforced
        }),
        store.shrink_to(live)
    );
    assert_eq!(live, store.mark());
    assert_eq!(Some(MemoState::Unforced), store.cell(cell));
    let missing = CellId::from(1_u32);
    store
        .push_frame(Frame::Update { cell: missing })
        .expect("room");
    assert_eq!(
        Err(StoreFault::DanglingCell(missing)),
        store.shrink_to(live)
    );
    assert_eq!(live, store.mark());
    assert_eq!(Ok(()), store.shrink_to(ContinuationMark::BASE));
    assert_eq!(ContinuationMark::BASE, store.mark());
}
