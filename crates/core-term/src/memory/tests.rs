use alloc::vec::Vec;

use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::AccessMode;
use super::MemoryForm;
use super::MemoryKind;
use super::Place;
use crate::Binders;
use crate::Computation;
use crate::CoreArena;
use crate::session::ChildOrder;

#[test]
fn forms_name_their_resident_and_children()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_unit();
    let other = arena.value_tuple(&[unit, unit]);
    let body = arena.computation_return(unit);
    let unwind = arena.computation_return(unit);
    let held = DeBruijnIndex::from(1_u32);
    let hold: MemoryForm = MemoryForm::Hold { value: unit, body };
    assert_eq!(hold.kind(), MemoryKind::Hold, "a hold is a hold");
    assert!(
        matches!(hold.resident(), Maybe::Absent(_)),
        "and names no slot: it binds one"
    );
    assert_eq!(
        hold.values().collect::<Vec<_>>(),
        [unit],
        "its value is a child"
    );
    let mut seen = Vec::new();
    let mapped = hold
        .try_map(
            ChildOrder::Reverse,
            &mut seen,
            |seen: &mut Vec<&str>, value| {
                seen.push("value");
                Ok::<_, ()>(value)
            },
            |seen, computation| {
                seen.push("body");
                Ok(computation)
            },
        )
        .expect("identity maps succeed");
    assert_eq!(
        seen,
        ["body", "value"],
        "a reverse map is the canonical order reversed, across families"
    );
    assert_eq!(mapped, hold, "and keeps each child in its place");
    let access: MemoryForm = MemoryForm::Access {
        mode: AccessMode::Exclusive { unwind },
        held,
        place: Place::Whole,
        body,
    };
    assert_eq!(access.kind(), MemoryKind::Access, "an access is an access");
    assert_eq!(
        access.resident(),
        Maybe::Present(held),
        "and names the slot it lends"
    );
    assert_eq!(
        access.scoped().collect::<Vec<_>>(),
        [(body, Binders::ONE), (unwind, Binders::NONE)],
        "its body stands under the view's binder, its unwind under none"
    );
    let shared: MemoryForm = MemoryForm::Access {
        mode: AccessMode::Shared,
        held,
        place: Place::Whole,
        body,
    };
    assert_eq!(
        shared.scoped().collect::<Vec<_>>(),
        [(body, Binders::ONE)],
        "a shared access has its body alone: no unwind"
    );
    assert_ne!(
        shared.shape(),
        access.shape(),
        "a shared access and an exclusive one of one slot are two formers"
    );
    assert!(
        matches!(
            (shared.shape(), access.shape()),
            (
                MemoryForm::Access {
                    mode: AccessMode::Shared,
                    ..
                },
                MemoryForm::Access {
                    mode: AccessMode::Exclusive { .. },
                    ..
                }
            )
        ),
        "each keeps its mode through the map"
    );
    let indexed: MemoryForm = MemoryForm::Access {
        mode: AccessMode::Exclusive { unwind },
        held,
        place: Place::At { index: other },
        body,
    };
    assert_eq!(
        indexed.values().collect::<Vec<_>>(),
        [other],
        "an access at an index has its index as its value child"
    );
    assert_ne!(
        indexed.shape(),
        access.shape(),
        "an access at an index and one of the whole value are two formers"
    );
    let mut order = Vec::new();
    for direction in [ChildOrder::Forward, ChildOrder::Reverse] {
        let mapped = indexed
            .try_map(
                direction,
                &mut order,
                |order: &mut Vec<&str>, value| {
                    order.push("index");
                    Ok::<_, ()>(value)
                },
                |order, computation| {
                    order.push(if computation == body {
                        "body"
                    }
                    else {
                        "unwind"
                    });
                    Ok(computation)
                },
            )
            .expect("identity maps succeed");
        assert_eq!(mapped, indexed, "a map keeps the place and its index");
    }
    assert_eq!(
        order,
        ["index", "body", "unwind", "unwind", "body", "index"],
        "the index is read before the body forward, after it in reverse"
    );
    let view = DeBruijnIndex::from(0_u32);
    let resume: MemoryForm = MemoryForm::Resume { view, value: unit };
    assert_eq!(
        resume.resident(),
        Maybe::Present(view),
        "a resume names its view"
    );
    assert_eq!(
        resume.shape(),
        MemoryForm::<_>::Resume { view, value: other }.shape(),
        "two values written back through one view are one shape"
    );
    assert_ne!(
        resume.shape(),
        MemoryForm::<_>::Resume {
            view: held,
            value: unit
        }
        .shape(),
        "two views are not"
    );
    let abort: MemoryForm = MemoryForm::Abort { view };
    assert_eq!(abort.kind(), MemoryKind::Abort, "an abort is an abort");
    assert_eq!(
        abort
            .values()
            .chain(abort.computations().map(|_| unit))
            .count(),
        0_usize,
        "and has no child"
    );
    let minted = arena.computation_memory(access.clone());
    assert_eq!(
        arena.computation(minted),
        Some(&Computation::Memory(access)),
        "a minted access reads back whole"
    );
}
