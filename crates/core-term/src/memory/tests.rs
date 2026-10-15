use alloc::vec::Vec;

use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::MemoryForm;
use super::MemoryKind;
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
    let access: MemoryForm = MemoryForm::Access { held, body, unwind };
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
