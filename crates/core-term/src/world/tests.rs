use alloc::vec::Vec;

use gandr_kernel_term::ConstantIndex;

use super::World;
use super::WorldForm;
use super::WorldKind;
use super::WorldType;
use crate::Binders;
use crate::Computation;
use crate::CoreArena;
use crate::ValueType;
use crate::session::ChildOrder;

#[test]
fn forms_name_their_children_and_binders()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_unit();
    let body = arena.computation_return(unit);
    let seat = World::Declared(ConstantIndex::from(0_usize));
    let operator = World::Declared(ConstantIndex::from(1_usize));

    let hold: WorldForm = WorldForm::Hold { value: unit };
    assert_eq!(hold.kind(), WorldKind::Hold);
    assert_eq!(hold.values().collect::<Vec<_>>(), [unit]);
    assert_eq!(hold.scoped().count(), 0, "a hold has no computation child");

    let leta: WorldForm = WorldForm::Leta { value: unit, body };
    assert_eq!(leta.kind(), WorldKind::Leta);
    assert_eq!(
        leta.scoped().collect::<Vec<_>>(),
        [(body, Binders::ONE)],
        "a leta's body stands under the one binder it opens"
    );
    let mut seen = Vec::new();
    let mapped = leta
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
        "the reverse order visits the body first"
    );
    assert_eq!(mapped, leta, "each image stays at its own position");

    let there: WorldForm = WorldForm::Migrate { world: seat, body };
    assert_eq!(there.kind(), WorldKind::Migrate);
    assert_eq!(there.values().count(), 0);
    assert_eq!(
        there.scoped().collect::<Vec<_>>(),
        [(body, Binders::NONE)],
        "a migration binds nothing"
    );
    let elsewhere: WorldForm = WorldForm::Migrate {
        world: operator,
        body,
    };
    assert_eq!(there.shape(), there.shape());
    assert_ne!(
        there.shape(),
        elsewhere.shape(),
        "two migrations share a shape only when they name one world"
    );

    let minted = arena.computation_world(leta);
    assert_eq!(arena.computation(minted), Some(&Computation::World(leta)));

    let unit_type = arena.value_type_unit();
    let handle = WorldType::At {
        inner: unit_type,
        world: seat,
    };
    assert_eq!(handle.world(), seat);
    assert_eq!(handle.types().collect::<Vec<_>>(), [unit_type]);
    let capability: WorldType = WorldType::Capability(operator);
    assert_eq!(capability.types().count(), 0, "a capability holds no type");
    let product = arena.value_type_product(&[unit_type, unit_type]);
    assert_eq!(
        handle.try_map(|_| Ok::<_, ()>(product)),
        Ok(WorldType::At {
            inner: product,
            world: seat
        }),
        "a handle maps its held type and keeps its world"
    );
    let at = arena.value_type_world(handle);
    assert_eq!(arena.value_type(at), Some(&ValueType::World(handle)));
}
