use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;

use super::BinderDepth;
use super::Context;
use super::ContextError;
use super::LinearUse;
use crate::arena::CoreArena;
use crate::arena::ValueTypeId;
use crate::syntax::Zone;

/// Two distinct value-type ids to open binders at, so a lookup returning
/// the wrong slot is visible rather than accidentally right.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns an arena holding the unit value type and the product of
///   it with itself, together with both ids, which are distinct.
/// - provides: the shared fixture the context rows open binders at.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — unequal declared types distinguish the innermost binder
///   from the outer one as opening shifts de Bruijn indices.
/// - witness: `context::tests::opening_a_binder_shifts_the_zones_indices`
#[spec(ensures: |ret| ret.1 != ret.2
        && ret.0.value_type(ret.1) == Some(&crate::ValueType::unit())
        && ret.0.value_type(ret.2) == Some(&crate::ValueType::Product([ret.1, ret.1].into())))]
fn two_types() -> (CoreArena, ValueTypeId, ValueTypeId)
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pair = arena.value_type_product(&[unit, unit]);
    (arena, unit, pair)
}

#[test]
fn occurrences_preserve_other_slots_and_refusal_state()
{
    let (_arena, outer, inner) = two_types();
    let mut context = Context::new();
    for zone in [Zone::Intuitionistic, Zone::Linear] {
        context.open(zone, outer);
        context.open(zone, inner);
    }
    for zone in [Zone::Intuitionistic, Zone::Linear] {
        for raw in [2_u32, u32::MAX] {
            let index = DeBruijnIndex::from(raw);
            let before = context.clone();
            assert_eq!(
                Err(ContextError::UnboundIndex {
                    zone,
                    index,
                    depth: BinderDepth::from(2_usize)
                }),
                context.occurrence(zone, index)
            );
            assert_eq!(before, context);
        }
    }
    let zero = DeBruijnIndex::from(0_u32);
    let one = DeBruijnIndex::from(1_u32);
    assert_eq!(Ok(outer), context.occurrence(Zone::Linear, one));
    assert_eq!(Ok(LinearUse::Available), context.linear_use(zero));
    assert_eq!(Ok(LinearUse::Consumed), context.linear_use(one));
    let before = context.clone();
    assert_eq!(
        Err(ContextError::LinearSlotUnconsumed {
            depth: BinderDepth::from(2_usize)
        }),
        context.close(Zone::Linear)
    );
    assert_eq!(before, context);
    assert_eq!(Ok(inner), context.occurrence(Zone::Intuitionistic, zero));
    assert_eq!(before, context);
    assert_eq!(Ok(inner), context.occurrence(Zone::Linear, zero));
    assert_eq!(Ok(inner), context.close(Zone::Linear));
    assert_eq!(Ok(outer), context.declared(Zone::Linear, zero));
    assert_eq!(
        Err(ContextError::LinearSlotConsumed { index: zero }),
        context.occurrence(Zone::Linear, zero)
    );
    assert_eq!(Ok(inner), context.declared(Zone::Intuitionistic, zero));
    assert_eq!(Ok(outer), context.declared(Zone::Intuitionistic, one));
    assert_eq!(Ok(outer), context.close(Zone::Linear));
    assert_eq!(BinderDepth::from(0_usize), context.depth(Zone::Linear));
}

#[test]
fn opening_a_binder_shifts_the_zones_indices()
{
    let (_arena, outer, inner) = two_types();
    let mut context = Context::new();
    context.open(Zone::Intuitionistic, outer);
    assert_eq!(
        Ok(outer),
        context.declared(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
        "the only binder is index zero"
    );
    context.open(Zone::Intuitionistic, inner);
    assert_eq!(
        Ok(inner),
        context.declared(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
        "the new binder takes index zero"
    );
    assert_eq!(
        Ok(outer),
        context.declared(Zone::Intuitionistic, DeBruijnIndex::from(1_u32)),
        "the old binder moved out by exactly one — weakening in the structural zone"
    );
    assert_eq!(
        BinderDepth::from(0_usize),
        context.depth(Zone::Linear),
        "the zones have separate binder stacks"
    );
}

#[test]
fn the_intuitionistic_zone_admits_contraction()
{
    let (_arena, declared, _other) = two_types();
    let mut context = Context::new();
    context.open(Zone::Intuitionistic, declared);
    let index = DeBruijnIndex::from(0_u32);
    assert_eq!(
        Ok(declared),
        context.occurrence(Zone::Intuitionistic, index),
        "the first occurrence types"
    );
    assert_eq!(
        Ok(declared),
        context.occurrence(Zone::Intuitionistic, index),
        "and so does the second — a structural slot spends nothing"
    );
}

#[test]
fn the_linear_zone_refuses_contraction()
{
    let (_arena, declared, _other) = two_types();
    let mut context = Context::new();
    context.open(Zone::Linear, declared);
    let index = DeBruijnIndex::from(0_u32);
    assert_eq!(
        Ok(declared),
        context.occurrence(Zone::Linear, index),
        "the single use types the first occurrence"
    );
    assert_eq!(
        Err(ContextError::LinearSlotConsumed { index }),
        context.occurrence(Zone::Linear, index),
        "the second occurrence is refused by name"
    );
    assert_eq!(
        Ok(LinearUse::Consumed),
        context.linear_use(index),
        "the refusal left the slot consumed rather than reopening it"
    );
    assert_eq!(
        Ok(declared),
        context.declared(Zone::Linear, index),
        "a consumed slot still reports the type it was opened at"
    );
}

#[test]
fn a_fresh_linear_slot_opens_available()
{
    let (_arena, declared, _other) = two_types();
    let mut context = Context::new();
    context.open(Zone::Linear, declared);
    let index = DeBruijnIndex::from(0_u32);
    assert_eq!(
        Ok(LinearUse::Available),
        context.linear_use(index),
        "a linear binder opens carrying its use"
    );
    assert_eq!(
        Err(ContextError::UnboundIndex {
            zone: Zone::Linear,
            index: DeBruijnIndex::from(1_u32),
            depth: BinderDepth::from(1_usize),
        }),
        context.linear_use(DeBruijnIndex::from(1_u32)),
        "an index past the linear depth has no use to report"
    );
}

#[test]
fn advancing_rebinds_one_available_slot()
{
    let (_arena, declared, other) = two_types();
    let mut context = Context::new();
    context.open(Zone::Linear, declared);
    context.open(Zone::Linear, declared);
    let outer = DeBruijnIndex::from(1_u32);
    let inner = DeBruijnIndex::from(0_u32);
    assert_eq!(
        Ok(declared),
        context.advance(outer, other),
        "the move answers the type it replaced"
    );
    assert_eq!(
        Ok(other),
        context.declared(Zone::Linear, outer),
        "the outer slot moved"
    );
    assert_eq!(
        Ok(declared),
        context.declared(Zone::Linear, inner),
        "the inner did not"
    );
    assert_eq!(
        Ok(LinearUse::Available),
        context.linear_use(outer),
        "a move spends no use"
    );
    assert_eq!(Ok(declared), context.occurrence(Zone::Linear, inner));
    let before = context.clone();
    assert_eq!(
        Err(ContextError::LinearSlotConsumed { index: inner }),
        context.advance(inner, other),
        "a closed endpoint does not move"
    );
    assert_eq!(
        Err(ContextError::UnboundIndex {
            zone: Zone::Linear,
            index: DeBruijnIndex::from(2_u32),
            depth: BinderDepth::from(2_usize),
        }),
        context.advance(DeBruijnIndex::from(2_u32), other),
        "nor does an index past the depth"
    );
    assert_eq!(before, context, "a refused move changes nothing");
}

#[test]
fn a_restored_snapshot_undoes_uses_and_advances()
{
    let (_arena, declared, other) = two_types();
    let mut context = Context::new();
    context.open(Zone::Intuitionistic, other);
    context.open(Zone::Linear, declared);
    context.open(Zone::Linear, declared);
    let snapshot = context.linear_zone();
    assert_eq!(
        BinderDepth::from(2_usize),
        snapshot.depth(),
        "both slots are recorded"
    );
    assert_eq!(
        Ok(declared),
        context.advance(DeBruijnIndex::from(1_u32), other)
    );
    assert_eq!(
        Ok(declared),
        context.occurrence(Zone::Linear, DeBruijnIndex::from(0_u32))
    );
    assert_ne!(snapshot, context.linear_zone(), "the zone moved on");
    context.restore_linear(&snapshot);
    assert_eq!(snapshot, context.linear_zone(), "and is back as recorded");
    assert_eq!(
        [
            (declared, LinearUse::Available),
            (declared, LinearUse::Available)
        ],
        *context.linear_slots().collect::<alloc::vec::Vec<_>>(),
        "outermost first, both available at their first type"
    );
    assert_eq!(
        BinderDepth::from(1_usize),
        context.depth(Zone::Intuitionistic),
        "the intuitionistic zone is untouched"
    );
}

#[test]
fn truncating_drops_unspent_slots_without_refusal()
{
    let (_arena, declared, other) = two_types();
    let mut context = Context::new();
    context.open(Zone::Linear, declared);
    context.open(Zone::Linear, other);
    context.open(Zone::Intuitionistic, declared);
    context.truncate(Zone::Linear, BinderDepth::from(3_usize));
    assert_eq!(
        BinderDepth::from(2_usize),
        context.depth(Zone::Linear),
        "a depth above the zone's drops nothing"
    );
    context.truncate(Zone::Linear, BinderDepth::from(1_usize));
    assert_eq!(
        BinderDepth::from(1_usize),
        context.depth(Zone::Linear),
        "the unspent inner slot is dropped without a refusal"
    );
    assert_eq!(
        Ok(declared),
        context.declared(Zone::Linear, DeBruijnIndex::from(0_u32)),
        "the outer slot is kept"
    );
    assert_eq!(
        BinderDepth::from(1_usize),
        context.depth(Zone::Intuitionistic),
        "and the other zone is untouched"
    );
}

#[test]
fn a_declared_lookup_spends_no_use()
{
    let (_arena, declared, _other) = two_types();
    let mut context = Context::new();
    context.open(Zone::Linear, declared);
    let index = DeBruijnIndex::from(0_u32);
    assert_eq!(Ok(declared), context.declared(Zone::Linear, index));
    assert_eq!(
        Ok(LinearUse::Available),
        context.linear_use(index),
        "reading a slot is not occurring in it"
    );
}

#[test]
fn an_index_past_the_depth_is_unbound()
{
    let (_arena, declared, _other) = two_types();
    let mut context = Context::new();
    let empty = DeBruijnIndex::from(0_u32);
    assert_eq!(
        Err(ContextError::UnboundIndex {
            zone: Zone::Intuitionistic,
            index: empty,
            depth: BinderDepth::from(0_usize),
        }),
        context.occurrence(Zone::Intuitionistic, empty),
        "an empty zone binds no index"
    );
    context.open(Zone::Intuitionistic, declared);
    let past = DeBruijnIndex::from(1_u32);
    assert_eq!(
        Err(ContextError::UnboundIndex {
            zone: Zone::Intuitionistic,
            index: past,
            depth: BinderDepth::from(1_usize),
        }),
        context.declared(Zone::Intuitionistic, past),
        "the first index past the depth is refused, and the refusal names the depth"
    );
}

#[test]
fn closing_an_empty_zone_is_refused()
{
    let mut context = Context::new();
    for zone in [Zone::Intuitionistic, Zone::Linear] {
        assert_eq!(
            Err(ContextError::NoBinderToClose { zone }),
            context.close(zone),
            "an empty zone has no scope to close"
        );
        assert_eq!(
            BinderDepth::from(0_usize),
            context.depth(zone),
            "the refusal left the zone where it was"
        );
    }
}

#[test]
fn a_linear_binder_must_be_consumed_before_it_closes()
{
    let (_arena, declared, _other) = two_types();
    let mut context = Context::new();
    context.open(Zone::Linear, declared);
    assert_eq!(
        Err(ContextError::LinearSlotUnconsumed {
            depth: BinderDepth::from(1_usize),
        }),
        context.close(Zone::Linear),
        "an unspent linear use is a refusal, not a silent discard"
    );
    assert_eq!(
        BinderDepth::from(1_usize),
        context.depth(Zone::Linear),
        "the failure left the context at the failure point, un-unwound"
    );
    let consumed = context.occurrence(Zone::Linear, DeBruijnIndex::from(0_u32));
    assert_eq!(
        Ok(declared),
        consumed,
        "the slot was still there to be used"
    );
    assert_eq!(
        Ok(declared),
        context.close(Zone::Linear),
        "a consumed slot closes and reports the type it was opened at"
    );
}

#[test]
fn an_intuitionistic_scope_closes_without_a_use()
{
    let (_arena, declared, _other) = two_types();
    let mut context = Context::new();
    context.open(Zone::Intuitionistic, declared);
    assert_eq!(
        Ok(declared),
        context.close(Zone::Intuitionistic),
        "a structural binder closes unread — weakening is admissible in the structural zone"
    );
}

#[test]
fn a_binder_is_located_where_it_was_opened()
{
    let (_arena, declared, other) = two_types();
    let elsewhere = crate::world::World::Declared(gandr_kernel_term::ConstantIndex::from(3_usize));
    let mut context = Context::new();
    context.open(Zone::Intuitionistic, declared);
    context.open(Zone::Linear, declared);
    assert_eq!(
        crate::world::World::Host,
        context.relocate(elsewhere),
        "the register starts at the host's world and reports it on a move"
    );
    context.open(Zone::Intuitionistic, other);
    context.open_at(Zone::Linear, other, crate::world::World::Host);
    let zero = DeBruijnIndex::from(0_u32);
    let one = DeBruijnIndex::from(1_u32);
    assert_eq!(Ok(elsewhere), context.located(Zone::Intuitionistic, zero));
    assert_eq!(
        Ok(crate::world::World::Host),
        context.located(Zone::Intuitionistic, one),
        "a binder opened before the move stays where it was opened"
    );
    assert_eq!(
        Ok(crate::world::World::Host),
        context.located(Zone::Linear, zero),
        "an explicit location wins over the register"
    );
    assert_eq!(
        elsewhere,
        context.world(),
        "an explicit location moves no register"
    );
    assert!(matches!(
        context.located(Zone::Linear, DeBruijnIndex::from(2_u32)),
        Err(ContextError::UnboundIndex { .. })
    ));
    assert_eq!(Ok(other), context.close(Zone::Intuitionistic));
    assert_eq!(
        Ok(crate::world::World::Host),
        context.located(Zone::Intuitionistic, zero),
        "closing a binder drops its location with it"
    );
    context.open(Zone::Intuitionistic, other);
    context.open(Zone::Intuitionistic, other);
    context.open_at(Zone::Intuitionistic, declared, crate::world::World::Host);
    assert_eq!(
        [
            zero,
            one,
            DeBruijnIndex::from(2_u32),
            DeBruijnIndex::from(3_u32)
        ]
        .map(|index| context.located(Zone::Intuitionistic, index)),
        [
            Ok(crate::world::World::Host),
            Ok(elsewhere),
            Ok(elsewhere),
            Ok(crate::world::World::Host),
        ],
        "binders opened at one world in a row share it, and one opened back at the host's stands there"
    );
    context.truncate(Zone::Intuitionistic, BinderDepth::from(2_usize));
    context.open_at(Zone::Intuitionistic, other, crate::world::World::Host);
    assert_eq!(
        [zero, one, DeBruijnIndex::from(2_u32)]
            .map(|index| context.located(Zone::Intuitionistic, index)),
        [
            Ok(crate::world::World::Host),
            Ok(elsewhere),
            Ok(crate::world::World::Host),
        ],
        "truncating forgets the locations above the depth and keeps those below it"
    );
}
