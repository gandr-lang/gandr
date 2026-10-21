//! Witnesses for [`super`]: a call places each region binder at the region
//! its arguments show, and a definition abstracting none reads as declared.

use alloc::vec::Vec;

use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionBinder;
use gandr_core_term::effect::capability::RegionDepth;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::Unread;
use super::instantiated;
use super::placed;
use super::placement;

/// The domains of the arrows the thunk type `function` suspends, in order,
/// and the result its last codomain returns.
///
/// # Specification
/// trivial.
fn parameters(
    arena: &CoreArena,
    function: ValueTypeId,
) -> (Vec<Option<ValueType>>, Option<ValueType>)
{
    let Some(&ValueType::Thunk(mut body)) = arena.value_type(function)
    else {
        panic!("a thunk type");
    };
    let mut domains = Vec::new();
    loop {
        match arena.comp_type(body) {
            Some(&CompType::Arrow { domain, codomain }) => {
                domains.push(arena.value_type(domain).cloned());
                body = codomain;
            },
            Some(&CompType::Returner { result, .. }) => {
                return (domains, arena.value_type(result).cloned());
            },
            other => panic!("an arrow or a returner: {other:?}"),
        }
    }
}

#[test]
fn a_call_places_each_binder_at_the_shortest_region_shown_1221()
{
    let scoped = |depth: u32| Region::Scoped(RegionDepth::from(depth));
    let bound = |ordinal: u32| Region::Bound(RegionBinder::from(ordinal));
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    // U ((a : Integer at r) -> (b : Integer at r) -> (c : Integer at s) ->
    // F (Integer at r)), r and s the definition's two region binders.
    let at_r = arena.value_type_kept(integer, bound(0));
    let at_s = arena.value_type_kept(integer, bound(1));
    let answer = arena.comp_type_returner(at_r);
    let third = arena.comp_type_arrow(at_s, answer);
    let second = arena.comp_type_arrow(at_r, third);
    let first = arena.comp_type_arrow(at_r, second);
    let declared = arena.value_type_thunk(first);
    // f(x, y, z): x kept in the first scope's region, y in the second's, z
    // kept nowhere; the call stands inside a third.
    let shallow = arena.value_type_kept(integer, scoped(1));
    let deep = arena.value_type_kept(integer, scoped(2));
    let spine = [0_u32, 1, 2]
        .map(|index| arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)));
    let found = |index: DeBruijnIndex| {
        Ok(match u32::from(index) {
            0 => shallow,
            1 => deep,
            _ => integer,
        })
    };
    let Ok(Maybe::Present(renaming)) = placement(&arena, declared, (&spine, scoped(3)), found)
    else {
        panic!("a definition over regions is placed");
    };
    let read = instantiated(&mut arena, declared, &renaming);
    let kept = |region| {
        Some(ValueType::Kept {
            value: integer,
            region,
        })
    };
    assert_eq!(
        parameters(&arena, read),
        (
            alloc::vec![kept(scoped(2)), kept(scoped(2)), kept(scoped(3))],
            kept(scoped(2))
        ),
        "r stands at the deeper scope both arguments outlive, in the answer too; s, shown \
         nowhere, at the call's own region"
    );
    assert_eq!(
        placed(&[bound(0), scoped(1)], scoped(3)),
        scoped(1),
        "a caller's region binder outlives the caller's scope"
    );
    assert_eq!(
        placed(&[bound(0), bound(1)], scoped(3)),
        scoped(3),
        "two of the caller's binders are unordered, so the call's own region stands"
    );
}

#[test]
fn a_definition_abstracting_no_region_reads_as_declared()
{
    let scoped = |depth: u32| Region::Scoped(RegionDepth::from(depth));
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let kept = arena.value_type_kept(integer, scoped(1));
    let answer = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(kept, answer);
    let declared = arena.value_type_thunk(arrow);
    let spine = [arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))];
    assert_eq!(
        placement(&arena, declared, (&spine, scoped(2)), |_index| Ok(kept)),
        Ok(Maybe::Absent(Unread::Unabstracted)),
        "a type keeping its value at a scope names no binder"
    );
}
