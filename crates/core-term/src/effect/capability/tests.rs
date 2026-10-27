use quenchant_shape::shape::Maybe;

use super::Region;
use super::RegionBinder;
use super::RegionDepth;
use super::RegionOrder;
use super::RestrictionError;
use super::grant;
use crate::CoreArena;
use crate::effect::EffectName;
use crate::effect::EffectOp;
use crate::effect::EffectRow;
use crate::effect::EffectSig;
use crate::effect::OperationName;
use crate::effect::host::HostSignatures;
use crate::row::RowInclusion;

#[test]
fn a_region_outlives_only_regions_nested_in_it()
{
    let body = Region::Scoped(RegionDepth::from(0_u32));
    let outer = Region::Scoped(RegionDepth::from(1_u32));
    let inner = Region::Scoped(RegionDepth::from(2_u32));
    let bound = Region::Bound(RegionBinder::from(0_u32));
    let other = Region::Bound(RegionBinder::from(1_u32));
    for (first, second, expected) in [
        (Region::Held, Region::Held, RegionOrder::Outlives),
        (Region::Held, outer, RegionOrder::Outlives),
        (outer, Region::Held, RegionOrder::EndsFirst),
        (outer, inner, RegionOrder::Outlives),
        (inner, outer, RegionOrder::EndsFirst),
        (inner, inner, RegionOrder::Outlives),
        (body, outer, RegionOrder::Outlives),
        (bound, bound, RegionOrder::Outlives),
        (bound, other, RegionOrder::EndsFirst),
        (other, bound, RegionOrder::EndsFirst),
        (Region::Held, bound, RegionOrder::Outlives),
        (bound, Region::Held, RegionOrder::EndsFirst),
        (bound, body, RegionOrder::Outlives),
        (body, bound, RegionOrder::EndsFirst),
        (bound, inner, RegionOrder::Outlives),
        (inner, bound, RegionOrder::EndsFirst),
    ] {
        assert_eq!(
            first.outlives(second),
            expected,
            "{first:?} against {second:?}"
        );
    }
}

#[test]
fn a_restriction_keeps_exactly_the_named_operations()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).expect("host interfaces");
    let read = OperationName::from("read");
    let write = OperationName::from("write");
    let forward = host.fs.restrict([&read, &write]).expect("two operations");
    let backward = host.fs.restrict([&write, &read]).expect("two operations");
    assert_eq!(forward, backward, "a restriction is a set of operations");
    assert_eq!(forward.name(), host.fs.name());
    assert_eq!(
        forward
            .operations()
            .map(|operation| operation.name.as_ref())
            .collect::<alloc::vec::Vec<_>>(),
        ["read", "write"]
    );
    for operation in forward.operations() {
        assert_eq!(
            host.fs.operation(&operation.name),
            Maybe::Present(operation),
            "each operation keeps the interface's types"
        );
    }
    let exit = OperationName::from("exit");
    assert_eq!(
        host.fs.restrict([&read, &exit]),
        Err(RestrictionError::Unknown(exit))
    );
    assert_eq!(
        host.fs.restrict([&read, &read]),
        Err(RestrictionError::Repeated(read))
    );
}

#[test]
fn attenuation_is_inclusion_on_grant_atoms()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).expect("host interfaces");
    let read = OperationName::from("read");
    let write = OperationName::from("write");
    let reads = EffectRow::authority(&[host.fs.restrict([&read]).expect("one operation")])
        .expect("one interface");
    let both = EffectRow::authority(&[host.fs.restrict([&read, &write]).expect("two")])
        .expect("one interface");
    assert_eq!(reads.grants_within(&both, &arena), RowInclusion::Included);
    assert_eq!(both.grants_within(&reads, &arena), RowInclusion::Excluded);
    assert_eq!(
        EffectRow::EMPTY.grants_within(&reads, &arena),
        RowInclusion::Included
    );
    let exits = EffectRow::authority(core::slice::from_ref(&host.proc)).expect("one interface");
    assert_eq!(exits.grants_within(&both, &arena), RowInclusion::Excluded);
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let string = arena.value_type_base(gandr_kernel_term::BaseType::String);
    let counted = EffectSig::new(EffectName::from("Fs"), [EffectOp {
        name: read,
        payload: string,
        reply: integer,
    }])
    .expect("one operation");
    let counted = EffectRow::authority(&[counted]).expect("one interface");
    assert_eq!(
        counted.grants_within(&both, &arena),
        RowInclusion::Excluded,
        "an atom whose reply type differs is another atom"
    );
    assert!(
        matches!(both.granted(&crate::effect::EffectLabel::at(host.fs.name(), Region::Held), &write), Maybe::Present(operation) if operation.name == write)
    );
    assert_eq!(
        reads.granted(
            &crate::effect::EffectLabel::at(host.fs.name(), Region::Held),
            &write
        ),
        Maybe::Absent(grant::Absent::Operation)
    );
    assert_eq!(
        reads.granted(
            &crate::effect::EffectLabel::at(host.proc.name(), Region::Held),
            &OperationName::from("exit")
        ),
        Maybe::Absent(grant::Absent::Interface)
    );
    assert_eq!(
        EffectRow::authority(&[host.fs.clone(), host.fs.clone()]),
        Err(crate::effect::EffectConflict::Signature(
            crate::effect::EffectLabel::at(host.fs.name(), Region::Held)
        ))
    );
    let joined = EffectRow::authority(&[host.proc.clone(), host.fs]).expect("two");
    assert_eq!(joined.signatures().len(), 2);
    assert_eq!(both.grants_within(&joined, &arena), RowInclusion::Included);
}

/// The atoms apart are each type that differs from the held one, held type
/// first, payload before reply, and the lookup's reason for an atom the
/// authority does not grant.
#[test]
fn the_atoms_apart_are_each_type_that_differs_held_first()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).expect("host interfaces");
    let read = OperationName::from("read");
    let write = OperationName::from("write");
    let reads = EffectRow::authority(&[host.fs.restrict([&read]).expect("one operation")])
        .expect("one interface");
    let both = EffectRow::authority(&[host.fs.restrict([&read, &write]).expect("two")])
        .expect("one interface");
    let Maybe::Present(held) = host.fs.operation(&read)
    else {
        panic!("the host's file system reads");
    };
    let (held_payload, held_reply) = (held.payload, held.reply);
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let character = arena.value_type_base(gandr_kernel_term::BaseType::Character);
    let reading = |payload, reply| {
        let restricted = EffectSig::new(EffectName::from("Fs"), [EffectOp {
            name: read.clone(),
            payload,
            reply,
        }])
        .expect("one operation");
        EffectRow::authority(&[restricted]).expect("one interface")
    };
    let apart = |row: &EffectRow| {
        row.atoms_apart(&both, &arena)
            .collect::<alloc::vec::Vec<_>>()
    };

    assert!(apart(&reads).is_empty(), "an atom granted as written");
    assert_eq!(
        apart(&reading(held_payload, integer)),
        [Maybe::Present((held_reply, integer))],
        "the reply that differs, held type first"
    );
    assert_eq!(
        apart(&reading(integer, character)),
        [
            Maybe::Present((held_payload, integer)),
            Maybe::Present((held_reply, character))
        ],
        "the payload, then the reply"
    );
    let exits = EffectRow::authority(core::slice::from_ref(&host.proc)).expect("one interface");
    assert_eq!(
        apart(&exits).first(),
        Some(&Maybe::Absent(grant::Absent::Interface)),
        "an interface the authority does not restrict"
    );
}

#[test]
fn a_kept_type_keeps_its_region_across_substitution()
{
    let mut arena = CoreArena::default();
    let region = Region::Scoped(RegionDepth::from(1_u32));
    let code = arena.value_variable(
        crate::Zone::Intuitionistic,
        gandr_kernel_term::DeBruijnIndex::from(0_u32),
    );
    let element = arena.value_type_element(code, gandr_kernel_strata::Level::zero());
    let kept = arena.value_type_kept(element, region);
    let argument = arena.value_constant(gandr_kernel_term::ConstantIndex::from(0_usize));
    let rewritten = crate::rewrite::instantiate_value_type(&mut arena, kept, argument);
    assert_ne!(rewritten, kept, "the kept value mentions the binder");
    let Some(&crate::ValueType::Kept {
        value,
        region: lives,
    }) = arena.value_type(rewritten)
    else {
        panic!("a kept type rewrites to a kept type");
    };
    assert_eq!(lives, region, "the region is kept as written");
    assert!(
        matches!(arena.value_type(value), Some(crate::ValueType::Element { code: read, .. })
            if arena.value(*read) == Some(&crate::Value::Constant(gandr_kernel_term::ConstantIndex::from(0_usize)))),
        "the kept value reads the argument"
    );
    let unit = arena.value_type_unit();
    let closed = arena.value_type_kept(unit, region);
    assert_eq!(
        crate::rewrite::instantiate_value_type(&mut arena, closed, argument),
        closed,
        "a kept type that mentions no binder is left as it is"
    );
}
