use quenchant_shape::shape::Maybe;

use super::Region;
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
use crate::effect::RowInclusion;
use crate::effect::host::HostSignatures;

#[test]
fn a_region_outlives_only_regions_nested_in_it()
{
    let outer = Region::Scoped(RegionDepth::from(1_u32));
    let inner = Region::Scoped(RegionDepth::from(2_u32));
    for (first, second, expected) in [
        (Region::Held, Region::Held, RegionOrder::Outlives),
        (Region::Held, outer, RegionOrder::Outlives),
        (outer, Region::Held, RegionOrder::EndsFirst),
        (outer, inner, RegionOrder::Outlives),
        (inner, outer, RegionOrder::EndsFirst),
        (inner, inner, RegionOrder::Outlives),
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
        matches!(both.granted(host.fs.name(), &write), Maybe::Present(operation) if operation.name == write)
    );
    assert_eq!(
        reads.granted(host.fs.name(), &write),
        Maybe::Absent(grant::Absent::Operation)
    );
    assert_eq!(
        reads.granted(host.proc.name(), &OperationName::from("exit")),
        Maybe::Absent(grant::Absent::Interface)
    );
    assert_eq!(
        EffectRow::authority(&[host.fs.clone(), host.fs.clone()]),
        Err(crate::effect::EffectConflict::Signature(
            host.fs.name().clone()
        ))
    );
    let joined = EffectRow::authority(&[host.proc.clone(), host.fs]).expect("two");
    assert_eq!(joined.signatures().len(), 2);
    assert_eq!(both.grants_within(&joined, &arena), RowInclusion::Included);
}

#[test]
fn a_kept_type_keeps_its_region_across_substitution()
{
    let mut arena = CoreArena::default();
    let region = RegionDepth::from(1_u32);
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
