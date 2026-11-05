use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::ValueTypeId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::Departure;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::GroundSort;

use super::signature;
use crate::fixture::signature_parts as parts;

/// The holder's admission position in every case.
const HOLDER: usize = 0;

/// The signature over `parameters` with the constructors `constructors`.
///
/// # Specification
/// trivial.
fn signed(
    arena: &mut CoreArena,
    parameters: Vec<ValueTypeId>,
    constructors: Vec<Vec<ValueTypeId>>,
) -> DataSignature
{
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    DataSignature::new(parameters, constructors, kind)
}

/// The departure at field `field` of constructor `tag`.
///
/// # Specification
/// trivial.
fn at(
    tag: ConstructorTag,
    field: FieldPosition,
) -> Departure
{
    Departure::Field { tag, field }
}

#[test]
fn the_canonical_signature_type_is_admitted_5254()
{
    let mut arena = CoreArena::new();
    let holder = ConstantIndex::from(HOLDER);
    let [parameters, iota, sigma, delta] = parts(&mut arena, holder);
    let canonical = signed(&mut arena, parameters, Vec::from([iota, sigma, delta]));
    assert_eq!(signature(&arena, holder, &canonical), Ok(()));
}

#[test]
fn a_signature_type_is_refused_at_its_first_departure_5254()
{
    let mut arena = CoreArena::new();
    let holder = ConstantIndex::from(HOLDER);
    let [parameters, iota, sigma, delta] = parts(&mut arena, holder);
    let swapped = signed(
        &mut arena,
        parameters.clone(),
        Vec::from([iota.clone(), delta.clone(), sigma.clone()]),
    );
    assert_eq!(
        signature(&arena, holder, &swapped),
        Err(at(
            ConstructorTag::from(1_usize),
            FieldPosition::from(1_usize)
        )),
        "σ and δ in the other order depart at σ's place, whose function reads no decode"
    );
    let mut wider = parameters.clone();
    wider.extend(parameters.iter().copied());
    let wider = signed(
        &mut arena,
        wider,
        Vec::from([iota.clone(), sigma.clone(), delta.clone()]),
    );
    assert_eq!(
        signature(&arena, holder, &wider),
        Err(Departure::Parameters),
        "a second parameter departs at the telescope"
    );
    let short = signed(
        &mut arena,
        parameters.clone(),
        Vec::from([iota.clone(), sigma.clone()]),
    );
    assert_eq!(
        signature(&arena, holder, &short),
        Err(Departure::Constructors),
        "two constructors depart at the table"
    );
    let truncated = signed(
        &mut arena,
        parameters.clone(),
        Vec::from([iota.clone(), sigma.clone(), Vec::from(&delta[.. 1])]),
    );
    assert_eq!(
        signature(&arena, holder, &truncated),
        Err(Departure::Arity(ConstructorTag::from(2_usize))),
        "a δ of one field departs at its arity"
    );
    let typed = signed(
        &mut arena,
        parameters.clone(),
        Vec::from([Vec::from([parameters[0]]), sigma, delta.clone()]),
    );
    assert_eq!(
        signature(&arena, holder, &typed),
        Err(at(
            ConstructorTag::from(0_usize),
            FieldPosition::from(0_usize)
        )),
        "an ι whose field is a universe departs at that field"
    );
    let [_, _, foreign, _] = parts(&mut arena, ConstantIndex::from(7_usize));
    let elsewhere = signed(&mut arena, parameters, Vec::from([iota, foreign, delta]));
    assert_eq!(
        signature(&arena, holder, &elsewhere),
        Err(at(
            ConstructorTag::from(1_usize),
            FieldPosition::from(1_usize)
        )),
        "a σ whose function returns another family departs at that field"
    );
}
