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

use super::answers;
use super::pair;
use super::signature;
use crate::Checker;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::fixture::pair_parts;
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

#[test]
fn the_canonical_pair_type_is_admitted_5255()
{
    let mut arena = CoreArena::new();
    let [parameters, fields] = pair_parts(&mut arena);
    let canonical = signed(&mut arena, parameters, Vec::from([fields]));
    assert_eq!(pair(&arena, &canonical), Ok(()));
}

#[test]
fn a_pair_type_is_refused_at_its_first_departure_5255()
{
    let mut arena = CoreArena::new();
    let [parameters, fields] = pair_parts(&mut arena);
    let first_field =
        |position: usize| at(ConstructorTag::from(0_usize), FieldPosition::from(position));
    let swapped = signed(
        &mut arena,
        parameters.clone(),
        Vec::from([Vec::from([fields[1], fields[0]])]),
    );
    assert_eq!(
        pair(&arena, &swapped),
        Err(first_field(0)),
        "the fields in the other order depart at the first, which reads no `A`"
    );
    let plain = signed(
        &mut arena,
        parameters.clone(),
        Vec::from([Vec::from([fields[0], fields[0]])]),
    );
    assert_eq!(
        pair(&arena, &plain),
        Err(first_field(1)),
        "a second field of the first type departs at the second field"
    );
    let mut wider = parameters.clone();
    wider.push(parameters[0]);
    let wider = signed(&mut arena, wider, Vec::from([fields.clone()]));
    assert_eq!(
        pair(&arena, &wider),
        Err(Departure::Parameters),
        "a third parameter departs at the telescope"
    );
    let flat = signed(
        &mut arena,
        Vec::from([parameters[0], parameters[0]]),
        Vec::from([fields.clone()]),
    );
    assert_eq!(
        pair(&arena, &flat),
        Err(Departure::Parameters),
        "a second parameter that is no family over the first departs at the telescope"
    );
    let doubled = signed(
        &mut arena,
        parameters.clone(),
        Vec::from([fields.clone(), fields.clone()]),
    );
    assert_eq!(
        pair(&arena, &doubled),
        Err(Departure::Constructors),
        "a second constructor departs at the table"
    );
    let short = signed(
        &mut arena,
        parameters,
        Vec::from([Vec::from(&fields[.. 1])]),
    );
    assert_eq!(
        pair(&arena, &short),
        Err(Departure::Arity(ConstructorTag::from(0_usize))),
        "a constructor of one field departs at its arity"
    );
}

#[test]
fn a_holder_of_e_is_refused_at_its_first_departing_answer_5255()
{
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::Builtin;

    let mut arena = CoreArena::new();
    let codes = alloc::sync::Arc::new(crate::fixture::canonical_signature(
        &mut arena,
        ConstantIndex::from(0_usize),
    ));
    let pairs = alloc::sync::Arc::new(crate::fixture::canonical_pair(&mut arena));
    // `λ O c X t. return Integer`: a unit type at no constructor.
    let integer = arena.value_type_base(BaseType::Integer);
    let integer = arena.value_quote(integer);
    let constant = arena.computation_return(integer);
    let curried = (0_u32 .. 4_u32).fold(constant, |body, _| arena.computation_lambda(body));
    let defined = arena.value_thunk(curried);
    let holder = ConstantIndex::from(2_usize);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT, &Checker);
    assert_eq!(
        context.claim_builtin(
            ConstantIndex::from(0_usize),
            Builtin::IrSignature,
            &crate::DeclarationContent::Data(codes)
        ),
        Ok(())
    );
    assert_eq!(
        answers(&mut context, Builtin::IrArgs, (holder, defined)),
        Err(Departure::Reads(Builtin::IrPair)),
        "`E` reads the pair type, which no declaration holds yet"
    );
    assert_eq!(
        context.claim_builtin(
            ConstantIndex::from(1_usize),
            Builtin::IrPair,
            &crate::DeclarationContent::Data(pairs)
        ),
        Ok(())
    );
    assert_eq!(
        answers(&mut context, Builtin::IrDecode, (holder, defined)),
        Err(Departure::Reads(Builtin::IrArgs)),
        "`F` reads `E`, which no declaration holds yet"
    );
    assert_eq!(
        answers(&mut context, Builtin::IrArgs, (holder, defined)),
        Err(Departure::Answer(ConstructorTag::from(0_usize))),
        "an answer of `Integer` at `ι` departs from the unit type there"
    );
}
