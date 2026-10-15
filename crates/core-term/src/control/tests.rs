use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;

use super::*;
use crate::CertificateEquality;
use crate::TypeImporter;
use crate::Zone;
use crate::effect::EffectName;
use crate::effect::EffectOp;
use crate::effect::EffectRow;
use crate::equal_certificate_syntax;
use crate::instantiate_value;

#[test]
fn stack_literals_preserve_binder_scope()
{
    let mut arena = CoreArena::new();
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let beneath = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let pair = arena.value_tuple(&[outer, beneath]);
    let bound_body = arena.computation_return(pair);
    let stack = arena.value_reify(Arc::from([
        StackFrame::Apply(outer),
        StackFrame::Bind(bound_body),
        StackFrame::Project(Side::Left),
    ]));
    let unit = arena.value_unit();
    let rewritten = instantiate_value(&mut arena, stack, unit);
    let Value::Reify(ref frames) = *arena.value(rewritten).unwrap()
    else {
        panic!("stack literal")
    };
    let [
        StackFrame::Apply(actual),
        StackFrame::Bind(body),
        StackFrame::Project(side),
    ] = *frames.as_ref()
    else {
        panic!("flat stack frames")
    };
    assert_eq!(actual, unit);
    assert_eq!(side, Side::Left);
    let Computation::Return(pair) = *arena.computation(body).unwrap()
    else {
        panic!("return")
    };
    assert_eq!(arena.value(pair), Some(&Value::Tuple([outer, unit].into())));
    let fed = arena.computation_return(beneath);
    let resumed = arena.computation_resume(outer, fed);
    let shifted = arena.computation_shift(resumed);
    let reset = arena.computation_reset(shifted);
    let thunk = arena.value_thunk(reset);
    let rewritten = instantiate_value(&mut arena, thunk, unit);
    let expected_fed = arena.computation_return(unit);
    let expected_resume = arena.computation_resume(outer, expected_fed);
    let expected_shift = arena.computation_shift(expected_resume);
    let expected_reset = arena.computation_reset(expected_shift);
    let expected = arena.value_thunk(expected_reset);
    assert_eq!(
        equal_certificate_syntax(&arena, rewritten, expected),
        CertificateEquality::Equal
    );
    assert_eq!(
        equal_certificate_syntax(&arena, thunk, expected),
        CertificateEquality::Different
    );
}

/// The index the code of a returner's element type names.
///
/// # Specification
/// trivial.
fn returned_code(
    arena: &CoreArena,
    returner: CompTypeId,
) -> Option<DeBruijnIndex>
{
    let &CompType::Returner { result, .. } = arena.comp_type(returner)?
    else {
        return None;
    };
    let &ValueType::Element { code, .. } = arena.value_type(result)?
    else {
        return None;
    };
    let &Value::Variable { index, .. } = arena.value(code)?
    else {
        return None;
    };
    Some(index)
}

#[test]
fn stack_types_rebuild_both_computation_children()
{
    let mut arena = CoreArena::new();
    let local = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let ambient = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
    let local_type = arena.value_type_element(local, Level::zero());
    let ambient_type = arena.value_type_element(ambient, Level::zero());
    let consumes = arena.comp_type_returner(local_type);
    let delivers = arena.comp_type_returner(ambient_type);
    let stack = arena.value_type_stack(consumes, delivers);
    assert_eq!(
        arena.value_type(stack),
        Some(&ValueType::Stack {
            input: consumes,
            output: delivers,
        })
    );
    let rewritten = crate::instantiate_value_type(&mut arena, stack, argument);
    let Some(&ValueType::Stack { input, output }) = arena.value_type(rewritten)
    else {
        panic!("a stack type stays a stack type")
    };
    assert_eq!(
        returned_code(&arena, input),
        Some(DeBruijnIndex::from(3_u32))
    );
    assert_eq!(
        returned_code(&arena, output),
        Some(DeBruijnIndex::from(0_u32))
    );
}

#[test]
fn lazy_pairs_keep_their_components_and_projection_side()
{
    let mut arena = CoreArena::new();
    let free = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let unit = arena.value_unit();
    let first = arena.computation_return(free);
    let second = arena.computation_return(unit);
    let pair = arena.computation_with(first, second);
    let left = arena.computation_project(Side::Left, pair);
    let right = arena.computation_project(Side::Right, pair);
    assert_eq!(
        arena.computation(pair),
        Some(&Computation::With(first, second))
    );
    assert_eq!(
        arena.computation(left),
        Some(&Computation::Project(Side::Left, pair))
    );
    let flipped = arena.computation_with(second, first);
    let flipped_left = arena.computation_project(Side::Left, flipped);
    let observed_left = arena.value_thunk(left);
    let observed_right = arena.value_thunk(right);
    let observed_flipped = arena.value_thunk(flipped_left);
    for other in [observed_right, observed_flipped] {
        assert_eq!(
            equal_certificate_syntax(&arena, observed_left, other),
            CertificateEquality::Different
        );
    }
    let replacement = arena.value_unit();
    let rewritten = instantiate_value(&mut arena, observed_left, replacement);
    let expected_first = arena.computation_return(replacement);
    let expected_pair = arena.computation_with(expected_first, second);
    let expected_left = arena.computation_project(Side::Left, expected_pair);
    let expected = arena.value_thunk(expected_left);
    assert_eq!(
        equal_certificate_syntax(&arena, rewritten, expected),
        CertificateEquality::Equal
    );
}

#[test]
fn effect_interfaces_and_clauses_rewrite_in_their_own_scopes()
{
    let mut arena = CoreArena::new();
    let variable = |arena: &mut CoreArena, index| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    let free = variable(&mut arena, 0_u32);
    let under_one = variable(&mut arena, 1_u32);
    let under_two = variable(&mut arena, 2_u32);
    let element = arena.value_type_element(free, gandr_kernel_strata::Level::zero());
    let reply = arena.value_type_list(element);
    let signature = EffectSig::new(EffectName::from("Probe"), [EffectOp {
        name: "ask".into(),
        payload: element,
        reply,
    }])
    .unwrap();
    let performed = arena.computation_perform(signature.clone(), "ask".into(), free);
    let returned = arena.computation_return(under_one);
    let pair = arena.value_tuple(&[free, under_two]);
    let clause = arena.computation_return(pair);
    let handled = arena.computation_handle(
        signature,
        performed,
        returned,
        Arc::from([EffectClause {
            operation: "ask".into(),
            body: clause,
        }]),
    );
    let thunk = arena.value_thunk(handled);
    let string = arena.value_type_base(BaseType::String);
    let quote = arena.value_quote(string);
    let rewritten = instantiate_value(&mut arena, thunk, quote);
    let Value::Thunk(body) = *arena.value(rewritten).unwrap()
    else {
        panic!("thunk")
    };
    let Computation::Handle {
        ref signature,
        subject,
        on_return,
        ref clauses,
    } = *arena.computation(body).unwrap()
    else {
        panic!("handler")
    };
    let operation = signature.operations().next().unwrap();
    assert_eq!(operation.payload, string);
    assert_eq!(
        arena.value_type(operation.reply),
        Some(&ValueType::List(string))
    );
    assert_eq!(
        arena.computation(on_return),
        Some(&Computation::Return(quote))
    );
    let Computation::Perform {
        ref signature,
        payload,
        ..
    } = *arena.computation(subject).unwrap()
    else {
        panic!("perform")
    };
    assert_eq!(payload, quote);
    assert_eq!(signature.operations().next().unwrap().payload, string);
    let Computation::Return(pair) = *arena.computation(clauses[0].body).unwrap()
    else {
        panic!("clause")
    };
    assert_eq!(arena.value(pair), Some(&Value::Tuple([free, quote].into())));
}

#[test]
fn a_capability_scope_binds_its_subject_once()
{
    use crate::effect::capability::CapabilityGrade;
    use crate::effect::capability::Region;
    use crate::effect::capability::RegionDepth;

    let mut arena = CoreArena::new();
    let variable = |arena: &mut CoreArena, index| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    let free = variable(&mut arena, 0_u32);
    let under_one = variable(&mut arena, 1_u32);
    let under_two = variable(&mut arena, 2_u32);
    let element = arena.value_type_element(free, Level::zero());
    let unit = arena.value_type_unit();
    let signature = EffectSig::new(EffectName::from("Probe"), [EffectOp {
        name: "ask".into(),
        payload: element,
        reply: unit,
    }])
    .unwrap();
    let exercised = arena.computation_exercise(free, signature.clone(), "ask".into(), under_one);
    let returned = arena.computation_return(under_one);
    let pair = arena.value_tuple(&[free, under_two]);
    let clause = arena.computation_return(pair);
    let scoped = arena.computation_scope(
        signature,
        exercised,
        returned,
        Arc::from([EffectClause {
            operation: "ask".into(),
            body: clause,
        }]),
    );
    let thunk = arena.value_thunk(scoped);
    let string = arena.value_type_base(BaseType::String);
    let quote = arena.value_quote(string);
    let rewritten = instantiate_value(&mut arena, thunk, quote);
    let Value::Thunk(body) = *arena.value(rewritten).unwrap()
    else {
        panic!("thunk")
    };
    let Computation::Scope {
        ref signature,
        subject,
        on_return,
        ref clauses,
    } = *arena.computation(body).unwrap()
    else {
        panic!("capability scope")
    };
    assert_eq!(signature.operations().next().unwrap().payload, string);
    let Computation::Exercise {
        capability,
        payload,
        ..
    } = *arena.computation(subject).unwrap()
    else {
        panic!("exercise")
    };
    assert_eq!(capability, free, "the scope's own capability is bound");
    assert_eq!(
        payload, quote,
        "the subject sees the replacement one deeper"
    );
    assert_eq!(
        arena.computation(on_return),
        Some(&Computation::Return(quote))
    );
    let Computation::Return(pair) = *arena.computation(clauses[0].body).unwrap()
    else {
        panic!("clause")
    };
    assert_eq!(arena.value(pair), Some(&Value::Tuple([free, quote].into())));
    let swapped = arena.computation_exercise(under_one, signature.clone(), "ask".into(), free);
    let original = arena.value_thunk(exercised);
    let swapped = arena.value_thunk(swapped);
    assert_eq!(
        equal_certificate_syntax(&arena, original, swapped),
        CertificateEquality::Different
    );

    let scoped_region = Region::Scoped(RegionDepth::from(1_u32));
    let authority = EffectRow::singleton(
        EffectSig::new(EffectName::from("Probe"), [EffectOp {
            name: "ask".into(),
            payload: element,
            reply: unit,
        }])
        .unwrap(),
    );
    let capability =
        arena.value_type_capability(authority, CapabilityGrade::Durable, scoped_region);
    let rewritten = crate::instantiate_value_type(&mut arena, capability, quote);
    let Some(&ValueType::Capability {
        ref authority,
        grade,
        region,
    }) = arena.value_type(rewritten)
    else {
        panic!("a capability type stays a capability type")
    };
    assert_eq!((grade, region), (CapabilityGrade::Durable, scoped_region));
    let granted = authority
        .signatures()
        .next()
        .unwrap()
        .operations()
        .next()
        .unwrap();
    assert_eq!(granted.payload, string);
    let build = |arena: &mut CoreArena| {
        let unit = arena.value_type_unit();
        let strings = arena.value_type_base(BaseType::String);
        let authority = EffectRow::singleton(
            EffectSig::new(EffectName::from("Probe"), [EffectOp {
                name: "ask".into(),
                payload: strings,
                reply: unit,
            }])
            .unwrap(),
        );
        arena.value_type_capability(authority, CapabilityGrade::Consumable, Region::Held)
    };
    let mut source = CoreArena::new();
    let root = build(&mut source);
    let mut target = CoreArena::new();
    let _occupied = target.value_type_unit();
    let imported = TypeImporter::new(&source, &mut target)
        .value_type(root)
        .unwrap();
    let expected = build(&mut target);
    let held =
        target.value_type_capability(EffectRow::EMPTY, CapabilityGrade::Consumable, Region::Held);
    let [imported, expected, held] = [imported, expected, held].map(|ty| target.value_quote(ty));
    assert_eq!(
        equal_certificate_syntax(&target, imported, expected),
        CertificateEquality::Equal
    );
    assert_eq!(
        equal_certificate_syntax(&target, imported, held),
        CertificateEquality::Different,
        "authority participates in syntax equality"
    );
}

#[test]
fn effect_and_stack_annotations_import_without_foreign_handles()
{
    let build = |arena: &mut CoreArena| {
        let unit = arena.value_type_unit();
        let strings = arena.value_type_base(BaseType::String);
        let list = arena.value_type_list(strings);
        let signature = EffectSig::new(EffectName::from("Probe"), [EffectOp {
            name: "ask".into(),
            payload: unit,
            reply: list,
        }])
        .unwrap();
        let input = arena.comp_type_returner_with_effects(list, EffectRow::singleton(signature));
        let pure = arena.comp_type_returner(unit);
        let output = arena.comp_type_with(pure, input);
        arena.value_type_stack(input, output)
    };
    let mut source = CoreArena::new();
    let root = build(&mut source);
    let mut target = CoreArena::new();
    for _ in 0_u32 .. 17_u32 {
        let _ = target.value_type_unit();
    }
    let imported = TypeImporter::new(&source, &mut target)
        .value_type(root)
        .unwrap();
    let expected = build(&mut target);
    let imported = target.value_quote(imported);
    let expected = target.value_quote(expected);
    assert_eq!(
        equal_certificate_syntax(&target, imported, expected),
        CertificateEquality::Equal
    );
}
