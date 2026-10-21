use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;

use super::*;

#[test]
fn dependent_annotations_preserve_sharing_across_arenas()
{
    let mut source = CoreArena::new();
    let variable = source.value_variable(crate::Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let dependent = source.value_type_element(variable, Level::zero());
    let list = source.value_type_list(dependent);
    let pair = source.value_type_product(&[list, list]);
    let mut target = CoreArena::new();
    let unit = target.value_type_unit();
    let _occupied = target.value_quote(unit);
    let mut importer = TypeImporter::new(&source, &mut target);
    let copied = importer.value_type(pair).expect("source graph resolves");
    let list_image = importer.value_type(list).expect("shared child is imported");
    assert_eq!(
        importer.target.value_type(copied),
        Some(&ValueType::Product([list_image, list_image].into()))
    );
    let ValueType::List(element) = *importer.target.value_type(list_image).expect("list")
    else {
        panic!("native list");
    };
    let ValueType::Element { code, .. } = *importer.target.value_type(element).expect("element")
    else {
        panic!("dependent element");
    };
    assert_eq!(
        importer.target.value(code),
        Some(&Value::Variable {
            zone: crate::Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32)
        })
    );
    assert_eq!(importer.target.value(variable), Some(&Value::Quote(unit)));
}

#[test]
fn an_imported_arrow_answers_its_image()
{
    let mut source = CoreArena::new();
    let universe = source.value_type_unit();
    let variable = source.value_variable(crate::Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let dependent = source.value_type_element(variable, Level::zero());
    let returner = source.comp_type_returner(dependent);
    let arrow = source.comp_type_pi(universe, returner);
    let thunk = source.value_type_thunk(arrow);
    let unreached = source.comp_type_returner(universe);
    let unlisted = source.value_type_list(universe);
    let mut target = CoreArena::new();
    let _occupied = target.value_type_unit();
    let mut importer = TypeImporter::new(&source, &mut target);
    assert_eq!(
        importer.comp_type_image(arrow),
        None,
        "nothing is imported yet"
    );
    let copied = importer.value_type(thunk).expect("source graph resolves");
    let Some(&ValueType::Thunk(image)) = importer.target.value_type(copied)
    else {
        panic!("a thunk");
    };
    assert_eq!(
        importer.comp_type_image(arrow),
        Some(image),
        "the arrow answers its image"
    );
    assert_eq!(
        importer.comp_type_image(unreached),
        None,
        "a node no import reached answers none"
    );
    assert_eq!(
        importer.value_type_image(thunk),
        Some(copied),
        "the root answers its image"
    );
    let Some(&CompType::Pi { codomain, .. }) = importer.target.comp_type(image)
    else {
        panic!("a dependent arrow");
    };
    let Some(&CompType::Returner { result, .. }) = importer.target.comp_type(codomain)
    else {
        panic!("a returner");
    };
    assert_eq!(
        importer.value_type_image(dependent),
        Some(result),
        "a value type inside the root answers its image"
    );
    assert_eq!(
        importer.value_type_image(unlisted),
        None,
        "a value type no import reached answers none"
    );
}

#[test]
fn an_imported_code_keeps_its_type()
{
    let mut source = CoreArena::new();
    let unit = source.value_type_unit();
    let list = source.value_type_list(unit);
    let code = source.value_quote(list);
    let mut target = CoreArena::new();
    let occupied = target.value_type_unit();
    let _shifted = target.value_type_list(occupied);
    let mut importer = TypeImporter::new(&source, &mut target);
    let copied = importer.value(code).expect("source graph resolves");
    let list_image = importer
        .value_type_image(list)
        .expect("the quoted type is imported");
    assert_eq!(
        importer.target.value(copied),
        Some(&Value::Quote(list_image)),
        "the code quotes the image of its type"
    );
    let Some(&ValueType::List(element)) = importer.target.value_type(list_image)
    else {
        panic!("a native list");
    };
    assert!(
        matches!(importer.target.value_type(element), Some(&ValueType::Product(ref parts)) if parts.is_empty()),
        "the quoted type keeps its element, the unit"
    );
}

/// `Path((), ⟨stack, run, handler, chooser⟩, ())`: a type whose endpoint
/// holds a stack of an application and a bind, a recorded send, a handler
/// with one clause and a case of two branches, every one of them over values
/// and computations of its own.
///
/// # Specification
/// trivial.
fn spelled(arena: &mut CoreArena) -> ValueTypeId
{
    use alloc::sync::Arc;

    use crate::control::EffectClause;
    use crate::control::StackFrame;
    use crate::effect::EffectName;
    use crate::effect::EffectOp;
    use crate::effect::EffectSig;
    use crate::effect::OperationName;
    use crate::session::RecordedMove;

    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let nil = arena.value_list_nil();
    let returned = arena.computation_return(nil);
    let stack = arena.value_reify(Arc::from([
        StackFrame::Apply(nil),
        StackFrame::Bind(returned),
    ]));
    let run = arena.value_recorded(Arc::from([RecordedMove::Sent(nil)]));
    let signature = EffectSig::new(EffectName::from("Probe"), [EffectOp {
        name: OperationName::from("ask"),
        payload: unit_type,
        reply: unit_type,
    }])
    .expect("one operation");
    let answer = arena.computation_return(unit);
    let handled = arena.computation_handle(
        signature,
        returned,
        returned,
        Arc::from([EffectClause {
            operation: OperationName::from("ask"),
            body: answer,
        }]),
    );
    let handler = arena.value_thunk(handled);
    let chosen = arena.computation_case(nil, &[answer, returned]);
    let chooser = arena.value_thunk(chosen);
    let endpoint = arena.value_tuple(&[stack, run, handler, chooser]);
    arena.value_type_path(unit_type, endpoint, unit)
}

#[test]
fn an_imported_endpoint_maps_every_stack_frame_move_and_clause()
{
    let mut source = CoreArena::new();
    let root = spelled(&mut source);
    let mut target = CoreArena::new();
    let unit = target.value_type_unit();
    // Every family is occupied, so no image shares its source's id.
    for _ in 0_u8 .. 4 {
        let quoted = target.value_quote(unit);
        let returned = target.computation_return(quoted);
        let _occupied = target.comp_type_returner(unit);
        let _thunk = target.value_thunk(returned);
    }
    let copied = TypeImporter::new(&source, &mut target)
        .value_type(root)
        .expect("source graph resolves");
    let twin = spelled(&mut target);
    assert_eq!(
        crate::CertificateEquality::Equal,
        crate::equal_type_syntax(&target, copied, twin),
        "the image reads as the same spelling written in the target"
    );
}

/// Every former the rewrite witnesses, read through a decode, imports into
/// an arena whose families are all occupied as the same spelling written
/// there: each child edge of every family is relocated to its image.
#[test]
fn every_former_imports_as_its_own_spelling()
{
    use gandr_kernel_term::ConstantIndex;

    use crate::rewrite::tests::Witnessed;
    use crate::rewrite::tests::formers;

    for Witnessed { what, former } in formers() {
        let mut source = CoreArena::new();
        let child = source.value_constant(ConstantIndex::from(7_usize));
        let code = former(&mut source, child);
        let root = source.value_type_element(code, Level::zero());
        let mut target = CoreArena::new();
        let unit = target.value_type_unit();
        // Every family is occupied, so no image shares its source's id.
        for _ in 0_u8 .. 4 {
            let quoted = target.value_quote(unit);
            let returned = target.computation_return(quoted);
            let _occupied = target.comp_type_returner(unit);
            let _thunk = target.value_thunk(returned);
        }
        let copied = TypeImporter::new(&source, &mut target)
            .value_type(root)
            .unwrap_or_else(|ImportFault| panic!("{what}: the source graph resolves"));
        let child = target.value_constant(ConstantIndex::from(7_usize));
        let code = former(&mut target, child);
        let twin = target.value_type_element(code, Level::zero());
        assert_eq!(
            crate::CertificateEquality::Equal,
            crate::equal_type_syntax(&target, copied, twin),
            "{what}: the image reads as the same spelling written in the target"
        );
    }
}
