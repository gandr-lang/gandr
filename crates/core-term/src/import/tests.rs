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
}
