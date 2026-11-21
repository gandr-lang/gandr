use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;

use super::CompTypeView;
use super::FragmentRefusal;
use super::ValueTypeView;
use super::comp_type_view;
use super::value_type_view;
use crate::refusal::CoreNode;
use crate::refusal::TypeNode;

#[test]
fn the_unknown_type_and_the_decode_of_a_hole_view_alike()
{
    let mut arena = CoreArena::new();
    let hole = arena.value_hole(HoleId::from(0_u32));
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let unknown = arena.value_type_unknown();
    let decoded_hole = arena.value_type_element(hole, Level::zero());
    let decoded_variable = arena.value_type_element(variable, Level::zero());
    let unknown_computation = arena.comp_type_unknown();
    let decoded_hole_computation = arena.comp_type_element(hole, Level::zero());
    let decoded_variable_computation = arena.comp_type_element(variable, Level::zero());
    assert_eq!(value_type_view(&arena, unknown), Ok(ValueTypeView::Unknown));
    assert_eq!(
        value_type_view(&arena, decoded_hole),
        Ok(ValueTypeView::Unknown),
        "the decode of a hole is the unknown type"
    );
    assert!(
        matches!(value_type_view(&arena, decoded_variable), Ok(ValueTypeView::Element { code, .. }) if code == variable),
        "the decode of a variable stays a decode"
    );
    assert_eq!(
        comp_type_view(&arena, unknown_computation),
        Ok(CompTypeView::Unknown)
    );
    assert_eq!(
        comp_type_view(&arena, decoded_hole_computation),
        Ok(CompTypeView::Unknown)
    );
    assert!(matches!(
        comp_type_view(&arena, decoded_variable_computation),
        Ok(CompTypeView::Element { code, .. }) if code == variable
    ));
}

#[test]
fn both_views_refuse_ids_missing_from_their_arena()
{
    let mut producer = CoreArena::new();
    let value_type = producer.value_type_unit();
    let comp_type = producer.comp_type_returner(value_type);
    let empty = CoreArena::new();
    assert_eq!(
        value_type_view(&empty, value_type),
        Err(FragmentRefusal::DanglingNode {
            node: CoreNode::Type(TypeNode::Value(value_type)),
        })
    );
    assert_eq!(
        comp_type_view(&empty, comp_type),
        Err(FragmentRefusal::DanglingNode {
            node: CoreNode::Type(TypeNode::Computation(comp_type)),
        })
    );
}

#[test]
fn products_and_sums_view_at_every_arity()
{
    let mut arena = CoreArena::new();
    let a = arena.value_type_unit();
    let b = arena.value_type_list(a);
    let c = arena.value_type_unknown();
    let unit = arena.value_type_product(&[]);
    let pair = arena.value_type_product(&[a, b]);
    let single = arena.value_type_product(&[a]);
    let triple = arena.value_type_product(&[a, b, c]);
    let either = arena.value_type_sum(&[b, a]);
    let empty = arena.value_type_sum(&[]);
    let three = arena.value_type_sum(&[a, b, c]);
    assert_eq!(value_type_view(&arena, unit), Ok(ValueTypeView::Unit));
    assert_eq!(
        value_type_view(&arena, pair),
        Ok(ValueTypeView::Product(&[a, b]))
    );
    assert_eq!(
        value_type_view(&arena, either),
        Ok(ValueTypeView::Sum(&[b, a])),
        "the summands keep their order"
    );
    assert_eq!(
        value_type_view(&arena, single),
        Ok(ValueTypeView::Product(&[a]))
    );
    assert_eq!(
        value_type_view(&arena, triple),
        Ok(ValueTypeView::Product(&[a, b, c]))
    );
    assert_eq!(
        value_type_view(&arena, empty),
        Ok(ValueTypeView::Sum(&[])),
        "the empty sum is the empty type"
    );
    assert_eq!(
        value_type_view(&arena, three),
        Ok(ValueTypeView::Sum(&[a, b, c]))
    );
}
