use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::equal_certificate_syntax;

use super::CompileFault;
use super::compile_value;
use crate::overlay::Bound;
use crate::overlay::Overlay;
use crate::overlay::OverlayId;
use crate::overlay::ShareArity;
use crate::overlay::ShareDistance;
use crate::overlay::SharePosition;
use crate::overlay::Sharing;
use crate::overlay::ValueGraft;
use crate::overlay::ValueNode;
use crate::overlay::erase_value;

#[test]
fn a_node_reached_twice_is_one_share_of_two_occurrences()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let pair = core.value_tuple(&[unit, unit]);
    let mut overlay = Overlay::new();
    let root = compile_value(&mut overlay, &core, pair).expect("a pair of one unit compiles");
    assert_eq!(Ok(()), overlay.validate(OverlayId::Value(root)));
    let Some(&ValueNode::Shared(Sharing { arity, leg, body })) = overlay.value(root)
    else {
        panic!("the root is the share of the unit");
    };
    assert_eq!(
        ShareArity::from(2_u32),
        arity,
        "both reaches are occurrences"
    );
    let OverlayId::Value(leg) = leg
    else {
        panic!("the leg is a value");
    };
    assert_eq!(
        Some(&ValueNode::Grafted(ValueGraft::Unit)),
        overlay.value(leg)
    );
    let Some(&ValueNode::Grafted(ValueGraft::Pair(first, second))) = overlay.value(body)
    else {
        panic!("the body is the pair");
    };
    let occurrence = |position: u32| {
        ValueNode::Bound(Bound {
            distance: ShareDistance::from(0_u32),
            position: SharePosition::from(position),
        })
    };
    assert_eq!(
        [Some(&occurrence(0)), Some(&occurrence(1))],
        [overlay.value(first), overlay.value(second)],
        "the components are the share's occurrences in preorder"
    );
    let erased = erase_value(&overlay, root, &mut core).expect("the compiled root erases");
    assert_eq!(
        CertificateEquality::Equal,
        equal_certificate_syntax(&core, erased, pair),
        "the compiled root erases to its input"
    );
}

#[test]
fn a_node_that_names_nothing_is_refused_and_mints_nothing()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let pair = core.value_tuple(&[unit, unit]);
    let mut other = core.clone();
    let dangling: ValueId = other.value_unit();
    let mut overlay = Overlay::new();
    let entry = overlay.watermark();
    assert_eq!(
        Err(CompileFault::Dangling),
        compile_value(&mut overlay, &core, dangling),
        "a root the arena does not hold is refused"
    );
    assert_eq!(entry, overlay.watermark(), "and the refusal mints nothing");
    let root = compile_value(&mut overlay, &core, pair).expect("a held root compiles");
    assert_eq!(Ok(()), overlay.validate(OverlayId::Value(root)));
}
