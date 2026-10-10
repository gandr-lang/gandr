//! Image boundaries and independent wire goldens.

use gandr_runtime_compile_host::image::BinderIndex;
use gandr_runtime_compile_host::image::CtorTag;
use gandr_runtime_compile_host::image::DispatchPresence;
use gandr_runtime_compile_host::image::Image;
use gandr_runtime_compile_host::image::ImageError;
use gandr_runtime_compile_host::image::Literal;
use gandr_runtime_compile_host::image::MAX_IMAGE_NODES;
use gandr_runtime_compile_host::image::Node;
use gandr_runtime_compile_host::image::NodeKind;

/// A literal or structural node without operands.
///
/// # Specification
/// trivial.
pub fn leaf(kind: NodeKind) -> Node
{
    Node {
        kind,
        tag: CtorTag::Unit,
        binder: BinderIndex::default(),
        literal: Literal::default(),
        operands: Vec::new(),
    }
}
#[test]
fn the_arena_refuses_a_node_past_the_declared_bound()
{
    let mut image = Image::new();
    for position in 0 .. MAX_IMAGE_NODES {
        assert_eq!(
            u32::from(image.push(leaf(NodeKind::Lit)).expect("fits")),
            u32::try_from(position).expect("small")
        );
    }
    let before = image.encode();
    assert_eq!(
        image.push(leaf(NodeKind::Lit)),
        Err(ImageError::TooManyNodes)
    );
    assert_eq!(image.encode(), before);
}
#[test]
fn the_wire_form_leads_with_its_version_and_node_count()
{
    let mut image = Image::new();
    let node = Node {
        literal: Literal::from(-7_i64),
        ..leaf(NodeKind::Lit)
    };
    let literal = image.push(node).expect("literal");
    image
        .push(Node {
            operands: vec![literal],
            ..leaf(NodeKind::Cut)
        })
        .expect("cut");
    assert_eq!(image.encode().as_ref(), &[
        1, 2, 0, 0, 0, 0, 0, 0, 0, 249, 255, 255, 255, 255, 255, 255, 255, 0, 7, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    ]);
}
#[test]
fn accounted_work_counts_each_kind_separately()
{
    let mut image = Image::new();
    for kind in [NodeKind::Dup, NodeKind::Dup, NodeKind::Drop] {
        image.push(leaf(kind)).expect("fits");
    }
    let work = image.accounted_work();
    assert_eq!(
        (i64::from(work.duplications), i64::from(work.discards)),
        (2, 1)
    );
    assert_eq!(image.has_dispatch(), DispatchPresence::Absent);
    image.push(leaf(NodeKind::Case)).expect("case");
    assert_eq!(image.has_dispatch(), DispatchPresence::Present);
    assert_eq!(image.accounted_work(), work);
}
#[test]
fn unencodable_operands_preserve_the_arena()
{
    let mut image = Image::new();
    let zero = image.push(leaf(NodeKind::Lit)).expect("literal");
    let before = image.encode();
    assert_eq!(
        image.push(Node {
            operands: vec![zero; 256],
            ..leaf(NodeKind::Ctor)
        }),
        Err(ImageError::TooManyOperands)
    );
    assert_eq!(image.encode(), before);
    let future = 1_u32.into();
    assert_eq!(
        image.push(Node {
            operands: vec![future],
            ..leaf(NodeKind::Cut)
        }),
        Err(ImageError::ForwardOperand(future))
    );
    assert_eq!(image.encode(), before);
    image
        .push(Node {
            operands: vec![zero; 255],
            ..leaf(NodeKind::Ctor)
        })
        .expect("one byte of operands");
    assert_eq!(image.encode().as_ref().get(32), Some(&255));
}
