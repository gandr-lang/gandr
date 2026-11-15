use alloc::string::String;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;

use super::Bound;
use super::CompGraft;
use super::CompNode;
use super::CompTypeGraft;
use super::CompTypeNode;
use super::EraseFault;
use super::Overlay;
use super::OverlayCompId;
use super::OverlayCompTypeId;
use super::OverlayFamily;
use super::OverlayFault;
use super::OverlayId;
use super::OverlayRefusal;
use super::OverlayValueId;
use super::OverlayValueTypeId;
use super::OverlayWatermark;
use super::ShareArity;
use super::ShareDistance;
use super::SharePosition;
use super::Sharing;
use super::ValueGraft;
use super::ValueNode;
use super::ValueTypeGraft;
use super::ValueTypeNode;
use super::erase_comp_type;
use super::erase_computation;
use super::erase_value;
use super::erase_value_type;

/// A grafted unit value.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a fresh value leaf.
/// - provides: the legs and leaves the validation witnesses share.
/// - panics: when a leaf mint is refused, which only the id ceiling causes.
///
/// # Adequacy
/// - hypothesis: L3 — the fixture mints a fresh node with exactly the supplied
///   scope or child metadata. Validation distinguishes open and closed scopes,
///   ordered positions and implicit reuse; erasure observes the resulting
///   constructors rather than merely successful allocation.
/// - witness: `overlay::tests::validation_refuses_a_node_reached_twice`
/// - witness: `overlay::tests::erasure_mints_every_former_of_every_family_in_order`
#[spec(
        captures: [length = overlay.values.len()],
        ensures: |ret| usize::try_from(ret.0).ok() == Some(length) && length.checked_add(1) == Some(overlay.values.len()) && overlay.value(ret) == Some(&ValueNode::Grafted(ValueGraft::Unit))
    )]
fn unit(overlay: &mut Overlay) -> OverlayValueId
{
    overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Unit))
        .expect("a leaf names no child")
}

/// A value occurrence `distance` shares out, at `position`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a fresh value occurrence.
/// - provides: the occurrences the validation witnesses place.
/// - panics: when a leaf mint is refused, which only the id ceiling causes.
///
/// # Adequacy
/// - hypothesis: L3 — the fixture mints a fresh node with exactly the supplied
///   scope or child metadata. Validation distinguishes open and closed scopes,
///   ordered positions and implicit reuse; erasure observes the resulting
///   constructors rather than merely successful allocation.
/// - witness: `overlay::tests::validation_refuses_an_open_node_set_by_name`
/// - witness: `overlay::tests::validation_holds_each_share_to_its_arity_in_preorder`
#[spec(
        captures: [length = overlay.values.len()],
        ensures: |ret| usize::try_from(ret.0).ok() == Some(length) && length.checked_add(1) == Some(overlay.values.len()) && overlay.value(ret) == Some(&ValueNode::Bound(Bound{distance,position}))
    )]
fn occurrence(
    overlay: &mut Overlay,
    distance: ShareDistance,
    position: SharePosition,
) -> OverlayValueId
{
    overlay
        .mint_value(ValueNode::Bound(Bound { distance, position }))
        .expect("an occurrence names no child")
}

/// A value share of `leg` among `arity` occurrences in `body`.
///
/// # Specification
/// - requires: `leg` and `body` resolve in `overlay`.
/// - ensures: a fresh value share.
/// - provides: the shares the validation witnesses build.
/// - panics: when the mint is refused, which the requirement excludes.
///
/// # Adequacy
/// - hypothesis: L3 — the fixture mints a fresh node with exactly the supplied
///   scope or child metadata. Validation distinguishes open and closed scopes,
///   ordered positions and implicit reuse; erasure observes the resulting
///   constructors rather than merely successful allocation.
/// - witness: `overlay::tests::validation_holds_each_share_to_its_arity_in_preorder`
/// - witness: `overlay::tests::a_leg_counts_from_outside_its_share`
#[spec(
        captures: [length = overlay.values.len()],
        ensures: |ret| usize::try_from(ret.0).ok() == Some(length) && length.checked_add(1) == Some(overlay.values.len()) && overlay.value(ret) == Some(&ValueNode::Shared(Sharing{arity,leg,body}))
    )]
fn share(
    overlay: &mut Overlay,
    arity: ShareArity,
    leg: OverlayId,
    body: OverlayValueId,
) -> OverlayValueId
{
    overlay
        .mint_value(ValueNode::Shared(Sharing { arity, leg, body }))
        .expect("the leg and the body resolve")
}

/// A value pair of two nodes.
///
/// # Specification
/// - requires: both nodes resolve in `overlay`.
/// - ensures: a fresh grafted pair.
/// - provides: the two-child body the occurrence witnesses order.
/// - panics: when the mint is refused, which the requirement excludes.
///
/// # Adequacy
/// - hypothesis: L3 — the fixture mints a fresh node with exactly the supplied
///   scope or child metadata. Validation distinguishes open and closed scopes,
///   ordered positions and implicit reuse; erasure observes the resulting
///   constructors rather than merely successful allocation.
/// - witness: `overlay::tests::validation_refuses_a_node_reached_twice`
/// - witness: `overlay::tests::validation_holds_each_share_to_its_arity_in_preorder`
#[spec(
        captures: [length = overlay.values.len()],
        ensures: |ret| usize::try_from(ret.0).ok() == Some(length) && length.checked_add(1) == Some(overlay.values.len()) && overlay.value(ret) == Some(&ValueNode::Grafted(ValueGraft::Pair(first,second)))
    )]
fn pair(
    overlay: &mut Overlay,
    first: OverlayValueId,
    second: OverlayValueId,
) -> OverlayValueId
{
    overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Pair(first, second)))
        .expect("both components resolve")
}

#[test]
fn minting_refuses_a_child_the_overlay_does_not_hold()
{
    let mut elsewhere = Overlay::new();
    let foreign = unit(&mut elsewhere);
    let foreign_comp = elsewhere
        .mint_computation(CompNode::Grafted(CompGraft::Return(foreign)))
        .expect("the returned value resolves");

    let mut overlay = Overlay::new();
    assert_eq!(
        Err(OverlayFault::DanglingChild {
            child: OverlayId::Value(foreign)
        }),
        overlay.mint_value(ValueNode::Grafted(ValueGraft::Pair(foreign, foreign))),
        "a graft over a child this overlay never minted is refused"
    );
    assert_eq!(
        Err(OverlayFault::DanglingChild {
            child: OverlayId::Computation(foreign_comp)
        }),
        overlay.mint_value(ValueNode::Grafted(ValueGraft::Thunk(foreign_comp))),
        "and so is one across families"
    );
    assert_eq!(
        OverlayWatermark::default(),
        overlay.watermark(),
        "a refused mint leaves nothing behind"
    );

    let leg = unit(&mut overlay);
    let body = overlay
        .mint_computation(CompNode::Bound(Bound {
            distance: ShareDistance::from(0_u32),
            position: SharePosition::from(0_u32),
        }))
        .expect("an occurrence names no child");
    // An id carries no provenance, so the foreign leg is one past every
    // computation this overlay holds rather than the other overlay's first.
    let missing = OverlayCompId(7);
    assert_eq!(
        Err(OverlayFault::DanglingChild {
            child: OverlayId::Computation(missing)
        }),
        overlay.mint_computation(CompNode::Shared(Sharing {
            arity: ShareArity::from(1_u32),
            leg: OverlayId::Computation(missing),
            body,
        })),
        "a share's leg is a child like any other"
    );
    assert!(
        overlay
            .mint_computation(CompNode::Shared(Sharing {
                arity: ShareArity::from(1_u32),
                leg: OverlayId::Value(leg),
                body,
            }))
            .is_ok(),
        "and a share whose leg and body resolve mints"
    );

    let result = elsewhere
        .mint_value_type(ValueTypeNode::Grafted(ValueTypeGraft::Unit))
        .expect("a leaf names no child");
    let codomain = elsewhere
        .mint_comp_type(CompTypeNode::Grafted(CompTypeGraft::Returner(result)))
        .expect("the result type resolves");
    let domain = overlay
        .mint_value_type(ValueTypeNode::Grafted(ValueTypeGraft::Unit))
        .expect("a leaf names no child");
    assert_eq!(
        Err(OverlayFault::DanglingChild {
            child: OverlayId::CompType(codomain)
        }),
        overlay.mint_comp_type(CompTypeNode::Grafted(CompTypeGraft::Arrow {
            domain,
            codomain
        })),
        "the type families check their children too"
    );
    assert_eq!(
        Err(OverlayFault::DanglingChild {
            child: OverlayId::Value(OverlayValueId(7))
        }),
        overlay.mint_value_type(ValueTypeNode::Grafted(ValueTypeGraft::Element {
            code: OverlayValueId(7),
            target: Level::zero(),
        })),
        "including the one child that crosses into the term families"
    );
}

#[test]
fn validation_refuses_an_open_node_set_by_name()
{
    let mut overlay = Overlay::new();
    let zero = ShareDistance::from(0_u32);
    let first = SharePosition::from(0_u32);

    let stray = occurrence(&mut overlay, zero, first);
    assert_eq!(
        Err(OverlayRefusal::OpenReference {
            node: OverlayId::Value(stray)
        }),
        overlay.validate(OverlayId::Value(stray)),
        "an occurrence with no share around it leaves the node set open"
    );

    let leg = unit(&mut overlay);
    let escaping = occurrence(&mut overlay, ShareDistance::from(1_u32), first);
    let one = share(
        &mut overlay,
        ShareArity::from(1_u32),
        OverlayId::Value(leg),
        escaping,
    );
    assert_eq!(
        Err(OverlayRefusal::OpenReference {
            node: OverlayId::Value(escaping)
        }),
        overlay.validate(OverlayId::Value(one)),
        "one share around an occurrence that counts two out leaves it open too"
    );

    let leg = unit(&mut overlay);
    let closed = occurrence(&mut overlay, zero, first);
    let shared = share(
        &mut overlay,
        ShareArity::from(1_u32),
        OverlayId::Value(leg),
        closed,
    );
    assert_eq!(
        Ok(()),
        overlay.validate(OverlayId::Value(shared)),
        "the same occurrence counting to the share around it closes"
    );
}

#[test]
fn validation_refuses_an_occurrence_of_another_family()
{
    let mut overlay = Overlay::new();
    let leg = unit(&mut overlay);
    let stray = overlay
        .mint_computation(CompNode::Bound(Bound {
            distance: ShareDistance::from(0_u32),
            position: SharePosition::from(0_u32),
        }))
        .expect("an occurrence names no child");
    let shared = overlay
        .mint_computation(CompNode::Shared(Sharing {
            arity: ShareArity::from(1_u32),
            leg: OverlayId::Value(leg),
            body: stray,
        }))
        .expect("the leg and the body resolve");
    assert_eq!(
        Err(OverlayRefusal::FamilyMismatch {
            node: OverlayId::Computation(stray),
            occurrence: OverlayFamily::Computation,
            leg: OverlayFamily::Value,
        }),
        overlay.validate(OverlayId::Computation(shared)),
        "a computation occurrence cannot stand for a value leg"
    );

    let produced = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Return(leg)))
        .expect("the returned value resolves");
    let value_occurrence = occurrence_in_return(&mut overlay);
    let returned = overlay
        .mint_computation(CompNode::Shared(Sharing {
            arity: ShareArity::from(1_u32),
            leg: OverlayId::Computation(produced),
            body: value_occurrence,
        }))
        .expect("the leg and the body resolve");
    assert!(
        matches!(
            overlay.validate(OverlayId::Computation(returned)),
            Err(OverlayRefusal::FamilyMismatch {
                occurrence: OverlayFamily::Value,
                leg: OverlayFamily::Computation,
                ..
            })
        ),
        "nor a value occurrence for a computation leg"
    );
}

/// `return x₀`, with `x₀` a value occurrence of the innermost share.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a fresh returner over a fresh value occurrence.
/// - provides: the computation body whose occurrence is a value.
/// - panics: when a mint is refused, which only the id ceiling causes.
///
/// # Adequacy
/// - hypothesis: L3 — the fixture returns an innermost value occurrence from a
///   computation body. The exact family-mismatch refusal distinguishes a
///   computation occurrence from the intended value occurrence, a wrong
///   distance and a missing return constructor.
/// - witness: `overlay::tests::validation_refuses_an_occurrence_of_another_family`
#[spec(
        captures: [mark = overlay.watermark()],
        ensures: |ret| usize::try_from(ret.0).ok() == Some(mark.computations)
         && mark.computations.checked_add(1) == Some(overlay.computations.len()) && mark.values.checked_add(1) == Some(overlay.values.len())
         && overlay.computation(ret).is_some_and(|node| match *node {
         CompNode::Grafted(CompGraft::Return(value)) => usize::try_from(value.0).ok() == Some(mark.values)
          && overlay.value(value) == Some(&ValueNode::Bound(Bound{distance:ShareDistance(0),position:SharePosition(0)})), CompNode::Opaque(_) | CompNode::Bound(_) | CompNode::Shared(_) | CompNode::Grafted(_) => false,
        })
    )]
fn occurrence_in_return(overlay: &mut Overlay) -> OverlayCompId
{
    let carried = occurrence(
        overlay,
        ShareDistance::from(0_u32),
        SharePosition::from(0_u32),
    );
    overlay
        .mint_computation(CompNode::Grafted(CompGraft::Return(carried)))
        .expect("the returned value resolves")
}

#[test]
fn validation_holds_each_share_to_its_arity_in_preorder()
{
    let mut overlay = Overlay::new();
    let zero = ShareDistance::from(0_u32);
    let first = SharePosition::from(0_u32);
    let second = SharePosition::from(1_u32);

    let leg = unit(&mut overlay);
    let body = unit(&mut overlay);
    let empty = share(
        &mut overlay,
        ShareArity::from(0_u32),
        OverlayId::Value(leg),
        body,
    );
    assert_eq!(
        Err(OverlayRefusal::ZeroArity {
            share: OverlayId::Value(empty)
        }),
        overlay.validate(OverlayId::Value(empty)),
        "a share standing for nothing is refused"
    );

    let leg = unit(&mut overlay);
    let only = occurrence(&mut overlay, zero, first);
    let short = share(
        &mut overlay,
        ShareArity::from(2_u32),
        OverlayId::Value(leg),
        only,
    );
    assert_eq!(
        Err(OverlayRefusal::MissingOccurrences {
            share: OverlayId::Value(short),
            arity: ShareArity::from(2_u32),
            next: second,
        }),
        overlay.validate(OverlayId::Value(short)),
        "a body holding fewer occurrences than the arity is refused at its share"
    );

    let leg = unit(&mut overlay);
    let taken = occurrence(&mut overlay, zero, first);
    let surplus = occurrence(&mut overlay, zero, second);
    let both = pair(&mut overlay, taken, surplus);
    let over = share(
        &mut overlay,
        ShareArity::from(1_u32),
        OverlayId::Value(leg),
        both,
    );
    assert_eq!(
        Err(OverlayRefusal::SurplusOccurrence {
            node: OverlayId::Value(surplus),
            arity: ShareArity::from(1_u32),
        }),
        overlay.validate(OverlayId::Value(over)),
        "an occurrence past the arity is refused where it stands"
    );

    let leg = unit(&mut overlay);
    let late = occurrence(&mut overlay, zero, second);
    let early = occurrence(&mut overlay, zero, first);
    let swapped = pair(&mut overlay, late, early);
    let misordered = share(
        &mut overlay,
        ShareArity::from(2_u32),
        OverlayId::Value(leg),
        swapped,
    );
    assert_eq!(
        Err(OverlayRefusal::PositionOutOfOrder {
            node: OverlayId::Value(late),
            expected: first,
            found: second,
        }),
        overlay.validate(OverlayId::Value(misordered)),
        "positions follow the body's preorder, leftmost first"
    );

    let leg = unit(&mut overlay);
    let left = occurrence(&mut overlay, zero, first);
    let right = occurrence(&mut overlay, zero, second);
    let ordered = pair(&mut overlay, left, right);
    let canonical = share(
        &mut overlay,
        ShareArity::from(2_u32),
        OverlayId::Value(leg),
        ordered,
    );
    assert_eq!(
        Ok(()),
        overlay.validate(OverlayId::Value(canonical)),
        "the same two occurrences in preorder close their share exactly"
    );
}

#[test]
fn validation_refuses_a_node_reached_twice()
{
    let mut overlay = Overlay::new();
    let leaf = unit(&mut overlay);
    let reused = pair(&mut overlay, leaf, leaf);
    assert_eq!(
        Err(OverlayRefusal::ReachedTwice {
            node: OverlayId::Value(leaf)
        }),
        overlay.validate(OverlayId::Value(reused)),
        "a node reused without a share is refused at its second arrival"
    );

    let leg = unit(&mut overlay);
    let left = occurrence(
        &mut overlay,
        ShareDistance::from(0_u32),
        SharePosition::from(0_u32),
    );
    let right = occurrence(
        &mut overlay,
        ShareDistance::from(0_u32),
        SharePosition::from(1_u32),
    );
    let body = pair(&mut overlay, left, right);
    let explicit = share(
        &mut overlay,
        ShareArity::from(2_u32),
        OverlayId::Value(leg),
        body,
    );
    assert_eq!(
        Ok(()),
        overlay.validate(OverlayId::Value(explicit)),
        "the same sharing named by a share is accepted"
    );
}

#[test]
fn validation_refuses_a_root_the_overlay_does_not_hold()
{
    let mut overlay = Overlay::new();
    let kept = unit(&mut overlay);
    let mark = overlay.watermark();
    let dropped = unit(&mut overlay);
    overlay.truncate_to(mark);
    assert_eq!(
        Err(OverlayRefusal::Unresolved {
            node: OverlayId::Value(dropped)
        }),
        overlay.validate(OverlayId::Value(dropped)),
        "a root truncated away names no node"
    );
    assert_eq!(Ok(()), overlay.validate(OverlayId::Value(kept)));
}

#[test]
fn a_leg_counts_from_outside_its_share()
{
    // outer = (inner = (⟨x₀, y₁⟩)[x₀ ← y₀])[y₀ y₁ ← ⟨⟩]: the inner share's leg
    // is y₀, counted from the outer frame because a leg stands outside its own
    // share, while y₁ in the inner body counts one frame further out.
    let mut overlay = Overlay::new();
    let outer_leg = unit(&mut overlay);
    let inner_leg = occurrence(
        &mut overlay,
        ShareDistance::from(0_u32),
        SharePosition::from(0_u32),
    );
    let inner_occurrence = occurrence(
        &mut overlay,
        ShareDistance::from(0_u32),
        SharePosition::from(0_u32),
    );
    let outer_occurrence = occurrence(
        &mut overlay,
        ShareDistance::from(1_u32),
        SharePosition::from(1_u32),
    );
    let body = pair(&mut overlay, inner_occurrence, outer_occurrence);
    let inner = share(
        &mut overlay,
        ShareArity::from(1_u32),
        OverlayId::Value(inner_leg),
        body,
    );
    let outer = share(
        &mut overlay,
        ShareArity::from(2_u32),
        OverlayId::Value(outer_leg),
        inner,
    );
    assert_eq!(
        Ok(()),
        overlay.validate(OverlayId::Value(outer)),
        "the leg counts from the shares around its share, the body from its own"
    );

    let self_reference = occurrence(
        &mut overlay,
        ShareDistance::from(0_u32),
        SharePosition::from(0_u32),
    );
    let body = occurrence(
        &mut overlay,
        ShareDistance::from(0_u32),
        SharePosition::from(0_u32),
    );
    let circular = share(
        &mut overlay,
        ShareArity::from(1_u32),
        OverlayId::Value(self_reference),
        body,
    );
    assert_eq!(
        Err(OverlayRefusal::OpenReference {
            node: OverlayId::Value(self_reference)
        }),
        overlay.validate(OverlayId::Value(circular)),
        "so a leg cannot name an occurrence of its own share"
    );
}

#[test]
fn truncating_to_a_watermark_drops_later_nodes()
{
    let mut overlay = Overlay::new();
    let kept = unit(&mut overlay);
    let kept_comp = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Return(kept)))
        .expect("the returned value resolves");
    let mark = overlay.watermark();
    let dropped = unit(&mut overlay);
    let dropped_comp = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Force(dropped)))
        .expect("the forced value resolves");
    let dropped_type = overlay
        .mint_value_type(ValueTypeNode::Grafted(ValueTypeGraft::Unit))
        .expect("a leaf names no child");
    let dropped_comp_type = overlay
        .mint_comp_type(CompTypeNode::Grafted(CompTypeGraft::Returner(dropped_type)))
        .expect("the result type resolves");

    overlay.truncate_to(mark);
    assert_eq!(mark, overlay.watermark());
    assert!(overlay.value(kept).is_some() && overlay.computation(kept_comp).is_some());
    assert!(
        overlay.value(dropped).is_none(),
        "a value past the mark is gone"
    );
    assert!(overlay.computation(dropped_comp).is_none());
    assert!(overlay.value_type(dropped_type).is_none());
    assert!(overlay.comp_type(dropped_comp_type).is_none());

    overlay.truncate_to(OverlayWatermark::default());
    assert_eq!(Overlay::new(), overlay, "the floor is the whole teardown");
}

/// Mint a computation node whose children resolve.
///
/// # Specification
/// - requires: every child of `node` resolves in `overlay`.
/// - ensures: a fresh computation id.
/// - provides: the terse mint the erasure witnesses build with.
/// - panics: when the mint is refused, which the requirement excludes.
///
/// # Adequacy
/// - hypothesis: L3 — the supplied computation node has live children and the
///   family has room. Exact whole-arena erasure checks every former and
///   payload, while refused opaque erasure checks the boundary; wrong metadata,
///   wrong children or reusing a previous id changes those observations.
/// - witness: `overlay::tests::erasure_mints_every_former_of_every_family_in_order`
/// - witness: `overlay::tests::a_refused_erasure_leaves_the_core_arena_unchanged`
#[spec(
        captures: [length = overlay.computations.len(), shape = node.shape()],
        ensures: |ret| usize::try_from(ret.0).ok() == Some(length) && length.checked_add(1) == Some(overlay.computations.len()) && overlay.computation(ret).is_some_and(|node| node.shape() == shape)
    )]
fn computation(
    overlay: &mut Overlay,
    node: CompNode,
) -> OverlayCompId
{
    overlay
        .mint_computation(node)
        .expect("every child resolves")
}

/// Mint a value-type node whose children resolve.
///
/// # Specification
/// - requires: every child of `node` resolves in `overlay`.
/// - ensures: a fresh value-type id.
/// - provides: the terse mint the erasure witnesses build with.
/// - panics: when the mint is refused, which the requirement excludes.
///
/// # Adequacy
/// - hypothesis: L3 — the supplied value-type node has live children and the
///   family has room. Exact whole-arena erasure checks every former and
///   payload, while refused opaque erasure checks the boundary; wrong metadata,
///   wrong children or reusing a previous id changes those observations.
/// - witness: `overlay::tests::erasure_mints_every_former_of_every_family_in_order`
/// - witness: `overlay::tests::a_refused_erasure_leaves_the_core_arena_unchanged`
#[spec(
        captures: [length = overlay.value_types.len(), shape = node.shape()],
        ensures: |ret| usize::try_from(ret.0).ok() == Some(length) && length.checked_add(1) == Some(overlay.value_types.len()) && overlay.value_type(ret).is_some_and(|node| node.shape() == shape)
    )]
fn value_type(
    overlay: &mut Overlay,
    node: ValueTypeNode,
) -> OverlayValueTypeId
{
    overlay.mint_value_type(node).expect("every child resolves")
}

/// Mint a computation-type node whose children resolve.
///
/// # Specification
/// - requires: every child of `node` resolves in `overlay`.
/// - ensures: a fresh computation-type id.
/// - provides: the terse mint the erasure witnesses build with.
/// - panics: when the mint is refused, which the requirement excludes.
///
/// # Adequacy
/// - hypothesis: L3 — the supplied comp-type node has live children and the
///   family has room. Exact whole-arena erasure checks every former and
///   payload, while refused opaque erasure checks the boundary; wrong metadata,
///   wrong children or reusing a previous id changes those observations.
/// - witness: `overlay::tests::erasure_mints_every_former_of_every_family_in_order`
/// - witness: `overlay::tests::a_refused_erasure_leaves_the_core_arena_unchanged`
#[spec(
        captures: [length = overlay.comp_types.len(), shape = node.shape()],
        ensures: |ret| usize::try_from(ret.0).ok() == Some(length) && length.checked_add(1) == Some(overlay.comp_types.len()) && overlay.comp_type(ret).is_some_and(|node| node.shape() == shape)
    )]
fn comp_type(
    overlay: &mut Overlay,
    node: CompTypeNode,
) -> OverlayCompTypeId
{
    overlay.mint_comp_type(node).expect("every child resolves")
}

/// Mint a value node whose children resolve.
///
/// # Specification
/// - requires: every child of `node` resolves in `overlay`.
/// - ensures: a fresh value id.
/// - provides: the terse mint the erasure witnesses build with.
/// - panics: when the mint is refused, which the requirement excludes.
///
/// # Adequacy
/// - hypothesis: L3 — the supplied value node has live children and the family
///   has room. Exact whole-arena erasure checks every former and payload, while
///   refused opaque erasure checks the boundary; wrong metadata, wrong children
///   or reusing a previous id changes those observations.
/// - witness: `overlay::tests::erasure_mints_every_former_of_every_family_in_order`
/// - witness: `overlay::tests::a_refused_erasure_leaves_the_core_arena_unchanged`
#[spec(
        captures: [length = overlay.values.len(), shape = node.shape()],
        ensures: |ret| usize::try_from(ret.0).ok() == Some(length) && length.checked_add(1) == Some(overlay.values.len()) && overlay.value(ret).is_some_and(|node| node.shape() == shape)
    )]
fn value(
    overlay: &mut Overlay,
    node: ValueNode,
) -> OverlayValueId
{
    overlay.mint_value(node).expect("every child resolves")
}

#[test]
fn erasure_mints_every_former_of_every_family_in_order()
{
    let target = Level::zero().succ().expect("level one exists");
    let magnitude =
        Magnitude::from_decimal_text(String::from("1")).expect("the digits are decimal");
    let literal = Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude));
    let innermost = DeBruijnIndex::from(0_u32);
    let first = ConstantIndex::from(0_usize);
    let second = ConstantIndex::from(1_usize);
    let zero = ShareDistance::from(0_u32);

    // The reference: every former minted by hand, in the order erasure walks —
    // a share's leg first, then each graft after its children, left to right.
    let mut reference = CoreArena::new();
    let held = reference.value_unit();
    let r_variable = reference.value_variable(Zone::Intuitionistic, innermost);
    let r_constant = reference.value_constant(first);
    let r_names = reference.value_tuple(&[r_variable, r_constant]);
    let r_literal = reference.value_literal(literal.clone());
    let r_injected = reference.value_injection(Side::Left.into(), r_literal);
    let r_returned = reference.value_unit();
    let r_return = reference.computation_return(r_returned);
    let r_thunk = reference.value_thunk(r_return);
    let r_lifted = reference.value_unit();
    let r_lift = reference.value_lift(target.clone(), r_lifted);
    let r_suspended = reference.value_tuple(&[r_thunk, r_lift]);
    let r_wrapped = reference.value_tuple(&[r_injected, r_suspended]);
    let r_quoted = reference.value_type_unit();
    let r_quote = reference.value_quote(r_quoted);
    let r_quoted_result = reference.value_type_unit();
    let r_quoted_returner = reference.comp_type_returner(r_quoted_result);
    let r_quote_computation = reference.value_quote_computation(r_quoted_returner);
    let r_quotes = reference.value_tuple(&[r_quote, r_quote_computation]);
    let r_rest = reference.value_tuple(&[r_wrapped, r_quotes]);
    let r_value = reference.value_tuple(&[r_names, r_rest]);

    let r_leg = reference.value_unit();
    let r_force = reference.computation_force(r_leg);
    let r_bound = reference.value_variable(Zone::Intuitionistic, innermost);
    let r_body = reference.computation_return(r_bound);
    let r_lambda = reference.computation_lambda(r_body);
    let r_application = reference.computation_application(r_lambda, held);
    let r_produced = reference.value_unit();
    let r_then = reference.computation_return(r_produced);
    let r_bind = reference.computation_bind(r_application, r_then);
    let r_case = reference.computation_case(r_leg, &[r_force, r_bind]);

    let r_base = reference.value_type_base(BaseType::Integer);
    let r_unit = reference.value_type_unit();
    let r_sum = reference.value_type_sum(&[r_base, r_unit]);
    let r_result = reference.value_type_unit();
    let r_returner = reference.comp_type_returner(r_result);
    let r_thunk_type = reference.value_type_thunk(r_returner);
    let r_universe =
        reference.value_type_universe(Sort::Ground(GroundSort::Computation), target.clone());
    let r_atom = reference.value_type_abstract(first);
    let r_lift_type = reference.value_type_lift(r_atom, target.clone());
    let r_code = reference.value_unit();
    let r_element = reference.value_type_element(r_code, target.clone());
    let r_comp_code = reference.value_unit();
    let r_comp_element = reference.comp_type_element(r_comp_code, target.clone());
    let r_suspended_element = reference.value_type_thunk(r_comp_element);
    let r_decodes = reference.value_type_product(&[r_element, r_suspended_element]);
    let r_codes = reference.value_type_product(&[r_lift_type, r_decodes]);
    let r_universes = reference.value_type_product(&[r_universe, r_codes]);
    let r_thunks = reference.value_type_product(&[r_thunk_type, r_universes]);
    let r_value_type = reference.value_type_product(&[r_sum, r_thunks]);

    let r_domain = reference.value_type_unit();
    let r_sealed = reference.value_type_abstract(second);
    let r_codomain = reference.comp_type_returner(r_sealed);
    let r_arrow = reference.comp_type_arrow(r_domain, r_codomain);
    let r_pi = reference.comp_type_pi(r_domain, r_arrow);

    // The overlay: the same four terms, the computation and the
    // computation type each sharing one leg between two occurrences.
    let mut core = CoreArena::new();
    let opaque = core.value_unit();
    let mut overlay = Overlay::new();

    let o_variable = value(
        &mut overlay,
        ValueNode::Grafted(ValueGraft::Variable {
            zone: Zone::Intuitionistic,
            index: innermost,
        }),
    );
    let o_constant = value(
        &mut overlay,
        ValueNode::Grafted(ValueGraft::Constant(first)),
    );
    let o_names = pair(&mut overlay, o_variable, o_constant);
    let o_literal = value(
        &mut overlay,
        ValueNode::Grafted(ValueGraft::Literal(literal)),
    );
    let o_injected = value(
        &mut overlay,
        ValueNode::Grafted(ValueGraft::Injection(Side::Left, o_literal)),
    );
    let o_returned = unit(&mut overlay);
    let o_return = computation(
        &mut overlay,
        CompNode::Grafted(CompGraft::Return(o_returned)),
    );
    let o_thunk = value(
        &mut overlay,
        ValueNode::Grafted(ValueGraft::Thunk(o_return)),
    );
    let o_lifted = unit(&mut overlay);
    let o_lift = value(
        &mut overlay,
        ValueNode::Grafted(ValueGraft::Lift {
            target: target.clone(),
            body: o_lifted,
        }),
    );
    let o_suspended = pair(&mut overlay, o_thunk, o_lift);
    let o_wrapped = pair(&mut overlay, o_injected, o_suspended);
    let o_quoted = value_type(&mut overlay, ValueTypeNode::Grafted(ValueTypeGraft::Unit));
    let o_quote = value(
        &mut overlay,
        ValueNode::Grafted(ValueGraft::Quote(o_quoted)),
    );
    let o_quoted_result = value_type(&mut overlay, ValueTypeNode::Grafted(ValueTypeGraft::Unit));
    let o_quoted_returner = comp_type(
        &mut overlay,
        CompTypeNode::Grafted(CompTypeGraft::Returner(o_quoted_result)),
    );
    let o_quote_computation = value(
        &mut overlay,
        ValueNode::Grafted(ValueGraft::QuoteComputation(o_quoted_returner)),
    );
    let o_quotes = pair(&mut overlay, o_quote, o_quote_computation);
    let o_rest = pair(&mut overlay, o_wrapped, o_quotes);
    let o_value = pair(&mut overlay, o_names, o_rest);

    let o_leg = unit(&mut overlay);
    let o_scrutinee = occurrence(&mut overlay, zero, SharePosition::from(0_u32));
    let o_forced = occurrence(&mut overlay, zero, SharePosition::from(1_u32));
    let o_force = computation(&mut overlay, CompNode::Grafted(CompGraft::Force(o_forced)));
    let o_bound = value(
        &mut overlay,
        ValueNode::Grafted(ValueGraft::Variable {
            zone: Zone::Intuitionistic,
            index: innermost,
        }),
    );
    let o_body = computation(&mut overlay, CompNode::Grafted(CompGraft::Return(o_bound)));
    let o_lambda = computation(&mut overlay, CompNode::Grafted(CompGraft::Lambda(o_body)));
    let o_held = value(&mut overlay, ValueNode::Opaque(opaque));
    let o_application = computation(
        &mut overlay,
        CompNode::Grafted(CompGraft::Application(o_lambda, o_held)),
    );
    let o_produced = unit(&mut overlay);
    let o_then = computation(
        &mut overlay,
        CompNode::Grafted(CompGraft::Return(o_produced)),
    );
    let o_bind = computation(
        &mut overlay,
        CompNode::Grafted(CompGraft::Bind(o_application, o_then)),
    );
    let o_case = computation(
        &mut overlay,
        CompNode::Grafted(CompGraft::Case {
            scrutinee: o_scrutinee,
            on_left: o_force,
            on_right: o_bind,
        }),
    );
    let o_computation = computation(
        &mut overlay,
        CompNode::Shared(Sharing {
            arity: ShareArity::from(2_u32),
            leg: OverlayId::Value(o_leg),
            body: o_case,
        }),
    );

    let o_base = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Base(BaseType::Integer)),
    );
    let o_unit = value_type(&mut overlay, ValueTypeNode::Grafted(ValueTypeGraft::Unit));
    let o_sum = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Sum(o_base, o_unit)),
    );
    let o_result = value_type(&mut overlay, ValueTypeNode::Grafted(ValueTypeGraft::Unit));
    let o_returner = comp_type(
        &mut overlay,
        CompTypeNode::Grafted(CompTypeGraft::Returner(o_result)),
    );
    let o_thunk_type = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Thunk(o_returner)),
    );
    let o_universe = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Universe {
            sort: Sort::Ground(GroundSort::Computation),
            level: target.clone(),
        }),
    );
    let o_atom = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Abstract(first)),
    );
    let o_lift_type = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Lift {
            inner: o_atom,
            target: target.clone(),
        }),
    );
    let o_code = unit(&mut overlay);
    let o_element = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Element {
            code: o_code,
            target: target.clone(),
        }),
    );
    let o_comp_code = unit(&mut overlay);
    let o_comp_element = comp_type(
        &mut overlay,
        CompTypeNode::Grafted(CompTypeGraft::Element {
            code: o_comp_code,
            target,
        }),
    );
    let o_suspended_element = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Thunk(o_comp_element)),
    );
    let o_decodes = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Product(o_element, o_suspended_element)),
    );
    let o_codes = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Product(o_lift_type, o_decodes)),
    );
    let o_universes = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Product(o_universe, o_codes)),
    );
    let o_thunks = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Product(o_thunk_type, o_universes)),
    );
    let o_value_type = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Product(o_sum, o_thunks)),
    );

    let o_domain = value_type(&mut overlay, ValueTypeNode::Grafted(ValueTypeGraft::Unit));
    let o_dependent = value_type(
        &mut overlay,
        ValueTypeNode::Bound(Bound {
            distance: zero,
            position: SharePosition::from(0_u32),
        }),
    );
    let o_plain = value_type(
        &mut overlay,
        ValueTypeNode::Bound(Bound {
            distance: zero,
            position: SharePosition::from(1_u32),
        }),
    );
    let o_sealed = value_type(
        &mut overlay,
        ValueTypeNode::Grafted(ValueTypeGraft::Abstract(second)),
    );
    let o_codomain = comp_type(
        &mut overlay,
        CompTypeNode::Grafted(CompTypeGraft::Returner(o_sealed)),
    );
    let o_arrow = comp_type(
        &mut overlay,
        CompTypeNode::Grafted(CompTypeGraft::Arrow {
            domain: o_plain,
            codomain: o_codomain,
        }),
    );
    let o_pi = comp_type(
        &mut overlay,
        CompTypeNode::Grafted(CompTypeGraft::Pi {
            domain: o_dependent,
            codomain: o_arrow,
        }),
    );
    let o_comp_type = comp_type(
        &mut overlay,
        CompTypeNode::Shared(Sharing {
            arity: ShareArity::from(2_u32),
            leg: OverlayId::ValueType(o_domain),
            body: o_pi,
        }),
    );

    let erased = (
        erase_value(&overlay, o_value, &mut core),
        erase_computation(&overlay, o_computation, &mut core),
        erase_value_type(&overlay, o_value_type, &mut core),
        erase_comp_type(&overlay, o_comp_type, &mut core),
    );
    assert_eq!(
        (Ok(r_value), Ok(r_case), Ok(r_value_type), Ok(r_pi)),
        erased,
        "each root erases to the id its hand-built term takes"
    );
    assert_eq!(
        reference, core,
        "and the arena holds node for node what the hand-built terms minted: one node \
             per graft, the opaque id as it stands, and one leg per share"
    );
}

#[test]
fn a_refused_erasure_leaves_the_core_arena_unchanged()
{
    let mut core = CoreArena::new();
    let _ = core.value_unit();
    let entry = core.clone();
    let mut overlay = Overlay::new();

    let stray = occurrence(
        &mut overlay,
        ShareDistance::from(0_u32),
        SharePosition::from(0_u32),
    );
    let wrapped = computation(&mut overlay, CompNode::Grafted(CompGraft::Return(stray)));
    assert_eq!(
        Err(EraseFault::Refused(OverlayRefusal::OpenReference {
            node: OverlayId::Value(stray)
        })),
        erase_computation(&overlay, wrapped, &mut core),
        "validation refuses in its own vocabulary"
    );
    assert_eq!(entry, core, "before anything is minted");

    // A core id one past every value the arena holds, so it cannot resolve.
    let foreign = {
        let mut elsewhere = CoreArena::new();
        let leaf = elsewhere.value_unit();
        let pair = elsewhere.value_tuple(&[leaf, leaf]);
        elsewhere.value_tuple(&[pair, pair])
    };
    let leaf = unit(&mut overlay);
    let opaque = value(&mut overlay, ValueNode::Opaque(foreign));
    let both = pair(&mut overlay, leaf, opaque);
    assert_eq!(
        Err(EraseFault::UnresolvedOpaque {
            node: OverlayId::Value(opaque)
        }),
        erase_value(&overlay, both, &mut core),
        "an opaque id the core arena does not hold is refused where it stands"
    );
    assert_eq!(
        entry, core,
        "opaque preflight leaves the entry arena unchanged"
    );
}

#[test]
fn opaque_erasure_does_not_resurrect_a_missing_core_id()
{
    let mut core = CoreArena::new();
    let retained = core.value_unit();
    let mark = core.watermark();
    let missing = core.value_constant(ConstantIndex::from(11_usize));
    core.truncate_to(mark);
    let mut overlay = Overlay::new();
    let fresh = unit(&mut overlay);
    let opaque = value(&mut overlay, ValueNode::Opaque(missing));
    let root = pair(&mut overlay, fresh, opaque);
    assert_eq!(
        Err(EraseFault::UnresolvedOpaque {
            node: OverlayId::Value(opaque)
        }),
        erase_value(&overlay, root, &mut core)
    );
    assert_eq!(
        mark,
        core.watermark(),
        "earlier grafts cannot make an initially missing opaque id live"
    );
    assert_eq!(Some(&gandr_core_term::Value::unit()), core.value(retained));
}

#[test]
fn lookup_offsets_are_local_and_out_of_range_ids_fail_closed()
{
    let mut overlay = Overlay::new();
    let leaf = unit(&mut overlay);
    let returned = computation(&mut overlay, CompNode::Grafted(CompGraft::Return(leaf)));
    let ty = value_type(&mut overlay, ValueTypeNode::Grafted(ValueTypeGraft::Unit));
    let cty = comp_type(
        &mut overlay,
        CompTypeNode::Grafted(CompTypeGraft::Returner(ty)),
    );
    let mut core = CoreArena::new();
    let core_ty = core.value_type_unit();
    let core_cty = core.comp_type_returner(core_ty);
    let mut foreign = Overlay::new();
    let fv = value(
        &mut foreign,
        ValueNode::Grafted(ValueGraft::Constant(ConstantIndex::from(11_usize))),
    );
    let fc = computation(&mut foreign, CompNode::Grafted(CompGraft::Force(fv)));
    let ft = value_type(&mut foreign, ValueTypeNode::Opaque(core_ty));
    let fct = comp_type(&mut foreign, CompTypeNode::Opaque(core_cty));
    assert_eq!(
        Some(&ValueNode::Grafted(ValueGraft::Unit)),
        overlay.value(fv)
    );
    assert_eq!(
        Some(&CompNode::Grafted(CompGraft::Return(leaf))),
        overlay.computation(fc)
    );
    assert_eq!(
        Some(&ValueTypeNode::Grafted(ValueTypeGraft::Unit)),
        overlay.value_type(ft)
    );
    assert_eq!(
        Some(&CompTypeNode::Grafted(CompTypeGraft::Returner(ty))),
        overlay.comp_type(fct)
    );
    for missing in [
        OverlayId::Value(OverlayValueId(1)),
        OverlayId::Computation(OverlayCompId(1)),
        OverlayId::ValueType(OverlayValueTypeId(1)),
        OverlayId::CompType(OverlayCompTypeId(1)),
    ] {
        assert_eq!(
            Err(OverlayRefusal::Unresolved { node: missing }),
            overlay.shape(missing)
        );
        assert_eq!(
            Err(OverlayRefusal::Unresolved { node: missing }),
            overlay.validate(missing)
        );
    }
    overlay.truncate_to(OverlayWatermark::default());
    assert_eq!(None, overlay.value(leaf));
    assert_eq!(None, overlay.computation(returned));
    assert_eq!(None, overlay.value_type(ty));
    assert_eq!(None, overlay.comp_type(cty));
}

#[test]
fn index_ceiling_is_checked_without_allocating_nodes()
{
    let ceiling = usize::try_from(u32::MAX).expect("the target supports 32-bit indices");
    assert_eq!(super::Offset(0), super::offset(super::Index(0)));
    assert_eq!(
        super::Offset(ceiling),
        super::offset(super::Index(u32::MAX))
    );
    assert_eq!(
        Ok(super::Index(u32::MAX)),
        super::next_index(super::Offset(ceiling), OverlayFamily::Value)
    );
    if let Some(past) = ceiling.checked_add(1) {
        assert_eq!(
            Err(OverlayFault::FamilyFull {
                family: OverlayFamily::CompType
            }),
            super::next_index(super::Offset(past), OverlayFamily::CompType)
        );
    }
}

#[test]
fn mint_refusals_preserve_prefixes_and_name_the_first_missing_child()
{
    let mut overlay = Overlay::new();
    let leaf = unit(&mut overlay);
    let _returned = computation(&mut overlay, CompNode::Grafted(CompGraft::Return(leaf)));
    let ty = value_type(&mut overlay, ValueTypeNode::Grafted(ValueTypeGraft::Unit));
    let _cty = comp_type(
        &mut overlay,
        CompTypeNode::Grafted(CompTypeGraft::Returner(ty)),
    );
    let entry = overlay.clone();
    let missing_value = OverlayValueId(7);
    let missing_comp = OverlayCompId(7);
    let missing_type = OverlayValueTypeId(7);
    let missing_comp_type = OverlayCompTypeId(9);
    assert_eq!(
        Err(OverlayFault::DanglingChild {
            child: OverlayId::Value(missing_value)
        }),
        overlay.mint_value(ValueNode::Grafted(ValueGraft::Pair(
            missing_value,
            OverlayValueId(9)
        )))
    );
    assert_eq!(entry, overlay);
    assert_eq!(
        Err(OverlayFault::DanglingChild {
            child: OverlayId::Computation(missing_comp)
        }),
        overlay.mint_computation(CompNode::Grafted(CompGraft::Case {
            scrutinee: leaf,
            on_left: missing_comp,
            on_right: OverlayCompId(9)
        }))
    );
    assert_eq!(entry, overlay);
    assert_eq!(
        Err(OverlayFault::DanglingChild {
            child: OverlayId::ValueType(missing_type)
        }),
        overlay.mint_value_type(ValueTypeNode::Grafted(ValueTypeGraft::Product(
            missing_type,
            OverlayValueTypeId(9)
        )))
    );
    assert_eq!(entry, overlay);
    assert_eq!(
        Err(OverlayFault::DanglingChild {
            child: OverlayId::CompType(missing_comp_type)
        }),
        overlay.mint_comp_type(CompTypeNode::Grafted(CompTypeGraft::Arrow {
            domain: ty,
            codomain: missing_comp_type
        }))
    );
    assert_eq!(entry, overlay);
    assert_eq!(
        Err(OverlayFault::DanglingChild {
            child: OverlayId::Computation(missing_comp)
        }),
        overlay.mint_value(ValueNode::Shared(Sharing {
            arity: ShareArity(1),
            leg: OverlayId::Computation(missing_comp),
            body: missing_value
        }))
    );
    assert_eq!(
        entry, overlay,
        "a share checks its leg before its body without mutating the prefix"
    );
}

#[test]
fn occurrence_ceiling_and_refusal_precedence_preserve_the_frame()
{
    let node = OverlayId::Value(OverlayValueId(0));
    let mut frames = [super::Frame {
        arity: ShareArity(u32::MAX),
        leg: OverlayFamily::Value,
        next: SharePosition(u32::MAX.saturating_sub(1)),
    }];
    assert_eq!(
        Ok(()),
        super::occur(&mut frames, node, Bound {
            distance: ShareDistance(0),
            position: SharePosition(u32::MAX.saturating_sub(1))
        })
    );
    assert_eq!(SharePosition(u32::MAX), frames[0].next);
    let full = frames;
    assert_eq!(
        Err(OverlayRefusal::SurplusOccurrence {
            node,
            arity: ShareArity(u32::MAX)
        }),
        super::occur(&mut frames, node, Bound {
            distance: ShareDistance(0),
            position: SharePosition(0)
        })
    );
    assert_eq!(
        full, frames,
        "surplus takes precedence over a wrong position"
    );
    let other = OverlayId::Computation(OverlayCompId(0));
    assert_eq!(
        Err(OverlayRefusal::FamilyMismatch {
            node: other,
            occurrence: OverlayFamily::Computation,
            leg: OverlayFamily::Value
        }),
        super::occur(&mut frames, other, Bound {
            distance: ShareDistance(0),
            position: SharePosition(0)
        })
    );
    assert_eq!(full, frames, "family takes precedence over surplus");
    assert_eq!(
        Err(OverlayRefusal::OpenReference { node: other }),
        super::occur(&mut frames, other, Bound {
            distance: ShareDistance(1),
            position: SharePosition(0)
        })
    );
    assert_eq!(full, frames, "scope takes precedence over family");
    frames[0].next = SharePosition(3);
    let ready = frames;
    assert_eq!(
        Err(OverlayRefusal::PositionOutOfOrder {
            node,
            expected: SharePosition(3),
            found: SharePosition(5)
        }),
        super::occur(&mut frames, node, Bound {
            distance: ShareDistance(0),
            position: SharePosition(5)
        })
    );
    assert_eq!(ready, frames);
}

#[test]
fn erasure_keeps_nested_legs_in_postorder_and_rolls_back_late_failures()
{
    let mut overlay = Overlay::new();
    let leaf = unit(&mut overlay);
    let outer_use = occurrence(&mut overlay, ShareDistance(0), SharePosition(0));
    let inner_leg = computation(
        &mut overlay,
        CompNode::Grafted(CompGraft::Return(outer_use)),
    );
    let inner_use = computation(
        &mut overlay,
        CompNode::Bound(Bound {
            distance: ShareDistance(0),
            position: SharePosition(0),
        }),
    );
    let inner = computation(
        &mut overlay,
        CompNode::Shared(Sharing {
            arity: ShareArity(1),
            leg: OverlayId::Computation(inner_leg),
            body: inner_use,
        }),
    );
    let root = computation(
        &mut overlay,
        CompNode::Shared(Sharing {
            arity: ShareArity(1),
            leg: OverlayId::Value(leaf),
            body: inner,
        }),
    );
    let mut core = CoreArena::new();
    let _prefix = core.value_unit();
    let mut expected = core.clone();
    let erased_leaf = expected.value_unit();
    let erased_return = expected.computation_return(erased_leaf);
    let erased = super::erase_with_legs(&overlay, OverlayId::Computation(root), &mut core)
        .expect("both share scopes close");
    assert_eq!(super::CoreId::Computation(erased_return), erased.root());
    assert_eq!(
        &[
            super::CoreId::Value(erased_leaf),
            super::CoreId::Computation(erased_return)
        ],
        erased.legs()
    );
    assert_eq!(expected, core);
    let mut elsewhere = CoreArena::new();
    let foreign_value = elsewhere.value_unit();
    let mut missing = elsewhere.computation_return(foreign_value);
    for _ in 0_u32 .. 8_u32 {
        missing = elsewhere.computation_lambda(missing);
    }
    let opaque = computation(&mut overlay, CompNode::Opaque(missing));
    let bad = computation(
        &mut overlay,
        CompNode::Grafted(CompGraft::Bind(root, opaque)),
    );
    assert_eq!(
        Err(EraseFault::UnresolvedOpaque {
            node: OverlayId::Computation(opaque)
        }),
        super::erase_with_legs(&overlay, OverlayId::Computation(bad), &mut core)
    );
    assert_eq!(
        expected, core,
        "a late-in-traversal opaque failure keeps neither new nodes nor legs"
    );
}

#[test]
fn erasure_rejects_incomplete_or_mistyped_stacks()
{
    let mut overlay = Overlay::new();
    let leaf = unit(&mut overlay);
    let mut core = CoreArena::new();
    let value = core.value_unit();
    let comp = core.computation_return(value);
    let value_type = core.value_type_unit();
    let comp_type = core.comp_type_returner(value_type);
    let entry = core.clone();
    let mut erasure = super::Erasure {
        overlay: &overlay,
        core: &mut core,
        steps: alloc::vec::Vec::new(),
        legs: alloc::vec::Vec::new(),
        results: alloc::vec::Vec::new(),
        keeping: super::Keeping::Nothing,
        kept: alloc::vec::Vec::new(),
    };
    assert_eq!(Err(EraseFault::MachineInvariant), erasure.run());
    for step in [super::Step::Bind, super::Step::Unbind] {
        erasure.steps.push(step);
        assert_eq!(Err(EraseFault::MachineInvariant), erasure.run());
    }
    erasure.results.extend([
        super::CoreId::Value(value),
        super::CoreId::Computation(comp),
    ]);
    assert_eq!(Err(EraseFault::MachineInvariant), erasure.value());
    assert_eq!(&[super::CoreId::Value(value)], erasure.results.as_slice());
    assert_eq!(Ok(value), erasure.value());
    assert_eq!(Err(EraseFault::MachineInvariant), erasure.computation());
    erasure.results.push(super::CoreId::CompType(comp_type));
    assert_eq!(Err(EraseFault::MachineInvariant), erasure.value_type());
    erasure.results.push(super::CoreId::ValueType(value_type));
    assert_eq!(Err(EraseFault::MachineInvariant), erasure.comp_type());
    erasure.results.push(super::CoreId::Value(value));
    assert_eq!(
        Err(EraseFault::MachineInvariant),
        erasure.assemble_value(&ValueGraft::Thunk(OverlayCompId(0)))
    );
    erasure.results.push(super::CoreId::CompType(comp_type));
    assert_eq!(
        Err(EraseFault::MachineInvariant),
        erasure.assemble_computation(CompGraft::Return(leaf))
    );
    erasure.results.push(super::CoreId::Computation(comp));
    assert_eq!(
        Err(EraseFault::MachineInvariant),
        erasure.assemble_value_type(&ValueTypeGraft::Thunk(OverlayCompTypeId(0)))
    );
    erasure.results.push(super::CoreId::Value(value));
    assert_eq!(
        Err(EraseFault::MachineInvariant),
        erasure.assemble_comp_type(&CompTypeGraft::Returner(OverlayValueTypeId(0)))
    );
    assert_eq!(entry, *erasure.core, "mistyped stacks mint no parent");
    erasure.results.extend([
        super::CoreId::Value(value),
        super::CoreId::Computation(comp),
    ]);
    assert_eq!(
        Err(EraseFault::MachineInvariant),
        erasure.run(),
        "two remaining roots cannot be accepted as one"
    );
    erasure.legs.push(super::CoreId::Value(value));
    assert_eq!(
        Err(EraseFault::MachineInvariant),
        erasure.run(),
        "a bound leg cannot escape the walk"
    );
}

#[test]
fn structural_refusals_precede_opaque_preflight_failures()
{
    let mut core = CoreArena::new();
    let mut elsewhere = CoreArena::new();
    let missing = elsewhere.value_unit();
    let mut overlay = Overlay::new();
    let opaque = value(&mut overlay, ValueNode::Opaque(missing));
    let stray = occurrence(&mut overlay, ShareDistance(0), SharePosition(0));
    let root = pair(&mut overlay, opaque, stray);
    assert_eq!(
        Err(EraseFault::Refused(OverlayRefusal::OpenReference {
            node: OverlayId::Value(stray)
        })),
        erase_value(&overlay, root, &mut core)
    );
    assert_eq!(CoreArena::new(), core);
    let valid = unit(&mut overlay);
    let erased = erase_value(&overlay, valid, &mut core)
        .expect("unreachable invalid nodes do not taint another root");
    assert_eq!(Some(&gandr_core_term::Value::unit()), core.value(erased));
}
