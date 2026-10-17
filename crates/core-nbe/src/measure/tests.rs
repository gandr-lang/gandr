use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_kernel_term::Side;

use super::ExpansionSize;
use super::MeasureFault;
use super::MeasuredQuantity;
use super::NodeCount;
use super::OccurrenceCount;
use super::ShareCount;
use super::ShareDepth;
use super::SharingMeasure;
use crate::overlay::Bound;
use crate::overlay::CompGraft;
use crate::overlay::CompNode;
use crate::overlay::Overlay;
use crate::overlay::OverlayId;
use crate::overlay::OverlayRefusal;
use crate::overlay::OverlayValueId;
use crate::overlay::ShareArity;
use crate::overlay::ShareDistance;
use crate::overlay::SharePosition;
use crate::overlay::Sharing;
use crate::overlay::ValueGraft;
use crate::overlay::ValueNode;

/// How many links a test chain holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Links(u32);

/// The occurrences the many-occurrence share stands for.
const OCCURRENCES: u32 = 1_000;

/// The longest doubling chain whose expansion fits a 64-bit counter:
/// link `k` stands for `2^(k + 1) - 1` nodes.
const FITTING_LINKS: Links = Links(63);

/// A grafted unit value.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a fresh value leaf.
/// - provides: the legs and leaves the cases share.
/// - panics: when the mint is refused, which only the id ceiling causes.
///
/// # Adequacy
/// - hypothesis: L3 — replacing a unit leaf with another former changes the
///   exact no-sharing measure and the independent erased-tree count.
/// - witness: `measure::tests::an_occurrence_free_root_measures_its_own_size`
/// - witness: `measure::measure::the_expansion_size_is_what_the_unshared_walk_visits`
#[spec(
        captures: entry = overlay.watermark(),
        ensures: |ret| overlay.watermark() != entry && overlay.value(ret) == Some(&ValueNode::Grafted(ValueGraft::Unit))
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
/// - provides: the occurrences the cases place in preorder.
/// - panics: when the mint is refused, which only the id ceiling causes.
///
/// # Adequacy
/// - hypothesis: L3 — changing distance or position either refuses the root or
///   reads a differently sized leg.
/// - witness: `measure::tests::an_occurrence_reads_the_leg_its_distance_names`
/// - witness: `measure::tests::an_invalid_overlay_is_refused_by_name_before_measuring`
#[spec(
        captures: entry = overlay.watermark(),
        ensures: |ret| overlay.watermark() != entry && overlay.value(ret) == Some(&ValueNode::Bound(Bound { distance, position }))
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

/// A value pair of two nodes.
///
/// # Specification
/// - requires: both nodes resolve in `overlay`.
/// - ensures: a fresh grafted pair.
/// - provides: the two-child graft the cases build with.
/// - panics: when the mint is refused, which the requirement excludes.
///
/// # Adequacy
/// - hypothesis: L3 — reversing the pair or dropping a child changes occurrence
///   preorder or the exact expanded size.
/// - witness: `measure::tests::a_share_with_many_occurrences_inlines_its_leg_at_each`
/// - witness: `measure::tests::an_invalid_overlay_is_refused_by_name_before_measuring`
#[spec(
        ensures: |ret| ret != first && ret != second && overlay.value(ret) == Some(&ValueNode::Grafted(ValueGraft::Pair(first, second)))
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

/// A value share of the value `leg` among `arity` occurrences in `body`.
///
/// # Specification
/// - requires: `leg` and `body` resolve in `overlay`.
/// - ensures: a fresh value share.
/// - provides: the shares the cases build.
/// - panics: when the mint is refused, which the requirement excludes.
///
/// # Adequacy
/// - hypothesis: L3 — replacing the arity or interchanging the leg and body
///   changes the scope, share depth or measured expansion.
/// - witness: `measure::tests::a_leg_reads_the_shares_outside_its_own`
/// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
#[spec(
        ensures: |ret| ret != leg && ret != body && overlay.value(ret) == Some(&ValueNode::Shared(Sharing { arity, leg: OverlayId::Value(leg), body }))
    )]
fn share(
    overlay: &mut Overlay,
    arity: ShareArity,
    leg: OverlayValueId,
    body: OverlayValueId,
) -> OverlayValueId
{
    overlay
        .mint_value(ValueNode::Shared(Sharing {
            arity,
            leg: OverlayId::Value(leg),
            body,
        }))
        .expect("the leg and the body resolve")
}

/// The occurrence at distance zero and position zero: the only occurrence
/// of a share of arity one directly around it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a fresh value occurrence.
/// - provides: the one occurrence each chain link holds.
/// - panics: when the mint is refused, which only the id ceiling causes.
///
/// # Adequacy
/// - hypothesis: L3 — changing either zero selects a different frame or refuses
///   a single-occurrence share.
/// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
/// - witness: `measure::tests::a_leg_reads_the_shares_outside_its_own`
#[spec(
        captures: entry = overlay.watermark(),
        ensures: |ret| overlay.watermark() != entry && overlay.value(ret) == Some(&ValueNode::Bound(Bound { distance: ShareDistance::from(0_u32), position: SharePosition::from(0_u32) }))
    )]
fn only_occurrence(overlay: &mut Overlay) -> OverlayValueId
{
    occurrence(
        overlay,
        ShareDistance::from(0_u32),
        SharePosition::from(0_u32),
    )
}

/// `⟨x₀, link⟩[x₀ ← ⟨⟩]` per link over a unit: shares nested through
/// their bodies.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the outermost of `links` links, each a share of arity one whose
///   body pairs its occurrence with the link below.
/// - provides: a chain whose share depth is its length, whose node count is
///   four per link and one, and whose expansion is two per link and one.
/// - panics: when a mint is refused, which only the id ceiling causes.
///
/// # Adequacy
/// - hypothesis: L3 — nesting through the wrong side, adding a link twice or
///   dropping an occurrence changes the exact depth, physical size or
///   expansion; unequal sibling chains witness the maximum rather than the sum.
/// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "parity: the check measures the nodes the body minted, each once"
    )
)]
#[spec(
        ensures: |ret| SharingMeasure::of(overlay, OverlayId::Value(ret)).is_ok_and(|measured| measured.shares.0 == u64::from(links.0) && measured.occurrences.0 == u64::from(links.0) && measured.depth.0 == u64::from(links.0) && measured.nodes.0 == u64::from(links.0).saturating_mul(4).saturating_add(1) && measured.expansion.0 == u64::from(links.0).saturating_mul(2).saturating_add(1))
    )]
fn body_chain(
    overlay: &mut Overlay,
    links: Links,
) -> OverlayValueId
{
    let mut nested = unit(overlay);
    for _link in 0 .. links.0 {
        let leg = unit(overlay);
        let read = only_occurrence(overlay);
        let body = pair(overlay, read, nested);
        nested = share(overlay, ShareArity::from(1_u32), leg, body);
    }
    nested
}

/// `x₀[x₀ ← link]` per link over a unit: shares nested through their
/// legs.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the outermost of `links` links, each a share of arity one whose
///   leg is the link below and whose body is its occurrence.
/// - provides: a chain whose share depth is its length, whose node count is two
///   per link and one, and whose expansion is the unit's alone.
/// - panics: when a mint is refused, which only the id ceiling causes.
///
/// # Adequacy
/// - hypothesis: L3 — nesting through the wrong side, adding a link twice or
///   dropping an occurrence changes the exact depth, physical size or
///   expansion; unequal sibling chains witness the maximum rather than the sum.
/// - witness: `measure::tests::the_share_depth_is_the_longest_chain_of_nested_shares`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "parity: the check measures the nodes the body minted, each once"
    )
)]
#[spec(
        ensures: |ret| SharingMeasure::of(overlay, OverlayId::Value(ret)).is_ok_and(|measured| measured.shares.0 == u64::from(links.0) && measured.occurrences.0 == u64::from(links.0) && measured.depth.0 == u64::from(links.0) && measured.nodes.0 == u64::from(links.0).saturating_mul(2).saturating_add(1) && measured.expansion.0 == 1_u64)
    )]
fn leg_chain(
    overlay: &mut Overlay,
    links: Links,
) -> OverlayValueId
{
    let mut nested = unit(overlay);
    for _link in 0 .. links.0 {
        let read = only_occurrence(overlay);
        nested = share(overlay, ShareArity::from(1_u32), nested, read);
    }
    nested
}

/// `⟨x₀, x₁⟩[x₀ x₁ ← link]` per link over a unit: the chain whose
/// expansion doubles per link.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the outermost of `links` links, each a share of arity two whose
///   leg is the link below and whose body pairs its two occurrences, together
///   with the outermost link's body.
/// - provides: a chain of four nodes per link and one whose link `k` stands for
///   `2^(k + 1) - 1` nodes.
/// - panics: when a mint is refused, which only the id ceiling causes.
///
/// # Adequacy
/// - hypothesis: L3 — replacing doubling with one occurrence, returning another
///   body id or wrapping the last sum changes the last-fitting expansion or the
///   exact overflowing graft.
/// - witness: `measure::tests::a_doubling_chain_measures_in_its_own_size`
/// - witness: `measure::tests::an_expansion_past_the_counter_is_refused_at_its_node`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "parity: the check measures the nodes the body minted, each once"
    )
)]
#[spec(
        ensures: |ret| {
            let expansion = 1_u64.checked_shl(links.0).and_then(|half| half.checked_add(half.saturating_sub(1)));
            let shape = if links.0 == 0 { ret.0 == ret.1 && overlay.value(ret.0) == Some(&ValueNode::Grafted(ValueGraft::Unit)) } else { matches!(overlay.value(ret.0), Some(&ValueNode::Shared(sharing)) if sharing.body == ret.1 && u32::from(sharing.arity) == 2) };
            shape && SharingMeasure::of(overlay, OverlayId::Value(ret.0)).map_or_else(
                |fault| expansion.is_none() && matches!(fault, MeasureFault::Overflow { quantity: MeasuredQuantity::Expansion, .. }),
                |measured| expansion == Some(measured.expansion.0) && measured.shares.0 == u64::from(links.0) && measured.occurrences.0 == u64::from(links.0).saturating_mul(2) && measured.depth.0 == u64::from(links.0) && measured.nodes.0 == u64::from(links.0).saturating_mul(4).saturating_add(1))
        }
    )]
fn doubling_chain(
    overlay: &mut Overlay,
    links: Links,
) -> (OverlayValueId, OverlayValueId)
{
    let mut nested = unit(overlay);
    let mut body = nested;
    for _link in 0 .. links.0 {
        let left = occurrence(
            overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(0_u32),
        );
        let right = occurrence(
            overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(1_u32),
        );
        body = pair(overlay, left, right);
        nested = share(overlay, ShareArity::from(2_u32), nested, body);
    }
    (nested, body)
}

/// `⟨x₀, y₀[y₀ ← x₁]⟩[x₀ x₁ ← ⟨⟨⟩, ⟨⟩⟩]`: an inner share whose leg is an
/// occurrence of the outer one.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the outer share, whose second occurrence stands as the inner
///   share's leg and so counts from outside the inner share.
/// - provides: the root the scope and purity cases measure: nine nodes, two
///   shares of three occurrences nested two deep, standing for seven nodes.
/// - panics: when a mint is refused, which only the id ceiling causes.
///
/// # Adequacy
/// - hypothesis: L3 — counting an occurrence in a leg from inside its own share
///   changes the refusal or expanded size; adding unrelated nodes must not
///   change this root-local tuple.
/// - witness: `measure::tests::a_leg_reads_the_shares_outside_its_own`
/// - witness: `measure::tests::the_measure_is_a_function_of_what_the_root_reaches`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "parity: the check measures the nine nodes the body minted, each once"
    )
)]
#[spec(
        ensures: |ret| SharingMeasure::of(overlay, OverlayId::Value(ret)) == Ok(SharingMeasure { shares: ShareCount(2), occurrences: OccurrenceCount(3), depth: ShareDepth(2), nodes: NodeCount(9), expansion: ExpansionSize(7) })
    )]
fn leg_scope_case(overlay: &mut Overlay) -> OverlayValueId
{
    let first = unit(overlay);
    let second = unit(overlay);
    let leg = pair(overlay, first, second);
    let read_outer = only_occurrence(overlay);
    let inner_leg = occurrence(
        overlay,
        ShareDistance::from(0_u32),
        SharePosition::from(1_u32),
    );
    let read_inner = only_occurrence(overlay);
    let inner = share(overlay, ShareArity::from(1_u32), inner_leg, read_inner);
    let body = pair(overlay, read_outer, inner);
    share(overlay, ShareArity::from(2_u32), leg, body)
}

/// Measure a value root, refusal included.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`SharingMeasure::of`] at the value root `root`.
/// - provides: the one call every case below measures through.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3/L1 — changing the root or replacing a refusal with a
///   measure changes the exact values, fault payloads and independently counted
///   erasures observed by the callers.
/// - witness: `measure::tests::an_invalid_overlay_is_refused_by_name_before_measuring`
/// - witness: `measure::measure::the_expansion_size_is_what_the_unshared_walk_visits`
#[spec(
        ensures: |ret| ret == SharingMeasure::of(overlay, OverlayId::Value(root))
    )]
fn measured(
    overlay: &Overlay,
    root: OverlayValueId,
) -> Result<SharingMeasure, MeasureFault>
{
    SharingMeasure::of(overlay, OverlayId::Value(root))
}

#[test]
fn a_share_with_many_occurrences_inlines_its_leg_at_each()
{
    let mut overlay = Overlay::new();
    let first = unit(&mut overlay);
    let second = unit(&mut overlay);
    let leg = pair(&mut overlay, first, second);
    let mut body = only_occurrence(&mut overlay);
    for position in 1 .. OCCURRENCES {
        let read = occurrence(
            &mut overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(position),
        );
        body = pair(&mut overlay, body, read);
    }
    let root = share(&mut overlay, ShareArity::from(OCCURRENCES), leg, body);
    assert_eq!(
        Ok(SharingMeasure {
            shares: ShareCount(1),
            occurrences: OccurrenceCount(1_000),
            depth: ShareDepth(1),
            nodes: NodeCount(2_003),
            expansion: ExpansionSize(3_999),
        }),
        measured(&overlay, root),
        "the three-node leg counts once among the nodes and three times per occurrence in \
             the expansion, beside the 999 pairs that hold the occurrences"
    );
}

#[test]
fn the_share_depth_is_the_longest_chain_of_nested_shares()
{
    let mut overlay = Overlay::new();
    let short_bodies = body_chain(&mut overlay, Links(3));
    let long_legs = leg_chain(&mut overlay, Links(5));
    let long_bodies = body_chain(&mut overlay, Links(5));
    let short_legs = leg_chain(&mut overlay, Links(3));
    assert_eq!(
        Ok(SharingMeasure {
            shares: ShareCount(3),
            occurrences: OccurrenceCount(3),
            depth: ShareDepth(3),
            nodes: NodeCount(13),
            expansion: ExpansionSize(7),
        }),
        measured(&overlay, short_bodies),
        "a chain of three shares nested through their bodies is three deep"
    );
    assert_eq!(
        Ok(SharingMeasure {
            shares: ShareCount(5),
            occurrences: OccurrenceCount(5),
            depth: ShareDepth(5),
            nodes: NodeCount(11),
            expansion: ExpansionSize(1),
        }),
        measured(&overlay, long_legs),
        "a chain of five shares nested through their legs is five deep, and stands for the \
             one unit at its bottom"
    );
    let legs_longer = pair(&mut overlay, short_bodies, long_legs);
    let bodies_longer = pair(&mut overlay, long_bodies, short_legs);
    assert_eq!(
        Ok(SharingMeasure {
            shares: ShareCount(8),
            occurrences: OccurrenceCount(8),
            depth: ShareDepth(5),
            nodes: NodeCount(25),
            expansion: ExpansionSize(9),
        }),
        measured(&overlay, legs_longer),
        "two sibling chains measure the longer, here the right one"
    );
    assert_eq!(
        Ok(SharingMeasure {
            shares: ShareCount(8),
            occurrences: OccurrenceCount(8),
            depth: ShareDepth(5),
            nodes: NodeCount(29),
            expansion: ExpansionSize(13),
        }),
        measured(&overlay, bodies_longer),
        "and here the left one"
    );
}

#[test]
fn an_occurrence_free_root_measures_its_own_size()
{
    let mut core = CoreArena::new();
    let held_unit = core.value_unit();
    let held = core.value_tuple(&[held_unit, held_unit]);

    let mut overlay = Overlay::new();
    let left = unit(&mut overlay);
    let opaque = overlay
        .mint_value(ValueNode::Opaque(held))
        .expect("an opaque node names no overlay child");
    let injected = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Injection(
            Side::Left,
            opaque,
        )))
        .expect("the injected value resolves");
    let root = pair(&mut overlay, left, injected);
    assert_eq!(
        Ok(SharingMeasure {
            shares: ShareCount(0),
            occurrences: OccurrenceCount(0),
            depth: ShareDepth(0),
            nodes: NodeCount(4),
            expansion: ExpansionSize(4),
        }),
        measured(&overlay, root),
        "with no share the expansion is the node count, the opaque pair counting once"
    );

    let scrutinee = overlay
        .mint_value(ValueNode::Opaque(held))
        .expect("an opaque node names no overlay child");
    let returned_left = unit(&mut overlay);
    let on_left = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Return(returned_left)))
        .expect("the returned value resolves");
    let returned_right = unit(&mut overlay);
    let on_right = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Return(returned_right)))
        .expect("the returned value resolves");
    let case = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Case {
            scrutinee,
            on_left,
            on_right,
        }))
        .expect("the scrutinee and both branches resolve");
    assert_eq!(
        Ok(SharingMeasure {
            shares: ShareCount(0),
            occurrences: OccurrenceCount(0),
            depth: ShareDepth(0),
            nodes: NodeCount(6),
            expansion: ExpansionSize(6),
        }),
        SharingMeasure::of(&overlay, OverlayId::Computation(case)),
        "a computation root of three children measures the same way"
    );
}

#[test]
fn a_leg_reads_the_shares_outside_its_own()
{
    let mut overlay = Overlay::new();
    let root = leg_scope_case(&mut overlay);
    assert_eq!(
        Ok(SharingMeasure {
            shares: ShareCount(2),
            occurrences: OccurrenceCount(3),
            depth: ShareDepth(2),
            nodes: NodeCount(9),
            expansion: ExpansionSize(7),
        }),
        measured(&overlay, root),
        "the inner leg is an occurrence of the outer share, so the inner body stands for the \
             outer leg's three nodes: one pair, then three nodes at each of two places"
    );
}

#[test]
fn an_occurrence_reads_the_leg_its_distance_names()
{
    let mut overlay = Overlay::new();
    let first = unit(&mut overlay);
    let second = unit(&mut overlay);
    let outer_leg = pair(&mut overlay, first, second);
    let read_outer_first = only_occurrence(&mut overlay);
    let inner_leg = unit(&mut overlay);
    let read_outer_second = occurrence(
        &mut overlay,
        ShareDistance::from(1_u32),
        SharePosition::from(1_u32),
    );
    let read_inner_first = only_occurrence(&mut overlay);
    let read_inner_second = occurrence(
        &mut overlay,
        ShareDistance::from(0_u32),
        SharePosition::from(1_u32),
    );
    let inner_reads = pair(&mut overlay, read_inner_first, read_inner_second);
    let inner_body = pair(&mut overlay, read_outer_second, inner_reads);
    let inner = share(&mut overlay, ShareArity::from(2_u32), inner_leg, inner_body);
    let outer_body = pair(&mut overlay, read_outer_first, inner);
    let root = share(&mut overlay, ShareArity::from(2_u32), outer_leg, outer_body);
    assert_eq!(
        Ok(SharingMeasure {
            shares: ShareCount(2),
            occurrences: OccurrenceCount(4),
            depth: ShareDepth(2),
            nodes: NodeCount(13),
            expansion: ExpansionSize(11),
        }),
        measured(&overlay, root),
        "the occurrence at distance one reads the outer three-node leg and the two at \
             distance zero the inner unit; read from the other end of the scope, the same \
             occurrences would stand for thirteen nodes"
    );
}

#[test]
fn a_doubling_chain_measures_in_its_own_size()
{
    let mut overlay = Overlay::new();
    let (root, _body) = doubling_chain(&mut overlay, FITTING_LINKS);
    assert_eq!(
        Ok(SharingMeasure {
            shares: ShareCount(63),
            occurrences: OccurrenceCount(126),
            depth: ShareDepth(63),
            nodes: NodeCount(253),
            expansion: ExpansionSize(u64::MAX),
        }),
        measured(&overlay, root),
        "253 nodes stand for 2^64 - 1, a size no walk over the expansion could reach, \
             measured exactly at the counter's ceiling"
    );
}

#[test]
fn an_expansion_past_the_counter_is_refused_at_its_node()
{
    let mut overlay = Overlay::new();
    let (root, body) = doubling_chain(&mut overlay, Links(64));
    let Some(&ValueNode::Shared(sharing)) = overlay.value(root)
    else {
        panic!("the chain's root is its outermost share");
    };
    let OverlayId::Value(below) = sharing.leg
    else {
        panic!("each link's leg is the value link below it");
    };
    assert_eq!(
        Ok(ExpansionSize(u64::MAX)),
        measured(&overlay, below).map(|fitting| fitting.expansion()),
        "the link below still fits the counter exactly"
    );
    assert_eq!(
        Err(MeasureFault::Overflow {
            quantity: MeasuredQuantity::Expansion,
            node: OverlayId::Value(body),
        }),
        measured(&overlay, root),
        "one link more and the outermost body's pair passes the counter, refused there \
             rather than wrapped or saturated"
    );
}

#[test]
fn an_invalid_overlay_is_refused_by_name_before_measuring()
{
    let mut elsewhere = Overlay::new();
    let _first = unit(&mut elsewhere);
    let _second = unit(&mut elsewhere);
    let foreign = unit(&mut elsewhere);

    let mut overlay = Overlay::new();
    let leaf = unit(&mut overlay);
    assert_eq!(
        Err(MeasureFault::Refused(OverlayRefusal::Unresolved {
            node: OverlayId::Value(foreign)
        })),
        measured(&overlay, foreign),
        "a root the overlay does not hold"
    );

    let open = only_occurrence(&mut overlay);
    assert_eq!(
        Err(MeasureFault::Refused(OverlayRefusal::OpenReference {
            node: OverlayId::Value(open)
        })),
        measured(&overlay, open),
        "an occurrence with no share around it"
    );

    let twice = pair(&mut overlay, leaf, leaf);
    assert_eq!(
        Err(MeasureFault::Refused(OverlayRefusal::ReachedTwice {
            node: OverlayId::Value(leaf)
        })),
        measured(&overlay, twice),
        "sharing no share names"
    );

    let short_leg = unit(&mut overlay);
    let short_read = only_occurrence(&mut overlay);
    let short = share(&mut overlay, ShareArity::from(2_u32), short_leg, short_read);
    assert_eq!(
        Err(MeasureFault::Refused(OverlayRefusal::MissingOccurrences {
            share: OverlayId::Value(short),
            arity: ShareArity::from(2_u32),
            next: SharePosition::from(1_u32),
        })),
        measured(&overlay, short),
        "a share its body under-fills"
    );

    let (overflowing, _body) = doubling_chain(&mut overlay, Links(64));
    let empty_body = unit(&mut overlay);
    let empty = share(
        &mut overlay,
        ShareArity::from(0_u32),
        overflowing,
        empty_body,
    );
    assert_eq!(
        Err(MeasureFault::Refused(OverlayRefusal::ZeroArity {
            share: OverlayId::Value(empty)
        })),
        measured(&overlay, empty),
        "a share standing for nothing is refused by validation before its leg, whose \
             expansion passes the counter, is measured"
    );
}

#[test]
fn the_measure_is_a_function_of_what_the_root_reaches()
{
    let mut overlay = Overlay::new();
    let root = leg_scope_case(&mut overlay);
    let first = measured(&overlay, root);
    assert_eq!(
        first,
        measured(&overlay, root),
        "measuring again answers the same"
    );

    let beside = unit(&mut overlay);
    let _parent = pair(&mut overlay, root, beside);
    assert_eq!(
        first,
        measured(&overlay, root),
        "a parent minted over the root changes nothing it reaches"
    );

    let mut padded = Overlay::new();
    let padding = body_chain(&mut padded, Links(4));
    let moved = leg_scope_case(&mut padded);
    assert_ne!(
        OverlayId::Value(root),
        OverlayId::Value(moved),
        "the same structure sits at other ids"
    );
    assert_eq!(
        first,
        measured(&padded, moved),
        "and measures the same in another overlay, beside nodes it does not reach"
    );
    assert!(
        measured(&padded, padding).is_ok_and(|other| Ok(other) != first),
        "while the padding measures as itself"
    );
}

#[test]
fn a_measure_that_ends_with_a_leg_still_in_scope_is_refused()
{
    use alloc::vec::Vec;

    use super::Measured;
    use super::Measuring;
    use super::Visit;

    let mut overlay = Overlay::new();
    let root = OverlayId::Value(unit(&mut overlay));
    let measuring = |legs| Measuring {
        overlay: &overlay,
        visits: Vec::from([Visit::Enter(root)]),
        legs,
        results: Vec::new(),
        shares: ShareCount::default(),
        occurrences: OccurrenceCount::default(),
        nodes: NodeCount::default(),
    };
    let leg = Measured {
        expansion: ExpansionSize(1),
        depth: ShareDepth(0),
    };
    assert_eq!(
        Ok(leg),
        measuring(Vec::new()).run(),
        "the unit measures as one node under no share"
    );
    assert_eq!(
        Err(MeasureFault::MachineInvariant),
        measuring(Vec::from([leg])).run(),
        "a leg no unbind closed is an unbalanced walk"
    );
}
