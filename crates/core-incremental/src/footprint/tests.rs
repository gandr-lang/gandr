use alloc::collections::BTreeSet;
use alloc::vec;

use anodized::spec;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::Footprint;
use super::HoleMark;
use super::footprint_of;
use crate::boundary::ItemOrdinal;
use crate::boundary::Occurrence;
use crate::content::Opacity;
use crate::content::encode_item;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;
use crate::region::Reference;

/// The reference of the first item of `key`.
///
/// # Specification
/// trivial.
fn named(key: &ItemKey) -> Reference
{
    Reference::Item {
        key: key.clone(),
        occurrence: Occurrence::from(0_usize),
    }
}

/// The footprint of an appended item with `signature` and `body`, after
/// holes under the keys of `earlier` in their given order.
///
/// # Specification
/// - requires: the supplied signature, body and their descendants resolve in
///   `arena`; the fixture is finite.
/// - ensures: returns the appended item's transparent footprint, preserving the
///   supplied body-presence mark and type-read inclusion.
/// - panics: when the fixture is refused as out of order or has an unresolved
///   arena node.
///
/// # Adequacy
/// - hypothesis: L3 — holes and filled bodies, bound and free variables and
///   shared type/term references distinguish encoding the wrong item or losing
///   its body/position information through exact marks and read sets.
/// - witness: `footprint::tests::hole_sets_has_hole`
/// - witness: `footprint::tests::shadowed_binder_is_not_a_read`
/// - witness: `footprint::tests::free_occurrence_under_binders_is_read`
/// - witness: `footprint::tests::a_term_position_does_not_suppress_a_type_position`
#[spec(ensures: |ret| ret.opacity == Opacity::Transparent
        && ret.type_reads.is_subset(&ret.reads)
        && ret.hole == match body {
            Maybe::Absent(body::Absent::Hole) => HoleMark::Hole,
            Maybe::Present(_) => HoleMark::Filled,
        })]
fn last_footprint(
    arena: CoreArena,
    earlier: &[ItemKey],
    signature: Maybe<ValueTypeId, signature::Absent>,
    body: Maybe<ValueId, body::Absent>,
) -> Footprint
{
    let mut items: alloc::vec::Vec<Item> = earlier
        .iter()
        .enumerate()
        .map(|(position, key)| {
            Item::new(
                key.clone(),
                Declaration::new(
                    ConstantIndex::from(position),
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Absent(body::Absent::Hole),
                    OriginToken::from(position),
                ),
            )
        })
        .collect();
    items.push(Item::new(
        ItemKey::from("last"),
        Declaration::new(
            ConstantIndex::from(earlier.len()),
            signature,
            body,
            OriginToken::from(earlier.len()),
        ),
    ));
    let program = Program::new(arena, items).expect("ascending");
    let encoded = encode_item(
        program.arena(),
        program.layout(),
        ItemOrdinal::from(earlier.len()),
    );
    assert_eq!(
        encoded.content.opacity(),
        Opacity::Transparent,
        "the fixture resolves"
    );
    footprint_of(&encoded.content)
}

#[test]
fn shadowed_binder_is_not_a_read()
{
    let mut arena = CoreArena::new();
    // thunk (λ. return v0): the variable is the lambda's own binder.
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let thunk = arena.value_thunk(lambda);
    let footprint = last_footprint(
        arena,
        &[ItemKey::from("v0")],
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(thunk),
    );
    assert_eq!(
        footprint.reads().count(),
        0_usize,
        "a bound variable reads nothing, whatever an earlier item is called"
    );
}

#[test]
fn free_occurrence_under_binders_is_read()
{
    let mut arena = CoreArena::new();
    // thunk (λ. λ. return d): the constant sits under two binders.
    let constant = arena.value_constant(ConstantIndex::from(0_usize));
    let returned = arena.computation_return(constant);
    let inner = arena.computation_lambda(returned);
    let outer = arena.computation_lambda(inner);
    let thunk = arena.value_thunk(outer);
    let d = ItemKey::from("d");
    let footprint = last_footprint(
        arena,
        core::slice::from_ref(&d),
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(thunk),
    );
    assert_eq!(
        footprint.reads,
        BTreeSet::from([named(&d)]),
        "a constant under binders is a read"
    );
    assert_eq!(
        footprint.type_reads().count(),
        0_usize,
        "and not a type read"
    );
}

#[test]
fn hole_sets_has_hole()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_unit();
    let holey = last_footprint(
        arena.clone(),
        &[],
        Maybe::Present(integer),
        Maybe::Absent(body::Absent::Hole),
    );
    assert_eq!(holey.hole(), HoleMark::Hole, "a hole sets the mark");
    let filled = last_footprint(
        arena,
        &[],
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(unit),
    );
    assert_eq!(filled.hole(), HoleMark::Filled, "a body clears it");
    assert_eq!(
        (holey.opacity(), filled.opacity()),
        (Opacity::Transparent, Opacity::Transparent),
        "both resolve"
    );
}

#[test]
fn ascription_names_are_reads()
{
    let mut arena = CoreArena::new();
    let code = arena.value_constant(ConstantIndex::from(0_usize));
    let element = arena.value_type_element(code, Level::zero());
    let unit = arena.value_unit();
    let c = ItemKey::from("c");
    let footprint = last_footprint(
        arena,
        core::slice::from_ref(&c),
        Maybe::Present(element),
        Maybe::Present(unit),
    );
    assert_eq!(
        (footprint.reads, footprint.type_reads),
        (BTreeSet::from([named(&c)]), BTreeSet::from([named(&c)])),
        "a constant in the signature is a read and a type read"
    );
}

#[test]
fn type_support_holds_only_type_positions()
{
    let mut arena = CoreArena::new();
    // signature El(a); body (b, a): a is read in both positions, b only
    // among terms.
    let a = arena.value_constant(ConstantIndex::from(0_usize));
    let b = arena.value_constant(ConstantIndex::from(1_usize));
    let element = arena.value_type_element(a, Level::zero());
    let pair = arena.value_tuple(&[b, a]);
    let keys = vec![ItemKey::from("a"), ItemKey::from("b")];
    let footprint = last_footprint(arena, &keys, Maybe::Present(element), Maybe::Present(pair));
    let [ref a_key, ref b_key] = *keys.as_slice()
    else {
        panic!("two keys");
    };
    assert_eq!(
        footprint.reads,
        BTreeSet::from([named(a_key), named(b_key)]),
        "every mention is a read"
    );
    assert_eq!(
        footprint.type_reads,
        BTreeSet::from([named(a_key)]),
        "only the signature's mention is type support, though the body shares its node"
    );
}

#[test]
fn a_term_position_does_not_suppress_a_type_position()
{
    let mut arena = CoreArena::new();
    let a = arena.value_constant(ConstantIndex::from(0_usize));
    let element = arena.value_type_element(a, Level::zero());
    let key = ItemKey::from("a");
    let footprint = last_footprint(
        arena,
        core::slice::from_ref(&key),
        Maybe::Present(element),
        Maybe::Present(a),
    );
    assert_eq!(footprint.reads, BTreeSet::from([named(&key)]));
    assert_eq!(footprint.type_reads, BTreeSet::from([named(&key)]));
}

#[test]
fn a_quoted_abstract_type_reads_its_own_reference_in_type_position()
{
    let mut arena = CoreArena::new();
    let abstract_type = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let quoted = arena.value_quote(abstract_type);
    let key = ItemKey::from("a");
    let footprint = last_footprint(
        arena,
        core::slice::from_ref(&key),
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(quoted),
    );
    assert_eq!(footprint.reads, BTreeSet::from([named(&key)]));
    assert_eq!(footprint.type_reads, BTreeSet::from([named(&key)]));
}

#[test]
fn bounded_tables_separate_reachability_opacity_and_holes()
{
    let key = ItemKey::from("reachable");
    let filled = crate::content::DeclarationRoots::Value {
        signature: Maybe::Absent(signature::Absent::Unsigned),
        body: Maybe::Present(crate::boundary::NodeIndex::from(0_usize)),
        laws: Vec::new(),
        rules: Vec::new(),
    };
    let cyclic = crate::fixture::item_content(Reference::Unoccupied, &filled, &[
        crate::content::ContentNode::Tuple(vec![
            crate::boundary::NodeIndex::from(0_usize),
            crate::boundary::NodeIndex::from(1_usize),
        ]),
        crate::content::ContentNode::Constant(named(&key)),
        crate::content::ContentNode::Constant(named(&ItemKey::from("unreachable"))),
    ]);
    let footprint = footprint_of(&cyclic);
    assert_eq!(
        footprint.reads,
        BTreeSet::from([named(&key)]),
        "an entry the roots do not reach is not read"
    );
    assert_eq!(footprint.type_reads, BTreeSet::new());
    assert_eq!(
        (footprint.opacity, footprint.hole),
        (Opacity::Opaque, HoleMark::Filled),
        "the edge closing the cycle is an unresolved leaf beneath the body"
    );

    let empty = crate::fixture::item_content(
        Reference::Unoccupied,
        &crate::content::DeclarationRoots::Value {
            signature: Maybe::Absent(signature::Absent::Unsigned),
            body: Maybe::Absent(body::Absent::Hole),
            laws: Vec::new(),
            rules: Vec::new(),
        },
        &[],
    );
    let footprint = footprint_of(&empty);
    assert_eq!(
        (footprint.reads, footprint.type_reads),
        (BTreeSet::new(), BTreeSet::new())
    );
    assert_eq!(
        (footprint.opacity, footprint.hole),
        (Opacity::Transparent, HoleMark::Hole)
    );
}
