//! The standing leaf-shift guard, the negation guard's dual.
//!
//! Over `IntBox` (`Box = Integer`, an endo-boundary with one unbounded
//! primitive leaf), the successor/predecessor `leaf_shift` is a legitimate
//! certificate — its round trips hold on every integer — yet it is
//! replay-distinct from the identity and has no structural preimage: `IntBox`
//! has one constructor, so the only leaf-natural (constructor-permuting,
//! leaf-preserving) auto-isomorphism is the identity, while the shift moves
//! the leaf content.
//!
//! The negation guard keeps the identity of certificates from collapsing to
//! code equality; this one keeps a completeness statement about certificates
//! from ranging over every translator. Quantified over all translators,
//! completeness against structural certificates is refuted at the first
//! unbounded leaf; it holds only over translators uniform in leaf contents,
//! which exclude the shift by construction. These tests pin the facts that
//! make the shift unreachable, so a drift towards the wider quantifier breaks
//! them by name.

use gandr_theory_levitation::CodeView;
use gandr_theory_levitation::PrimTy;
use gandr_theory_levitation::ValueTypeView;
use gandr_theory_levitation::generic_eq;
use quenchant_shape::shape::Maybe;

use crate::code_iso::fixtures;
use crate::code_iso::harness::replay_disagreement;
use crate::code_iso::harness::replay_equivalent;

#[test]
fn leaf_shift_is_a_replay_distinct_auto_iso_member()
{
    let shift = fixtures::leaf_shift();
    let identity = fixtures::int_box_identity();
    let samples = fixtures::int_box_values();

    let report = shift.round_trips(&samples, &samples);
    assert!(
        bool::from(report.holds()),
        "the leaf shift round-trips on every integer, failing: {}",
        report.describe()
    );
    assert!(
        bool::from(shift.is_monomorphic()),
        "the leaf-shift boundary is monomorphic"
    );
    assert!(
        !bool::from(replay_equivalent(&shift, &identity, &samples, &samples)),
        "the leaf shift is replay-distinct from the identity (it moves every leaf)"
    );
}

#[test]
fn the_endo_boundary_is_a_single_constructor_infinite_leaf()
{
    // The structural premise the no-preimage claim rests on.
    let shift = fixtures::leaf_shift();
    assert_eq!(
        shift.source(),
        shift.target(),
        "the leaf shift is an auto-isomorphism (endo-boundary)"
    );
    let desc = fixtures::int_box();
    assert_eq!(
        1,
        desc.ctors.len(),
        "IntBox has one constructor, so the structural auto-isomorphism group is trivial"
    );
    assert!(
        matches!(desc.ctors[0].code.view(), CodeView::Field { ty, .. }
            if matches!(ty.view(), ValueTypeView::Prim(PrimTy::Integer))),
        "IntBox's sole field is the unbounded Integer leaf"
    );
}

#[test]
fn the_shift_is_witnessed_as_the_successor_with_no_structural_preimage()
{
    let shift = fixtures::leaf_shift();
    let identity = fixtures::int_box_identity();
    let samples = fixtures::int_box_values();
    let box_desc = fixtures::int_box();

    // At the leaf `0`, the first sample, the shift yields `1` and the identity
    // `0`.
    let Maybe::Present(disagreement) = replay_disagreement(&shift, &identity, &samples, &samples)
    else {
        panic!("the leaf shift disagrees with the identity under replay");
    };
    assert!(
        bool::from(generic_eq(
            &box_desc,
            &disagreement.input,
            &fixtures::int_leaf(fixtures::IntBoxLeaf::ZERO)
        )),
        "the earliest disagreement is at the leaf 0"
    );
    assert!(
        bool::from(generic_eq(
            &box_desc,
            &disagreement.left_image,
            &fixtures::int_leaf(fixtures::IntBoxLeaf::ONE)
        )),
        "the shift sends 0 to its successor 1"
    );
    assert!(
        bool::from(generic_eq(
            &box_desc,
            &disagreement.right_image,
            &fixtures::int_leaf(fixtures::IntBoxLeaf::ZERO)
        )),
        "the identity fixes 0"
    );

    // The image depends on the leaf read — distinct leaves map to distinct
    // successors — so it is no constant relabelling a leaf-uniform translator
    // could mimic.
    assert!(
        !bool::from(generic_eq(
            &box_desc,
            &shift.forward_value(&fixtures::int_leaf(fixtures::IntBoxLeaf::ZERO)),
            &shift.forward_value(&fixtures::int_leaf(fixtures::IntBoxLeaf::ONE)),
        )),
        "the shift maps distinct leaves to distinct images (it reads the content)"
    );

    // With one constructor the only leaf-natural auto-isomorphism is the
    // identity, and the shift is replay-distinct from it.
    assert_eq!(
        1,
        box_desc.ctors.len(),
        "the structural auto-isomorphism group is trivial"
    );
    assert!(
        !bool::from(replay_equivalent(&shift, &identity, &samples, &samples)),
        "no leaf-natural certificate is replay-equivalent to the shift"
    );
}
