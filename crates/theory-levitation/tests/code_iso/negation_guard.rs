//! The standing negation guard: `CodeIso(Boolean, Boolean)` has at least two
//! replay-inequivalent members.
//!
//! The identity and negation certificates have the same source code and the
//! same target code — both are auto-isomorphisms of one description — yet
//! negation disagrees with the identity on `False`. The identity of
//! certificates is replay-equivalence, not code equality.
//!
//! Were a path between codes ever realized as decidable code equality, the
//! instance set at `(Boolean, Boolean)` would collapse to a singleton: two
//! auto-isomorphisms of one description have equal boundary codes, so a
//! code-equality identity would merge identity and negation. These tests pin
//! that the two are replay-distinct although code equality would identify
//! them, so such a collapse fails here, loudly, by name.

use anodized::spec;
use gandr_theory_levitation::ConstructorTag;
use gandr_theory_levitation::DescValue;
use gandr_theory_levitation::Payload;
use gandr_theory_levitation::generic_eq;
use quenchant_shape::shape::Maybe;

use crate::code_iso::fixtures;
use crate::code_iso::harness::CodeIso;
use crate::code_iso::harness::replay_disagreement;
use crate::code_iso::harness::replay_equivalent;
use crate::support::ReplayClassCount;

#[test]
fn code_iso_bool_bool_has_at_least_two_replay_inequivalent_members()
{
    let identity = fixtures::identity_bool();
    let negation = fixtures::negation_bool();
    let samples = fixtures::bool_two_ctor_values();

    assert!(
        !bool::from(replay_equivalent(&identity, &negation, &samples, &samples)),
        "identity and negation are replay-inequivalent: CodeIso(Bool, Bool) is not a singleton"
    );
    assert_eq!(
        distinct_up_to_replay(&[identity, negation], &samples, &samples),
        ReplayClassCount::from(2_usize),
        "the two transformations represent two replay classes"
    );
}

/// How many of `members` are pairwise replay-inequivalent: a greedy
/// deduplication by [`replay_equivalent`] over the samples.
///
/// # Specification
/// - requires: all members share source and target descriptions; samples belong
///   to those descriptions and translators are deterministic on them.
/// - ensures: the number of greedy representatives of sample replay
///   equivalence.
/// - panics: on a boundary mismatch or a translator panic.
///
/// # Adequacy
/// - hypothesis: L3 — empty, singleton and repeated identity/negation lists
///   expose exact class counts; an empty corpus collapses nonempty lists to one
///   class. These observations detect counting members, dropping negation or
///   discarding the empty-list boundary; mixed boundaries refuse instead of
///   being compared. The quotient is over deterministic replay on these
///   samples, not all values.
/// - witness: `tests::code_iso::negation_guard::replay_classes_handle_empty_and_repeated_members`
/// - witness: `tests::code_iso::negation_guard::code_iso_bool_bool_has_at_least_two_replay_inequivalent_members`
#[spec(requires: members.iter().zip(members.iter().skip(1)).all(|(left, right)|
    (left.source(), left.target()) == (right.source(), right.target())),
    ensures: |count| usize::from(count) <= members.len()
        && (usize::from(count) == 0) == members.is_empty()
        && (!(source_samples.is_empty() && target_samples.is_empty())
            || usize::from(count) == usize::from(!members.is_empty())))]
fn distinct_up_to_replay(
    members: &[CodeIso],
    source_samples: &[DescValue],
    target_samples: &[DescValue],
) -> ReplayClassCount
{
    let mut representatives: Vec<&CodeIso> = Vec::new();
    for member in members {
        let already = representatives.iter().any(|representative| {
            bool::from(replay_equivalent(
                representative,
                member,
                source_samples,
                target_samples,
            ))
        });
        if !already {
            representatives.push(member);
        }
    }
    ReplayClassCount::from(representatives.len())
}

#[test]
fn identity_and_negation_share_their_boundary_codes()
{
    // The premise decidable code equality would exploit: both are
    // auto-isomorphisms of one description, so their source codes coincide
    // and their target codes coincide. Only replay tells them apart.
    let identity = fixtures::identity_bool();
    let negation = fixtures::negation_bool();
    assert_eq!(
        identity.source(),
        negation.source(),
        "identity and negation have the same source code"
    );
    assert_eq!(
        identity.target(),
        negation.target(),
        "identity and negation have the same target code"
    );
    assert_eq!(
        identity.source(),
        identity.target(),
        "the boundary is the endo-boundary (Boolean, Boolean)"
    );
}

#[test]
fn the_disagreement_is_witnessed_on_false()
{
    // At `False` the identity yields `False` and negation yields `True`; were
    // the identity of certificates code equality, no such witness could
    // exist.
    let identity = fixtures::identity_bool();
    let negation = fixtures::negation_bool();
    let samples = fixtures::bool_two_ctor_values();
    let false_value = DescValue::new(ConstructorTag::from(0_usize), Payload::unit());
    let true_value = DescValue::new(ConstructorTag::from(1_usize), Payload::unit());

    let Maybe::Present(disagreement) =
        replay_disagreement(&identity, &negation, &samples, &samples)
    else {
        panic!("identity and negation disagree under replay");
    };
    let boolean = fixtures::bool_two_ctor();
    assert!(
        bool::from(generic_eq(&boolean, &disagreement.input, &false_value)),
        "the earliest disagreement is on False"
    );
    assert!(
        bool::from(generic_eq(&boolean, &disagreement.left_image, &false_value)),
        "the identity fixes False"
    );
    assert!(
        bool::from(generic_eq(&boolean, &disagreement.right_image, &true_value)),
        "negation sends False to True"
    );
    assert!(
        !bool::from(generic_eq(
            &boolean,
            &disagreement.left_image,
            &disagreement.right_image
        )),
        "the two images are distinct: the collapse guard bites"
    );
}

#[test]
fn replay_classes_handle_empty_and_repeated_members()
{
    let samples = fixtures::bool_two_ctor_values();
    let identity = fixtures::identity_bool();
    let negation = fixtures::negation_bool();
    assert_eq!(
        distinct_up_to_replay(&[], &samples, &samples),
        ReplayClassCount::from(0_usize)
    );
    assert_eq!(
        distinct_up_to_replay(core::slice::from_ref(&identity), &samples, &samples),
        ReplayClassCount::from(1_usize)
    );
    let repeated = [identity.clone(), identity.clone(), negation, identity];
    assert_eq!(
        distinct_up_to_replay(&repeated, &samples, &samples),
        ReplayClassCount::from(2_usize)
    );
    assert_eq!(
        distinct_up_to_replay(&repeated, &[], &[]),
        ReplayClassCount::from(1_usize)
    );
    assert!(
        std::panic::catch_unwind(|| distinct_up_to_replay(
            &[fixtures::identity_bool(), fixtures::bool_bridge()],
            &[],
            &[]
        ))
        .is_err()
    );
}
