//! The certificate discipline and the invertible-mode groupoid: identity,
//! inverse and composition, all up to replay-equivalence, the only identity a
//! certificate has.

use gandr_theory_levitation::check_desc;
use gandr_theory_levitation::generic_eq;
use proptest::prelude::*;
use quenchant_shape::shape::Maybe;

use crate::code_iso::fixtures;
use crate::code_iso::harness::CodeIso;
use crate::code_iso::harness::replay_equivalent;
use crate::support::RoundTripSampleCount;

#[test]
fn every_description_is_monomorphic_and_well_formed()
{
    for desc in [
        fixtures::bool_two_ctor(),
        fixtures::bool_sum(),
        fixtures::rgb(),
    ] {
        assert!(
            desc.params.is_empty(),
            "the description is monomorphic (no parameters): {}",
            desc.id.name
        );
        assert!(
            check_desc(&desc).is_empty(),
            "the description is well-formed: {}",
            desc.id.name
        );
    }
    for iso in [
        fixtures::identity_bool(),
        fixtures::negation_bool(),
        fixtures::bool_bridge(),
        fixtures::rgb_rotate(),
    ] {
        assert!(
            bool::from(iso.is_monomorphic()),
            "the certificate boundary is monomorphic: {}",
            iso.label()
        );
    }
}

#[test]
fn every_named_iso_holds_its_round_trips_exhaustively()
{
    // The full (finite) value space of each boundary is replayed; a valid
    // certificate holds `back ∘ fwd ≡ id` and `fwd ∘ back ≡ id`.
    let cases = [
        (
            fixtures::identity_bool(),
            fixtures::bool_two_ctor_values(),
            fixtures::bool_two_ctor_values(),
        ),
        (
            fixtures::negation_bool(),
            fixtures::bool_two_ctor_values(),
            fixtures::bool_two_ctor_values(),
        ),
        (
            fixtures::bool_bridge(),
            fixtures::bool_two_ctor_values(),
            fixtures::bool_sum_values(),
        ),
        (
            fixtures::rgb_rotate(),
            fixtures::rgb_values(),
            fixtures::rgb_values(),
        ),
    ];
    for (iso, source_samples, target_samples) in cases {
        let report = iso.round_trips(&source_samples, &target_samples);
        assert!(
            bool::from(report.holds()),
            "the certificate `{}` round-trips on every value, failing: {}",
            iso.label(),
            report.describe()
        );
        assert_eq!(
            report.forward_checked,
            RoundTripSampleCount::from(source_samples.len()),
            "every source sample was replayed"
        );
        assert_eq!(
            report.backward_checked,
            RoundTripSampleCount::from(target_samples.len()),
            "every target sample was replayed"
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Negation round-trips (`back ∘ fwd ≡ id`) on every generated Boolean.
    #[test]
    fn negation_round_trips_on_generated_values(
        value in proptest::sample::select(fixtures::bool_two_ctor_values())
    ) {
        let iso = fixtures::negation_bool();
        let round = iso.backward_value(&iso.forward_value(&value));
        prop_assert!(
            bool::from(generic_eq(&fixtures::bool_two_ctor(), &round, &value)),
            "negation back∘fwd recovers the value up to generic_eq"
        );
    }

    /// The cross-code bridge round-trips forward from every generated Boolean
    /// (`back ∘ fwd ≡ id`).
    #[test]
    fn bridge_round_trips_forward_on_generated_values(
        value in proptest::sample::select(fixtures::bool_two_ctor_values())
    ) {
        let iso = fixtures::bool_bridge();
        let round = iso.backward_value(&iso.forward_value(&value));
        prop_assert!(
            bool::from(generic_eq(&fixtures::bool_two_ctor(), &round, &value)),
            "bridge back∘fwd recovers the Boolean up to generic_eq"
        );
    }

    /// The cross-code bridge round-trips backward from every generated
    /// `BoolSum` value (`fwd ∘ back ≡ id`).
    #[test]
    fn bridge_round_trips_backward_on_generated_values(
        value in proptest::sample::select(fixtures::bool_sum_values())
    ) {
        let iso = fixtures::bool_bridge();
        let round = iso.forward_value(&iso.backward_value(&value));
        prop_assert!(
            bool::from(generic_eq(&fixtures::bool_sum(), &round, &value)),
            "bridge fwd∘back recovers the BoolSum value up to generic_eq"
        );
    }

    /// Rotation round-trips (`back ∘ fwd ≡ id`) on every generated RGB value.
    #[test]
    fn rotate_round_trips_on_generated_values(
        value in proptest::sample::select(fixtures::rgb_values())
    ) {
        let iso = fixtures::rgb_rotate();
        let round = iso.backward_value(&iso.forward_value(&value));
        prop_assert!(
            bool::from(generic_eq(&fixtures::rgb(), &round, &value)),
            "rotate back∘fwd recovers the RGB value up to generic_eq"
        );
    }
}

/// The composite `first ⨟ next`, whose boundaries the caller knows match.
///
/// # Specification
/// - requires: `first.target` is `next.source`.
/// - panics: on a boundary mismatch, a test-author error.
fn composite(
    first: &CodeIso,
    next: &CodeIso,
) -> CodeIso
{
    let Maybe::Present(composed) = first.compose_invertible(next)
    else {
        panic!(
            "`{}` ⨟ `{}` shares the middle boundary",
            first.label(),
            next.label()
        );
    };
    composed
}

#[test]
fn inverse_swaps_the_boundary_and_is_involutive()
{
    let bridge = fixtures::bool_bridge();
    let inverse = bridge.inverse();
    assert_eq!(
        inverse.source().id.name,
        bridge.target().id.name,
        "the inverse's source is the original's target"
    );
    assert_eq!(
        inverse.target().id.name,
        bridge.source().id.name,
        "the inverse's target is the original's source"
    );
    assert!(
        bool::from(replay_equivalent(
            &bridge.inverse().inverse(),
            &bridge,
            &fixtures::bool_two_ctor_values(),
            &fixtures::bool_sum_values(),
        )),
        "double inverse is replay-equivalent to the original"
    );
}

#[test]
fn inverse_undoes_composition_up_to_replay()
{
    // iso ⨟ iso⁻¹ ≡ id(source) and iso⁻¹ ⨟ iso ≡ id(target).
    let bridge = fixtures::bool_bridge();
    let forward_then_back = composite(&bridge, &bridge.inverse());
    assert!(
        bool::from(replay_equivalent(
            &forward_then_back,
            &fixtures::identity_bool(),
            &fixtures::bool_two_ctor_values(),
            &fixtures::bool_two_ctor_values(),
        )),
        "iso ⨟ iso⁻¹ is replay-equivalent to the identity on the source"
    );
    let back_then_forward = composite(&bridge.inverse(), &bridge);
    assert!(
        bool::from(replay_equivalent(
            &back_then_forward,
            &CodeIso::identity("id[BoolSum]", fixtures::bool_sum()),
            &fixtures::bool_sum_values(),
            &fixtures::bool_sum_values(),
        )),
        "iso⁻¹ ⨟ iso is replay-equivalent to the identity on the target"
    );
}

#[test]
fn negation_is_self_inverse_up_to_replay()
{
    let negation = fixtures::negation_bool();
    let twice = composite(&negation, &negation);
    assert!(
        bool::from(replay_equivalent(
            &twice,
            &fixtures::identity_bool(),
            &fixtures::bool_two_ctor_values(),
            &fixtures::bool_two_ctor_values(),
        )),
        "negation ⨟ negation is replay-equivalent to the identity"
    );
}

#[test]
fn rotation_has_order_three_up_to_replay()
{
    let rotate = fixtures::rgb_rotate();
    let thrice = composite(&composite(&rotate, &rotate), &rotate);
    assert!(
        bool::from(replay_equivalent(
            &thrice,
            &CodeIso::identity("id[RGB]", fixtures::rgb()),
            &fixtures::rgb_values(),
            &fixtures::rgb_values(),
        )),
        "rotate cubed is replay-equivalent to the identity"
    );
}

#[test]
fn composition_is_associative_up_to_replay()
{
    let rotate = fixtures::rgb_rotate();
    let left = composite(&composite(&rotate, &rotate), &rotate);
    let right = composite(&rotate, &composite(&rotate, &rotate));
    assert!(
        bool::from(replay_equivalent(
            &left,
            &right,
            &fixtures::rgb_values(),
            &fixtures::rgb_values(),
        )),
        "invertible-mode composition is associative up to replay"
    );
}

#[test]
fn identity_is_a_two_sided_unit_up_to_replay()
{
    let bridge = fixtures::bool_bridge();
    let left_unit = composite(&fixtures::identity_bool(), &bridge);
    let right_unit = composite(
        &bridge,
        &CodeIso::identity("id[BoolSum]", fixtures::bool_sum()),
    );
    for unit in [&left_unit, &right_unit] {
        assert!(
            bool::from(replay_equivalent(
                unit,
                &bridge,
                &fixtures::bool_two_ctor_values(),
                &fixtures::bool_sum_values(),
            )),
            "composing with the identity is replay-equivalent to the iso alone"
        );
    }
}

#[test]
fn invertible_composition_declines_only_on_a_boundary_mismatch()
{
    // A matching boundary always composes: invertible mode is unconditional.
    let bridge = fixtures::bool_bridge();
    assert!(
        matches!(
            bridge.compose_invertible(&CodeIso::identity("id[BoolSum]", fixtures::bool_sum())),
            Maybe::Present(_)
        ),
        "a shared boundary composes unconditionally"
    );
    // A mismatched boundary is the only decline: BoolSum ≠ Boolean.
    assert!(
        matches!(
            bridge.compose_invertible(&fixtures::negation_bool()),
            Maybe::Absent(_)
        ),
        "a boundary-object mismatch is the sole decline, a domain error rather than a gate"
    );
}
