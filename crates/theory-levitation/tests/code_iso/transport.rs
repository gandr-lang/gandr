//! Transport of the generic programs across a certificate.
//!
//! For a certificate `iso : A → B`, the crate's generic programs behave
//! compatibly across the translation with no machinery beyond them:
//!
//! * `generic_eq` agreement — equality on `A`-values agrees with equality on
//!   their forward images, since a certificate neither merges nor splits
//!   equivalence classes;
//! * `serialize_value` naturality up to re-encoding — a certificate does not
//!   preserve the bytes (the codes differ), but it preserves the byte-equality
//!   relation, and re-encoding after a round trip recovers the original bytes;
//! * code-table coherence — a content-addressed code table keyed by the derived
//!   code equality commutes with an auto-isomorphism trivially (the translation
//!   acts on values, not codes) and, for a cross-code certificate, exposes the
//!   genuine code difference it bridges.

use gandr_theory_levitation::DescValue;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::generic_eq;
use gandr_theory_levitation::serialize_value;
use proptest::prelude::*;

use crate::code_iso::fixtures;
use crate::code_iso::harness::CodeIso;
use crate::code_iso::harness::CodeTable;
use crate::support::CodeSlot;
use crate::support::Grade;

/// One transported certificate: the certificate, its two boundary
/// descriptions, and the source values it is transported over.
struct Transported
{
    /// The certificate.
    iso: CodeIso,
    /// Its source description.
    source: SignDesc<Grade>,
    /// Its target description.
    target: SignDesc<Grade>,
    /// The whole finite source value space.
    values: Vec<DescValue>,
}

/// The four named certificates with their boundaries and source values.
///
/// # Specification
/// trivial.
fn transportable() -> Vec<Transported>
{
    vec![
        Transported {
            iso: fixtures::identity_bool(),
            source: fixtures::bool_two_ctor(),
            target: fixtures::bool_two_ctor(),
            values: fixtures::bool_two_ctor_values(),
        },
        Transported {
            iso: fixtures::negation_bool(),
            source: fixtures::bool_two_ctor(),
            target: fixtures::bool_two_ctor(),
            values: fixtures::bool_two_ctor_values(),
        },
        Transported {
            iso: fixtures::bool_bridge(),
            source: fixtures::bool_two_ctor(),
            target: fixtures::bool_sum(),
            values: fixtures::bool_two_ctor_values(),
        },
        Transported {
            iso: fixtures::rgb_rotate(),
            source: fixtures::rgb(),
            target: fixtures::rgb(),
            values: fixtures::rgb_values(),
        },
    ]
}

#[test]
fn generic_eq_agrees_across_every_iso()
{
    for case in transportable() {
        for left in &case.values {
            for right in &case.values {
                let source_eq = generic_eq(&case.source, left, right);
                let target_eq = generic_eq(
                    &case.target,
                    &case.iso.forward_value(left),
                    &case.iso.forward_value(right),
                );
                assert_eq!(
                    source_eq,
                    target_eq,
                    "eq on A-values agrees with eq on their images under `{}`",
                    case.iso.label()
                );
            }
        }
    }
}

#[test]
fn serialize_value_is_natural_up_to_re_encoding()
{
    for case in transportable() {
        // The byte-equality relation is preserved; the bytes themselves are
        // not, across distinct codes.
        for left in &case.values {
            for right in &case.values {
                let source_same =
                    serialize_value(&case.source, left) == serialize_value(&case.source, right);
                let target_same = serialize_value(&case.target, &case.iso.forward_value(left))
                    == serialize_value(&case.target, &case.iso.forward_value(right));
                assert_eq!(
                    source_same,
                    target_same,
                    "byte-equality is preserved across `{}` (naturality up to re-encoding)",
                    case.iso.label()
                );
            }
        }
        // Re-encoding after a round trip recovers the original bytes.
        for value in &case.values {
            let round = case.iso.backward_value(&case.iso.forward_value(value));
            assert_eq!(
                serialize_value(&case.source, &round),
                serialize_value(&case.source, value),
                "encode ∘ back ∘ fwd = encode under `{}`",
                case.iso.label()
            );
        }
    }
}

/// The slots of a description's constructor codes, in declaration order,
/// against a shared table.
///
/// # Specification
/// trivial.
fn ctor_slots(
    table: &mut CodeTable,
    desc: &SignDesc<Grade>,
) -> Vec<CodeSlot>
{
    desc.ctors
        .iter()
        .map(|ctor| table.intern(ctor.code.clone()))
        .collect()
}

#[test]
fn auto_iso_leaves_code_interning_fixed()
{
    // An auto-isomorphism acts on values, never on codes, so its source and
    // target constructor codes take the same slots.
    for iso in [
        fixtures::identity_bool(),
        fixtures::negation_bool(),
        fixtures::rgb_rotate(),
    ] {
        let mut table = CodeTable::default();
        let source_slots = ctor_slots(&mut table, iso.source());
        let target_slots = ctor_slots(&mut table, iso.target());
        assert_eq!(
            source_slots,
            target_slots,
            "the auto-isomorphism `{}` leaves code interning fixed",
            iso.label()
        );
    }
}

#[test]
fn cross_code_iso_interns_to_distinct_codes()
{
    // The bridge relates structurally distinct codes, and the table tells
    // them apart: the identification it carries is not code equality.
    let bridge = fixtures::bool_bridge();
    let mut table = CodeTable::default();
    let source_slots = ctor_slots(&mut table, bridge.source());
    let target_slots = ctor_slots(&mut table, bridge.target());
    assert_ne!(
        source_slots, target_slots,
        "the bridge's boundary codes take distinct slots (the codes genuinely differ)"
    );
    assert_eq!(
        CodeSlot::from(2_usize),
        table.size(),
        "content addressing merges the two unit codes and gives the inline sum its own slot"
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// `generic_eq` agrees across the flagship bridge over generated pairs.
    #[test]
    fn bridge_generic_eq_agreement_on_generated_pairs(
        left in proptest::sample::select(fixtures::bool_two_ctor_values()),
        right in proptest::sample::select(fixtures::bool_two_ctor_values()),
    ) {
        let iso = fixtures::bool_bridge();
        prop_assert_eq!(
            generic_eq(&fixtures::bool_two_ctor(), &left, &right),
            generic_eq(
                &fixtures::bool_sum(),
                &iso.forward_value(&left),
                &iso.forward_value(&right),
            ),
            "eq agrees across the bridge on generated pairs"
        );
    }

    /// `serialize_value` byte-equality is preserved across rotation over
    /// generated pairs.
    #[test]
    fn rotate_serialize_naturality_on_generated_pairs(
        left in proptest::sample::select(fixtures::rgb_values()),
        right in proptest::sample::select(fixtures::rgb_values()),
    ) {
        let iso = fixtures::rgb_rotate();
        let source_same =
            serialize_value(&fixtures::rgb(), &left) == serialize_value(&fixtures::rgb(), &right);
        let target_same = serialize_value(&fixtures::rgb(), &iso.forward_value(&left))
            == serialize_value(&fixtures::rgb(), &iso.forward_value(&right));
        prop_assert_eq!(
            source_same, target_same,
            "byte-equality is preserved across rotation on generated pairs"
        );
    }
}
