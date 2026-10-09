//! The certificate the suite checks: a paired value translator between two
//! monomorphic descriptions, its invertible-mode groupoid operations, and the
//! replay evidence discipline.
//!
//! A [`CodeIso`] is a thin wrapper over the crate's generic programs, and its
//! evidence is replay: [`CodeIso::round_trips`] checks `back ∘ fwd ≡ id` and
//! `fwd ∘ back ≡ id` up to `generic_eq`, and two certificates are the same
//! transformation exactly when they are [`replay_equivalent`]. Neither is an
//! equality on codes; the negation guard is why.
//!
//! Composition is the invertible mode ([`CodeIso::compose_invertible`]): it
//! carries no acyclicity gate, because both members carry an inverse by
//! construction, and it declines only on a boundary mismatch, which is a
//! domain error rather than a refusal.

use alloc::sync::Arc;
use std::collections::HashMap;

use anodized::spec;
use gandr_theory_levitation::Code;
use gandr_theory_levitation::DescValue;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::generic_eq;
use quenchant_shape::shape::Maybe;

use crate::support::CodeSlot;
use crate::support::Grade;
use crate::support::MonomorphicStatus;
use crate::support::ReplayEquivalence;
use crate::support::RoundTripSampleCount;
use crate::support::RoundTripStatus;

/// One direction of a [`CodeIso`]: maps a value of the source description to
/// a value of the target description.
///
/// Shared, so the groupoid operations re-wrap the maps without re-deriving
/// them.
pub type Translate = Arc<dyn Fn(&DescValue) -> DescValue + Send + Sync>;

/// A certificate: two description-driven value translators between two
/// monomorphic descriptions, whose evidence is the replay of its round trips.
#[derive(Clone)]
pub struct CodeIso
{
    /// A provenance label for inspection (`negation`, `Boolean ⨟ BoolSum`).
    label: Name,
    /// The description the forward translator reads.
    source: SignDesc<Grade>,
    /// The description the forward translator writes.
    target: SignDesc<Grade>,
    /// The forward translator `source → target`.
    forward: Translate,
    /// The backward translator `target → source`.
    backward: Translate,
}

quenchant_shape::reason_enum! {
    /// Why two certificates compose to nothing.
    pub mod composition {
        /// The reason the composite is absent.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The first certificate's target is not the second's source.
            BoundaryMismatch,
        }
    }
}

impl CodeIso
{
    /// A certificate from its label, boundary descriptions and translators.
    ///
    /// # Specification
    /// trivial.
    pub fn new<L>(
        label: L,
        source: SignDesc<Grade>,
        target: SignDesc<Grade>,
        forward: Translate,
        backward: Translate,
    ) -> Self
    where
        L: Into<Name>,
    {
        Self {
            label: label.into(),
            source,
            target,
            forward,
            backward,
        }
    }

    /// The identity certificate on `desc`, the groupoid unit.
    ///
    /// # Specification
    /// trivial.
    pub fn identity<L>(
        label: L,
        desc: SignDesc<Grade>,
    ) -> Self
    where
        L: Into<Name>,
    {
        let forward: Translate = Arc::new(DescValue::clone);
        let backward: Translate = Arc::new(DescValue::clone);
        Self::new(label, desc.clone(), desc, forward, backward)
    }

    /// The certificate's provenance label.
    ///
    /// # Specification
    /// trivial.
    pub const fn label(&self) -> &Name
    {
        &self.label
    }

    /// The source description.
    ///
    /// # Specification
    /// trivial.
    pub const fn source(&self) -> &SignDesc<Grade>
    {
        &self.source
    }

    /// The target description.
    ///
    /// # Specification
    /// trivial.
    pub const fn target(&self) -> &SignDesc<Grade>
    {
        &self.target
    }

    /// Whether both boundary descriptions are parameter-free.
    ///
    /// # Specification
    /// trivial.
    pub fn is_monomorphic(&self) -> MonomorphicStatus
    {
        MonomorphicStatus::from(self.source.params.is_empty() && self.target.params.is_empty())
    }

    /// The forward translator applied to a source value.
    ///
    /// # Specification
    /// trivial.
    pub fn forward_value(
        &self,
        value: &DescValue,
    ) -> DescValue
    {
        (self.forward)(value)
    }

    /// The backward translator applied to a target value.
    ///
    /// # Specification
    /// trivial.
    pub fn backward_value(
        &self,
        value: &DescValue,
    ) -> DescValue
    {
        (self.backward)(value)
    }

    /// The inverse certificate: the two translators and the two boundaries
    /// swapped.
    ///
    /// # Specification
    /// trivial.
    pub fn inverse(&self) -> Self
    {
        Self {
            label: Name::from(format!("{}⁻¹", self.label)),
            source: self.target.clone(),
            target: self.source.clone(),
            forward: Arc::clone(&self.backward),
            backward: Arc::clone(&self.forward),
        }
    }

    /// Invertible-mode composition `self ⨟ next`, the groupoid composite
    /// `source → next.target`.
    ///
    /// # Specification
    /// - ensures: the composite whose forward is `next.forward ∘ self.forward`
    ///   and whose backward is `self.backward ∘ next.backward` when
    ///   `self.target` equals `next.source`; otherwise
    ///   [`composition::Absent::BoundaryMismatch`]. There is no acyclicity
    ///   gate.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — matching and mismatched descriptions are observed
    ///   through refusal and composite replay. The noncommuting three-value
    ///   permutations detect reversed forward or backward composition, beyond
    ///   the group laws; arbitrary translators remain outside this finite
    ///   witness.
    /// - witness: `tests::code_iso::certificates::invertible_composition_declines_only_on_a_boundary_mismatch`
    /// - witness: `tests::code_iso::harness::tests::composition_preserves_noncommuting_order`
    #[spec(ensures: |ref result| match *result {
        | Maybe::Present(ref composite) => self.target == next.source
            && (&composite.source, &composite.target) == (&self.source, &next.target),
        | Maybe::Absent(composition::Absent::BoundaryMismatch) => self.target != next.source,
    })]
    pub fn compose_invertible(
        &self,
        next: &Self,
    ) -> Maybe<Self, composition::Absent>
    {
        if self.target != next.source {
            return Maybe::Absent(composition::Absent::BoundaryMismatch);
        }
        let self_forward = Arc::clone(&self.forward);
        let next_forward = Arc::clone(&next.forward);
        let self_backward = Arc::clone(&self.backward);
        let next_backward = Arc::clone(&next.backward);
        let forward: Translate = Arc::new(move |value| next_forward(&self_forward(value)));
        let backward: Translate = Arc::new(move |value| self_backward(&next_backward(value)));
        Maybe::Present(Self {
            label: Name::from(format!("{} ⨟ {}", self.label, next.label)),
            source: self.source.clone(),
            target: next.target.clone(),
            forward,
            backward,
        })
    }

    /// Replay the round trips of this certificate against `generic_eq` over
    /// the given samples.
    ///
    /// # Specification
    /// - requires: `source_samples` are values of [`Self::source`] and
    ///   `target_samples` values of [`Self::target`].
    /// - ensures: a report recording every sample whose round trip `generic_eq`
    ///   does not relate to it, in sample order, source samples first; the
    ///   certificate holds exactly when the report does.
    /// - panics: a translator's panic propagates.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite valid descriptions include exhaustive
    ///   invertible maps and a deliberately non-invertible map with repeated
    ///   failing samples. Exact direction, original, image and count
    ///   observations detect omitted, reordered or deduplicated failures and
    ///   swapped directions; empty samples constrain the zero boundary, not
    ///   unobserved values of an infinite type.
    /// - witness: `tests::code_iso::certificates::every_named_iso_holds_its_round_trips_exhaustively`
    /// - witness: `tests::code_iso::harness::tests::round_trip_failures_keep_direction_order_and_multiplicity`
    #[spec(ensures: |ref report| report.forward_checked == RoundTripSampleCount::from(source_samples.len())
        && report.backward_checked == RoundTripSampleCount::from(target_samples.len())
        && report.failures.len() <= source_samples.len().saturating_add(target_samples.len())
        && report.failures.iter().all(|failure| match failure.direction {
            | Direction::BackAfterForward => source_samples.contains(&failure.original)
                && !bool::from(generic_eq(&self.source, &failure.round_tripped, &failure.original)),
            | Direction::ForwardAfterBackward => target_samples.contains(&failure.original)
                && !bool::from(generic_eq(&self.target, &failure.round_tripped, &failure.original)),
        })
        && report.failures.iter().skip_while(|failure| failure.direction == Direction::BackAfterForward)
            .all(|failure| failure.direction == Direction::ForwardAfterBackward))]
    pub fn round_trips(
        &self,
        source_samples: &[DescValue],
        target_samples: &[DescValue],
    ) -> RoundTripReport
    {
        let mut failures = Vec::new();
        for value in source_samples {
            let round = self.backward_value(&self.forward_value(value));
            if !bool::from(generic_eq(&self.source, &round, value)) {
                failures.push(RoundTripFailure {
                    direction: Direction::BackAfterForward,
                    original: value.clone(),
                    round_tripped: round,
                });
            }
        }
        for value in target_samples {
            let round = self.forward_value(&self.backward_value(value));
            if !bool::from(generic_eq(&self.target, &round, value)) {
                failures.push(RoundTripFailure {
                    direction: Direction::ForwardAfterBackward,
                    original: value.clone(),
                    round_tripped: round,
                });
            }
        }
        RoundTripReport {
            forward_checked: RoundTripSampleCount::from(source_samples.len()),
            backward_checked: RoundTripSampleCount::from(target_samples.len()),
            failures,
        }
    }
}

/// Which round-trip direction a [`RoundTripFailure`] records.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Direction
{
    /// `back ∘ fwd` on a source value failed to recover it.
    BackAfterForward,
    /// `fwd ∘ back` on a target value failed to recover it.
    ForwardAfterBackward,
}

/// One recorded round-trip failure: the original value, what it
/// round-tripped to, and in which direction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoundTripFailure
{
    /// The direction whose round trip failed.
    pub direction: Direction,
    /// The value fed into the round trip.
    pub original: DescValue,
    /// The value the round trip produced.
    pub round_tripped: DescValue,
}

/// The result of replaying a certificate's round trips.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoundTripReport
{
    /// The number of source samples checked through `back ∘ fwd`.
    pub forward_checked: RoundTripSampleCount,
    /// The number of target samples checked through `fwd ∘ back`.
    pub backward_checked: RoundTripSampleCount,
    /// Every round-trip failure witnessed; empty means the certificate holds.
    pub failures: Vec<RoundTripFailure>,
}

impl RoundTripReport
{
    /// Whether every replayed round trip held.
    ///
    /// # Specification
    /// trivial.
    pub fn holds(&self) -> RoundTripStatus
    {
        RoundTripStatus::from(self.failures.is_empty())
    }

    /// The failures in the direction each was replayed, rendered for an
    /// assertion message.
    ///
    /// # Specification
    /// trivial.
    pub fn describe(&self) -> String
    {
        self.failures
            .iter()
            .map(|failure| match failure.direction {
                | Direction::BackAfterForward => "back ∘ fwd",
                | Direction::ForwardAfterBackward => "fwd ∘ back",
            })
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// The first point at which two same-boundary certificates disagree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Disagreement
{
    /// The sample the two certificates were applied to.
    pub input: DescValue,
    /// The first certificate's image of it.
    pub left_image: DescValue,
    /// The second certificate's image of it.
    pub right_image: DescValue,
}

quenchant_shape::reason_enum! {
    /// Why two certificates disagree nowhere.
    pub mod disagreement {
        /// The reason no disagreement is witnessed.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The certificates replay alike on every sample.
            Equivalent,
        }
    }
}

/// Whether two certificates over one boundary are the same transformation,
/// decided over the given samples.
///
/// # Specification
/// - requires: `left` and `right` share a boundary; the samples are values of
///   it.
/// - ensures: positive exactly when [`replay_disagreement`] finds nothing.
/// - panics: on a boundary mismatch, a test-author error, or a translator
///   panic.
///
/// # Adequacy
/// - hypothesis: L3 — shared finite boundaries distinguish agreement and a
///   backward-only disagreement; empty samples agree, while a mismatched
///   boundary is refused before replay. These observers detect ignoring
///   backward replay or its domain restriction; sampled agreement is not a
///   universal certificate.
/// - witness: `tests::code_iso::harness::tests::disagreement_search_reaches_backward_samples`
/// - witness: `tests::code_iso::harness::tests::equivalence_rejects_mismatched_boundaries`
#[spec(requires: left.source == right.source && left.target == right.target)]
pub fn replay_equivalent(
    left: &CodeIso,
    right: &CodeIso,
    source_samples: &[DescValue],
    target_samples: &[DescValue],
) -> ReplayEquivalence
{
    ReplayEquivalence::from(matches!(
        replay_disagreement(left, right, source_samples, target_samples),
        Maybe::Absent(disagreement::Absent::Equivalent)
    ))
}

/// The first point at which two same-boundary certificates disagree under
/// replay.
///
/// # Specification
/// - requires: as [`replay_equivalent`].
/// - ensures: the earliest sample where the two forward images (source samples
///   first) or the two backward images differ under `generic_eq`, with both
///   images; [`disagreement::Absent::Equivalent`] when there is none.
/// - panics: on a boundary mismatch, a test-author error, or a translator
///   panic.
///
/// # Adequacy
/// - hypothesis: L3 — forward and backward-only disagreements expose exact
///   first input and both images; no samples expose equivalence. These
///   observations reject skipped backward search, later-sample selection and
///   swapped images; a rejected boundary is a domain check, not an equivalence
///   verdict.
/// - witness: `tests::code_iso::harness::tests::disagreement_search_reaches_backward_samples`
/// - witness: `tests::code_iso::harness::tests::disagreement_rejects_mismatched_boundaries`
/// - witness: `tests::code_iso::negation_guard::the_disagreement_is_witnessed_on_false`
#[spec(requires: left.source == right.source && left.target == right.target,
    ensures: |ref result| match *result {
        | Maybe::Present(ref disagreement) =>
            (source_samples.contains(&disagreement.input)
                && !bool::from(generic_eq(&left.target, &disagreement.left_image, &disagreement.right_image)))
            || (target_samples.contains(&disagreement.input)
                && !bool::from(generic_eq(&left.source, &disagreement.left_image, &disagreement.right_image))),
        | Maybe::Absent(disagreement::Absent::Equivalent) => true,
    })]
pub fn replay_disagreement(
    left: &CodeIso,
    right: &CodeIso,
    source_samples: &[DescValue],
    target_samples: &[DescValue],
) -> Maybe<Disagreement, disagreement::Absent>
{
    assert!(
        left.source == right.source && left.target == right.target,
        "replay comparison is only defined between certificates over one boundary"
    );
    for value in source_samples {
        let left_image = left.forward_value(value);
        let right_image = right.forward_value(value);
        if !bool::from(generic_eq(&left.target, &left_image, &right_image)) {
            return Maybe::Present(Disagreement {
                input: value.clone(),
                left_image,
                right_image,
            });
        }
    }
    for value in target_samples {
        let left_image = left.backward_value(value);
        let right_image = right.backward_value(value);
        if !bool::from(generic_eq(&left.source, &left_image, &right_image)) {
            return Maybe::Present(Disagreement {
                input: value.clone(),
                left_image,
                right_image,
            });
        }
    }
    Maybe::Absent(disagreement::Absent::Equivalent)
}

/// A content-addressed code table: one slot per structurally distinct code,
/// keyed by the crate's derived code equality and hash.
#[derive(Default)]
#[repr(transparent)]
pub struct CodeTable
{
    /// The slot each distinct code was given, in insertion order.
    slots: HashMap<Code<Grade>, CodeSlot>,
}

impl CodeTable
{
    /// The slot of `code`, minting the next one for a code not yet held.
    ///
    /// # Specification
    /// - ensures: equal codes receive equal slots; a code unequal to every held
    ///   one receives the next unused slot.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — interleaving repeated and distinct codes observes
    ///   exact first-insertion slots and table size. It rejects duplicate
    ///   allocation, collisions and allocating before checking for an existing
    ///   code; it does not establish collision resistance beyond structural
    ///   equality.
    /// - witness: `tests::code_iso::harness::tests::interning_reuses_slots_without_advancing_the_fresh_slot`
    /// - witness: `tests::code_iso::transport::cross_code_iso_interns_to_distinct_codes`
    #[spec(captures: [before = self.slots.len(), existing = self.slots.get(&code).copied()],
        ensures: |slot| match existing {
            | Some(previous) => slot == previous && self.slots.len() == before,
            | None => slot == CodeSlot::from(before) && self.slots.len() == before.saturating_add(1),
        })]
    pub fn intern(
        &mut self,
        code: Code<Grade>,
    ) -> CodeSlot
    {
        let next = CodeSlot::from(self.slots.len());
        *self.slots.entry(code).or_insert(next)
    }

    /// How many distinct codes the table holds.
    ///
    /// # Specification
    /// trivial.
    pub fn size(&self) -> CodeSlot
    {
        CodeSlot::from(self.slots.len())
    }
}

#[cfg(test)]
mod tests
{
    use gandr_theory_levitation::ConstructorTag;

    use super::*;
    use crate::code_iso::fixtures;

    #[test]
    fn composition_preserves_noncommuting_order()
    {
        let swap: Translate = Arc::new(|value| {
            DescValue::new(
                ConstructorTag::from(match usize::from(value.ctor) {
                    | 0 => 1_usize,
                    | 1 => 0,
                    | _ => 2,
                }),
                value.payload.clone(),
            )
        });
        let reflection = CodeIso::new(
            "swap",
            fixtures::rgb(),
            fixtures::rgb(),
            Arc::clone(&swap),
            swap,
        );
        let Maybe::Present(composed) = fixtures::rgb_rotate().compose_invertible(&reflection)
        else {
            panic!("matching boundaries");
        };
        for (value, expected) in fixtures::rgb_values().iter().zip([0_usize, 2, 1]) {
            let expected = DescValue::new(ConstructorTag::from(expected), value.payload.clone());
            assert_eq!(composed.forward_value(value), expected);
            assert_eq!(composed.backward_value(value), expected);
        }
    }

    #[test]
    fn round_trip_failures_keep_direction_order_and_multiplicity()
    {
        let [zero, one] = <[DescValue; 2]>::try_from(fixtures::bool_two_ctor_values())
            .expect("two Boolean values");
        let forward_value = zero.clone();
        let backward_value = one.clone();
        let bad = CodeIso::new(
            "constant",
            fixtures::bool_two_ctor(),
            fixtures::bool_two_ctor(),
            Arc::new(move |_| forward_value.clone()),
            Arc::new(move |_| backward_value.clone()),
        );
        let source = [zero.clone(), one.clone(), zero.clone()];
        let target = [one.clone(), zero.clone(), one.clone()];
        let source_failure = RoundTripFailure {
            direction: Direction::BackAfterForward,
            original: zero.clone(),
            round_tripped: one.clone(),
        };
        let target_failure = RoundTripFailure {
            direction: Direction::ForwardAfterBackward,
            original: one,
            round_tripped: zero,
        };
        let report = bad.round_trips(&source, &target);
        assert_eq!(report, RoundTripReport {
            forward_checked: RoundTripSampleCount::from(3_usize),
            backward_checked: RoundTripSampleCount::from(3_usize),
            failures: vec![
                source_failure.clone(),
                source_failure,
                target_failure.clone(),
                target_failure
            ]
        });
        assert!(!bool::from(report.holds()));
        assert_eq!(bad.round_trips(&[], &[]), RoundTripReport {
            forward_checked: RoundTripSampleCount::from(0_usize),
            backward_checked: RoundTripSampleCount::from(0_usize),
            failures: vec![]
        });
    }

    #[test]
    fn disagreement_search_reaches_backward_samples()
    {
        let identity = fixtures::identity_bool();
        let negation = fixtures::negation_bool();
        let backward_only = CodeIso::new(
            "backward-only",
            fixtures::bool_two_ctor(),
            fixtures::bool_two_ctor(),
            Arc::new(DescValue::clone),
            Arc::new(move |value| negation.backward_value(value)),
        );
        let source = fixtures::bool_two_ctor_values();
        let [zero, one] = <[DescValue; 2]>::try_from(source.clone()).expect("two Boolean values");
        let target = [one.clone(), zero.clone()];
        assert_eq!(
            replay_disagreement(&identity, &backward_only, &source, &target),
            Maybe::Present(Disagreement {
                input: one.clone(),
                left_image: one,
                right_image: zero
            })
        );
        assert!(!bool::from(replay_equivalent(
            &identity,
            &backward_only,
            &source,
            &target
        )));
        assert_eq!(
            replay_disagreement(&identity, &backward_only, &[], &[]),
            Maybe::Absent(disagreement::Absent::Equivalent)
        );
        assert!(bool::from(replay_equivalent(
            &identity,
            &backward_only,
            &[],
            &[]
        )));
        assert_eq!(
            replay_disagreement(&identity, &identity, &source, &target),
            Maybe::Absent(disagreement::Absent::Equivalent)
        );
    }

    #[test]
    fn equivalence_rejects_mismatched_boundaries()
    {
        assert!(
            std::panic::catch_unwind(|| replay_equivalent(
                &fixtures::identity_bool(),
                &fixtures::bool_bridge(),
                &[],
                &[]
            ))
            .is_err()
        );
    }

    #[test]
    fn disagreement_rejects_mismatched_boundaries()
    {
        assert!(
            std::panic::catch_unwind(|| replay_disagreement(
                &fixtures::identity_bool(),
                &fixtures::bool_bridge(),
                &[],
                &[]
            ))
            .is_err()
        );
    }

    #[test]
    fn interning_reuses_slots_without_advancing_the_fresh_slot()
    {
        let mut table = CodeTable::default();
        let first = Code::<Grade>::var("X");
        let second = Code::<Grade>::var("Y");
        let third = Code::<Grade>::var("Z");
        for (code, slot, size) in [
            (first.clone(), 0_usize, 1_usize),
            (second.clone(), 1, 2),
            (first, 0, 2),
            (third, 2, 3),
            (second, 1, 3),
        ] {
            assert_eq!(table.intern(code), CodeSlot::from(slot));
            assert_eq!(table.size(), CodeSlot::from(size));
        }
    }
}
