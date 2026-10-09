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
    /// - panics: none; `generic_eq` is total.
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
/// - panics: on a boundary mismatch, a test-author error.
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
/// - panics: on a boundary mismatch, a test-author error.
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
