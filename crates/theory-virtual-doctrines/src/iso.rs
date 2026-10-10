//! Paired replayable witnesses for reflected isomorphisms.

use alloc::vec;

use anodized::spec;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_decomposition_spaces::compose_invertible;
use quenchant_shape::shape::Maybe;

use crate::boundary::DerivationIndex;
use crate::boundary::IsoValidity;
use crate::boundary::RoundTripIdentity;
use crate::syntax::Proterm;
use crate::syntax::ProtermKind;
use crate::vdc::Derivation;
use crate::vdc::Elaborated;

/// A **pair of mutually-inverse replayable witnesses** — the engine-level
/// protype isomorphism the groupoid laws operate on.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IsoWitness
{
    /// The forward derivation `A ⇒ B`.
    pub fwd: Derivation,
    /// The backward derivation `B ⇒ A`.
    pub bwd: Derivation,
}

impl IsoWitness
{
    /// A witness from a forward/backward derivation pair.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new(
        fwd: Derivation,
        bwd: Derivation,
    ) -> Self
    {
        Self { fwd, bwd }
    }

    /// The **identity** isomorphism — the reflexive derivation both ways
    /// (groupoid identity law).
    ///
    /// # Specification
    /// - ensures: `fwd == bwd == reflexive`; valid iff `reflexive` is a
    ///   reflexive certificate (or the trivial transformation) that replays.
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the same reflexive evidence supplies both directions,
    ///   then the law suite replays both round trips.
    /// - witness: `tests::laws::tests::a_reflexive_witness_pair_is_a_valid_iso`
    #[spec(captures: expected = reflexive.clone(), ensures: |out| out.fwd == expected && out.bwd == expected)]
    pub fn identity(reflexive: Derivation) -> Self
    {
        Self {
            fwd: reflexive.clone(),
            bwd: reflexive,
        }
    }

    /// The **inverse** isomorphism — swap the witnesses (groupoid inverse law).
    ///
    /// # Specification
    /// - ensures: `fwd`/`bwd` swapped; the inverse of a valid iso is valid (the
    ///   round-trip conditions are symmetric).
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — both directions exchange, and the law suite checks
    ///   validity rather than code equality of the witnesses.
    /// - witness: `tests::laws::tests::the_inverse_of_a_valid_iso_is_valid`
    #[spec(ensures: |out| out.fwd == self.bwd && out.bwd == self.fwd)]
    pub fn inverse(&self) -> Self
    {
        Self {
            fwd: self.bwd.clone(),
            bwd: self.fwd.clone(),
        }
    }

    /// The **composite** `other ∘ self` (`self : A ≅ B`, `other : B ≅ C`) —
    /// composed in the **invertible mode** (groupoid composition law).
    ///
    /// # Specification
    /// - ensures: the forward witness grafts `self.fwd` then `other.fwd` (`A ⇒
    ///   C`) and the backward witness grafts `other.bwd` then `self.bwd` (`C ⇒
    ///   A`); elaboration uses
    ///   [`gandr_theory_decomposition_spaces::compose_invertible`], so the
    ///   composite of two valid isos is valid unconditionally (the reflection
    ///   rules).
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L1 — the predicate observes composition direction at both
    ///   codomains. Grafting and replay laws establish the engine composition,
    ///   not endpoint agreement alone.
    /// - witness: `tests::laws::tests::cell_grafting_matches_engine_composition`
    #[spec(ensures: |out| out.fwd.cod() == other.fwd.cod() && out.bwd.cod() == self.bwd.cod())]
    pub fn compose(
        &self,
        other: &Self,
    ) -> Self
    {
        Self {
            fwd: Derivation::graft(other.fwd.clone(), vec![self.fwd.clone()]),
            bwd: Derivation::graft(self.bwd.clone(), vec![other.bwd.clone()]),
        }
    }

    /// Whether this witness is a **genuine isomorphism** — both round-trips
    /// replay to the identity.
    ///
    /// # Specification
    /// - ensures: `true` iff `bwd ∘ fwd` and `fwd ∘ bwd` each elaborate (in the
    ///   invertible mode) to a **reflexive** certificate (`peak == joins_at`)
    ///   that replays in `cells`, or to the trivial transformation; a stuck or
    ///   non-reflexive round-trip yields `false`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 evidence — the validator composes the witness pair and
    ///   replays the round-trips against the store; any mutant admitting a
    ///   non-reflexive or non-replaying round-trip is caught. Boundary: a
    ///   one-direction replay failure (`protype-iso-replay-fail`) is rejected.
    /// - witness: `tests::laws::tests::a_reflexive_witness_pair_is_a_valid_iso`
    /// - witness: `tests::laws::tests::an_iso_whose_one_direction_fails_replay_is_rejected`
    /// - witness: `tests::laws::tests::the_inverse_of_a_valid_iso_is_valid`
    #[inline]
    #[must_use]
    #[spec(ensures: |out| bool::from(out) == (bool::from(round_trips_to_identity(&self.fwd.elaborate(), &self.bwd.elaborate(), cells)) && bool::from(round_trips_to_identity(&self.bwd.elaborate(), &self.fwd.elaborate(), cells))))]
    pub fn is_valid(
        &self,
        cells: &CellStore,
    ) -> IsoValidity
    {
        let fwd = self.fwd.elaborate();
        let bwd = self.bwd.elaborate();
        IsoValidity::from(
            bool::from(round_trips_to_identity(&fwd, &bwd, cells))
                && bool::from(round_trips_to_identity(&bwd, &fwd, cells)),
        )
    }
}

/// Whether composing `a` then `b` (invertible mode) yields the identity — a
/// reflexive certificate that replays, or the trivial transformation.
///
/// # Specification
/// - ensures: `true` iff both are the trivial transformation; or both are
///   certificates sharing the seam (`a.joins_at == b.overlap.peak`) whose
///   invertible composite is reflexive (`peak == joins_at`) and replays; or one
///   is trivial and the other a reflexive certificate that replays. A stuck
///   elaboration or an open round-trip yields `false`.
/// - panics: none.
#[inline]
#[must_use]
/// # Adequacy
/// - hypothesis: L3 — malformed evidence is refused by actual engine replay.
///   The predicate observes the necessary seam and round-trip endpoints;
///   endpoint agreement alone never establishes replay.
/// - witness: `tests::laws::tests::an_iso_whose_one_direction_fails_replay_is_rejected`
#[spec(ensures: |out| !bool::from(out) || match *a { Elaborated::Stuck => false, Elaborated::Trivial => match *b { Elaborated::Trivial => true, Elaborated::Stuck => false, Elaborated::Cert(ref cert) => cert.overlap.peak == cert.joins_at && bool::from(cert.replay(cells)) }, Elaborated::Cert(ref first) => match *b { Elaborated::Stuck => false, Elaborated::Trivial => first.overlap.peak == first.joins_at && bool::from(first.replay(cells)), Elaborated::Cert(ref second) => first.joins_at == second.overlap.peak && first.overlap.peak == second.joins_at } })]
fn round_trips_to_identity(
    a: &Elaborated<'_>,
    b: &Elaborated<'_>,
    cells: &CellStore,
) -> RoundTripIdentity
{
    let valid = match (a, b) {
        | (&Elaborated::Trivial, &Elaborated::Trivial) => true,
        | (&Elaborated::Cert(ref ca), &Elaborated::Cert(ref cb)) => {
            if ca.joins_at != cb.overlap.peak {
                return RoundTripIdentity::from(false);
            }
            let composite = compose_invertible(ca, cb);
            composite.overlap.peak == composite.joins_at && bool::from(composite.replay(cells))
        },
        | (&Elaborated::Trivial, &Elaborated::Cert(ref c))
        | (&Elaborated::Cert(ref c), &Elaborated::Trivial) => {
            c.overlap.peak == c.joins_at && bool::from(c.replay(cells))
        },
        | (&Elaborated::Stuck, _) | (_, &Elaborated::Stuck) => false,
    };
    RoundTripIdentity::from(valid)
}

/// A **protype isomorphism** — the reflected-syntax surface: a pair of
/// certificate-witness proterms.
///
/// Well-formed iff [`ProtypeIso::is_valid`] — `bwd ∘ fwd ≡ id` and `fwd ∘ bwd ≡
/// id`, decided by replaying the resolved [`IsoWitness`]. Only
/// [`ProtermKind::Cert`] witnesses are engine-replayable at this stage; a
/// non-certificate witness makes [`ProtypeIso::witness`] `Absent` (and the iso
/// invalid).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ProtypeIso
{
    /// The forward witness proterm.
    pub fwd: Proterm,
    /// The backward witness proterm.
    pub bwd: Proterm,
}

impl ProtypeIso
{
    /// An isomorphism from a forward/backward witness pair.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new(
        fwd: Proterm,
        bwd: Proterm,
    ) -> Self
    {
        Self { fwd, bwd }
    }

    /// Resolve the certificate witnesses to an [`IsoWitness`] over
    /// `derivations`.
    ///
    /// # Specification
    /// - ensures: `Present(witness)` iff both `fwd` and `bwd` are
    ///   [`ProtermKind::Cert`] proterms referencing derivations present in
    ///   `derivations`; `Absent` otherwise (a non-certificate witness is not
    ///   engine-replayable at this stage).
    /// - panics: none.
    #[inline]
    /// # Adequacy
    /// - hypothesis: L1 — both resolved directions retain the bound evidence;
    ///   resolution does not assert isomorphism validity.
    /// - witness: `tests::laws::tests::a_reflexive_witness_pair_is_a_valid_iso`
    #[spec(ensures: |out| match out { Maybe::Present(ref witness) => resolve_cert(&self.fwd, derivations) == Maybe::Present(&witness.fwd) && resolve_cert(&self.bwd, derivations) == Maybe::Present(&witness.bwd), Maybe::Absent(_) => matches!(resolve_cert(&self.fwd, derivations), Maybe::Absent(_)) || matches!(resolve_cert(&self.bwd, derivations), Maybe::Absent(_)) })]
    pub fn witness(
        &self,
        derivations: &[Derivation],
    ) -> Maybe<IsoWitness, witness_resolution::Absent>
    {
        resolve_cert(&self.fwd, derivations).and_then(|fwd| {
            resolve_cert(&self.bwd, derivations)
                .map(|bwd| IsoWitness::new(fwd.clone(), bwd.clone()))
        })
    }

    /// Whether this isomorphism is well-formed — its witnesses resolve and both
    /// round-trips replay to the identity.
    ///
    /// # Specification
    /// - ensures: `true` iff [`ProtypeIso::witness`] resolves and the resolved
    ///   [`IsoWitness::is_valid`] holds against `cells`.
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — both recorded directions must resolve and their two
    ///   round trips must replay; the negative fixture corrupts one direction.
    /// - witness: `tests::laws::tests::an_iso_whose_one_direction_fails_replay_is_rejected`
    #[spec(ensures: |out| bool::from(out) == match (resolve_cert(&self.fwd, derivations), resolve_cert(&self.bwd, derivations)) { (Maybe::Present(fwd), Maybe::Present(bwd)) => bool::from(round_trips_to_identity(&fwd.elaborate(), &bwd.elaborate(), cells)) && bool::from(round_trips_to_identity(&bwd.elaborate(), &fwd.elaborate(), cells)), _ => false })]
    pub fn is_valid(
        &self,
        derivations: &[Derivation],
        cells: &CellStore,
    ) -> IsoValidity
    {
        match (
            resolve_cert(&self.fwd, derivations),
            resolve_cert(&self.bwd, derivations),
        ) {
            | (Maybe::Present(fwd), Maybe::Present(bwd)) => {
                let fwd = fwd.elaborate();
                let bwd = bwd.elaborate();
                IsoValidity::from(
                    bool::from(round_trips_to_identity(&fwd, &bwd, cells))
                        && bool::from(round_trips_to_identity(&bwd, &fwd, cells)),
                )
            },
            | _ => IsoValidity::from(false),
        }
    }
}

/// Resolve a certificate witness proterm to its embedded derivation.
///
/// # Specification
/// - ensures: `Present(derivation)` iff `term` is a [`ProtermKind::Cert`] whose
///   id is present in `derivations`; `Absent` for any other proterm form or an
///   absent id.
/// - panics: none.
#[inline]
/// # Adequacy
/// - hypothesis: L1 — the predicate distinguishes syntax that is not a
///   certificate from an unbound certificate id, and projects the actual bound
///   derivation.
/// - witness: `tests::laws::tests::a_reflexive_witness_pair_is_a_valid_iso`
#[spec(ensures: |out| match *term.to_node().kind() { ProtermKind::Cert { id } => match out { Maybe::Present(derivation) => derivations.get(usize::from(DerivationIndex::from(id))) == Some(derivation), Maybe::Absent(witness_resolution::Absent::Unbound(missing)) => id == missing && derivations.get(usize::from(DerivationIndex::from(id))).is_none(), Maybe::Absent(witness_resolution::Absent::NotCertificate) => false }, _ => matches!(out, Maybe::Absent(witness_resolution::Absent::NotCertificate)) })]
fn resolve_cert<'env>(
    term: &Proterm,
    derivations: &'env [Derivation],
) -> Maybe<&'env Derivation, witness_resolution::Absent>
{
    match *term.to_node().kind() {
        | ProtermKind::Cert { id } => match derivations.get(usize::from(DerivationIndex::from(id)))
        {
            | Some(derivation) => Maybe::Present(derivation),
            | None => Maybe::Absent(witness_resolution::Absent::Unbound(id)),
        },
        | _ => Maybe::Absent(witness_resolution::Absent::NotCertificate),
    }
}
quenchant_shape::reason_enum! {
/// Why a reflected isomorphism has no engine witness.
pub mod witness_resolution {
    /// The reason the requested value is unavailable.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Absent {
    /// The witness term is not an embedded certificate.
    NotCertificate,
    /// The derivation identifier is absent from its environment.
    Unbound(crate::syntax::DerivationId),
}
}

}
