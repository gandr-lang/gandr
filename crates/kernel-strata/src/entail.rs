//! Entailment under an admitted landmark poset: `left ≤ right`, or
//! `left < right`, under the poset's order hypotheses, decided by the
//! minimal-model computation and returning checkable evidence either way — an
//! [`EntailmentWitness`], a replayable forward derivation of every goal atom;
//! or an [`EntailmentCountermodel`], the minimal model itself, which satisfies
//! the whole query system and the query body while refuting a goal atom.
//!
//! # The query encoding
//!
//! A query `left ≤ right` asks whether each atom of `left` follows from the
//! atoms of `right`, with two adjustments, both definitional and shared
//! verbatim by the oracle and the validators:
//!
//! * **Constants ride the pinned bottom generator `⊥`**, since the algebra of
//!   the loop-checking paper is constant-free: a constant part `c` becomes the
//!   atom `⊥ + c`, and one bottom clause `x → ⊥` per in-scope variable orders
//!   `⊥` below everything. The landmark-poset module records why this is sound,
//!   conservative, and loop-immune exactly for variable-only declared
//!   constraints. Under this encoding the derived maximum of `⊥` is the right
//!   side's value at the zero valuation, which is what makes empty-poset
//!   agreement with the free order oracle exact.
//! * **Everything shifts up by one**, the paper's lemma 2.1 device, used
//!   uniformly: the system takes minimum shift `1`, every in-scope variable is
//!   seeded at `0` — the lemma's body atoms — the right side seeds at `offset +
//!   1` with `⊥` at `c_right + 1`, and each goal atom asks one above its
//!   offset. This makes queries over variables missing from the body sound
//!   without a case split.
//!
//! The goal list is `⊥ + c_left + 1`, plus one more when strict, first, then
//! one goal per left atom in ascending variable order at `offset + 1`, plus one
//! more when strict; strictness is the same left shift the free order oracle
//! uses.
//!
//! Divergence cannot occur here: an admitted poset has no loop, bottom clauses
//! cannot close a cycle, and upward shifts preserve gains, so the query
//! system's minimal models are finite. The engine still guards the computation
//! and surfaces the impossible case as [`PosetError::UnexpectedDivergence`]
//! rather than trusting it.
//!
//! The primary reference is Marc Bezem and Thierry Coquand, "Loop-checking and
//! the uniform word problem for join-semilattices with an inflationary
//! endomorphism", *Theoretical Computer Science* 913 (2022), 1–7,
//! `doi:10.1016/j.tcs.2022.01.017`; entailment is its corollary 3.4.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::ops::Not;

use anodized::spec;

use crate::horn;
use crate::horn::ClauseIndex;
use crate::horn::ClauseSystem;
use crate::horn::FiringLogStep;
use crate::horn::HVar;
use crate::horn::HornAtom;
use crate::horn::HornClause;
use crate::horn::HornOffset;
use crate::horn::HornShift;
use crate::horn::ModelValue;
use crate::horn::SaturationBound;
use crate::level::Level;
use crate::level::LevelVar;
use crate::order::Strictness;
use crate::poset::Derivation;
use crate::poset::EvidenceSubject;
use crate::poset::LandmarkPoset;
use crate::poset::PosetError;
use crate::poset::PosetEvidenceError;
use crate::poset::replay_derivation;

/// Whether an entailment dichotomy is the positive branch.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EntailmentHolds(bool);

impl From<bool> for EntailmentHolds
{
    /// Wraps a dichotomy decision as the entailment answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(holds: bool) -> Self
    {
        Self(holds)
    }
}

impl From<EntailmentHolds> for bool
{
    /// Unwraps the entailment answer to a plain decision.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(holds: EntailmentHolds) -> Self
    {
        holds.0
    }
}

impl Not for EntailmentHolds
{
    type Output = Self;

    /// The opposite entailment answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn not(self) -> Self::Output
    {
        Self::from(!bool::from(self))
    }
}

/// The length of the derivation-log prefix needed to cover a query.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct WitnessPrefixLength(usize);

impl From<usize> for WitnessPrefixLength
{
    /// Wraps a raw count as a derivation-prefix length.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: usize) -> Self
    {
        Self(length)
    }
}

impl From<WitnessPrefixLength> for usize
{
    /// Unwraps a derivation-prefix length to its raw count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: WitnessPrefixLength) -> Self
    {
        length.0
    }
}

/// The positive entailment evidence: a replayable forward derivation covering
/// every goal atom of the claim from the query seeds.
///
/// Constructed only by the oracle, since the fields are private; inspected
/// through the accessors and replayed by [`validate_entailment_witness`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EntailmentWitness
{
    /// Whether this witnesses the strict order.
    strict: Strictness,
    /// The replayable derivation.
    derivation: Derivation,
}

impl EntailmentWitness
{
    /// Whether this witnesses the strict order (`left < right`).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn strict(&self) -> Strictness
    {
        self.strict
    }

    /// The replayable derivation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn derivation(&self) -> &Derivation
    {
        &self.derivation
    }
}

/// The negative entailment evidence: a model of the whole query system that
/// covers the query seeds while refuting one recorded goal atom, which is
/// exactly what non-derivability means, checkably.
///
/// Constructed only by the oracle, since the fields are private; inspected
/// through the accessors and checked by [`validate_entailment_countermodel`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EntailmentCountermodel
{
    /// Whether this refutes the strict order.
    strict: Strictness,
    /// The model's value at the bottom generator.
    bottom: ModelValue,
    /// The model's value at each in-scope variable.
    values: BTreeMap<LevelVar, ModelValue>,
    /// The refuted goal's subject.
    refuted_subject: EvidenceSubject,
    /// The refuted goal's encoded, shifted offset.
    refuted_offset: HornOffset,
}

impl EntailmentCountermodel
{
    /// Whether this refutes the strict order (`left < right`).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn strict(&self) -> Strictness
    {
        self.strict
    }

    /// The model's value at the bottom generator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn bottom_value(&self) -> ModelValue
    {
        self.bottom
    }

    /// The model's value at `variable`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some(value)` when `variable` is in the query's scope, `None`
    ///   when it is not — ordinary lookup absence, not a swallowed failure,
    ///   since the operation cannot fail.
    /// - provides: the per-variable read the countermodel validator needs.
    /// - panics: none.
    #[spec(ensures: |ret| ret == self.values.get(&variable).copied())]
    #[inline]
    #[must_use]
    pub fn value_of(
        &self,
        variable: LevelVar,
    ) -> Option<ModelValue>
    {
        self.values.get(&variable).copied()
    }

    /// The assignments in ascending variable order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields each in-scope variable exactly once with its model
    ///   value, in ascending variable order.
    /// - provides: the whole-model read the countermodel validator walks.
    /// - panics: none.
    #[inline]
    pub fn assignments(&self) -> impl Iterator<Item = (LevelVar, ModelValue)> + '_
    {
        self.values
            .iter()
            .map(|(&variable, &value)| (variable, value))
    }

    /// The refuted goal's subject.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn refuted_subject(&self) -> EvidenceSubject
    {
        self.refuted_subject
    }

    /// The refuted goal's encoded, shifted offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn refuted_offset(&self) -> HornOffset
    {
        self.refuted_offset
    }
}

/// The entailment dichotomy as data: under an admitted poset a query either
/// holds with a derivation or is refuted by a countermodel.
#[derive(Clone, Debug)]
pub enum Entailment
{
    /// The claim holds; the witness derivation replays.
    Holds(EntailmentWitness),
    /// The claim fails; the countermodel checks.
    Refuted(EntailmentCountermodel),
}

impl Entailment
{
    /// Whether this is the positive case.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn holds(&self) -> EntailmentHolds
    {
        EntailmentHolds::from(matches!(*self, Self::Holds(_)))
    }
}

/// The deterministic query encoding shared by the oracle and both validators,
/// as the module docs describe it.
pub struct QueryEncoding
{
    /// The query clause system's base clauses: the poset's compiled clauses,
    /// then one bottom clause per in-scope variable, ascending.
    clauses: Vec<HornClause>,
    /// The seeds: every in-scope variable at `0`, the right side's atoms at
    /// `offset + 1`, the bottom generator at `c_right + 1`.
    seed: BTreeMap<HVar, HornOffset>,
    /// The goals: the bottom goal first, then one per left atom, ascending;
    /// offsets already shifted.
    goals: Vec<HornAtom>,
}

/// The shared decision path of both public faces.
///
/// # Specification
/// - requires: `poset` is admitted, so its query systems have finite minimal
///   models.
/// - ensures: [`Entailment::Holds`] with the shortest covering prefix of the
///   saturation log exactly when every goal atom is covered by the minimal
///   model, and [`Entailment::Refuted`] with that model otherwise.
/// - provides: the single decision path both entailment faces share.
///   Minimal-model identity and the shortest saturation-log prefix stay prose:
///   the return value retains neither the full log nor a leastness certificate.
///   Re-running saturation would check the engine against itself.
/// - fails: [`PosetError::Overflow`] past the representable range;
///   [`PosetError::UnexpectedDivergence`] and
///   [`PosetError::EvidenceIncomplete`] only under a defect the theory
///   excludes.
/// - panics: none.
fn decide(
    poset: &LandmarkPoset,
    left: &Level,
    right: &Level,
    strict: Strictness,
) -> Result<Entailment, PosetError>
{
    let encoding = encode_query(poset, left, right, strict)?;
    let system = ClauseSystem {
        clauses: encoding.clauses,
        min_shift: HornShift::ONE,
    };
    let maxgain = system.maxgain();
    let max_seed = encoding
        .seed
        .values()
        .copied()
        .max()
        .unwrap_or(HornOffset::ZERO);
    let scope_count = u128::try_from(encoding.seed.len()).map_err(|_error| PosetError::Overflow)?;
    let headroom = scope_count
        .checked_mul(u128::from(maxgain))
        .ok_or(PosetError::Overflow)?;
    let snap_bound = u128::from(max_seed)
        .checked_add(headroom)
        .map(SaturationBound::from)
        .ok_or(PosetError::Overflow)?;
    let seed_model: BTreeMap<HVar, ModelValue> = encoding
        .seed
        .iter()
        .map(|(&variable, &value)| (variable, ModelValue::Finite(value)))
        .collect();
    let outcome =
        horn::saturate(&system, seed_model, snap_bound).map_err(|_error| PosetError::Overflow)?;
    if bool::from(outcome.diverged) {
        return Err(PosetError::UnexpectedDivergence);
    }
    let uncovered = encoding.goals.iter().copied().find(|goal| {
        !outcome
            .values
            .get(&goal.variable())
            .is_some_and(|value| bool::from(value.covers(goal.offset())))
    });
    if let Some(goal) = uncovered {
        let bottom = outcome
            .values
            .get(&HVar::Bottom)
            .copied()
            .unwrap_or(ModelValue::Finite(HornOffset::ZERO));
        let values: BTreeMap<LevelVar, ModelValue> = outcome
            .values
            .iter()
            .filter_map(|(&variable, &value)| match variable {
                | HVar::Var(level_var) => Some((level_var, value)),
                | HVar::Bottom => None,
            })
            .collect();
        return Ok(Entailment::Refuted(EntailmentCountermodel {
            strict,
            bottom,
            values,
            refuted_subject: EvidenceSubject::from_horn(goal.variable()),
            refuted_offset: goal.offset(),
        }));
    }
    let cutoff = witness_cutoff(&encoding.seed, &encoding.goals, &outcome.log)
        .ok_or(PosetError::EvidenceIncomplete)?;
    let trimmed: Vec<FiringLogStep> = outcome.log.into_iter().take(usize::from(cutoff)).collect();
    Ok(Entailment::Holds(EntailmentWitness {
        strict,
        derivation: Derivation::from_log(&trimmed),
    }))
}

impl LandmarkPoset
{
    /// Decides `left ≤ right` under this poset's hypotheses, returning
    /// checkable evidence either way.
    ///
    /// # Specification
    /// - requires: nothing beyond canonical inputs, guaranteed by construction;
    ///   queries may mention any variables, declared or not.
    /// - ensures: [`Entailment::Holds`] with a witness passing
    ///   [`validate_entailment_witness`] exactly when every goal atom of the
    ///   encoded claim is derivable; [`Entailment::Refuted`] with a
    ///   countermodel passing [`validate_entailment_countermodel`] otherwise.
    ///   With no declared constraints this agrees with [`Level::leq`] on every
    ///   input.
    /// - provides: the kernel's hypothesis-aware level order.
    /// - fails: [`PosetError::Overflow`] past the representable range;
    ///   [`PosetError::UnexpectedDivergence`] and
    ///   [`PosetError::EvidenceIncomplete`] only under a defect the theory
    ///   excludes, surfaced rather than trusted.
    /// - panics: none.
    /// - intension: the countermodel names the first uncovered goal in encoding
    ///   order, the bottom goal first and then ascending variables; the witness
    ///   derivation is the engine's firing log truncated at the step that
    ///   covers the last outstanding goal.
    ///
    /// # Errors
    /// [`PosetError::Overflow`], [`PosetError::UnexpectedDivergence`], and
    /// [`PosetError::EvidenceIncomplete`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the empty-poset property differential against the
    ///   free order oracle, exact agreement in both strictness modes, plus
    ///   evidence validation on every decided query; the L3 residues are the
    ///   hypothesis paths — landmark order used, the strict against non-strict
    ///   split, and the refusal of a non-total order — each pinned by a unit
    ///   golden.
    /// - witness: `entailment_oracle::entailment_oracle::prop_empty_poset_agrees_with_the_free_oracle`
    /// - witness: `entail::tests::landmark_order_is_entailed`
    /// - witness: `entail::tests::strictness_needs_a_strict_hypothesis`
    /// - witness: `entail::tests::non_total_order_is_refused_with_a_countermodel`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|evidence| {
        let validates = match *evidence {
            Entailment::Holds(ref witness) => witness.strict() == Strictness::NON_STRICT
                && validate_entailment_witness(self, left, right, witness).is_ok(),
            Entailment::Refuted(ref countermodel) => countermodel.strict() == Strictness::NON_STRICT
                && validate_entailment_countermodel(self, left, right, countermodel).is_ok(),
        };
        validates && (!self.constraints().is_empty()
            || bool::from(evidence.holds()) == bool::from(left.leq(right)))
    }))]
    #[inline]
    pub fn entails_leq_with_evidence(
        &self,
        left: &Level,
        right: &Level,
    ) -> Result<Entailment, PosetError>
    {
        decide(self, left, right, Strictness::NON_STRICT)
    }

    /// Decides the strict order `left < right` under this poset's hypotheses,
    /// returning checkable evidence either way.
    ///
    /// # Specification
    /// - requires: nothing beyond canonical inputs.
    /// - ensures: agrees with `left.succ()` entailed below `right` whenever the
    ///   successor is representable, and stays total where it is not, since the
    ///   shift happens in the wide encoding; on an admitted poset `left < left`
    ///   is always refuted, and admission's consistency certificate is what
    ///   keeps the universe rule's irreflexivity under hypotheses.
    /// - provides: the hypothesis-aware consistency-bearing comparison.
    /// - fails: as [`Self::entails_leq_with_evidence`].
    /// - panics: none.
    /// - intension: as [`Self::entails_leq_with_evidence`].
    ///
    /// # Errors
    /// As [`Self::entails_leq_with_evidence`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the empty-poset differential plus the law that `lt`
    ///   is `leq` after `succ` under a fixed poset; the L3 residue is
    ///   hypothesis strictness, where `x < y` needs `x+1 ≤ y` declared rather
    ///   than `x ≤ y`, pinned by the strictness golden.
    /// - witness: `entailment_oracle::entailment_oracle::prop_lt_equals_succ_leq_under_the_fixed_poset`
    /// - witness: `entail::tests::strictness_needs_a_strict_hypothesis`
    /// - witness: `entail::tests::entailment_is_irreflexive_for_lt_on_admitted_posets`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|evidence| {
        (left != right || !bool::from(evidence.holds()))
            && left.succ().map_or(true, |successor| {
                self.entails_leq_with_evidence(&successor, right)
                    .is_ok_and(|shifted| shifted.holds() == evidence.holds())
            })
    }))]
    #[inline]
    pub fn entails_lt_with_evidence(
        &self,
        left: &Level,
        right: &Level,
    ) -> Result<Entailment, PosetError>
    {
        decide(self, left, right, Strictness::STRICT)
    }

    /// The boolean face of [`Self::entails_leq_with_evidence`].
    ///
    /// # Specification
    /// - requires: nothing beyond canonical inputs.
    /// - ensures: holds exactly when the evidence face returns
    ///   [`Entailment::Holds`].
    /// - provides: the verdict without its evidence, for callers that only
    ///   branch on it.
    /// - fails: as [`Self::entails_leq_with_evidence`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::entails_leq_with_evidence`].
    #[spec(ensures: |ret| ret == self.entails_leq_with_evidence(left, right)
        .map(|evidence| evidence.holds()))]
    #[inline]
    pub fn entails_leq(
        &self,
        left: &Level,
        right: &Level,
    ) -> Result<EntailmentHolds, PosetError>
    {
        let evidence = self.entails_leq_with_evidence(left, right)?;
        Ok(evidence.holds())
    }

    /// The boolean face of [`Self::entails_lt_with_evidence`].
    ///
    /// # Specification
    /// - requires: nothing beyond canonical inputs.
    /// - ensures: holds exactly when the evidence face returns
    ///   [`Entailment::Holds`].
    /// - provides: the verdict without its evidence, for callers that only
    ///   branch on it.
    /// - fails: as [`Self::entails_lt_with_evidence`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::entails_lt_with_evidence`].
    #[spec(ensures: |ret| ret == self.entails_lt_with_evidence(left, right)
        .map(|evidence| evidence.holds()))]
    #[inline]
    pub fn entails_lt(
        &self,
        left: &Level,
        right: &Level,
    ) -> Result<EntailmentHolds, PosetError>
    {
        let evidence = self.entails_lt_with_evidence(left, right)?;
        Ok(evidence.holds())
    }
}

/// Checks an entailment witness against its claim by replaying its derivation
/// over the recomputed query encoding.
///
/// # Specification
/// - requires: `witness` claims `left ≤ right` under `poset`, or `left < right`
///   when its strict flag holds; the claim direction is read from the witness.
///   The encoding is definitional and shared with the oracle, so the replay is
///   the trusted step.
/// - ensures: `Ok(())` exactly when the derivation replays from the query seeds
///   — every step a known clause at an admissible shift with its body available
///   — to cover every goal atom of the claim.
/// - provides: the trusted half of the positive entailment evidence.
/// - fails: the first [`PosetEvidenceError`] encountered — replay errors in
///   step order, then uncovered goals in encoding order.
/// - panics: none.
///
/// # Errors
/// The replay errors and [`PosetEvidenceError::TargetUncovered`], plus
/// [`PosetEvidenceError::Overflow`] on adversarial arithmetic.
///
/// # Adequacy
/// - hypothesis: L3 — each rejection arm pinned by a hand-perturbed witness
///   asserting the exact variant, acceptance pinned by the property that every
///   oracle witness validates.
/// - witness: `entail::tests::perturbed_witness_arms_are_rejected`
/// - witness: `entailment_oracle::entailment_oracle::prop_fixed_poset_evidence_validates`
#[spec(ensures: |ret| ret.is_ok() == encode_query(poset, left, right, witness.strict())
    .is_ok_and(|encoding| {
        replay_derivation(&encoding.clauses, HornShift::ONE, encoding.seed, witness.derivation())
            .is_ok_and(|maxima| encoding.goals.iter().all(|goal| {
                maxima.get(&goal.variable()).is_some_and(|maximum| goal.offset() <= *maximum)
            }))
    })
)]
#[inline]
pub fn validate_entailment_witness(
    poset: &LandmarkPoset,
    left: &Level,
    right: &Level,
    witness: &EntailmentWitness,
) -> Result<(), PosetEvidenceError>
{
    let encoding = encode_query(poset, left, right, witness.strict())
        .map_err(|_error| PosetEvidenceError::Overflow)?;
    let maxima = replay_derivation(
        &encoding.clauses,
        HornShift::ONE,
        encoding.seed,
        witness.derivation(),
    )?;
    for &goal in &encoding.goals {
        let covered = maxima
            .get(&goal.variable())
            .is_some_and(|&maximum| goal.offset() <= maximum);
        if !covered {
            return Err(PosetEvidenceError::TargetUncovered {
                subject: EvidenceSubject::from_horn(goal.variable()),
            });
        }
    }
    Ok(())
}

/// Checks an entailment countermodel against its claim.
///
/// The model must satisfy the whole recomputed query system, cover the query
/// seeds, and refute its recorded goal, which soundly witnesses
/// non-derivability.
///
/// # Specification
/// - requires: `countermodel` claims `left ≤ right` fails under `poset`, or
///   fails strictly when its strict flag holds; the claim direction is read
///   from the countermodel.
/// - ensures: `Ok(())` exactly when the model assigns every in-scope variable,
///   covers every seed atom, satisfies every clause family of the query system,
///   and its recorded refuted goal is a goal of the claim that the model does
///   not cover.
/// - provides: the trusted half of the negative entailment evidence,
///   independent of the minimal-model computation since it only checks
///   satisfaction.
/// - fails: the first [`PosetEvidenceError`] encountered — missing values, then
///   seeds, then clauses in index order, then the refuted goal.
/// - panics: none.
///
/// # Errors
/// [`PosetEvidenceError::MissingValue`],
/// [`PosetEvidenceError::SeedUnsatisfied`],
/// [`PosetEvidenceError::ClauseUnsatisfied`],
/// [`PosetEvidenceError::NotRefuting`], and
/// [`PosetEvidenceError::Overflow`].
///
/// # Adequacy
/// - hypothesis: L3 — each rejection arm pinned by a hand-perturbed
///   countermodel asserting the exact variant, acceptance pinned by the
///   property that every oracle countermodel validates.
/// - witness: `entail::tests::perturbed_countermodel_arms_are_rejected`
/// - witness: `entailment_oracle::entailment_oracle::prop_fixed_poset_evidence_validates`
#[spec(ensures: |ret| ret.is_ok() == encode_query(poset, left, right, countermodel.strict())
    .is_ok_and(|encoding| {
        let model: Option<BTreeMap<_, _>> = encoding.seed.keys().map(|variable| {
            match *variable {
                HVar::Bottom => Some((*variable, countermodel.bottom_value())),
                HVar::Var(variable) => countermodel.value_of(variable)
                    .map(|value| (HVar::Var(variable), value)),
            }
        }).collect();
        model.is_some_and(|model| {
            encoding.seed.iter().all(|(variable, offset)| {
                model.get(variable).is_some_and(|value| bool::from(value.covers(*offset)))
            })
                && encoding.clauses.iter().all(|clause| {
                    horn::fire(clause, &model, HornShift::ONE).is_ok_and(|firing| {
                        firing.is_none_or(|firing| match (model.get(&clause.head().variable()), firing.value) {
                            (Some(&ModelValue::Infinite), _) => true,
                            (Some(&ModelValue::Finite(existing)), ModelValue::Finite(forced)) => forced <= existing,
                            _ => false,
                        })
                    })
                })
                && encoding.goals.contains(&HornAtom::new(
                    countermodel.refuted_subject().to_horn(), countermodel.refuted_offset()
                ))
                && model.get(&countermodel.refuted_subject().to_horn())
                    .is_some_and(|value| !bool::from(value.covers(countermodel.refuted_offset())))
        })
    })
)]
#[inline]
pub fn validate_entailment_countermodel(
    poset: &LandmarkPoset,
    left: &Level,
    right: &Level,
    countermodel: &EntailmentCountermodel,
) -> Result<(), PosetEvidenceError>
{
    let encoding = encode_query(poset, left, right, countermodel.strict())
        .map_err(|_error| PosetEvidenceError::Overflow)?;
    let mut model: BTreeMap<HVar, ModelValue> = BTreeMap::new();
    let _bottom_slot = model.insert(HVar::Bottom, countermodel.bottom_value());
    for &variable in encoding.seed.keys() {
        let HVar::Var(level_var) = variable
        else {
            continue;
        };
        let value = countermodel
            .value_of(level_var)
            .ok_or(PosetEvidenceError::MissingValue {
                variable: level_var,
            })?;
        let _variable_slot = model.insert(variable, value);
    }
    for (&variable, &seeded) in &encoding.seed {
        let covered = model
            .get(&variable)
            .is_some_and(|value| bool::from(value.covers(seeded)));
        if !covered {
            return Err(PosetEvidenceError::SeedUnsatisfied {
                subject: EvidenceSubject::from_horn(variable),
            });
        }
    }
    for (index, clause) in encoding.clauses.iter().enumerate() {
        let maybe_firing = horn::fire(clause, &model, HornShift::ONE)
            .map_err(|_error| PosetEvidenceError::Overflow)?;
        let Some(firing) = maybe_firing
        else {
            continue;
        };
        let head_var = clause.head().variable();
        let satisfied = match (model.get(&head_var), firing.value) {
            | (Some(&ModelValue::Infinite), _) => true,
            | (Some(&ModelValue::Finite(existing)), ModelValue::Finite(forced)) => {
                forced <= existing
            },
            | (Some(&ModelValue::Finite(_)), ModelValue::Infinite) | (None, _) => false,
        };
        if !satisfied {
            return Err(PosetEvidenceError::ClauseUnsatisfied {
                clause: ClauseIndex::from(index),
            });
        }
    }
    let goal = HornAtom::new(
        countermodel.refuted_subject().to_horn(),
        countermodel.refuted_offset(),
    );
    if !encoding.goals.contains(&goal) {
        return Err(PosetEvidenceError::NotRefuting);
    }
    let refuted = !model
        .get(&goal.variable())
        .is_some_and(|value| bool::from(value.covers(goal.offset())));
    if refuted {
        Ok(())
    }
    else {
        Err(PosetEvidenceError::NotRefuting)
    }
}

/// Builds the query encoding for `left ≤ right`, strict when `strict`.
///
/// # Specification
/// - requires: nothing beyond canonical inputs; the query scope is the poset's
///   declared variables together with those either side mentions.
/// - ensures: the clauses, seeds, and goals the module docs describe, in the
///   documented order, so the oracle and both validators compute the same
///   system from the same claim.
/// - provides: the definitional encoding shared across the oracle/validator
///   boundary.
/// - fails: [`PosetError::Overflow`] when a seed or goal offset leaves the
///   `u128` range.
/// - panics: none.
///
/// # Errors
/// [`PosetError::Overflow`] — a seed or goal offset passed the `u128` range.
///
/// # Adequacy
/// - hypothesis: L2 — the encoding is exercised by every property in the
///   entailment differential, whose empty-poset arm pins it against the free
///   order oracle exactly; the L3 residue is the constant-carrying bottom
///   encoding, pinned by the constant boundary triple.
/// - witness: `entail::tests::constants_cross_the_bottom_encoding`
/// - witness: `entailment_oracle::entailment_oracle::prop_empty_poset_agrees_with_the_free_oracle`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|encoding| {
    let scope = encoding.seed.keys().filter_map(|variable| match *variable {
        HVar::Var(variable) => Some(variable),
        HVar::Bottom => None,
    });
    let scope_matches = poset.variables().iter().copied()
        .chain(left.atoms().map(|(variable, _)| variable))
        .chain(right.atoms().map(|(variable, _)| variable))
        .all(|variable| encoding.seed.contains_key(&HVar::Var(variable)))
        && scope.clone().all(|variable| poset.variables().contains(&variable)
            || left.offset_of(variable).is_some() || right.offset_of(variable).is_some());
    let seeds_match = encoding.seed.get(&HVar::Bottom)
        == Some(&HornOffset::from(u128::from(right.constant_part()).saturating_add(1)))
        && scope.clone().all(|variable| {
            let offset = right.offset_of(variable).map_or(0, |offset| u128::from(offset).saturating_add(1));
            encoding.seed.get(&HVar::Var(variable)) == Some(&HornOffset::from(offset))
        });
    let clauses_match = encoding.clauses.iter().take(poset.compiled_clauses().len())
        .eq(poset.compiled_clauses().iter())
        && encoding.clauses.len() == poset.compiled_clauses().len().saturating_add(scope.clone().count())
        && encoding.clauses.iter().skip(poset.compiled_clauses().len()).zip(scope)
            .all(|(clause, variable)| {
                clause.head() == HornAtom::new(HVar::Bottom, HornOffset::ZERO)
                    && clause.body() == [HornAtom::new(HVar::Var(variable), HornOffset::ZERO)]
            });
    let shift = u128::from(strict.shift()).saturating_add(1);
    let goals_match = encoding.goals.iter().copied().eq(
        core::iter::once(HornAtom::new(HVar::Bottom,
            HornOffset::from(u128::from(left.constant_part()).saturating_add(shift))))
            .chain(left.atoms().map(|(variable, offset)| HornAtom::new(HVar::Var(variable),
                HornOffset::from(u128::from(offset).saturating_add(shift)))))
    );
    scope_matches && seeds_match && clauses_match && goals_match
}))]
pub fn encode_query(
    poset: &LandmarkPoset,
    left: &Level,
    right: &Level,
    strict: Strictness,
) -> Result<QueryEncoding, PosetError>
{
    let goal_shift = HornOffset::ONE
        .checked_add(HornOffset::from(u128::from(strict.shift())))
        .map_err(|_error| PosetError::Overflow)?;
    let mut scope: BTreeSet<LevelVar> = poset.variables().clone();
    scope.extend(left.atoms().map(|(variable, _offset)| variable));
    scope.extend(right.atoms().map(|(variable, _offset)| variable));
    let mut clauses = poset.compiled_clauses().to_vec();
    for &variable in &scope {
        if let Some(clause) = HornClause::new(
            &[HornAtom::new(HVar::Var(variable), HornOffset::ZERO)],
            HornAtom::new(HVar::Bottom, HornOffset::ZERO),
        ) {
            clauses.push(clause);
        }
    }
    let mut seed: BTreeMap<HVar, HornOffset> = scope
        .iter()
        .map(|&variable| (HVar::Var(variable), HornOffset::ZERO))
        .collect();
    for (variable, offset) in right.atoms() {
        let seeded = HornOffset::from(offset)
            .checked_add(HornOffset::ONE)
            .map_err(|_error| PosetError::Overflow)?;
        let _previous = seed.insert(HVar::Var(variable), seeded);
    }
    let bottom_seed = HornOffset::from(right.constant_part())
        .checked_add(HornOffset::ONE)
        .map_err(|_error| PosetError::Overflow)?;
    let _previous = seed.insert(HVar::Bottom, bottom_seed);
    let mut goals = Vec::new();
    let bottom_goal = HornOffset::from(left.constant_part())
        .checked_add(goal_shift)
        .map_err(|_error| PosetError::Overflow)?;
    goals.push(HornAtom::new(HVar::Bottom, bottom_goal));
    for (variable, offset) in left.atoms() {
        let goal = HornOffset::from(offset)
            .checked_add(goal_shift)
            .map_err(|_error| PosetError::Overflow)?;
        goals.push(HornAtom::new(HVar::Var(variable), goal));
    }
    Ok(QueryEncoding {
        clauses,
        seed,
        goals,
    })
}

/// The shortest log prefix whose replay covers every goal.
///
/// # Specification
/// - requires: `log` is a saturation firing log over the same encoding as
///   `seed` and `goals`, so each step carries the atom its instance concluded.
/// - ensures: `Some(length)` for the shortest prefix covering every goal, and
///   `Some(0)` when the seeds already do — the documented absence case is
///   `None`, reached only when even the full log leaves a goal uncovered, which
///   the caller surfaces as a typed error rather than trusting.
/// - provides: the truncation that turns a saturation log into a minimal
///   witness derivation. The log's saturation provenance stays prose: the
///   producing clause system is not an argument. Coverage and the shortest
///   prefix use only the stored concluded atoms, without replaying or copying
///   the seed.
/// - fails: never; because each step carries its concluded atom, the scan needs
///   neither a clause lookup nor arithmetic, so it has no failure mode beyond
///   the absence case.
/// - panics: none.
/// - intension: the scan is a single forward pass over the log, never
///   recursive, and stops at the first step that clears the outstanding goals.
///
/// # Adequacy
/// - hypothesis: L2 — the truncated derivation must replay through the
///   independent witness validator on every decided query of the entailment
///   differential, so a mutant truncating early or late fails validation; the
///   L3 residue is the already-covered boundary, where the seeds cover the
///   goals and the prefix must be empty, pinned by the reflexive constant
///   golden.
/// - witness: `entail::tests::constants_cross_the_bottom_encoding`
/// - witness: `entailment_oracle::entailment_oracle::prop_fixed_poset_evidence_validates`
#[spec(ensures: |ret| {
    let covers = |length| goals.iter().all(|goal| {
        seed.get(&goal.variable()).is_some_and(|maximum| goal.offset() <= *maximum)
            || log.iter().take(length).any(|step| {
                step.concluded().variable() == goal.variable()
                    && goal.offset() <= step.concluded().offset()
            })
    });
    ret.map_or_else(|| !covers(log.len()), |length| {
        let length = usize::from(length);
        length <= log.len() && covers(length)
            && (length == 0 || !covers(length.saturating_sub(1)))
    })
})]
fn witness_cutoff(
    seed: &BTreeMap<HVar, HornOffset>,
    goals: &[HornAtom],
    log: &[FiringLogStep],
) -> Option<WitnessPrefixLength>
{
    let mut maxima = seed.clone();
    let covered = |state: &BTreeMap<HVar, HornOffset>, goal: HornAtom| {
        state
            .get(&goal.variable())
            .is_some_and(|&maximum| goal.offset() <= maximum)
    };
    let mut remaining: Vec<HornAtom> = goals
        .iter()
        .copied()
        .filter(|&goal| !covered(&maxima, goal))
        .collect();
    if remaining.is_empty() {
        return Some(WitnessPrefixLength::from(0_usize));
    }
    for (position, step) in log.iter().enumerate() {
        let concluded = step.concluded();
        let offset = concluded.offset();
        let maximum = maxima.entry(concluded.variable()).or_insert(offset);
        *maximum = (*maximum).max(offset);
        remaining.retain(|&goal| !covered(&maxima, goal));
        if remaining.is_empty() {
            return position.checked_add(1_usize).map(WitnessPrefixLength::from);
        }
    }
    None
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::vec;
    use alloc::vec::Vec;

    use super::Entailment;
    use super::EntailmentCountermodel;
    use super::EntailmentWitness;
    use super::validate_entailment_countermodel;
    use super::validate_entailment_witness;
    use crate::horn::ClauseIndex;
    use crate::horn::FiringLogStep;
    use crate::horn::HVar;
    use crate::horn::HornAtom;
    use crate::horn::HornOffset;
    use crate::horn::HornShift;
    use crate::horn::ModelValue;
    use crate::level::Level;
    use crate::level::LevelConstant;
    use crate::level::LevelOffset;
    use crate::level::LevelVar;
    use crate::level::LevelVarIndex;
    use crate::order::Strictness;
    use crate::poset::AdmissionOutcome;
    use crate::poset::Derivation;
    use crate::poset::EvidenceSubject;
    use crate::poset::LandmarkConstraint;
    use crate::poset::LandmarkPoset;
    use crate::poset::PosetEvidenceError;

    #[test]
    fn constants_cross_the_bottom_encoding()
    {
        // The encoding-soundness pins: the constant-versus-atom bound that a
        // passively pinned bottom would lose, and the already-covered boundary
        // where the seeds discharge the goals with no derivation step.
        let poset = empty_poset();
        let _witness = holds(
            &poset,
            &Level::constant(LevelConstant::from(3_u64)),
            &var_plus(x(), LevelOffset::from(3_u64)),
        );
        let _countermodel = refuted(
            &poset,
            &Level::constant(LevelConstant::from(4_u64)),
            &var_plus(x(), LevelOffset::from(3_u64)),
        );
        let reflexive = holds(
            &poset,
            &Level::constant(LevelConstant::from(5_u64)),
            &Level::constant(LevelConstant::from(5_u64)),
        );
        assert!(
            reflexive.derivation().steps().is_empty(),
            "a claim the seeds already cover needs no derivation step"
        );
    }

    #[test]
    fn landmark_order_is_entailed()
    {
        let poset = leq_poset();
        let witness = holds(
            &poset,
            &var_plus(x(), LevelOffset::from(0_u64)),
            &var_plus(y(), LevelOffset::from(0_u64)),
        );
        assert!(
            !witness.derivation().steps().is_empty(),
            "x <= y under the hypothesis needs a genuine derivation step"
        );
        assert!(
            !bool::from(
                var_plus(x(), LevelOffset::from(0_u64))
                    .leq(&var_plus(y(), LevelOffset::from(0_u64)))
            ),
            "the free fragment cannot see the hypothesis"
        );
    }

    #[test]
    fn shifted_landmark_order_is_entailed()
    {
        let poset = leq_poset();
        let _witness = holds(
            &poset,
            &var_plus(x(), LevelOffset::from(3_u64)),
            &var_plus(y(), LevelOffset::from(3_u64)),
        );
        let countermodel = refuted(
            &poset,
            &var_plus(y(), LevelOffset::from(0_u64)),
            &var_plus(x(), LevelOffset::from(0_u64)),
        );
        assert_eq!(
            countermodel.refuted_subject(),
            EvidenceSubject::Variable(y()),
            "the reverse direction is refuted at its variable goal"
        );
    }

    #[test]
    fn strictness_needs_a_strict_hypothesis()
    {
        let weak = leq_poset();
        let strict_claim = weak
            .entails_lt_with_evidence(
                &var_plus(x(), LevelOffset::from(0_u64)),
                &var_plus(y(), LevelOffset::from(0_u64)),
            )
            .expect("the query decides");
        assert!(
            !bool::from(strict_claim.holds()),
            "x <= y does not entail x < y"
        );
        let strong = admitted(vec![
            LandmarkConstraint::leq(
                var_plus(x(), LevelOffset::from(1_u64)),
                var_plus(y(), LevelOffset::from(0_u64)),
            )
            .expect("variable-only sides are well formed"),
        ]);
        let strict_holds = strong
            .entails_lt_with_evidence(
                &var_plus(x(), LevelOffset::from(0_u64)),
                &var_plus(y(), LevelOffset::from(0_u64)),
            )
            .expect("the query decides");
        assert!(bool::from(strict_holds.holds()), "x+1 <= y entails x < y");
    }

    #[test]
    fn non_total_order_is_refused_with_a_countermodel()
    {
        // Levels are not totally ordered: `x ∨ y = x+1` does not entail
        // `y = x+1`, though `y ≤ x+1` does follow.
        let poset = admitted(vec![
            LandmarkConstraint::equal(
                var_plus(x(), LevelOffset::from(0_u64))
                    .max(&var_plus(y(), LevelOffset::from(0_u64))),
                var_plus(x(), LevelOffset::from(1_u64)),
            )
            .expect("variable-only sides are well formed"),
        ]);
        let _forward = holds(
            &poset,
            &var_plus(y(), LevelOffset::from(0_u64)),
            &var_plus(x(), LevelOffset::from(1_u64)),
        );
        let _countermodel = refuted(
            &poset,
            &var_plus(x(), LevelOffset::from(1_u64)),
            &var_plus(y(), LevelOffset::from(0_u64)),
        );
    }

    #[test]
    fn hypotheses_reach_constant_goals()
    {
        // Under x <= y, the value of the join at zero flows through the
        // hypothesis: 3 <= y+3 needs no landmark, but 1 <= y follows only if
        // something seeds y, which nothing does, so it is refuted; while
        // 0 <= y holds trivially.
        let poset = leq_poset();
        let _trivial = holds(
            &poset,
            &Level::zero(),
            &var_plus(y(), LevelOffset::from(0_u64)),
        );
        let _refused = refuted(
            &poset,
            &Level::constant(LevelConstant::from(1_u64)),
            &var_plus(x(), LevelOffset::from(0_u64)),
        );
    }

    #[test]
    fn perturbed_witness_arms_are_rejected()
    {
        let poset = leq_poset();
        let left = var_plus(x(), LevelOffset::from(0_u64));
        let right = var_plus(y(), LevelOffset::from(0_u64));
        let _genuine = holds(&poset, &left, &right);

        let unknown = forged_witness(ClauseIndex::from(99_usize), HornShift::ONE);
        assert_eq!(
            Err(PosetEvidenceError::UnknownClause {
                clause: ClauseIndex::from(99_usize),
            }),
            validate_entailment_witness(&poset, &left, &right, &unknown),
            "an out-of-range clause index is rejected"
        );

        let below_minimum = forged_witness(ClauseIndex::from(0_usize), HornShift::ZERO);
        assert_eq!(
            Err(PosetEvidenceError::ShiftBelowMinimum {
                clause: ClauseIndex::from(0_usize),
            }),
            validate_entailment_witness(&poset, &left, &right, &below_minimum),
            "a step below the query system's minimum shift is rejected"
        );

        let starved = forged_witness(ClauseIndex::from(0_usize), HornShift::from(9_u128));
        assert_eq!(
            Err(PosetEvidenceError::BodyUnavailable {
                clause: ClauseIndex::from(0_usize),
            }),
            validate_entailment_witness(&poset, &left, &right, &starved),
            "a step firing above its available body is rejected"
        );

        let empty = EntailmentWitness {
            strict: Strictness::NON_STRICT,
            derivation: Derivation::from_log(&[]),
        };
        assert_eq!(
            validate_entailment_witness(&poset, &left, &right, &empty),
            Err(PosetEvidenceError::TargetUncovered {
                subject: EvidenceSubject::Variable(x()),
            }),
            "an empty derivation leaves the variable goal uncovered"
        );
    }

    #[test]
    fn perturbed_countermodel_arms_are_rejected()
    {
        let poset = leq_poset();
        let left = var_plus(y(), LevelOffset::from(0_u64));
        let right = var_plus(x(), LevelOffset::from(0_u64));
        let genuine = refuted(&poset, &left, &right);

        let mut missing = genuine.clone();
        let _removed = missing.values.remove(&y());
        assert_eq!(
            validate_entailment_countermodel(&poset, &left, &right, &missing),
            Err(PosetEvidenceError::MissingValue { variable: y() }),
            "an unassigned in-scope variable is rejected"
        );

        let mut starving = genuine.clone();
        let _starved_slot = starving
            .values
            .insert(x(), ModelValue::Finite(HornOffset::from(0_u128)));
        assert_eq!(
            validate_entailment_countermodel(&poset, &left, &right, &starving),
            Err(PosetEvidenceError::SeedUnsatisfied {
                subject: EvidenceSubject::Variable(x()),
            }),
            "a model below the query seeds is rejected"
        );

        // `x <= y` compiles to the clause `{y} implies x`, the query system's
        // clause 0, so raising y's value while x stays low violates it.
        let mut violating = genuine.clone();
        let _violated_slot = violating
            .values
            .insert(y(), ModelValue::Finite(HornOffset::from(9_u128)));
        assert_eq!(
            Err(PosetEvidenceError::ClauseUnsatisfied {
                clause: ClauseIndex::from(0_usize),
            }),
            validate_entailment_countermodel(&poset, &left, &right, &violating),
            "a model violating a hypothesis clause is rejected"
        );

        let mut misdirected = genuine.clone();
        misdirected.refuted_subject = EvidenceSubject::Variable(x());
        assert_eq!(
            Err(PosetEvidenceError::NotRefuting),
            validate_entailment_countermodel(&poset, &left, &right, &misdirected),
            "a recorded goal outside the claim's goals is rejected"
        );

        let mut satisfied = genuine;
        let mut saturated_values: BTreeMap<LevelVar, ModelValue> = BTreeMap::new();
        let _first = saturated_values.insert(x(), ModelValue::Infinite);
        let _second = saturated_values.insert(y(), ModelValue::Infinite);
        satisfied.values = saturated_values;
        satisfied.bottom = ModelValue::Infinite;
        assert_eq!(
            Err(PosetEvidenceError::NotRefuting),
            validate_entailment_countermodel(&poset, &left, &right, &satisfied),
            "a model that covers the recorded goal refutes nothing"
        );

        // Overflow needs a clause with a positive head offset: under
        // `x+1 <= y` the clause `{y} implies x+1` fires at shift u128::MAX when
        // the model drives y that high, and 1 + u128::MAX overflows.
        let strong = admitted(vec![
            LandmarkConstraint::leq(
                var_plus(x(), LevelOffset::from(1_u64)),
                var_plus(y(), LevelOffset::from(0_u64)),
            )
            .expect("variable-only sides are well formed"),
        ]);
        let mut overflowing = refuted(
            &strong,
            &var_plus(y(), LevelOffset::from(0_u64)),
            &var_plus(x(), LevelOffset::from(0_u64)),
        );
        let _overflow_slot = overflowing
            .values
            .insert(y(), ModelValue::Finite(HornOffset::from(u128::MAX)));
        assert_eq!(
            Err(PosetEvidenceError::Overflow),
            validate_entailment_countermodel(
                &strong,
                &var_plus(y(), LevelOffset::from(0_u64)),
                &var_plus(x(), LevelOffset::from(0_u64)),
                &overflowing
            ),
            "adversarial magnitudes are rejected, never wrapped"
        );
    }

    #[test]
    fn queries_mentioning_undeclared_variables_work()
    {
        let poset = leq_poset();
        let _witness = holds(
            &poset,
            &var_plus(var7(), LevelOffset::from(0_u64)),
            &var_plus(var7(), LevelOffset::from(2_u64)),
        );
        let _countermodel = refuted(
            &poset,
            &var_plus(var7(), LevelOffset::from(0_u64)),
            &var_plus(var8(), LevelOffset::from(0_u64)),
        );
    }

    #[test]
    fn lt_equals_succ_leq_under_hypotheses()
    {
        let poset = leq_poset();
        let pairs = [
            (
                var_plus(x(), LevelOffset::from(0_u64)),
                var_plus(y(), LevelOffset::from(0_u64)),
            ),
            (
                var_plus(x(), LevelOffset::from(0_u64)),
                var_plus(y(), LevelOffset::from(2_u64)),
            ),
            (
                var_plus(x(), LevelOffset::from(2_u64)),
                var_plus(y(), LevelOffset::from(1_u64)),
            ),
            (
                Level::constant(LevelConstant::from(2_u64)),
                var_plus(y(), LevelOffset::from(3_u64)),
            ),
        ];
        for (left, right) in pairs {
            let via_lt = poset.entails_lt(&left, &right).expect("the query decides");
            let shifted = left.succ().expect("offsets in tests stay small");
            let via_succ = poset
                .entails_leq(&shifted, &right)
                .expect("the query decides");
            assert_eq!(
                via_lt, via_succ,
                "lt must equal leq after succ ({left:?}, {right:?})"
            );
        }
    }

    #[test]
    fn entailment_is_irreflexive_for_lt_on_admitted_posets()
    {
        let poset = leq_poset();
        let composite =
            var_plus(x(), LevelOffset::from(2_u64)).max(&var_plus(y(), LevelOffset::from(5_u64)));
        let verdict = poset
            .entails_lt(&composite, &composite)
            .expect("the query decides");
        assert!(
            !bool::from(verdict),
            "lt stays irreflexive under admitted hypotheses"
        );
    }

    /// A witness carrying one hand-written step, for the replay rejection arms.
    ///
    /// # Specification
    /// - requires: nothing; the step is deliberately unrelated to any real
    ///   derivation.
    /// - ensures: returns a non-strict witness whose derivation is the single
    ///   step naming `clause` at `shift`.
    /// - provides: the forged evidence each replay rejection arm is stated
    ///   against.
    /// - panics: none.
    fn forged_witness(
        clause: ClauseIndex,
        shift: HornShift,
    ) -> EntailmentWitness
    {
        let log = [FiringLogStep::new(
            clause,
            shift,
            HornAtom::new(HVar::Bottom, HornOffset::ZERO),
        )];
        EntailmentWitness {
            strict: Strictness::NON_STRICT,
            derivation: Derivation::from_log(&log),
        }
    }

    /// The empty poset, under which entailment degenerates to the free oracle.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the poset with no declared constraints.
    /// - provides: the fixture the agreement rows compare against the free
    ///   oracle.
    /// - panics: when admission overflows or loops, neither of which an empty
    ///   constraint set can do.
    fn empty_poset() -> LandmarkPoset
    {
        admitted(vec![])
    }

    /// A poset declaring `x ≤ y` over variables `0` and `1`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the poset declaring `x ≤ y` and nothing else.
    /// - provides: the one-hypothesis fixture the entailment rows are stated
    ///   against.
    /// - panics: when admission overflows or loops, neither of which this
    ///   single acyclic constraint can do.
    fn leq_poset() -> LandmarkPoset
    {
        admitted(vec![
            LandmarkConstraint::leq(
                var_plus(x(), LevelOffset::from(0_u64)),
                var_plus(y(), LevelOffset::from(0_u64)),
            )
            .expect("variable-only sides are well formed"),
        ])
    }

    /// Admits a constraint set that must admit.
    ///
    /// # Specification
    /// - requires: `constraints` admits, which is what the calling test is
    ///   asserting about.
    /// - ensures: returns the admitted poset.
    /// - provides: the admitted-arm fixture, with the dichotomy's other arm
    ///   turned into a test failure at the point it appears.
    /// - panics: when admission overflows or returns a loop.
    fn admitted(constraints: Vec<LandmarkConstraint>) -> LandmarkPoset
    {
        match LandmarkPoset::admit(constraints).expect("admission does not overflow") {
            | AdmissionOutcome::Admitted(poset) => poset,
            | AdmissionOutcome::Loop(_witness) => panic!("expected admission"),
        }
    }

    /// The first test variable.
    ///
    /// # Specification
    /// trivial.
    fn x() -> LevelVar
    {
        LevelVar::new(LevelVarIndex::from(0_u32))
    }

    /// The second test variable.
    ///
    /// # Specification
    /// trivial.
    fn y() -> LevelVar
    {
        LevelVar::new(LevelVarIndex::from(1_u32))
    }

    /// The variable at index 7.
    ///
    /// # Specification
    /// trivial.
    fn var7() -> LevelVar
    {
        LevelVar::new(LevelVarIndex::from(7_u32))
    }

    /// The variable at index 8.
    ///
    /// # Specification
    /// trivial.
    fn var8() -> LevelVar
    {
        LevelVar::new(LevelVarIndex::from(8_u32))
    }

    /// `var + n` built through the public constructors.
    ///
    /// # Specification
    /// - requires: `offset` is small enough that `variable + offset` stays
    ///   representable.
    /// - ensures: returns the canonical level `variable + offset`.
    /// - provides: the atom builder these tests state their fixtures with.
    /// - panics: when a successor step passes the representable range, which
    ///   the offsets these tests use never reach.
    fn var_plus(
        variable: LevelVar,
        offset: LevelOffset,
    ) -> Level
    {
        let mut level = Level::var(variable);
        for _step in 0_u64 .. u64::from(offset) {
            level = level.succ().expect("offsets in tests stay small");
        }
        level
    }

    /// Decides and unwraps the positive case, validating the witness.
    ///
    /// # Specification
    /// - requires: the query holds under `poset`, which is what the calling
    ///   test is asserting about.
    /// - ensures: returns the oracle's witness, having first checked it through
    ///   the validator.
    /// - provides: the positive-arm fixture, with the validator run folded in
    ///   so no test reads an unvalidated witness.
    /// - panics: when the query fails to decide, when it is refuted, or when
    ///   the witness fails validation.
    fn holds(
        poset: &LandmarkPoset,
        left: &Level,
        right: &Level,
    ) -> EntailmentWitness
    {
        match poset
            .entails_leq_with_evidence(left, right)
            .expect("the query decides")
        {
            | Entailment::Holds(witness) => {
                assert_eq!(
                    Ok(()),
                    validate_entailment_witness(poset, left, right, &witness),
                    "the witness must validate"
                );
                witness
            },
            | Entailment::Refuted(_countermodel) => panic!("expected entailment"),
        }
    }

    /// Decides and unwraps the negative case, validating the countermodel.
    ///
    /// # Specification
    /// - requires: the query is refuted under `poset`, which is what the
    ///   calling test is asserting about.
    /// - ensures: returns the oracle's countermodel, having first checked it
    ///   through the validator.
    /// - provides: the negative-arm fixture, with the validator run folded in
    ///   so no test reads an unvalidated countermodel.
    /// - panics: when the query fails to decide, when it holds, or when the
    ///   countermodel fails validation.
    fn refuted(
        poset: &LandmarkPoset,
        left: &Level,
        right: &Level,
    ) -> EntailmentCountermodel
    {
        match poset
            .entails_leq_with_evidence(left, right)
            .expect("the query decides")
        {
            | Entailment::Refuted(countermodel) => {
                assert_eq!(
                    Ok(()),
                    validate_entailment_countermodel(poset, left, right, &countermodel),
                    "the countermodel must validate"
                );
                countermodel
            },
            | Entailment::Holds(_witness) => panic!("expected refusal"),
        }
    }
}
