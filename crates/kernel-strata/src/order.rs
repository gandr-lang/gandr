//! The order oracle over canonical levels — [`Level::leq_with_evidence`] and
//! [`Level::lt_with_evidence`] — together with the evidence vocabulary and the
//! validators that check evidence against its levels.
//!
//! The decision is **domination** on canonical forms: `l ≤ m` at every
//! valuation exactly when each atom `x + a` of `l` has a same-variable atom
//! `x + b` in `m` with `a ≤ b` (a spike valuation on `x` refutes anything
//! less), and `l`'s constant part is at most `m`'s value at the zero valuation
//! (which is where a constant violation shows). Strict order is the same
//! comparison with the left side shifted up by one: `l < m` iff `l + 1 ≤ m`
//! over the naturals.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::error::Error;
use core::fmt;
use core::ops::Not;

use anodized::spec;

use crate::level::Level;
use crate::level::LevelOffset;
use crate::level::LevelValue;
use crate::level::LevelVar;

/// Whether an order query is strict (`left < right`) or non-strict
/// (`left ≤ right`).
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Strictness(bool);

impl Strictness
{
    /// Non-strict comparison mode.
    pub const NON_STRICT: Self = Self(false);

    /// Strict comparison mode.
    pub const STRICT: Self = Self(true);

    /// The one-or-zero shift the mode applies to the left side.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns `1` for the strict mode and `0` for the non-strict
    ///   one, which is what makes `l < m` the comparison `l + 1 ≤ m`.
    /// - provides: the one place the two comparison modes differ.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — strict and non-strict comparisons on equal atoms and
    ///   adjacent successors distinguish a missing or reversed unit shift by
    ///   exact comparison verdicts.
    /// - witness: `order::tests::leq_is_reflexive_and_lt_is_irreflexive_on_atoms`
    /// - witness: `order::tests::var_is_strictly_below_its_successor`
    #[spec(ensures: |ret| ret.0 == if self.0 { 1_u128 } else { 0_u128 })]
    #[inline]
    #[must_use]
    pub(crate) const fn shift(self) -> OrderShift
    {
        OrderShift(if self.0 { 1_u128 } else { 0_u128 })
    }
}

/// The upward shift a comparison mode applies to the left side: one for the
/// strict order, zero for the non-strict one.
///
/// It is wide so that shifting the left side of a comparison at the numeric
/// ceiling of the level representation cannot overflow.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct OrderShift(u128);

impl From<OrderShift> for u128
{
    /// Unwraps the shift to the width the comparison arithmetic runs at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(shift: OrderShift) -> Self
    {
        shift.0
    }
}

impl From<bool> for Strictness
{
    /// Wraps a strictness decision as the comparison mode.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(strict: bool) -> Self
    {
        Self(strict)
    }
}

impl From<Strictness> for bool
{
    /// Unwraps the comparison mode to a plain decision.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(strict: Strictness) -> Self
    {
        strict.0
    }
}

/// The truth value returned by the boolean face of the free order oracle.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OrderComparison(bool);

impl From<bool> for OrderComparison
{
    /// Wraps an order answer as the oracle's comparison result.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(holds: bool) -> Self
    {
        Self(holds)
    }
}

impl From<OrderComparison> for bool
{
    /// Unwraps the oracle's comparison result to a plain answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(holds: OrderComparison) -> Self
    {
        holds.0
    }
}

impl Not for OrderComparison
{
    type Output = Self;

    /// The opposite comparison answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn not(self) -> Self::Output
    {
        Self::from(!bool::from(self))
    }
}

/// What bounds the left level's constant part within the right level.
///
/// # Specification
/// - ensures: the selected constant or atom component dominates the external
///   left constant.
/// - executable: none — the operand levels are not fields of this evidence tag.
///
/// # Adequacy
/// - hypothesis: L3 — genuine and forged bounds over canonical levels are
///   checked by the independent validator. Equality and one-past-offset
///   constants, an absent named atom and two equally dominating atoms expose
///   wrong source selection and acceptance of non-dominating components.
/// - witness: `order::tests::constant_dominated_by_atom_offset`
/// - witness: `order::tests::constant_past_atom_offset_is_refuted_at_zero`
/// - witness: `order::tests::constant_bound_names_the_least_dominating_variable`
/// - witness: `order::tests::perturbed_witness_absent_constant_atom_is_rejected`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstantBound
{
    /// The right level's own constant part dominates it.
    Constant,
    /// The right level's atom over this variable dominates it: that atom's
    /// offset is a pointwise lower bound of the atom, hence of the right level.
    Atom(LevelVar),
}

/// One step of a domination witness.
///
/// The left atom over `variable` is dominated by the right level's
/// same-variable atom. Offsets are recorded so a reviewer or validator can
/// check the claim against the levels directly.
///
/// # Specification
/// - ensures: oracle-produced bounds name equal variables, record their exact
///   offsets and establish domination.
/// - executable: none — the compared levels and strictness are external to the
///   bound.
///
/// # Adequacy
/// - hypothesis: L3 — a genuine bound for unequal offsets is inspected; a
///   forged offset and an accurate but insufficient bound must produce distinct
///   typed refusals, exposing altered offsets and a weakened domination guard.
/// - witness: `order::tests::witness_records_accurate_offsets`
/// - witness: `order::tests::perturbed_witness_offset_mismatch_is_rejected`
/// - witness: `order::tests::false_witness_insufficient_bound_is_rejected`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AtomBound
{
    /// The variable both atoms range over.
    variable: LevelVar,
    /// The left atom's offset, as recorded from the left level.
    left_offset: LevelOffset,
    /// The dominating right atom's offset, as recorded from the right level.
    right_offset: LevelOffset,
}

impl AtomBound
{
    /// The variable both atoms range over.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn variable(&self) -> LevelVar
    {
        self.variable
    }

    /// The left atom's recorded offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn left_offset(&self) -> LevelOffset
    {
        self.left_offset
    }

    /// The dominating right atom's recorded offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn right_offset(&self) -> LevelOffset
    {
        self.right_offset
    }
}

/// A checkable **domination witness** for `left ≤ right`, or for
/// `left < right` when [`Self::strict`] holds.
///
/// It carries one [`AtomBound`] per left atom in ascending variable order, plus
/// the [`ConstantBound`] for the left constant part.
///
/// Witnesses are constructed only by the oracle, since the fields are private;
/// they are inspected through the accessors and checked by
/// [`validate_witness`].
///
/// # Specification
/// - ensures: oracle-produced witnesses account for every left atom and the
///   constant, with no unrelated bounds.
/// - executable: none — validity relates this value to two external levels.
///
/// # Adequacy
/// - hypothesis: L2 — generated comparisons validate their evidence. L3 mutates
///   genuine or forged bounds at the missing, stray and insufficient bound
///   boundaries; the exact validator refusal distinguishes incomplete or
///   unsound certificates from valid ones.
/// - witness: `level_oracle::level_oracle::prop_evidence_validates`
/// - witness: `order::tests::perturbed_witness_missing_bound_is_rejected`
/// - witness: `order::tests::perturbed_witness_stray_bound_is_rejected`
/// - witness: `order::tests::false_witness_insufficient_constant_is_rejected`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeqWitness
{
    /// Whether this witnesses the strict order (`left + 1 ≤ right`).
    strict: Strictness,
    /// Per-atom domination bounds, in ascending variable order.
    atoms: Vec<AtomBound>,
    /// The bound on the left constant part.
    constant: ConstantBound,
}

impl LeqWitness
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

    /// The per-atom domination bounds, in ascending variable order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn atom_bounds(&self) -> &[AtomBound]
    {
        &self.atoms
    }

    /// The bound on the left constant part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant_bound(&self) -> ConstantBound
    {
        self.constant
    }
}

/// A checkable **refutation** of `left ≤ right`, or of `left < right` when
/// [`Self::strict`] holds: a concrete counter-valuation under which the claimed
/// order fails. Absent variables read as `0`.
///
/// Refutations are constructed only by the oracle, since the fields are
/// private; they are inspected through the accessors and checked by
/// [`validate_refutation`].
///
/// # Specification
/// - ensures: oracle-produced valuations refute the external comparison in the
///   recorded mode.
/// - executable: none — the compared levels are not stored in the
///   counter-valuation.
///
/// # Adequacy
/// - hypothesis: L2 — generated comparisons independently validate both
///   evidence branches. L3 checks incomparable variables, non-refuting equality
///   and arithmetic overflow, distinguishing a false counterexample from a
///   valid one by exact validator outcomes.
/// - witness: `level_oracle::level_oracle::prop_evidence_validates`
/// - witness: `order::tests::distinct_variables_are_incomparable`
/// - witness: `order::tests::non_refuting_valuation_is_rejected`
/// - witness: `order::tests::overflowing_valuation_is_rejected`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeqRefutation
{
    /// Whether this refutes the strict order (`left < right`).
    strict: Strictness,
    /// The counter-valuation; absent variables read as `0`.
    valuation: BTreeMap<LevelVar, LevelValue>,
}

impl LeqRefutation
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

    /// The counter-valuation; absent variables read as `0`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn valuation(&self) -> &BTreeMap<LevelVar, LevelValue>
    {
        &self.valuation
    }
}

/// Rejection vocabulary of the evidence validators: exactly why a piece of
/// evidence fails to check against its levels.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvidenceError
{
    /// A left atom has no bound in the witness.
    MissingAtomBound
    {
        /// The uncovered left variable.
        variable: LevelVar,
    },
    /// The witness carries a bound for an atom the left level lacks, or a
    /// duplicate or out-of-order bound.
    StrayAtomBound
    {
        /// The offending bound's variable.
        variable: LevelVar,
    },
    /// A bound's recorded offsets differ from the levels' actual offsets.
    AtomOffsetMismatch
    {
        /// The variable whose recorded offsets are wrong.
        variable: LevelVar,
    },
    /// A bound's offsets are accurate but do not dominate: the recorded left
    /// offset, plus one when strict, exceeds the right offset.
    InsufficientAtomBound
    {
        /// The variable whose bound fails.
        variable: LevelVar,
    },
    /// The constant bound names a right atom that does not exist.
    MissingConstantBound
    {
        /// The named absent variable.
        variable: LevelVar,
    },
    /// The constant bound exists but does not dominate the left constant part.
    InsufficientConstantBound,
    /// The refutation's valuation does not order the two levels the wrong way.
    NotRefuting,
    /// Evaluating under the adversarial valuation overflowed; the evidence is
    /// rejected rather than wrapped.
    Overflow,
}

impl fmt::Display for EvidenceError
{
    /// Renders the rejection as one sentence naming the offending part of the
    /// evidence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::MissingAtomBound { variable } => write!(
                f,
                "no bound covers the left atom over variable {}",
                variable.index()
            ),
            | Self::StrayAtomBound { variable } => write!(
                f,
                "a bound names variable {} outside the left level's atoms",
                variable.index()
            ),
            | Self::AtomOffsetMismatch { variable } => write!(
                f,
                "recorded offsets for variable {} differ from the levels",
                variable.index()
            ),
            | Self::InsufficientAtomBound { variable } => write!(
                f,
                "the bound for variable {} does not dominate",
                variable.index()
            ),
            | Self::MissingConstantBound { variable } => write!(
                f,
                "the constant bound names absent variable {}",
                variable.index()
            ),
            | Self::InsufficientConstantBound => {
                f.write_str("the constant bound does not dominate")
            },
            | Self::NotRefuting => f.write_str("the valuation does not refute the claimed order"),
            | Self::Overflow => f.write_str("evaluating the valuation overflowed"),
        }
    }
}

impl Error for EvidenceError
{
}

impl Level
{
    /// Decides `self ≤ other` over all valuations, returning checkable evidence
    /// either way.
    ///
    /// # Specification
    /// - requires: nothing beyond canonical inputs, guaranteed by construction.
    /// - ensures: `Ok(witness)` exactly when `self ≤ other` at every valuation
    ///   of the variables, with the witness passing [`validate_witness`];
    ///   `Err(refutation)` otherwise, with a concrete counter-valuation passing
    ///   [`validate_refutation`].
    /// - provides: the kernel's level-order oracle over the free fragment.
    /// - fails: never — the refutation branch is a negative answer, not a
    ///   failure.
    /// - panics: none.
    /// - intension: when several right atoms dominate the left constant part,
    ///   the witness names the least such variable; refutations use the zero
    ///   valuation for constant violations and a single-variable spike, one
    ///   past the right level's largest component, for atom violations. Both
    ///   choices are deterministic and observable through the evidence
    ///   accessors.
    ///
    /// # Errors
    /// The `Err` branch is the checkable refutation, not an operational
    /// failure.
    ///
    /// # Adequacy
    /// - hypothesis: L2 against the independent semantic reference — direct
    ///   term evaluation over the provably complete zero-plus-spikes valuation
    ///   family — on generated term pairs, plus L1, since returned evidence
    ///   must validate against the inputs, so a mutant deciding wrongly must
    ///   also forge coherent evidence; the L3 residue is the boundary set `x ≤
    ///   x+1` against `x+1 ≰ x`, constant-versus-atom domination, and
    ///   distinct-variable incomparability.
    /// - witness: `level_oracle::level_oracle::prop_leq_agrees_with_semantic_reference`
    /// - witness: `level_oracle::level_oracle::prop_evidence_validates`
    /// - witness: `order::tests::var_is_strictly_below_its_successor`
    /// - witness: `order::tests::distinct_variables_are_incomparable`
    /// - witness: `order::tests::constant_dominated_by_atom_offset`
    #[spec(ensures: |ret| match ret.as_ref() {
        Ok(witness) => witness.strict() == Strictness::NON_STRICT
            && validate_witness(self, other, witness).is_ok(),
        Err(refutation) => refutation.strict() == Strictness::NON_STRICT
            && validate_refutation(self, other, refutation).is_ok(),
    })]
    #[inline]
    pub fn leq_with_evidence(
        &self,
        other: &Self,
    ) -> Result<LeqWitness, LeqRefutation>
    {
        compare(self, other, Strictness::NON_STRICT)
    }

    /// Decides the strict order `self < other`, that is `self + 1 ≤ other` over
    /// the naturals, returning checkable evidence either way.
    ///
    /// # Specification
    /// - requires: nothing beyond canonical inputs, guaranteed by construction.
    /// - ensures: `Ok(witness)` exactly when `self < other` at every valuation;
    ///   agrees with `self.succ()?.leq_with_evidence(other)` whenever the
    ///   successor is representable, and stays total where it is not, since the
    ///   shift happens in wide arithmetic.
    /// - provides: the consistency-bearing comparison of the universe rule
    ///   (`U_l : U_m` iff `l < m`), whose invariant is irreflexivity.
    /// - fails: never — the refutation branch is a negative answer.
    /// - panics: none.
    ///
    /// # Errors
    /// The `Err` branch is the checkable refutation, not an operational
    /// failure.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — semantic agreement plus the `lt` equals `leq` after
    ///   `succ` internal consistency law on generated pairs; the L3 residue is
    ///   irreflexivity on composite levels, the soundness boundary, together
    ///   with the `x < x+1` and `x ≮ x` pair.
    /// - witness: `level_oracle::level_oracle::prop_lt_agrees_with_semantic_reference`
    /// - witness: `level_oracle::level_oracle::prop_lt_equals_succ_leq`
    /// - witness: `order::tests::lt_is_irreflexive`
    #[spec(ensures: |ret| ret.is_ok() == (
        self.atoms().all(|(variable, offset)| other.offset_of(variable).is_some_and(|bound| {
            u128::from(offset).checked_add(1).is_some_and(|shifted| shifted <= u128::from(bound))
        }))
            && u128::from(self.constant_part()).checked_add(1).is_some_and(|shifted|
                shifted <= other.atoms().map(|(_, offset)| u128::from(offset))
                    .fold(u128::from(other.constant_part()), u128::max))
    ) && self.succ().map_or(true, |successor| {
        ret.is_ok() == successor.leq_with_evidence(other).is_ok()
    }))]
    #[inline]
    pub fn lt_with_evidence(
        &self,
        other: &Self,
    ) -> Result<LeqWitness, LeqRefutation>
    {
        compare(self, other, Strictness::STRICT)
    }

    /// The boolean face of [`Self::leq_with_evidence`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: holds exactly when [`Self::leq_with_evidence`] returns `Ok`.
    /// - provides: the verdict without its evidence, for callers that only
    ///   branch on it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated canonical levels are compared with
    ///   independent zero-and-spike valuation decisions; equality, zero,
    ///   incomparable variables and one-offset separation distinguish reversed
    ///   or constant verdicts.
    /// - witness: `level_oracle::level_oracle::prop_leq_agrees_with_semantic_reference`
    /// - witness: `order::tests::zero_is_leq_everything`
    /// - witness: `order::tests::distinct_variables_are_incomparable`
    #[spec(ensures: |ret| bool::from(ret) == self.leq_with_evidence(other).is_ok())]
    #[inline]
    #[must_use]
    pub fn leq(
        &self,
        other: &Self,
    ) -> OrderComparison
    {
        OrderComparison::from(self.leq_with_evidence(other).is_ok())
    }

    /// The boolean face of [`Self::lt_with_evidence`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: holds exactly when [`Self::lt_with_evidence`] returns `Ok`.
    /// - provides: the verdict without its evidence, for callers that only
    ///   branch on it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated canonical levels are compared with
    ///   independent strict valuation decisions. L3 separates equality from a
    ///   one-offset gap to expose an inclusive or missing strictness shift.
    /// - witness: `level_oracle::level_oracle::prop_lt_agrees_with_semantic_reference`
    /// - witness: `order::tests::leq_is_reflexive_and_lt_is_irreflexive_on_atoms`
    /// - witness: `order::tests::var_is_strictly_below_its_successor`
    #[spec(ensures: |ret| bool::from(ret) == self.lt_with_evidence(other).is_ok())]
    #[inline]
    #[must_use]
    pub fn lt(
        &self,
        other: &Self,
    ) -> OrderComparison
    {
        OrderComparison::from(self.lt_with_evidence(other).is_ok())
    }
}

/// The shared comparison: decides `left + shift ≤ right` pointwise, where
/// `shift` is one exactly when `strict`.
///
/// # Specification
/// - requires: canonical inputs, guaranteed by construction.
/// - ensures: `Ok` exactly when domination holds — each left atom bounded by a
///   same-variable right atom under the shift, and the shifted left constant
///   bounded by the right level's value at the zero valuation.
/// - provides: the single decision path both public comparisons share.
/// - fails: never; the `Err` branch carries the counter-valuation.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the pointwise domination test is the decision surface,
///   and it is carried by the public faces' witnesses, since this is their
///   whole body. Checked shifts and spikes cannot overflow: level components
///   are at most `u64::MAX` and the shift is at most one, widened to `u128`.
///   Their refusal branches therefore exclude no representable input. Widening
///   the components requires a distinct overflow carrier: a zero valuation
///   would not refute every unrepresentable-spike case.
/// - witness: `order::tests::comparison_is_total_at_the_offset_ceiling`
/// - witness: `order::tests::strict_comparison_at_the_constant_ceiling_refutes_at_the_zero_valuation`
/// - witness: `order::tests::an_atom_refutation_spikes_above_the_constant_ceiling`
#[spec(ensures: |ret| ret.is_ok() == (
    left.atoms().all(|(variable, offset)| right.offset_of(variable).is_some_and(|bound| {
        u128::from(offset).checked_add(u128::from(strict.shift())).is_some_and(|shifted| shifted <= u128::from(bound))
    }))
        && u128::from(left.constant_part()).checked_add(u128::from(strict.shift())).is_some_and(|shifted|
            shifted <= right.atoms().map(|(_, offset)| u128::from(offset))
                .fold(u128::from(right.constant_part()), u128::max))
))]
fn compare(
    left: &Level,
    right: &Level,
    strict: Strictness,
) -> Result<LeqWitness, LeqRefutation>
{
    let shift = u128::from(strict.shift());
    let mut atoms = Vec::with_capacity(left.atoms_map().len());
    for (&variable, &left_offset) in left.atoms_map() {
        let Some(shifted_left) = u128::from(left_offset).checked_add(shift)
        else {
            return Err(LeqRefutation {
                strict,
                valuation: BTreeMap::new(),
            });
        };
        let dominating = right
            .atoms_map()
            .get(&variable)
            .copied()
            .filter(|&bound| shifted_left <= u128::from(bound));
        let Some(right_offset) = dominating
        else {
            let Some(spike) = spike_value(right)
            else {
                return Err(LeqRefutation {
                    strict,
                    valuation: BTreeMap::new(),
                });
            };
            let mut valuation = BTreeMap::new();
            let _previous = valuation.insert(variable, spike);
            return Err(LeqRefutation { strict, valuation });
        };
        atoms.push(AtomBound {
            variable,
            left_offset,
            right_offset,
        });
    }
    let Some(shifted_constant) = u128::from(left.constant_part()).checked_add(shift)
    else {
        return Err(LeqRefutation {
            strict,
            valuation: BTreeMap::new(),
        });
    };
    let constant = if shifted_constant <= u128::from(right.constant_part()) {
        ConstantBound::Constant
    }
    else {
        let dominating = right
            .atoms()
            .find(|&(_variable, offset)| shifted_constant <= u128::from(offset));
        let Some((variable, _offset)) = dominating
        else {
            return Err(LeqRefutation {
                strict,
                valuation: BTreeMap::new(),
            });
        };
        ConstantBound::Atom(variable)
    };
    Ok(LeqWitness {
        strict,
        atoms,
        constant,
    })
}

/// One past the right level's largest component: a spike this high makes a
/// non-dominated left atom overtake everything the right level can reach on
/// that variable.
///
/// # Specification
/// - requires: `right` is canonical, guaranteed by construction.
/// - ensures: returns Some of one more than the largest right component. The
///   None branch refuses an unrepresentable spike; it is unreachable because
///   every component is u64-wide and the successor is u128-wide.
/// - provides: the value the refutation branch spikes a variable to, so that a
///   left atom the right level does not dominate overtakes it there.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero, a dominating atom, a dominating constant and the
///   u64 ceiling distinguish omitted components, missing successor and
///   narrowing arithmetic by the exact spike value.
/// - witness: `order::tests::spike_exceeds_zero_atom_and_numeric_ceiling`
#[spec(ensures: |ret| ret.map(u128::from) == right.atoms()
    .map(|(_, offset)| u128::from(offset))
    .fold(u128::from(right.constant_part()), u128::max).checked_add(1))]
fn spike_value(right: &Level) -> Option<LevelValue>
{
    let mut ceiling = u128::from(right.constant_part());
    for (_variable, offset) in right.atoms() {
        ceiling = ceiling.max(u128::from(offset));
    }
    ceiling.checked_add(1_u128).map(LevelValue::from)
}

/// Checks a domination witness against its two levels.
///
/// # Specification
/// - requires: `witness` claims `left ≤ right`, or `left < right` when its
///   strict flag holds; the claim direction is read from the witness.
/// - ensures: `Ok(())` exactly when the witness proves the claim — every left
///   atom is covered in order by an accurate, dominating bound, no bound is
///   stray, and the constant bound exists and dominates the shifted left
///   constant part.
/// - provides: the trusted half of the evidence discipline, a validator small
///   enough to audit, against which the decision procedure is
///   self-incriminating.
/// - fails: the first [`EvidenceError`] encountered, walking atoms in ascending
///   variable order and the constant bound last. An unrepresentable shifted
///   atom or constant refuses with its corresponding insufficient-bound error;
///   widening u64 components into u128 currently excludes those branches.
/// - panics: none.
///
/// # Errors
/// Every variant of [`EvidenceError`] except [`EvidenceError::NotRefuting`] and
/// [`EvidenceError::Overflow`], which belong to [`validate_refutation`].
///
/// # Adequacy
/// - hypothesis: L3 — the validator is itself an oracle, so each rejection arm
///   is pinned by a hand-perturbed witness asserting the exact variant, and
///   acceptance is pinned by the property that every oracle-produced witness
///   validates.
/// - witness: `order::tests::perturbed_witness_missing_bound_is_rejected`
/// - witness: `order::tests::perturbed_witness_stray_bound_is_rejected`
/// - witness: `order::tests::perturbed_witness_offset_mismatch_is_rejected`
/// - witness: `order::tests::false_witness_insufficient_bound_is_rejected`
/// - witness: `order::tests::perturbed_witness_absent_constant_atom_is_rejected`
/// - witness: `order::tests::false_witness_insufficient_constant_is_rejected`
/// - witness: `level_oracle::level_oracle::prop_evidence_validates`
#[spec(ensures: |ret| ret.is_ok() == (
    witness.atoms.len() == left.atoms_map().len()
        && left.atoms().zip(&witness.atoms).all(|((variable, offset), bound)| {
            bound.variable == variable
                && bound.left_offset == offset
                && right.offset_of(variable) == Some(bound.right_offset)
                && u128::from(offset).checked_add(u128::from(witness.strict.shift()))
                    .is_some_and(|shifted| shifted <= u128::from(bound.right_offset))
        })
        && match witness.constant {
            ConstantBound::Constant => u128::from(left.constant_part())
                .checked_add(u128::from(witness.strict.shift())).is_some_and(|shifted| shifted <= u128::from(right.constant_part())),
            ConstantBound::Atom(variable) => right.offset_of(variable).is_some_and(|offset| {
                u128::from(left.constant_part()).checked_add(u128::from(witness.strict.shift()))
                    .is_some_and(|shifted| shifted <= u128::from(offset))
            }),
        }
))]
#[inline]
pub fn validate_witness(
    left: &Level,
    right: &Level,
    witness: &LeqWitness,
) -> Result<(), EvidenceError>
{
    let shift = u128::from(witness.strict.shift());
    let mut bounds = witness.atoms.iter();
    for (variable, left_offset) in left.atoms() {
        let Some(bound) = bounds.next()
        else {
            return Err(EvidenceError::MissingAtomBound { variable });
        };
        if bound.variable != variable {
            return Err(if bound.variable < variable {
                EvidenceError::StrayAtomBound {
                    variable: bound.variable,
                }
            }
            else {
                EvidenceError::MissingAtomBound { variable }
            });
        }
        let actual_right = right.offset_of(variable);
        if bound.left_offset != left_offset || actual_right != Some(bound.right_offset) {
            return Err(EvidenceError::AtomOffsetMismatch { variable });
        }
        let Some(shifted) = u128::from(bound.left_offset).checked_add(shift)
        else {
            return Err(EvidenceError::InsufficientAtomBound { variable });
        };
        if shifted > u128::from(bound.right_offset) {
            return Err(EvidenceError::InsufficientAtomBound { variable });
        }
    }
    if let Some(stray) = bounds.next() {
        return Err(EvidenceError::StrayAtomBound {
            variable: stray.variable,
        });
    }
    let Some(shifted_constant) = u128::from(left.constant_part()).checked_add(shift)
    else {
        return Err(EvidenceError::InsufficientConstantBound);
    };
    match witness.constant {
        | ConstantBound::Constant => {
            if shifted_constant > u128::from(right.constant_part()) {
                return Err(EvidenceError::InsufficientConstantBound);
            }
        },
        | ConstantBound::Atom(variable) => {
            let Some(offset) = right.offset_of(variable)
            else {
                return Err(EvidenceError::MissingConstantBound { variable });
            };
            if shifted_constant > u128::from(offset) {
                return Err(EvidenceError::InsufficientConstantBound);
            }
        },
    }
    Ok(())
}

/// Checks a refutation against its two levels by direct evaluation.
///
/// # Specification
/// - requires: `refutation` claims `left ≤ right` fails, or that `left < right`
///   fails when its strict flag holds; the claim direction is read from the
///   refutation.
/// - ensures: `Ok(())` exactly when the valuation orders the levels the wrong
///   way — strictly greater for a non-strict claim, at-least for a strict one.
/// - provides: the semantic check on counter-valuations, independent of the
///   domination machinery, since it only evaluates.
/// - fails: [`EvidenceError::NotRefuting`] when the valuation does not refute,
///   and [`EvidenceError::Overflow`] when an adversarial valuation overflows
///   evaluation, which is rejected rather than wrapped.
/// - panics: none.
///
/// # Errors
/// [`EvidenceError::NotRefuting`] and [`EvidenceError::Overflow`].
///
/// # Adequacy
/// - hypothesis: L3 — both rejection arms pinned by exact-variant cases, a
///   non-refuting valuation and an overflowing valuation, with acceptance
///   pinned by the property that every oracle-produced refutation validates.
/// - witness: `order::tests::non_refuting_valuation_is_rejected`
/// - witness: `order::tests::overflowing_valuation_is_rejected`
/// - witness: `level_oracle::level_oracle::prop_evidence_validates`
#[spec(ensures: |ret| ret.is_ok() == match (
    left.eval(&refutation.valuation), right.eval(&refutation.valuation)
) {
    (Ok(left_value), Ok(right_value)) => if bool::from(refutation.strict) {
        left_value >= right_value
    } else {
        left_value > right_value
    },
    _ => false,
})]
#[inline]
pub fn validate_refutation(
    left: &Level,
    right: &Level,
    refutation: &LeqRefutation,
) -> Result<(), EvidenceError>
{
    let left_value = left
        .eval(&refutation.valuation)
        .map_err(|_error| EvidenceError::Overflow)?;
    let right_value = right
        .eval(&refutation.valuation)
        .map_err(|_error| EvidenceError::Overflow)?;
    let refutes = if bool::from(refutation.strict) {
        left_value >= right_value
    }
    else {
        left_value > right_value
    };
    if refutes {
        Ok(())
    }
    else {
        Err(EvidenceError::NotRefuting)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::vec;

    use anodized::spec;

    use super::AtomBound;
    use super::ConstantBound;
    use super::EvidenceError;
    use super::LeqRefutation;
    use super::LeqWitness;
    use super::Strictness;
    use super::validate_refutation;
    use super::validate_witness;
    use crate::level::Level;
    use crate::level::LevelConstant;
    use crate::level::LevelOffset;
    use crate::level::LevelValue;
    use crate::level::LevelVar;
    use crate::level::LevelVarIndex;

    #[test]
    fn zero_is_leq_everything()
    {
        let composite = Level::constant(LevelConstant::from(5_u64))
            .max(&var_plus(x(), LevelOffset::from(3_u64)));
        assert!(
            bool::from(Level::zero().leq(&composite)),
            "zero is a global lower bound"
        );
        assert!(
            bool::from(Level::zero().leq(&Level::zero())),
            "zero is below itself"
        );
    }

    #[test]
    fn leq_is_reflexive_and_lt_is_irreflexive_on_atoms()
    {
        let atom = var_plus(x(), LevelOffset::from(2_u64));
        assert!(bool::from(atom.leq(&atom)), "leq must be reflexive");
        assert!(!bool::from(atom.lt(&atom)), "lt must be irreflexive");
    }

    #[test]
    fn lt_is_irreflexive()
    {
        let composite = Level::constant(LevelConstant::from(7_u64))
            .max(&var_plus(x(), LevelOffset::from(3_u64)))
            .max(&var_plus(y(), LevelOffset::from(5_u64)));
        assert!(
            !bool::from(composite.lt(&composite)),
            "lt must be irreflexive on composites"
        );
    }

    #[test]
    fn var_is_strictly_below_its_successor()
    {
        let base = Level::var(x());
        let above = var_plus(x(), LevelOffset::from(1_u64));
        assert!(bool::from(base.lt(&above)), "x < x+1 must hold");
        assert!(!bool::from(above.leq(&base)), "x+1 <= x must fail");
    }

    #[test]
    fn distinct_variables_are_incomparable()
    {
        let left = Level::var(x());
        let right = Level::var(y());
        let refutation = left
            .leq_with_evidence(&right)
            .expect_err("distinct variables are incomparable");
        assert_eq!(
            Ok(()),
            validate_refutation(&left, &right, &refutation),
            "the refutation must validate"
        );
        let reverse = right
            .leq_with_evidence(&left)
            .expect_err("the reverse direction is incomparable too");
        assert_eq!(
            Ok(()),
            validate_refutation(&right, &left, &reverse),
            "the reverse refutation must validate"
        );
    }

    #[test]
    fn max_is_an_upper_bound()
    {
        let left = var_plus(x(), LevelOffset::from(1_u64));
        let right = var_plus(y(), LevelOffset::from(4_u64));
        let joined = left.max(&right);
        assert!(
            bool::from(left.leq(&joined)),
            "the left component is below the join"
        );
        assert!(
            bool::from(right.leq(&joined)),
            "the right component is below the join"
        );
    }

    #[test]
    fn constant_dominated_by_atom_offset()
    {
        let constant = Level::constant(LevelConstant::from(3_u64));
        let atom = var_plus(x(), LevelOffset::from(3_u64));
        let witness = constant
            .leq_with_evidence(&atom)
            .expect("3 <= x+3 must hold");
        assert_eq!(
            witness.constant_bound(),
            ConstantBound::Atom(x()),
            "3 <= x+3 rests on the atom bound"
        );
        assert_eq!(
            Ok(()),
            validate_witness(&constant, &atom, &witness),
            "the witness must validate"
        );
    }

    #[test]
    fn constant_past_atom_offset_is_refuted_at_zero()
    {
        let constant = Level::constant(LevelConstant::from(4_u64));
        let atom = var_plus(x(), LevelOffset::from(3_u64));
        let refutation = constant
            .leq_with_evidence(&atom)
            .expect_err("4 <= x+3 must fail");
        assert!(
            refutation.valuation().is_empty(),
            "constant violations refute at the zero valuation"
        );
        assert_eq!(
            Ok(()),
            validate_refutation(&constant, &atom, &refutation),
            "the refutation must validate"
        );
    }

    #[test]
    fn constant_bound_names_the_least_dominating_variable()
    {
        let right =
            var_plus(x(), LevelOffset::from(5_u64)).max(&var_plus(y(), LevelOffset::from(5_u64)));
        let left = Level::constant(LevelConstant::from(3_u64));
        let witness = left.leq_with_evidence(&right).expect("3 <= x+5 max y+5");
        assert_eq!(
            witness.constant_bound(),
            ConstantBound::Atom(x()),
            "the least dominating variable is named"
        );
    }

    #[test]
    fn perturbed_witness_absent_constant_atom_is_rejected()
    {
        let left = Level::constant(LevelConstant::from(3_u64));
        let right = var_plus(x(), LevelOffset::from(3_u64));
        let mut witness = left.leq_with_evidence(&right).expect("3 <= x+3 must hold");
        witness.constant = ConstantBound::Atom(y());
        assert_eq!(
            validate_witness(&left, &right, &witness),
            Err(EvidenceError::MissingConstantBound { variable: y() }),
            "a constant bound naming an absent atom must be rejected"
        );
    }

    #[test]
    fn overflowing_valuation_is_rejected()
    {
        let left = var_plus(x(), LevelOffset::from(1_u64));
        let right = Level::zero();
        let mut valuation = BTreeMap::new();
        let _previous = valuation.insert(x(), LevelValue::from(u128::MAX));
        let forged = LeqRefutation {
            strict: Strictness::NON_STRICT,
            valuation,
        };
        assert_eq!(
            Err(EvidenceError::Overflow),
            validate_refutation(&left, &right, &forged),
            "an overflowing valuation must be rejected, never wrapped"
        );
    }

    #[test]
    fn witness_records_accurate_offsets()
    {
        let left = var_plus(x(), LevelOffset::from(1_u64));
        let right = var_plus(x(), LevelOffset::from(4_u64));
        let witness = left.leq_with_evidence(&right).expect("x+1 <= x+4");
        let bounds = witness.atom_bounds();
        assert_eq!(1_usize, bounds.len(), "one atom, one bound");
        let bound = bounds.first().expect("the single bound is present");
        assert_eq!(bound.variable(), x(), "the bound names the atom's variable");
        assert_eq!(
            LevelOffset::from(1_u64),
            bound.left_offset(),
            "the left offset is recorded"
        );
        assert_eq!(
            LevelOffset::from(4_u64),
            bound.right_offset(),
            "the right offset is recorded"
        );
    }

    #[test]
    fn perturbed_witness_offset_mismatch_is_rejected()
    {
        let left = var_plus(x(), LevelOffset::from(1_u64));
        let right = var_plus(x(), LevelOffset::from(4_u64));
        let mut witness = left.leq_with_evidence(&right).expect("x+1 <= x+4");
        witness.atoms = vec![AtomBound {
            variable: x(),
            left_offset: LevelOffset::from(0_u64),
            right_offset: LevelOffset::from(4_u64),
        }];
        assert_eq!(
            validate_witness(&left, &right, &witness),
            Err(EvidenceError::AtomOffsetMismatch { variable: x() }),
            "tampered offsets must be rejected"
        );
    }

    #[test]
    fn false_witness_insufficient_bound_is_rejected()
    {
        let left = var_plus(x(), LevelOffset::from(1_u64));
        let right = Level::var(x());
        let forged = LeqWitness {
            strict: Strictness::NON_STRICT,
            atoms: vec![AtomBound {
                variable: x(),
                left_offset: LevelOffset::from(1_u64),
                right_offset: LevelOffset::from(0_u64),
            }],
            constant: ConstantBound::Atom(x()),
        };
        assert_eq!(
            validate_witness(&left, &right, &forged),
            Err(EvidenceError::InsufficientAtomBound { variable: x() }),
            "an accurate but non-dominating bound must be rejected"
        );
    }

    #[test]
    fn perturbed_witness_missing_bound_is_rejected()
    {
        let left = Level::var(x());
        let right = Level::var(x());
        let forged = LeqWitness {
            strict: Strictness::NON_STRICT,
            atoms: vec![],
            constant: ConstantBound::Constant,
        };
        assert_eq!(
            validate_witness(&left, &right, &forged),
            Err(EvidenceError::MissingAtomBound { variable: x() }),
            "an uncovered atom must be rejected"
        );
    }

    #[test]
    fn perturbed_witness_stray_bound_is_rejected()
    {
        let left = Level::zero();
        let right = Level::var(x());
        let forged = LeqWitness {
            strict: Strictness::NON_STRICT,
            atoms: vec![AtomBound {
                variable: x(),
                left_offset: LevelOffset::from(0_u64),
                right_offset: LevelOffset::from(0_u64),
            }],
            constant: ConstantBound::Atom(x()),
        };
        assert_eq!(
            validate_witness(&left, &right, &forged),
            Err(EvidenceError::StrayAtomBound { variable: x() }),
            "a bound over an absent left atom must be rejected"
        );
    }

    #[test]
    fn non_refuting_valuation_is_rejected()
    {
        let level = Level::var(x());
        let forged = LeqRefutation {
            strict: Strictness::NON_STRICT,
            valuation: BTreeMap::new(),
        };
        assert_eq!(
            Err(EvidenceError::NotRefuting),
            validate_refutation(&level, &level, &forged),
            "a valuation that does not refute must be rejected"
        );
    }

    #[test]
    fn comparison_is_total_at_the_offset_ceiling()
    {
        let ceiling = Level::constant(LevelConstant::from(u64::MAX));
        assert!(
            bool::from(ceiling.leq(&ceiling)),
            "leq stays total at the ceiling"
        );
        assert!(
            !bool::from(ceiling.lt(&ceiling)),
            "lt stays total (and irreflexive) at the ceiling"
        );
    }

    #[test]
    fn strict_comparison_at_the_constant_ceiling_refutes_at_the_zero_valuation()
    {
        let ceiling = Level::constant(LevelConstant::from(u64::MAX));
        let refutation = ceiling
            .lt_with_evidence(&ceiling)
            .expect_err("the strict order is irreflexive at the ceiling");
        assert_eq!(Strictness::STRICT, refutation.strict());
        assert!(refutation.valuation().is_empty());
        assert_eq!(Ok(()), validate_refutation(&ceiling, &ceiling, &refutation));
    }

    #[test]
    fn an_atom_refutation_spikes_above_the_constant_ceiling()
    {
        let left = Level::var(x());
        let right = Level::constant(LevelConstant::from(u64::MAX));
        let refutation = left
            .leq_with_evidence(&right)
            .expect_err("an unbounded variable exceeds every constant");
        assert_eq!(
            BTreeMap::from([(x(), LevelValue::from(0x1_0000_0000_0000_0000_u128))]),
            *refutation.valuation(),
        );
        assert_eq!(Ok(()), validate_refutation(&left, &right, &refutation));
    }

    #[test]
    fn forged_witness_insufficient_constant_at_the_ceiling_is_rejected()
    {
        let ceiling = Level::constant(LevelConstant::from(u64::MAX));
        let forged = LeqWitness {
            strict: Strictness::STRICT,
            atoms: vec![],
            constant: ConstantBound::Constant,
        };
        assert_eq!(
            Err(EvidenceError::InsufficientConstantBound),
            validate_witness(&ceiling, &ceiling, &forged),
        );
    }

    #[test]
    fn false_witness_insufficient_constant_is_rejected()
    {
        let left = Level::constant(LevelConstant::from(4_u64));
        let right = Level::constant(LevelConstant::from(3_u64));
        let forged = LeqWitness {
            strict: Strictness::NON_STRICT,
            atoms: vec![],
            constant: ConstantBound::Constant,
        };
        assert_eq!(
            Err(EvidenceError::InsufficientConstantBound),
            validate_witness(&left, &right, &forged),
            "a non-dominating constant bound must be rejected"
        );
    }

    #[test]
    fn spike_exceeds_zero_atom_and_numeric_ceiling()
    {
        for (right, expected) in [
            (Level::zero(), 1_u128),
            (Level::constant(LevelConstant::from(5_u64)), 6),
            (
                var_plus(x(), LevelOffset::from(3_u64))
                    .max(&Level::constant(LevelConstant::from(1_u64))),
                4,
            ),
            (
                Level::constant(LevelConstant::from(u64::MAX)).max(&Level::var(x())),
                u128::from(u64::MAX).saturating_add(1),
            ),
        ] {
            assert_eq!(super::spike_value(&right), Some(LevelValue::from(expected)));
        }
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — small offsets zero through five produce levels whose
    ///   order and evidence expose changed variable selection, a missing
    ///   successor or an extra shift; unequal offsets are inspected in a
    ///   genuine witness.
    /// - witness: `order::tests::witness_records_accurate_offsets`
    /// - witness: `order::tests::constant_dominated_by_atom_offset`
    /// - witness: `order::tests::var_is_strictly_below_its_successor`
    #[spec(ensures: |ret| ret.constant_part() == LevelConstant::ZERO
        && ret.atoms().eq(core::iter::once((variable, offset))))]
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
}
