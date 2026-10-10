//! The canonical level representation: [`LevelVar`], [`Level`], and the smart
//! constructors that keep every reachable value in canonical form.

use alloc::collections::BTreeMap;
use core::error::Error;
use core::fmt;

use anodized::spec;

/// An index into a level-variable context.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LevelVarIndex(u32);

impl From<u32> for LevelVarIndex
{
    /// Wraps a raw index as a level-variable index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self(index)
    }
}

impl From<LevelVarIndex> for u32
{
    /// Unwraps a level-variable index to its raw index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: LevelVarIndex) -> Self
    {
        index.0
    }
}

impl fmt::Display for LevelVarIndex
{
    /// Renders the index as its decimal value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        u32::from(*self).fmt(f)
    }
}

/// A finite successor count used as a level atom offset.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LevelOffset(u64);

impl LevelOffset
{
    /// The zero offset.
    pub const ZERO: Self = Self(0_u64);

    /// Adds one successor to this offset.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the offset one above `self` when representable.
    /// - provides: the offset half of the level algebra's successor.
    /// - fails: [`LevelError::Overflow`] at the numeric ceiling, rather than
    ///   saturating — saturation would identify distinct offsets.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LevelError::Overflow`] — the offset was at the numeric ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, ordinary offsets, the last representable
    ///   successor and the ceiling expose changed increments and overflow
    ///   guards by exact values and the Overflow variant.
    /// - witness: `level::tests::arithmetic_boundaries_preserve_values_and_refuse_overflow`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map(|value| u64::from(*value)).ok() == u64::from(self).checked_add(1))]
    pub fn succ(self) -> Result<Self, LevelError>
    {
        self.0
            .checked_add(1_u64)
            .map(Self)
            .ok_or(LevelError::Overflow)
    }
}

impl From<u64> for LevelOffset
{
    /// Wraps a raw successor count as a level atom offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: u64) -> Self
    {
        Self(offset)
    }
}

impl From<LevelOffset> for u64
{
    /// Unwraps a level atom offset to its raw successor count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: LevelOffset) -> Self
    {
        offset.0
    }
}

impl From<LevelOffset> for u128
{
    /// Widens a level atom offset to the evaluation arithmetic's width.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: LevelOffset) -> Self
    {
        Self::from(offset.0)
    }
}

/// The canonical constant component of a universe level.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LevelConstant(u64);

impl LevelConstant
{
    /// The zero constant.
    pub const ZERO: Self = Self(0_u64);

    /// Adds one successor to this constant.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the constant one above `self` when representable.
    /// - provides: the constant half of the level algebra's successor.
    /// - fails: [`LevelError::Overflow`] at the numeric ceiling, rather than
    ///   saturating — saturation would identify distinct constants.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LevelError::Overflow`] — the constant was at the numeric ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, ordinary constants, the last representable
    ///   successor and the ceiling expose changed increments and overflow
    ///   guards by exact values and the Overflow variant.
    /// - witness: `level::tests::arithmetic_boundaries_preserve_values_and_refuse_overflow`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map(|value| u64::from(*value)).ok() == u64::from(self).checked_add(1))]
    pub fn succ(self) -> Result<Self, LevelError>
    {
        self.0
            .checked_add(1_u64)
            .map(Self)
            .ok_or(LevelError::Overflow)
    }
}

impl From<u64> for LevelConstant
{
    /// Wraps a raw value as the constant component of a level.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(constant: u64) -> Self
    {
        Self(constant)
    }
}

impl From<LevelConstant> for u64
{
    /// Unwraps a level constant to its raw value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(constant: LevelConstant) -> Self
    {
        constant.0
    }
}

impl From<LevelConstant> for u128
{
    /// Widens a level constant to the evaluation arithmetic's width.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(constant: LevelConstant) -> Self
    {
        Self::from(constant.0)
    }
}

/// A natural value produced by evaluating a level under a valuation.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LevelValue(u128);

impl LevelValue
{
    /// The zero evaluation value.
    pub const ZERO: Self = Self(0_u128);

    /// Adds an atom offset to this valuation value.
    ///
    /// # Specification
    /// - requires: nothing; adversarial values are admissible and are the
    ///   reason the sum is checked.
    /// - ensures: returns the sum when it fits the `u128` range.
    /// - provides: the single arithmetic step of level evaluation.
    /// - fails: [`LevelError::Overflow`] when the sum leaves the range.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LevelError::Overflow`] — the sum passed the `u128` range.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero and positive offsets at ordinary values and
    ///   immediately below, at, and above the u128 sum ceiling distinguish
    ///   changed arithmetic and guards by exact results.
    /// - witness: `level::tests::arithmetic_boundaries_preserve_values_and_refuse_overflow`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map(|value| u128::from(*value)).ok() == u128::from(self).checked_add(u128::from(offset)))]
    pub fn checked_add_offset(
        self,
        offset: LevelOffset,
    ) -> Result<Self, LevelError>
    {
        self.0
            .checked_add(u128::from(offset))
            .map(Self)
            .ok_or(LevelError::Overflow)
    }
}

impl From<u128> for LevelValue
{
    /// Wraps a raw natural as a level evaluation value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u128) -> Self
    {
        Self(value)
    }
}

impl From<LevelValue> for u128
{
    /// Unwraps a level evaluation value to its raw natural.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: LevelValue) -> Self
    {
        value.0
    }
}

impl From<LevelConstant> for LevelValue
{
    /// Reads a level constant as an evaluation value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(constant: LevelConstant) -> Self
    {
        Self(u128::from(constant))
    }
}

impl From<LevelOffset> for LevelValue
{
    /// Reads an atom offset as an evaluation value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: LevelOffset) -> Self
    {
        Self(u128::from(offset))
    }
}

/// Whether a canonical level is the zero level.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LevelIsZero(bool);

impl From<bool> for LevelIsZero
{
    /// Wraps a decision about zeroness as the level-zero answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(is_zero: bool) -> Self
    {
        Self(is_zero)
    }
}

impl From<LevelIsZero> for bool
{
    /// Unwraps the level-zero answer to a plain decision.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(is_zero: LevelIsZero) -> Self
    {
        is_zero.0
    }
}

/// A level variable: an index into the owning declaration's prenex level
/// context.
///
/// The landmark-poset encoding reuses the same index space for declared
/// landmark constants.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LevelVar(LevelVarIndex);

impl LevelVar
{
    /// Wraps a prenex-context index as a level variable.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(index: LevelVarIndex) -> Self
    {
        Self(index)
    }

    /// The prenex-context index this variable wraps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn index(self) -> LevelVarIndex
    {
        self.0
    }
}

impl From<LevelVarIndex> for LevelVar
{
    /// Wraps a prenex-context index as a level variable.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: LevelVarIndex) -> Self
    {
        Self::new(index)
    }
}

impl fmt::Display for LevelVar
{
    /// Renders the variable as its prenex-context index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.index().fmt(f)
    }
}

/// Failures of level arithmetic.
///
/// The vocabulary is closed and total: every operation on levels either
/// succeeds or surfaces one of these, so the kernel never panics on level data.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LevelError
{
    /// An offset or constant stepped past the representable range. Saturating
    /// instead would silently identify distinct levels, so the overflow
    /// surfaces as a typed error.
    Overflow,
}

impl fmt::Display for LevelError
{
    /// Renders the failure as one sentence naming the range it stepped past.
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
            | Self::Overflow => {
                f.write_str("level arithmetic stepped past the representable range")
            },
        }
    }
}

impl Error for LevelError
{
}

/// A universe level in **canonical form**: the finite join
/// `max(constant, x_1 + o_1, …, x_k + o_k)` of a constant part and one offset
/// per variable, interpreted over the naturals.
///
/// The canonical invariant, maintained by every constructor: atoms are keyed by
/// variable with a single maximal offset each, and the constant part is `0`
/// whenever some atom offset dominates it — an atom `x + o` is at least `o`
/// under every valuation, so a constant `c ≤ o` never contributes. Under that
/// invariant, canonical-form identity coincides with semantic equality at every
/// valuation, which is why `Eq` on this type is the kernel's level-equality
/// oracle.
///
/// # Specification
/// - ensures: each variable has one offset, and any constant dominated by an
///   atom offset is zero; equality therefore decides equality of denotations.
/// - panics: none.
/// - executable: none — a data value does not retain its construction inputs;
///   constructor predicates check the canonical invariant when values arise.
///
/// # Adequacy
/// - hypothesis: L2 — generated terms are compared by an independent evaluator
///   and semantic equality. L3 separates constant domination at equality from a
///   larger constant, observing canonical equality and component values.
/// - witness: `level_oracle::level_oracle::prop_eq_agrees_with_semantic_reference`
/// - witness: `level::tests::max_absorbs_dominated_constant`
/// - witness: `level::tests::max_keeps_undominated_constant`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Level
{
    /// The constant part of the join; `0` when dominated by an atom offset.
    constant: LevelConstant,
    /// The variable atoms: each entry `(x, o)` denotes `x + o`.
    atoms: BTreeMap<LevelVar, LevelOffset>,
}

impl Level
{
    /// The level `0`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the canonical form with constant part `0` and no
    ///   atoms, which denotes `0` under every valuation.
    /// - provides: the unit of the level algebra's join.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — under empty and nonempty valuations, the constant and
    ///   atom projections distinguish a nonzero constant or spurious atom.
    /// - witness: `level::tests::constructors_preserve_their_denotations`
    #[spec(ensures: |ret| ret.constant == LevelConstant::ZERO && ret.atoms.is_empty())]
    #[inline]
    #[must_use]
    pub fn zero() -> Self
    {
        Self {
            constant: LevelConstant::ZERO,
            atoms: BTreeMap::new(),
        }
    }

    /// The constant level `value`, the `value`-fold successor of zero.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the canonical form whose constant part is `value` and
    ///   which carries no atoms, so it denotes `value` under every valuation.
    /// - provides: the constant embedding of the naturals into levels.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, an ordinary constant, and the numeric ceiling
    ///   retain their exact value under unrelated variable assignments; the
    ///   atom iterator detects contamination by a variable component.
    /// - witness: `level::tests::constructors_preserve_their_denotations`
    #[spec(ensures: |ret| ret.constant == value && ret.atoms.is_empty())]
    #[inline]
    #[must_use]
    pub fn constant(value: LevelConstant) -> Self
    {
        Self {
            constant: value,
            atoms: BTreeMap::new(),
        }
    }

    /// The level of the bare variable `variable`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the canonical form whose one atom is `variable` at
    ///   offset `0` and whose constant part is `0`, so it denotes the value a
    ///   valuation gives `variable`.
    /// - provides: the variable embedding of the level context into levels.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — variable indices zero and the index ceiling, under
    ///   absent and explicit valuations, expose an altered variable, offset, or
    ///   constant through exact atoms and evaluation.
    /// - witness: `level::tests::constructors_preserve_their_denotations`
    #[spec(ensures: |ret| ret.constant == LevelConstant::ZERO
        && ret.atoms.len() == 1 && ret.atoms.get(&variable) == Some(&LevelOffset::ZERO))]
    #[inline]
    #[must_use]
    pub fn var(variable: LevelVar) -> Self
    {
        let mut atoms = BTreeMap::new();
        let _previous = atoms.insert(variable, LevelOffset::ZERO);
        Self {
            constant: LevelConstant::ZERO,
            atoms,
        }
    }

    /// The successor level: every component shifted up by one.
    ///
    /// # Specification
    /// - requires: nothing beyond a canonical `self`, guaranteed by
    ///   construction.
    /// - ensures: the result denotes `self + 1` at every valuation and is
    ///   canonical.
    /// - provides: the `+1` generator of the level algebra.
    /// - fails: [`LevelError::Overflow`] when a component would pass the
    ///   representable range, rather than saturating, which would identify
    ///   distinct levels.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LevelError::Overflow`] — some constant or offset was at the numeric
    /// ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L2 for the shift itself — the differential suite compares
    ///   against the reference evaluator and the successor/`max` distribution
    ///   law pins the interaction; L3 for the two residues, the overflow
    ///   boundary at the numeric ceiling asserted by exact variant and the
    ///   constant-renormalization pair, where a dominated constant must leave
    ///   the canonical constant at `0` after the shift.
    /// - witness: `level::tests::succ_overflow_surfaces_exact_variant`
    /// - witness: `level::tests::arithmetic_boundaries_preserve_values_and_refuse_overflow`
    /// - witness: `level::tests::succ_renormalizes_dominated_constant`
    /// - witness: `level_oracle::level_oracle::prop_succ_distributes_over_max`
    /// - witness: `level_oracle::level_oracle::prop_eval_agrees_with_reference`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|level| {
        level.atoms.len() == self.atoms.len()
            && self.atoms.iter().all(|(variable, offset)| {
                level.atoms.get(variable).is_some_and(|bumped| {
                    u64::from(*offset).checked_add(1) == Some(u64::from(*bumped))
                })
            })
            && level.constant == if level.atoms.values().any(|offset| {
                u128::from(*offset) >= u128::from(self.constant).saturating_add(1)
            }) {
                LevelConstant::ZERO
            } else {
                LevelConstant::from(u64::from(self.constant).saturating_add(1))
            }
    }))]
    #[inline]
    pub fn succ(&self) -> Result<Self, LevelError>
    {
        let constant = self.constant.succ()?;
        let mut atoms = BTreeMap::new();
        for (&variable, &offset) in &self.atoms {
            let bumped = offset.succ()?;
            let _previous = atoms.insert(variable, bumped);
        }
        Ok(Self::canonicalized(constant, atoms))
    }

    /// The join of two levels.
    ///
    /// # Specification
    /// - requires: nothing beyond canonical inputs, guaranteed by construction.
    /// - ensures: the result denotes the pointwise maximum of the two levels at
    ///   every valuation and is canonical; the operation is commutative,
    ///   associative, and idempotent with `zero` as unit.
    /// - provides: the `max` generator of the level algebra. The clause states
    ///   the pointwise maximum and the canonical form; the algebraic laws
    ///   relate several calls, which one call's postcondition cannot state, and
    ///   the differential suite carries them.
    /// - fails: never — joins take maxima and cannot overflow.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the differential suite checks agreement with the
    ///   reference evaluator and the algebraic laws on generated terms; the L3
    ///   residue is the constant-domination boundary, pinned by the
    ///   absorbed/kept pair, where `max(3, x+3)` collapses to `x+3` while
    ///   `max(5, x+3)` keeps the constant `5`.
    /// - witness: `level::tests::max_absorbs_dominated_constant`
    /// - witness: `level::tests::max_keeps_undominated_constant`
    /// - witness: `level_oracle::level_oracle::prop_max_laws`
    /// - witness: `level_oracle::level_oracle::prop_eval_agrees_with_reference`
    #[spec(ensures: |ret| {
        self.atoms.keys().chain(other.atoms.keys()).all(|variable| ret.atoms.contains_key(variable))
            && ret.atoms.iter().all(|(variable, offset)| {
                Some(*offset) == self.atoms.get(variable).max(other.atoms.get(variable)).copied()
            })
            && ret.constant == if ret.atoms.values().any(|offset| {
                u128::from(*offset) >= u128::from(self.constant.max(other.constant))
            }) {
                LevelConstant::ZERO
            } else {
                self.constant.max(other.constant)
            }
    })]
    #[inline]
    #[must_use]
    pub fn max(
        &self,
        other: &Self,
    ) -> Self
    {
        let constant = self.constant.max(other.constant);
        let mut atoms = self.atoms.clone();
        for (&variable, &offset) in &other.atoms {
            let maximum = atoms.entry(variable).or_insert(offset);
            *maximum = (*maximum).max(offset);
        }
        Self::canonicalized(constant, atoms)
    }

    /// The canonical constant part, which is `0` when dominated by an atom
    /// offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn constant_part(&self) -> LevelConstant
    {
        self.constant
    }

    /// The offset of `variable` in this level.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some(offset)` when the canonical form carries an atom over
    ///   `variable`, `None` when it carries none — ordinary lookup absence, not
    ///   a swallowed failure, since the operation cannot fail.
    /// - provides: per-variable read access to the canonical form, used by the
    ///   evidence validators.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — absent variables and present zero/nonzero offsets
    ///   distinguish fabricated membership, wrong-key lookup, and lost offsets
    ///   by exact optional values.
    /// - witness: `level::tests::var_has_zero_offset`
    /// - witness: `level::tests::absent_variable_reads_as_lookup_absence`
    /// - witness: `level::tests::max_keeps_undominated_constant`
    #[spec(ensures: |ret| ret == self.atoms.get(&variable).copied())]
    #[inline]
    #[must_use]
    pub fn offset_of(
        &self,
        variable: LevelVar,
    ) -> Option<LevelOffset>
    {
        self.atoms.get(&variable).copied()
    }

    /// The variable atoms in ascending variable order, each as
    /// `(variable, offset)`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields each atom of the canonical form exactly once, in
    ///   ascending variable order, and yields nothing for a level with no
    ///   atoms.
    /// - provides: the atom-by-atom read the order oracle and the evidence
    ///   validators walk.
    /// - panics: none.
    /// - executable: none — the opaque iterator cannot be named by the
    ///   postcondition expansion or consumed without changing its output.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, singleton, and reverse-inserted distinct atoms
    ///   expose omission, duplication, reordering, and wrong offsets through
    ///   exact iteration to exhaustion.
    /// - witness: `level::tests::atom_iteration_preserves_order_and_offsets`
    #[inline]
    pub fn atoms(&self) -> impl Iterator<Item = (LevelVar, LevelOffset)> + '_
    {
        self.atoms
            .iter()
            .map(|(&variable, &offset)| (variable, offset))
    }

    /// Whether this is the level `0`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: answers affirmatively exactly when the level denotes `0`
    ///   under every valuation; canonicity makes the syntactic test — constant
    ///   part `0` and no atoms — the semantic one.
    /// - provides: the zero decision, without building a level to compare
    ///   against.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, positive constants, and zero-offset variables
    ///   separate both conjuncts of the zero decision by exact truth values.
    /// - witness: `level::tests::constructors_preserve_their_denotations`
    #[spec(ensures: |ret| bool::from(ret) == (self.constant == LevelConstant::ZERO && self.atoms.is_empty()))]
    #[inline]
    #[must_use]
    pub fn is_zero(&self) -> LevelIsZero
    {
        LevelIsZero::from(self.constant == LevelConstant::ZERO && self.atoms.is_empty())
    }

    /// Evaluates the level under a valuation of its variables, reading absent
    /// variables as `0`.
    ///
    /// # Specification
    /// - requires: nothing; any valuation is admissible.
    /// - ensures: returns `max(constant, valuation(x_i) + o_i, …)`, the
    ///   denotation the canonical form stands for.
    /// - provides: the crate's semantic anchor, used by [`validate_refutation`]
    ///   to check counter-valuations.
    /// - fails: [`LevelError::Overflow`] when a valuation value plus an offset
    ///   passes the `u128` range — unreachable for oracle-constructed evidence,
    ///   reachable for adversarial valuations, which are rejected rather than
    ///   wrapped.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LevelError::Overflow`] — a component sum passed the `u128` range.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — agreement with the independent reference evaluator on
    ///   generated terms under random valuations kills value mutants; the L3
    ///   residue is the overflow guard, asserted by exact variant at the `u128`
    ///   ceiling.
    /// - witness: `level::tests::eval_overflow_surfaces_exact_variant`
    /// - witness: `level_oracle::level_oracle::prop_eval_agrees_with_reference`
    ///
    /// [`validate_refutation`]: crate::validate_refutation
    #[spec(ensures: |ret| ret.as_ref().ok().map(|value| u128::from(*value)) ==
        self.atoms.iter().try_fold(u128::from(self.constant), |maximum, (variable, offset)| {
            valuation.get(variable).copied().unwrap_or(LevelValue::ZERO)
                .0.checked_add(u128::from(*offset)).map(|component| maximum.max(component))
        }))]
    #[inline]
    pub fn eval(
        &self,
        valuation: &BTreeMap<LevelVar, LevelValue>,
    ) -> Result<LevelValue, LevelError>
    {
        let mut value = LevelValue::from(self.constant);
        for (&variable, &offset) in &self.atoms {
            let base = valuation
                .get(&variable)
                .copied()
                .unwrap_or(LevelValue::ZERO);
            let component = base.checked_add_offset(offset)?;
            value = value.max(component);
        }
        Ok(value)
    }

    /// Crate-internal read access to the atom map. Fields stay private so
    /// canonical form is unforgeable outside the constructors.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn atoms_map(&self) -> &BTreeMap<LevelVar, LevelOffset>
    {
        &self.atoms
    }

    /// Restores the canonical-constant invariant over raw parts: a constant
    /// dominated by some atom offset is replaced by `0`.
    ///
    /// # Specification
    /// - requires: `atoms` already holds at most one maximal offset per
    ///   variable — the map shape guarantees the former, the callers the
    ///   latter.
    /// - ensures: the result is canonical and denotes `max(constant, atoms…)`
    ///   at every valuation, since dropping a dominated constant never changes
    ///   the denotation: an atom `x + o` evaluates to at least `o`.
    /// - provides: the single point where the canonical invariant is
    ///   re-established after an operation.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L0 mostly — the invariant makes non-canonical levels
    ///   unrepresentable, so an equality mutant must forge identical canonical
    ///   forms; the constant-domination decision itself is the L3 residue,
    ///   pinned by the absorbed/kept boundary pair on [`Self::max`].
    /// - witness: `level::tests::max_absorbs_dominated_constant`
    /// - witness: `level::tests::max_keeps_undominated_constant`
    // The predicate is the canonical-constant invariant read off the result:
    // either the constant is zero, or it strictly dominates every atom offset.
    // It repeats the body's `max` scan, so `canonicalized` costs twice its atom
    // walk — the same order, over a map whose size is the declaration's level
    // arity.
    #[spec(ensures: |ret| ret.constant == LevelConstant::ZERO
        || ret
            .atoms
            .values()
            .copied()
            .max()
            .is_none_or(|ceiling| u128::from(ceiling) < u128::from(ret.constant)))]
    fn canonicalized(
        constant: LevelConstant,
        atoms: BTreeMap<LevelVar, LevelOffset>,
    ) -> Self
    {
        let dominated = atoms
            .values()
            .copied()
            .max()
            .is_some_and(|ceiling| u128::from(constant) <= u128::from(ceiling));
        Self {
            constant: if dominated {
                LevelConstant::ZERO
            }
            else {
                constant
            },
            atoms,
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;

    use anodized::spec;

    use super::Level;
    use super::LevelConstant;
    use super::LevelError;
    use super::LevelOffset;
    use super::LevelValue;
    use super::LevelVar;
    use super::LevelVarIndex;

    #[test]
    fn constructors_preserve_their_denotations()
    {
        for index in [0_u32, u32::MAX] {
            let variable = LevelVar::new(LevelVarIndex::from(index));
            let valuation = BTreeMap::from([(variable, LevelValue::from(11_u128))]);
            let zero = Level::zero();
            assert_eq!(zero.eval(&valuation), Ok(LevelValue::ZERO));
            assert_eq!(zero.atoms().next(), None);
            assert!(bool::from(zero.is_zero()));
            for value in [0_u64, 7, u64::MAX] {
                let constant = Level::constant(LevelConstant::from(value));
                assert_eq!(
                    constant.eval(&valuation),
                    Ok(LevelValue::from(u128::from(value)))
                );
                assert_eq!(constant.atoms().next(), None);
                assert_eq!(bool::from(constant.is_zero()), value == 0);
            }
            let level = Level::var(variable);
            assert_eq!(level.eval(&valuation), Ok(LevelValue::from(11_u128)));
            assert_eq!(level.eval(&BTreeMap::new()), Ok(LevelValue::ZERO));
            assert_eq!(level.atoms().collect::<alloc::vec::Vec<_>>(), [(
                variable,
                LevelOffset::ZERO
            )]);
            assert!(!bool::from(level.is_zero()));
        }
    }

    #[test]
    fn arithmetic_boundaries_preserve_values_and_refuse_overflow()
    {
        for value in [0_u64, 7, u64::MAX.saturating_sub(1), u64::MAX] {
            let expected = value.checked_add(1).ok_or(LevelError::Overflow);
            assert_eq!(LevelOffset::from(value).succ().map(u64::from), expected);
            assert_eq!(LevelConstant::from(value).succ().map(u64::from), expected);
            let level = Level::canonicalized(
                LevelConstant::ZERO,
                BTreeMap::from([(x(), LevelOffset::from(value))]),
            );
            assert_eq!(
                level.succ().map(|level| level.offset_of(x())),
                expected.map(|offset| Some(LevelOffset::from(offset)))
            );
        }
        for (base, offset, expected) in [
            (0_u128, 0_u64, Ok(0_u128)),
            (7, 3, Ok(10)),
            (u128::MAX, 0, Ok(u128::MAX)),
            (u128::MAX.saturating_sub(1), 1, Ok(u128::MAX)),
            (u128::MAX, 1, Err(LevelError::Overflow)),
        ] {
            assert_eq!(
                LevelValue::from(base)
                    .checked_add_offset(LevelOffset::from(offset))
                    .map(u128::from),
                expected
            );
        }
    }

    #[test]
    fn atom_iteration_preserves_order_and_offsets()
    {
        assert_eq!(Level::zero().atoms().next(), None);
        let level = var_plus(y(), LevelOffset::from(3_u64)).max(&var_plus(x(), LevelOffset::ZERO));
        let mut atoms = level.atoms();
        assert_eq!(atoms.next(), Some((x(), LevelOffset::ZERO)));
        assert_eq!(atoms.next(), Some((y(), LevelOffset::from(3_u64))));
        assert_eq!(atoms.next(), None);
        assert_eq!(atoms.next(), None);
    }

    #[test]
    fn zero_is_zero()
    {
        assert!(
            bool::from(Level::zero().is_zero()),
            "zero must report is_zero"
        );
        assert_eq!(
            LevelConstant::from(0_u64),
            Level::zero().constant_part(),
            "zero has constant part 0"
        );
    }

    #[test]
    fn var_has_zero_offset()
    {
        let level = Level::var(x());
        assert_eq!(
            Some(LevelOffset::from(0_u64)),
            level.offset_of(x()),
            "a bare variable has offset 0"
        );
        assert!(!bool::from(level.is_zero()), "a bare variable is not zero");
    }

    #[test]
    fn absent_variable_reads_as_lookup_absence()
    {
        let level = Level::var(x());
        assert_eq!(
            None,
            level.offset_of(y()),
            "a variable the level does not mention has no offset"
        );
    }

    #[test]
    fn max_absorbs_dominated_constant()
    {
        let atom = var_plus(x(), LevelOffset::from(3_u64));
        let joined = Level::constant(LevelConstant::from(3_u64)).max(&atom);
        assert_eq!(joined, atom, "max(3, x+3) must collapse to x+3");
        assert_eq!(
            LevelConstant::from(0_u64),
            joined.constant_part(),
            "the dominated constant must canonicalize to 0"
        );
    }

    #[test]
    fn max_keeps_undominated_constant()
    {
        let atom = var_plus(x(), LevelOffset::from(3_u64));
        let joined = Level::constant(LevelConstant::from(5_u64)).max(&atom);
        assert_ne!(joined, atom, "max(5, x+3) must not collapse to x+3");
        assert_eq!(
            LevelConstant::from(5_u64),
            joined.constant_part(),
            "the undominated constant must survive"
        );
        assert_eq!(
            Some(LevelOffset::from(3_u64)),
            joined.offset_of(x()),
            "the atom must survive beside it"
        );
    }

    #[test]
    fn succ_renormalizes_dominated_constant()
    {
        let bumped = Level::var(x()).succ().expect("succ of a bare variable");
        assert_eq!(
            LevelConstant::from(0_u64),
            bumped.constant_part(),
            "succ(x) has a dominated constant part"
        );
        assert_eq!(
            Some(LevelOffset::from(1_u64)),
            bumped.offset_of(x()),
            "succ(x) is the atom x+1"
        );
    }

    #[test]
    fn succ_overflow_surfaces_exact_variant()
    {
        let ceiling = Level::constant(LevelConstant::from(u64::MAX));
        assert_eq!(
            Err(LevelError::Overflow),
            ceiling.succ(),
            "succ at the ceiling must overflow"
        );
    }

    #[test]
    fn eval_reads_absent_variables_as_zero()
    {
        let level = var_plus(x(), LevelOffset::from(2_u64));
        let empty = BTreeMap::new();
        assert_eq!(
            Ok(LevelValue::from(2_u128)),
            level.eval(&empty),
            "an absent variable evaluates as 0"
        );
    }

    #[test]
    fn eval_takes_the_join()
    {
        let level = Level::constant(LevelConstant::from(5_u64))
            .max(&var_plus(x(), LevelOffset::from(3_u64)));
        let mut valuation = BTreeMap::new();
        let _previous = valuation.insert(x(), LevelValue::from(4_u128));
        assert_eq!(
            Ok(LevelValue::from(7_u128)),
            level.eval(&valuation),
            "max(5, 4+3) is 7"
        );
    }

    #[test]
    fn eval_overflow_surfaces_exact_variant()
    {
        let level = var_plus(x(), LevelOffset::from(1_u64));
        let mut valuation = BTreeMap::new();
        let _previous = valuation.insert(x(), LevelValue::from(u128::MAX));
        assert_eq!(
            Err(LevelError::Overflow),
            level.eval(&valuation),
            "u128::MAX + 1 must overflow"
        );
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
    /// - hypothesis: L3 — offsets zero, one, and three retain the requested
    ///   variable and offset; exact canonical projections expose omitted or
    ///   repeated successors.
    /// - witness: `level::tests::atom_iteration_preserves_order_and_offsets`
    /// - witness: `level::tests::max_absorbs_dominated_constant`
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
