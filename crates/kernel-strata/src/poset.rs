//! The landmark poset: a fixed, declared set of order constraints over level
//! variables, admitted into the kernel by Bezem–Coquand loop-checking with
//! checkable evidence either way — a [`ConsistencyWitness`], an explicit
//! `ℕ`-homomorphism validated by evaluating every constraint under it, on
//! admission; or a [`LoopWitness`], a replayable pumping derivation, on
//! refusal. Exactly one of the two exists, which is what makes admission
//! consistency-bearing: an admitted poset has an `ℕ` model, so `U_l : U_l`
//! stays underivable under its hypotheses.
//!
//! # The constraint language is variable-only
//!
//! Declared constraint sides must be **variable-only levels**: canonical
//! constant part `0` and at least one atom. The algebra of the loop-checking
//! paper is deliberately constant-free, and this crate carries query constants
//! across that gap with a pinned bottom generator `⊥` — a constant `c` becomes
//! the atom `⊥ + c` — ordered below every in-scope variable by bottom clauses
//! `x → ⊥` added at query time. That encoding is sound and conservative
//! *because* constraints are variable-only:
//!
//! * soundness — `⊥ ≤ x` proves `⊥+k ≤ x+k` by the monotone endomorphism, which
//!   is exactly the bottom clauses' shift family, so any semilattice model of
//!   the constraints extends over the freely adjoined bottom;
//! * conservativity — bottom atoms are derivation dead ends, since no declared
//!   clause has `⊥` in its body, because no declared constraint may mention a
//!   constant, so a derivation of a `⊥`-free goal never needs them and
//!   restricts to the declared system;
//! * loop-immunity — for the same reason `⊥` cannot participate in a cycle, so
//!   admission is decided on the declared constraints alone.
//!
//! Allowing constants in declared constraints, say `α ≥ 5`, would put `⊥` in
//! clause bodies and break all three arguments at once; that needs its own
//! design pass rather than a lifted restriction.
//!
//! # Determinism of compiled clauses
//!
//! Evidence refers to clauses by index into one documented, deterministic
//! compilation, so the indices mean the same thing to the oracle, the
//! validators, and a human reviewer:
//!
//! * constraints compile in declaration order;
//! * `left ≤ right` compiles to `atoms(right) → a` for each atom `a` of `left`
//!   in ascending variable order — the non-trivial family of the equation `left
//!   ∨ right = right`;
//! * `left = right` compiles to `atoms(left) → b` for each atom `b` of `right`
//!   in ascending variable order, then `atoms(right) → a` for each atom `a` of
//!   `left`;
//! * self-subsumed clauses, whose conclusion is dominated by a same-variable
//!   body atom, are omitted, since every model satisfies them vacuously;
//! * query systems append one bottom clause `x → ⊥` per in-scope variable in
//!   ascending order after the constraint clauses.
//!
//! The primary reference is Marc Bezem and Thierry Coquand, "Loop-checking and
//! the uniform word problem for join-semilattices with an inflationary
//! endomorphism", *Theoretical Computer Science* 913 (2022), 1–7,
//! `doi:10.1016/j.tcs.2022.01.017`; admission is its corollary 3.5 and
//! entailment its corollary 3.4.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::error::Error;
use core::fmt;

use anodized::spec;

use crate::horn;
use crate::horn::ClauseIndex;
use crate::horn::ClauseSystem;
use crate::horn::DerivationRoundLimit;
use crate::horn::FiringLogStep;
use crate::horn::HVar;
use crate::horn::HornAtom;
use crate::horn::HornClause;
use crate::horn::HornOffset;
use crate::horn::HornShift;
use crate::horn::MaxGain;
use crate::horn::ModelValue;
use crate::horn::SaturationBound;
use crate::level::Level;
use crate::level::LevelConstant;
use crate::level::LevelVar;

/// A natural value in a consistency homomorphism certificate.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ConsistencyValue(u128);

impl From<u128> for ConsistencyValue
{
    /// Wraps a raw natural as a consistency-certificate value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u128) -> Self
    {
        Self(value)
    }
}

impl From<ConsistencyValue> for u128
{
    /// Unwraps a consistency-certificate value to its raw natural.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: ConsistencyValue) -> Self
    {
        value.0
    }
}

/// A constraint's position in the declared list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ConstraintIndex(usize);

impl From<usize> for ConstraintIndex
{
    /// Wraps a position in the declared list as a constraint index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<ConstraintIndex> for usize
{
    /// Unwraps a constraint index to its raw position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ConstraintIndex) -> Self
    {
        index.0
    }
}

impl fmt::Display for ConstraintIndex
{
    /// Renders the index as its decimal position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        usize::from(*self).fmt(f)
    }
}

/// Which generator an evidence position names: the pinned bottom generator that
/// carries constants, or a level variable.
///
/// This is the public mirror of the compiled system's variable domain. It is a
/// total two-case vocabulary rather than an `Option<LevelVar>`, so "the
/// constant side" is stated rather than encoded as an absent variable.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum EvidenceSubject
{
    /// The pinned bottom generator, which carries the constant part.
    Bottom,
    /// An ordinary level variable.
    Variable(LevelVar),
}

impl EvidenceSubject
{
    /// The compiled-system variable this subject names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn to_horn(self) -> HVar
    {
        match self {
            | Self::Bottom => HVar::Bottom,
            | Self::Variable(variable) => HVar::Var(variable),
        }
    }

    /// The subject naming a compiled-system variable.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn from_horn(variable: HVar) -> Self
    {
        match variable {
            | HVar::Bottom => Self::Bottom,
            | HVar::Var(level_var) => Self::Variable(level_var),
        }
    }
}

impl fmt::Display for EvidenceSubject
{
    /// Renders the subject as the constant generator or as its variable.
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
            | Self::Bottom => f.write_str("the constant (bottom) generator"),
            | Self::Variable(variable) => write!(f, "variable {}", variable.index()),
        }
    }
}

/// The declared relation of a [`LandmarkConstraint`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConstraintRelation
{
    /// `left ≤ right`.
    Leq,
    /// `left = right`.
    Eq,
}

/// Failures of poset construction and the decision procedures.
///
/// The vocabulary is closed and total: every operation either succeeds, returns
/// its negative evidence, or surfaces one of these, so the kernel never panics
/// on poset data.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PosetError
{
    /// A declared constraint side mentions a constant — a nonzero canonical
    /// constant part, or no atoms at all — outside the variable-only
    /// restriction this module's docs record.
    ConstantInConstraint,
    /// Arithmetic stepped past the representable range. Saturating instead
    /// would silently identify distinct judgments, so the overflow surfaces as
    /// a typed error.
    Overflow,
    /// A query's model computation diverged on an admitted poset. Admission
    /// excludes this: an admitted poset has no loop, and a divergent component
    /// implies one. It is reachable only under a defect in admission itself,
    /// and is surfaced rather than trusted.
    UnexpectedDivergence,
    /// Evidence extraction hit its round limit before covering its targets. The
    /// theory excludes this, since the targets are derivable whenever this path
    /// runs; it is surfaced rather than trusted.
    EvidenceIncomplete,
}

impl fmt::Display for PosetError
{
    /// Renders the failure as one sentence naming what the operation hit.
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
            | Self::ConstantInConstraint => {
                f.write_str("a declared constraint side mentions a constant")
            },
            | Self::Overflow => {
                f.write_str("poset arithmetic stepped past the representable range")
            },
            | Self::UnexpectedDivergence => {
                f.write_str("a query diverged on an admitted poset (excluded by admission)")
            },
            | Self::EvidenceIncomplete => {
                f.write_str("evidence extraction missed its targets (excluded by the theory)")
            },
        }
    }
}

impl Error for PosetError
{
}

/// One declared landmark constraint: `left REL right` over variable-only
/// levels.
///
/// Constructed only through [`Self::leq`] and [`Self::equal`], which enforce
/// the variable-only restriction, so an ill-formed constraint is
/// unrepresentable.
///
/// # Specification
/// - ensures: both sides are nonempty joins of variables and offsets with no
///   residual constant.
/// - executable: none — data-item predicates are not checked at construction;
///   the two checked constructors enforce this invariant.
///
/// # Adequacy
/// - hypothesis: L3 — zero, pure constants and undominated constants on either
///   side are refused, while a dominated constant and repeated variables across
///   the sides are accepted and enumerated exactly.
/// - witness: `poset::tests::constraint_guards_both_sides_and_preserves_variable_order`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LandmarkConstraint
{
    /// The left side, variable-only.
    left: Level,
    /// The declared relation.
    relation: ConstraintRelation,
    /// The right side, variable-only.
    right: Level,
}

impl LandmarkConstraint
{
    /// Declares `left ≤ right`.
    ///
    /// # Specification
    /// - requires: nothing; any pair of canonical levels is admissible input.
    /// - ensures: a well-formed constraint carrying the sides verbatim.
    /// - provides: the non-strict half of the declared constraint language.
    /// - fails: [`PosetError::ConstantInConstraint`] otherwise.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PosetError::ConstantInConstraint`] — a side mentions a constant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the guard is a conjunction over two sides and two
    ///   conditions, so each rejecting shape is enumerated exactly: an
    ///   undominated constant beside an atom, a pure constant side, the zero
    ///   side, and the accepted boundary where the constant is canonicalized
    ///   away.
    /// - witness: `poset::tests::constants_in_constraints_are_rejected`
    // The predicate covers the relation the declaration names, which is the one
    // half of "carrying the sides verbatim" that survives the sides being moved
    // into the constructor; the guard itself is stated on [`Self::new`]'s prose
    // and answered there as a typed error rather than assumed.
    #[inline]
    #[spec(ensures: |ret| ret.is_err()
        || ret
            .as_ref()
            .is_ok_and(|constraint| constraint.relation() == ConstraintRelation::Leq))]
    pub fn leq(
        left: Level,
        right: Level,
    ) -> Result<Self, PosetError>
    {
        Self::new(left, ConstraintRelation::Leq, right)
    }

    /// Declares `left = right`.
    ///
    /// # Specification
    /// - requires: nothing; any pair of canonical levels is admissible input.
    /// - ensures: a well-formed constraint carrying the sides verbatim.
    /// - provides: the equational half of the declared constraint language.
    /// - fails: [`PosetError::ConstantInConstraint`] otherwise.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PosetError::ConstantInConstraint`] — a side mentions a constant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the guard is shared with [`Self::leq`] and pinned
    ///   there; the equational arm's own effect is on compilation, pinned by
    ///   the self-successor loop golden.
    /// - witness: `poset::tests::constants_in_constraints_are_rejected`
    /// - witness: `poset::tests::self_successor_equality_loops`
    #[inline]
    #[spec(ensures: |ret| ret.is_err()
        || ret
            .as_ref()
            .is_ok_and(|constraint| constraint.relation() == ConstraintRelation::Eq))]
    pub fn equal(
        left: Level,
        right: Level,
    ) -> Result<Self, PosetError>
    {
        Self::new(left, ConstraintRelation::Eq, right)
    }

    /// The shared checked constructor.
    ///
    /// # Specification
    /// - requires: nothing; any pair of levels is admissible input.
    /// - ensures: `Ok` exactly when both sides are variable-only.
    /// - provides: the single point where the variable-only restriction is
    ///   enforced.
    /// - fails: [`PosetError::ConstantInConstraint`] when either side carries a
    ///   nonzero canonical constant part or has no atoms.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PosetError::ConstantInConstraint`] for either non-variable-only side.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, a pure constant and an undominated constant on
    ///   either side are refused; a dominated constant disappears before
    ///   admission. Exact errors and successful relations distinguish a missing
    ///   conjunct.
    /// - witness: `poset::tests::constraint_guards_both_sides_and_preserves_variable_order`
    #[spec(
        captures: [variable_only = left.constant_part() == LevelConstant::ZERO
            && left.atoms().next().is_some()
            && right.constant_part() == LevelConstant::ZERO
            && right.atoms().next().is_some()],
        ensures: |ret| ret.is_ok() == variable_only,
    )]
    fn new(
        left: Level,
        relation: ConstraintRelation,
        right: Level,
    ) -> Result<Self, PosetError>
    {
        let variable_only = |side: &Level| {
            side.constant_part() == LevelConstant::ZERO && side.atoms().next().is_some()
        };
        if variable_only(&left) && variable_only(&right) {
            Ok(Self {
                left,
                relation,
                right,
            })
        }
        else {
            Err(PosetError::ConstantInConstraint)
        }
    }

    /// The left side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn left(&self) -> &Level
    {
        &self.left
    }

    /// The declared relation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn relation(&self) -> ConstraintRelation
    {
        self.relation
    }

    /// The right side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn right(&self) -> &Level
    {
        &self.right
    }

    /// The variables the constraint mentions.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields every variable the two sides mention — the left side's
    ///   atoms in ascending order, then the right side's — so a variable both
    ///   sides mention is yielded twice.
    /// - provides: the variable collection admission declares the poset over,
    ///   which is a set and therefore absorbs the repetition.
    /// - panics: none.
    /// - executable: none — the opaque iterator cannot be named by the
    ///   postcondition expansion or consumed without changing its output.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two ordered sides share one variable; exact iteration
    ///   including that repetition exposes omission, premature deduplication
    ///   and interleaving the sides instead of concatenating them.
    /// - witness: `poset::tests::constraint_guards_both_sides_and_preserves_variable_order`
    fn variables(&self) -> impl Iterator<Item = LevelVar> + '_
    {
        let left = self.left.atoms().map(|(variable, _offset)| variable);
        let right = self.right.atoms().map(|(variable, _offset)| variable);
        left.chain(right)
    }
}

/// One step of a replayable forward derivation: the base clause, by index into
/// the documented compilation, and the upward shift it fires at.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DerivationStep
{
    /// The base clause index.
    clause: ClauseIndex,
    /// The upward shift the instance fires at.
    shift: HornShift,
}

impl DerivationStep
{
    /// Builds a replayable derivation step.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        clause: ClauseIndex,
        shift: HornShift,
    ) -> Self
    {
        Self { clause, shift }
    }

    /// The base clause index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn clause(&self) -> ClauseIndex
    {
        self.clause
    }

    /// The upward shift the instance fires at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn shift(&self) -> HornShift
    {
        self.shift
    }
}

/// A replayable forward derivation.
///
/// A derivation is a sequence of clause-instance applications. Predecessor
/// clauses stay implicit: an atom is available whenever the derived maximum of
/// its variable reaches its offset, which is the downward-closed model reading.
///
/// Derivations are constructed only by the oracle, since the field is private;
/// they are inspected through the accessors and replayed by the validators.
///
/// # Specification
/// - ensures: oracle-produced steps replay in order to the claimed targets from
///   the originating seed.
/// - executable: none — legality depends on the external seed and clause
///   system.
///
/// # Adequacy
/// - hypothesis: L2 — generated evidence replays independently. L3 mutates
///   clause indices, shifts and step availability; the exact refusal separates
///   an invalid derivation from a valid pumping certificate.
/// - witness: `entailment_oracle::entailment_oracle::prop_fixed_poset_evidence_validates`
/// - witness: `poset::tests::perturbed_loop_witness_arms_are_rejected`
/// - witness: `entail::tests::perturbed_witness_arms_are_rejected`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Derivation
{
    /// The steps, in application order.
    steps: Vec<DerivationStep>,
}

impl Derivation
{
    /// The steps, in application order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn steps(&self) -> &[DerivationStep]
    {
        &self.steps
    }

    /// Wraps an engine firing log, dropping the concluded atoms the engine
    /// carries for its own bookkeeping: a validator recomputes them from the
    /// clause and the shift, so recording them would be trusting them.
    ///
    /// # Specification
    /// - requires: `log` is an engine firing log, whose steps are in
    ///   application order.
    /// - ensures: returns the derivation carrying one step per log entry, in
    ///   the same order, each keeping the entry's clause index and shift and
    ///   dropping its concluded atom.
    /// - provides: the engine-to-evidence boundary, across which a validator
    ///   recomputes what it would otherwise have to trust.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — oracle-produced derivations replay against
    ///   independent validators. The empty derivation and multi-step paper loop
    ///   distinguish omission, reversal or altered clause indices and shifts by
    ///   target coverage.
    /// - witness: `poset::tests::paper_loop_variant_returns_a_validating_loop_witness`
    /// - witness: `poset::tests::perturbed_loop_witness_arms_are_rejected`
    /// - witness: `entail::tests::perturbed_witness_arms_are_rejected`
    #[spec(ensures: |ret| ret.steps.iter().map(|step| (step.clause(), step.shift()))
        .eq(log.iter().map(|step| (step.clause(), step.shift()))))]
    pub(crate) fn from_log(log: &[FiringLogStep]) -> Self
    {
        let steps = log
            .iter()
            .map(|step| DerivationStep {
                clause: step.clause(),
                shift: step.shift(),
            })
            .collect();
        Self { steps }
    }
}

/// The positive admission evidence.
///
/// An explicit homomorphism into `ℕ` — one value per declared variable — under
/// which every declared constraint holds. Its existence is what admission
/// certifies; [`validate_consistency`] checks it by direct evaluation.
///
/// # Specification
/// - ensures: an oracle-produced assignment is total over declared variables
///   and satisfies the originating constraints.
/// - executable: none — the originating constraints are external to the
///   assignment.
///
/// # Adequacy
/// - hypothesis: L2 — the paper certificate satisfies direct constraint
///   evaluation. L3 deletes an assignment or violates an inequality and
///   observes the exact validator error; the empty constraint set has an empty
///   certificate.
/// - witness: `poset::tests::paper_example_admits_with_a_validating_homomorphism`
/// - witness: `poset::tests::perturbed_consistency_witness_is_rejected`
/// - witness: `poset::tests::empty_constraint_set_admits_with_an_empty_certificate`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConsistencyWitness
{
    /// The homomorphism's value at each declared variable.
    values: BTreeMap<LevelVar, ConsistencyValue>,
}

impl ConsistencyWitness
{
    /// The homomorphism's value at `variable`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some(value)` when `variable` is declared, `None` when it is
    ///   not — ordinary lookup absence, not a swallowed failure, since the
    ///   operation cannot fail.
    /// - provides: the per-variable read the consistency validator needs.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and nonempty certificates expose missing versus
    ///   present zero and positive assignments through exact lookup results. A
    ///   variable outside the declared set must remain absent.
    /// - witness: `poset::tests::reflection_and_assignment_boundaries`
    #[spec(ensures: |ret| ret == self.values.get(&variable).copied())]
    #[inline]
    #[must_use]
    pub fn value_of(
        &self,
        variable: LevelVar,
    ) -> Option<ConsistencyValue>
    {
        self.values.get(&variable).copied()
    }

    /// The assignments in ascending variable order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields each declared variable exactly once with its
    ///   homomorphism value, in ascending variable order.
    /// - provides: the whole-certificate read the consistency validator walks.
    /// - panics: none.
    /// - executable: none — the opaque iterator cannot be named by the
    ///   postcondition expansion or consumed without changing its output.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty certificate and a reverse-inserted
    ///   two-variable certificate are enumerated exactly, distinguishing
    ///   omission, duplicate entries, wrong values and changed ordering.
    /// - witness: `poset::tests::reflection_and_assignment_boundaries`
    #[inline]
    pub fn assignments(&self) -> impl Iterator<Item = (LevelVar, ConsistencyValue)> + '_
    {
        self.values
            .iter()
            .map(|(&variable, &value)| (variable, value))
    }
}

/// The negative admission evidence.
///
/// A nonempty variable set `W` and shift `n` such that the derivation replays,
/// from exactly the atoms `{w+n | w ∈ W}`, to cover every `w+n+1` — a pumping
/// certificate, so `∨_{w∈W} w+n` is a loop and no homomorphism into `ℕ` exists.
///
/// # Specification
/// - ensures: an oracle-produced nonempty member set has a replayable positive
///   pumping derivation.
/// - executable: none — the clause system needed for pumping validity is
///   external to the witness.
///
/// # Adequacy
/// - hypothesis: L2 — total and partial loops replay against their constraints.
///   L3 forges empty members, unknown clauses, unavailable bodies and uncovered
///   targets; typed refusals distinguish malformed evidence from a pumping
///   proof.
/// - witness: `poset::tests::paper_loop_variant_returns_a_validating_loop_witness`
/// - witness: `poset::tests::partial_loop_pins_the_shift_choice`
/// - witness: `poset::tests::perturbed_loop_witness_arms_are_rejected`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoopWitness
{
    /// The looping variable set `W`.
    members: BTreeSet<LevelVar>,
    /// The shift `n` at which the pumping is exhibited.
    shift: HornShift,
    /// The replayable pumping derivation.
    derivation: Derivation,
}

impl LoopWitness
{
    /// The looping variable set `W`, in ascending order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn members(&self) -> &BTreeSet<LevelVar>
    {
        &self.members
    }

    /// The shift `n` at which the pumping is exhibited.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn shift(&self) -> HornShift
    {
        self.shift
    }

    /// The replayable pumping derivation.
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

/// Rejection vocabulary of the poset and entailment evidence validators:
/// exactly why a piece of evidence fails to check.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PosetEvidenceError
{
    /// A loop witness with an empty member set.
    EmptyLoop,
    /// A derivation step names a clause index outside the compiled system.
    UnknownClause
    {
        /// The offending step's clause index.
        clause: ClauseIndex,
    },
    /// A derivation step fires below the system's minimum shift.
    ShiftBelowMinimum
    {
        /// The offending step's clause index.
        clause: ClauseIndex,
    },
    /// A derivation step's body is not available at its shift.
    BodyUnavailable
    {
        /// The offending step's clause index.
        clause: ClauseIndex,
    },
    /// A required target atom is not covered after replay.
    TargetUncovered
    {
        /// The uncovered target's subject.
        subject: EvidenceSubject,
    },
    /// A consistency witness misses a declared variable.
    MissingAssignment
    {
        /// The unassigned variable.
        variable: LevelVar,
    },
    /// A declared constraint fails under the consistency witness.
    ConstraintViolated
    {
        /// The failing constraint's declaration index.
        index: ConstraintIndex,
    },
    /// A countermodel misses an in-scope variable.
    MissingValue
    {
        /// The unassigned variable.
        variable: LevelVar,
    },
    /// A countermodel fails to cover a query seed atom.
    SeedUnsatisfied
    {
        /// The uncovered seed's subject.
        subject: EvidenceSubject,
    },
    /// A countermodel violates a clause of the query system.
    ClauseUnsatisfied
    {
        /// The violated clause's index.
        clause: ClauseIndex,
    },
    /// The recorded refuted goal is not a goal of the claim, or the
    /// countermodel does not refute it.
    NotRefuting,
    /// Evaluating the adversarial evidence overflowed; the evidence is rejected
    /// rather than wrapped.
    Overflow,
}

impl fmt::Display for PosetEvidenceError
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
            | Self::EmptyLoop => f.write_str("the loop witness has no members"),
            | Self::UnknownClause { clause } => {
                write!(f, "step names clause {clause} outside the compiled system")
            },
            | Self::ShiftBelowMinimum { clause } => {
                write!(f, "step on clause {clause} fires below the minimum shift")
            },
            | Self::BodyUnavailable { clause } => {
                write!(f, "step on clause {clause} fires without its body")
            },
            | Self::TargetUncovered { subject } => {
                write!(f, "the target over {subject} is not covered")
            },
            | Self::MissingAssignment { variable } => write!(
                f,
                "the witness assigns no value to variable {}",
                variable.index()
            ),
            | Self::ConstraintViolated { index } => {
                write!(f, "declared constraint {index} fails under the witness")
            },
            | Self::MissingValue { variable } => write!(
                f,
                "the countermodel assigns no value to variable {}",
                variable.index()
            ),
            | Self::SeedUnsatisfied { subject } => {
                write!(f, "the countermodel misses the seed over {subject}")
            },
            | Self::ClauseUnsatisfied { clause } => {
                write!(f, "the countermodel violates clause {clause}")
            },
            | Self::NotRefuting => f.write_str("the recorded goal is not refuted"),
            | Self::Overflow => f.write_str("evaluating the evidence overflowed"),
        }
    }
}

impl Error for PosetEvidenceError
{
}

/// The loop-checking dichotomy as data: a declared constraint set either
/// admits, carrying its consistency certificate inside the poset, or loops,
/// carrying the pumping witness. Exactly one case holds.
#[derive(Clone, Debug)]
pub enum AdmissionOutcome
{
    /// The constraints admit; the poset carries its consistency witness.
    Admitted(LandmarkPoset),
    /// The constraints loop; no homomorphism into `ℕ` exists.
    Loop(LoopWitness),
}

/// An admitted landmark poset.
///
/// It carries the declared constraints, their compiled clause system — fixed at
/// admission and reused by every query — and the consistency certificate
/// admission produced.
///
/// # Specification
/// - ensures: the retained consistency certificate satisfies the admitted
///   constraints and the compiled clauses preserve their declaration order.
/// - executable: none — data-item predicates do not run at construction;
///   admission and the independent validators check this invariant.
///
/// # Adequacy
/// - hypothesis: L2 — the finite paper model validates independently, while
///   total and partial loops are refused. L3 — an empty declaration admits with
///   an empty certificate, separating vacuous admission from spurious refusal.
/// - witness: `poset::tests::paper_example_admits_with_a_validating_homomorphism`
/// - witness: `poset::tests::paper_loop_variant_returns_a_validating_loop_witness`
/// - witness: `poset::tests::partial_loop_pins_the_shift_choice`
/// - witness: `poset::tests::empty_constraint_set_admits_with_an_empty_certificate`
#[derive(Clone, Debug)]
pub struct LandmarkPoset
{
    /// The declared constraints, in declaration order.
    constraints: Vec<LandmarkConstraint>,
    /// The declared variables, ascending.
    variables: BTreeSet<LevelVar>,
    /// The compiled base clauses, in the documented deterministic order.
    clauses: Vec<HornClause>,
    /// The consistency certificate.
    consistency: ConsistencyWitness,
}

impl LandmarkPoset
{
    /// Admits a declared constraint set by loop-checking, returning the
    /// dichotomy as evidence-carrying data.
    ///
    /// # Specification
    /// - requires: nothing beyond well-formed constraints, guaranteed by
    ///   construction.
    /// - ensures: [`AdmissionOutcome::Admitted`] with a poset whose
    ///   [`ConsistencyWitness`] passes [`validate_consistency`] exactly when
    ///   the constraints have no loop; [`AdmissionOutcome::Loop`] with a
    ///   witness passing [`validate_loop_witness`] otherwise.
    /// - provides: the kernel's landmark-poset admission choke point. The empty
    ///   set admits with an empty certificate, and queries under it agree
    ///   exactly with the free order oracle. The predicate checks the retained
    ///   consistency certificate and nonempty pumping evidence; loop replay
    ///   additionally needs the consumed constraints and is witnessed below.
    /// - fails: [`PosetError::Overflow`] on arithmetic past the representable
    ///   range; [`PosetError::EvidenceIncomplete`] if loop evidence extraction
    ///   misses its round limit, which the theory excludes and which is
    ///   surfaced rather than trusted.
    /// - panics: none.
    /// - intension: the seed is the maximal body offset over the declared
    ///   variables, the small-model snap bound is that offset plus the variable
    ///   count times the maximum gain, and the loop shift is the seed when
    ///   every variable loops and the largest finite value plus the maximum
    ///   gain otherwise — the constructions of the loop-checking paper
    ///   verbatim.
    ///
    /// # Errors
    /// [`PosetError::Overflow`] and [`PosetError::EvidenceIncomplete`], the
    /// latter excluded by the theory.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the worked example of the loop-checking paper pins
    ///   both dichotomy arms end to end, with an exact certificate on admission
    ///   and an exact member set and shift on refusal, and every produced
    ///   witness must pass its independent validator, so a deciding mutant must
    ///   also forge coherent evidence; the L3 residue is the shift choice when
    ///   the loop covers every variable against when it covers some, pinned by
    ///   the two loop goldens. The two theory-excluded error arms have no
    ///   witness by construction: no input reaches them, and manufacturing one
    ///   would mean corrupting admission itself.
    /// - witness: `poset::tests::paper_example_admits_with_a_validating_homomorphism`
    /// - witness: `poset::tests::paper_loop_variant_returns_a_validating_loop_witness`
    /// - witness: `poset::tests::partial_loop_pins_the_shift_choice`
    /// - witness: `poset::tests::self_successor_equality_loops`
    /// - witness: `poset::tests::empty_constraint_set_admits_with_an_empty_certificate`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|outcome| match *outcome {
        AdmissionOutcome::Admitted(ref poset) =>
            validate_consistency(poset.constraints(), poset.consistency()).is_ok(),
        AdmissionOutcome::Loop(ref witness) =>
            !witness.members().is_empty() && !witness.derivation().steps().is_empty(),
    }))]
    #[inline]
    pub fn admit(constraints: Vec<LandmarkConstraint>) -> Result<AdmissionOutcome, PosetError>
    {
        let variables: BTreeSet<LevelVar> = constraints
            .iter()
            .flat_map(LandmarkConstraint::variables)
            .collect();
        let clauses = compile(&constraints);
        let system = ClauseSystem {
            clauses,
            min_shift: HornShift::ZERO,
        };
        let maxgain = system.maxgain();
        let seed_value = system.max_body_offset();
        let variable_count =
            u128::try_from(variables.len()).map_err(|_error| PosetError::Overflow)?;
        let headroom = variable_count
            .checked_mul(u128::from(maxgain))
            .ok_or(PosetError::Overflow)?;
        let snap_bound = u128::from(seed_value)
            .checked_add(headroom)
            .map(SaturationBound::from)
            .ok_or(PosetError::Overflow)?;
        let seed: BTreeMap<HVar, ModelValue> = variables
            .iter()
            .map(|&variable| (HVar::Var(variable), ModelValue::Finite(seed_value)))
            .collect();
        let outcome =
            horn::saturate(&system, seed, snap_bound).map_err(|_error| PosetError::Overflow)?;
        let members: BTreeSet<LevelVar> = variables
            .iter()
            .copied()
            .filter(|&variable| {
                outcome
                    .values
                    .get(&HVar::Var(variable))
                    .copied()
                    .is_some_and(|value| bool::from(value.is_infinite()))
            })
            .collect();
        if members.is_empty() {
            let consistency = consistency_certificate(&variables, &outcome.values)?;
            let poset = Self {
                constraints,
                variables,
                clauses: system.clauses,
                consistency,
            };
            return Ok(AdmissionOutcome::Admitted(poset));
        }
        let shift = if members.len() == variables.len() {
            seed_value.shift_from_zero()
        }
        else {
            let finite_ceiling = finite_ceiling(&outcome.values);
            let finite_shift = u128::from(finite_ceiling)
                .checked_add(u128::from(maxgain))
                .ok_or(PosetError::Overflow)?;
            HornOffset::from(finite_shift).shift_from_zero()
        };
        let witness = extract_loop_witness(&system, &members, shift, maxgain)?;
        Ok(AdmissionOutcome::Loop(witness))
    }

    /// The declared constraints, in declaration order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn constraints(&self) -> &[LandmarkConstraint]
    {
        &self.constraints
    }

    /// The declared variables, in ascending order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn variables(&self) -> &BTreeSet<LevelVar>
    {
        &self.variables
    }

    /// The consistency certificate admission produced.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn consistency(&self) -> &ConsistencyWitness
    {
        &self.consistency
    }

    /// Crate-internal access to the compiled clause list.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn compiled_clauses(&self) -> &[HornClause]
    {
        &self.clauses
    }
}

/// The largest finite value in a saturated model, or zero when every value is
/// infinite.
///
/// # Specification
/// - requires: `values` is a saturated model, whose values are finite or
///   infinite.
/// - ensures: returns the largest finite value present, and zero when the model
///   holds no finite value at all.
/// - provides: the finite base the loop shift is measured from.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, all-infinite and mixed models with unequal finite
///   values distinguish a missing zero identity, treating infinity as finite
///   and selecting the minimum through exact ceiling values.
/// - witness: `poset::tests::reflection_and_assignment_boundaries`
#[spec(ensures: |ret| ret == values.values().filter_map(|value| value.as_finite())
    .max().unwrap_or(HornOffset::ZERO))]
fn finite_ceiling(values: &BTreeMap<HVar, ModelValue>) -> HornOffset
{
    values
        .values()
        .filter_map(|value| value.as_finite())
        .max()
        .unwrap_or(HornOffset::ZERO)
}

/// Turns a converged least model into the admission certificate by reflecting
/// it: a variable the model raises higher must be assigned lower, since the
/// clauses read `right → left`.
///
/// # Specification
/// - requires: `values` is the converged model over `variables` with no
///   infinite component, which is exactly the admitting branch's state.
/// - ensures: every variable is assigned the ceiling minus its model value, a
///   non-negative homomorphism under which every declared constraint holds.
/// - provides: the positive half of the admission dichotomy. Convergence and
///   the homomorphism consequence use the originating clause system, which this
///   interface does not carry; the predicate checks the stated reflection on
///   successful returns.
/// - fails: [`PosetError::Overflow`] when the reflection underflows, which the
///   ceiling's definition excludes.
/// - panics: none.
///
/// # Errors
/// [`PosetError::Overflow`] if a reflected value exceeds its ceiling.
///
/// # Adequacy
/// - hypothesis: L3 — empty variables and unequal finite model values expose
///   wrong reflection direction, missing assignments and a nonzero empty
///   identity through exact ordered assignments. The paper example validates
///   the resulting homomorphism against its constraints.
/// - witness: `poset::tests::reflection_and_assignment_boundaries`
/// - witness: `poset::tests::paper_example_admits_with_a_validating_homomorphism`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|witness| {
    let ceiling = u128::from(finite_ceiling(values));
    witness.values.len() == variables.len()
        && variables.iter().all(|variable| {
            let value = values.get(&HVar::Var(*variable)).copied()
                .and_then(ModelValue::as_finite).unwrap_or(HornOffset::ZERO);
            ceiling.checked_sub(u128::from(value))
                == witness.values.get(variable).copied().map(u128::from)
        })
}))]
fn consistency_certificate(
    variables: &BTreeSet<LevelVar>,
    values: &BTreeMap<HVar, ModelValue>,
) -> Result<ConsistencyWitness, PosetError>
{
    let ceiling = finite_ceiling(values);
    let mut assigned = BTreeMap::new();
    for &variable in variables {
        let level = values
            .get(&HVar::Var(variable))
            .copied()
            .and_then(ModelValue::as_finite)
            .unwrap_or(HornOffset::ZERO);
        let value = u128::from(ceiling)
            .checked_sub(u128::from(level))
            .ok_or(PosetError::Overflow)?;
        let _previous = assigned.insert(variable, ConsistencyValue::from(value));
    }
    Ok(ConsistencyWitness { values: assigned })
}

/// Extracts the replayable pumping derivation behind a loop refusal: from the
/// atoms `{w+shift | w ∈ members}` over the clauses that stay inside `members`,
/// derive every `w+shift+1`.
///
/// # Specification
/// - requires: `members` is the nonempty infinite-component set of the
///   saturated model and `shift` the corresponding pumping shift.
/// - ensures: a loop witness whose derivation replays through
///   [`validate_loop_witness`], with step clause indices remapped back into the
///   full compiled system.
/// - provides: the negative half of the admission dichotomy. The input's
///   saturation provenance stays prose: the saturated model is not an argument.
///   The postcondition replays against the full clause list, so remapped
///   indices are checked in their destination system.
/// - fails: [`PosetError::Overflow`] on arithmetic past the representable
///   range; [`PosetError::EvidenceIncomplete`] when extraction exceeds its
///   round limit, which the theory excludes.
/// - panics: none.
/// - intension: the round limit is the gain budget times the traversal length,
///   both computed from the member and clause counts, so extraction terminates
///   on a counter rather than on a semantic condition.
///
/// # Errors
/// [`PosetError::Overflow`] or [`PosetError::EvidenceIncomplete`].
///
/// # Adequacy
/// - hypothesis: L2 — total and partial loops replay their pumping derivations
///   in the full compiled system; exact member sets and shifts distinguish bad
///   subset selection, remapped indices and a wrong shift choice.
/// - witness: `poset::tests::paper_loop_variant_returns_a_validating_loop_witness`
/// - witness: `poset::tests::partial_loop_pins_the_shift_choice`
/// - witness: `poset::tests::self_successor_equality_loops`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|witness| {
    let seed = members.iter().map(|variable| {
        (HVar::Var(*variable), shift.offset_from_zero())
    }).collect();
    let replay = replay_derivation(&system.clauses, HornShift::ZERO, seed, witness.derivation());
    witness.members() == members && witness.shift() == shift && !members.is_empty()
        && replay.is_ok_and(|maxima| {
            u128::from(shift).checked_add(1).is_some_and(|target| {
                members.iter().all(|variable| maxima.get(&HVar::Var(*variable))
                    .is_some_and(|maximum| target <= u128::from(*maximum)))
            })
        })
}))]
fn extract_loop_witness(
    system: &ClauseSystem,
    members: &BTreeSet<LevelVar>,
    shift: HornShift,
    maxgain: MaxGain,
) -> Result<LoopWitness, PosetError>
{
    let inside = |variable: HVar| match variable {
        | HVar::Var(level_var) => members.contains(&level_var),
        | HVar::Bottom => false,
    };
    let mut filtered = Vec::new();
    let mut indices = Vec::new();
    for (index, clause) in system.clauses.iter().enumerate() {
        let head_inside = inside(clause.head().variable());
        let body_inside = clause.body().iter().all(|atom| inside(atom.variable()));
        if head_inside && body_inside {
            filtered.push(clause.clone());
            indices.push(index);
        }
    }
    let member_count = u128::try_from(members.len()).map_err(|_error| PosetError::Overflow)?;
    let clause_count = u128::try_from(filtered.len()).map_err(|_error| PosetError::Overflow)?;
    // A generous syntactic round limit: pumping raises every member within one
    // clause-graph traversal per unit of gain deficit, so the product of the
    // total gain budget and the traversal length bounds the rounds with
    // headroom. Exceeding it is theory-refuting and surfaces as
    // `EvidenceIncomplete` rather than being trusted or looping forever.
    let gain_budget = member_count
        .checked_mul(u128::from(maxgain))
        .and_then(|product| product.checked_add(2_u128))
        .ok_or(PosetError::Overflow)?;
    let traversal = clause_count
        .checked_add(member_count)
        .and_then(|sum| sum.checked_add(2_u128))
        .ok_or(PosetError::Overflow)?;
    let round_limit = gain_budget
        .checked_mul(traversal)
        .ok_or(PosetError::Overflow)?;
    let filtered_system = ClauseSystem {
        clauses: filtered,
        min_shift: HornShift::ZERO,
    };
    let seed: BTreeMap<HVar, ModelValue> = members
        .iter()
        .map(|&variable| {
            (
                HVar::Var(variable),
                ModelValue::Finite(shift.offset_from_zero()),
            )
        })
        .collect();
    let target_offset = shift
        .offset_from_zero()
        .checked_add(HornOffset::ONE)
        .map_err(|_error| PosetError::Overflow)?;
    let targets: Vec<HornAtom> = members
        .iter()
        .map(|&variable| HornAtom::new(HVar::Var(variable), target_offset))
        .collect();
    let log = horn::derive_targets(
        &filtered_system,
        seed,
        &targets,
        DerivationRoundLimit::from(round_limit),
    )
    .map_err(|_error| PosetError::Overflow)?;
    let log = log.ok_or(PosetError::EvidenceIncomplete)?;
    let remapped: Vec<FiringLogStep> = log
        .into_iter()
        .filter_map(|step| {
            indices.get(usize::from(step.clause())).map(|&original| {
                FiringLogStep::new(ClauseIndex::from(original), step.shift(), step.concluded())
            })
        })
        .collect();
    Ok(LoopWitness {
        members: members.clone(),
        shift,
        derivation: Derivation::from_log(&remapped),
    })
}

/// Checks a loop witness against its declared constraints by replaying its
/// pumping derivation.
///
/// # Specification
/// - requires: `witness` claims the constraints loop, and `constraints` is the
///   declared list. The clause compilation is definitional, so validator and
///   oracle share it: the check, not the encoding, is the trusted step.
/// - ensures: `Ok(())` exactly when the member set is nonempty and the
///   derivation replays from exactly `{w + shift | w ∈ members}` to cover every
///   `w + shift + 1`, which exhibits the join of the shifted members as a loop,
///   so no homomorphism into `ℕ` can exist.
/// - provides: the trusted half of the refusal evidence.
/// - fails: the first [`PosetEvidenceError`] encountered — replay errors in
///   step order, then uncovered targets in ascending variable order.
/// - panics: none.
///
/// # Errors
/// [`PosetEvidenceError::EmptyLoop`], the replay errors, and
/// [`PosetEvidenceError::TargetUncovered`].
///
/// # Adequacy
/// - hypothesis: L3 — rejection arms pinned by hand-perturbed witnesses
///   asserting the exact variant, acceptance pinned by the loop goldens.
/// - witness: `poset::tests::perturbed_loop_witness_arms_are_rejected`
/// - witness: `poset::tests::paper_loop_variant_returns_a_validating_loop_witness`
#[spec(ensures: |ret| ret.is_ok() == {
    let seed = witness.members().iter().map(|variable| {
        (HVar::Var(*variable), witness.shift().offset_from_zero())
    }).collect();
    !witness.members().is_empty()
        && replay_derivation(&compile(constraints), HornShift::ZERO, seed, witness.derivation())
            .is_ok_and(|maxima| {
                u128::from(witness.shift()).checked_add(1).is_some_and(|target| {
                    witness.members().iter().all(|variable| maxima.get(&HVar::Var(*variable))
                        .is_some_and(|maximum| target <= u128::from(*maximum)))
                })
            })
})]
#[inline]
pub fn validate_loop_witness(
    constraints: &[LandmarkConstraint],
    witness: &LoopWitness,
) -> Result<(), PosetEvidenceError>
{
    if witness.members().is_empty() {
        return Err(PosetEvidenceError::EmptyLoop);
    }
    let clauses = compile(constraints);
    let seed: BTreeMap<HVar, HornOffset> = witness
        .members()
        .iter()
        .map(|&variable| (HVar::Var(variable), witness.shift().offset_from_zero()))
        .collect();
    let maxima = replay_derivation(&clauses, HornShift::ZERO, seed, witness.derivation())?;
    let target = witness
        .shift()
        .offset_from_zero()
        .checked_add(HornOffset::ONE)
        .map_err(|_error| PosetEvidenceError::Overflow)?;
    for &variable in witness.members() {
        let covered = maxima
            .get(&HVar::Var(variable))
            .is_some_and(|&maximum| target <= maximum);
        if !covered {
            return Err(PosetEvidenceError::TargetUncovered {
                subject: EvidenceSubject::Variable(variable),
            });
        }
    }
    Ok(())
}

/// Compiles a declared constraint list into its base clauses, following the
/// deterministic enumeration this module's docs record.
///
/// # Specification
/// - requires: well-formed constraints, so every side carries at least one
///   atom.
/// - ensures: the clause list in declaration order, with self-subsumed clauses
///   omitted.
/// - provides: the shared encoding of the oracle and the validators, which is
///   what makes clause indices in evidence meaningful.
/// - fails: never; a constraint side with no atoms would contribute no clause,
///   and the constraint constructor excludes that side.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — inequality, equality and a self-subsumed component are
///   compiled together. Exact clause order, directions and atom offsets expose
///   missing equality orientation, reversed implication and failed omission.
/// - witness: `poset::tests::compilation_preserves_direction_order_and_subsumption`
// The precondition is the variable-only guard `LandmarkConstraint::new`
// establishes, re-read here at the one point that depends on it. The scan is
// linear in the constraint list, which the compilation below already walks.
#[spec(requires: constraints.iter().all(|constraint| {
    constraint.left().atoms().next().is_some() && constraint.right().atoms().next().is_some()
}))]
fn compile(constraints: &[LandmarkConstraint]) -> Vec<HornClause>
{
    let mut clauses = Vec::new();
    for constraint in constraints {
        let left_atoms = level_atoms(constraint.left());
        let right_atoms = level_atoms(constraint.right());
        match constraint.relation() {
            | ConstraintRelation::Leq => {
                push_family(&mut clauses, &right_atoms, &left_atoms);
            },
            | ConstraintRelation::Eq => {
                push_family(&mut clauses, &left_atoms, &right_atoms);
                push_family(&mut clauses, &right_atoms, &left_atoms);
            },
        }
    }
    clauses
}

/// A variable-only level's atoms as Horn atoms, ascending.
///
/// # Specification
/// - requires: `level` is variable-only, which the constraint constructor's
///   guard establishes at every call site.
/// - ensures: returns one Horn atom per level atom, over the same variable and
///   offset, in ascending variable order.
/// - provides: the atom-level half of the documented compilation.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — multiple variables with unequal offsets occur in an
///   inequality and an equality; the exact compiled bodies and heads expose
///   changed variables, offsets or ordering in the level-to-Horn translation.
/// - witness: `poset::tests::compilation_preserves_direction_order_and_subsumption`
#[spec(ensures: |ret| ret.iter().map(|atom| (atom.variable(), atom.offset()))
    .eq(level.atoms().map(|(variable, offset)| (HVar::Var(variable), HornOffset::from(offset)))))]
fn level_atoms(level: &Level) -> Vec<HornAtom>
{
    level
        .atoms()
        .map(|(variable, offset)| HornAtom::new(HVar::Var(variable), HornOffset::from(offset)))
        .collect()
}

/// Appends the clause family `body → head` for each head atom, omitting
/// self-subsumed clauses.
///
/// # Specification
/// - requires: `body` is nonempty, which the constraint constructor's
///   variable-only guard establishes at every call site.
/// - ensures: one clause per head atom that is not self-subsumed, appended in
///   the head atoms' ascending order.
/// - provides: the inner loop of the documented compilation.
/// - fails: never; an empty body contributes nothing, which the caller-side
///   invariant excludes.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — compilation appends families to an existing prefix and
///   omits a head already covered by its body. Exact emitted clauses expose
///   prefix replacement, reversed head order and retention of a trivial clause.
/// - witness: `poset::tests::compilation_preserves_direction_order_and_subsumption`
#[spec(requires: !body.is_empty())]
fn push_family(
    clauses: &mut Vec<HornClause>,
    body: &[HornAtom],
    heads: &[HornAtom],
)
{
    for &head in heads {
        if let Some(clause) = HornClause::new(body, head)
            && !bool::from(clause.is_trivial())
        {
            clauses.push(clause);
        }
    }
}

/// Replays a derivation over a compiled clause list from seeded atom
/// availability, returning the per-variable maxima it reaches.
///
/// # Specification
/// - requires: `seed` maps each initially available variable to its maximal
///   seeded offset; absent variables have no atoms.
/// - ensures: `Ok(maxima)` exactly when every step names a known clause, fires
///   at or above `min_shift`, and finds its whole shifted body available at
///   application time; the maxima then bound exactly the atoms the derivation
///   establishes.
/// - provides: the shared replay engine of [`validate_loop_witness`] and the
///   entailment witness validator. The predicate checks known clauses, minimum
///   shifts and retention of every conclusion; step-time availability also
///   depends on the consumed seed and is witnessed by adversarial replay.
/// - fails: the first [`PosetEvidenceError`] encountered, in step order;
///   adversarial arithmetic overflow is rejected as
///   [`PosetEvidenceError::Overflow`] rather than wrapped.
/// - panics: none.
/// - intension: steps are consumed in a single forward pass over an explicit
///   iterator, never recursively, so replay cost is linear in the derivation
///   length.
///
/// # Errors
/// [`PosetEvidenceError::UnknownClause`],
/// [`PosetEvidenceError::ShiftBelowMinimum`],
/// [`PosetEvidenceError::BodyUnavailable`], and
/// [`PosetEvidenceError::Overflow`].
///
/// # Adequacy
/// - hypothesis: L3 — each rejection arm is pinned by a hand-perturbed
///   derivation asserting the exact variant, and acceptance is pinned by the
///   property that every oracle-produced derivation replays.
/// - witness: `poset::tests::replay_distinguishes_body_and_head_overflow`
/// - witness: `poset::tests::perturbed_loop_witness_arms_are_rejected`
/// - witness: `entail::tests::perturbed_witness_arms_are_rejected`
/// - witness: `entailment_oracle::entailment_oracle::prop_fixed_poset_evidence_validates`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|maxima|
    derivation.steps().iter().all(|step| step.shift() >= min_shift &&
        clauses.get(usize::from(step.clause())).is_some_and(|clause|
            u128::from(clause.head().offset()).checked_add(u128::from(step.shift()))
                .is_some_and(|concluded| maxima.get(&clause.head().variable())
                    .is_some_and(|maximum| concluded <= u128::from(*maximum)))))))]
pub fn replay_derivation(
    clauses: &[HornClause],
    min_shift: HornShift,
    seed: BTreeMap<HVar, HornOffset>,
    derivation: &Derivation,
) -> Result<BTreeMap<HVar, HornOffset>, PosetEvidenceError>
{
    let mut maxima = seed;
    for step in derivation.steps() {
        let Some(clause) = clauses.get(usize::from(step.clause()))
        else {
            return Err(PosetEvidenceError::UnknownClause {
                clause: step.clause(),
            });
        };
        if step.shift() < min_shift {
            return Err(PosetEvidenceError::ShiftBelowMinimum {
                clause: step.clause(),
            });
        }
        for &atom in clause.body() {
            let needed = atom
                .offset()
                .checked_add_shift(step.shift())
                .map_err(|_error| PosetEvidenceError::Overflow)?;
            let available = maxima
                .get(&atom.variable())
                .is_some_and(|&maximum| needed <= maximum);
            if !available {
                return Err(PosetEvidenceError::BodyUnavailable {
                    clause: step.clause(),
                });
            }
        }
        let head = clause.head();
        let concluded = head
            .offset()
            .checked_add_shift(step.shift())
            .map_err(|_error| PosetEvidenceError::Overflow)?;
        let maximum = maxima.entry(head.variable()).or_insert(concluded);
        *maximum = (*maximum).max(concluded);
    }
    Ok(maxima)
}

/// Checks a consistency witness against its declared constraints by direct
/// evaluation into `ℕ`.
///
/// # Specification
/// - requires: `witness` claims the constraints admit, and `constraints` is the
///   declared list; order matters only for error indices.
/// - ensures: `Ok(())` exactly when the witness assigns every mentioned
///   variable and every constraint holds under the assignment, evaluating a
///   side as `max(h(x) + offset, …)` — the homomorphism reading.
/// - provides: the trusted half of the admission evidence, a validator
///   independent of the whole Horn machinery since it only evaluates, against
///   which the decision procedure is self-incriminating.
/// - fails: the first [`PosetEvidenceError`] encountered, walking constraints
///   in declaration order.
/// - panics: none.
///
/// # Errors
/// [`PosetEvidenceError::MissingAssignment`],
/// [`PosetEvidenceError::ConstraintViolated`], and
/// [`PosetEvidenceError::Overflow`].
///
/// # Adequacy
/// - hypothesis: L3 — each rejection arm pinned by a hand-perturbed witness
///   asserting the exact variant, acceptance pinned by the property that every
///   admission certificate validates and by the worked example's exact
///   certificate.
/// - witness: `poset::tests::perturbed_consistency_witness_is_rejected`
/// - witness: `poset::tests::paper_example_admits_with_a_validating_homomorphism`
/// - witness: `poset::tests::equality_constraints_validate_under_the_certificate`
#[spec(ensures: |ret| ret.is_ok() == constraints.iter().all(|constraint| {
    match (evaluate_side(constraint.left(), witness), evaluate_side(constraint.right(), witness)) {
        (Ok(left), Ok(right)) => match constraint.relation() {
            ConstraintRelation::Leq => left <= right,
            ConstraintRelation::Eq => left == right,
        },
        _ => false,
    }
}))]
#[inline]
pub fn validate_consistency(
    constraints: &[LandmarkConstraint],
    witness: &ConsistencyWitness,
) -> Result<(), PosetEvidenceError>
{
    for (index, constraint) in constraints.iter().enumerate() {
        let left = evaluate_side(constraint.left(), witness)?;
        let right = evaluate_side(constraint.right(), witness)?;
        let holds = match constraint.relation() {
            | ConstraintRelation::Leq => left <= right,
            | ConstraintRelation::Eq => left == right,
        };
        if !holds {
            return Err(PosetEvidenceError::ConstraintViolated {
                index: ConstraintIndex::from(index),
            });
        }
    }
    Ok(())
}

/// Evaluates a variable-only side under a consistency witness.
///
/// # Specification
/// - requires: `side` is a canonical level; a nonzero constant part is
///   admissible input and contributes as the join's floor.
/// - ensures: `Ok(value)` is the join of the constant part and each assigned
///   variable value plus its offset.
/// - provides: the homomorphism reading the consistency validator checks
///   against.
/// - fails: [`PosetEvidenceError::MissingAssignment`] when a mentioned variable
///   is unassigned; [`PosetEvidenceError::Overflow`] when a component sum
///   leaves the `u128` range.
/// - panics: none.
///
/// # Errors
/// [`PosetEvidenceError::MissingAssignment`] or
/// [`PosetEvidenceError::Overflow`].
///
/// # Adequacy
/// - hypothesis: L3 — a constant floor, unequal assigned atom components, a
///   missing variable, the exact u128 ceiling and one overflowing successor
///   distinguish an omitted component, default assignment and unchecked
///   addition by exact values and typed refusals.
/// - witness: `poset::tests::side_evaluation_distinguishes_missing_values_and_overflow`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|value| {
    side.atoms().try_fold(u128::from(side.constant_part()), |maximum, (variable, offset)| {
        let base = witness.value_of(variable)?;
        u128::from(base).checked_add(u128::from(offset)).map(|component| maximum.max(component))
    }) == Some(u128::from(*value))
}))]
fn evaluate_side(
    side: &Level,
    witness: &ConsistencyWitness,
) -> Result<ConsistencyValue, PosetEvidenceError>
{
    let mut value = u128::from(side.constant_part());
    for (variable, offset) in side.atoms() {
        let base = witness
            .value_of(variable)
            .ok_or(PosetEvidenceError::MissingAssignment { variable })?;
        let component = u128::from(base)
            .checked_add(u128::from(offset))
            .ok_or(PosetEvidenceError::Overflow)?;
        value = value.max(component);
    }
    Ok(ConsistencyValue::from(value))
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::collections::BTreeSet;
    use alloc::vec;
    use alloc::vec::Vec;

    use super::AdmissionOutcome;
    use super::ConsistencyValue;
    use super::ConsistencyWitness;
    use super::ConstraintIndex;
    use super::Derivation;
    use super::DerivationStep;
    use super::EvidenceSubject;
    use super::LandmarkConstraint;
    use super::LandmarkPoset;
    use super::LoopWitness;
    use super::PosetError;
    use super::PosetEvidenceError;
    use super::validate_consistency;
    use super::validate_loop_witness;
    use crate::horn::ClauseIndex;
    use crate::horn::HVar;
    use crate::horn::HornAtom;
    use crate::horn::HornClause;
    use crate::horn::HornOffset;
    use crate::horn::HornShift;
    use crate::horn::ModelValue;
    use crate::level::Level;
    use crate::level::LevelConstant;
    use crate::level::LevelOffset;
    use crate::level::LevelVar;
    use crate::level::LevelVarIndex;

    #[test]
    fn constraint_guards_both_sides_and_preserves_variable_order()
    {
        let valid = Level::var(x());
        for invalid in [
            Level::zero(),
            Level::constant(LevelConstant::from(2_u64)),
            Level::constant(LevelConstant::from(2_u64)).max(&Level::var(y())),
        ] {
            for (left, right) in [(invalid.clone(), valid.clone()), (valid.clone(), invalid)] {
                assert_eq!(
                    LandmarkConstraint::leq(left.clone(), right.clone()),
                    Err(PosetError::ConstantInConstraint)
                );
                assert_eq!(
                    LandmarkConstraint::equal(left, right),
                    Err(PosetError::ConstantInConstraint)
                );
            }
        }
        let left = var_plus(y(), LevelOffset::from(1_u64)).max(&Level::var(x()));
        let right = Level::var(var2()).max(&var_plus(x(), LevelOffset::from(2_u64)));
        for constraint in [
            LandmarkConstraint::leq(left.clone(), right.clone()),
            LandmarkConstraint::equal(left, right),
        ] {
            assert_eq!(
                constraint
                    .expect("variable-only sides")
                    .variables()
                    .collect::<Vec<_>>(),
                [x(), y(), x(), var2()]
            );
        }
        let dominated = Level::constant(LevelConstant::from(2_u64))
            .max(&var_plus(x(), LevelOffset::from(2_u64)));
        assert_eq!(
            LandmarkConstraint::equal(dominated, valid)
                .expect("dominated constant")
                .relation(),
            super::ConstraintRelation::Eq
        );
    }

    #[test]
    fn reflection_and_assignment_boundaries()
    {
        let empty = BTreeMap::new();
        assert_eq!(super::finite_ceiling(&empty), HornOffset::ZERO);
        let certificate =
            super::consistency_certificate(&BTreeSet::new(), &empty).expect("empty model");
        assert_eq!(certificate.assignments().next(), None);
        assert_eq!(certificate.value_of(x()), None);
        let infinite = BTreeMap::from([(HVar::Var(x()), ModelValue::Infinite)]);
        assert_eq!(super::finite_ceiling(&infinite), HornOffset::ZERO);
        let mixed = BTreeMap::from([
            (HVar::Var(y()), ModelValue::Finite(HornOffset::from(7_u128))),
            (HVar::Var(x()), ModelValue::Finite(HornOffset::from(2_u128))),
            (HVar::Var(var2()), ModelValue::Infinite),
        ]);
        assert_eq!(super::finite_ceiling(&mixed), HornOffset::from(7_u128));
        let finite = BTreeMap::from([
            (HVar::Var(y()), ModelValue::Finite(HornOffset::from(7_u128))),
            (HVar::Var(x()), ModelValue::Finite(HornOffset::from(2_u128))),
        ]);
        let certificate = super::consistency_certificate(&BTreeSet::from([y(), x()]), &finite)
            .expect("finite model");
        assert_eq!(certificate.assignments().collect::<Vec<_>>(), [
            (x(), ConsistencyValue::from(5_u128)),
            (y(), ConsistencyValue::from(0_u128)),
        ]);
        assert_eq!(
            certificate.value_of(x()),
            Some(ConsistencyValue::from(5_u128))
        );
        assert_eq!(
            certificate.value_of(y()),
            Some(ConsistencyValue::from(0_u128))
        );
        assert_eq!(certificate.value_of(var2()), None);
    }

    #[test]
    fn compilation_preserves_direction_order_and_subsumption()
    {
        let constraints = vec![
            LandmarkConstraint::leq(
                var_plus(x(), LevelOffset::from(2_u64))
                    .max(&var_plus(y(), LevelOffset::from(1_u64))),
                var_plus(y(), LevelOffset::from(1_u64)),
            )
            .expect("variable-only sides"),
            LandmarkConstraint::equal(
                var_plus(y(), LevelOffset::from(1_u64)),
                var_plus(var2(), LevelOffset::from(3_u64)),
            )
            .expect("variable-only sides"),
        ];
        let clauses = super::compile(&constraints);
        assert_eq!(
            clauses
                .iter()
                .map(|clause| (clause.head().variable(), u128::from(clause.head().offset())))
                .collect::<Vec<_>>(),
            [
                (HVar::Var(x()), 2_u128),
                (HVar::Var(var2()), 3),
                (HVar::Var(y()), 1)
            ]
        );
        assert_eq!(
            clauses
                .iter()
                .map(|clause| clause
                    .body()
                    .iter()
                    .map(|atom| (atom.variable(), u128::from(atom.offset())))
                    .collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            [
                vec![(HVar::Var(y()), 1_u128)],
                vec![(HVar::Var(y()), 1)],
                vec![(HVar::Var(var2()), 3)]
            ]
        );
    }

    #[test]
    fn side_evaluation_distinguishes_missing_values_and_overflow()
    {
        let witness = ConsistencyWitness {
            values: BTreeMap::from([
                (x(), ConsistencyValue::from(2_u128)),
                (y(), ConsistencyValue::from(7_u128)),
            ]),
        };
        let atoms = var_plus(x(), LevelOffset::from(3_u64)).max(&Level::var(y()));
        assert_eq!(
            super::evaluate_side(&atoms, &witness),
            Ok(ConsistencyValue::from(7_u128))
        );
        assert_eq!(
            super::evaluate_side(
                &atoms.max(&Level::constant(LevelConstant::from(9_u64))),
                &witness
            ),
            Ok(ConsistencyValue::from(9_u128))
        );
        assert_eq!(
            super::evaluate_side(&Level::var(var2()), &witness),
            Err(PosetEvidenceError::MissingAssignment { variable: var2() })
        );
        let largest = ConsistencyWitness {
            values: BTreeMap::from([(x(), ConsistencyValue::from(u128::MAX))]),
        };
        assert_eq!(
            super::evaluate_side(&Level::var(x()), &largest),
            Ok(ConsistencyValue::from(u128::MAX))
        );
        assert_eq!(
            super::evaluate_side(&var_plus(x(), LevelOffset::from(1_u64)), &largest),
            Err(PosetEvidenceError::Overflow)
        );
    }

    #[test]
    fn replay_distinguishes_body_and_head_overflow()
    {
        let seed = BTreeMap::from([(HVar::Var(x()), HornOffset::from(u128::MAX))]);
        let derivation = Derivation {
            steps: vec![DerivationStep::new(
                ClauseIndex::from(0_usize),
                HornShift::from(u128::MAX),
            )],
        };
        for (body, head) in [(1_u128, 0_u128), (0, 1)] {
            let clauses = [HornClause::new(
                &[HornAtom::new(HVar::Var(x()), HornOffset::from(body))],
                HornAtom::new(HVar::Var(y()), HornOffset::from(head)),
            )
            .expect("nonempty body")];
            assert_eq!(
                super::replay_derivation(&clauses, HornShift::ZERO, seed.clone(), &derivation),
                Err(PosetEvidenceError::Overflow)
            );
        }
        let clauses = [HornClause::new(
            &[HornAtom::new(HVar::Var(x()), HornOffset::ZERO)],
            HornAtom::new(HVar::Var(y()), HornOffset::ZERO),
        )
        .expect("nonempty body")];
        assert_eq!(
            super::replay_derivation(&clauses, HornShift::ZERO, seed, &derivation),
            Ok(BTreeMap::from([
                (HVar::Var(x()), HornOffset::from(u128::MAX)),
                (HVar::Var(y()), HornOffset::from(u128::MAX)),
            ]))
        );
    }

    #[test]
    fn paper_loop_variant_returns_a_validating_loop_witness()
    {
        let mut constraints = paper_constraints();
        constraints.push(
            LandmarkConstraint::leq(
                var_plus(x(), LevelOffset::from(0_u64)),
                var_plus(var4(), LevelOffset::from(0_u64)),
            )
            .expect("variable-only sides are well formed"),
        );
        let witness = looped(&constraints);
        let expected: BTreeSet<LevelVar> = [x(), y(), var2(), var3(), var4()].into_iter().collect();
        assert_eq!(
            witness.members(),
            &expected,
            "the loop closes over every variable"
        );
        assert_eq!(
            2_u128,
            u128::from(witness.shift()),
            "a total loop pins the shift to the maximal body offset 2"
        );
        assert_eq!(
            Ok(()),
            validate_loop_witness(&constraints, &witness),
            "the pumping derivation replays"
        );
    }

    #[test]
    fn paper_example_admits_with_a_validating_homomorphism()
    {
        let poset = admitted(paper_constraints());
        assert_eq!(
            Ok(()),
            validate_consistency(poset.constraints(), poset.consistency()),
            "the certificate validates by direct evaluation"
        );
        // Admission seeds the maximal body offset 2, reaching the least model
        // a2 b3 c6 d5 e3, so the assignment ceiling minus model value is pinned
        // exactly.
        let expected: BTreeMap<LevelVar, ConsistencyValue> = [
            (x(), ConsistencyValue::from(4_u128)),
            (y(), ConsistencyValue::from(3_u128)),
            (var2(), ConsistencyValue::from(0_u128)),
            (var3(), ConsistencyValue::from(1_u128)),
            (var4(), ConsistencyValue::from(3_u128)),
        ]
        .into_iter()
        .collect();
        let actual: BTreeMap<LevelVar, ConsistencyValue> =
            poset.consistency().assignments().collect();
        assert_eq!(actual, expected, "the certificate is the published one");
    }

    #[test]
    fn transitive_chain_admits()
    {
        let constraints = vec![
            LandmarkConstraint::leq(
                var_plus(x(), LevelOffset::from(0_u64)),
                var_plus(y(), LevelOffset::from(0_u64)),
            )
            .expect("variable-only sides are well formed"),
            LandmarkConstraint::leq(
                var_plus(y(), LevelOffset::from(0_u64)),
                var_plus(var2(), LevelOffset::from(0_u64)),
            )
            .expect("variable-only sides are well formed"),
        ];
        let poset = admitted(constraints);
        assert_eq!(
            Ok(()),
            validate_consistency(poset.constraints(), poset.consistency()),
            "a transitive chain admits with a validating certificate"
        );
    }

    #[test]
    fn equality_constraints_validate_under_the_certificate()
    {
        // Pins the equality arm of the consistency check; the worked example is
        // non-strict only.
        let constraints = vec![
            LandmarkConstraint::leq(
                var_plus(x(), LevelOffset::from(0_u64)),
                var_plus(y(), LevelOffset::from(0_u64)),
            )
            .expect("variable-only sides are well formed"),
            LandmarkConstraint::equal(
                var_plus(y(), LevelOffset::from(0_u64)),
                var_plus(var2(), LevelOffset::from(0_u64)),
            )
            .expect("variable-only sides are well formed"),
        ];
        let poset = admitted(constraints);
        assert_eq!(
            Ok(()),
            validate_consistency(poset.constraints(), poset.consistency()),
            "an equality constraint validates under the certificate"
        );
    }

    #[test]
    fn self_successor_equality_loops()
    {
        let constraints = vec![
            LandmarkConstraint::equal(
                var_plus(x(), LevelOffset::from(0_u64)),
                var_plus(x(), LevelOffset::from(1_u64)),
            )
            .expect("variable-only sides are well formed"),
        ];
        let witness = looped(&constraints);
        let expected: BTreeSet<LevelVar> = core::iter::once(x()).collect();
        assert_eq!(witness.members(), &expected, "x = x+1 loops on x");
        assert_eq!(
            Ok(()),
            validate_loop_witness(&constraints, &witness),
            "the one-step pumping derivation replays"
        );
    }

    #[test]
    fn perturbed_loop_witness_arms_are_rejected()
    {
        let constraints = vec![
            LandmarkConstraint::equal(
                var_plus(x(), LevelOffset::from(0_u64)),
                var_plus(x(), LevelOffset::from(1_u64)),
            )
            .expect("variable-only sides are well formed"),
        ];
        let genuine = looped(&constraints);

        let empty = LoopWitness {
            members: BTreeSet::new(),
            shift: genuine.shift(),
            derivation: genuine.derivation().clone(),
        };
        assert_eq!(
            Err(PosetEvidenceError::EmptyLoop),
            validate_loop_witness(&constraints, &empty),
            "an empty member set is rejected"
        );

        let unknown = LoopWitness {
            members: genuine.members().clone(),
            shift: genuine.shift(),
            derivation: Derivation {
                steps: vec![DerivationStep::new(
                    ClauseIndex::from(7_usize),
                    HornShift::ZERO,
                )],
            },
        };
        assert_eq!(
            Err(PosetEvidenceError::UnknownClause {
                clause: ClauseIndex::from(7_usize),
            }),
            validate_loop_witness(&constraints, &unknown),
            "an out-of-range clause index is rejected"
        );

        let unavailable = LoopWitness {
            members: genuine.members().clone(),
            shift: genuine.shift(),
            derivation: Derivation {
                steps: vec![DerivationStep::new(
                    ClauseIndex::from(0_usize),
                    HornShift::from(5_u128),
                )],
            },
        };
        assert_eq!(
            Err(PosetEvidenceError::BodyUnavailable {
                clause: ClauseIndex::from(0_usize),
            }),
            validate_loop_witness(&constraints, &unavailable),
            "a step firing above its available body is rejected"
        );

        let uncovered = LoopWitness {
            members: genuine.members().clone(),
            shift: genuine.shift(),
            derivation: Derivation { steps: vec![] },
        };
        assert_eq!(
            validate_loop_witness(&constraints, &uncovered),
            Err(PosetEvidenceError::TargetUncovered {
                subject: EvidenceSubject::Variable(x()),
            }),
            "an empty derivation covers no pumping target"
        );
    }

    #[test]
    fn partial_loop_pins_the_shift_choice()
    {
        // The loop set is a proper subset of the declared variables: `x = x+1`
        // loops on x while nothing ever raises y, so the witness shift takes
        // the largest-finite-value plus maximum-gain branch, which the total
        // loop goldens never reach.
        let constraints = vec![
            LandmarkConstraint::equal(
                var_plus(x(), LevelOffset::from(0_u64)),
                var_plus(x(), LevelOffset::from(1_u64)),
            )
            .expect("variable-only sides are well formed"),
            LandmarkConstraint::leq(
                var_plus(x(), LevelOffset::from(0_u64)),
                var_plus(y(), LevelOffset::from(0_u64)),
            )
            .expect("variable-only sides are well formed"),
        ];
        let witness = looped(&constraints);
        let expected: BTreeSet<LevelVar> = core::iter::once(x()).collect();
        assert_eq!(witness.members(), &expected, "only x loops");
        assert_eq!(
            1_u128,
            u128::from(witness.shift()),
            "the shift is the largest finite value 0 plus the maximum gain 1"
        );
        assert_eq!(
            Ok(()),
            validate_loop_witness(&constraints, &witness),
            "the partial-loop pumping derivation replays"
        );
    }

    #[test]
    fn constants_in_constraints_are_rejected()
    {
        let undominated = Level::constant(LevelConstant::from(5_u64))
            .max(&var_plus(x(), LevelOffset::from(3_u64)));
        assert_eq!(
            Err(PosetError::ConstantInConstraint),
            LandmarkConstraint::leq(undominated, var_plus(y(), LevelOffset::from(0_u64))),
            "an undominated constant part is rejected"
        );
        assert_eq!(
            Err(PosetError::ConstantInConstraint),
            LandmarkConstraint::leq(
                Level::constant(LevelConstant::from(3_u64)),
                var_plus(x(), LevelOffset::from(0_u64))
            ),
            "a pure constant side is rejected"
        );
        assert_eq!(
            Err(PosetError::ConstantInConstraint),
            LandmarkConstraint::leq(Level::zero(), var_plus(x(), LevelOffset::from(0_u64))),
            "the zero side is rejected, since zero is the constant 0"
        );
        let dominated = Level::constant(LevelConstant::from(3_u64))
            .max(&var_plus(x(), LevelOffset::from(3_u64)));
        assert!(
            LandmarkConstraint::leq(dominated, var_plus(x(), LevelOffset::from(4_u64))).is_ok(),
            "a dominated, canonicalized-away constant is variable-only"
        );
    }

    #[test]
    fn perturbed_consistency_witness_is_rejected()
    {
        let constraints = vec![
            LandmarkConstraint::leq(
                var_plus(x(), LevelOffset::from(1_u64)),
                var_plus(y(), LevelOffset::from(0_u64)),
            )
            .expect("variable-only sides are well formed"),
        ];
        let missing = ConsistencyWitness {
            values: core::iter::once((x(), ConsistencyValue::from(0_u128))).collect(),
        };
        assert_eq!(
            validate_consistency(&constraints, &missing),
            Err(PosetEvidenceError::MissingAssignment { variable: y() }),
            "an unassigned variable is rejected"
        );
        let violating = ConsistencyWitness {
            values: [
                (x(), ConsistencyValue::from(0_u128)),
                (y(), ConsistencyValue::from(0_u128)),
            ]
            .into_iter()
            .collect(),
        };
        assert_eq!(
            Err(PosetEvidenceError::ConstraintViolated {
                index: ConstraintIndex::from(0_usize),
            }),
            validate_consistency(&constraints, &violating),
            "x+1 <= y fails when both are assigned 0"
        );
    }

    #[test]
    fn empty_constraint_set_admits_with_an_empty_certificate()
    {
        let poset = admitted(vec![]);
        assert!(poset.variables().is_empty(), "no variables are declared");
        assert_eq!(
            0_usize,
            poset.consistency().assignments().count(),
            "the certificate is empty"
        );
        assert_eq!(
            Ok(()),
            validate_consistency(poset.constraints(), poset.consistency()),
            "the empty certificate validates"
        );
    }

    /// The worked example as declared constraints over `a` to `e`, that is
    /// variables `0` to `4`: `b+1 ≤ a∨b`, `c+3 ≤ b`, `d ≤ c+1`, `e ≤ b∨d+2`,
    /// compiling to exactly the published clause set.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the four declared constraints of the worked example,
    ///   in the published order.
    /// - provides: the fixture both dichotomy arms are stated against.
    /// - panics: when a declared side is rejected as not variable-only, which
    ///   the literal sides here never are.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the fixed paper constraints produce the published
    ///   finite homomorphism and, with the closing inequality, the all-variable
    ///   loop. Those exact outcomes expose altered direction, dropped
    ///   hypotheses and offsets.
    /// - witness: `poset::tests::paper_example_admits_with_a_validating_homomorphism`
    /// - witness: `poset::tests::paper_loop_variant_returns_a_validating_loop_witness`
    #[anodized::spec(ensures: |ret| ret.iter().map(|constraint| constraint.left().atoms().next()
        .map(|(variable, _)| variable)).eq([Some(y()), Some(var2()), Some(var3()), Some(var4())]))]
    fn paper_constraints() -> Vec<LandmarkConstraint>
    {
        vec![
            LandmarkConstraint::leq(
                var_plus(y(), LevelOffset::from(1_u64)),
                var_plus(x(), LevelOffset::from(0_u64))
                    .max(&var_plus(y(), LevelOffset::from(0_u64))),
            )
            .expect("variable-only sides are well formed"),
            LandmarkConstraint::leq(
                var_plus(var2(), LevelOffset::from(3_u64)),
                var_plus(y(), LevelOffset::from(0_u64)),
            )
            .expect("variable-only sides are well formed"),
            LandmarkConstraint::leq(
                var_plus(var3(), LevelOffset::from(0_u64)),
                var_plus(var2(), LevelOffset::from(1_u64)),
            )
            .expect("variable-only sides are well formed"),
            LandmarkConstraint::leq(
                var_plus(var4(), LevelOffset::from(0_u64)),
                var_plus(y(), LevelOffset::from(0_u64))
                    .max(&var_plus(var3(), LevelOffset::from(2_u64))),
            )
            .expect("variable-only sides are well formed"),
        ]
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

    /// The variable at index 2.
    ///
    /// # Specification
    /// trivial.
    fn var2() -> LevelVar
    {
        LevelVar::new(LevelVarIndex::from(2_u32))
    }

    /// The variable at index 3.
    ///
    /// # Specification
    /// trivial.
    fn var3() -> LevelVar
    {
        LevelVar::new(LevelVarIndex::from(3_u32))
    }

    /// The variable at index 4.
    ///
    /// # Specification
    /// trivial.
    fn var4() -> LevelVar
    {
        LevelVar::new(LevelVarIndex::from(4_u32))
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
    /// - hypothesis: L3 — small offsets zero through three participate in exact
    ///   compiled clauses and model evaluation; changing the variable or
    ///   iteration count moves the head/body boundary or the resulting
    ///   homomorphism.
    /// - witness: `poset::tests::compilation_preserves_direction_order_and_subsumption`
    /// - witness: `poset::tests::paper_example_admits_with_a_validating_homomorphism`
    #[anodized::spec(ensures: |ret| ret.constant_part() == LevelConstant::ZERO
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

    /// Admits a constraint set that must admit.
    ///
    /// # Specification
    /// - requires: `constraints` admits, which is what the calling test is
    ///   asserting about.
    /// - ensures: returns the admitted poset.
    /// - provides: the admitted-arm fixture, with the dichotomy's other arm
    ///   turned into a test failure at the point it appears.
    /// - panics: when admission overflows or returns a loop.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — empty and nonempty admitting constraints yield a
    ///   homomorphism validated independently; exact paper assignments
    ///   distinguish discarded constraints or a spurious admitting branch.
    /// - witness: `poset::tests::empty_constraint_set_admits_with_an_empty_certificate`
    /// - witness: `poset::tests::paper_example_admits_with_a_validating_homomorphism`
    #[anodized::spec(ensures: |ret| validate_consistency(ret.constraints(), ret.consistency()).is_ok())]
    fn admitted(constraints: Vec<LandmarkConstraint>) -> LandmarkPoset
    {
        match LandmarkPoset::admit(constraints).expect("admission does not overflow") {
            | AdmissionOutcome::Admitted(poset) => poset,
            | AdmissionOutcome::Loop(witness) => {
                panic!(
                    "expected admission, got a loop over {:?}",
                    witness.members()
                )
            },
        }
    }

    /// Admits a constraint set that must loop.
    ///
    /// # Specification
    /// - requires: `constraints` loops, which is what the calling test is
    ///   asserting about.
    /// - ensures: returns the loop witness.
    /// - provides: the loop-arm fixture, with the dichotomy's other arm turned
    ///   into a test failure at the point it appears.
    /// - panics: when admission overflows or admits.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — self-successor, total and partial loops replay
    ///   against their original constraints; exact members and shifts expose
    ///   fabricated evidence, a wrong pumping set or a mischosen shift.
    /// - witness: `poset::tests::self_successor_equality_loops`
    /// - witness: `poset::tests::paper_loop_variant_returns_a_validating_loop_witness`
    /// - witness: `poset::tests::partial_loop_pins_the_shift_choice`
    #[anodized::spec(ensures: |ret| validate_loop_witness(constraints, &ret).is_ok())]
    fn looped(constraints: &[LandmarkConstraint]) -> LoopWitness
    {
        match LandmarkPoset::admit(constraints.to_vec()).expect("admission does not overflow") {
            | AdmissionOutcome::Loop(witness) => witness,
            | AdmissionOutcome::Admitted(_poset) => panic!("expected a loop, got admission"),
        }
    }
}
