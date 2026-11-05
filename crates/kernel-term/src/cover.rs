//! Cover derivations: the evidence that a match's arms cover its scrutinee.
//!
//! # Why a derivation
//!
//! A decision tree says how a match runs. It does not say why every value
//! reaches an arm. A [`Cover`] states that reason as a derivation `{arms} ◁ Ξ`,
//! built from three rules, so a checker reads the reason step by step and
//! trusts no verdict the lowering wrote.
//!
//! # Three rules over a flat table
//!
//! [`Step::Var`] names the arm a leaf runs. [`Step::Split`] lists the cases of
//! one column, one child for each case, in the order the column's type lists
//! them. [`Step::Compose`] stands a derivation under one branch of a split. A
//! part is minted before the step holding it, so every walk is a loop over
//! ids. The derivation names arms by position and copies no pattern.
//!
//! # Who reads it
//!
//! The lowering records a derivation beside each match's tree. The kernel
//! replays it against the admitted environment: each data split re-derives
//! its family's constructors and the loops its case owes, and each step meets
//! the tree's node at its place. A higher inductive type's case owes one branch
//! for each loop after its constructors, so a data split lists both.
//!
//! # References
//!
//! - `vault:01a1567c-2c32-7ed3-a102-45e54f702b4f` — anchor: Eremondi and
//!   Kammar's coverage semantics, § 5 — the closure operations whose
//!   isomorphism, coproduct injections and composition are `var`, `split` and
//!   `compose`.
//! - `vault:01a1567c-2c32-7ed3-a102-45dc5330206a` — anchor: coverage and
//!   unification, § coverage-evidence-form — the derivation as the evidence
//!   form a match carries.

use alloc::vec::Vec;

use anodized::spec;

use crate::CellIndex;
use crate::ConstantIndex;
use crate::ConstructorTag;
use crate::FieldCount;
use crate::Literal;

/// The id of a step in a [`Cover`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StepId(u32);

/// How many branches a split holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BranchCount(usize);

impl From<usize> for BranchCount
{
    /// The count of `branches`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(branches: usize) -> Self
    {
        Self(branches)
    }
}

impl From<BranchCount> for usize
{
    /// The number of branches.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: BranchCount) -> Self
    {
        count.0
    }
}

/// How many arms a match holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArmCount(usize);

impl From<usize> for ArmCount
{
    /// The count of `arms`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(arms: usize) -> Self
    {
        Self(arms)
    }
}

impl From<ArmCount> for usize
{
    /// The number of arms.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ArmCount) -> Self
    {
        count.0
    }
}

/// One loop a case over a presented sort owes: its type of words and its
/// cell among the words' cells.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Loop
{
    /// The type of words the loop is a letter of.
    words: ConstantIndex,
    /// The loop's position among its words' cells.
    cell: CellIndex,
}

impl Loop
{
    /// The loop at `cell` of the words `words`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        words: ConstantIndex,
        cell: CellIndex,
    ) -> Self
    {
        Self { words, cell }
    }

    /// The type of words the loop is a letter of.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn words(self) -> ConstantIndex
    {
        self.words
    }

    /// The loop's position among its words' cells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cell(self) -> CellIndex
    {
        self.cell
    }
}

/// The cases one split lists.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Cases
{
    /// A data family's constructors: one tag and its field count for each
    /// branch, in the order the branches stand; then the loops its case owes,
    /// one branch each.
    Data
    {
        /// The family's declaration.
        family: ConstantIndex,
        /// Each branch's constructor and the fields it binds.
        constructors: Vec<(ConstructorTag, FieldCount)>,
        /// Each loop the case owes, after the constructors' branches.
        loops: Vec<Loop>,
    },
    /// A boolean: `true`, then `false`.
    Boolean,
    /// An integer compared with a literal: equal, then any other.
    Integer(Literal),
    /// A tuple of this many components, under one branch.
    Tuple(usize),
    /// A record's projected fields, under one branch.
    Record(usize),
    /// A sum of this many summands, one branch each.
    Sum(usize),
    /// A native list: the empty list, then a cell.
    List,
    /// A guard: the arm where it holds, then the rows after it.
    Guard,
    /// A branch no row admits: no case at all.
    Absurd,
}

impl Cases
{
    /// How many branches a split over these cases holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one for each constructor and loop of a data split, two for a
    ///   boolean, an integer, a list and a guard, one for a tuple and a record,
    ///   the summands of a sum, and none for an absurd branch.
    /// - provides: the width every split's branches must match.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a data split, a sum and an absurd branch separate the
    ///   widths.
    /// - witness: `cover::tests::each_split_holds_one_branch_per_case`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| usize::from(ret) <= 2_usize || matches!(*self, Self::Data { .. } | Self::Sum(_)))]
    pub fn width(&self) -> BranchCount
    {
        BranchCount(match *self {
            Self::Data {
                ref constructors,
                ref loops,
                ..
            } => constructors.len().saturating_add(loops.len()),
            Self::Boolean | Self::Integer(_) | Self::List | Self::Guard => 2,
            Self::Tuple(_) | Self::Record(_) => 1,
            Self::Sum(summands) => summands,
            Self::Absurd => 0,
        })
    }
}

/// One step of a cover derivation.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Step
{
    /// `var`: the arm, by its position among the match's arms, that every
    /// value reaching this leaf runs.
    Var(usize),
    /// `split`: one column's cases and one child for each case.
    Split
    {
        /// The cases, in the order the column's type lists them.
        cases: Cases,
        /// One child for each case, in the same order.
        branches: Vec<StepId>,
    },
    /// `compose`: a derivation standing under one branch of a split.
    Compose(StepId),
}

impl Step
{
    /// The steps this step names, left to right.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a split's branches in order, a composition's inner step, and
    ///   nothing for a `var`.
    /// - provides: the one child relation every walk over a derivation follows.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `var`, a split of two branches and a composition
    ///   separate the arities and the order.
    /// - witness: `cover::tests::a_step_names_its_parts_in_order`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match *self {
        Self::Var(_) => ret.is_empty(),
        Self::Split { ref branches, .. } => ret == branches.as_slice(),
        Self::Compose(inner) => ret == [inner],
    })]
    pub fn parts(&self) -> &[StepId]
    {
        match *self {
            Self::Var(_) => &[],
            Self::Split { ref branches, .. } => branches,
            Self::Compose(ref inner) => core::slice::from_ref(inner),
        }
    }
}

/// A cover derivation, each part minted before the step holding it; the
/// last step minted is the root.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Cover
{
    /// The steps, by id.
    steps: Vec<Step>,
}

/// Why a cover derivation is refused.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CoverRefusal
{
    /// The derivation holds no step.
    Empty,
    /// A step names a step minted after it, or none.
    Dangling(StepId),
    /// A split holds a number of branches other than its cases'.
    BranchCount(StepId),
    /// A data split names a family the signature does not declare.
    UnknownFamily(StepId),
    /// A data split lists a number of constructors other than its family's.
    ConstructorCount(StepId),
    /// A data split lists a constructor at a place other than its tag.
    ConstructorOrder(StepId),
    /// A data split gives a constructor a field count other than its
    /// declaration's.
    FieldCount(StepId),
    /// A `var` names an arm the match does not have.
    UnknownArm(StepId),
    /// A data split lists other loops than the ones its case owes.
    Loops(StepId),
    /// A step meets a node of the tree that is not its own: a split over
    /// another former, another number of branches, or a branch that binds
    /// other than its fields.
    Tree(StepId),
}

impl Cover
{
    /// An empty derivation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Mint `step` and name it.
    ///
    /// # Specification
    /// - requires: every part `step` names was minted in this derivation, and
    ///   the derivation holds fewer than `u32::MAX` steps.
    /// - ensures: a fresh id naming `step`; every earlier id names what it
    ///   named.
    /// - provides: the only way a step enters the derivation.
    /// - fails: never.
    /// - panics: none — an id past the representable ceiling saturates, which
    ///   the requirement excludes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two steps minted in turn get distinct ids, each
    ///   reading back what was minted under it.
    /// - witness: `cover::tests::a_step_names_its_parts_in_order`
    #[inline]
    #[spec(captures: [entry = self.steps.len(), minted = step.clone()],
        ensures: |ret| self.steps.len() == entry.saturating_add(1_usize) && self.step(ret) == Some(&minted))]
    pub fn mint(
        &mut self,
        step: Step,
    ) -> StepId
    {
        let id = StepId(u32::try_from(self.steps.len()).unwrap_or(u32::MAX));
        self.steps.push(step);
        id
    }

    /// The step `id` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the step minted under `id`, or nothing when `id` names none
    ///   of this derivation's.
    /// - provides: the checked read every walk resolves a part through.
    /// - fails: answers nothing for a foreign or dangling id.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a minted id and an empty derivation separate the hit
    ///   from the miss.
    /// - witness: `cover::tests::a_step_names_its_parts_in_order`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() == usize::try_from(id.0).is_ok_and(|at| at < self.steps.len()))]
    pub fn step(
        &self,
        id: StepId,
    ) -> Option<&Step>
    {
        self.steps.get(usize::try_from(id.0).ok()?)
    }

    /// Every step with its id, in mint order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one pair for each step, the id the step was minted under
    ///   first, ascending.
    /// - provides: the walk a reader or a rebuild of the derivation follows.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a lazy iterator, and a predicate that
    ///   reads it drains the answer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::step`].
    /// - witness: `cover::tests::a_step_names_its_parts_in_order`
    #[inline]
    pub fn steps(&self) -> impl Iterator<Item = (StepId, &Step)>
    {
        self.steps
            .iter()
            .enumerate()
            .map(|(at, step)| (StepId(u32::try_from(at).unwrap_or(u32::MAX)), step))
    }

    /// Check the derivation against the signature and the match's arms.
    ///
    /// # Specification
    /// - requires: `declared` answers the field counts of each family's
    ///   constructors, in tag order.
    /// - ensures: `Ok` when every step names only steps minted before it, every
    ///   split holds one branch for each case, every data split lists its
    ///   family's constructors once each, in tag order, each with its declared
    ///   field count, and every `var` names one of `arms` arms.
    /// - provides: the check that refuses a derivation whose split leaves out,
    ///   repeats or reorders a constructor, by the refusal's name.
    /// - fails: [`CoverRefusal`] naming the first step, in mint order, that
    ///   breaks a rule.
    /// - panics: none.
    ///
    /// # Termination
    /// One pass over the steps, each step reading its own parts once.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a derivation for a nested match is admitted, and the
    ///   same derivation with one constructor dropped from a split is refused
    ///   `ConstructorCount`.
    /// - witness: `cover::tests::a_split_that_drops_a_constructor_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || !self.steps.is_empty())]
    pub fn check<Declared, Fields>(
        &self,
        arms: ArmCount,
        declared: Declared,
    ) -> Result<(), CoverRefusal>
    where
        Declared: Fn(ConstantIndex) -> Option<Fields>,
        Fields: ExactSizeIterator<Item = FieldCount>,
    {
        if self.steps.is_empty() {
            return Err(CoverRefusal::Empty);
        }
        for (at, step) in self.steps.iter().enumerate() {
            let id = StepId(u32::try_from(at).unwrap_or(u32::MAX));
            if step.parts().iter().any(|part| part.0 >= id.0) {
                return Err(CoverRefusal::Dangling(id));
            }
            match *step {
                Step::Var(arm) if arm >= arms.0 => return Err(CoverRefusal::UnknownArm(id)),
                Step::Var(_) | Step::Compose(_) => {},
                Step::Split {
                    ref cases,
                    ref branches,
                } => {
                    if BranchCount::from(branches.len()) != cases.width() {
                        return Err(CoverRefusal::BranchCount(id));
                    }
                    if let Cases::Data {
                        family,
                        ref constructors,
                        ..
                    } = *cases
                    {
                        Self::check_family(id, family, constructors, &declared)?;
                    }
                },
            }
        }
        Ok(())
    }

    /// Check one data split's constructors against its family's declaration.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` when `constructors` lists the declaration's constructors
    ///   once each, in tag order, each with its field count.
    /// - fails: [`CoverRefusal::UnknownFamily`], then
    ///   [`CoverRefusal::ConstructorCount`], then
    ///   [`CoverRefusal::ConstructorOrder`], then [`CoverRefusal::FieldCount`]
    ///   at the first constructor that breaks each.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::check`].
    /// - witness: `cover::tests::a_split_that_drops_a_constructor_is_refused`
    #[spec(ensures: |ret| ret.is_err()
        || declared(family).is_some_and(|fields| fields.len() == constructors.len()))]
    fn check_family<Declared, Fields>(
        id: StepId,
        family: ConstantIndex,
        constructors: &[(ConstructorTag, FieldCount)],
        declared: &Declared,
    ) -> Result<(), CoverRefusal>
    where
        Declared: Fn(ConstantIndex) -> Option<Fields>,
        Fields: ExactSizeIterator<Item = FieldCount>,
    {
        let fields = declared(family).ok_or(CoverRefusal::UnknownFamily(id))?;
        if constructors.len() != fields.len() {
            return Err(CoverRefusal::ConstructorCount(id));
        }
        for (place, (&(tag, count), declared)) in constructors.iter().zip(fields).enumerate() {
            if tag != ConstructorTag::from(place) {
                return Err(CoverRefusal::ConstructorOrder(id));
            }
            if count != declared {
                return Err(CoverRefusal::FieldCount(id));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
