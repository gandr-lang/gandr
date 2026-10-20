//! A definition's signature quantified over stages.
//!
//! `def applyAt @[i : Size] (f : Nat[<i] => Nat, x : Nat[<i])` takes a stage
//! `i` beside its parameters. The declared type crosses erased, `(Nat => Nat,
//! Nat) -> F Nat`, and the signature says where each binder stands in it: a
//! [`StageMark`] is a path from the declared type to a data-type occurrence,
//! each step a child the stage order places, and the stage that occurrence is
//! refined at. A stage never enters a node's identity; the kernel re-stages the
//! declared type from the marks, at stages it mints for the definition's own
//! body and at stages it reads off the arguments of each call.
//!
//! # Items
//! - [`StageSignature`]: the binders, their bounds and the marks.
//! - [`StageBound`], [`StageMark`], [`StageReach`]: one binder's bound and one
//!   occurrence's stage.

use alloc::vec::Vec;

use anodized::spec;

use crate::term::StageDepth;

/// A binder of a stage signature, by its place among the signature's
/// binders, counted from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StageBinder(usize);

impl From<usize> for StageBinder
{
    /// Preserve the binder's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<StageBinder> for usize
{
    /// Read the binder's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(binder: StageBinder) -> Self
    {
        binder.0
    }
}

/// One step of a mark's path: the ordinal of a child among those the stage
/// order places under a type former, counted from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PlacedChild(usize);

impl From<usize> for PlacedChild
{
    /// Preserve the child's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<PlacedChild> for usize
{
    /// Read the child's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(child: PlacedChild) -> Self
    {
        child.0
    }
}

/// The bound a stage binder carries.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum StageBound
{
    /// Any stage: `@[i : Size]`.
    Unbounded,
    /// A stage strictly below an earlier binder's: `@[n : Size, i : Size, i <
    /// n]`.
    Below(StageBinder),
}

/// Where an occurrence stands relative to its binder.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum StageReach
{
    /// At the binder's stage: `Nat[i]`.
    At,
    /// Below it by `depth` steps: `Nat[<i]` at one.
    Below(StageDepth),
}

/// One data-type occurrence of a declared type refined at a binder's stage.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct StageMark
{
    /// The path from the declared type to the occurrence.
    path: Vec<PlacedChild>,
    /// The binder the occurrence's stage is read from.
    binder: StageBinder,
    /// Where it stands relative to that binder.
    reach: StageReach,
}

impl StageMark
{
    /// The occurrence at `path` refined at `binder`'s stage, read through
    /// `reach`.
    ///
    /// # Specification
    /// - requires: nothing — the kernel refuses a path that reaches no data
    ///   type and a binder the signature does not bind at admission.
    /// - ensures: the accessors return exactly the arguments.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mark crosses the wire with its path, binder and
    ///   reach.
    /// - witness: `encode::tests::a_stage_signature_fills_the_erasure_slot`
    #[spec(ensures: |ret| ret.binder == binder && ret.reach == reach)]
    #[inline]
    #[must_use]
    pub fn new(
        path: Vec<PlacedChild>,
        binder: StageBinder,
        reach: StageReach,
    ) -> Self
    {
        Self {
            path,
            binder,
            reach,
        }
    }

    /// The path from the declared type to the occurrence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn path(&self) -> &[PlacedChild]
    {
        &self.path
    }

    /// The binder the occurrence's stage is read from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn binder(&self) -> StageBinder
    {
        self.binder
    }

    /// Where the occurrence stands relative to its binder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reach(&self) -> StageReach
    {
        self.reach
    }
}

/// The stages a definition's signature quantifies over and where its declared
/// type reads each; empty for a definition quantified over none.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct StageSignature
{
    /// Each binder's bound, in binder order.
    bounds: Vec<StageBound>,
    /// The occurrences the binders refine, in the order the declared type's
    /// walk reaches them.
    marks: Vec<StageMark>,
}

impl StageSignature
{
    /// The signature of a definition quantified over no stage.
    pub const UNQUANTIFIED: Self = Self {
        bounds: Vec::new(),
        marks: Vec::new(),
    };

    /// The signature binding one stage per entry of `bounds`, refining the
    /// occurrences `marks` name.
    ///
    /// # Specification
    /// - requires: nothing — the kernel refuses a bound or a mark naming a
    ///   binder out of order at admission.
    /// - ensures: the accessors return exactly the arguments, in order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a signature crosses the wire with its bounds and
    ///   marks in order.
    /// - witness: `encode::tests::a_stage_signature_fills_the_erasure_slot`
    #[spec(captures: lengths = (bounds.len(), marks.len()), ensures: |ret| ret.bounds.len() == lengths.0 && ret.marks.len() == lengths.1)]
    #[inline]
    #[must_use]
    pub fn new(
        bounds: Vec<StageBound>,
        marks: Vec<StageMark>,
    ) -> Self
    {
        Self { bounds, marks }
    }

    /// Each binder's bound, in binder order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn bounds(&self) -> &[StageBound]
    {
        &self.bounds
    }

    /// The occurrences the binders refine.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn marks(&self) -> &[StageMark]
    {
        &self.marks
    }
}
