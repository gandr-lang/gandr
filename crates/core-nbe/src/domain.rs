//! The glued value domain: both faces named on the domain's own types.
//!
//! # Why both faces are named together
//!
//! Readback *chooses* a face and conversion *forces* a face, so the two
//! policies are one table. Both faces are fields of the domain's own types, so
//! the table has one shape; a face kept beside the domain would give two
//! tables that disagree at the seams.
//!
//! **The term face.** A domain value caches the id of the core term it came
//! from, and keeps it exactly while nothing inside it reduced. Readback of such
//! a value is the cached id rather than a rebuild, which is what makes an
//! unreduced subterm free to traverse and what preserves the sharing the core
//! arena already carried. The moment anything inside reduces, the face is
//! [`TermFace::Reduced`] and there is no source term that denotes the value —
//! stating the absence is the point, because a stale source id is a wrong
//! readback rather than a slow one.
//!
//! **The unfolding face.** A neutral keeps its neutral form beside a lazily
//! forced unfolded form. A neutral headed by a variable, or by a definition
//! that is opaque where it is being read, is [`Unfolding::Rigid`] and has no
//! second form at all. A neutral headed by a manifest definition carries the
//! body's content id unforced, and forcing replaces the content id by the
//! glued form it evaluated to — **beside** the neutral form, never instead of
//! it, because conversion compares neutral forms and only falls back to
//! unfolding.
//!
//! # Neutrals are one family, and the spine is what separates the polarities
//!
//! A stuck value and a stuck computation share a head and differ in what is
//! stacked on it. The vocabulary's one value eliminator is the static
//! application, so a neutral standing in a value position carries a spine of
//! static applications alone — empty for a bare variable or constant — while a
//! neutral standing in a computation position carries the applications, binds
//! and cases that could not fire. [`Neutral`] is therefore one node kind, and
//! the well-formedness condition — a value-position neutral's spine holds
//! static applications only — is enforced by the arena constructor rather than
//! left to a convention.
//!
//! **Module forms enter as neutrals and cost nothing.** A module reference is a
//! rigid head like any other opaque constant; no arm anywhere replaces it by a
//! representation, and no eliminator is written for it here.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::Side;

use crate::arena::CompClosureId;
use crate::arena::DomainCompId;
use crate::arena::DomainValueId;
use crate::arena::NeutralId;
use crate::arena::ValueClosureId;

/// A de Bruijn **level**: binders counted inward from the empty context, so a
/// level names the same binder however deep the reader has gone.
///
/// The domain counts levels where the syntax counts indices, which is what lets
/// a closure be entered under a fresh binder without shifting anything already
/// in the environment.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BinderLevel(u32);

impl BinderLevel
{
    /// The outermost level: the first binder opened from the empty context.
    pub const FLOOR: Self = Self(0_u32);
}

impl From<u32> for BinderLevel
{
    /// Read a `u32` as a binder level.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(level: u32) -> Self
    {
        Self(level)
    }
}

impl From<BinderLevel> for u32
{
    /// Read the level back out as a `u32`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(level: BinderLevel) -> Self
    {
        level.0
    }
}

/// The term face of a domain value: the core value it came from, while nothing
/// inside it has reduced.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TermFace
{
    /// Nothing inside this value reduced, so this core value still denotes it
    /// and a readback may answer with the id rather than rebuilding.
    Source(ValueId),
    /// Something inside reduced, so no core value denotes this one and a
    /// readback must rebuild.
    Reduced,
}

/// The term face of a domain computation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompTermFace
{
    /// Nothing inside this computation reduced.
    Source(ComputationId),
    /// Something inside reduced.
    Reduced,
}

/// A cross-polarity reference into the domain, which is what an unfolding
/// resolves to and what a walk over the domain carries.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Glued
{
    /// A domain value.
    Value(DomainValueId),
    /// A domain computation at weak head.
    Computation(DomainCompId),
}

/// The unfolding face of a neutral.
///
/// The three states are not a progression: a rigid neutral never acquires an
/// unfolding, because there is nothing to unfold, and that is a different fact
/// from "not forced yet".
///
/// # Both loaded states are about the **head**, never about the spine
///
/// [`Self::Unforced`] and [`Self::Forced`] name the same object at two stages —
/// the head's definition body, first as a table entry and then as the glued
/// value it evaluated to. **Neither names the value of the neutral as a
/// whole.**
///
/// That is what makes the face spine-independent, and it is the reading every
/// consumer must take. Reducing a neutral through its unfolding is therefore
/// two moves rather than one: take the head's value, then re-apply this
/// neutral's own spine to it. Growing a spine consequently carries the face
/// across unchanged and invalidates nothing, at either loaded state — whereas a
/// face that named the whole neutral's value would be falsified by the very
/// next elimination stacked on it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Unfolding
{
    /// There is no body to unfold: the head is a bound variable, a module form,
    /// an axiom or a sealed atom, or a definition that is opaque where this
    /// neutral is being read.
    Rigid,
    /// The **head** is a manifest definition whose body has not been forced.
    /// The body is named by its canonical subterm-table entry, which is
    /// what lets the neutral be built before any arena holds the body.
    Unforced(GlobalIndex),
    /// The **head's** body, forced into this run's arena.
    ///
    /// This is the head's value alone. The neutral's own value is this with the
    /// neutral's spine re-applied, which is why the state stays correct as the
    /// spine grows.
    Forced(Glued),
}

/// What a neutral is stuck on.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum NeutralHead
{
    /// A bound variable, named by its zone and its de Bruijn level.
    Variable
    {
        /// The zone the binder was opened in.
        zone: Zone,
        /// The level, counted inward from the empty context.
        level: BinderLevel,
    },
    /// A declaration standing rigid here: an axiom, a sealed atom, or a
    /// definition this scope reads as opaque.
    Constant(ConstantIndex),
    /// A module form. It enters as a neutral and costs nothing: no eliminator
    /// is written for it, and no arm replaces it by a representation.
    Module(ConstantIndex),
}

/// One elimination stacked on a neutral head.
///
/// Every arm but [`Self::StaticApply`] is a computation eliminator. The static
/// application is the vocabulary's one value eliminator, which is why a
/// neutral in value position carries only static applications.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Elimination
{
    /// Transport under a neutral path head.
    Transport(DomainValueId),
    /// Product transport waiting for a neutral pair operand.
    ProductTransport(DomainValueId),
    /// `M v`: applied to a domain value argument.
    Apply(DomainValueId),
    /// `force v`: the forced thunk was itself stuck.
    Force,
    /// `x ← M; N`: sequenced into a body that could not run.
    Bind(CompClosureId),
    /// A sum elimination whose scrutinee was stuck.
    Case
    {
        /// The left branch, closed over its environment.
        on_left: CompClosureId,
        /// The right branch, closed over its environment.
        on_right: CompClosureId,
    },
    /// `f a`: a static application whose operator was stuck, applied to a
    /// domain value argument.
    StaticApply(DomainValueId),
}

/// A stuck computation or value: a head, the eliminations stacked on it, and
/// the unfolding face.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Neutral
{
    /// What the neutral is stuck on.
    head: NeutralHead,
    /// The eliminations, innermost first, so the last is the outermost. Empty
    /// exactly when the neutral stands in a value position.
    spine: Vec<Elimination>,
    /// The unfolding face, beside the neutral form rather than instead of it.
    unfolding: Unfolding,
}

impl Neutral
{
    /// Build a neutral over a head, a spine and an unfolding face.
    ///
    /// # Specification
    /// - requires: `spine` holds static applications alone exactly when the
    ///   neutral will stand in a value position, and `unfolding` is loaded only
    ///   for a head a definition can stand behind. The arena checks both at its
    ///   own mint, which is why this constructor is crate-private.
    /// - ensures: the neutral carries exactly the head, spine, and unfolding
    ///   face offered, in that spine order.
    /// - provides: the one neutral shape both positions share, so the position
    ///   is a property of the spine rather than of the type.
    /// - fails: never — the two conditions are refused at the arena's mint, not
    ///   here.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub(crate) fn new(
        head: NeutralHead,
        spine: Vec<Elimination>,
        unfolding: Unfolding,
    ) -> Self
    {
        Self {
            head,
            spine,
            unfolding,
        }
    }

    /// What this neutral is stuck on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn head(&self) -> NeutralHead
    {
        self.head
    }

    /// The eliminations stacked on the head, innermost first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the eliminations in the order they were stacked, innermost
    ///   first, so the last is the outermost; the slice holds static
    ///   applications alone exactly when the neutral stands in a value
    ///   position.
    /// - provides: the spine the arena's value-position guard reads, and the
    ///   walk readback rebuilds an eliminated term from.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn spine(&self) -> &[Elimination]
    {
        &self.spine
    }

    /// The unfolding face.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unfolding(&self) -> Unfolding
    {
        self.unfolding
    }

    /// Record that this neutral's **head's** body has been forced to `glued`.
    ///
    /// # Specification
    /// - requires: nothing — a rigid neutral and an already-forced one are both
    ///   admissible input.
    /// - ensures: on success the unfolding face is `Forced(glued)` and the
    ///   neutral form — head and spine — is untouched, which is the property
    ///   conversion stands on: forcing adds a second reading, it never replaces
    ///   the first. `glued` is the **head's** body, not this neutral's value;
    ///   the neutral's value is `glued` with this neutral's spine re-applied.
    /// - provides: the one transition of the unfolding face. The clause states
    ///   the transition against the entry face, the unchanged head, and the
    ///   spine's unchanged length; the spine's contents would need an owned
    ///   entry snapshot, which the pinned expansion evaluates even in a
    ///   non-enforcing build.
    /// - fails: returns the reason without changing anything when the face has
    ///   nothing to force (rigid) or was already forced. Forcing twice is a
    ///   caller error rather than an idempotent no-op, because the second call
    ///   would discard an evaluation the first one paid for.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ForceRefusal::Rigid`] — there is no body to force.
    /// - [`ForceRefusal::AlreadyForced`] — the body was forced before.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the three-state match,
    ///   separated by forcing an unforced neutral, forcing a rigid one, and
    ///   forcing a forced one, with the head and spine asserted unchanged in
    ///   every case.
    /// - witness: `domain::tests::forcing_adds_a_reading_and_keeps_the_neutral_form`
    /// - witness: `domain::tests::a_rigid_neutral_has_nothing_to_force`
    #[inline]
    #[spec(
        captures: [
            entry_unfolding = self.unfolding,
            entry_head = self.head,
            entry_spine = self.spine.len(),
        ],
        ensures: |ret| [
            match entry_unfolding {
                | Unfolding::Unforced(_) => {
                    ret.is_ok() && self.unfolding == Unfolding::Forced(glued)
                },
                | Unfolding::Rigid => ret == Err(ForceRefusal::Rigid),
                | Unfolding::Forced(_) => ret == Err(ForceRefusal::AlreadyForced),
            },
            ret.is_ok() || self.unfolding == entry_unfolding,
            self.head == entry_head,
            self.spine.len() == entry_spine,
        ],
    )]
    pub fn force_to(
        &mut self,
        glued: Glued,
    ) -> Result<(), ForceRefusal>
    {
        match self.unfolding {
            | Unfolding::Rigid => Err(ForceRefusal::Rigid),
            | Unfolding::Forced(_) => Err(ForceRefusal::AlreadyForced),
            | Unfolding::Unforced(_) => {
                self.unfolding = Unfolding::Forced(glued);
                Ok(())
            },
        }
    }
}

/// Why an unfolding could not be forced.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ForceRefusal
{
    /// The neutral has no body: its head is a variable or an opaque constant.
    Rigid,
    /// The body was forced already, and forcing again would discard the result.
    AlreadyForced,
}

/// A domain value: the positive fragment, glued to its source term.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DomainValue
{
    /// A closed reflexivity or equivalence certificate, kept as raw syntax.
    /// Translator programs are not normalized by certificate conversion.
    PathCertificate
    {
        /// The core certificate whose complete syntax remains available.
        certificate: ValueId,
        /// The term face.
        face: TermFace,
    },
    /// A componentwise path product; components may arrive by substitution.
    PathProduct
    {
        /// The first path component.
        first: DomainValueId,
        /// The second path component.
        second: DomainValueId,
        /// The term face.
        face: TermFace,
    },
    /// The unit value.
    Unit
    {
        /// The term face.
        face: TermFace,
    },
    /// A base-type literal.
    ///
    /// The payload stays in the core arena rather than being copied here, so
    /// the node carries the core value that holds it. That field is
    /// **independent of the face**: it names where the payload lives and
    /// stays valid when the face is [`TermFace::Reduced`], which is what a
    /// literal that arrived through a substitution looks like.
    Literal
    {
        /// The core value holding the literal.
        literal: ValueId,
        /// The term face.
        face: TermFace,
    },
    /// A pair.
    Pair
    {
        /// The first component.
        first: DomainValueId,
        /// The second component.
        second: DomainValueId,
        /// The term face.
        face: TermFace,
    },
    /// A sum injection.
    Injection
    {
        /// The side injected into.
        side: Side,
        /// The injected value.
        body: DomainValueId,
        /// The term face.
        face: TermFace,
    },
    /// A thunk: a suspended computation closure. This is the one value that
    /// embeds a computation, and it suspends rather than runs it.
    Thunk
    {
        /// The suspended computation, closed over its environment.
        body: CompClosureId,
        /// The term face.
        face: TermFace,
    },
    /// An explicit universe lift.
    Lift
    {
        /// The target level.
        target: LiftTarget,
        /// The lifted value.
        body: DomainValueId,
        /// The term face.
        face: TermFace,
    },
    /// A stuck value: a neutral whose spine holds static applications alone.
    Neutral
    {
        /// The neutral.
        neutral: NeutralId,
        /// The term face.
        face: TermFace,
    },
    /// A code: a quote of a value or computation type, closed over the
    /// environment the type's free variables stand in.
    ///
    /// A quote carries a type into a term, and a type reads the variables its
    /// decodes' codes name, so a quote is suspended as a value closure whose
    /// body is the quote itself rather than evaluated: a type has no weak head
    /// to reach, and the codes inside it are evaluated where a readback or a
    /// comparison reads them.
    Code
    {
        /// The quote, closed over its environment.
        code: ValueClosureId,
        /// The term face.
        face: TermFace,
    },
    /// A type operator: a static lambda, closed over the environment its
    /// body reads.
    ///
    /// Like a code, the closure's body is the static lambda itself rather
    /// than the lambda's body, so a comparison reads the operator whole as it
    /// reads a quote; a static application enters the lambda's body in the
    /// closure's environment extended by the argument.
    StaticLambda
    {
        /// The static lambda, closed over its environment.
        lambda: ValueClosureId,
        /// The term face.
        face: TermFace,
    },
}

impl DomainValue
{
    /// The term face this value carries, which every arm holds in the same
    /// field.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn face(&self) -> TermFace
    {
        match *self {
            | Self::PathCertificate { face, .. }
            | Self::PathProduct { face, .. }
            | Self::Unit { face }
            | Self::Literal { face, .. }
            | Self::Pair { face, .. }
            | Self::Injection { face, .. }
            | Self::Thunk { face, .. }
            | Self::Lift { face, .. }
            | Self::Neutral { face, .. }
            | Self::Code { face, .. }
            | Self::StaticLambda { face, .. } => face,
        }
    }
}

/// The target level of a lift, held by id so a [`DomainValue`] stays `Copy`.
///
/// A level is a vector of atoms, so storing one inline would make every domain
/// value a heap-owning node and every arena clone a deep one. The level lives
/// in the run's level table and the value names it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LiftTarget(u32);

impl From<u32> for LiftTarget
{
    /// Read a `u32` as a lift's level-table target.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(target: u32) -> Self
    {
        Self(target)
    }
}

impl From<LiftTarget> for u32
{
    /// Read the target back out as a `u32`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(target: LiftTarget) -> Self
    {
        target.0
    }
}

/// A domain computation at weak head: the negative fragment, glued to its
/// source term.
///
/// Evaluation stops here. A lambda is a closure rather than a body, a returner
/// carries the value it produced, and everything that could not fire is a
/// neutral.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DomainComp
{
    /// A lambda, closed over its environment.
    Lambda
    {
        /// The body, closed over its environment.
        body: CompClosureId,
        /// The term face.
        face: CompTermFace,
    },
    /// A returner carrying the value it produced.
    Return
    {
        /// The produced value.
        value: DomainValueId,
        /// The term face.
        face: CompTermFace,
    },
    /// A stuck computation: a neutral head with the eliminations that could not
    /// fire stacked on it.
    Neutral
    {
        /// The neutral.
        neutral: NeutralId,
        /// The term face.
        face: CompTermFace,
    },
}

impl DomainComp
{
    /// The term face this weak head carries, which every arm holds in the same
    /// field.
    ///
    /// # Specification
    /// - requires: nothing; every arm carries a face.
    /// - ensures: the face the arm holds, whichever arm this weak head is.
    /// - provides: the one read that spares every caller a match over the whole
    ///   vocabulary.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn face(&self) -> CompTermFace
    {
        match *self {
            | Self::Lambda { face, .. }
            | Self::Return { face, .. }
            | Self::Neutral { face, .. } => face,
        }
    }
}

/// A level held in a run's level table, beside the levels a lift names.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LevelEntry
{
    /// The level itself.
    level: Level,
}

impl LevelEntry
{
    /// Hold a level.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn new(level: Level) -> Self
    {
        Self { level }
    }

    /// The level held.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn level(&self) -> &Level
    {
        &self.level
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::GlobalIndex;

    use super::ForceRefusal;
    use super::Glued;
    use super::Neutral;
    use super::NeutralHead;
    use super::TermFace;
    use super::Unfolding;
    use crate::arena::DomainArena;

    /// A neutral headed by a manifest definition whose body is not yet forced.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a spineless neutral headed by a manifest definition whose
    ///   unfolding face is loaded but not forced, so it is the one input state
    ///   from which a force succeeds.
    /// - provides: the entry state the three-state force fixture below is
    ///   separated from.
    /// - panics: none.
    fn unforced() -> Neutral
    {
        Neutral::new(
            NeutralHead::Constant(ConstantIndex::from(3_usize)),
            Vec::new(),
            Unfolding::Unforced(GlobalIndex::from(7_u32)),
        )
    }

    #[test]
    fn forcing_adds_a_reading_and_keeps_the_neutral_form()
    {
        let mut arena = DomainArena::new();
        let first = Glued::Value(arena.value_unit(TermFace::Reduced));
        let second = Glued::Value(arena.value_unit(TermFace::Reduced));
        let mut neutral = unforced();
        let head = neutral.head();

        assert_eq!(Ok(()), neutral.force_to(first));
        assert_eq!(
            Unfolding::Forced(first),
            neutral.unfolding(),
            "the unfolded form is recorded"
        );
        assert_eq!(
            head,
            neutral.head(),
            "beside the neutral form rather than instead of it"
        );
        assert!(
            neutral.spine().is_empty(),
            "and the spine is untouched by forcing"
        );
        assert_eq!(
            Err(ForceRefusal::AlreadyForced),
            neutral.force_to(second),
            "forcing twice is refused rather than silently discarding the first result"
        );
        assert_eq!(
            Unfolding::Forced(first),
            neutral.unfolding(),
            "and the refusal kept the first result"
        );
    }

    #[test]
    fn a_rigid_neutral_has_nothing_to_force()
    {
        let mut arena = DomainArena::new();
        let glued = Glued::Value(arena.value_unit(TermFace::Reduced));
        let mut neutral = Neutral::new(
            NeutralHead::Module(ConstantIndex::from(0_usize)),
            Vec::new(),
            Unfolding::Rigid,
        );
        assert_eq!(
            Err(ForceRefusal::Rigid),
            neutral.force_to(glued),
            "a module form is rigid: no arm replaces it by a representation"
        );
        assert_eq!(
            Unfolding::Rigid,
            neutral.unfolding(),
            "and the refusal left it rigid rather than half-forced"
        );
    }
}
