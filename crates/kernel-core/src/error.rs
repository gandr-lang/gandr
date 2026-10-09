//! The kernel's refusal vocabulary: one typed error per way a declaration can
//! fail to be admitted, with self-contained payloads.
//!
//! # Every payload survives the truncation that produced it
//!
//! Admission truncates the arena on rejection, so an error carrying an arena id
//! would name a node that no longer exists by the time the caller reads it.
//! Every payload here is therefore **content**: a head former the caller can
//! match on, and the offending node's content digest, which identifies it
//! across the truncation and across arenas without holding a reference into
//! either.
//!
//! # Faults are surfaced, never trusted
//!
//! Three variants name conditions the design excludes: an id that resolves to
//! nothing, a register holding the wrong polarity, and a level-oracle fault the
//! theory rules out. Each is unreachable when the machine is wired correctly,
//! and each is a *refusal* rather than an assumption — a wiring defect rejects
//! the declaration instead of fabricating a type that could wrongly convert.

use alloc::boxed::Box;

use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_strata::EntailmentCountermodel;
use gandr_kernel_strata::LeqRefutation;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelError;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LoopWitness;
use gandr_kernel_strata::PosetError;
use gandr_kernel_term::CompType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TableEntryCount;
use gandr_kernel_term::ValueType;

use crate::env::OutstandingCount;

/// The head former of a value type, as an error payload names it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ValueTypeHead
{
    /// A rigid base-type atom.
    Base,
    /// The unit type.
    Unit,
    /// A product.
    Product,
    /// A sum.
    Sum,
    /// A thunk type.
    Thunk,
    /// A universe, of either ground sort; the digest tells the sorts apart.
    Universe,
    /// An explicit lift.
    Lift,
    /// A type read off a code.
    Element,
    /// A sealed abstract type.
    Abstract,
    /// A static Pi, classifying type operators.
    StaticPi,
    /// The reference resolved to nothing.
    Unreadable,
}

impl ValueTypeHead
{
    /// The head of a resolved value type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn of(value_type: &ValueType) -> Self
    {
        match *value_type {
            | ValueType::Base(_) => Self::Base,
            | ValueType::Unit => Self::Unit,
            | ValueType::Element { .. } => Self::Element,
            | ValueType::Product(..) => Self::Product,
            | ValueType::Sum(..) => Self::Sum,
            | ValueType::Thunk(_) => Self::Thunk,
            | ValueType::Universe { .. } => Self::Universe,
            | ValueType::Lift { .. } => Self::Lift,
            | ValueType::Abstract(_) => Self::Abstract,
            | ValueType::StaticPi { .. } => Self::StaticPi,
        }
    }
}

/// The head former of a computation type, as an error payload names it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CompTypeHead
{
    /// A returner.
    Returner,
    /// A non-dependent function type.
    Arrow,
    /// A dependent function type.
    Pi,
    /// A computation type read off a code.
    Element,
    /// The reference resolved to nothing.
    Unreadable,
}

impl CompTypeHead
{
    /// The head of a resolved computation type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn of(comp_type: &CompType) -> Self
    {
        match *comp_type {
            | CompType::Returner(_) => Self::Returner,
            | CompType::Arrow { .. } => Self::Arrow,
            | CompType::Pi { .. } => Self::Pi,
            | CompType::Element { .. } => Self::Element,
        }
    }
}

/// A self-contained reference to a value type that a refusal is about.
///
/// The head is what a caller matches on; the digest is what identifies *which*
/// type of that head it was, and it identifies it by content, so it stays
/// meaningful after the arena that held it is truncated.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ValueTypeWitness
{
    /// The head former.
    head: ValueTypeHead,
    /// The content digest of the whole type.
    digest: ContentDigest,
}

impl ValueTypeWitness
{
    /// Pair a head with the content digest of the type it heads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        head: ValueTypeHead,
        digest: ContentDigest,
    ) -> Self
    {
        Self { head, digest }
    }

    /// The head former.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn head(self) -> ValueTypeHead
    {
        self.head
    }

    /// The content digest of the whole type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn digest(self) -> ContentDigest
    {
        self.digest
    }
}

/// A self-contained reference to a computation type that a refusal is about.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CompTypeWitness
{
    /// The head former.
    head: CompTypeHead,
    /// The content digest of the whole type.
    digest: ContentDigest,
}

impl CompTypeWitness
{
    /// Pair a head with the content digest of the type it heads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        head: CompTypeHead,
        digest: ContentDigest,
    ) -> Self
    {
        Self { head, digest }
    }

    /// The head former.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn head(self) -> CompTypeHead
    {
        self.head
    }

    /// The content digest of the whole type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn digest(self) -> ContentDigest
    {
        self.digest
    }
}

/// The value-type shape a rule required at the position it refused.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ExpectedValueShape
{
    /// A product, for a pair.
    Product,
    /// A sum, for an injection or a case scrutinee.
    Sum,
    /// A thunk type, for a thunk or a force.
    Thunk,
    /// A static Pi, for a static application's head.
    StaticPi,
}

/// The computation-type shape a rule required at the position it refused.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ExpectedComputationShape
{
    /// A function type, for a lambda or an application.
    Arrow,
    /// A returner, for a `return` or the bound half of a sequencing bind.
    Returner,
}

/// A checking-only form that appeared where a type had to be synthesized.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NonInferableForm
{
    /// A sum injection carries no record of which sum it injects into.
    Injection,
    /// A lambda carries no domain annotation.
    Lambda,
}

/// Which polarity the checker machine's produced register was expected to hold.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RegisterFault
{
    /// A frame consuming a synthesized value type found something else.
    ExpectedValueType,
    /// A frame consuming a synthesized computation type found something else.
    ExpectedCompType,
}

/// Why a strict universe order `lower < upper` did not hold, in the oracle's
/// own evidence vocabulary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LevelOrderRefutation
{
    /// The free-fragment oracle's counter-valuation.
    Free(LeqRefutation),
    /// The landmark oracle's countermodel under the declared constraints.
    Landmark(Box<EntailmentCountermodel>),
}

/// A failed universe or lift judgement, with the two levels and re-checkable
/// refutation evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UniverseViolation
{
    /// The level required to be strictly below.
    lower: Level,
    /// The level required to be strictly above.
    upper: Level,
    /// The oracle's refutation.
    refutation: LevelOrderRefutation,
}

impl UniverseViolation
{
    /// Pair the two levels with the oracle's refutation of their strict order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        lower: Level,
        upper: Level,
        refutation: LevelOrderRefutation,
    ) -> Self
    {
        Self {
            lower,
            upper,
            refutation,
        }
    }

    /// The level required to be strictly below.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lower(&self) -> &Level
    {
        &self.lower
    }

    /// The level required to be strictly above.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn upper(&self) -> &Level
    {
        &self.upper
    }

    /// The oracle's refutation, for a caller that re-checks it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn refutation(&self) -> &LevelOrderRefutation
    {
        &self.refutation
    }
}

/// A mismatch between two value types the checker required to convert.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ValueTypeMismatch
{
    /// The type flowing down.
    expected: ValueTypeWitness,
    /// The type flowing up.
    actual: ValueTypeWitness,
}

impl ValueTypeMismatch
{
    /// Pair the expected witness with the actual one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        expected: ValueTypeWitness,
        actual: ValueTypeWitness,
    ) -> Self
    {
        Self { expected, actual }
    }

    /// The type flowing down.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn expected(self) -> ValueTypeWitness
    {
        self.expected
    }

    /// The type flowing up.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn actual(self) -> ValueTypeWitness
    {
        self.actual
    }
}

/// A mismatch between two computation types the checker required to convert.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CompTypeMismatch
{
    /// The type flowing down, or the left branch's.
    expected: CompTypeWitness,
    /// The type flowing up, or the right branch's.
    actual: CompTypeWitness,
}

impl CompTypeMismatch
{
    /// Pair the expected witness with the actual one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        expected: CompTypeWitness,
        actual: CompTypeWitness,
    ) -> Self
    {
        Self { expected, actual }
    }

    /// The type flowing down, or the left branch's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn expected(self) -> CompTypeWitness
    {
        self.expected
    }

    /// The type flowing up, or the right branch's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn actual(self) -> CompTypeWitness
    {
        self.actual
    }
}

/// Every way the kernel refuses a declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum KernelError
{
    /// A value variable's de Bruijn index escaped the typing context.
    UnboundVariable
    {
        /// The out-of-range index.
        index: DeBruijnIndex,
    },
    /// A constant reference named no prior admitted declaration — out of range,
    /// or a forward reference into the append-only environment.
    UnboundConstant
    {
        /// The unresolved position.
        index: ConstantIndex,
    },
    /// A checking-only term form appeared where a type had to be synthesized.
    NotInferable
    {
        /// The offending form.
        form: NonInferableForm,
    },
    /// A value of the wrong type shape met an eliminator or a checking rule.
    ValueShapeMismatch
    {
        /// The value-type shape the rule required.
        expected: ExpectedValueShape,
        /// The type actually present.
        actual: ValueTypeWitness,
    },
    /// A computation of the wrong type shape met an eliminator or a checking
    /// rule.
    ComputationShapeMismatch
    {
        /// The computation-type shape the rule required.
        expected: ExpectedComputationShape,
        /// The type actually present.
        actual: CompTypeWitness,
    },
    /// The drain of deferred code obligations reached its ceiling.
    ///
    /// A code obligation's check can form a synthesized type and owe further
    /// codes, so the drain's bound is not the artifact's own size. Reaching the
    /// ceiling refuses the declaration rather than pursuing it, which is the
    /// same fail-closed posture the kernel takes toward every condition it
    /// cannot bound.
    CodeObligationCeiling
    {
        /// The ceiling that was reached.
        ceiling: TableEntryCount,
    },
    /// A synthesized value type failed to convert against the expected type.
    ValueTypeMismatch(ValueTypeMismatch),
    /// A synthesized computation type failed to convert against the expected
    /// type.
    ComputationTypeMismatch(CompTypeMismatch),
    /// The two branches of a synthesized `case` produced inconvertible types.
    CaseBranchMismatch(CompTypeMismatch),
    /// A bind's body or a case branch synthesized a computation type that
    /// mentions the value its binder introduced, so no type outside the binder
    /// states what it computes.
    BinderEscape
    {
        /// The type synthesized under the binder.
        actual: CompTypeWitness,
    },
    /// A level variable's index reached or exceeded the declaration's prenex
    /// parameter count.
    LevelVariableOutOfScope
    {
        /// The out-of-scope variable.
        variable: LevelVar,
    },
    /// Level arithmetic stepped past the representable range. Saturating would
    /// silently identify distinct levels, so the overflow surfaces.
    LevelArithmetic,
    /// A universe or lift judgement `lower < upper` failed, with re-checkable
    /// refutation evidence.
    UniverseViolation(Box<UniverseViolation>),
    /// The declaration's landmark constraints have no model — an inconsistent
    /// level context that would make a universe inhabit itself. The replayable
    /// pumping witness is carried.
    InconsistentLevelConstraints(Box<LoopWitness>),
    /// A landmark-entailment query hit a fault the theory excludes, since an
    /// admitted poset does not loop. Surfaced rather than trusted.
    LevelOracleFault(PosetError),
    /// The checker machine's produced register held the wrong polarity for its
    /// consuming frame. Unreachable when the goal-to-frame correspondence is
    /// wired as its table states; surfaced rather than trusted, so a wiring
    /// defect rejects rather than fabricating a type.
    CheckerRegisterFault(RegisterFault),
    /// An arena id resolved to no node. Unreachable under constructor-only
    /// minting; surfaced rather than trusted, so a resolution defect rejects
    /// rather than proceeding on a fabricated node.
    ArenaFault,
    /// An abstract-type declaration's kind was not a universe. The kind is what
    /// every reference to the atom reads its level from, so admitting a
    /// non-universe kind would leave type formation with a level to *infer*
    /// rather than to look up.
    AbstractTypeKindNotUniverse
    {
        /// The kind actually declared.
        actual: ValueTypeWitness,
    },
    /// A sealed-atom reference named a position that is not an admitted
    /// abstract-type declaration: out of range, a forward reference, or a
    /// definition or axiom masquerading as an atom.
    ///
    /// This is where a forged atom dies. Nothing in an artifact says "I am an
    /// atom"; the kernel resolves the position and requires the declaration it
    /// finds to be one.
    NotAnAbstractType
    {
        /// The position the reference named.
        index: ConstantIndex,
    },
    /// A declaration's sealing-provenance slot named an atom that does not
    /// occur in its declared type, which is an unfalsifiable claim about the
    /// elaborator's history rather than about the declaration.
    SealingProvenanceNotProjected
    {
        /// The atom claimed but not projected onto.
        atom: ConstantIndex,
    },
    /// A declaration's sealing-provenance slot was not strictly ascending —
    /// unsorted, or naming one atom twice. Canonical order is what makes the
    /// slot a set with one spelling.
    SealingProvenanceNotCanonical
    {
        /// The entry that did not strictly exceed its predecessor.
        atom: ConstantIndex,
    },
    /// A declaration was offered while content staged **after** it is still
    /// unresolved.
    ///
    /// Admission's rollback is a contiguous truncation to the declaration's
    /// content-start, and it cannot spare a later staging's nodes sitting above
    /// that mark. Performing it would delete content a producer still holds, or
    /// — the worse face — free indices a later staging re-mints, so a
    /// subsequent admission would check other content under that declaration's
    /// name. The kernel refuses rather than producing either, and the
    /// producer's remedy is to resolve the later staging first, by
    /// admitting, bypassing, or abandoning it.
    OutstandingStagedContent
    {
        /// How many staged, unresolved marks sit above this declaration's.
        above: OutstandingCount,
    },
    /// A static Pi's domain or codomain was not a static classifier: a
    /// universe, or a static Pi over them. An operator ranges over codes, so
    /// its classifier is built of the types that classify codes.
    StaticClassifierExpected
    {
        /// The child type actually present.
        actual: ValueTypeWitness,
    },
}

impl From<LevelError> for KernelError
{
    /// The refusal a level-arithmetic failure surfaces as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every level error becomes `KernelError::LevelArithmetic`, so
    ///   an arithmetic step that left the representable range refuses the
    ///   declaration instead of saturating and silently identifying two
    ///   distinct levels.
    /// - provides: the one conversion from the level algebra's own failure into
    ///   the kernel's refusal vocabulary.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn from(_error: LevelError) -> Self
    {
        Self::LevelArithmetic
    }
}

impl core::fmt::Display for KernelError
{
    /// Writes a short description of this refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::UnboundVariable { .. } => f.write_str("a variable escaped its context"),
            | Self::UnboundConstant { .. } => {
                f.write_str("a constant named no admitted declaration")
            },
            | Self::NotInferable { .. } => {
                f.write_str("a checking-only form was used where a type had to be inferred")
            },
            | Self::ValueShapeMismatch { .. } => f.write_str("a value type had a wrong shape"),
            | Self::ComputationShapeMismatch { .. } => {
                f.write_str("a computation type had a wrong shape")
            },
            | Self::CodeObligationCeiling { .. } => {
                f.write_str("the deferred code obligations reached their ceiling")
            },
            | Self::ValueTypeMismatch(_) => f.write_str("two value types are not convertible"),
            | Self::ComputationTypeMismatch(_) => {
                f.write_str("two computation types are not convertible")
            },
            | Self::CaseBranchMismatch(_) => {
                f.write_str("the two branches of a case produced inconvertible types")
            },
            | Self::BinderEscape { .. } => {
                f.write_str("a type synthesized under a binder mentions the value it bound")
            },
            | Self::LevelVariableOutOfScope { .. } => {
                f.write_str("a level variable escaped the declaration's prenex parameters")
            },
            | Self::LevelArithmetic => f.write_str("level arithmetic left the representable range"),
            | Self::UniverseViolation(_) => f.write_str("a universe judgement does not hold"),
            | Self::InconsistentLevelConstraints(_) => {
                f.write_str("the declared level constraints have no model")
            },
            | Self::LevelOracleFault(_) => f.write_str("the level oracle reported a fault"),
            | Self::CheckerRegisterFault(_) => {
                f.write_str("the checker's produced register held the wrong polarity")
            },
            | Self::ArenaFault => f.write_str("an arena id resolved to no node"),
            | Self::AbstractTypeKindNotUniverse { .. } => {
                f.write_str("an abstract type's kind is not a universe")
            },
            | Self::NotAnAbstractType { .. } => {
                f.write_str("a sealed-atom reference named no abstract-type declaration")
            },
            | Self::SealingProvenanceNotProjected { .. } => {
                f.write_str("a claimed sealing atom does not occur in the declared type")
            },
            | Self::SealingProvenanceNotCanonical { .. } => {
                f.write_str("a sealing-provenance slot is not strictly ascending")
            },
            | Self::OutstandingStagedContent { .. } => {
                f.write_str("a later staged declaration is still unresolved")
            },
            | Self::StaticClassifierExpected { .. } => {
                f.write_str("a static Pi stands over a type that classifies no codes")
            },
        }
    }
}

impl core::error::Error for KernelError
{
}
