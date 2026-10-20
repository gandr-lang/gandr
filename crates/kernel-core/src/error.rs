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

use anodized::spec;
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
    /// A generative datatype application.
    Data,
    /// A structural record classifier.
    Record,
    /// A finite session code.
    Session,
    /// A universe-path classifier.
    PathUniverse,
    /// A universe-flow classifier.
    FlowUniverse,
    /// An identity type between two elements.
    Path,
    /// A directed identity type between two elements.
    Flow,
    /// A bridge between two elements: a relation with no reflexivity.
    Bridge,
    /// A rigid base-type atom.
    Base,
    /// A product, the unit type among them.
    Product,
    /// A dependent pair.
    Sigma,
    /// A sum, the empty type among them.
    Sum,
    /// A strictly positive list fixed point.
    List,
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
    /// A type refined at a stage of a recursion.
    Staged,
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
            ValueType::Data { .. } => Self::Data,
            ValueType::Record(_) => Self::Record,
            ValueType::PathUniverse(..) => Self::PathUniverse,
            ValueType::FlowUniverse(..) => Self::FlowUniverse,
            ValueType::Path { .. } => Self::Path,
            ValueType::Flow { .. } => Self::Flow,
            ValueType::Bridge { .. } => Self::Bridge,
            ValueType::Base(_) => Self::Base,
            ValueType::Element { .. } => Self::Element,
            ValueType::Product(..) => Self::Product,
            ValueType::Sigma { .. } => Self::Sigma,
            ValueType::Sum(..) => Self::Sum,
            ValueType::Session { .. } => Self::Session,
            ValueType::List(_) => Self::List,
            ValueType::Thunk(_) => Self::Thunk,
            ValueType::Universe { .. } => Self::Universe,
            ValueType::Lift { .. } => Self::Lift,
            ValueType::Abstract(_) => Self::Abstract,
            ValueType::StaticPi { .. } => Self::StaticPi,
            ValueType::Staged { .. } => Self::Staged,
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
    /// A lazy product.
    With,
    /// A codata type: an observation-indexed computation type.
    Codata,
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
            CompType::Returner(_) => Self::Returner,
            CompType::Arrow { .. } => Self::Arrow,
            CompType::Pi { .. } => Self::Pi,
            CompType::Element { .. } => Self::Element,
            CompType::With(..) => Self::With,
            CompType::Codata { .. } => Self::Codata,
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
    /// A nominal datatype, for a constructor or nominal case.
    Data,
    /// A structural record, for a record literal or projection.
    Record,
    /// A universe path, for transport or a product-path component.
    PathUniverse,
    /// An element identity, for `here`, a higher form or an identity
    /// eliminator.
    Path,
    /// A product, for a pair.
    Product,
    /// A dependent pair, for a dependent split's scrutinee.
    Sigma,
    /// A sum, for an injection or a case scrutinee.
    Sum,
    /// A native list, for nil and cons and a list case's scrutinee.
    List,
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
    /// A lazy product, for a lazy pairing or a projection.
    With,
    /// A dependent arrow whose codomain is a dependent arrow into a returner,
    /// for a telescope transport's motive.
    Telescope,
}

/// A checking-only form that appeared where a type had to be synthesized.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NonInferableForm
{
    /// A sum injection carries no record of which sum it injects into.
    Injection,
    /// A lambda carries no domain annotation.
    Lambda,
    /// A case of no branches, the empty sum's elimination, carries no result
    /// annotation and has no branch to synthesize one from.
    EmptyCase,
    /// A case on a native list carries no result annotation; it only checks.
    ListCase,
    /// A fixpoint carries no classifier annotation.
    Fixpoint,
    /// A native list introduction needs its element classifier.
    List,
    /// A higher field carries no record of the identities it relates.
    HigherField,
    /// A higher or quantified evaluation carries no record of the functions it
    /// relates.
    HigherEvaluation,
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
    /// A nominal head does not name an admitted data declaration.
    NotADataType
    {
        index: ConstantIndex
    },
    /// A data signature's kind is not a positive universe.
    DataKindNotUniverse,
    /// An application supplies the wrong number of declaration arguments.
    DataArgumentArity,
    /// A codata head does not name an admitted codata declaration.
    NotACodataType
    {
        index: ConstantIndex
    },
    /// A codata signature's kind is not a computation universe.
    CodataKindNotUniverse,
    /// A codata declaration states no observation.
    CodataWithoutObservations,
    /// A codata declaration names itself other than at an observation's
    /// result, at its parameter variables in telescope order.
    CodataOccurrence,
    /// A constructor tag is absent from the declaration table.
    UnknownConstructor
    {
        tag: gandr_kernel_term::ConstructorTag,
    },
    /// A constructor supplies the wrong number of fields.
    ConstructorArity,
    /// A constructor of an indexed family is classified at another index than
    /// the one it states.
    ConstructorIndex
    {
        /// The constructor's tag.
        tag: gandr_kernel_term::ConstructorTag,
    },
    /// A case scrutinises an indexed family, whose branches would check under
    /// the index each constructor stands at.
    IndexedCase,
    /// An indexed family's constructor states a result index of another
    /// length than its family's index telescope, or presents rules.
    IndexedSignature,
    /// A case does not provide exactly one branch per constructor.
    NonExhaustiveDataCase,
    /// A data declaration's own family stands under a function's domain where
    /// no stage reaches it: at other arguments, inside a term, or through a
    /// parameter that is not strictly positive.
    NegativeOccurrence(gandr_kernel_term::OccurrenceSite),
    /// A data declaration's own family stands nested through another family's
    /// parameter that is not strictly positive, or under a former that places
    /// nothing.
    NestedOccurrence(gandr_kernel_term::OccurrenceSite),
    /// A data declaration's own family stands inside a term a type reads: a
    /// decode, a quote, a lift, path endpoints, or its parameter telescope.
    IndexOccurrence(gandr_kernel_term::OccurrenceSite),
    /// A data declaration's own family is applied to anything but its
    /// parameter variables in telescope order.
    NonUniformOccurrence(gandr_kernel_term::OccurrenceSite),
    /// A data declaration names a declaration admitted after its own block.
    CrossBlockReference
    {
        /// Where the reference stands.
        site: gandr_kernel_term::OccurrenceSite,
        /// The later position it names.
        index: ConstantIndex,
    },
    /// A presented data declaration's rule does not present its type: it is
    /// not a linear, constructor-headed, terminating rewrite over the
    /// declaration's own constructor table.
    RuleNotPresentable(gandr_kernel_term::RuleRefusal),
    /// A definition's operation rules do not converge: a rule is malformed,
    /// not oriented by the path order, or one of its critical pairs does not
    /// join.
    OperationRulesRefused(gandr_kernel_term::OperationRuleRefusal),
    /// A presentation's rules are not one convergent rewriting system as its
    /// value states them: a rule is unreadable or malformed, not decreased by
    /// the stated order, a derived rule does not replay its peak, or a
    /// critical pair does not join.
    PresentationRulesRefused(gandr_kernel_term::TheoryRuleRefusal),
    /// A ruled definition's body is not its rules' decision tree: its shape is
    /// not a fixpoint over cases, or a leaf is the right side of no rule
    /// whose left side matches it.
    OperationBodyUnlinked(crate::ruled::OperationBodyFault),
    /// A type of words is not the words its free cells mint: a cell is not a
    /// loop at one closed point of an earlier parameterless data declaration,
    /// or the declaration's table or rules are not the mint, or an earlier type
    /// of words already loops at that point.
    WordsRefused(gandr_kernel_term::CellFault),
    /// A case over a presented type is not shown to respect the named rule of
    /// its type: its arms might tell apart two terms the rule identifies.
    RuleNotRespected(gandr_kernel_term::RuleIndex),
    /// A case of no branches over a path type whose endpoints are not shown
    /// apart: the reason the apartness rule names.
    NotApart(gandr_kernel_term::Apartness),
    /// A case over a sort its words loop at is not shown to respect the named
    /// loop: carried along it, its answer at the loop's point does not convert
    /// with that answer.
    LoopNotRespected(gandr_kernel_term::CellIndex),
    /// A case's obligation for the named loop ran past its conversion's
    /// budget: unfolding the definitions its sides run neither met nor parted
    /// them in the steps allowed.
    LoopUndecided(gandr_kernel_term::CellIndex),
    /// A value checked where the recursion typing wants a stage it does not
    /// stand at or below: a self-reference's argument not strictly below the
    /// fixpoint's stage, a constructor with no recursive field where no value
    /// in scope shows a stage below the one wanted, or a value at no stage
    /// where one is wanted.
    StageNotBelow
    {
        /// Where the value stands.
        found: gandr_kernel_term::Standing,
        /// The stage it was wanted at or below.
        bound: gandr_kernel_term::Stage,
    },
    /// A presented type names a stage. Admission alone mints a stage, at a
    /// structural fixpoint and a case under it; a declaration never writes
    /// one.
    StagePresented,
    /// A required record field is absent.
    AbsentRecordField
    {
        label: gandr_kernel_term::FieldLabel,
    },
    /// A tuple projection names a component past the product's last, or a
    /// lazy projection one past the lazy product's last.
    AbsentTupleComponent
    {
        component: gandr_kernel_term::Component,
    },
    /// Session formation or finite relation replay failed.
    Session(crate::session::SessionError),
    /// A native universe-path formation or replay obligation failed.
    Path(crate::path_universe::PathError),
    /// A native universe-flow classifier or session simulation failed.
    Flow(crate::flow_universe::FlowError),
    /// An element-identity formation, introduction or elimination failed.
    Identity(crate::element_identity::IdentityError),
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
    /// A seal named a position that is not an abstract type whose minting
    /// admission is still open: a closed atom, an atom whose own scope closes
    /// it, or any other declaration.
    SealNotOpen
    {
        /// The position the seal named.
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 at the constant-level successor ceiling for both
    ///   universe sorts; predecessor admission and exact ceiling refusal
    ///   distinguish saturation, a wrong refusal and lost prior content.
    /// - witness: `error::tests::universe_successor_overflow_refuses_admission_without_truncating_prior_content`
    #[spec(ensures: |ret| matches!(ret, Self::LevelArithmetic))]
    #[inline]
    fn from(_error: LevelError) -> Self
    {
        Self::LevelArithmetic
    }
}

impl core::fmt::Display for KernelError
{
    /// Writes the description of this refusal class.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes a class-specific description; payloads remain
    ///   available through the error's typed variants.
    /// - provides: a readable refusal without depending on the rejected arena.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over every refusal variant and failure on its first
    ///   write; pairwise descriptions and exact errors distinguish conflated
    ///   classes and suppressed sink failures, without pinning prose.
    /// - witness: `error::tests::refusal_descriptions_separate_classes_and_propagate_sink_failure`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::NotADataType { .. } => f.write_str("a nominal head named no data declaration"),
            Self::DataKindNotUniverse => {
                f.write_str("a data declaration kind was not a positive universe")
            },
            Self::DataArgumentArity => {
                f.write_str("a data application had the wrong argument arity")
            },
            Self::NotACodataType { .. } => f.write_str("a codata head named no codata declaration"),
            Self::CodataKindNotUniverse => {
                f.write_str("a codata declaration kind was not a computation universe")
            },
            Self::CodataWithoutObservations => {
                f.write_str("a codata declaration stated no observation")
            },
            Self::CodataOccurrence => f.write_str(
                "a codata declaration named itself other than at an observation's result, at its \
                 parameters",
            ),
            Self::UnknownConstructor { .. } => {
                f.write_str("a constructor tag was absent from its declaration")
            },
            Self::ConstructorArity => f.write_str("a constructor had the wrong field arity"),
            Self::ConstructorIndex { .. } => {
                f.write_str("a constructor was classified at another index than it states")
            },
            Self::IndexedCase => f.write_str("a data case scrutinised an indexed family"),
            Self::IndexedSignature => f.write_str(
                "an indexed family's constructor stated another index arity, or the family \
                 presented rules",
            ),
            Self::NonExhaustiveDataCase => {
                f.write_str("a data case did not cover exactly its constructor table")
            },
            Self::NegativeOccurrence(_) => f.write_str(
                "a data declaration's family stood under a function's domain where no stage \
                     reaches it",
            ),
            Self::NestedOccurrence(_) => {
                f.write_str("a data declaration's family stood nested where no stage reaches it")
            },
            Self::IndexOccurrence(_) => {
                f.write_str("a data declaration's family stood inside a term a type reads")
            },
            Self::NonUniformOccurrence(_) => {
                f.write_str("a data declaration's family was applied to non-parameter arguments")
            },
            Self::CrossBlockReference { .. } => {
                f.write_str("a data declaration named a declaration after its own block")
            },
            Self::RuleNotPresentable(_) => {
                f.write_str("a data declaration's rule did not present its type")
            },
            Self::OperationRulesRefused(_) => {
                f.write_str("a definition's operation rules did not converge")
            },
            Self::PresentationRulesRefused(_) => {
                f.write_str("a presentation's rules did not converge as its value states them")
            },
            Self::OperationBodyUnlinked(_) => {
                f.write_str("a definition's body is not its operation rules' decision tree")
            },
            Self::WordsRefused(_) => {
                f.write_str("a type of words was not the words its free cells mint")
            },
            Self::RuleNotRespected(_) => {
                f.write_str("a case over a presented type was not shown to respect its rules")
            },
            Self::NotApart(_) => {
                f.write_str("a case of no branches met a path whose endpoints are not apart")
            },
            Self::LoopNotRespected(_) => {
                f.write_str("a case over a looped sort was not shown to respect its loops")
            },
            Self::LoopUndecided(_) => f.write_str(
                "a case over a looped sort ran past its budget deciding whether it respects its \
                 loops",
            ),
            Self::StageNotBelow { .. } => {
                f.write_str("a value did not stand below the stage its recursion wants")
            },
            Self::StagePresented => f.write_str("a presented type named a stage"),
            Self::AbsentRecordField { .. } => f.write_str("a required record field was absent"),
            Self::AbsentTupleComponent { .. } => {
                f.write_str("a projection named a component the product does not have")
            },
            Self::Session(ref error) => error.fmt(f),
            Self::Path(ref error) => error.fmt(f),
            Self::Flow(ref error) => error.fmt(f),
            Self::Identity(ref error) => error.fmt(f),
            Self::UnboundVariable { .. } => f.write_str("a variable escaped its context"),
            Self::UnboundConstant { .. } => f.write_str("a constant named no admitted declaration"),
            Self::NotInferable { .. } => {
                f.write_str("a checking-only form was used where a type had to be inferred")
            },
            Self::ValueShapeMismatch { .. } => f.write_str("a value type had a wrong shape"),
            Self::ComputationShapeMismatch { .. } => {
                f.write_str("a computation type had a wrong shape")
            },
            Self::CodeObligationCeiling { .. } => {
                f.write_str("the deferred code obligations reached their ceiling")
            },
            Self::ValueTypeMismatch(_) => f.write_str("two value types are not convertible"),
            Self::ComputationTypeMismatch(_) => {
                f.write_str("two computation types are not convertible")
            },
            Self::CaseBranchMismatch(_) => {
                f.write_str("the two branches of a case produced inconvertible types")
            },
            Self::BinderEscape { .. } => {
                f.write_str("a type synthesized under a binder mentions the value it bound")
            },
            Self::LevelVariableOutOfScope { .. } => {
                f.write_str("a level variable escaped the declaration's prenex parameters")
            },
            Self::LevelArithmetic => f.write_str("level arithmetic left the representable range"),
            Self::UniverseViolation(_) => f.write_str("a universe judgement does not hold"),
            Self::InconsistentLevelConstraints(_) => {
                f.write_str("the declared level constraints have no model")
            },
            Self::LevelOracleFault(_) => f.write_str("the level oracle reported a fault"),
            Self::CheckerRegisterFault(_) => {
                f.write_str("the checker's produced register held the wrong polarity")
            },
            Self::ArenaFault => f.write_str("an arena id resolved to no node"),
            Self::AbstractTypeKindNotUniverse { .. } => {
                f.write_str("an abstract type's kind is not a universe")
            },
            Self::NotAnAbstractType { .. } => {
                f.write_str("a sealed-atom reference named no abstract-type declaration")
            },
            Self::SealNotOpen { .. } => {
                f.write_str("a seal named no abstract type whose minting admission is open")
            },
            Self::SealingProvenanceNotProjected { .. } => {
                f.write_str("a claimed sealing atom does not occur in the declared type")
            },
            Self::SealingProvenanceNotCanonical { .. } => {
                f.write_str("a sealing-provenance slot is not strictly ascending")
            },
            Self::OutstandingStagedContent { .. } => {
                f.write_str("a later staged declaration is still unresolved")
            },
            Self::StaticClassifierExpected { .. } => {
                f.write_str("a static Pi stands over a type that classifies no codes")
            },
        }
    }
}

impl core::error::Error for KernelError
{
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString;
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_kernel_check_memo::ContentDigest;
    use gandr_kernel_strata::LandmarkConstraint;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_strata::LevelVar;
    use gandr_kernel_strata::LevelVarIndex;
    use gandr_kernel_strata::PosetError;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LayerPosition;
    use gandr_kernel_term::LevelParamCount;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::TableEntryCount;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::ValueType;

    use super::CompTypeMismatch;
    use super::ExpectedComputationShape;
    use super::ExpectedValueShape;
    use super::KernelError;
    use super::NonInferableForm;
    use super::RegisterFault;
    use super::ValueTypeMismatch;
    use crate::element_identity::EndpointSide;
    use crate::element_identity::IdentityError;
    use crate::env::Environment;
    use crate::env::OutstandingCount;
    use crate::identity_recursion::Component;
    use crate::identity_recursion::EvaluationSide;
    use crate::levels::LevelContext;
    use crate::replay::KernelVerdict;
    use crate::witness::comp_type_witness;
    use crate::witness::value_type_witness;

    /// A formatter whose first write fails.
    struct RefusingSink;

    impl core::fmt::Write for RefusingSink
    {
        /// Refuses every offered write.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: returns the formatter's write error.
        /// - provides: an observable refusal at the formatter boundary.
        /// - fails: always, with `core::fmt::Error`.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 at the first write of every refusal class; exact
        ///   formatter errors distinguish swallowed write failures.
        /// - witness: `error::tests::refusal_descriptions_separate_classes_and_propagate_sink_failure`
        #[spec(ensures: |ret| ret == Err(core::fmt::Error))]
        fn write_str(
            &mut self,
            _s: &str,
        ) -> core::fmt::Result
        {
            Err(core::fmt::Error)
        }
    }

    #[test]
    fn refusal_descriptions_separate_classes_and_propagate_sink_failure()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit_returner = arena.comp_type_returner(unit);
        let integer_returner = arena.comp_type_returner(integer);
        let unit = value_type_witness(&arena, unit);
        let integer = value_type_witness(&arena, integer);
        let unit_returner = comp_type_witness(&arena, unit_returner);
        let integer_returner = comp_type_witness(&arena, integer_returner);
        let mismatch = CompTypeMismatch::new(unit_returner, integer_returner);
        let free = LevelContext::admit(LevelParamCount::from(0_u32), Vec::new())
            .expect("an unconstrained context admits");
        let universe = free
            .check_universe_below(&Level::zero(), &Level::zero())
            .expect_err("strict order is irreflexive");
        let variable = LevelVar::new(LevelVarIndex::from(0_u32));
        let level = Level::var(variable);
        let constraint =
            LandmarkConstraint::leq(level.succ().expect("one successor is representable"), level)
                .expect("a variable-only constraint is well formed");
        let inconsistent = LevelContext::admit(LevelParamCount::from(1_u32), vec![constraint])
            .expect_err("a self-successor constraint has no model");
        let index = ConstantIndex::from(usize::MAX);
        let cases = [
            KernelError::UnboundVariable {
                index: DeBruijnIndex::from(u32::MAX),
            },
            KernelError::UnboundConstant { index },
            KernelError::NotInferable {
                form: NonInferableForm::Injection,
            },
            KernelError::ValueShapeMismatch {
                expected: ExpectedValueShape::Product,
                actual: unit,
            },
            KernelError::ComputationShapeMismatch {
                expected: ExpectedComputationShape::Arrow,
                actual: unit_returner,
            },
            KernelError::CodeObligationCeiling {
                ceiling: TableEntryCount::from(usize::MAX),
            },
            KernelError::ValueTypeMismatch(ValueTypeMismatch::new(unit, integer)),
            KernelError::ComputationTypeMismatch(mismatch),
            KernelError::CaseBranchMismatch(mismatch),
            KernelError::BinderEscape {
                actual: unit_returner,
            },
            KernelError::LevelVariableOutOfScope { variable },
            KernelError::LevelArithmetic,
            universe,
            inconsistent,
            KernelError::LevelOracleFault(PosetError::Overflow),
            KernelError::CheckerRegisterFault(RegisterFault::ExpectedValueType),
            KernelError::ArenaFault,
            KernelError::AbstractTypeKindNotUniverse { actual: unit },
            KernelError::NotAnAbstractType { index },
            KernelError::SealNotOpen { index },
            KernelError::SealingProvenanceNotProjected { atom: index },
            KernelError::SealingProvenanceNotCanonical { atom: index },
            KernelError::OutstandingStagedContent {
                above: OutstandingCount::from(usize::MAX),
            },
            KernelError::StaticClassifierExpected { actual: unit },
            KernelError::Identity(IdentityError::OutsideFold(unit)),
            KernelError::Identity(IdentityError::EndpointsDiffer {
                left: ContentDigest::default(),
                right: ContentDigest::default(),
                side: EndpointSide::Left,
                verdict: KernelVerdict::NotConvertible,
            }),
            KernelError::Identity(IdentityError::RelatedEndpointsDiffer {
                left: ContentDigest::default(),
                right: ContentDigest::default(),
                verdict: KernelVerdict::NotConvertible,
            }),
            KernelError::Identity(IdentityError::NeutralFibre),
            KernelError::Identity(IdentityError::EmptyFibre),
            KernelError::Identity(IdentityError::HigherFieldRequired),
            KernelError::Identity(IdentityError::HigherEvaluationRequired),
            KernelError::Identity(IdentityError::RecursiveObservation),
            KernelError::Identity(IdentityError::CertificateOperation),
            KernelError::Identity(IdentityError::Boundary),
            KernelError::Identity(IdentityError::ZeroDepth),
            KernelError::Identity(IdentityError::NonProductive(LayerPosition(0))),
            KernelError::Identity(IdentityError::DepthBound),
            KernelError::Identity(IdentityError::UnknownLayer(LayerPosition(0))),
            KernelError::Identity(IdentityError::GuardEvidence),
            KernelError::Identity(IdentityError::Coverage),
            KernelError::Identity(IdentityError::CoverageBudget),
            KernelError::Identity(IdentityError::Evaluation {
                component: Component(0),
                side: EvaluationSide::Left,
                verdict: KernelVerdict::NotConvertible,
            }),
            KernelError::Identity(IdentityError::OpenFunctions),
            KernelError::Identity(IdentityError::ReturnedNonReturner(unit_returner)),
            KernelError::Identity(IdentityError::NotOver {
                expected: unit,
                actual: unit,
            }),
            KernelError::Identity(IdentityError::BridgeAtSealedType(unit)),
        ];
        let descriptions = cases.each_ref().map(ToString::to_string);
        for (position, description) in descriptions.iter().enumerate() {
            for other in descriptions.iter().skip(position.saturating_add(1)) {
                assert_ne!(
                    description, other,
                    "different refusal classes remain distinguishable"
                );
            }
        }
        for error in cases {
            assert_eq!(
                core::fmt::write(&mut RefusingSink, format_args!("{error}")),
                Err(core::fmt::Error)
            );
        }
    }

    #[test]
    fn universe_successor_overflow_refuses_admission_without_truncating_prior_content()
    {
        let mut environment = Environment::new();
        let (unit, first) = {
            let mut staging = environment.stage();
            let unit = staging.arena().value_type_unit();
            (unit, staging.axiom(LevelSignature::monomorphic(), unit))
        };
        assert_eq!(
            environment
                .add_decl(first)
                .expect("the unit type forms")
                .position(),
            ConstantIndex::from(0_usize)
        );
        for sort in [GroundSort::Value, GroundSort::Computation] {
            let position = ConstantIndex::from(environment.entries().len());
            let admitted = {
                let mut staging = environment.stage();
                let declared = staging.arena().value_type_universe(
                    sort,
                    Level::constant(LevelConstant::from(u64::MAX.saturating_sub(1))),
                );
                staging.axiom(LevelSignature::monomorphic(), declared)
            };
            assert_eq!(
                environment
                    .add_decl(admitted)
                    .expect("the successor fits")
                    .position(),
                position
            );
            let watermark = environment.arena().watermark();
            let entries = environment.entries().len();
            let refused = {
                let mut staging = environment.stage();
                let declared = staging
                    .arena()
                    .value_type_universe(sort, Level::constant(LevelConstant::from(u64::MAX)));
                staging.axiom(LevelSignature::monomorphic(), declared)
            };
            assert_eq!(
                environment.add_decl(refused),
                Err(KernelError::LevelArithmetic)
            );
            assert_eq!(environment.arena().watermark(), watermark);
            assert_eq!(environment.entries().len(), entries);
            assert_eq!(
                environment.arena().value_type(unit),
                Some(&ValueType::unit())
            );
        }
    }
}
