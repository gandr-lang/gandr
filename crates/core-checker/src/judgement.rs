//! The judgement: four directed faces over one machine, which also runs type
//! formation.
//!
//! # The former decides the mode
//!
//! Every term former but the bind and the pair has one mode. Leaves and
//! eliminations synthesise — their type is read out of the context, the
//! signature table, an atom, the type they quote, or the type of the term
//! they eliminate — and introductions check against a type handed in,
//! because nothing in an introduction alone fixes its type:
//!
//! |Former|Mode|Rule|
//! |---|---|---|
//! |variable|synthesise|the type its binder declared, shifted past the binders opened since|
//! |constant|synthesise|the type its declaration supplied|
//! |unit, integer and string literal|synthesise|the atom|
//! |quote `⌜A⌝`, `⌜C⌝`|synthesise|the quoted type is formed; the quote has the universe of its family's sort at the type's level|
//! |thunk|check against `U C`|its body checks against `C`|
//! |force|synthesise|the forced value synthesises `U C`; the force has `C`|
//! |application|synthesise|the head synthesises `A → C` or `(x : A) → C`, the argument checks against `A`; the application has `C`, instantiated at the argument for the dependent arrow; an argument at a static Pi must not normalize away|
//! |bind|either|the bound computation synthesises `F A`; opens a binder of `A`; the body is judged in the bind's own mode, and the bind has what the body has, lowered out of the binder|
//! |pair|either|synthesising, each component synthesises and the pair has their eager product; checking against `A × B`, each component checks against its factor|
//! |lambda|check against `A → C` or `(x : A) → C`|opens a binder of `A`; the body checks against `C`|
//! |static lambda|check against a static Pi `K ⇒ J`|opens a binder of `K`; the body checks against `J`|
//! |static application|synthesise|the head synthesises one static Pi per argument; each argument checks against its Pi's domain; the application has the last codomain|
//! |return|check against `F A`|the value checks against `A`|
//!
//! A bind and a pair are the formers of either mode. A bind eliminates the
//! returner its bound computation synthesises, so that half synthesises, and
//! it hands its type through from its body, so the body is judged in
//! whichever mode the bind was asked for. A bound computation that only
//! checks — a bare `return` — is refused as not synthesisable rather than
//! given a guessed type, and a body type that mentions the bound name is
//! refused as a dependent bind: the binder is opaque to types, so that type
//! has no reading outside it. A pair synthesises when every component does
//! and checks component-wise otherwise, so a thunk stands in a pair checked
//! against a product.
//!
//! A synthesising term in checking position synthesises, then its type crosses
//! the conversion boundary to the expected type; that is the only place a
//! type meets a type. A checking form in synthesis position is refused, naming
//! the form: the judgement never guesses a type an introduction did not
//! carry.
//!
//! # Static operators
//!
//! A static application past its head's static Pis is refused as
//! [`CheckRefusal::FamilyArity`], naming both counts; an argument whose
//! classifier does not cross to its domain as
//! [`CheckRefusal::FamilyArgumentClassifier`], naming its position and both
//! classifiers, so a sort or level mismatch reads as the family's. A static
//! lambda, or a static definition, handed to a static parameter normalizes
//! away before the kernel sees it; handed to a dynamic one it would be a value
//! the kernel types, which no kernel former is, so it is refused as
//! [`CheckRefusal::StaticLambdaArgument`]. An opaque operator is a value the
//! kernel types, and passes.
//!
//! # Types are read at their weak head
//!
//! Every rule that reads the former of a type — a thunk checked against it, a
//! head applied at it, a returner bound — reads it at its weak head first, so
//! `El Num` for `def Num : Type = U (F Integer)` is a thunk type to a thunk.
//! The unfolding is the context's: the normaliser's conversion certifies each
//! step and the constant is logged as consulted.
//!
//! # Formation is goals of the same machine
//!
//! A type is formed by goals beside the term goals: a decode `El c` asks for
//! the synthesis of `c`, which may itself form a quoted type, and a dependent
//! arrow forms its codomain under a binder of its domain. Running both in one
//! machine keeps the judgement free of recursion between the two and charges
//! both to one allowance.
//!
//! # One machine, no recursion
//!
//! The four faces and formation all run [`Machine`]: an explicit goal and a
//! stack of frames, one step per transition, charged against the context's
//! allowance. A term as deep as memory holds is judged without a native
//! stack, and the allowance bounds the run whatever sharing the term has.
//!
//! # A shared subterm is judged per occurrence
//!
//! The machine keeps no memo: a subterm reached twice is judged twice. The
//! fragment's terms are what a lowering produced from source text, whose
//! sharing is the author's repetition, and the allowance bounds the rest. A
//! memo keyed by node and context is the upgrade when a producer starts
//! sharing aggressively.
//!
//! # A hole and a mark are judged without their contents
//!
//! A term hole checks against any type and synthesises the unknown type, as
//! Hazelnut's empty hole does (Omar et al., POPL 2017,
//! doi:10.1145/3009837.3009900). A mark is Hazelnut's non-empty hole: it
//! records a refusal its body already met, so its body is not judged again,
//! and it checks and synthesises as a hole does. A rule that demands a
//! former of an expected or a synthesised type reads it through the matched
//! operations of `gandr_core_term::hole`: the unknown type matches every
//! former with unknown components, so an introduction checked against it and
//! an elimination of a term that synthesised it both go on, and conversion
//! treats the unknown as consistent with every type. A path's endpoints and a
//! nominal type's constructors are read off the type itself, so a transport
//! or a native case over the unknown type is refused, and a total elaboration
//! marks it.
//!
//! # A refusal leaves the context as it found it
//!
//! A refused run closes every binder it opened before it returns, so the
//! next judgement in the same context starts where this one did.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::ContextError;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::CodomainScope;
use gandr_core_term::hole::matched_function;
use gandr_core_term::hole::matched_list;
use gandr_core_term::hole::matched_product;
use gandr_core_term::hole::matched_returner;
use gandr_core_term::hole::matched_stack;
use gandr_core_term::hole::matched_static_pi;
use gandr_core_term::hole::matched_sum;
use gandr_core_term::hole::matched_thunk;
use gandr_core_term::hole::matched_with;
use gandr_core_term::hole::matching;
use gandr_core_term::instantiate_comp_type;
use gandr_core_term::shift_comp_type;
use gandr_core_term::shift_value_type;
use gandr_core_term::strengthen_comp_type;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use crate::context::Atom;
use crate::context::CheckingContext;
use crate::conversion::ConversionCount;
use crate::conversion::comp_bridge;
use crate::conversion::decode_bridge;
use crate::conversion::value_bridge;
use crate::formation::FormedCompType;
use crate::formation::FormedValueType;
use crate::formation::level_of;
use crate::refusal::ArgumentPosition;
use crate::refusal::CheckRefusal;
use crate::refusal::CheckingForm;
use crate::refusal::CoreNode;
use crate::refusal::ExpectedShape;
use crate::refusal::StaticArity;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

mod elaboration;
mod native;

use self::elaboration::Anchor;
pub use self::elaboration::Elaboration;
pub use self::elaboration::MarkEntry;
use self::elaboration::Marking;
pub use self::elaboration::Pending;
pub use self::elaboration::elaborate_comp;
pub use self::elaboration::elaborate_value;
pub use self::elaboration::pending;
pub use self::elaboration::trace_value;

/// The direction a judgement runs in.
///
/// # Judgement
/// - direction: synthesis hands the term's type out; checking takes the
///   expected type in. A dispatch on it names both, so a rule added in one mode
///   is a compile error in every dispatch that forgot the other.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Direction<Expected>
{
    /// The term's type is read off the term.
    Synthesise,
    /// The term is checked against the type held.
    Check(Expected),
}

/// A type a judgement synthesised, beside the evidence of how it got there.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Synthesised<Type>
{
    /// The type.
    produced: Type,
    /// The conversions the run made.
    conversions: ConversionCount,
}

impl<Type: Copy> Synthesised<Type>
{
    /// The type synthesised.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn produced(&self) -> Type
    {
        self.produced
    }

    /// How many times the run crossed the conversion boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn conversions(&self) -> ConversionCount
    {
        self.conversions
    }
}

/// The evidence a check succeeded with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Checked
{
    /// The conversions the run made.
    conversions: ConversionCount,
}

impl Checked
{
    /// How many times the run crossed the conversion boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn conversions(&self) -> ConversionCount
    {
        self.conversions
    }
}

/// Synthesise the type of `value`.
///
/// # Specification
/// - requires: `value` is closed over the context's binders, which are empty
///   between judgements.
/// - ensures: the formed type `value` has by the synthesis rule of its former,
///   the checks of its subterms done by their rules.
/// - provides: the conversions the run made, as [`Synthesised::conversions`].
/// - fails: [`CheckRefusal::NotSynthesisable`] for a thunk; otherwise any
///   refusal a reached rule gives — see the vocabulary.
/// - panics: none.
/// - intension: the conversion count is the declared projection of the run's
///   crossings of the boundary.
///
/// # Errors
/// - [`CheckRefusal`] — the term has no type in the fragment, or the run hit
///   the allowance or a dangling id.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the per-former rule table in
///   synthesis mode, separated by one term of every value former, each asserted
///   to synthesise its exact type or refuse with its exact refusal; the free
///   generator pins the faces against each other by property.
/// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
/// - witness: `judgement::tests::the_faces_agree_on_free_terms`
/// - witness: `judgement::tests::well_typed_terms_synthesise_and_check_their_type`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth && match ret {
        | Ok(synthesised) => context.arena().value_type(synthesised.produced().id()).is_some()
            && usize::from(synthesised.conversions()) <= usize::from(context.budget()),
        | Err(_) => true,
    },
)]
#[inline]
pub fn synthesise_value(
    context: &mut CheckingContext<'_>,
    value: ValueId,
) -> Result<Synthesised<FormedValueType>, CheckRefusal>
{
    let (produced, conversions) = Machine::run(context, Goal::Value {
        term: value,
        direction: Direction::Synthesise,
    })?;
    match produced {
        | Produced::ValueType(produced) => Ok(Synthesised {
            produced: FormedValueType::derived(produced),
            conversions,
        }),
        | Produced::CompType(_) | Produced::Checked => Err(CheckRefusal::MachineInvariant),
    }
}

/// Check `value` against `expected`.
///
/// # Specification
/// - requires: `value` is closed over the context's binders, which are empty
///   between judgements.
/// - ensures: success exactly when the check rule of `value`'s former accepts
///   `expected`; for a synthesising former, exactly when its synthesised type
///   converts to `expected`.
/// - provides: the conversions the run made, as [`Checked::conversions`].
/// - fails: [`CheckRefusal::ShapeMismatch`] for a thunk checked against a type
///   that is no thunk type; [`CheckRefusal::TypeMismatch`] for a synthesising
///   value whose type does not convert; otherwise any refusal a reached rule
///   gives.
/// - panics: none.
/// - intension: the conversion count is the declared projection of the run's
///   crossings of the boundary.
///
/// # Errors
/// - [`CheckRefusal`] — the term does not have `expected`, or the run hit the
///   allowance or a dangling id.
///
/// # Judgement
/// - expected: `expected`
///
/// # Adequacy
/// - hypothesis: L3 — the per-former rule table in checking mode, separated as
///   for [`synthesise_value`], plus a mismatching literal and a thunk against
///   the wrong former.
/// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
/// - witness: `judgement::tests::a_mismatched_literal_is_refused_with_both_types`
/// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
/// - witness: `judgement::tests::the_faces_agree_on_free_terms`
/// - witness: `judgement::tests::well_typed_terms_synthesise_and_check_their_type`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth
        && ret.as_ref().is_ok_and(|checked| usize::from(checked.conversions()) <= usize::from(context.budget())) == ret.is_ok(),
)]
#[inline]
pub fn check_value(
    context: &mut CheckingContext<'_>,
    value: ValueId,
    expected: FormedValueType,
) -> Result<Checked, CheckRefusal>
{
    let (produced, conversions) = Machine::run(context, Goal::Value {
        term: value,
        direction: Direction::Check(expected.id()),
    })?;
    checked(produced, conversions)
}

/// Synthesise the type of `computation`.
///
/// # Specification
/// - requires: `computation` is closed over the context's binders, which are
///   empty between judgements.
/// - ensures: the formed type `computation` has by the synthesis rule of its
///   former.
/// - provides: the conversions the run made, as [`Synthesised::conversions`].
/// - fails: [`CheckRefusal::NotSynthesisable`] for a lambda or a return;
///   [`CheckRefusal::ShapeMismatch`] for a force of a value of no thunk type,
///   an application whose head has no arrow type, or a bind whose bound
///   computation has no returner type; otherwise any refusal a reached rule
///   gives.
/// - panics: none.
/// - intension: the conversion count is the declared projection of the run's
///   crossings of the boundary.
///
/// # Errors
/// - [`CheckRefusal`] — the term has no type in the fragment, or the run hit
///   the allowance or a dangling id.
///
/// # Adequacy
/// - hypothesis: L3 — the per-former rule table over computations in synthesis
///   mode, separated by one term of every computation former and the two
///   elimination shape refusals.
/// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
/// - witness: `judgement::tests::an_elimination_of_the_wrong_former_is_a_shape_mismatch`
/// - witness: `judgement::tests::a_bind_synthesises_its_continuations_type`
/// - witness: `judgement::tests::a_bind_of_a_non_returner_is_a_shape_mismatch`
/// - witness: `judgement::tests::the_faces_agree_on_free_terms`
/// - witness: `judgement::tests::well_typed_terms_synthesise_and_check_their_type`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth && match ret {
        | Ok(synthesised) => context.arena().comp_type(synthesised.produced().id()).is_some()
            && usize::from(synthesised.conversions()) <= usize::from(context.budget()),
        | Err(_) => true,
    },
)]
#[inline]
pub fn synthesise_comp(
    context: &mut CheckingContext<'_>,
    computation: ComputationId,
) -> Result<Synthesised<FormedCompType>, CheckRefusal>
{
    let (produced, conversions) = Machine::run(context, Goal::Computation {
        term: computation,
        direction: Direction::Synthesise,
    })?;
    match produced {
        | Produced::CompType(produced) => Ok(Synthesised {
            produced: FormedCompType::derived(produced),
            conversions,
        }),
        | Produced::ValueType(_) | Produced::Checked => Err(CheckRefusal::MachineInvariant),
    }
}

/// Check `computation` against `expected`.
///
/// # Specification
/// - requires: `computation` is closed over the context's binders, which are
///   empty between judgements.
/// - ensures: success exactly when the check rule of the former accepts
///   `expected`; for a synthesising former, exactly when its synthesised type
///   converts to `expected`.
/// - provides: the conversions the run made, as [`Checked::conversions`].
/// - fails: [`CheckRefusal::ShapeMismatch`] for a lambda against no arrow, a
///   return against no returner, or a bind whose bound computation has no
///   returner type; [`CheckRefusal::TypeMismatch`] for a synthesising
///   computation whose type does not convert; otherwise any refusal a reached
///   rule gives.
/// - panics: none.
/// - intension: the conversion count is the declared projection of the run's
///   crossings of the boundary.
///
/// # Errors
/// - [`CheckRefusal`] — the term does not have `expected`, or the run hit the
///   allowance or a dangling id.
///
/// # Judgement
/// - expected: `expected`
///
/// # Adequacy
/// - hypothesis: L3 — the per-former rule table over computations in checking
///   mode, separated by one term of every computation former, the two
///   introduction shape refusals and a mismatching application.
/// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
/// - witness: `judgement::tests::a_mismatched_application_is_refused_at_the_computation_bridge`
/// - witness: `judgement::tests::a_bind_checks_against_the_expected_computation`
/// - witness: `judgement::tests::a_bind_of_a_non_returner_is_a_shape_mismatch`
/// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
/// - witness: `judgement::tests::well_typed_terms_synthesise_and_check_their_type`
/// - witness: `judgement::tests::the_faces_agree_on_free_terms`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth
        && ret.as_ref().is_ok_and(|checked| usize::from(checked.conversions()) <= usize::from(context.budget())) == ret.is_ok(),
)]
#[inline]
pub fn check_comp(
    context: &mut CheckingContext<'_>,
    computation: ComputationId,
    expected: FormedCompType,
) -> Result<Checked, CheckRefusal>
{
    let (produced, conversions) = Machine::run(context, Goal::Computation {
        term: computation,
        direction: Direction::Check(expected.id()),
    })?;
    checked(produced, conversions)
}

/// The evidence of a check run that produced `produced`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Checked`] carrying `conversions` when the run ended on a check.
/// - fails: [`CheckRefusal::MachineInvariant`] when a check run produced a
///   type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a check result and both type-result families expose check
///   evidence or the exact machine fault; public checking also observes the
///   retained conversion count.
/// - witness: `judgement::tests::a_result_of_the_wrong_kind_is_a_machine_fault`
/// - witness: `judgement::tests::a_two_bridge_check_crosses_the_boundary_twice`
#[spec(ensures: |ret| match produced {
    | Produced::Checked => ret.is_ok(),
    | Produced::ValueType(_) | Produced::CompType(_) => matches!(ret, Err(CheckRefusal::MachineInvariant)),
})]
const fn checked(
    produced: Produced,
    conversions: ConversionCount,
) -> Result<Checked, CheckRefusal>
{
    match produced {
        | Produced::Checked => Ok(Checked { conversions }),
        | Produced::ValueType(_) | Produced::CompType(_) => Err(CheckRefusal::MachineInvariant),
    }
}

/// Form `node` in the context's binders: the goal [`crate::formation`]'s faces
/// run.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when every node `node` reaches has a formation
///   rule that accepts it, as [`crate::formation::form_value_type`] states.
/// - fails: the first refusal a formation rule or a code's judgement gives.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — the type is not formed.
///
/// # Adequacy
/// - hypothesis: L1 over bounded generated type programs compares the exact
///   classifier, with L3 every admitted or refused former and a dangling node;
///   wrong formation decisions and scope leakage change those observations.
/// - witness: `formation::tests::every_type_has_exactly_one_classifier`
/// - witness: `formation::tests::every_value_type_constructor_has_a_formation_rule`
/// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: context.depth(Zone::Intuitionistic) == depth,
)]
pub fn form(
    context: &mut CheckingContext<'_>,
    node: TypeNode,
) -> Result<(), CheckRefusal>
{
    let (produced, conversions) = Machine::run(context, Goal::Form(node))?;
    checked(produced, conversions).map(|_| ())
}

/// The fixed endpoints of a forward stack-typing judgment.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct StackJudgement
{
    /// The source stack literal.
    at: ValueId,
    /// The caller's expected stack classifier.
    expected: ValueTypeId,
    /// The original consumed computation type.
    consumed: CompTypeId,
}

/// A position in a stack literal's frames or a handler's clauses, counted
/// from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Ordinal(usize);

impl Ordinal
{
    /// The first frame or clause.
    const FIRST: Self = Self(0);

    /// The position after this one.
    ///
    /// # Specification
    /// - ensures: the successor position.
    /// - fails: [`CheckRefusal::MachineInvariant`] past the largest position,
    ///   which no arena-held list reaches.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a multi-frame stack and a multi-clause handler visit
    ///   each element once and in order; a skipped or repeated position changes
    ///   the observed rows and binders.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    /// - witness: `judgement::tests::handlers_discharge_only_their_own_interface`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|next| next.0 == self.0.wrapping_add(1)))]
    fn next(self) -> Result<Self, CheckRefusal>
    {
        self.0
            .checked_add(1)
            .map(Self)
            .ok_or(CheckRefusal::MachineInvariant)
    }
}

/// A judgement the machine is to run.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Goal
{
    /// Advance one frame of a first-class stack.
    Stack
    {
        /// The source and fixed endpoint of the judgment.
        judgement: StackJudgement,
        /// The next source frame.
        position: Ordinal,
        /// The type delivered by the preceding frames.
        input: CompTypeId,
    },
    /// Judge a value.
    Value
    {
        /// The value.
        term: ValueId,
        /// The direction, holding the expected value type when checking.
        direction: Direction<ValueTypeId>,
    },
    /// Judge a computation.
    Computation
    {
        /// The computation.
        term: ComputationId,
        /// The direction, holding the expected computation type when checking.
        direction: Direction<CompTypeId>,
    },
    /// Form a type; a formed type ends in [`Produced::Checked`].
    Form(TypeNode),
}

/// What a finished judgement hands to the frame awaiting it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Produced
{
    /// A synthesised value type.
    ValueType(ValueTypeId),
    /// A synthesised computation type.
    CompType(CompTypeId),
    /// A check that succeeded, or a type formed.
    Checked,
}

/// The codomain an application has once its argument checks.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Codomain
{
    /// An arrow's: the application has it as it stands.
    Ambient(CompTypeId),
    /// A dependent arrow's, scoped under the argument's binder: the application
    /// has it instantiated at the argument.
    Dependent(CompTypeId),
}

/// The completed premise of a native List fold rule.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ListPhase
{
    /// The element annotation is formed.
    Element,
    /// The result annotation is formed.
    Result,
    /// The list checks at its annotated element type.
    Input,
    /// The nil branch checks in the ambient context.
    Nil,
    /// The cell branch checks under its two binders.
    Cons,
}

/// A rule waiting on the judgement of one of its subterms.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Frame
{
    /// Continue a native premise after the previous premise succeeded.
    NativeNext(Goal),
    /// Publish the native judgment after all its premises succeeded.
    NativeYield(Produced),
    /// Retain a synthesized field type in the flat native result stack.
    NativeCollect,
    /// An extra record field was typed but does not contribute to the expected
    /// type.
    NativeDiscard,
    /// Assemble a record's exact inferred field types.
    NativeRecord
    {
        /// The source record supplies labels.
        term: ValueId,
        /// The result-stack suffix owned by this record.
        base: usize,
    },
    /// Await the case scrutinee's nominal classifier.
    NativeCase(ComputationId),
    /// Await formation under the case's one motive binder.
    NativeMotive
    {
        /// The case.
        term: ComputationId,
        /// Its scrutinee classifier.
        datatype: ValueTypeId,
    },
    /// Await a projection operand's record classifier.
    NativeProjection(ComputationId),
    /// Check an operation payload after forming its interface.
    PerformPayload
    {
        /// The supplied payload.
        payload: ValueId,
        /// Its interface classifier.
        expected: ValueTypeId,
        /// The singleton-row result.
        result: CompTypeId,
    },
    /// Continue with another checking premise.
    Next(Goal),
    /// Read a resumption's stack classifier.
    Resume
    {
        /// The first-class stack.
        stack: ValueId,
        /// The computation fed to it.
        body: ComputationId,
    },
    /// Select one component of a synthesized lazy pair.
    Project
    {
        /// The projection.
        at: ComputationId,
        /// The selected component.
        side: gandr_kernel_term::Side,
    },
    /// The nearest answer delimiter, retained while checking its body.
    Reset
    {
        /// Its answer in the delimiter's scope.
        answer: CompTypeId,
        /// The scope in which the answer was formed.
        depth: BinderDepth,
    },
    /// Infer a handler's subject after forming the carried interface.
    HandlerForm
    {
        /// The handler.
        at: ComputationId,
        /// Its answer type.
        answer: CompTypeId,
        /// The formed interface carrier.
        interface: CompTypeId,
    },
    /// Read the subject's result and residual effects.
    HandlerSubject
    {
        /// The handler.
        at: ComputationId,
        /// Its answer type.
        answer: CompTypeId,
        /// The formed interface carrier.
        interface: CompTypeId,
    },
    /// Close the return-clause binder and check the operation clauses.
    HandlerReturn
    {
        /// The handler.
        at: ComputationId,
        /// Its ambient answer type.
        answer: CompTypeId,
    },
    /// Close one operation clause's payload and resumption binders.
    HandlerClause
    {
        /// The handler.
        at: ComputationId,
        /// Its ambient answer type.
        answer: CompTypeId,
        /// The next clause.
        position: Ordinal,
    },
    /// Continue a stack after its current frame synthesizes an output.
    StackNext
    {
        /// The source and fixed endpoints.
        judgement: StackJudgement,
        /// The next source frame.
        position: Ordinal,
    },
    /// Strengthen a stack bind's body and accumulate its consumed row.
    StackBind
    {
        /// The source stack literal.
        at: ValueId,
        /// The body, for row diagnostics.
        body: ComputationId,
        /// The consumed returner in the ambient scope.
        bound: CompTypeId,
    },
    /// Await a pure native List fold premise.
    ListFold
    {
        /// The source fold.
        at: ComputationId,
        /// Its ambient pure returner classifier.
        result: CompTypeId,
        /// The premise just checked.
        phase: ListPhase,
    },
    /// Await the first component path.
    PathProductFirst
    {
        /// The first path.
        at: ValueId,
        /// The second path.
        second: ValueId,
    },
    /// Await the second component path.
    PathProductSecond
    {
        /// The second path.
        at: ValueId,
        /// The first source.
        source: ValueTypeId,
        /// The first target.
        target: ValueTypeId,
    },
    /// Check the inverse after the forward map.
    PathBackward
    {
        /// The inverse map.
        backward: ValueId,
        /// The source type.
        source: ValueTypeId,
        /// The target type.
        target: ValueTypeId,
        /// The certificate classifier.
        path_type: ValueTypeId,
    },
    /// Finish a native certificate after both maps check.
    PathChecked
    {
        /// The certificate classifier.
        path_type: ValueTypeId,
    },
    /// Check the second argument of a saturated native operation.
    PrimitiveSecond
    {
        /// The second argument.
        argument: ValueId,
        /// Its table-declared classifier.
        expected: ValueTypeId,
        /// The operation's returner type.
        result: CompTypeId,
    },
    /// Complete a native operation after its arguments checked.
    PrimitiveResult
    {
        /// The operation's returner type.
        result: CompTypeId,
    },
    /// Await the path classifier.
    TransportPath
    {
        /// The path.
        path: ValueId,
        /// The transported operand.
        value: ValueId,
    },
    /// Await the source operand check.
    TransportOperand
    {
        /// The target returner.
        result: CompTypeId,
    },
    /// Await the sum scrutinee classifier.
    CaseScrutinee
    {
        /// The scrutinee.
        scrutinee: ValueId,
        /// The left branch.
        on_left: ComputationId,
        /// The right branch.
        on_right: ComputationId,
        /// The common result type.
        expected: CompTypeId,
    },
    /// Close the left binder and check the right branch.
    CaseRight
    {
        /// The right branch.
        on_right: ComputationId,
        /// The right summand.
        right: ValueTypeId,
        /// The common result type under one binder.
        expected: CompTypeId,
    },
    /// A force waits on the type its value synthesises, which must be a thunk
    /// type; the force has the thunk's body.
    Force
    {
        /// The forced value.
        value: ValueId,
    },
    /// An application waits on the type its head synthesises, which must be an
    /// arrow or a dependent arrow; the argument then checks against the
    /// domain.
    ApplicationHead
    {
        /// The head.
        head: ComputationId,
        /// The argument still to check.
        argument: ValueId,
    },
    /// An application waits on its argument's check; an argument at a static
    /// Pi must then be rigid, and the application has the codomain.
    ApplicationArgument
    {
        /// The argument, which a dependent codomain is instantiated at.
        argument: ValueId,
        /// The domain the argument checked against.
        domain: ValueTypeId,
        /// The codomain.
        codomain: Codomain,
    },
    /// A lambda waits on its body's check, then closes the binder it opened.
    LambdaBody,
    /// A bind waits on the type its bound computation synthesises, which must
    /// be a returner; it then opens a binder of the returned type and judges
    /// its body in the bind's own direction.
    BindBound
    {
        /// The bind.
        at: ComputationId,
        /// The bound computation.
        bound: ComputationId,
        /// The body still to judge.
        body: ComputationId,
        /// The bind's own direction, which the body takes.
        direction: Direction<CompTypeId>,
    },
    /// A bind waits on its body's judgement, then closes the binder it opened
    /// and hands the body's result on, a synthesised type lowered out of the
    /// binder.
    BindBody
    {
        /// The bind.
        at: ComputationId,
        /// The bound returner's type, in the ambient context.
        bound: CompTypeId,
    },
    /// A synthesising value in checking position waits on its synthesised type,
    /// which then crosses the value bridge.
    ValueBridge
    {
        /// The value.
        at: ValueId,
        /// The type it is checked against.
        expected: ValueTypeId,
    },
    /// A synthesising computation in checking position waits on its
    /// synthesised type, which then crosses the computation bridge.
    CompBridge
    {
        /// The computation.
        at: ComputationId,
        /// The type it is checked against.
        expected: CompTypeId,
    },
    /// A quote waits on the formation of the type it quotes; it then has the
    /// universe at that type's level.
    Quote(TypeNode),
    /// A former waits on the formation of one child; the next is formed then.
    FormNext(TypeNode),
    /// A dependent arrow waits on its domain's formation; it then forms its
    /// codomain under a binder of the domain.
    FormPi
    {
        /// The domain.
        domain: ValueTypeId,
        /// The codomain, scoped under the domain's binder.
        codomain: CompTypeId,
    },
    /// A dependent arrow waits on its codomain's formation, then closes the
    /// binder it opened.
    FormBinder,
    /// A lift waits on its type's formation; its target must then lie above
    /// the type's level.
    FormLift(ValueTypeId),
    /// A decode waits on the type its code synthesises, which then crosses the
    /// decode bridge.
    FormElement(TypeNode),
    /// A static Pi waits on the formation of both its classifiers; each must
    /// then be a static classifier — a universe or a static Pi — at its weak
    /// head.
    FormStaticPi(ValueTypeId),
    /// A pair checked against an eager product waits on its first
    /// component's check; the second then checks against the second factor.
    PairSecond
    {
        /// The second component.
        second: ValueId,
        /// The second factor.
        expected: ValueTypeId,
    },
    /// A synthesised pair waits on its first component's type; the second
    /// component then synthesises.
    PairFirstSynthesised
    {
        /// The second component.
        second: ValueId,
    },
    /// A synthesised pair waits on its second component's type; the pair
    /// then has the eager product of both.
    PairSecondSynthesised
    {
        /// The first component's type.
        first: ValueTypeId,
    },
    /// A static application waits on the type its head so far synthesises,
    /// which must be a static Pi; the argument at `position` then meets its
    /// domain.
    StaticSpine
    {
        /// The whole application.
        at: ValueId,
        /// How many arguments stand before this one.
        position: ArgumentPosition,
        /// The argument.
        argument: ValueId,
        /// How many arguments the application spine applies.
        spine: StaticArity,
    },
    /// A static application's argument waits on its synthesised type, which
    /// then crosses the value bridge to the domain; the application so far
    /// has the codomain.
    StaticArgument
    {
        /// The argument.
        argument: ValueId,
        /// How many arguments stand before this one.
        position: ArgumentPosition,
        /// The static Pi's domain.
        domain: ValueTypeId,
        /// The static Pi's codomain.
        codomain: ValueTypeId,
    },
    /// A static application's static-lambda argument waits on its check
    /// against the domain; the application so far has the codomain.
    StaticOperand
    {
        /// The static Pi's codomain.
        codomain: ValueTypeId,
    },
    /// A total run checked a term that could not synthesise against the
    /// unknown type; the term synthesises the unknown type of its family.
    Unknowing(TermNode),
}

/// The machine's next move.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Step
{
    /// Start a judgement.
    Descend(Goal),
    /// Hand a finished judgement's result to the innermost frame.
    Ascend(Produced),
}

/// One run of the judgement: the context, the frames, the conversions made
/// and the allowance left; in a total run, the terms it would recover at and
/// the refusals it marked.
struct Machine<'context, 'arena>
{
    /// The context the run reads and goes under binders in.
    context: &'context mut CheckingContext<'arena>,
    /// The rules waiting on subterms, innermost last.
    frames: Vec<Frame>,
    /// Inferred record field types; nested records own separate suffixes.
    native_types: Vec<ValueTypeId>,
    /// The crossings of the conversion boundary so far.
    conversions: ConversionCount,
    /// The steps left before the run refuses.
    remaining: usize,
    /// Whether a refusal ends the run or marks the term it stands at.
    marking: Marking,
    /// The term judgements under way, innermost last; empty in a strict run.
    anchors: Vec<Anchor>,
    /// The refusals a total run marked, in the order met.
    marks: Vec<MarkEntry>,
}

impl<'context, 'arena> Machine<'context, 'arena>
{
    /// Read the two endpoints of a first-class stack classifier.
    ///
    /// # Specification
    /// - ensures: success returns the weak-head stack's input and output, or
    ///   two unknown computation types when the classifier is unknown.
    /// - fails: a shape mismatch names the original value and classifier.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — differing endpoints and a non-stack separate the
    ///   rule; the unknown type reads as a stack of unknowns.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret { Err(CheckRefusal::ShapeMismatch { at: site, wanted, found }) => site == TermNode::Value(at) && wanted == ExpectedShape::Stack && found == TypeNode::Value(classifier), Ok((input, output)) => self.context.arena().comp_type(input).is_some() && self.context.arena().comp_type(output).is_some(), Err(_) => true })]
    fn stack_expected(
        &mut self,
        at: ValueId,
        classifier: ValueTypeId,
    ) -> Result<(CompTypeId, CompTypeId), CheckRefusal>
    {
        let head = self.context.whnf_value_type(classifier)?;
        match matched_stack(self.context.arena_mut(), head) {
            | Maybe::Present(endpoints) => Ok(endpoints),
            | Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::Stack,
                    found: TypeNode::Value(classifier),
                },
            )),
        }
    }

    /// Read a lazy pair without evaluating either component.
    ///
    /// # Specification
    /// - ensures: the components retain their left-to-right order; an unknown
    ///   classifier reads as two unknown components.
    /// - fails: a non-With classifier is a named shape mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct component types expose selecting the wrong
    ///   side.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret { Err(CheckRefusal::ShapeMismatch { at: site, wanted, found }) => site == at && wanted == ExpectedShape::With && found == TypeNode::Computation(classifier), Ok((first, second)) => self.context.arena().comp_type(first).is_some() && self.context.arena().comp_type(second).is_some(), Err(_) => true })]
    fn with_parts(
        &mut self,
        at: TermNode,
        classifier: CompTypeId,
    ) -> Result<(CompTypeId, CompTypeId), CheckRefusal>
    {
        let head = self.context.whnf_comp_type(classifier)?;
        match matched_with(self.context.arena_mut(), head) {
            | Maybe::Present(components) => Ok(components),
            | Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Computation(head),
                CheckRefusal::ShapeMismatch {
                    at,
                    wanted: ExpectedShape::With,
                    found: TypeNode::Computation(classifier),
                },
            )),
        }
    }

    /// Read an application domain and distinguish ambient from dependent
    /// output.
    ///
    /// # Specification
    /// - ensures: a Pi's codomain remains under its argument binder.
    /// - fails: a non-function is a shape mismatch at the calling term.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dependent stack application must substitute its
    ///   argument.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    #[spec(ensures: |ret| match ret { Err(CheckRefusal::ShapeMismatch { at: site, wanted, found }) => site == at && wanted == ExpectedShape::Arrow && found == TypeNode::Computation(classifier), Ok((domain, _)) => self.context.arena().value_type(domain).is_some(), Err(_) => true })]
    fn application_type(
        &mut self,
        at: TermNode,
        classifier: CompTypeId,
    ) -> Result<(ValueTypeId, Codomain), CheckRefusal>
    {
        let head = self.context.whnf_comp_type(classifier)?;
        match matched_function(self.context.arena_mut(), head) {
            | Maybe::Present(function) => Ok((function.domain(), match function.scope() {
                | CodomainScope::Ambient => Codomain::Ambient(function.codomain()),
                | CodomainScope::UnderBinder => Codomain::Dependent(function.codomain()),
            })),
            | Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Computation(head),
                CheckRefusal::ShapeMismatch {
                    at,
                    wanted: ExpectedShape::Arrow,
                    found: TypeNode::Computation(classifier),
                },
            )),
        }
    }

    /// Advance a flat stack from its consumed type, one frame per machine step.
    ///
    /// # Specification
    /// - ensures: only Bind opens a value binder; later stack frames are
    ///   ambient.
    /// - fails: mismatched frame shapes, operands, or delivered endpoint.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an interior bind and a dependent application expose
    ///   row loss and accidental capture by a preceding frame's binder.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)),
        ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == if matches!(self.context.arena().value(judgement.at), Some(Value::Reify(frames)) if matches!(frames.get(position.0), Some(gandr_core_term::control::StackFrame::Bind(_)))) { depth.saturating_add(1) } else { depth })]
    fn stack_step(
        &mut self,
        judgement: StackJudgement,
        position: Ordinal,
        input: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let Value::Reify(ref frames) = *self.value(judgement.at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let Some(frame) = frames.get(position.0).copied()
        else {
            let actual = self
                .context
                .arena_mut()
                .value_type_stack(judgement.consumed, input);
            value_bridge(
                self.context,
                judgement.at,
                actual,
                judgement.expected,
                &mut self.conversions,
            )?;
            return Ok(Step::Ascend(Produced::Checked));
        };
        let position = position.next()?;
        match frame {
            | gandr_core_term::control::StackFrame::Apply(argument) => {
                let (domain, codomain) =
                    self.application_type(TermNode::Value(judgement.at), input)?;
                self.frames.push(Frame::StackNext {
                    judgement,
                    position,
                });
                self.frames.push(Frame::ApplicationArgument {
                    argument,
                    domain,
                    codomain,
                });
                Ok(Step::Descend(Goal::Value {
                    term: argument,
                    direction: Direction::Check(domain),
                }))
            },
            | gandr_core_term::control::StackFrame::Bind(body) => {
                let head = self.context.whnf_comp_type(input)?;
                let CompTypeView::Returner { result, .. } =
                    comp_type_view(self.context.arena(), head)?
                else {
                    return Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Value(judgement.at),
                        wanted: ExpectedShape::Returner,
                        found: TypeNode::Computation(input),
                    });
                };
                self.context.binders().open(Zone::Intuitionistic, result);
                self.frames.push(Frame::StackNext {
                    judgement,
                    position,
                });
                self.frames.push(Frame::StackBind {
                    at: judgement.at,
                    body,
                    bound: head,
                });
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Synthesise,
                }))
            },
            | gandr_core_term::control::StackFrame::Project(side) => {
                let (first, second) = self.with_parts(TermNode::Value(judgement.at), input)?;
                let input = match side {
                    | gandr_kernel_term::Side::Left => first,
                    | gandr_kernel_term::Side::Right => second,
                };
                Ok(Step::Descend(Goal::Stack {
                    judgement,
                    position,
                    input,
                }))
            },
        }
    }

    /// Check a shift under the nearest reset's answer, weakened to this scope.
    ///
    /// # Specification
    /// - ensures: success opens exactly the captured stack's binder.
    /// - fails: a shift without an answer delimiter is named at its source.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested resets and an intervening binder distinguish
    ///   scope.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)), ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == depth.saturating_add(1))]
    fn shift(
        &mut self,
        at: ComputationId,
        body: ComputationId,
        captured: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let Some((answer, depth)) = self.frames.iter().rev().find_map(|frame| match *frame {
            | Frame::Reset { answer, depth } => Some((answer, depth)),
            | _ => None,
        })
        else {
            return Err(CheckRefusal::ShiftWithoutReset { at });
        };
        let added = usize::from(self.context.depth(Zone::Intuitionistic))
            .checked_sub(usize::from(depth))
            .ok_or(CheckRefusal::MachineInvariant)?;
        let added = u32::try_from(added).map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        let answer = shift_comp_type(self.context.arena_mut(), answer, Binders::from(added));
        let stack = self.context.arena_mut().value_type_stack(captured, answer);
        let expected = shift_comp_type(self.context.arena_mut(), answer, Binders::from(1_u32));
        self.context.binders().open(Zone::Intuitionistic, stack);
        self.frames.push(Frame::LambdaBody);
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction: Direction::Check(expected),
        }))
    }

    /// Form a handler's interface after checking exact clause coverage.
    ///
    /// # Specification
    /// - ensures: a complete clause set and one pending subject judgment.
    /// - fails: missing, repeated and unknown clauses are malformed source.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct operation names separate exact coverage from
    ///   count.
    /// - witness: `judgement::tests::handlers_discharge_only_their_own_interface`
    #[spec(captures: depth = self.frames.len(), ensures: |ret| ret.is_err() || (self.frames.len() == depth.saturating_add(1) && matches!(self.frames.last(), Some(Frame::HandlerForm { at: site, .. }) if *site == at)))]
    fn handle(
        &mut self,
        at: ComputationId,
        answer: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let result = self.returner_expected(at, answer)?;
        let Computation::Handle {
            ref signature,
            ref clauses,
            ..
        } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if signature.operations().len() != clauses.len() {
            return Err(CheckRefusal::HandlerCoverage { at });
        }
        let mut names: Vec<_> = clauses.iter().map(|clause| &clause.operation).collect();
        names.sort_unstable();
        if !names
            .into_iter()
            .zip(signature.operations())
            .all(|(name, operation)| name == &operation.name)
        {
            return Err(CheckRefusal::HandlerCoverage { at });
        }
        let effects = gandr_core_term::effect::EffectRow::singleton(signature.clone());
        let interface = self
            .context
            .arena_mut()
            .comp_type_returner_with_effects(result, effects);
        self.frames.push(Frame::HandlerForm {
            at,
            answer,
            interface,
        });
        Ok(Step::Descend(Goal::Form(TypeNode::Computation(interface))))
    }

    /// Check a handler's residual row and open its return clause.
    ///
    /// # Specification
    /// - ensures: only this handler's interface is discharged; success binds
    ///   the subject's returned payload, not the handler's answer payload.
    /// - fails: conflicting signatures, a non-returner or leaked effects.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unrelated effect and distinct payload types expose
    ///   loss.
    /// - witness: `judgement::tests::handlers_discharge_only_their_own_interface`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)), ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == depth.saturating_add(1))]
    fn handle_subject(
        &mut self,
        at: ComputationId,
        answer: CompTypeId,
        interface: CompTypeId,
        subject: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let answer_result = self.returner_expected(at, answer)?;
        let head = self.context.whnf_comp_type(subject)?;
        let CompTypeView::Returner { result, effects } =
            comp_type_view(self.context.arena(), head)?
        else {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Returner,
                found: TypeNode::Computation(subject),
            });
        };
        let Computation::Handle {
            ref signature,
            ref on_return,
            ..
        } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if effects.signatures().any(|held| {
            held.name() == signature.name()
                && held.inclusion(signature, self.context.arena())
                    == gandr_core_term::effect::RowInclusion::Excluded
        }) {
            return Err(CheckRefusal::EffectSignatureConflict {
                at,
                first: subject,
                second: interface,
            });
        }
        let residual = effects.without(signature.name());
        let on_return = *on_return;
        let natural = self
            .context
            .arena_mut()
            .comp_type_returner_with_effects(answer_result, residual);
        comp_bridge(self.context, at, natural, answer, &mut self.conversions)?;
        let expected = shift_comp_type(self.context.arena_mut(), answer, Binders::from(1_u32));
        self.context.binders().open(Zone::Intuitionistic, result);
        self.frames.push(Frame::HandlerReturn { at, answer });
        Ok(Step::Descend(Goal::Computation {
            term: on_return,
            direction: Direction::Check(expected),
        }))
    }

    /// Open one deep operation clause: payload first, resumption second.
    ///
    /// # Specification
    /// - ensures: the resumption consumes the operation reply with the answer's
    ///   row and delivers the answer; an unknown answer, which `handle` read
    ///   through the matched returner, contributes the empty row. Completing
    ///   the clause list opens no binder.
    /// - fails: inconsistent private continuation state or existing type
    ///   faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unlike payload/reply/answer types expose swapped
    ///   binders; a handler with clauses checked against the unknown answer
    ///   exposes a reader that demands a known returner.
    /// - witness: `judgement::tests::handlers_discharge_only_their_own_interface`
    /// - witness: `judgement::tests::handle_against_unknown_answer`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)), ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == if matches!(ret, Ok(Step::Ascend(Produced::Checked))) { depth } else { depth.saturating_add(2) })]
    fn handle_clause(
        &mut self,
        at: ComputationId,
        answer: CompTypeId,
        position: Ordinal,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Handle {
            ref signature,
            ref clauses,
            ..
        } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let Some(clause) = clauses.get(position.0)
        else {
            return Ok(Step::Ascend(Produced::Checked));
        };
        let Maybe::Present(operation) = signature.operation(&clause.operation)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let (payload, reply, body) = (operation.payload, operation.reply, clause.body);
        let head = self.context.whnf_comp_type(answer)?;
        let effects = match comp_type_view(self.context.arena(), head)? {
            | CompTypeView::Returner { effects, .. } => effects.clone(),
            | CompTypeView::Unknown => gandr_core_term::effect::EffectRow::EMPTY,
            | CompTypeView::Element { .. }
            | CompTypeView::Arrow { .. }
            | CompTypeView::Pi { .. }
            | CompTypeView::With(..) => return Err(CheckRefusal::MachineInvariant),
        };
        let input = self
            .context
            .arena_mut()
            .comp_type_returner_with_effects(reply, effects);
        let stack = self.context.arena_mut().value_type_stack(input, answer);
        let stack = shift_value_type(self.context.arena_mut(), stack, Binders::from(1_u32));
        let expected = shift_comp_type(self.context.arena_mut(), answer, Binders::from(2_u32));
        let position = position.next()?;
        self.context.binders().open(Zone::Intuitionistic, payload);
        self.context.binders().open(Zone::Intuitionistic, stack);
        self.frames.push(Frame::HandlerClause {
            at,
            answer,
            position,
        });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction: Direction::Check(expected),
        }))
    }

    /// Run `goal` to its result in `context`, strictly.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the result the goal's rule produced and the
    ///   crossings made; on success and on refusal alike, the binders stand
    ///   where they stood at entry.
    /// - fails: the first refusal a rule gives, or
    ///   [`CheckRefusal::BudgetExceeded`] when the allowance runs out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the step loop, the
    ///   allowance and the unwinding, separated by a run that finishes, one cut
    ///   short by the allowance, and a refusal under binders followed by a
    ///   judgement in the same context.
    /// - witness: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`
    /// - witness: `judgement::tests::a_refusal_under_binders_leaves_the_context_as_found`
    /// - witness: `judgement::tests::the_faces_agree_on_free_terms`
    #[spec(
        captures: depth = context.depth(Zone::Intuitionistic),
        ensures: |ret| context.depth(Zone::Intuitionistic) == depth && match ret {
            | Ok((produced, conversions)) => usize::from(conversions) <= usize::from(context.budget())
                && matches!((goal, produced),
                    (Goal::Value { direction: Direction::Synthesise, .. }, Produced::ValueType(_))
                        | (Goal::Computation { direction: Direction::Synthesise, .. }, Produced::CompType(_))
                        | (Goal::Value { direction: Direction::Check(_), .. }
                            | Goal::Computation { direction: Direction::Check(_), .. }
                            | Goal::Form(_) | Goal::Stack { .. }, Produced::Checked)),
            | Err(_) => true,
        },
    )]
    fn run(
        context: &'context mut CheckingContext<'arena>,
        goal: Goal,
    ) -> Result<(Produced, ConversionCount), CheckRefusal>
    {
        Machine::execute(context, goal, Marking::Strict)
            .map(|(produced, conversions, _marks)| (produced, conversions))
    }

    /// Run `goal` to its result in `context`, strictly or totally.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the result the goal's rule produced, the crossings
    ///   made and the refusals marked, none in a strict run; on success and on
    ///   refusal alike, the binders stand where they stood at entry.
    /// - fails: in a strict run, the first refusal a rule gives; in a total
    ///   run, the first engine fault; in both, [`CheckRefusal::BudgetExceeded`]
    ///   when the allowance runs out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a strict run and a total run over the same ill-typed
    ///   term separate the refusal from the mark; a run cut short by the
    ///   allowance and a refusal under binders keep the context as found.
    /// - witness: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`
    /// - witness: `judgement::tests::a_refusal_under_binders_leaves_the_context_as_found`
    /// - witness: `judgement::elaboration::tests::a_total_run_marks_where_a_strict_run_refuses`
    #[spec(
        captures: depth = context.depth(Zone::Intuitionistic),
        ensures: |ret| context.depth(Zone::Intuitionistic) == depth && match ret.as_ref() {
            | Ok(&(produced, conversions, ref marks)) => usize::from(conversions) <= usize::from(context.budget())
                && (marking == Marking::Total || marks.is_empty())
                && matches!((goal, produced),
                    (Goal::Value { direction: Direction::Synthesise, .. }, Produced::ValueType(_))
                        | (Goal::Computation { direction: Direction::Synthesise, .. }, Produced::CompType(_))
                        | (Goal::Value { direction: Direction::Check(_), .. }
                            | Goal::Computation { direction: Direction::Check(_), .. }
                            | Goal::Form(_), Produced::Checked)),
            | Err(_) => true,
        },
    )]
    fn execute(
        context: &'context mut CheckingContext<'arena>,
        goal: Goal,
        marking: Marking,
    ) -> Result<(Produced, ConversionCount, Vec<MarkEntry>), CheckRefusal>
    {
        let entry = context.binders().depth(Zone::Intuitionistic);
        let remaining = usize::from(context.budget());
        let mut machine = Machine {
            context,
            frames: Vec::new(),
            native_types: Vec::new(),
            conversions: ConversionCount::default(),
            remaining,
            marking,
            anchors: Vec::new(),
            marks: Vec::new(),
        };
        match machine.drive(goal) {
            | Ok(produced) => Ok((produced, machine.conversions, machine.marks)),
            | Err(refusal) => {
                machine.unwind(entry);
                Err(refusal)
            },
        }
    }

    /// Step from `goal` until no frame waits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the result handed out when the frame stack empties.
    /// - fails: as for [`Self::run`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — completing and budget-exhausted runs expose final
    ///   results and retained scope; L1 bounded free terms compare the two
    ///   faces. Premature completion or uncharged transitions changes these
    ///   observations, not a claim about arbitrary malformed frame stacks.
    /// - witness: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`
    /// - witness: `judgement::tests::the_faces_agree_on_free_terms`
    #[spec(
        captures: before = self.remaining,
        ensures: |ret| self.remaining <= before && (ret.is_err() || self.frames.is_empty()),
    )]
    fn drive(
        &mut self,
        goal: Goal,
    ) -> Result<Produced, CheckRefusal>
    {
        let mut step = Step::Descend(goal);
        loop {
            self.charge()?;
            let next = match step {
                | Step::Descend(goal) => {
                    self.anchor(goal);
                    self.descend(goal)
                },
                | Step::Ascend(produced) => {
                    self.settle();
                    match self.frames.pop() {
                        | Some(frame) => self.resume(frame, produced),
                        | None => return Ok(produced),
                    }
                },
            };
            step = match next {
                | Ok(next) => next,
                | Err(refusal) => self.recover(refusal)?,
            };
        }
    }

    /// Spend one step of the allowance.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success one fewer step remains; refusal leaves zero.
    /// - fails: [`CheckRefusal::BudgetExceeded`] when none remains.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero and one remaining step expose exact exhaustion
    ///   and the original allowance; complete judgements distinguish charging
    ///   too early, too late or not at all.
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    /// - witness: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`
    #[spec(
        captures: before = self.remaining,
        ensures: |ret| match before.checked_sub(1) {
            | Some(remaining) => ret == Ok(()) && self.remaining == remaining,
            | None => self.remaining == 0 && ret == Err(CheckRefusal::BudgetExceeded { budget: self.context.budget() }),
        },
    )]
    fn charge(&mut self) -> Result<(), CheckRefusal>
    {
        let Some(remaining) = self.remaining.checked_sub(1_usize)
        else {
            return Err(CheckRefusal::BudgetExceeded {
                budget: self.context.budget(),
            });
        };
        self.remaining = remaining;
        Ok(())
    }

    /// Close every binder opened since the binders stood at `entry`.
    ///
    /// # Specification
    /// - requires: the binders stand at or above `entry`.
    /// - ensures: the binders stand at `entry`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refusal inside binders and explicit zero/one-scope
    ///   transitions observe the original depth before the next judgement;
    ///   incomplete unwinding or closing an outer binder changes the result.
    /// - witness: `judgement::tests::a_refusal_under_binders_leaves_the_context_as_found`
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    #[spec(
        requires: self.context.depth(Zone::Intuitionistic) >= entry,
        ensures: self.context.depth(Zone::Intuitionistic) == entry,
    )]
    fn unwind(
        &mut self,
        entry: BinderDepth,
    )
    {
        while self.context.binders().depth(Zone::Intuitionistic) > entry {
            if self.context.binders().close(Zone::Intuitionistic).is_err() {
                break;
            }
        }
    }

    /// Close the innermost binder this run opened.
    ///
    /// # Specification
    /// - requires: a rule of this run opened a binder it has not closed.
    /// - ensures: that binder is closed.
    /// - fails: [`CheckRefusal::MachineInvariant`] when no binder is open.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and one-binder scopes expose an exact machine
    ///   fault or one removed binder; checked lambdas and binds observe that
    ///   closing restores the surrounding context rather than an outer scope.
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    /// - witness: `judgement::tests::a_bind_checks_against_the_expected_computation`
    #[spec(
        captures: before = usize::from(self.context.depth(Zone::Intuitionistic)),
        ensures: |ret| match before.checked_sub(1) {
            | Some(depth) => ret == Ok(()) && usize::from(self.context.depth(Zone::Intuitionistic)) == depth,
            | None => ret == Err(CheckRefusal::MachineInvariant)
                && self.context.depth(Zone::Intuitionistic) == BinderDepth::default(),
        },
    )]
    fn close(&mut self) -> Result<(), CheckRefusal>
    {
        match self.context.binders().close(Zone::Intuitionistic) {
            | Ok(_) => Ok(()),
            | Err(_) => Err(CheckRefusal::MachineInvariant),
        }
    }

    /// Start the judgement `goal`, by its direction.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the rule of the goal's direction for its term's former runs,
    ///   or the formation rule of the type's former.
    /// - fails: as that rule.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each former through each public direction exposes its
    ///   result family or named refusal, with L1 bounded free terms comparing
    ///   the faces; wrong dispatch or an unrelated ascent differs.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::the_faces_agree_on_free_terms`
    /// - witness: `native_formers::native_formers::record_width_depth_and_projection`
    #[spec(ensures: |ret| match ret {
        | Ok(Step::Ascend(produced)) => matches!((goal, produced),
            (Goal::Value { direction: Direction::Synthesise, .. }, Produced::ValueType(_))
                | (Goal::Computation { direction: Direction::Synthesise, .. }, Produced::CompType(_))
                | (Goal::Value { direction: Direction::Check(_), .. }
                    | Goal::Computation { direction: Direction::Check(_), .. } | Goal::Form(_) | Goal::Stack { .. }, Produced::Checked)),
        | Ok(Step::Descend(_)) | Err(_) => true,
    })]
    fn descend(
        &mut self,
        goal: Goal,
    ) -> Result<Step, CheckRefusal>
    {
        match goal {
            | Goal::Stack {
                judgement,
                position,
                input,
            } => self.stack_step(judgement, position, input),
            | Goal::Value { term, direction } => match direction {
                | Direction::Synthesise => self.synthesise_value(term),
                | Direction::Check(expected) => self.check_value(term, expected),
            },
            | Goal::Computation { term, direction } => match direction {
                | Direction::Synthesise => self.synthesise_comp(term),
                | Direction::Check(expected) => self.check_comp(term, expected),
            },
            | Goal::Form(TypeNode::Value(at)) => self.form_value_type(at),
            | Goal::Form(TypeNode::Computation(at)) => self.form_comp_type(at),
        }
    }

    /// The node of `term`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the node `term` names.
    /// - fails: [`CheckRefusal::DanglingNode`] when the arena holds none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — present value formers and a missing value id expose
    ///   the exact node rule or exact dangling fault; these distinguish a wrong
    ///   family, substituted node and omitted failure.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    #[spec(ensures: |ret| match (self.context.arena().value(term), ret) {
        | (Some(expected), Ok(held)) => core::ptr::eq(core::ptr::from_ref(expected), core::ptr::from_ref(held)),
        | (None, Err(refusal)) => refusal == CheckRefusal::DanglingNode { node: CoreNode::Term(TermNode::Value(term)) },
        | _ => false,
    })]
    fn value(
        &self,
        term: ValueId,
    ) -> Result<&Value, CheckRefusal>
    {
        self.context
            .arena()
            .value(term)
            .ok_or(CheckRefusal::DanglingNode {
                node: CoreNode::Term(TermNode::Value(term)),
            })
    }

    /// The node of `term`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the node `term` names.
    /// - fails: [`CheckRefusal::DanglingNode`] when the arena holds none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — present computation formers and a missing computation
    ///   id expose the selected rule or exact dangling fault; these separate a
    ///   substituted node and a value-family diagnostic.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    #[spec(ensures: |ret| match (self.context.arena().computation(term), ret) {
        | (Some(expected), Ok(held)) => core::ptr::eq(core::ptr::from_ref(expected), core::ptr::from_ref(held)),
        | (None, Err(refusal)) => refusal == CheckRefusal::DanglingNode { node: CoreNode::Term(TermNode::Computation(term)) },
        | _ => false,
    })]
    fn computation(
        &self,
        term: ComputationId,
    ) -> Result<&Computation, CheckRefusal>
    {
        self.context
            .arena()
            .computation(term)
            .ok_or(CheckRefusal::DanglingNode {
                node: CoreNode::Term(TermNode::Computation(term)),
            })
    }

    /// The synthesis rules over values.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a variable has the type its binder declared, shifted past the
    ///   binders opened since; a constant the type its declaration supplied;
    ///   the unit value and an integer or string literal their atom; a hole and
    ///   a mark the unknown type, minted; a quote awaits its type's formation;
    ///   a pair awaits its components' types and has their eager product; a
    ///   static application awaits its head's type and meets each argument in
    ///   turn. A leaf ascends with the frames as found; every other rule
    ///   descends above a new frame.
    /// - fails: [`CheckRefusal::NotSynthesisable`] for a thunk and a static
    ///   lambda; [`CheckRefusal::UnboundIndex`] for a variable past its zone's
    ///   binders; [`CheckRefusal::UnknownConstant`] for a constant with no
    ///   type; [`CheckRefusal::OutOfFragment`] for a numeric literal, an
    ///   injection and a value lift.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one value of every former synthesised, each to its
    ///   exact type or refusal.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_pair_synthesises_its_eager_product_and_checks_against_one`
    /// - witness: `judgement::tests::a_static_lambda_checks_only_against_a_static_pi`
    /// - witness: `bridge::tests::family_applied_at_wrong_arity_raises_the_exact_variant`
    /// - witness: `judgement::tests::a_hole_synthesises_the_unknown_type_and_checks_against_any`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| match ret {
            | Ok(Step::Ascend(_)) => self.frames.len() == depth || (matches!(self.context.arena().value(term), Some(Value::Record(_))) && self.frames.len() > depth),
            | Ok(Step::Descend(_)) => self.frames.len() > depth,
            | Err(_) => true,
        },
    )]
    fn synthesise_value(
        &mut self,
        term: ValueId,
    ) -> Result<Step, CheckRefusal>
    {
        let produced = |found: FormedValueType| Ok(Step::Ascend(Produced::ValueType(found.id())));
        match *self.value(term)? {
            | Value::Constructor { .. } => self.native_constructor(term),
            | Value::Record(_) => self.native_record(term),
            | Value::Reify(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Reify(term),
            }),
            | Value::ListNil | Value::ListCons(..) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::List(term),
            }),
            | Value::Primitive { primitive, .. } => {
                let computation = primitive.declared_type(self.context.arena_mut());
                let classifier = self.context.arena_mut().value_type_thunk(computation);
                Ok(Step::Ascend(Produced::ValueType(classifier)))
            },
            | Value::PathRefl(code) => {
                let _endpoint = crate::formation::path_code(self.context.arena(), code)?;
                let classifier = self
                    .context
                    .arena_mut()
                    .value_type_path_universe(code, code);
                Ok(Step::Ascend(Produced::ValueType(classifier)))
            },
            | Value::PathProduct(first, second) => {
                self.frames
                    .push(Frame::PathProductFirst { at: first, second });
                Ok(Step::Descend(Goal::Value {
                    term: first,
                    direction: Direction::Synthesise,
                }))
            },
            | Value::PathEquiv {
                path_type,
                forward,
                backward,
                ..
            } => {
                let (source, target) = self.path_endpoints(term, path_type)?;
                let expected = self.map_type(source, target);
                self.frames.push(Frame::PathBackward {
                    backward,
                    source,
                    target,
                    path_type,
                });
                Ok(Step::Descend(Goal::Value {
                    term: forward,
                    direction: Direction::Check(expected),
                }))
            },
            | Value::Variable { zone, index } => {
                match self.context.binders().occurrence(zone, index) {
                    | Ok(declared) => {
                        let read = match zone {
                            | Zone::Intuitionistic => shift_value_type(
                                self.context.arena_mut(),
                                declared,
                                Binders::past(index),
                            ),
                            | Zone::Linear => declared,
                        };
                        Ok(Step::Ascend(Produced::ValueType(read)))
                    },
                    | Err(ContextError::UnboundIndex { zone, index, depth }) => {
                        Err(CheckRefusal::UnboundIndex {
                            at: term,
                            zone,
                            index,
                            depth,
                        })
                    },
                    | Err(
                        ContextError::LinearSlotConsumed { .. }
                        | ContextError::LinearSlotUnconsumed { .. }
                        | ContextError::NoBinderToClose { .. },
                    ) => Err(CheckRefusal::MachineInvariant),
                }
            },
            | Value::Constant(constant) => match self.context.consult(constant) {
                | Maybe::Present(declared) => produced(declared),
                | Maybe::Absent(_) => Err(CheckRefusal::UnknownConstant { at: term, constant }),
            },
            | Value::Unit => produced(self.context.atom(Atom::Unit)),
            | Value::Literal(ref literal) => match literal.base_type() {
                | BaseType::Integer => produced(self.context.atom(Atom::Integer)),
                | BaseType::String => produced(self.context.atom(Atom::String)),
                | BaseType::Numeric => {
                    Err(unadmitted_value(term, UnadmittedFormer::NumericLiteral))
                },
            },
            | Value::Quote(quoted) => Ok(self.quote(TypeNode::Value(quoted))),
            | Value::QuoteComputation(quoted) => Ok(self.quote(TypeNode::Computation(quoted))),
            | Value::Thunk(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Thunk(term),
            }),
            | Value::Pair(first, second) => {
                self.frames.push(Frame::PairFirstSynthesised { second });
                Ok(Step::Descend(Goal::Value {
                    term: first,
                    direction: Direction::Synthesise,
                }))
            },
            | Value::Injection(..) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Injection(term),
            }),
            | Value::Lift { .. } => Err(unadmitted_value(term, UnadmittedFormer::ValueLift)),
            | Value::StaticLambda(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::StaticLambda(term),
            }),
            | Value::StaticApplication(..) => self.static_application(term),
            | Value::Hole(_) | Value::Mark { .. } => {
                let unknown = self.context.arena_mut().value_type_unknown();
                Ok(Step::Ascend(Produced::ValueType(unknown)))
            },
        }
    }

    /// Start a quote of `quoted`: the quoted type's formation is the next
    /// goal, with the quote's frame awaiting it.
    ///
    /// # Specification
    /// - requires: nothing; formation answers a missing or unadmitted type.
    /// - ensures: one quote frame awaits formation of exactly `quoted`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — quotes of value and computation types expose their
    ///   exact universe families and levels; a missing frame or wrong quoted
    ///   node changes synthesis, within those admitted quote forms.
    /// - witness: `judgement::tests::a_universe_classifies_one_level_up_in_the_positive_sort`
    #[spec(
        captures: before = self.frames.len(),
        ensures: |ret| self.frames.len().checked_sub(before) == Some(1)
            && self.frames.last() == Some(&Frame::Quote(quoted))
            && ret == Step::Descend(Goal::Form(quoted)),
    )]
    fn quote(
        &mut self,
        quoted: TypeNode,
    ) -> Step
    {
        self.frames.push(Frame::Quote(quoted));
        Step::Descend(Goal::Form(quoted))
    }

    /// The checking rules over values.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: a thunk's body checks against the body `expected` matches as
    ///   a thunk type at its weak head; a pair's components check against the
    ///   factors it matches as an eager product; a static lambda opens a binder
    ///   of the domain it matches as a static Pi and its body checks against
    ///   the codomain shifted past the binder; a hole and a mark check against
    ///   any type at once; a synthesising value synthesises, then crosses the
    ///   value bridge to `expected`. Every other rule descends.
    /// - fails: [`CheckRefusal::ShapeMismatch`] for a thunk against no thunk
    ///   type, a pair against no eager product, a static lambda against no
    ///   static Pi; [`CheckRefusal::OutOfFragment`] for an injection and a
    ///   value lift.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one value of every former checked, against its own
    ///   former and another.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_pair_synthesises_its_eager_product_and_checks_against_one`
    /// - witness: `judgement::tests::a_static_lambda_checks_only_against_a_static_pi`
    /// - witness: `judgement::tests::a_hole_synthesises_the_unknown_type_and_checks_against_any`
    ///
    /// # Judgement
    /// - expected: `expected`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| ret.is_err()
            || (self.frames.len() >= depth && matches!(ret, Ok(Step::Descend(_) | Step::Ascend(Produced::Checked)))),
    )]
    fn check_value(
        &mut self,
        term: ValueId,
        expected: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        match *self.value(term)? {
            | Value::Record(_) => self.check_native_record(term, expected),
            | Value::Reify(_) => {
                let (input, _) = self.stack_expected(term, expected)?;
                Ok(Step::Descend(Goal::Stack {
                    judgement: StackJudgement {
                        at: term,
                        expected,
                        consumed: input,
                    },
                    position: Ordinal::FIRST,
                    input,
                }))
            },
            | Value::ListNil => {
                self.list_expected(term, expected)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            | Value::ListCons(first, second) => {
                let element = self.list_expected(term, expected)?;
                self.frames.push(Frame::PairSecond { second, expected });
                Ok(Step::Descend(Goal::Value {
                    term: first,
                    direction: Direction::Check(element),
                }))
            },
            | Value::Thunk(body) => {
                let body_type = self.thunk_expected(term, expected)?;
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Check(body_type),
                }))
            },
            | Value::Pair(first, second) => {
                let (first_factor, second_factor) = self.product_expected(term, expected)?;
                self.frames.push(Frame::PairSecond {
                    second,
                    expected: second_factor,
                });
                Ok(Step::Descend(Goal::Value {
                    term: first,
                    direction: Direction::Check(first_factor),
                }))
            },
            | Value::StaticLambda(body) => {
                let (domain, codomain) = self.static_pi_expected(term, expected)?;
                self.context.binders().open(Zone::Intuitionistic, domain);
                self.frames.push(Frame::LambdaBody);
                Ok(Step::Descend(Goal::Value {
                    term: body,
                    direction: Direction::Check(codomain),
                }))
            },
            | Value::PathRefl(_)
            | Value::Constructor { .. }
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Primitive { .. }
            | Value::Variable { .. }
            | Value::Constant(_)
            | Value::Unit
            | Value::Literal(_)
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::StaticApplication(..) => {
                self.frames.push(Frame::ValueBridge { at: term, expected });
                Ok(Step::Descend(Goal::Value {
                    term,
                    direction: Direction::Synthesise,
                }))
            },
            | Value::Injection(side, value) => {
                let (left, right) = self.sum_expected(term, expected)?;
                let summand = match side {
                    | gandr_kernel_term::Side::Left => left,
                    | gandr_kernel_term::Side::Right => right,
                };
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Check(summand),
                }))
            },
            | Value::Lift { .. } => Err(unadmitted_value(term, UnadmittedFormer::ValueLift)),
            | Value::Hole(_) | Value::Mark { .. } => Ok(Step::Ascend(Produced::Checked)),
        }
    }

    /// Start the static application `at`: the root head's synthesis is the
    /// next goal, with one frame per argument awaiting the type the spine so
    /// far has, the first argument's innermost.
    ///
    /// # Specification
    /// - requires: `at` is a static application.
    /// - ensures: the frames, outermost last, name each argument with its
    ///   position and the spine's length; the head's synthesis is the step,
    ///   above at least one new frame.
    /// - fails: [`CheckRefusal::DanglingNode`] for a node the arena does not
    ///   hold; [`CheckRefusal::MachineInvariant`] for a spine past the `u32`
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Termination
    /// - reason: the `while let` loop descends the spine's heads, and the `for`
    ///   loop walks the arguments it collected, not recursion.
    /// - measure: the arena position of the head, which a static application
    ///   holds below its own; then the arguments left.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a saturated instance, one past its
    ///   arity, one of a code that is no operator, and one whose argument
    ///   misses its classifier at either position.
    /// - witness: `bridge::tests::family_applied_at_wrong_arity_raises_the_exact_variant`
    /// - witness: `bridge::tests::family_argument_at_wrong_classifier_raises_the_exact_variant`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| ret.is_err()
            || (matches!(ret, Ok(Step::Descend(_))) && self.frames.len() > depth),
    )]
    fn static_application(
        &mut self,
        at: ValueId,
    ) -> Result<Step, CheckRefusal>
    {
        let mut arguments = Vec::new();
        let mut head = at;
        while let Value::StaticApplication(function, argument) = *self.value(head)? {
            arguments.push(argument);
            head = function;
        }
        let length =
            u32::try_from(arguments.len()).map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        let spine = StaticArity::from(length);
        let mut position = length;
        for argument in arguments {
            position = position
                .checked_sub(1)
                .ok_or(CheckRefusal::MachineInvariant)?;
            self.frames.push(Frame::StaticSpine {
                at,
                position: ArgumentPosition::from(position),
                argument,
                spine,
            });
        }
        Ok(Step::Descend(Goal::Value {
            term: head,
            direction: Direction::Synthesise,
        }))
    }

    /// Whether the argument `argument` a computation applies at a static Pi is
    /// rigid: a static lambda, a static definition and an unsaturated
    /// instance of one normalize away, and the kernel has no static lambda.
    ///
    /// # Specification
    /// - requires: `argument` checked against a static Pi.
    /// - ensures: success when `argument`, reduced at its head, is a spine
    ///   whose root is neither a static lambda nor a code constant with a body.
    /// - fails: [`CheckRefusal::StaticLambdaArgument`] at `argument` otherwise;
    ///   the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Termination
    /// - reason: the `while let` loop descends the spine's heads, not
    ///   recursion.
    /// - measure: the arena position of the head, which a static application
    ///   holds below its own.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a static lambda, a static definition and
    ///   an opaque operator, each at a dynamic parameter.
    /// - witness: `bridge::tests::a_static_lambda_at_a_dynamic_parameter_is_refused_by_name`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::StaticLambdaArgument { at }) => at == argument,
        | Ok(()) | Err(_) => true,
    })]
    fn rigid_operator(
        &mut self,
        argument: ValueId,
    ) -> Result<(), CheckRefusal>
    {
        let mut root = self.context.whnf_code(argument)?;
        while let Value::StaticApplication(function, _) = *self.value(root)? {
            root = function;
        }
        let normalizes_away = match *self.value(root)? {
            | Value::StaticLambda(_) => true,
            | Value::Constant(constant) => {
                matches!(self.context.definitions().body(constant), Maybe::Present(_))
            },
            | Value::PathRefl(_)
            | Value::Constructor { .. }
            | Value::Record(_)
            | Value::Reify(_)
            | Value::Primitive { .. }
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Variable { .. }
            | Value::Unit
            | Value::ListNil
            | Value::ListCons(..)
            | Value::Literal(_)
            | Value::Pair(..)
            | Value::Injection(..)
            | Value::Thunk(_)
            | Value::Lift { .. }
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::StaticApplication(..)
            | Value::Hole(_)
            | Value::Mark { .. } => false,
        };
        if normalizes_away {
            Err(CheckRefusal::StaticLambdaArgument { at: argument })
        }
        else {
            Ok(())
        }
    }

    /// The synthesis rules over computations.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a force awaits its value's synthesised type; an application
    ///   awaits its head's; a bind awaits its bound computation's; a hole and a
    ///   mark have the unknown computation type, minted, and ascend.
    /// - fails: [`CheckRefusal::NotSynthesisable`] for a lambda, a return or a
    ///   fixpoint; [`CheckRefusal::OutOfFragment`] for a case.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — force, application and bind expose their synthesised
    ///   types while introductions and case expose exact refusals; L1 free
    ///   pools compare the faces, separating wrong child goals and frames.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::the_faces_agree_on_free_terms`
    /// - witness: `judgement::tests::a_hole_synthesises_the_unknown_type_and_checks_against_any`
    #[spec(
        captures: before = self.frames.len(),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(_)))
            && self.frames.len().checked_sub(before) == Some(1))
            || (matches!(ret, Ok(Step::Ascend(Produced::CompType(_)))) && self.frames.len() == before),
    )]
    fn synthesise_comp(
        &mut self,
        term: ComputationId,
    ) -> Result<Step, CheckRefusal>
    {
        match *self.computation(term)? {
            | Computation::DataCase { scrutinee, .. } => {
                self.frames.push(Frame::NativeCase(term));
                Ok(Step::Descend(Goal::Value {
                    term: scrutinee,
                    direction: Direction::Synthesise,
                }))
            },
            | Computation::RecordProjection(record, _) => {
                self.frames.push(Frame::NativeProjection(term));
                Ok(Step::Descend(Goal::Value {
                    term: record,
                    direction: Direction::Synthesise,
                }))
            },
            | Computation::Perform {
                ref signature,
                ref operation,
                payload,
            } => {
                let Maybe::Present(operation) = signature.operation(operation)
                else {
                    return Err(CheckRefusal::UnknownOperation { at: term });
                };
                let expected = operation.payload;
                let reply = operation.reply;
                let effects = gandr_core_term::effect::EffectRow::singleton(signature.clone());
                let result = self
                    .context
                    .arena_mut()
                    .comp_type_returner_with_effects(reply, effects);
                self.frames.push(Frame::PerformPayload {
                    payload,
                    expected,
                    result,
                });
                Ok(Step::Descend(Goal::Form(TypeNode::Computation(result))))
            },
            | Computation::Resume(stack, body) => {
                self.frames.push(Frame::Resume { stack, body });
                Ok(Step::Descend(Goal::Value {
                    term: stack,
                    direction: Direction::Synthesise,
                }))
            },
            | Computation::Project(side, subject) => {
                self.frames.push(Frame::Project { at: term, side });
                Ok(Step::Descend(Goal::Computation {
                    term: subject,
                    direction: Direction::Synthesise,
                }))
            },
            | Computation::Handle { .. } => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Handle(term),
            }),
            | Computation::Reset(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Reset(term),
            }),
            | Computation::Shift(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Shift(term),
            }),
            | Computation::With(..) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::With(term),
            }),
            | Computation::ListFold {
                element, result, ..
            } => {
                let result = self.context.arena_mut().comp_type_returner(result);
                self.frames.push(Frame::ListFold {
                    at: term,
                    result,
                    phase: ListPhase::Element,
                });
                Ok(Step::Descend(Goal::Form(TypeNode::Value(element))))
            },
            | Computation::Primitive {
                primitive,
                arguments,
            } => {
                let domains = primitive.arguments();
                if domains.len() != arguments.len() {
                    return Err(CheckRefusal::MachineInvariant);
                }
                let arena = self.context.arena_mut();
                let result = primitive.result().mint(arena);
                let result = arena.comp_type_returner(result);
                let first_domain = domains
                    .first()
                    .ok_or(CheckRefusal::MachineInvariant)?
                    .mint(arena);
                let first = match arguments {
                    | gandr_core_term::primitive::Arguments::Unary(argument) => {
                        self.frames.push(Frame::PrimitiveResult { result });
                        argument
                    },
                    | gandr_core_term::primitive::Arguments::Binary([first, second]) => {
                        let expected = domains
                            .get(1)
                            .ok_or(CheckRefusal::MachineInvariant)?
                            .mint(arena);
                        self.frames.push(Frame::PrimitiveSecond {
                            argument: second,
                            expected,
                            result,
                        });
                        first
                    },
                };
                Ok(Step::Descend(Goal::Value {
                    term: first,
                    direction: Direction::Check(first_domain),
                }))
            },
            | Computation::Transport(path, value) => {
                self.frames.push(Frame::TransportPath { path, value });
                Ok(Step::Descend(Goal::Value {
                    term: path,
                    direction: Direction::Synthesise,
                }))
            },
            | Computation::Force(value) => {
                self.frames.push(Frame::Force { value });
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Synthesise,
                }))
            },
            | Computation::Application(head, argument) => {
                self.frames.push(Frame::ApplicationHead { head, argument });
                Ok(Step::Descend(Goal::Computation {
                    term: head,
                    direction: Direction::Synthesise,
                }))
            },
            | Computation::Lambda(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Lambda(term),
            }),
            | Computation::Return(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Return(term),
            }),
            | Computation::Fixpoint { .. } => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Fixpoint(term),
            }),
            | Computation::Bind(bound, body) => {
                Ok(self.bind(term, bound, body, Direction::Synthesise))
            },
            | Computation::Case { .. } => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Case(term),
            }),
            | Computation::Hole(_) | Computation::Mark { .. } => {
                let unknown = self.context.arena_mut().comp_type_unknown();
                Ok(Step::Ascend(Produced::CompType(unknown)))
            },
        }
    }

    /// The checking rules over computations.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: a lambda opens a binder of the domain `expected` matches as a
    ///   function type at its weak head, and its body checks against the
    ///   codomain — an arrow's shifted past the binder, a dependent arrow's as
    ///   it stands; a return's value checks against the result it matches as a
    ///   returner; a bind awaits its bound computation's synthesised type, then
    ///   checks its body against `expected` shifted past its binder; a hole and
    ///   a mark check against any type at once; a fixpoint opens a binder of `U
    ///   expected` and checks its body against `expected` shifted past it,
    ///   after its structural-descent claim, when it makes one, replays; a
    ///   synthesising computation synthesises, then crosses the computation
    ///   bridge to `expected`.
    /// - fails: [`CheckRefusal::ShapeMismatch`] for a lambda against no arrow
    ///   or a return against no returner; [`CheckRefusal::OutOfFragment`] for a
    ///   case; [`CheckRefusal::DescentNotReplayed`] for a descent claim the
    ///   walk refuses.
    ///
    /// # Judgement
    /// - expected: `expected`
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each computation former checks against its own shape
    ///   or another, including dependent binders; exact acceptance or refusal
    ///   separates wrong child directions and expected-type dispatch.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
    /// - witness: `judgement::tests::a_bind_checks_against_the_expected_computation`
    /// - witness: `judgement::tests::a_hole_synthesises_the_unknown_type_and_checks_against_any`
    /// - witness: `recursive_data::recursive_data::a_fixpoint_checks_at_every_computation_type`
    /// - witness: `recursive_data::recursive_data::descent_claims_replay_or_are_refused_by_name`
    #[spec(
        captures: before = self.frames.len(),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(_))) && self.frames.len() >= before)
            || (matches!(ret, Ok(Step::Ascend(Produced::Checked))) && self.frames.len() == before
                && matches!(self.context.arena().computation(term), Some(Computation::Hole(_) | Computation::Mark { .. }))),
    )]
    fn check_comp(
        &mut self,
        term: ComputationId,
        expected: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        match *self.computation(term)? {
            | Computation::Handle { .. } => self.handle(term, expected),
            | Computation::Reset(body) => {
                self.frames.push(Frame::Reset {
                    answer: expected,
                    depth: self.context.depth(Zone::Intuitionistic),
                });
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Check(expected),
                }))
            },
            | Computation::Shift(body) => self.shift(term, body, expected),
            | Computation::With(first, second) => {
                let (first_type, second_type) =
                    self.with_parts(TermNode::Computation(term), expected)?;
                self.frames.push(Frame::Next(Goal::Computation {
                    term: second,
                    direction: Direction::Check(second_type),
                }));
                Ok(Step::Descend(Goal::Computation {
                    term: first,
                    direction: Direction::Check(first_type),
                }))
            },
            | Computation::Lambda(body) => {
                let (domain, codomain) = self.arrow_expected(term, expected)?;
                self.context.binders().open(Zone::Intuitionistic, domain);
                self.frames.push(Frame::LambdaBody);
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Check(codomain),
                }))
            },
            | Computation::Return(value) => {
                let result = self.returner_expected(term, expected)?;
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Check(result),
                }))
            },
            | Computation::Fixpoint { body, evidence } => {
                match evidence {
                    | FixpointEvidence::StructuralDescent => {
                        crate::descent::replay(self.context, term, expected, body)?;
                    },
                    | FixpointEvidence::Partial => {},
                }
                let arena = self.context.arena_mut();
                let recursive = arena.value_type_thunk(expected);
                let scoped = shift_comp_type(arena, expected, Binders::from(1_u32));
                self.context.binders().open(Zone::Intuitionistic, recursive);
                self.frames.push(Frame::LambdaBody);
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Check(scoped),
                }))
            },
            | Computation::Primitive { .. }
            | Computation::DataCase { .. }
            | Computation::RecordProjection(..)
            | Computation::Perform { .. }
            | Computation::Resume(..)
            | Computation::Project(..)
            | Computation::ListFold { .. }
            | Computation::Transport(..)
            | Computation::Force(_)
            | Computation::Application(..) => {
                self.frames.push(Frame::CompBridge { at: term, expected });
                Ok(Step::Descend(Goal::Computation {
                    term,
                    direction: Direction::Synthesise,
                }))
            },
            | Computation::Bind(bound, body) => {
                Ok(self.bind(term, bound, body, Direction::Check(expected)))
            },
            | Computation::Case {
                scrutinee,
                on_left,
                on_right,
            } => {
                self.frames.push(Frame::CaseScrutinee {
                    scrutinee,
                    on_left,
                    on_right,
                    expected,
                });
                Ok(Step::Descend(Goal::Value {
                    term: scrutinee,
                    direction: Direction::Synthesise,
                }))
            },
            | Computation::Hole(_) | Computation::Mark { .. } => {
                Ok(Step::Ascend(Produced::Checked))
            },
        }
    }

    /// Start the bind `at` of `bound` into `body`, judged in `direction`.
    ///
    /// # Specification
    /// - requires: `bound` and `body` are the two halves of the bind `at`.
    /// - ensures: the bound computation's synthesis is the next goal, with the
    ///   bind's frame awaiting its type and holding the direction the body is
    ///   judged in.
    /// - provides: the one rule both computation faces share.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the rule's surfaces are the two directions, the
    ///   returner test and the lowering out of the binder, separated by a bind
    ///   synthesising its body's type, a bind checked against its body's type,
    ///   a bind of an arrow-typed computation, and a bind whose body's type
    ///   mentions the bound name, each asserted as the exact type, check or
    ///   refusal.
    /// - witness: `judgement::tests::a_bind_synthesises_its_continuations_type`
    /// - witness: `judgement::tests::a_bind_checks_against_the_expected_computation`
    /// - witness: `judgement::tests::a_bind_of_a_non_returner_is_a_shape_mismatch`
    /// - witness: `judgement::tests::a_bind_whose_type_mentions_its_binder_is_refused`
    #[spec(
        captures: before = self.frames.len(),
        ensures: |ret| self.frames.len().checked_sub(before) == Some(1)
            && self.frames.last() == Some(&Frame::BindBound { at, bound, body, direction })
            && ret == Step::Descend(Goal::Computation { term: bound, direction: Direction::Synthesise }),
    )]
    fn bind(
        &mut self,
        at: ComputationId,
        bound: ComputationId,
        body: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Step
    {
        self.frames.push(Frame::BindBound {
            at,
            bound,
            body,
            direction,
        });

        Step::Descend(Goal::Computation {
            term: bound,
            direction: Direction::Synthesise,
        })
    }

    /// The body a thunk checks against: the one the expected type matches as a
    /// thunk type at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the body of `expected` when it is `U C` at its weak head; an
    ///   unknown computation type, minted, when it is the unknown type.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a thunk type,
    ///   for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk checked against a thunk type, the unknown
    ///   type and an atom exposes the selected body or exact shape refusal;
    ///   defined-code conversion covers a head reached through unfolding.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret {
        | Ok(body) => self.context.arena().comp_type(body).is_some()
            && match value_type_view(self.context.arena(), expected) {
                | Ok(ValueTypeView::Thunk(held)) => body == held,
                | Ok(ValueTypeView::Unknown) => matches!(comp_type_view(self.context.arena(), body), Ok(CompTypeView::Unknown)),
                | Ok(_) | Err(_) => true,
            },
        | Err(CheckRefusal::ShapeMismatch { at: named, wanted, found }) => named == TermNode::Value(at)
            && wanted == ExpectedShape::Thunk && found == TypeNode::Value(expected),
        | Err(_) => true,
    })]
    fn thunk_expected(
        &mut self,
        at: ValueId,
        expected: ValueTypeId,
    ) -> Result<CompTypeId, CheckRefusal>
    {
        let head = self.context.whnf_value_type(expected)?;
        match matched_thunk(self.context.arena_mut(), head) {
            | Maybe::Present(body) => Ok(body),
            | Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::Thunk,
                    found: TypeNode::Value(expected),
                },
            )),
        }
    }

    /// The factors a pair's components check against: the ones the expected
    /// type matches as an eager product at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: both factors of `expected` when it is `A × B` at its weak
    ///   head, or two unknown types when it is the unknown type, each resolving
    ///   in the arena.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting an eager
    ///   product, for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a pair against a product, against the
    ///   unknown type and against an atom.
    /// - witness: `judgement::tests::a_pair_synthesises_its_eager_product_and_checks_against_one`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    ///
    /// # Judgement
    /// - expected: `expected`
    #[spec(ensures: |ret| match ret {
        | Ok((first, second)) => {
            self.context.arena().value_type(first).is_some()
                && self.context.arena().value_type(second).is_some()
        },
        | Err(CheckRefusal::ShapeMismatch { at: shaped, wanted, found }) => {
            shaped == TermNode::Value(at)
                && wanted == ExpectedShape::Product
                && found == TypeNode::Value(expected)
        },
        | Err(_) => true,
    })]
    fn product_expected(
        &mut self,
        at: ValueId,
        expected: ValueTypeId,
    ) -> Result<(ValueTypeId, ValueTypeId), CheckRefusal>
    {
        let head = self.context.whnf_value_type(expected)?;
        match matched_product(self.context.arena_mut(), head) {
            | Maybe::Present(factors) => Ok(factors),
            | Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::Product,
                    found: TypeNode::Value(expected),
                },
            )),
        }
    }

    /// The domain and codomain a static lambda's body checks against: the
    /// ones the expected type matches as a static Pi at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the domain of `expected`, and its codomain shifted past the
    ///   lambda's binder: a static Pi's codomain stands in the ambient context;
    ///   two unknown types when it is the unknown type. Both resolve in the
    ///   arena.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a static Pi,
    ///   for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a static lambda against a static Pi, the
    ///   unknown type and an atom.
    /// - witness: `judgement::tests::a_static_lambda_checks_only_against_a_static_pi`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    ///
    /// # Judgement
    /// - expected: `expected`
    #[spec(ensures: |ret| match ret {
        | Ok((domain, codomain)) => {
            self.context.arena().value_type(domain).is_some()
                && self.context.arena().value_type(codomain).is_some()
        },
        | Err(CheckRefusal::ShapeMismatch { at: shaped, wanted, found }) => {
            shaped == TermNode::Value(at)
                && wanted == ExpectedShape::StaticPi
                && found == TypeNode::Value(expected)
        },
        | Err(_) => true,
    })]
    fn static_pi_expected(
        &mut self,
        at: ValueId,
        expected: ValueTypeId,
    ) -> Result<(ValueTypeId, ValueTypeId), CheckRefusal>
    {
        let head = self.context.whnf_value_type(expected)?;
        match matched_static_pi(self.context.arena_mut(), head) {
            | Maybe::Present((domain, codomain)) => {
                let scoped =
                    shift_value_type(self.context.arena_mut(), codomain, Binders::from(1_u32));
                Ok((domain, scoped))
            },
            | Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::StaticPi,
                    found: TypeNode::Value(expected),
                },
            )),
        }
    }

    /// The domain and codomain a lambda's body checks against: the ones the
    /// expected type matches as a function type at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the domain of `expected`, and its codomain read under the
    ///   lambda's binder — an arrow's shifted past it, a dependent arrow's as
    ///   it stands, the unknown type's unknown codomain shifted as an arrow's.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting an arrow, for
    ///   any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary and dependent lambdas expose checked bodies
    ///   and exact shape failures; the dependent application case separates
    ///   using the ambient codomain where substitution is required; a lambda
    ///   against the unknown type checks its body against the unknown.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_dependent_application_instantiates_its_codomain_at_the_argument`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret {
        | Ok((domain, codomain)) => self.context.arena().value_type(domain).is_some()
            && self.context.arena().comp_type(codomain).is_some()
            && match comp_type_view(self.context.arena(), expected) {
                | Ok(CompTypeView::Pi { domain: held_domain, codomain: held_codomain }) => domain == held_domain && codomain == held_codomain,
                | Ok(CompTypeView::Arrow { domain: held, .. }) => domain == held,
                | Ok(CompTypeView::Element { .. } | CompTypeView::Unknown) => true,
                | Ok(CompTypeView::Returner { .. } | CompTypeView::With(..)) | Err(_) => false,
            },
        | Err(CheckRefusal::ShapeMismatch { at: named, wanted, found }) => named == TermNode::Computation(at)
            && wanted == ExpectedShape::Arrow && found == TypeNode::Computation(expected),
        | Err(_) => true,
    })]
    fn arrow_expected(
        &mut self,
        at: ComputationId,
        expected: CompTypeId,
    ) -> Result<(ValueTypeId, CompTypeId), CheckRefusal>
    {
        let head = self.context.whnf_comp_type(expected)?;
        match matched_function(self.context.arena_mut(), head) {
            | Maybe::Present(function) => match function.scope() {
                | CodomainScope::Ambient => {
                    let scoped = shift_comp_type(
                        self.context.arena_mut(),
                        function.codomain(),
                        Binders::from(1_u32),
                    );
                    Ok((function.domain(), scoped))
                },
                | CodomainScope::UnderBinder => Ok((function.domain(), function.codomain())),
            },
            | Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Computation(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Computation(at),
                    wanted: ExpectedShape::Arrow,
                    found: TypeNode::Computation(expected),
                },
            )),
        }
    }

    /// The result type a return checks its value against: the one the
    /// expected type matches as a returner at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the result of `expected` when it is `F A` at its weak head;
    ///   an unknown value type, minted, when it is the unknown type.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a returner,
    ///   for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    ///
    /// # Adequacy
    /// - hypothesis: L3 — returns against a returner, the unknown type and an
    ///   arrow expose checking at the selected value type or the exact shape
    ///   failure; a substituted result type or wrong node family changes these
    ///   answers.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret {
        | Ok(result) => self.context.arena().value_type(result).is_some()
            && match comp_type_view(self.context.arena(), expected) {
                | Ok(CompTypeView::Returner { result: held, .. }) => result == held,
                | Ok(CompTypeView::Element { .. } | CompTypeView::Unknown) => true,
                | Ok(CompTypeView::Arrow { .. } | CompTypeView::Pi { .. } | CompTypeView::With(..)) | Err(_) => false,
            },
        | Err(CheckRefusal::ShapeMismatch { at: named, wanted, found }) => named == TermNode::Computation(at)
            && wanted == ExpectedShape::Returner && found == TypeNode::Computation(expected),
        | Err(_) => true,
    })]
    fn returner_expected(
        &mut self,
        at: ComputationId,
        expected: CompTypeId,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let head = self.context.whnf_comp_type(expected)?;
        match matched_returner(self.context.arena_mut(), head) {
            | Maybe::Present(result) => Ok(result),
            | Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Computation(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Computation(at),
                    wanted: ExpectedShape::Returner,
                    found: TypeNode::Computation(expected),
                },
            )),
        }
    }

    /// The formation rules over value types.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an atom and the unit type are formed; a thunk type forms its
    ///   body; a universe is formed below the greatest level; a lift forms its
    ///   type, then awaits the raise; a decode awaits its code's synthesised
    ///   type; an eager product forms both factors; a static Pi forms both
    ///   classifiers, then awaits their check as static classifiers. A former
    ///   formed at once leaves the frames as found; one that descends leaves
    ///   them no shorter.
    /// - fails: the view's refusal for a former outside the fragment or a
    ///   dangling id; [`CheckRefusal::OutOfFragment`] naming
    ///   [`UnadmittedFormer::TopUniverse`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one type of every former, formed or refused, through
    ///   the public faces.
    /// - witness: `formation::tests::every_value_type_constructor_has_a_formation_rule`
    /// - witness: `bridge::tests::a_static_pi_over_a_type_that_classifies_no_codes_is_refused_by_name`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| match ret {
            | Ok(Step::Ascend(_)) => self.frames.len() == depth || (matches!(self.context.arena().value_type(at), Some(gandr_core_term::ValueType::Data { .. } | gandr_core_term::ValueType::Record(_))) && self.frames.len() >= depth),
            | Ok(Step::Descend(_)) => self.frames.len() >= depth,
            | Err(_) => true,
        },
    )]
    fn form_value_type(
        &mut self,
        at: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        match value_type_view(self.context.arena(), at)? {
            | ValueTypeView::Data { .. } => self.native_data(at),
            | ValueTypeView::Record(fields) => {
                for &field in fields.values().rev() {
                    self.frames
                        .push(Frame::NativeNext(Goal::Form(TypeNode::Value(field))));
                }
                Ok(Step::Ascend(Produced::Checked))
            },
            | ValueTypeView::Stack { input, output } => {
                self.frames
                    .push(Frame::FormNext(TypeNode::Computation(output)));
                Ok(Step::Descend(Goal::Form(TypeNode::Computation(input))))
            },
            | ValueTypeView::PathUniverse(source, target) => {
                let _source = crate::formation::path_code(self.context.arena(), source)?;
                let _target = crate::formation::path_code(self.context.arena(), target)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            | ValueTypeView::Integer
            | ValueTypeView::String
            | ValueTypeView::Unit
            | ValueTypeView::Unknown => Ok(Step::Ascend(Produced::Checked)),
            | ValueTypeView::List(element) => {
                Ok(Step::Descend(Goal::Form(TypeNode::Value(element))))
            },
            | ValueTypeView::Thunk(body) => {
                Ok(Step::Descend(Goal::Form(TypeNode::Computation(body))))
            },
            | ValueTypeView::Universe { level, .. } => {
                if level.succ().is_err() {
                    return Err(CheckRefusal::OutOfFragment {
                        at: CoreNode::Type(TypeNode::Value(at)),
                        former: UnadmittedFormer::TopUniverse,
                    });
                }
                Ok(Step::Ascend(Produced::Checked))
            },
            | ValueTypeView::Lift { inner, .. } => {
                self.frames.push(Frame::FormLift(at));
                Ok(Step::Descend(Goal::Form(TypeNode::Value(inner))))
            },
            | ValueTypeView::Element { code, .. } => {
                self.frames.push(Frame::FormElement(TypeNode::Value(at)));
                Ok(Step::Descend(Goal::Value {
                    term: code,
                    direction: Direction::Synthesise,
                }))
            },
            | ValueTypeView::Sum(first, second) | ValueTypeView::Product(first, second) => {
                self.frames.push(Frame::FormNext(TypeNode::Value(second)));
                Ok(Step::Descend(Goal::Form(TypeNode::Value(first))))
            },
            | ValueTypeView::StaticPi { domain, codomain } => {
                self.frames.push(Frame::FormStaticPi(at));
                self.frames.push(Frame::FormNext(TypeNode::Value(codomain)));
                Ok(Step::Descend(Goal::Form(TypeNode::Value(domain))))
            },
        }
    }

    /// The formation rules over computation types.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a returner forms its result; an arrow forms its domain, then
    ///   its codomain; a dependent arrow forms its domain, then its codomain
    ///   under a binder of the domain; a decode awaits its code's synthesised
    ///   type; the unknown type is formed at once.
    /// - fails: the view's refusal for a dangling id.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the four computation-type formers expose exact
    ///   classifiers, including a dependent codomain; wrong children, skipped
    ///   domain formation or missing binder frames change those observations.
    /// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
    /// - witness: `formation::tests::the_dependent_arrow_forms_at_the_join_of_its_levels`
    #[spec(
        captures: before = self.frames.len(),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(_))) && self.frames.len() >= before)
            || (matches!(ret, Ok(Step::Ascend(Produced::Checked))) && self.frames.len() == before),
    )]
    fn form_comp_type(
        &mut self,
        at: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        match comp_type_view(self.context.arena(), at)? {
            | CompTypeView::With(first, second) => {
                self.frames
                    .push(Frame::FormNext(TypeNode::Computation(second)));
                Ok(Step::Descend(Goal::Form(TypeNode::Computation(first))))
            },
            | CompTypeView::Returner { result, effects } => {
                self.frames.extend(
                    effects
                        .types()
                        .rev()
                        .map(|ty| Frame::FormNext(TypeNode::Value(ty))),
                );
                Ok(Step::Descend(Goal::Form(TypeNode::Value(result))))
            },
            | CompTypeView::Arrow { domain, codomain } => {
                self.frames
                    .push(Frame::FormNext(TypeNode::Computation(codomain)));
                Ok(Step::Descend(Goal::Form(TypeNode::Value(domain))))
            },
            | CompTypeView::Pi { domain, codomain } => {
                self.frames.push(Frame::FormPi { domain, codomain });
                Ok(Step::Descend(Goal::Form(TypeNode::Value(domain))))
            },
            | CompTypeView::Element { code, .. } => {
                self.frames
                    .push(Frame::FormElement(TypeNode::Computation(at)));
                Ok(Step::Descend(Goal::Value {
                    term: code,
                    direction: Direction::Synthesise,
                }))
            },
            | CompTypeView::Unknown => Ok(Step::Ascend(Produced::Checked)),
        }
    }

    /// Add the bound computation's demand to the continuation's ambient type.
    ///
    /// # Specification
    /// - ensures: a pure bound leaves the continuation unchanged; otherwise
    ///   both demands remain in the returner, with one definition per name.
    /// - fails: a non-returner cannot carry a nonempty row; conflicting
    ///   definitions are refused rather than overwritten.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct rows and conflicting shared names
    ///   distinguish accumulation, row laundering, and silent signature
    ///   replacement.
    /// - witness: `judgement::tests::bind_unions_effect_rows`
    /// - witness: `judgement::tests::check_mode_bind_subsumes_the_accumulated_row`
    #[spec(ensures: |ret| ret.is_err() || match comp_type_view(self.context.arena(), bound) {
        Ok(CompTypeView::Returner { effects, .. }) if effects.purity() == gandr_core_term::effect::Purity::Pure => ret == Ok(continued),
        Ok(CompTypeView::Returner { effects, .. }) => ret.is_ok_and(|actual| matches!(comp_type_view(self.context.arena(), actual), Ok(CompTypeView::Returner { effects: actual, .. }) if effects.is_subset(actual, self.context.arena()) == gandr_core_term::effect::RowInclusion::Included)),
        _ => false,
    })]
    fn accumulate_effects(
        &mut self,
        at: ComputationId,
        bound: CompTypeId,
        continued: CompTypeId,
    ) -> Result<CompTypeId, CheckRefusal>
    {
        let CompTypeView::Returner { effects, .. } = comp_type_view(self.context.arena(), bound)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if effects.purity() == gandr_core_term::effect::Purity::Pure {
            return Ok(continued);
        }
        let demanded = effects.clone();
        let head = self.context.whnf_comp_type(continued)?;
        let CompTypeView::Returner { result, effects } =
            comp_type_view(self.context.arena(), head)?
        else {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Returner,
                found: TypeNode::Computation(continued),
            });
        };
        let combined = demanded
            .union(effects, self.context.arena())
            .map_err(|_conflict| CheckRefusal::EffectSignatureConflict {
                at,
                first: bound,
                second: continued,
            })?;
        Ok(self
            .context
            .arena_mut()
            .comp_type_returner_with_effects(result, combined))
    }

    /// The universe a quote of the formed type `quoted` has: its family's sort
    /// at the type's level.
    ///
    /// # Specification
    /// - requires: `quoted` is formed.
    /// - ensures: the value universe for a value type, the computation universe
    ///   for a computation type, at [`level_of`] the type, minted.
    /// - fails: as [`level_of`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — quotes of atoms, returners and universes expose exact
    ///   sorts and natural levels; swapped quote families or a missing universe
    ///   successor differs on these finite forms.
    /// - witness: `judgement::tests::a_universe_classifies_one_level_up_in_the_positive_sort`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|universe|
        matches!(value_type_view(self.context.arena(), universe), Ok(ValueTypeView::Universe { sort, .. })
            if matches!((quoted, sort), (TypeNode::Value(_), GroundSort::Value) | (TypeNode::Computation(_), GroundSort::Computation)))))]
    fn quoted(
        &mut self,
        quoted: TypeNode,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let level = level_of(self.context, quoted)?;
        let sort = match quoted {
            | TypeNode::Value(_) => GroundSort::Value,
            | TypeNode::Computation(_) => GroundSort::Computation,
        };
        Ok(self
            .context
            .arena_mut()
            .value_type_universe(Sort::Ground(sort), level))
    }

    /// Whether the lift `at`, its type formed, raises it.
    ///
    /// # Specification
    /// - requires: `at` is a lift whose type is formed.
    /// - ensures: success exactly when the lift's target lies strictly above
    ///   [`level_of`] its type.
    /// - fails: [`CheckRefusal::OutOfFragment`] naming
    ///   [`UnadmittedFormer::TypeLift`] otherwise;
    ///   [`CheckRefusal::MachineInvariant`] when `at` is no lift.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — targets below, equal to and above a nonzero natural
    ///   level expose exact lift refusal or formation, separating non-strict
    ///   comparison and wrong diagnostic identity; non-lifts fault explicitly.
    /// - witness: `judgement::tests::lift_formation_distinguishes_below_equal_and_above`
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    #[spec(ensures: |ret| match ret {
        | Ok(()) => matches!(value_type_view(self.context.arena(), at), Ok(ValueTypeView::Lift { .. })),
        | Err(CheckRefusal::OutOfFragment { at: named, former: UnadmittedFormer::TypeLift }) => named == CoreNode::Type(TypeNode::Value(at)),
        | Err(_) => true,
    })]
    fn raises(
        &self,
        at: ValueTypeId,
    ) -> Result<(), CheckRefusal>
    {
        let arena = self.context.arena();
        let ValueTypeView::Lift { inner, target } = value_type_view(arena, at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if bool::from(level_of(self.context, TypeNode::Value(inner))?.lt(target)) {
            Ok(())
        }
        else {
            Err(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Value(at)),
                former: UnadmittedFormer::TypeLift,
            })
        }
    }

    /// Whether the static Pi `at`, both classifiers formed, ranges over static
    /// classifiers only.
    ///
    /// # Specification
    /// - requires: `at` is a static Pi whose classifiers are formed.
    /// - ensures: success exactly when its domain and its codomain are each, at
    ///   the weak head, a universe or a static Pi.
    /// - fails: [`CheckRefusal::StaticClassifierExpected`] naming `at` and the
    ///   first classifier that is neither; [`CheckRefusal::MachineInvariant`]
    ///   when `at` is no static Pi; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Termination
    /// - reason: the `for` loop visits the two classifiers, not recursion.
    /// - measure: the classifiers left, at most two.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by classifiers that are universes and
    ///   static Pis, a domain that is neither, and a codomain that is neither.
    /// - witness: `bridge::tests::a_static_pi_over_a_type_that_classifies_no_codes_is_refused_by_name`
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::StaticClassifierExpected { at: named, .. }) => named == at,
        | Ok(()) | Err(_) => true,
    })]
    fn static_classifiers(
        &mut self,
        at: ValueTypeId,
    ) -> Result<(), CheckRefusal>
    {
        let ValueTypeView::StaticPi { domain, codomain } =
            value_type_view(self.context.arena(), at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        for classifier in [domain, codomain] {
            let head = self.context.whnf_value_type(classifier)?;
            match value_type_view(self.context.arena(), head)? {
                | ValueTypeView::Universe { .. }
                | ValueTypeView::StaticPi { .. }
                | ValueTypeView::Unknown => {},
                | ValueTypeView::PathUniverse(..)
                | ValueTypeView::Data { .. }
                | ValueTypeView::Record(_)
                | ValueTypeView::Sum(..)
                | ValueTypeView::List(_)
                | ValueTypeView::Stack { .. }
                | ValueTypeView::Integer
                | ValueTypeView::String
                | ValueTypeView::Unit
                | ValueTypeView::Thunk(_)
                | ValueTypeView::Lift { .. }
                | ValueTypeView::Element { .. }
                | ValueTypeView::Product(..) => {
                    return Err(CheckRefusal::StaticClassifierExpected {
                        at,
                        found: classifier,
                    });
                },
            }
        }
        Ok(())
    }

    /// Cross the decode bridge for the decode `node`, whose code synthesised
    /// `synthesised`.
    ///
    /// # Specification
    /// - requires: `node` is a decode.
    /// - ensures: as [`decode_bridge`] at the decode's code, its family's sort
    ///   and its level.
    /// - fails: as [`decode_bridge`]; [`CheckRefusal::MachineInvariant`] when
    ///   `node` is no decode.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — value and computation decodes expose their exact
    ///   classifier or sort/type refusal; these separate a wrong family, target
    ///   level or missing conversion crossing within the fragment.
    /// - witness: `formation::tests::every_value_type_constructor_has_a_formation_rule`
    /// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
    /// - witness: `judgement::tests::a_value_type_in_a_computation_universe_is_a_sort_mismatch`
    #[spec(
        captures: before = usize::from(self.conversions),
        ensures: usize::from(self.conversions) == if match node {
            | TypeNode::Value(at) => matches!(value_type_view(self.context.arena(), at), Ok(ValueTypeView::Element { .. })),
            | TypeNode::Computation(at) => matches!(comp_type_view(self.context.arena(), at), Ok(CompTypeView::Element { .. })),
        } { before.saturating_add(1) } else { before },
    )]
    fn decodes(
        &mut self,
        node: TypeNode,
        synthesised: ValueTypeId,
    ) -> Result<(), CheckRefusal>
    {
        let arena = self.context.arena();
        let (code, target, sort) = match node {
            | TypeNode::Value(at) => match value_type_view(arena, at)? {
                | ValueTypeView::Element { code, target } => {
                    (code, target.clone(), GroundSort::Value)
                },
                | ValueTypeView::PathUniverse(..)
                | ValueTypeView::Data { .. }
                | ValueTypeView::Record(_)
                | ValueTypeView::Sum(..)
                | ValueTypeView::List(_)
                | ValueTypeView::Stack { .. }
                | ValueTypeView::Integer
                | ValueTypeView::String
                | ValueTypeView::Unit
                | ValueTypeView::Thunk(_)
                | ValueTypeView::Universe { .. }
                | ValueTypeView::Lift { .. }
                | ValueTypeView::Product(..)
                | ValueTypeView::StaticPi { .. }
                | ValueTypeView::Unknown => return Err(CheckRefusal::MachineInvariant),
            },
            | TypeNode::Computation(at) => match comp_type_view(arena, at)? {
                | CompTypeView::Element { code, target } => {
                    (code, target.clone(), GroundSort::Computation)
                },
                | CompTypeView::Returner { .. }
                | CompTypeView::With(..)
                | CompTypeView::Arrow { .. }
                | CompTypeView::Pi { .. }
                | CompTypeView::Unknown => {
                    return Err(CheckRefusal::MachineInvariant);
                },
            },
        };
        decode_bridge(
            self.context,
            code,
            synthesised,
            sort,
            &target,
            &mut self.conversions,
        )
    }

    /// The type an application whose argument checked has.
    ///
    /// # Specification
    /// - requires: `argument` checked against the domain `codomain` belongs to.
    /// - ensures: an arrow's codomain as it stands; a dependent arrow's
    ///   instantiated at the argument — at the lifted code when the argument
    ///   crossed the value bridge with a lift, so the codomain reads the code
    ///   at the universe the domain names.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary and dependent applications expose exact
    ///   result types, with a dependent argument substituted into its codomain;
    ///   retaining a bound variable or changing an ambient codomain differs.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_dependent_application_instantiates_its_codomain_at_the_argument`
    #[spec(ensures: |ret| match codomain {
        | Codomain::Ambient(held) => ret == held,
        | Codomain::Dependent(_) => self.context.arena().comp_type(ret).is_some(),
    })]
    fn applied(
        &mut self,
        argument: ValueId,
        codomain: Codomain,
    ) -> CompTypeId
    {
        match codomain {
            | Codomain::Ambient(codomain) => codomain,
            | Codomain::Dependent(codomain) => {
                let lift = self.context.lifts().get(&argument).cloned();
                let arena = self.context.arena_mut();
                let code = match lift {
                    | Some(lift) => lift.mint(arena, argument),
                    | None => argument,
                };
                instantiate_comp_type(arena, codomain, code)
            },
        }
    }

    /// Hand `produced` to the rule `frame` holds.
    ///
    /// # Specification
    /// - requires: `frame` was pushed by a rule of this run.
    /// - ensures: a force has the body of its value's thunk type; an
    ///   application checks its argument against its head's domain, refuses an
    ///   argument at a static Pi that normalizes away, then has the codomain,
    ///   instantiated for a dependent arrow; a bind opens a binder of its bound
    ///   computation's returned type and judges its body, then closes the
    ///   binder and has what the body had, lowered out of the binder; a lambda
    ///   closes its binder; a bridge frame crosses its bridge and the check
    ///   succeeds; a quote has its universe; a formation frame forms the next
    ///   child, closes its binder, checks a lift's raise, crosses the decode
    ///   bridge or checks a static Pi's classifiers; a pair checks or
    ///   synthesises its second component after its first; a static application
    ///   meets each argument at the domain of the static Pi its head so far
    ///   has, and has the codomain. Every type read for its former is read at
    ///   its weak head.
    /// - fails: [`CheckRefusal::ShapeMismatch`] for a forced value of no thunk
    ///   type, a head of no arrow type, or a bound computation of no returner
    ///   type; [`CheckRefusal::DependentBind`] for a bind whose body's type
    ///   mentions the bound name; [`CheckRefusal::FamilyArity`] for a static
    ///   application whose head opens fewer static Pis than it has arguments;
    ///   [`CheckRefusal::FamilyArgumentClassifier`] for an argument whose type
    ///   does not cross to its domain; [`CheckRefusal::StaticLambdaArgument`]
    ///   for an argument at a dynamic application that normalizes away; the
    ///   bridges' refusals; [`CheckRefusal::MachineInvariant`] when `produced`
    ///   is not the kind the frame awaits.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every frame resumed by a term of its former through
    ///   the public faces, each to its exact answer or refusal, beside a result
    ///   of the wrong kind; an arity refusal names more arguments than the head
    ///   opened.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_result_of_the_wrong_kind_is_a_machine_fault`
    /// - witness: `judgement::tests::a_pair_synthesises_its_eager_product_and_checks_against_one`
    /// - witness: `bridge::tests::family_applied_at_wrong_arity_raises_the_exact_variant`
    /// - witness: `bridge::tests::family_argument_at_wrong_classifier_raises_the_exact_variant`
    /// - witness: `bridge::tests::a_static_lambda_at_a_dynamic_parameter_is_refused_by_name`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::FamilyArity { expected, actual, .. }) => {
            u32::from(expected) < u32::from(actual)
        },
        | Ok(_) | Err(_) => true,
    })]
    fn resume(
        &mut self,
        frame: Frame,
        produced: Produced,
    ) -> Result<Step, CheckRefusal>
    {
        match (frame, produced) {
            | (Frame::NativeNext(goal) | Frame::Next(goal), Produced::Checked) => {
                Ok(Step::Descend(goal))
            },
            | (Frame::NativeYield(result), Produced::Checked) => Ok(Step::Ascend(result)),
            | (Frame::NativeCollect, Produced::ValueType(field)) => {
                self.native_types.push(field);
                Ok(Step::Ascend(Produced::Checked))
            },
            | (Frame::NativeDiscard, Produced::ValueType(_))
            | (Frame::Reset { .. }, Produced::Checked) => Ok(Step::Ascend(Produced::Checked)),
            | (Frame::NativeRecord { term, base }, Produced::Checked) => {
                let Some(matched_native_node) = self.context.arena().value(term)
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let Value::Record(ref fields) = *matched_native_node
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                if self.native_types.len().checked_sub(base) != Some(fields.len()) {
                    return Err(CheckRefusal::MachineInvariant);
                }
                let fields = fields
                    .keys()
                    .cloned()
                    .zip(self.native_types.drain(base ..))
                    .collect();
                let record = self.context.arena_mut().value_type_record(fields);
                Ok(Step::Ascend(Produced::ValueType(record)))
            },
            | (Frame::NativeCase(term), Produced::ValueType(datatype)) => {
                self.native_case(term, datatype)
            },
            | (Frame::NativeMotive { term, datatype }, Produced::Checked) => {
                self.native_branches(term, datatype)
            },
            | (Frame::NativeProjection(term), Produced::ValueType(record)) => {
                self.native_projection(term, record)
            },
            | (
                Frame::NativeNext(_)
                | Frame::NativeYield(_)
                | Frame::NativeCollect
                | Frame::NativeDiscard
                | Frame::NativeRecord { .. }
                | Frame::NativeCase(_)
                | Frame::NativeMotive { .. }
                | Frame::NativeProjection(_),
                _,
            ) => Err(CheckRefusal::MachineInvariant),
            | (Frame::Resume { stack, body }, Produced::ValueType(classifier)) => {
                let (input, output) = self.stack_expected(stack, classifier)?;
                self.frames.push(Frame::PrimitiveResult { result: output });
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Check(input),
                }))
            },
            | (Frame::Project { at, side }, Produced::CompType(classifier)) => {
                let (first, second) = self.with_parts(TermNode::Computation(at), classifier)?;
                Ok(Step::Ascend(Produced::CompType(match side {
                    | gandr_kernel_term::Side::Left => first,
                    | gandr_kernel_term::Side::Right => second,
                })))
            },
            | (
                Frame::HandlerForm {
                    at,
                    answer,
                    interface,
                },
                Produced::Checked,
            ) => {
                let Computation::Handle { subject, .. } = *self.computation(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                self.frames.push(Frame::HandlerSubject {
                    at,
                    answer,
                    interface,
                });
                Ok(Step::Descend(Goal::Computation {
                    term: subject,
                    direction: Direction::Synthesise,
                }))
            },
            | (
                Frame::HandlerSubject {
                    at,
                    answer,
                    interface,
                },
                Produced::CompType(subject),
            ) => self.handle_subject(at, answer, interface, subject),
            | (Frame::HandlerReturn { at, answer }, Produced::Checked) => {
                self.close()?;
                self.handle_clause(at, answer, Ordinal::FIRST)
            },
            | (
                Frame::HandlerClause {
                    at,
                    answer,
                    position,
                },
                Produced::Checked,
            ) => {
                self.close()?;
                self.close()?;
                self.handle_clause(at, answer, position)
            },
            | (
                Frame::StackNext {
                    judgement,
                    position,
                },
                Produced::CompType(input),
            ) => Ok(Step::Descend(Goal::Stack {
                judgement,
                position,
                input,
            })),
            | (Frame::StackBind { at, body, bound }, Produced::CompType(synthesised)) => {
                let Maybe::Present(lowered) =
                    strengthen_comp_type(self.context.arena_mut(), synthesised)
                else {
                    return Err(CheckRefusal::DependentStack { at, synthesised });
                };
                self.close()?;
                let result = self.accumulate_effects(body, bound, lowered)?;
                Ok(Step::Ascend(Produced::CompType(result)))
            },
            | (Frame::ListFold { at, result, phase }, Produced::Checked) => {
                self.list_fold(at, result, phase)
            },
            | (
                Frame::PrimitiveSecond {
                    argument,
                    expected,
                    result,
                }
                | Frame::PerformPayload {
                    payload: argument,
                    expected,
                    result,
                },
                Produced::Checked,
            ) => {
                self.frames.push(Frame::PrimitiveResult { result });
                Ok(Step::Descend(Goal::Value {
                    term: argument,
                    direction: Direction::Check(expected),
                }))
            },
            | (
                Frame::PrimitiveResult { result } | Frame::TransportOperand { result },
                Produced::Checked,
            ) => Ok(Step::Ascend(Produced::CompType(result))),
            | (Frame::PathProductFirst { at, second }, Produced::ValueType(classifier)) => {
                let (source, target) = self.path_endpoints(at, classifier)?;
                self.frames.push(Frame::PathProductSecond {
                    at: second,
                    source,
                    target,
                });
                Ok(Step::Descend(Goal::Value {
                    term: second,
                    direction: Direction::Synthesise,
                }))
            },
            | (
                Frame::PathProductSecond { at, source, target },
                Produced::ValueType(classifier),
            ) => {
                let (right_source, right_target) = self.path_endpoints(at, classifier)?;
                let arena = self.context.arena_mut();
                let source = arena.value_type_product(&[source, right_source]);
                let target = arena.value_type_product(&[target, right_target]);
                let source = arena.value_quote(source);
                let target = arena.value_quote(target);
                let classifier = arena.value_type_path_universe(source, target);
                Ok(Step::Ascend(Produced::ValueType(classifier)))
            },
            | (
                Frame::PathBackward {
                    backward,
                    source,
                    target,
                    path_type,
                },
                Produced::Checked,
            ) => {
                let expected = self.map_type(target, source);
                self.frames.push(Frame::PathChecked { path_type });
                Ok(Step::Descend(Goal::Value {
                    term: backward,
                    direction: Direction::Check(expected),
                }))
            },
            | (Frame::PathChecked { path_type }, Produced::Checked) => {
                Ok(Step::Ascend(Produced::ValueType(path_type)))
            },
            | (Frame::TransportPath { path, value }, Produced::ValueType(classifier)) => {
                let (source, target) = self.path_endpoints(path, classifier)?;
                let result = self.context.arena_mut().comp_type_returner(target);
                self.frames.push(Frame::TransportOperand { result });
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Check(source),
                }))
            },
            | (
                Frame::CaseScrutinee {
                    scrutinee,
                    on_left,
                    on_right,
                    expected,
                },
                Produced::ValueType(classifier),
            ) => {
                let (left, right) = self.sum_expected(scrutinee, classifier)?;
                let expected =
                    shift_comp_type(self.context.arena_mut(), expected, Binders::from(1_u32));
                self.context.binders().open(Zone::Intuitionistic, left);
                self.frames.push(Frame::CaseRight {
                    on_right,
                    right,
                    expected,
                });
                Ok(Step::Descend(Goal::Computation {
                    term: on_left,
                    direction: Direction::Check(expected),
                }))
            },
            | (
                Frame::CaseRight {
                    on_right,
                    right,
                    expected,
                },
                Produced::Checked,
            ) => {
                self.close()?;
                self.context.binders().open(Zone::Intuitionistic, right);
                self.frames.push(Frame::LambdaBody);
                Ok(Step::Descend(Goal::Computation {
                    term: on_right,
                    direction: Direction::Check(expected),
                }))
            },
            | (Frame::Force { value }, Produced::ValueType(synthesised)) => {
                let head = self.context.whnf_value_type(synthesised)?;
                match matched_thunk(self.context.arena_mut(), head) {
                    | Maybe::Present(body) => Ok(Step::Ascend(Produced::CompType(body))),
                    | Maybe::Absent(absent) => Err(unmatched(
                        absent,
                        TypeNode::Value(head),
                        CheckRefusal::ShapeMismatch {
                            at: TermNode::Value(value),
                            wanted: ExpectedShape::Thunk,
                            found: TypeNode::Value(synthesised),
                        },
                    )),
                }
            },
            | (Frame::ApplicationHead { head, argument }, Produced::CompType(synthesised)) => {
                let (domain, codomain) =
                    self.application_type(TermNode::Computation(head), synthesised)?;
                self.frames.push(Frame::ApplicationArgument {
                    argument,
                    domain,
                    codomain,
                });
                Ok(Step::Descend(Goal::Value {
                    term: argument,
                    direction: Direction::Check(domain),
                }))
            },
            | (
                Frame::ApplicationArgument {
                    argument,
                    domain,
                    codomain,
                },
                Produced::Checked,
            ) => {
                let read = self.context.whnf_value_type(domain)?;
                if let ValueTypeView::StaticPi { .. } = value_type_view(self.context.arena(), read)?
                {
                    self.rigid_operator(argument)?;
                }
                Ok(Step::Ascend(Produced::CompType(
                    self.applied(argument, codomain),
                )))
            },
            | (
                Frame::LambdaBody | Frame::FormBinder | Frame::BindBody { .. },
                Produced::Checked,
            ) => {
                self.close()?;
                Ok(Step::Ascend(Produced::Checked))
            },
            | (
                Frame::BindBound {
                    at,
                    bound,
                    body,
                    direction,
                },
                Produced::CompType(synthesised),
            ) => {
                let read = self.context.whnf_comp_type(synthesised)?;
                let result = match matched_returner(self.context.arena_mut(), read) {
                    | Maybe::Present(result) => result,
                    | Maybe::Absent(absent) => {
                        return Err(unmatched(
                            absent,
                            TypeNode::Computation(read),
                            CheckRefusal::ShapeMismatch {
                                at: TermNode::Computation(bound),
                                wanted: ExpectedShape::Returner,
                                found: TypeNode::Computation(synthesised),
                            },
                        ));
                    },
                };
                let direction = match direction {
                    | Direction::Synthesise => Direction::Synthesise,
                    | Direction::Check(expected) => {
                        let accumulated = self.accumulate_effects(at, read, expected)?;
                        if accumulated != expected {
                            comp_bridge(
                                self.context,
                                at,
                                accumulated,
                                expected,
                                &mut self.conversions,
                            )?;
                        }
                        Direction::Check(shift_comp_type(
                            self.context.arena_mut(),
                            expected,
                            Binders::from(1_u32),
                        ))
                    },
                };
                self.context.binders().open(Zone::Intuitionistic, result);
                self.frames.push(Frame::BindBody { at, bound: read });
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction,
                }))
            },
            | (Frame::BindBody { at, bound }, Produced::CompType(synthesised)) => {
                let Maybe::Present(lowered) =
                    strengthen_comp_type(self.context.arena_mut(), synthesised)
                else {
                    return Err(CheckRefusal::DependentBind { at, synthesised });
                };
                self.close()?;
                let lowered = self.accumulate_effects(at, bound, lowered)?;
                Ok(Step::Ascend(Produced::CompType(lowered)))
            },
            | (Frame::ValueBridge { at, expected }, Produced::ValueType(synthesised)) => {
                value_bridge(
                    self.context,
                    at,
                    synthesised,
                    expected,
                    &mut self.conversions,
                )?;
                Ok(Step::Ascend(Produced::Checked))
            },
            | (Frame::CompBridge { at, expected }, Produced::CompType(synthesised)) => {
                comp_bridge(
                    self.context,
                    at,
                    synthesised,
                    expected,
                    &mut self.conversions,
                )?;
                Ok(Step::Ascend(Produced::Checked))
            },
            | (Frame::Quote(quoted), Produced::Checked) => {
                Ok(Step::Ascend(Produced::ValueType(self.quoted(quoted)?)))
            },
            | (Frame::FormNext(next), Produced::Checked) => Ok(Step::Descend(Goal::Form(next))),
            | (Frame::FormPi { domain, codomain }, Produced::Checked) => {
                self.context.binders().open(Zone::Intuitionistic, domain);
                self.frames.push(Frame::FormBinder);
                Ok(Step::Descend(Goal::Form(TypeNode::Computation(codomain))))
            },
            | (Frame::FormLift(at), Produced::Checked) => {
                self.raises(at)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            | (Frame::FormElement(node), Produced::ValueType(synthesised)) => {
                self.decodes(node, synthesised)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            | (Frame::FormStaticPi(at), Produced::Checked) => {
                self.static_classifiers(at)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            | (Frame::PairSecond { second, expected }, Produced::Checked) => {
                Ok(Step::Descend(Goal::Value {
                    term: second,
                    direction: Direction::Check(expected),
                }))
            },
            | (Frame::PairFirstSynthesised { second }, Produced::ValueType(first)) => {
                self.frames.push(Frame::PairSecondSynthesised { first });
                Ok(Step::Descend(Goal::Value {
                    term: second,
                    direction: Direction::Synthesise,
                }))
            },
            | (Frame::PairSecondSynthesised { first }, Produced::ValueType(second)) => {
                let product = self
                    .context
                    .arena_mut()
                    .value_type_product(&[first, second]);
                Ok(Step::Ascend(Produced::ValueType(product)))
            },
            | (
                Frame::StaticSpine {
                    at,
                    position,
                    argument,
                    spine,
                },
                Produced::ValueType(synthesised),
            ) => {
                let head = self.context.whnf_value_type(synthesised)?;
                let (domain, codomain) = match matched_static_pi(self.context.arena_mut(), head) {
                    | Maybe::Present(classifiers) => classifiers,
                    | Maybe::Absent(absent) => {
                        return Err(unmatched(
                            absent,
                            TypeNode::Value(head),
                            CheckRefusal::FamilyArity {
                                at,
                                expected: StaticArity::from(u32::from(position)),
                                actual: spine,
                            },
                        ));
                    },
                };
                if let Value::StaticLambda(_) = *self.value(argument)? {
                    self.frames.push(Frame::StaticOperand { codomain });
                    return Ok(Step::Descend(Goal::Value {
                        term: argument,
                        direction: Direction::Check(domain),
                    }));
                }
                self.frames.push(Frame::StaticArgument {
                    argument,
                    position,
                    domain,
                    codomain,
                });
                Ok(Step::Descend(Goal::Value {
                    term: argument,
                    direction: Direction::Synthesise,
                }))
            },
            | (
                Frame::StaticArgument {
                    argument,
                    position,
                    domain,
                    codomain,
                },
                Produced::ValueType(synthesised),
            ) => {
                value_bridge(
                    self.context,
                    argument,
                    synthesised,
                    domain,
                    &mut self.conversions,
                )
                .map_err(|refusal| match refusal {
                    | CheckRefusal::TypeMismatch(_)
                    | CheckRefusal::SortMismatch { .. }
                    | CheckRefusal::LevelMismatch { .. } => {
                        CheckRefusal::FamilyArgumentClassifier {
                            at: argument,
                            position,
                            synthesised,
                            expected: domain,
                        }
                    },
                    | other => other,
                })?;
                Ok(Step::Ascend(Produced::ValueType(codomain)))
            },
            | (Frame::StaticOperand { codomain }, Produced::Checked) => {
                Ok(Step::Ascend(Produced::ValueType(codomain)))
            },
            | (Frame::Unknowing(TermNode::Value(_)), Produced::Checked) => {
                let unknown = self.context.arena_mut().value_type_unknown();
                Ok(Step::Ascend(Produced::ValueType(unknown)))
            },
            | (Frame::Unknowing(TermNode::Computation(_)), Produced::Checked) => {
                let unknown = self.context.arena_mut().comp_type_unknown();
                Ok(Step::Ascend(Produced::CompType(unknown)))
            },
            | (
                Frame::PathProductFirst { .. }
                | Frame::Resume { .. }
                | Frame::PathProductSecond { .. }
                | Frame::TransportPath { .. }
                | Frame::CaseScrutinee { .. }
                | Frame::Force { .. }
                | Frame::ValueBridge { .. }
                | Frame::FormElement(_)
                | Frame::PairFirstSynthesised { .. }
                | Frame::PairSecondSynthesised { .. }
                | Frame::StaticSpine { .. }
                | Frame::StaticArgument { .. },
                Produced::CompType(_) | Produced::Checked,
            )
            | (
                Frame::ApplicationHead { .. }
                | Frame::CompBridge { .. }
                | Frame::BindBound { .. }
                | Frame::Project { .. }
                | Frame::HandlerSubject { .. }
                | Frame::StackNext { .. }
                | Frame::StackBind { .. },
                Produced::ValueType(_) | Produced::Checked,
            )
            | (
                Frame::PathBackward { .. }
                | Frame::PerformPayload { .. }
                | Frame::Next(_)
                | Frame::Reset { .. }
                | Frame::HandlerForm { .. }
                | Frame::HandlerReturn { .. }
                | Frame::HandlerClause { .. }
                | Frame::PathChecked { .. }
                | Frame::PrimitiveSecond { .. }
                | Frame::PrimitiveResult { .. }
                | Frame::ListFold { .. }
                | Frame::TransportOperand { .. }
                | Frame::CaseRight { .. }
                | Frame::ApplicationArgument { .. }
                | Frame::LambdaBody
                | Frame::FormBinder
                | Frame::Quote(_)
                | Frame::FormNext(_)
                | Frame::FormPi { .. }
                | Frame::FormLift(_)
                | Frame::FormStaticPi(_)
                | Frame::PairSecond { .. }
                | Frame::StaticOperand { .. }
                | Frame::Unknowing(_),
                Produced::ValueType(_) | Produced::CompType(_),
            )
            | (Frame::BindBody { .. }, Produced::ValueType(_)) => {
                Err(CheckRefusal::MachineInvariant)
            },
        }
    }
    /// Read the two decoded endpoints of a native path classifier.
    ///
    /// # Specification
    /// - requires: nothing; a non-path classifier is refused.
    /// - ensures: both endpoints are closed first-order value types.
    /// - provides: source and target types in classifier order.
    /// - fails: a shape mismatch or an unsupported path code.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — native endpoint codes remain ordered and in the
    ///   first-order fragment; mismatched classifiers report their original
    ///   site.
    /// - witness: `bridge::tests::native_path_module_round_trips`
    #[spec(ensures: |ret| match ret {
        Ok(pair) => <[ValueTypeId; 2]>::from(pair).iter().all(|&id| matches!(self.context.arena().value_type(id), Some(&(gandr_core_term::ValueType::Base(_) | gandr_core_term::ValueType::Product(_) | gandr_core_term::ValueType::Sum(_))))),
        Err(CheckRefusal::ShapeMismatch { at: found_at, wanted, found }) => found_at == TermNode::Value(at) && wanted == ExpectedShape::PathUniverse && found == TypeNode::Value(classifier),
        Err(_) => true,
    })]
    fn path_endpoints(
        &mut self,
        at: ValueId,
        classifier: ValueTypeId,
    ) -> Result<(ValueTypeId, ValueTypeId), CheckRefusal>
    {
        let head = self.context.whnf_value_type(classifier)?;
        let ValueTypeView::PathUniverse(source, target) =
            value_type_view(self.context.arena(), head)?
        else {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(at),
                wanted: ExpectedShape::PathUniverse,
                found: TypeNode::Value(classifier),
            });
        };
        Ok((
            crate::formation::path_code(self.context.arena(), source)?,
            crate::formation::path_code(self.context.arena(), target)?,
        ))
    }

    /// Form the thunked translator from a closed source to a closed target.
    ///
    /// # Specification
    /// trivial.
    fn map_type(
        &mut self,
        source: ValueTypeId,
        target: ValueTypeId,
    ) -> ValueTypeId
    {
        let arena = self.context.arena_mut();
        let result = arena.comp_type_returner(target);
        let arrow = arena.comp_type_arrow(source, result);
        arena.value_type_thunk(arrow)
    }

    /// Read the two summands used by injection and case checking.
    ///
    /// # Specification
    /// - requires: nothing; a non-sum classifier is refused.
    /// - ensures: the summands the classifier's weak head matches as a sum; two
    ///   unknown types for the unknown type.
    /// - provides: the left and right summands in that order.
    /// - fails: a shape mismatch when the weak head is not a sum.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sum operands retain their classifiers and mismatch
    ///   refusals retain the source site instead of reporting a native-path
    ///   shape; an injection against the unknown type checks its payload.
    /// - witness: `bridge::tests::native_path_module_round_trips`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret {
        Ok((left, right)) => self.context.arena().value_type(left).is_some() && self.context.arena().value_type(right).is_some() && self.context.arena().value_type(classifier).is_none_or(|held| !matches!(*held, gandr_core_term::ValueType::Sum(ref parts) if **parts != [left, right])),
        Err(CheckRefusal::ShapeMismatch { at: found_at, wanted, found }) => found_at == TermNode::Value(at) && wanted == ExpectedShape::Sum && found == TypeNode::Value(classifier),
        Err(_) => true,
    })]
    fn sum_expected(
        &mut self,
        at: ValueId,
        classifier: ValueTypeId,
    ) -> Result<(ValueTypeId, ValueTypeId), CheckRefusal>
    {
        let head = self.context.whnf_value_type(classifier)?;
        match matched_sum(self.context.arena_mut(), head) {
            | Maybe::Present(summands) => Ok(summands),
            | Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::Sum,
                    found: TypeNode::Value(classifier),
                },
            )),
        }
    }

    /// Read the element classifier of a native List expectation.
    ///
    /// # Specification
    /// - ensures: the element type at a List weak head, or an unknown element
    ///   when the classifier is unknown; no sum is unfolded.
    /// - fails: shape mismatch or the existing weak-head refusal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nil, cons, invalid head and invalid tail distinguish
    ///   the native rule.
    /// - witness: `bridge::tests::native_lists_check_and_round_trip`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|&element| self.context.arena().value_type(element).is_some()))]
    fn list_expected(
        &mut self,
        at: ValueId,
        classifier: ValueTypeId,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let head = self.context.whnf_value_type(classifier)?;
        match matched_list(self.context.arena_mut(), head) {
            | Maybe::Present(element) => Ok(element),
            | Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::List,
                    found: TypeNode::Value(classifier),
                },
            )),
        }
    }

    /// Advance the pure List fold's formation and typing premises.
    ///
    /// # Specification
    /// - requires: the preceding premise succeeded.
    /// - ensures: nil is checked in the ambient context; cons binds head then
    ///   folded result, and completing cons closes both binders.
    /// - fails: malformed source, type mismatch or existing formation refusal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold with distinct head and result classifiers
    ///   separates binder order and closure; malformed annotations are refused
    ///   before use.
    /// - witness: `bridge::tests::native_lists_check_and_round_trip`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)),
        ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == match phase {
            ListPhase::Nil => depth.saturating_add(2), ListPhase::Cons => depth.saturating_sub(2), _ => depth,
        })]
    fn list_fold(
        &mut self,
        at: ComputationId,
        classifier: CompTypeId,
        phase: ListPhase,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::ListFold {
            element,
            result,
            list,
            on_nil,
            on_cons,
        } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let (next, goal) = match phase {
            | ListPhase::Element => (ListPhase::Result, Goal::Form(TypeNode::Value(result))),
            | ListPhase::Result => {
                let expected = self.context.arena_mut().value_type_list(element);
                (ListPhase::Input, Goal::Value {
                    term: list,
                    direction: Direction::Check(expected),
                })
            },
            | ListPhase::Input => (ListPhase::Nil, Goal::Computation {
                term: on_nil,
                direction: Direction::Check(classifier),
            }),
            | ListPhase::Nil => {
                let result =
                    shift_value_type(self.context.arena_mut(), result, Binders::from(1_u32));
                let expected =
                    shift_comp_type(self.context.arena_mut(), classifier, Binders::from(2_u32));
                self.context.binders().open(Zone::Intuitionistic, element);
                self.context.binders().open(Zone::Intuitionistic, result);
                (ListPhase::Cons, Goal::Computation {
                    term: on_cons,
                    direction: Direction::Check(expected),
                })
            },
            | ListPhase::Cons => {
                self.close()?;
                self.close()?;
                return Ok(Step::Ascend(Produced::CompType(classifier)));
            },
        };
        self.frames.push(Frame::ListFold {
            at,
            result: classifier,
            phase: next,
        });
        Ok(Step::Descend(goal))
    }
}

/// The refusal a matched-type operation's absence answers: `mismatch` for a
/// known former other than the one asked for, a dangling node for an id the
/// arena does not hold.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `mismatch` for [`matching::Absent::Mismatched`];
///   [`CheckRefusal::DanglingNode`] naming `node` for
///   [`matching::Absent::Dangling`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the two arms, separated by an introduction against the
///   wrong former, which answers the mismatch.
/// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
#[spec(ensures: |ret| match absent {
    | matching::Absent::Mismatched => ret == mismatch,
    | matching::Absent::Dangling => ret == CheckRefusal::DanglingNode { node: CoreNode::Type(node) },
})]
fn unmatched(
    absent: matching::Absent,
    node: TypeNode,
    mismatch: CheckRefusal,
) -> CheckRefusal
{
    match absent {
        | matching::Absent::Mismatched => mismatch,
        | matching::Absent::Dangling => CheckRefusal::DanglingNode {
            node: CoreNode::Type(node),
        },
    }
}

/// The refusal of a value former the fragment has no rule for.
///
/// # Specification
/// trivial.
const fn unadmitted_value(
    term: ValueId,
    former: UnadmittedFormer,
) -> CheckRefusal
{
    CheckRefusal::OutOfFragment {
        at: CoreNode::Term(TermNode::Value(term)),
        former,
    }
}
#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_core_term::BinderDepth;
    use gandr_core_term::CompType;
    use gandr_core_term::CompTypeId;
    use gandr_core_term::Computation;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_core_term::Sort;
    use gandr_core_term::Value;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueType;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_core_term::hole::HoleId;
    use gandr_core_term::hole::MarkIndex;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::Side;
    use proptest::collection::vec;
    use proptest::prelude::ProptestConfig;
    use proptest::prelude::prop_assert;
    use proptest::prelude::prop_assert_eq;
    use proptest::prelude::proptest;

    use super::Frame;
    use super::Machine;
    use super::Marking;
    use super::Produced;
    use super::check_comp;
    use super::check_value;
    use super::checked;
    use super::synthesise_comp;
    use super::synthesise_value;
    use super::unadmitted_value;
    use crate::context::Atom;
    use crate::context::CheckBudget;
    use crate::context::CheckingContext;
    use crate::conversion::ConversionCount;
    use crate::conversion::comp_bridge;
    use crate::conversion::value_bridge;
    use crate::fixture::Mode;
    use crate::fixture::dangling_value;
    use crate::fixture::integer_literal;
    use crate::fixture::numeric_literal;
    use crate::fixture::seed;
    use crate::fixture::term_recipe;
    use crate::fixture::text_literal;
    use crate::fixture::type_recipe;
    use crate::fixture::typed_recipe;
    use crate::formation::form_comp_type;
    use crate::formation::form_value_type;
    use crate::refusal::CheckRefusal;
    use crate::refusal::CheckingForm;
    use crate::refusal::CoreNode;
    use crate::refusal::ExpectedShape;
    use crate::refusal::Mismatch;
    use crate::refusal::TermNode;
    use crate::refusal::TypeNode;
    use crate::refusal::UnadmittedFormer;

    /// One row of a rule table: the term, what it synthesises, the type it is
    /// checked against, and the crossings its check makes.
    type Row<Term, Type> = (
        Term,
        Result<Type, CheckRefusal>,
        Type,
        Result<ConversionCount, CheckRefusal>,
    );

    #[test]
    fn every_value_former_is_answered_in_both_modes()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let unit_type = arena.value_type_unit();
        let sum = arena.value_type_sum(&[unit_type, unit_type]);
        let returns_integer = arena.comp_type_returner(integer);
        let thunk_returns_integer = arena.value_type_thunk(returns_integer);
        let arrow = arena.comp_type_arrow(integer, returns_integer);
        let thunk_arrow = arena.value_type_thunk(arrow);
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let known = arena.value_constant(ConstantIndex::from(0_usize));
        let unknown = arena.value_constant(ConstantIndex::from(9_usize));
        let unit = arena.value_unit();
        let integer_value = arena.value_literal(integer_literal());
        let text = arena.value_literal(text_literal());
        let numeric = arena.value_literal(numeric_literal());
        let returned = arena.computation_return(integer_value);
        let thunk = arena.value_thunk(returned);
        let injection = arena.value_injection(Side::Left, unit);
        let lift = arena.value_lift(Level::zero(), unit);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[thunk_arrow]);
        let unbound = CheckRefusal::UnboundIndex {
            at: variable,
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
            depth: BinderDepth::from(0_usize),
        };
        let not_known = CheckRefusal::UnknownConstant {
            at: unknown,
            constant: ConstantIndex::from(9_usize),
        };
        let crossed_once = Ok(ConversionCount::from(1_usize));
        let rows: [Row<ValueId, ValueTypeId>; 10] = [
            (variable, Err(unbound), integer, Err(unbound)),
            (known, Ok(thunk_arrow), thunk_arrow, crossed_once),
            (unknown, Err(not_known), integer, Err(not_known)),
            (
                unit,
                Ok(context.atom(Atom::Unit).id()),
                unit_type,
                crossed_once,
            ),
            (
                integer_value,
                Ok(context.atom(Atom::Integer).id()),
                integer,
                crossed_once,
            ),
            (
                text,
                Ok(context.atom(Atom::String).id()),
                string,
                crossed_once,
            ),
            (
                numeric,
                Err(unadmitted_value(numeric, UnadmittedFormer::NumericLiteral)),
                integer,
                Err(unadmitted_value(numeric, UnadmittedFormer::NumericLiteral)),
            ),
            (
                thunk,
                Err(CheckRefusal::NotSynthesisable {
                    form: CheckingForm::Thunk(thunk),
                }),
                thunk_returns_integer,
                crossed_once,
            ),
            (
                injection,
                Err(CheckRefusal::NotSynthesisable {
                    form: CheckingForm::Injection(injection),
                }),
                sum,
                crossed_once,
            ),
            (
                lift,
                Err(unadmitted_value(lift, UnadmittedFormer::ValueLift)),
                unit_type,
                Err(unadmitted_value(lift, UnadmittedFormer::ValueLift)),
            ),
        ];
        for (term, synthesised, expected, checked) in rows {
            assert_eq!(
                synthesise_value(&mut context, term).map(|found| found.produced().id()),
                synthesised,
                "{term:?} synthesises by its former's rule"
            );
            let expected = form_value_type(&mut context, expected).unwrap();
            assert_eq!(
                check_value(&mut context, term, expected).map(|evidence| evidence.conversions()),
                checked,
                "{term:?} checks by its former's rule"
            );
        }
    }

    #[test]
    fn a_pair_synthesises_its_eager_product_and_checks_against_one()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit_type = arena.value_type_unit();
        let returns_integer = arena.comp_type_returner(integer);
        let suspended = arena.value_type_thunk(returns_integer);
        let product = arena.value_type_product(&[unit_type, integer]);
        let checking_only = arena.value_type_product(&[suspended, integer]);
        let unit = arena.value_unit();
        let zero = arena.value_literal(integer_literal());
        let returned = arena.computation_return(zero);
        let thunk = arena.value_thunk(returned);
        let pair = arena.value_pair(unit, zero);
        let with_thunk = arena.value_pair(thunk, zero);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let synthesised = synthesise_value(&mut context, pair)
            .map(|found| found.produced().id())
            .unwrap();
        let Some(held) = context.arena().value_type(synthesised)
        else {
            panic!("a pair synthesises an eager product");
        };
        let ValueType::Product(ref parts) = *held
        else {
            panic!("a pair synthesises an eager product");
        };
        let [first, second] = **parts
        else {
            panic!("the pair's product is binary");
        };
        assert_eq!(
            (first, second),
            (
                context.atom(Atom::Unit).id(),
                context.atom(Atom::Integer).id()
            ),
            "of its components' types, in order"
        );
        let product = form_value_type(&mut context, product).unwrap();
        let checking_only = form_value_type(&mut context, checking_only).unwrap();
        let integer = form_value_type(&mut context, integer).unwrap();
        assert_eq!(
            check_value(&mut context, pair, product).map(|evidence| evidence.conversions()),
            Ok(ConversionCount::from(2_usize)),
            "each component checks against its factor, crossing once"
        );
        assert_eq!(
            check_value(&mut context, with_thunk, checking_only)
                .map(|evidence| evidence.conversions()),
            Ok(ConversionCount::from(2_usize)),
            "a component that only checks is checked, not synthesised: the thunk's returned \
             literal and the second component each cross once"
        );
        assert_eq!(
            synthesise_value(&mut context, with_thunk).map(|found| found.produced().id()),
            Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Thunk(thunk),
            }),
            "while synthesis needs every component to synthesise"
        );
        assert_eq!(
            check_value(&mut context, pair, integer).map(|evidence| evidence.conversions()),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(pair),
                wanted: ExpectedShape::Product,
                found: TypeNode::Value(integer.id()),
            }),
            "a pair against no eager product is a shape mismatch"
        );
    }

    #[test]
    fn a_static_lambda_checks_only_against_a_static_pi()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let operator_type = arena.value_type_static_pi(small, small);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let identity = arena.value_static_lambda(bound);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let operator_type = form_value_type(&mut context, operator_type).unwrap();
        let integer = form_value_type(&mut context, integer).unwrap();
        assert_eq!(
            check_value(&mut context, identity, operator_type)
                .map(|evidence| evidence.conversions()),
            Ok(ConversionCount::from(1_usize)),
            "the body checks against the codomain beneath a binder of the domain"
        );
        assert_eq!(
            check_value(&mut context, identity, integer).map(|evidence| evidence.conversions()),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(identity),
                wanted: ExpectedShape::StaticPi,
                found: TypeNode::Value(integer.id()),
            }),
            "against any other former it is a shape mismatch"
        );
        assert_eq!(
            synthesise_value(&mut context, identity).map(|found| found.produced().id()),
            Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::StaticLambda(identity),
            }),
            "and it synthesises nothing"
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize),
            "every binder the checks opened is closed"
        );
    }

    #[test]
    fn every_comp_former_is_answered_in_both_modes()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns_integer);
        let thunk_arrow = arena.value_type_thunk(arrow);

        let unit = arena.value_unit();
        let integer_value = arena.value_literal(integer_literal());
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returns_variable = arena.computation_return(variable);
        let lambda = arena.computation_lambda(returns_variable);
        let function = arena.value_constant(ConstantIndex::from(0_usize));
        let force = arena.computation_force(function);
        let application = arena.computation_application(force, integer_value);
        let returned = arena.computation_return(integer_value);
        let bind = arena.computation_bind(application, force);
        let case = arena.computation_case(unit, returned, returned);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[thunk_arrow]);
        let crossed = |crossings: usize| Ok(ConversionCount::from(crossings));
        let rows: [Row<ComputationId, CompTypeId>; 5] = [
            (force, Ok(arrow), arrow, crossed(1)),
            (
                application,
                Ok(returns_integer),
                returns_integer,
                crossed(2),
            ),
            (
                lambda,
                Err(CheckRefusal::NotSynthesisable {
                    form: CheckingForm::Lambda(lambda),
                }),
                arrow,
                crossed(1),
            ),
            (
                returned,
                Err(CheckRefusal::NotSynthesisable {
                    form: CheckingForm::Return(returned),
                }),
                returns_integer,
                crossed(1),
            ),
            (bind, Ok(arrow), arrow, crossed(2)),
        ];
        for (term, synthesised, expected, checked) in rows {
            assert_eq!(
                synthesise_comp(&mut context, term).map(|found| found.produced().id()),
                synthesised,
                "{term:?} synthesises by its former's rule"
            );
            let expected = form_comp_type(&mut context, expected).unwrap();
            assert_eq!(
                check_comp(&mut context, term, expected).map(|evidence| evidence.conversions()),
                checked,
                "{term:?} checks by its former's rule"
            );
        }
        assert_eq!(
            synthesise_comp(&mut context, case).map(|found| found.produced().id()),
            Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Case(case)
            })
        );
        let expected = form_comp_type(&mut context, returns_integer).unwrap();
        let Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(at),
            wanted: ExpectedShape::Sum,
            found: TypeNode::Value(found),
        }) = check_comp(&mut context, case, expected)
        else {
            panic!("a unit scrutinee must report the required sum shape");
        };
        assert_eq!(at, unit);
        drop(context);
        assert_eq!(
            arena.value_type(found),
            Some(&ValueType::unit()),
            "the refusal reports the scrutinee's actual classifier, independent of arena allocation"
        );
    }

    #[test]
    fn a_bind_synthesises_its_continuations_type()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let returns_integer = arena.comp_type_returner(integer);
        let returns_string = arena.comp_type_returner(string);
        let arrow = arena.comp_type_arrow(integer, returns_string);
        let suspended_integer = arena.value_type_thunk(returns_integer);
        let suspended_arrow = arena.value_type_thunk(arrow);
        let produce = arena.value_constant(ConstantIndex::from(0_usize));
        let consume = arena.value_constant(ConstantIndex::from(1_usize));
        let bound = arena.computation_force(produce);
        let head = arena.computation_force(consume);
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let body = arena.computation_application(head, variable);
        let bind = arena.computation_bind(bound, body);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[suspended_integer, suspended_arrow]);

        assert_eq!(
            synthesise_comp(&mut context, bind).map(|found| found.produced().id()),
            Ok(returns_string),
            "the bind has its body's type, the bound name typed by the returner it eliminates"
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize),
            "the bind closes the binder it opened"
        );
    }

    #[test]
    fn host_operations_check_payloads_and_retain_effects()
    {
        use gandr_core_term::effect::EffectRow;
        use gandr_core_term::effect::host::HostSignatures;
        let mut arena = CoreArena::new();
        let host = HostSignatures::new(&mut arena).expect("host interfaces");
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let unit = arena.value_unit();
        let string = arena.value_literal(text_literal());
        for signature in [&host.exec, &host.fs, &host.proc, &host.env] {
            for operation in signature.operations() {
                let request =
                    arena.computation_perform(signature.clone(), operation.name.clone(), variable);
                let wrong_payload = if matches!(
                    arena.value_type(operation.payload),
                    Some(ValueType::Base(BaseType::String))
                ) {
                    unit
                }
                else {
                    string
                };
                let wrong = arena.computation_perform(
                    signature.clone(),
                    operation.name.clone(),
                    wrong_payload,
                );
                let unknown =
                    arena.computation_perform(signature.clone(), "missing".into(), variable);
                let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
                context
                    .binders()
                    .open(Zone::Intuitionistic, operation.payload);
                let inferred = synthesise_comp(&mut context, request)
                    .expect("typed host payload")
                    .produced()
                    .id();
                assert_eq!(
                    context.arena().comp_type(inferred),
                    Some(&gandr_core_term::CompType::Returner {
                        result: operation.reply,
                        effects: EffectRow::singleton(signature.clone())
                    })
                );
                assert!(
                    matches!(
                        synthesise_comp(&mut context, wrong),
                        Err(CheckRefusal::TypeMismatch(_) | CheckRefusal::ShapeMismatch { .. })
                    ),
                    "{} rejects the wrong payload",
                    operation.name.as_ref()
                );
                assert_eq!(
                    synthesise_comp(&mut context, unknown).unwrap_err(),
                    CheckRefusal::UnknownOperation { at: unknown }
                );
                assert_eq!(
                    context.binders().depth(Zone::Intuitionistic),
                    BinderDepth::from(1_usize)
                );
            }
        }
        let nil = arena.value_list_nil();
        let strings = arena.value_list_cons(string, nil);
        let mode = arena.value_pair(strings, string);
        let command = arena.value_pair(string, mode);
        let good = arena.computation_perform(host.exec.clone(), "exec".into(), command);
        let integer = arena.value_literal(integer_literal());
        let integers = arena.value_list_cons(integer, nil);
        let mode = arena.value_pair(integers, string);
        let command = arena.value_pair(string, mode);
        let bad = arena.computation_perform(host.exec, "exec".into(), command);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let inferred = synthesise_comp(&mut context, good)
            .expect("native string arguments")
            .produced();
        check_comp(&mut context, good, inferred).expect("perform checks by row subsumption");
        assert!(matches!(
            synthesise_comp(&mut context, bad),
            Err(CheckRefusal::TypeMismatch(_))
        ));
    }

    #[test]
    fn handlers_discharge_only_their_own_interface()
    {
        use gandr_core_term::control::EffectClause;
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectRow;
        use gandr_core_term::effect::EffectSig;
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let integer_type = arena.value_type_base(BaseType::Integer);
        let string_type = arena.value_type_base(BaseType::String);
        let answer = arena.comp_type_returner(string_type);
        let signature = EffectSig::new("Ask".into(), [EffectOp {
            name: "ask".into(),
            payload: unit_type,
            reply: integer_type,
        }])
        .unwrap();
        let other = EffectSig::new("Other".into(), [EffectOp {
            name: "other".into(),
            payload: unit_type,
            reply: string_type,
        }])
        .unwrap();
        let allowed =
            arena.comp_type_returner_with_effects(string_type, EffectRow::singleton(other.clone()));
        let unit = arena.value_unit();
        let integer = arena.value_literal(integer_literal());
        let string = arena.value_literal(text_literal());
        let zero = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let one = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let returned = arena.computation_return(string);
        let reply = arena.computation_return(integer);
        let first_resume = arena.computation_resume(zero, reply);
        let second_resume = arena.computation_resume(one, reply);
        let twice = arena.computation_bind(first_resume, second_resume);
        let clauses: alloc::sync::Arc<[_]> = [EffectClause {
            operation: "ask".into(),
            body: twice,
        }]
        .into();
        let subject = arena.computation_perform(signature.clone(), "ask".into(), unit);
        let good = arena.computation_handle(
            signature.clone(),
            subject,
            returned,
            alloc::sync::Arc::clone(&clauses),
        );
        let wrong_return = arena.computation_return(zero);
        let wrong_return = arena.computation_handle(
            signature.clone(),
            subject,
            wrong_return,
            alloc::sync::Arc::clone(&clauses),
        );
        let wrong_binder = arena.computation_resume(one, reply);
        let wrong_binder = arena.computation_handle(
            signature.clone(),
            subject,
            returned,
            [EffectClause {
                operation: "ask".into(),
                body: wrong_binder,
            }]
            .into(),
        );
        let missing = arena.computation_handle(signature.clone(), subject, returned, [].into());
        let unknown = arena.computation_handle(
            signature.clone(),
            subject,
            returned,
            [EffectClause {
                operation: "missing".into(),
                body: twice,
            }]
            .into(),
        );
        let extended = EffectSig::new("Ask".into(), [
            EffectOp {
                name: "ask".into(),
                payload: unit_type,
                reply: integer_type,
            },
            EffectOp {
                name: "tell".into(),
                payload: string_type,
                reply: unit_type,
            },
        ])
        .unwrap();
        let repeated = arena.computation_handle(
            extended,
            subject,
            returned,
            [
                EffectClause {
                    operation: "ask".into(),
                    body: twice,
                },
                EffectClause {
                    operation: "ask".into(),
                    body: twice,
                },
            ]
            .into(),
        );
        let other_request = arena.computation_perform(other, "other".into(), unit);
        let both = arena.computation_bind(subject, other_request);
        let residual = arena.computation_handle(signature.clone(), both, returned, clauses);
        let leaking_clause = arena.computation_bind(first_resume, other_request);
        let leaking_clause = arena.computation_handle(
            signature,
            subject,
            returned,
            [EffectClause {
                operation: "ask".into(),
                body: leaking_clause,
            }]
            .into(),
        );
        let conflict = EffectSig::new("Ask".into(), [EffectOp {
            name: "ask".into(),
            payload: unit_type,
            reply: string_type,
        }])
        .unwrap();
        let conflict = arena.computation_handle(
            conflict,
            subject,
            returned,
            [EffectClause {
                operation: "ask".into(),
                body: returned,
            }]
            .into(),
        );
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let answer = form_comp_type(&mut context, answer).unwrap();
        let allowed = form_comp_type(&mut context, allowed).unwrap();
        check_comp(&mut context, good, answer).expect("a deep resumption may be used twice");
        assert!(matches!(
            check_comp(&mut context, wrong_return, answer),
            Err(CheckRefusal::TypeMismatch(_))
        ));
        assert!(matches!(
            check_comp(&mut context, wrong_binder, answer),
            Err(CheckRefusal::ShapeMismatch {
                wanted: ExpectedShape::Stack,
                ..
            })
        ));
        for malformed in [missing, unknown, repeated] {
            assert_eq!(
                check_comp(&mut context, malformed, answer).unwrap_err(),
                CheckRefusal::HandlerCoverage { at: malformed }
            );
        }
        assert!(matches!(
            check_comp(&mut context, residual, answer),
            Err(CheckRefusal::TypeMismatch(_))
        ));
        check_comp(&mut context, residual, allowed)
            .expect("an unrelated effect remains in the answer row");
        assert!(matches!(
            check_comp(&mut context, leaking_clause, answer),
            Err(CheckRefusal::TypeMismatch(_))
        ));
        assert!(matches!(
            check_comp(&mut context, conflict, answer),
            Err(CheckRefusal::EffectSignatureConflict { .. })
        ));
        assert_eq!(
            synthesise_comp(&mut context, good).unwrap_err(),
            CheckRefusal::NotSynthesisable {
                form: CheckingForm::Handle(good)
            }
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn control_rules_preserve_rows_scopes_and_shapes()
    {
        use gandr_core_term::control::StackFrame;
        use gandr_kernel_term::Side;
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let integer_type = arena.value_type_base(BaseType::Integer);
        let string_type = arena.value_type_base(BaseType::String);
        let returned_unit = arena.comp_type_returner(unit_type);
        let returned_integer = arena.comp_type_returner(integer_type);
        let returned_string = arena.comp_type_returner(string_type);
        let ambient_type = arena.value_type_unit();
        let arrow = arena.comp_type_arrow(ambient_type, returned_integer);
        let pair = arena.comp_type_with(returned_unit, arrow);
        let suspended_pair = arena.value_type_thunk(pair);
        let outer = arena.value_constant(ConstantIndex::from(0_usize));
        let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let forced = arena.computation_force(outer);
        let stack = arena.value_reify(
            [
                StackFrame::Bind(forced),
                StackFrame::Project(Side::Right),
                StackFrame::Apply(argument),
            ]
            .into(),
        );
        let classifier = arena.value_type_stack(returned_integer, returned_integer);
        let effectful = arena.comp_type_returner_with_effects(
            integer_type,
            effect_row("Ask".into(), unit_type, integer_type),
        );
        let bad_classifier = arena.value_type_stack(effectful, returned_integer);
        let bad_stack = arena.value_reify([StackFrame::Project(Side::Left)].into());
        let code_type = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let bound_code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(bound_code, Level::zero());
        let returned_element = arena.comp_type_returner(element);
        let dependent = arena.comp_type_pi(code_type, returned_element);
        let quoted_string = arena.value_quote(string_type);
        let dependent_stack = arena.value_reify([StackFrame::Apply(quoted_string)].into());
        let dependent_classifier = arena.value_type_stack(dependent, returned_string);
        let unit = arena.value_unit();
        let integer = arena.value_literal(integer_literal());
        let string = arena.value_literal(text_literal());
        let return_unit = arena.computation_return(unit);
        let return_integer = arena.computation_return(integer);
        let return_string = arena.computation_return(string);
        let continuation = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let resumed = arena.computation_resume(continuation, return_integer);
        let shift = arena.computation_shift(resumed);
        let reset = arena.computation_reset(shift);
        let wrong_shift = arena.computation_shift(return_string);
        let wrong_reset = arena.computation_reset(wrong_shift);
        let negative_pair = arena.computation_with(reset, return_string);
        let negative_pair_type = arena.comp_type_with(returned_integer, returned_string);
        let nested = arena.computation_reset(negative_pair);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[suspended_pair]);
        context.binders().open(Zone::Intuitionistic, ambient_type);
        let classifier = form_value_type(&mut context, classifier).unwrap();
        check_value(&mut context, stack, classifier)
            .expect("later frames do not retain the bind's integer binder");
        let bad_classifier = form_value_type(&mut context, bad_classifier).unwrap();
        assert!(matches!(
            check_value(&mut context, stack, bad_classifier),
            Err(CheckRefusal::ShapeMismatch {
                wanted: ExpectedShape::Returner,
                ..
            })
        ));
        assert!(matches!(
            check_value(&mut context, bad_stack, classifier),
            Err(CheckRefusal::ShapeMismatch {
                wanted: ExpectedShape::With,
                ..
            })
        ));
        let dependent_classifier = form_value_type(&mut context, dependent_classifier).unwrap();
        check_value(&mut context, dependent_stack, dependent_classifier)
            .expect("stack application instantiates its Pi output");
        assert_eq!(
            synthesise_value(&mut context, stack).unwrap_err(),
            CheckRefusal::NotSynthesisable {
                form: CheckingForm::Reify(stack)
            }
        );
        let integer_answer = form_comp_type(&mut context, returned_integer).unwrap();
        check_comp(&mut context, reset, integer_answer).expect("capture and resume");
        assert_eq!(
            check_comp(&mut context, shift, integer_answer).unwrap_err(),
            CheckRefusal::ShiftWithoutReset { at: shift }
        );
        assert!(matches!(
            check_comp(&mut context, wrong_reset, integer_answer),
            Err(CheckRefusal::TypeMismatch(_))
        ));
        let pair_answer = form_comp_type(&mut context, negative_pair_type).unwrap();
        check_comp(&mut context, nested, pair_answer)
            .expect("the inner reset supplies its own answer");
        for (term, form) in [
            (reset, CheckingForm::Reset(reset)),
            (shift, CheckingForm::Shift(shift)),
            (negative_pair, CheckingForm::With(negative_pair)),
        ] {
            assert_eq!(
                synthesise_comp(&mut context, term).unwrap_err(),
                CheckRefusal::NotSynthesisable { form }
            );
        }
        let resume_type = context
            .arena_mut()
            .value_type_stack(returned_integer, returned_string);
        context.binders().open(Zone::Intuitionistic, resume_type);
        let inferred = synthesise_comp(&mut context, resumed)
            .expect("resume delivers its output, not its input")
            .produced()
            .id();
        assert_eq!(inferred, returned_string);
        let wrong = context
            .arena_mut()
            .computation_resume(continuation, return_unit);
        assert!(matches!(
            synthesise_comp(&mut context, wrong),
            Err(CheckRefusal::TypeMismatch(_))
        ));
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(2_usize)
        );
    }

    #[test]
    fn reset_answers_are_weakened_through_intervening_binders()
    {
        let mut arena = CoreArena::new();
        let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(code, Level::zero());
        let outer_code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let result = arena.value_type_element(outer_code, Level::zero());
        let result = arena.comp_type_returner(result);
        let unit = arena.value_type_unit();
        let answer = arena.comp_type_arrow(unit, result);
        let outer_value = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
        let returned = arena.computation_return(outer_value);
        let body = arena.computation_lambda(returned);
        let shifted = arena.computation_shift(body);
        let body = arena.computation_lambda(shifted);
        let reset = arena.computation_reset(body);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.binders().open(Zone::Intuitionistic, universe);
        context.binders().open(Zone::Intuitionistic, element);
        let answer = form_comp_type(&mut context, answer).unwrap();
        check_comp(&mut context, reset, answer).expect("answer code refers to the outer type binder through both lambdas and the captured stack");
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(2_usize)
        );
    }

    #[test]
    fn pure_bind_into_lambda_is_unchanged()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit = arena.value_type_unit();
        let result = arena.comp_type_returner(integer);
        let expected = arena.comp_type_arrow(unit, result);
        let value = arena.value_literal(integer_literal());
        let add = gandr_core_term::primitive::PRELUDE
            .iter()
            .copied()
            .find(|primitive| primitive.name().as_ref() == "add")
            .expect("native add");
        let bound = arena.computation_primitive(
            add,
            gandr_core_term::primitive::Arguments::Binary([value, value]),
        );
        let outer = arena.value_variable(Zone::Intuitionistic, 1_u32.into());
        let returned = arena.computation_return(outer);
        let lambda = arena.computation_lambda(returned);
        let program = arena.computation_bind(bound, lambda);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let expected = form_comp_type(&mut context, expected).unwrap();
        check_comp(&mut context, program, expected)
            .expect("a pure bind may continue with a negative computation");
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn effectful_bind_into_lambda_is_shape_mismatch()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit_type = arena.value_type_unit();
        let result = arena.comp_type_returner(integer);
        let expected = arena.comp_type_arrow(unit_type, result);
        let signature = effect_row("E".into(), unit_type, integer)
            .signatures()
            .next()
            .expect("one interface")
            .clone();
        let unit = arena.value_unit();
        let bound = arena.computation_perform(signature, "run".into(), unit);
        let outer = arena.value_variable(Zone::Intuitionistic, 1_u32.into());
        let returned = arena.computation_return(outer);
        let lambda = arena.computation_lambda(returned);
        let program = arena.computation_bind(bound, lambda);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let formed = form_comp_type(&mut context, expected).unwrap();
        assert_eq!(
            check_comp(&mut context, program, formed).unwrap_err(),
            CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(program),
                wanted: ExpectedShape::Returner,
                found: TypeNode::Computation(expected)
            }
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn a_stack_bind_cannot_export_its_local_type_code()
    {
        use gandr_core_term::control::StackFrame;
        let mut arena = CoreArena::new();
        let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let code = arena.value_variable(Zone::Intuitionistic, 0_u32.into());
        let element = arena.value_type_element(code, Level::zero());
        let result = arena.comp_type_returner(element);
        let function = arena.comp_type_pi(universe, result);
        let suspended = arena.value_type_thunk(function);
        let constant = arena.value_constant(ConstantIndex::from(0_usize));
        let forced = arena.computation_force(constant);
        let body = arena.computation_application(forced, code);
        let stack = arena.value_reify([StackFrame::Bind(body)].into());
        let input = arena.comp_type_returner(universe);
        let unit = arena.value_type_unit();
        let output = arena.comp_type_returner(unit);
        let expected = arena.value_type_stack(input, output);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[suspended]);
        let expected = form_value_type(&mut context, expected).unwrap();
        assert!(
            matches!(check_value(&mut context, stack, expected), Err(CheckRefusal::DependentStack { at, .. }) if at == stack)
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn stack_bind_accumulates_input_and_body_rows()
    {
        use gandr_core_term::control::StackFrame;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let left = effect_row("Input".into(), integer, integer);
        let right = effect_row("Body".into(), integer, integer);
        let both = left.union(&right, &arena).expect("disjoint names");
        let input = arena.comp_type_returner_with_effects(integer, left);
        let output = arena.comp_type_returner_with_effects(integer, both);
        let missing = arena.comp_type_returner_with_effects(integer, right.clone());
        let value = arena.value_variable(Zone::Intuitionistic, 0_u32.into());
        let signature = right.signatures().next().expect("one interface").clone();
        let body = arena.computation_perform(signature, "run".into(), value);
        let stack = arena.value_reify([StackFrame::Bind(body)].into());
        let expected = arena.value_type_stack(input, output);
        let dropped_input = arena.value_type_stack(input, missing);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let expected = form_value_type(&mut context, expected).unwrap();
        check_value(&mut context, stack, expected).expect("the output retains both rows");
        let missing = form_value_type(&mut context, dropped_input).unwrap();
        assert!(matches!(
            check_value(&mut context, stack, missing),
            Err(CheckRefusal::TypeMismatch(_))
        ));
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    /// A one-operation interface for checking row accumulation.
    ///
    /// # Specification
    /// trivial.
    fn effect_row(
        name: gandr_core_term::effect::EffectName,
        payload: ValueTypeId,
        reply: ValueTypeId,
    ) -> gandr_core_term::effect::EffectRow
    {
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectRow;
        use gandr_core_term::effect::EffectSig;
        use gandr_core_term::effect::OperationName;
        EffectRow::singleton(
            EffectSig::new(name, [EffectOp {
                name: OperationName::from("run"),
                payload,
                reply,
            }])
            .expect("one operation"),
        )
    }

    /// The interface with no operations: its handler has no operation clauses.
    ///
    /// # Specification
    /// trivial.
    fn empty_interface() -> gandr_core_term::effect::EffectSig
    {
        gandr_core_term::effect::EffectSig::new("Empty".into(), []).expect("no operations")
    }

    #[test]
    fn handle_against_a_non_returner_is_stuck()
    {
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let returns_unit = arena.comp_type_returner(unit_type);
        let arrow = arena.comp_type_arrow(unit_type, returns_unit);
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        let handler = arena.computation_handle(empty_interface(), returned, returned, [].into());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let arrow = form_comp_type(&mut context, arrow).unwrap();
        assert!(matches!(
            check_comp(&mut context, handler, arrow),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Returner,
                ..
            }) if at == handler
        ));
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn handle_of_a_non_returner_scrutinee_is_a_shape_mismatch()
    {
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let returns_unit = arena.comp_type_returner(unit_type);
        let arrow = arena.comp_type_arrow(unit_type, returns_unit);
        let suspended = arena.value_type_thunk(arrow);
        let function = arena.value_constant(ConstantIndex::from(0_usize));
        let subject = arena.computation_force(function);
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        let handler = arena.computation_handle(empty_interface(), subject, returned, [].into());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[suspended]);
        let answer = form_comp_type(&mut context, returns_unit).unwrap();
        assert!(matches!(
            check_comp(&mut context, handler, answer),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Returner,
                found: TypeNode::Computation(found),
            }) if at == handler && found == arrow
        ));
    }

    #[test]
    fn empty_signature_handler_finishes_after_the_return_clause()
    {
        let mut arena = CoreArena::new();
        let integer_type = arena.value_type_base(BaseType::Integer);
        let answer = arena.comp_type_returner(integer_type);
        let suspended = arena.value_type_thunk(answer);
        let pure = arena.value_constant(ConstantIndex::from(0_usize));
        let subject = arena.computation_force(pure);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let on_return = arena.computation_return(bound);
        let handler = arena.computation_handle(empty_interface(), subject, on_return, [].into());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[suspended]);
        let answer = form_comp_type(&mut context, answer).unwrap();
        check_comp(&mut context, handler, answer)
            .expect("a subject that performs nothing leaves the pure answer");
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn handle_against_unknown_answer()
    {
        use gandr_core_term::control::EffectClause;
        use gandr_core_term::effect::EffectOp;
        use gandr_core_term::effect::EffectSig;
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let integer_type = arena.value_type_base(BaseType::Integer);
        let unknown = arena.comp_type_unknown();
        let signature = EffectSig::new("Ask".into(), [EffectOp {
            name: "ask".into(),
            payload: unit_type,
            reply: integer_type,
        }])
        .unwrap();
        let unit = arena.value_unit();
        let subject = arena.computation_perform(signature.clone(), "ask".into(), unit);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let on_return = arena.computation_return(bound);
        let reply = arena.value_literal(integer_literal());
        let replied = arena.computation_return(reply);
        let resumed = arena.computation_resume(bound, replied);
        let held = arena.computation_hole(HoleId::from(0_u32));
        let handler = |arena: &mut CoreArena, body| {
            arena.computation_handle(
                signature.clone(),
                subject,
                on_return,
                [EffectClause {
                    operation: "ask".into(),
                    body,
                }]
                .into(),
            )
        };
        let resuming = handler(&mut arena, resumed);
        let holed = handler(&mut arena, held);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let unknown = form_comp_type(&mut context, unknown).unwrap();
        for term in [resuming, holed] {
            check_comp(&mut context, term, unknown)
                .expect("a handler against the unknown answer checks through the matched returner");
            assert_eq!(
                context.binders().depth(Zone::Intuitionistic),
                BinderDepth::from(0_usize)
            );
        }
        assert_eq!(
            synthesise_comp(&mut context, resuming).unwrap_err(),
            CheckRefusal::NotSynthesisable {
                form: CheckingForm::Handle(resuming)
            }
        );
    }

    /// `F Integer` and `F^⟨State⟩ Integer`, the first below the second, in the
    /// arena that holds them.
    ///
    /// # Specification
    /// trivial.
    fn pure_and_stateful() -> (CoreArena, CompTypeId, CompTypeId)
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let pure = arena.comp_type_returner(integer);
        let stateful = arena
            .comp_type_returner_with_effects(integer, effect_row("State".into(), integer, integer));
        (arena, pure, stateful)
    }

    #[test]
    fn reify_empty_stack_is_identity()
    {
        let (mut arena, pure, _) = pure_and_stateful();
        let unit = arena.value_type_unit();
        let other = arena.comp_type_returner(unit);
        let stack = arena.value_reify([].into());
        let identity = arena.value_type_stack(pure, pure);
        let changed = arena.value_type_stack(pure, other);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let identity = form_value_type(&mut context, identity).unwrap();
        check_value(&mut context, stack, identity)
            .expect("the empty stack delivers what it consumes");
        let changed = form_value_type(&mut context, changed).unwrap();
        assert!(matches!(
            check_value(&mut context, stack, changed),
            Err(CheckRefusal::TypeMismatch(_))
        ));
    }

    #[test]
    fn reify_delivered_answer_subsumes_up()
    {
        let (mut arena, pure, stateful) = pure_and_stateful();
        let stack = arena.value_reify([].into());
        let widened = arena.value_type_stack(pure, stateful);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let widened = form_value_type(&mut context, widened).unwrap();
        check_value(&mut context, stack, widened)
            .expect("the delivered pure answer subsumes to the effectful one");
    }

    #[test]
    fn reify_delivered_answer_cannot_drop_a_row()
    {
        let (mut arena, pure, stateful) = pure_and_stateful();
        let stack = arena.value_reify([].into());
        let dropped = arena.value_type_stack(stateful, pure);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let dropped = form_value_type(&mut context, dropped).unwrap();
        assert!(matches!(
            check_value(&mut context, stack, dropped),
            Err(CheckRefusal::TypeMismatch(_))
        ));
    }

    #[test]
    fn reify_against_non_stack_type_is_stuck()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let stack = arena.value_reify([].into());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let integer = form_value_type(&mut context, integer).unwrap();
        assert!(matches!(
            check_value(&mut context, stack, integer),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(at),
                wanted: ExpectedShape::Stack,
                ..
            }) if at == stack
        ));
    }

    #[test]
    fn reify_interior_bind_frame_threads_the_accumulated_row()
    {
        use gandr_core_term::control::StackFrame;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let input_row = effect_row("Input".into(), integer, integer);
        let body_row = effect_row("Body".into(), integer, integer);
        let both = input_row.union(&body_row, &arena).expect("disjoint names");
        let input = arena.comp_type_returner_with_effects(integer, input_row);
        let output = arena.comp_type_returner_with_effects(integer, both);
        let laundered = arena.comp_type_returner_with_effects(integer, body_row.clone());
        let bound = arena.value_variable(Zone::Intuitionistic, 0_u32.into());
        let signature = body_row.signatures().next().expect("one interface").clone();
        let performed = arena.computation_perform(signature.clone(), "run".into(), bound);
        let passed_on = arena.computation_perform(signature, "run".into(), bound);
        let stack =
            arena.value_reify([StackFrame::Bind(performed), StackFrame::Bind(passed_on)].into());
        let threaded = arena.value_type_stack(input, output);
        let laundered = arena.value_type_stack(input, laundered);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let threaded = form_value_type(&mut context, threaded).unwrap();
        check_value(&mut context, stack, threaded)
            .expect("the later frame receives the interior frame's row");
        let laundered = form_value_type(&mut context, laundered).unwrap();
        assert!(matches!(
            check_value(&mut context, stack, laundered),
            Err(CheckRefusal::TypeMismatch(_))
        ));
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn resume_of_a_non_stack_is_a_shape_mismatch()
    {
        let mut arena = CoreArena::new();
        let zero = arena.value_literal(integer_literal());
        let fed = arena.computation_return(zero);
        let resume = arena.computation_resume(zero, fed);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert!(matches!(
            synthesise_comp(&mut context, resume),
            Err(CheckRefusal::ShapeMismatch {
                wanted: ExpectedShape::Stack,
                ..
            })
        ));
    }

    #[test]
    fn resume_delivering_a_row_cannot_drop_it()
    {
        let (mut arena, pure, stateful) = pure_and_stateful();
        let stack_type = arena.value_type_stack(stateful, stateful);
        let continuation = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let zero = arena.value_literal(integer_literal());
        let fed = arena.computation_return(zero);
        let resume = arena.computation_resume(continuation, fed);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.binders().open(Zone::Intuitionistic, stack_type);
        let pure = form_comp_type(&mut context, pure).unwrap();
        assert!(matches!(
            check_comp(&mut context, resume, pure),
            Err(CheckRefusal::TypeMismatch(_))
        ));
    }

    #[test]
    fn resume_delivered_answer_subsumes_up()
    {
        let (mut arena, pure, stateful) = pure_and_stateful();
        let stack_type = arena.value_type_stack(pure, pure);
        let continuation = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let zero = arena.value_literal(integer_literal());
        let fed = arena.computation_return(zero);
        let resume = arena.computation_resume(continuation, fed);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.binders().open(Zone::Intuitionistic, stack_type);
        let stateful = form_comp_type(&mut context, stateful).unwrap();
        check_comp(&mut context, resume, stateful)
            .expect("the delivered pure answer subsumes to the effectful one");
    }

    #[test]
    fn resume_of_a_hole_infers_unknown()
    {
        let mut arena = CoreArena::new();
        let hole = arena.value_hole(HoleId::from(0_u32));
        let zero = arena.value_literal(integer_literal());
        let fed = arena.computation_return(zero);
        let resume = arena.computation_resume(hole, fed);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let inferred = synthesise_comp(&mut context, resume)
            .expect("a hole in stack position localizes rather than cascading")
            .produced()
            .id();
        assert_eq!(
            context.arena().comp_type(inferred),
            Some(&CompType::Unknown)
        );
    }

    #[test]
    fn reset_is_transparent_on_the_type()
    {
        let (mut arena, pure, _) = pure_and_stateful();
        let unit = arena.value_type_unit();
        let other = arena.comp_type_returner(unit);
        let zero = arena.value_literal(integer_literal());
        let returned = arena.computation_return(zero);
        let reset = arena.computation_reset(returned);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let pure = form_comp_type(&mut context, pure).unwrap();
        check_comp(&mut context, reset, pure).expect("a reset checks at its body's answer");
        let other = form_comp_type(&mut context, other).unwrap();
        assert!(matches!(
            check_comp(&mut context, reset, other),
            Err(CheckRefusal::TypeMismatch(_))
        ));
    }

    #[test]
    fn shift_binds_the_continuation_at_the_captured_type()
    {
        let (mut arena, pure, _) = pure_and_stateful();
        let unit = arena.value_unit();
        let continuation = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let fed = arena.computation_return(unit);
        let resumed = arena.computation_resume(continuation, fed);
        let shift = arena.computation_shift(resumed);
        let reset = arena.computation_reset(shift);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let pure = form_comp_type(&mut context, pure).unwrap();
        assert!(matches!(
            check_comp(&mut context, reset, pure),
            Err(CheckRefusal::TypeMismatch(_))
        ));
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn bind_unions_effect_rows()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let string = arena.value_type_base(BaseType::String);
        let first =
            arena.comp_type_returner_with_effects(unit, effect_row("IO".into(), unit, unit));
        let second =
            arena.comp_type_returner_with_effects(string, effect_row("State".into(), unit, string));
        let types = [
            arena.value_type_thunk(first),
            arena.value_type_thunk(second),
        ];
        let first_value = arena.value_constant(ConstantIndex::from(0_usize));
        let second_value = arena.value_constant(ConstantIndex::from(1_usize));
        let bound = arena.computation_force(first_value);
        let body = arena.computation_force(second_value);
        let bind = arena.computation_bind(bound, body);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &types);
        let produced = synthesise_comp(&mut context, bind)
            .expect("compatible interfaces")
            .produced()
            .id();
        let Some(&gandr_core_term::CompType::Returner {
            result,
            ref effects,
        }) = context.arena().comp_type(produced)
        else {
            panic!("bind returner");
        };
        assert_eq!(result, string);
        assert_eq!(
            effects
                .signatures()
                .map(|signature| signature.name().as_ref())
                .collect::<Vec<_>>(),
            ["IO", "State"]
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn check_mode_bind_subsumes_the_accumulated_row()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let demanded =
            arena.comp_type_returner_with_effects(unit, effect_row("IO".into(), unit, unit));
        let pure = arena.comp_type_returner(unit);
        let suspended = arena.value_type_thunk(demanded);
        let producer = arena.value_constant(ConstantIndex::from(0_usize));
        let bound = arena.computation_force(producer);
        let returned = arena.value_unit();
        let body = arena.computation_return(returned);
        let bind = arena.computation_bind(bound, body);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[suspended]);
        let expected = form_comp_type(&mut context, pure).expect("pure returner");
        let Err(CheckRefusal::TypeMismatch(Mismatch::Computation {
            at,
            synthesised,
            expected: found,
        })) = check_comp(&mut context, bind, expected)
        else {
            panic!("the bound effect cannot disappear into a pure continuation");
        };
        assert_eq!((at, found), (bind, pure));
        assert!(
            matches!(context.arena().comp_type(synthesised), Some(gandr_core_term::CompType::Returner { effects, .. }) if effects.contains(&"IO".into()) == gandr_core_term::effect::EffectPresence::Present)
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn check_mode_bind_accepts_a_contained_row()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let io = effect_row("IO".into(), unit, unit);
        let allowed = io
            .union(&effect_row("State".into(), unit, unit), &arena)
            .expect("distinct interfaces");
        let demanded = arena.comp_type_returner_with_effects(unit, io);
        let answer = arena.comp_type_returner_with_effects(unit, allowed);
        let suspended = arena.value_type_thunk(demanded);
        let producer = arena.value_constant(ConstantIndex::from(0_usize));
        let bound = arena.computation_force(producer);
        let value = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(value);
        let bind = arena.computation_bind(bound, body);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[suspended]);
        let expected = form_comp_type(&mut context, answer).expect("rowful returner");
        assert!(check_comp(&mut context, bind, expected).is_ok());
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn bind_refuses_conflicting_operation_types_without_replacing_a_signature()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let string = arena.value_type_base(BaseType::String);
        let first =
            arena.comp_type_returner_with_effects(unit, effect_row("IO".into(), unit, unit));
        let second =
            arena.comp_type_returner_with_effects(unit, effect_row("IO".into(), string, unit));
        let types = [
            arena.value_type_thunk(first),
            arena.value_type_thunk(second),
        ];
        let first_value = arena.value_constant(ConstantIndex::from(0_usize));
        let second_value = arena.value_constant(ConstantIndex::from(1_usize));
        let bound = arena.computation_force(first_value);
        let body = arena.computation_force(second_value);
        let bind = arena.computation_bind(bound, body);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &types);
        assert_eq!(
            synthesise_comp(&mut context, bind).map(|found| found.produced().id()),
            Err(CheckRefusal::EffectSignatureConflict {
                at: bind,
                first,
                second
            })
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }

    #[test]
    fn a_bind_checks_against_the_expected_computation()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let returns_integer = arena.comp_type_returner(integer);
        let returns_string = arena.comp_type_returner(string);
        let suspended_integer = arena.value_type_thunk(returns_integer);
        let produce = arena.value_constant(ConstantIndex::from(0_usize));
        let bound = arena.computation_force(produce);
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(variable);
        let bind = arena.computation_bind(bound, body);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[suspended_integer]);
        let expected = form_comp_type(&mut context, returns_integer).unwrap();
        let wrong = form_comp_type(&mut context, returns_string).unwrap();

        assert_eq!(
            check_comp(&mut context, bind, expected).map(|evidence| evidence.conversions()),
            Ok(ConversionCount::from(1_usize)),
            "the body checks against the expected type, under the bound name"
        );
        assert_eq!(
            check_comp(&mut context, bind, wrong).map(|evidence| evidence.conversions()),
            Err(CheckRefusal::TypeMismatch(Mismatch::Value {
                at: variable,
                synthesised: integer,
                expected: string,
            })),
            "the bound name has the type its returner returns, whatever the bind is checked \
             against"
        );
        assert_eq!(
            synthesise_comp(&mut context, bind).map(|found| found.produced().id()),
            Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Return(body),
            }),
            "a body that only checks leaves the bind with nothing to synthesise"
        );
    }

    #[test]
    fn a_bind_of_a_non_returner_is_a_shape_mismatch()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns_integer);
        let suspended_arrow = arena.value_type_thunk(arrow);
        let function = arena.value_constant(ConstantIndex::from(0_usize));
        let bound = arena.computation_force(function);
        let unit = arena.value_unit();
        let body = arena.computation_return(unit);
        let bind = arena.computation_bind(bound, body);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[suspended_arrow]);
        let expected = form_comp_type(&mut context, returns_integer).unwrap();
        let refusal = CheckRefusal::ShapeMismatch {
            at: TermNode::Computation(bound),
            wanted: ExpectedShape::Returner,
            found: TypeNode::Computation(arrow),
        };

        assert_eq!(
            synthesise_comp(&mut context, bind).map(|found| found.produced().id()),
            Err(refusal),
            "a bound function returns nothing to bind"
        );
        assert_eq!(
            check_comp(&mut context, bind, expected).map(|evidence| evidence.conversions()),
            Err(refusal),
            "the refusal is the bound computation's, whatever the bind is checked against"
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize),
            "a refused bind opened no binder"
        );
    }

    #[test]
    fn a_mismatched_literal_is_refused_with_both_types()
    {
        let mut arena = CoreArena::new();
        let string = arena.value_type_base(BaseType::String);
        let integer_value = arena.value_literal(integer_literal());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let expected = form_value_type(&mut context, string).unwrap();
        let refusal = check_value(&mut context, integer_value, expected).unwrap_err();
        assert_eq!(
            refusal,
            CheckRefusal::TypeMismatch(Mismatch::Value {
                at: integer_value,
                synthesised: context.atom(Atom::Integer).id(),
                expected: string,
            }),
            "the value bridge names the literal, the atom it synthesised and the type expected"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::MalformedSource,
            "a mismatch is the author's"
        );
    }

    #[test]
    fn a_mismatched_application_is_refused_at_the_computation_bridge()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let returns_integer = arena.comp_type_returner(integer);
        let returns_string = arena.comp_type_returner(string);
        let arrow = arena.comp_type_arrow(integer, returns_integer);
        let thunk_arrow = arena.value_type_thunk(arrow);
        let function = arena.value_constant(ConstantIndex::from(0_usize));
        let force = arena.computation_force(function);
        let argument = arena.value_literal(integer_literal());
        let application = arena.computation_application(force, argument);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[thunk_arrow]);
        let expected = form_comp_type(&mut context, returns_string).unwrap();
        let refusal = check_comp(&mut context, application, expected).unwrap_err();
        assert_eq!(
            refusal,
            CheckRefusal::TypeMismatch(Mismatch::Computation {
                at: application,
                synthesised: returns_integer,
                expected: returns_string,
            }),
            "the computation bridge names the application, its codomain and the type expected"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::MalformedSource,
            "a mismatch is the author's"
        );
    }

    #[test]
    fn an_introduction_against_the_wrong_former_is_a_shape_mismatch()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns_integer);
        let integer_value = arena.value_literal(integer_literal());
        let returned = arena.computation_return(integer_value);
        let thunk = arena.value_thunk(returned);
        let lambda = arena.computation_lambda(returned);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let formed_integer = form_value_type(&mut context, integer).unwrap();
        let formed_returner = form_comp_type(&mut context, returns_integer).unwrap();
        let formed_arrow = form_comp_type(&mut context, arrow).unwrap();
        let refusals = [
            (
                check_value(&mut context, thunk, formed_integer),
                TermNode::Value(thunk),
                ExpectedShape::Thunk,
                TypeNode::Value(integer),
            ),
            (
                check_comp(&mut context, lambda, formed_returner),
                TermNode::Computation(lambda),
                ExpectedShape::Arrow,
                TypeNode::Computation(returns_integer),
            ),
            (
                check_comp(&mut context, returned, formed_arrow),
                TermNode::Computation(returned),
                ExpectedShape::Returner,
                TypeNode::Computation(arrow),
            ),
        ];
        for (outcome, at, wanted, found) in refusals {
            let refusal = outcome.unwrap_err();
            assert_eq!(
                refusal,
                CheckRefusal::ShapeMismatch { at, wanted, found },
                "an introduction names the former it needed and the type it met"
            );
            assert_eq!(
                refusal.classify(),
                FailureClass::MalformedSource,
                "a shape mismatch is the author's"
            );
        }
    }

    #[test]
    fn an_elimination_of_the_wrong_former_is_a_shape_mismatch()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let thunk_returner = arena.value_type_thunk(returns_integer);
        let integer_value = arena.value_literal(integer_literal());
        let forced_literal = arena.computation_force(integer_value);
        let suspended = arena.value_constant(ConstantIndex::from(0_usize));
        let head = arena.computation_force(suspended);
        let application = arena.computation_application(head, integer_value);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[thunk_returner]);
        assert_eq!(
            synthesise_comp(&mut context, forced_literal),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(integer_value),
                wanted: ExpectedShape::Thunk,
                found: TypeNode::Value(context.atom(Atom::Integer).id()),
            }),
            "a forced value that synthesises no thunk type is refused at the value"
        );
        assert_eq!(
            synthesise_comp(&mut context, application),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(head),
                wanted: ExpectedShape::Arrow,
                found: TypeNode::Computation(returns_integer),
            }),
            "a head that synthesises no arrow is refused at the head"
        );
    }

    #[test]
    fn a_two_bridge_check_crosses_the_boundary_twice()
    {
        // def g : U (Integer -> F Integer) ;
        // def f : U (Integer -> F Integer) = thunk { \x. (force g) x } ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns_integer);
        let thunk_arrow = arena.value_type_thunk(arrow);
        let function = arena.value_constant(ConstantIndex::from(0_usize));
        let head = arena.computation_force(function);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let application = arena.computation_application(head, bound);
        let lambda = arena.computation_lambda(application);
        let body = arena.value_thunk(lambda);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[thunk_arrow]);
        let expected = form_value_type(&mut context, thunk_arrow).unwrap();
        assert_eq!(
            check_value(&mut context, body, expected).map(|evidence| evidence.conversions()),
            Ok(ConversionCount::from(2_usize)),
            "the bound argument crosses the value bridge and the application the computation \
             bridge, and nothing else converts"
        );
    }

    #[test]
    fn an_exhausted_allowance_is_refused_with_the_budget()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns_integer);
        let thunk_arrow = arena.value_type_thunk(arrow);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(bound);
        let lambda = arena.computation_lambda(returned);
        let identity = arena.value_thunk(lambda);
        let expected = {
            let mut forming = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            form_value_type(&mut forming, thunk_arrow).unwrap()
        };
        let budget = CheckBudget::from(3_usize);
        let mut context = CheckingContext::new(&mut arena, budget);
        assert_eq!(
            form_value_type(&mut context, thunk_arrow),
            Err(CheckRefusal::BudgetExceeded { budget }),
            "formation runs in the same machine, under the same allowance"
        );
        let refusal = check_value(&mut context, identity, expected).unwrap_err();
        assert_eq!(
            refusal,
            CheckRefusal::BudgetExceeded { budget },
            "a run longer than the allowance is refused, naming the allowance"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::EngineFault,
            "an exhausted allowance is the engine's"
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize),
            "the binder the cut-short run opened is closed"
        );
    }

    #[test]
    fn a_refusal_under_binders_leaves_the_context_as_found()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let inner = arena.comp_type_arrow(integer, returns_integer);
        let outer = arena.comp_type_arrow(integer, inner);
        let escaping = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(5_u32));
        let returns_escaping = arena.computation_return(escaping);
        let inner_lambda = arena.computation_lambda(returns_escaping);
        let outer_lambda = arena.computation_lambda(inner_lambda);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let expected = form_comp_type(&mut context, outer).unwrap();
        let refusal = check_comp(&mut context, outer_lambda, expected).unwrap_err();
        assert_eq!(
            refusal,
            CheckRefusal::UnboundIndex {
                at: escaping,
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(5_u32),
                depth: BinderDepth::from(2_usize),
            },
            "the variable is refused under the two binders the lambdas opened"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::EngineFault,
            "an unbound index is the producer's fault"
        );
        assert_eq!(
            synthesise_value(&mut context, escaping),
            Err(CheckRefusal::UnboundIndex {
                at: escaping,
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(5_u32),
                depth: BinderDepth::from(0_usize),
            }),
            "the next judgement in the context starts under no binder"
        );
    }

    #[test]
    fn a_dangling_term_is_refused_as_a_fault()
    {
        let mut arena = CoreArena::new();
        let dangling = dangling_value();
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let refusal = synthesise_value(&mut context, dangling).unwrap_err();
        assert_eq!(
            refusal,
            CheckRefusal::DanglingNode {
                node: CoreNode::Term(TermNode::Value(dangling)),
            },
            "an id the arena does not hold is refused rather than read"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::EngineFault,
            "a dangling id is the caller's fault, not the author's"
        );
    }

    #[test]
    fn a_result_of_the_wrong_kind_is_a_machine_fault()
    {
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            checked(Produced::ValueType(unit_type), ConversionCount::default()),
            Err(CheckRefusal::MachineInvariant),
            "a check run that ends on a type is reported, not trusted"
        );
        let mut machine = Machine {
            context: &mut context,
            frames: Vec::new(),
            native_types: Vec::new(),
            conversions: ConversionCount::default(),
            remaining: 1_usize,
            marking: Marking::Strict,
            anchors: Vec::new(),
            marks: Vec::new(),
        };
        let refusal = machine
            .resume(Frame::LambdaBody, Produced::ValueType(unit_type))
            .unwrap_err();
        assert_eq!(
            refusal,
            CheckRefusal::MachineInvariant,
            "a frame handed a result of another kind reports the miscount"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::EngineFault,
            "a machine invariant is the engine's"
        );
    }

    #[test]
    fn machine_bookkeeping_preserves_zero_and_one_boundaries()
    {
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let mut foreign = CoreArena::new();
        let foreign_unit = foreign.value_unit();
        let absent_comp = foreign.computation_return(foreign_unit);
        let absent_value = dangling_value();
        let budget = CheckBudget::from(1_usize);
        let mut context = CheckingContext::new(&mut arena, budget);
        let mut machine = Machine {
            context: &mut context,
            frames: Vec::new(),
            native_types: Vec::new(),
            conversions: ConversionCount::default(),
            remaining: 1,
            marking: Marking::Strict,
            anchors: Vec::new(),
            marks: Vec::new(),
        };
        assert_eq!(machine.charge(), Ok(()));
        assert_eq!(machine.remaining, 0);
        assert_eq!(
            machine.charge(),
            Err(CheckRefusal::BudgetExceeded { budget })
        );
        assert_eq!(machine.remaining, 0);
        assert_eq!(machine.close(), Err(CheckRefusal::MachineInvariant));
        machine
            .context
            .binders()
            .open(Zone::Intuitionistic, unit_type);
        assert_eq!(machine.close(), Ok(()));
        assert_eq!(
            machine.context.depth(Zone::Intuitionistic),
            BinderDepth::default()
        );
        machine
            .context
            .binders()
            .open(Zone::Intuitionistic, unit_type);
        machine.unwind(BinderDepth::default());
        assert_eq!(
            machine.context.depth(Zone::Intuitionistic),
            BinderDepth::default()
        );
        assert_eq!(
            machine.value(absent_value),
            Err(CheckRefusal::DanglingNode {
                node: CoreNode::Term(TermNode::Value(absent_value))
            })
        );
        assert_eq!(
            machine.computation(absent_comp),
            Err(CheckRefusal::DanglingNode {
                node: CoreNode::Term(TermNode::Computation(absent_comp))
            })
        );
        assert_eq!(
            machine.raises(unit_type),
            Err(CheckRefusal::MachineInvariant)
        );
    }

    #[test]
    fn lift_formation_distinguishes_below_equal_and_above()
    {
        let mut arena = CoreArena::new();
        let natural = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let below = arena.value_type_lift(natural, Level::zero());
        let equal = arena.value_type_lift(natural, Level::constant(LevelConstant::from(1_u64)));
        let above = arena.value_type_lift(natural, Level::constant(LevelConstant::from(2_u64)));
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        for at in [below, equal] {
            assert_eq!(
                form_value_type(&mut context, at),
                Err(CheckRefusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Value(at)),
                    former: UnadmittedFormer::TypeLift
                })
            );
        }
        assert_eq!(
            form_value_type(&mut context, above).map(crate::formation::FormedValueType::id),
            Ok(above)
        );
    }

    /// The universe a judged type stands at, read off the arena.
    ///
    /// # Specification
    /// - requires: `value_type` names a universe in the context arena.
    /// - ensures: its stored sort and level, without changing either.
    /// - panics: the id names no universe.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — quoted atoms, returners and universes expose exact
    ///   sorts and levels, separating wrong universe-family selection and
    ///   successor loss within this finite quote table.
    /// - witness: `judgement::tests::a_universe_classifies_one_level_up_in_the_positive_sort`
    #[spec(
        requires: matches!(context.arena().value_type(value_type), Some(ValueType::Universe { .. })),
        ensures: |ret| matches!(context.arena().value_type(value_type), Some(ValueType::Universe { sort, level }) if ret.0 == *sort && ret.1 == *level),
    )]
    fn universe_of(
        context: &CheckingContext<'_>,
        value_type: ValueTypeId,
    ) -> (Sort, Level)
    {
        match context.arena().value_type(value_type) {
            | Some(&ValueType::Universe { sort, ref level }) => (sort, level.clone()),
            | other => panic!("a universe was synthesised, not {other:?}"),
        }
    }

    #[test]
    fn a_universe_classifies_one_level_up_in_the_positive_sort()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let negative =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
        let quoted_small = arena.value_quote(small);
        let quoted_negative = arena.value_quote(negative);
        let quoted_integer = arena.value_quote(integer);
        let quoted_returner = arena.value_quote_computation(returns_integer);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let one = Level::constant(LevelConstant::from(1_u64));
        let positive_one = (Sort::Ground(GroundSort::Value), one);
        let rows = [
            (quoted_small, positive_one.clone()),
            (quoted_negative, positive_one),
            (
                quoted_integer,
                (Sort::Ground(GroundSort::Value), Level::zero()),
            ),
            (
                quoted_returner,
                (Sort::Ground(GroundSort::Computation), Level::zero()),
            ),
        ];
        for (quote, universe) in rows {
            let synthesised = synthesise_value(&mut context, quote).unwrap();
            assert_eq!(
                universe_of(&context, synthesised.produced().id()),
                universe,
                "a quote has the universe of its type's family at the type's level"
            );
        }
    }

    #[test]
    fn a_value_type_in_a_computation_universe_is_a_sort_mismatch()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let negative =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
        let quoted = arena.value_quote(integer);
        let code = arena.value_constant(ConstantIndex::from(0_usize));
        let decoded = arena.comp_type_element(code, Level::zero());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[small]);
        let expected = form_value_type(&mut context, negative).unwrap();
        let refusal = check_value(&mut context, quoted, expected).unwrap_err();
        assert!(
            matches!(
                refusal,
                CheckRefusal::SortMismatch { at, expected, .. } if at == quoted && expected == negative
            ),
            "a value type's code is refused at the computation universe, not lifted into it: \
             {refusal:?}"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::MalformedSource,
            "a sort mismatch is the author's"
        );
        assert!(
            matches!(
                form_comp_type(&mut context, decoded),
                Err(CheckRefusal::SortMismatch { at, synthesised, .. }) if at == code && synthesised == small
            ),
            "a computation decode of a value code is refused when formation crosses the decode \
             bridge"
        );
    }

    #[test]
    fn a_bind_whose_type_mentions_its_binder_is_refused()
    {
        // def mk : U (F Type) ; def pick : U ((A : Type) -> F El A) ;
        // x <- force mk ; (force pick) x
        let mut arena = CoreArena::new();
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let returns_small = arena.comp_type_returner(small);
        let make = arena.value_type_thunk(returns_small);
        let bound_code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = arena.value_type_element(bound_code, Level::zero());
        let returns_decoded = arena.comp_type_returner(decoded);
        let pi = arena.comp_type_pi(small, returns_decoded);
        let pick = arena.value_type_thunk(pi);
        let mk = arena.value_constant(ConstantIndex::from(0_usize));
        let picker = arena.value_constant(ConstantIndex::from(1_usize));
        let bound = arena.computation_force(mk);
        let head = arena.computation_force(picker);
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let body = arena.computation_application(head, variable);
        let bind = arena.computation_bind(bound, body);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[make, pick]);
        let refusal = synthesise_comp(&mut context, bind).unwrap_err();
        assert!(
            matches!(refusal, CheckRefusal::DependentBind { at, .. } if at == bind),
            "the body has `F El x`, which has no reading outside the bind: {refusal:?}"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::MalformedSource,
            "a dependent bind is the author's"
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize),
            "the refused bind closed the binder it opened"
        );
    }

    #[test]
    fn a_dependent_application_instantiates_its_codomain_at_the_argument()
    {
        // def id : U ((A : Type) -> F El A) ;
        // def lifted : U ((A : Type[+, 1]) -> F El A) ;
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let one = Level::constant(LevelConstant::from(1_u64));
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
        let bound_code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = arena.value_type_element(bound_code, Level::zero());
        let returns_decoded = arena.comp_type_returner(decoded);
        let pi = arena.comp_type_pi(small, returns_decoded);
        let identity = arena.value_type_thunk(pi);
        let decoded_large = arena.value_type_element(bound_code, one.clone());
        let returns_large = arena.comp_type_returner(decoded_large);
        let large_pi = arena.comp_type_pi(large, returns_large);
        let lifting = arena.value_type_thunk(large_pi);
        let lifted_integer = arena.value_type_lift(integer, one);
        let returns_lifted = arena.comp_type_returner(lifted_integer);
        let function = arena.value_constant(ConstantIndex::from(0_usize));
        let lifter = arena.value_constant(ConstantIndex::from(1_usize));
        let code = arena.value_quote(integer);
        let head = arena.computation_force(function);
        let applied = arena.computation_application(head, code);
        let lifted_head = arena.computation_force(lifter);
        let lifted_code = arena.value_quote(integer);
        let lifted_applied = arena.computation_application(lifted_head, lifted_code);
        let returned = arena.computation_return(bound_code);
        let lambda = arena.computation_lambda(returned);
        let returns_small = arena.comp_type_returner(small);
        let small_identity = arena.comp_type_pi(small, returns_small);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[identity, lifting]);
        let expected = form_comp_type(&mut context, returns_integer).unwrap();
        assert!(
            check_comp(&mut context, applied, expected).is_ok(),
            "applying at the code of Integer has F Integer: the decode of a quote is its type"
        );
        assert!(
            check_comp(&mut context, lifted_applied, expected).is_err(),
            "a small code at a large domain is read at its lift, not as itself"
        );
        let lifted = form_comp_type(&mut context, returns_lifted).unwrap();
        assert!(
            check_comp(&mut context, lifted_applied, lifted).is_ok(),
            "the codomain is instantiated at the lifted code"
        );
        let identity_type = form_comp_type(&mut context, small_identity).unwrap();
        assert!(
            check_comp(&mut context, lambda, identity_type).is_ok(),
            "a lambda checks against a dependent arrow, its body against the codomain under the \
             binder"
        );
    }

    #[test]
    fn a_hole_synthesises_the_unknown_type_and_checks_against_any()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returns_integer = arena.comp_type_returner(integer);
        let value_hole = arena.value_hole(HoleId::from(0_u32));
        let comp_hole = arena.computation_hole(HoleId::from(1_u32));
        let unit = arena.value_unit();
        let marked = arena.value_mark(MarkIndex::from(0_u32), unit);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let integer = form_value_type(&mut context, integer).unwrap();
        let returns_integer = form_comp_type(&mut context, returns_integer).unwrap();

        let found = synthesise_value(&mut context, value_hole).unwrap();
        assert_eq!(
            context.arena().value_type(found.produced().id()),
            Some(&ValueType::Unknown),
            "a value hole synthesises the unknown type"
        );
        assert_eq!(
            check_value(&mut context, value_hole, integer).map(|evidence| evidence.conversions()),
            Ok(ConversionCount::default()),
            "a value hole checks against Integer without crossing a bridge"
        );
        let found = synthesise_comp(&mut context, comp_hole).unwrap();
        assert_eq!(
            context.arena().comp_type(found.produced().id()),
            Some(&CompType::Unknown),
            "a computation hole synthesises the unknown computation type"
        );
        assert_eq!(
            check_comp(&mut context, comp_hole, returns_integer)
                .map(|evidence| evidence.conversions()),
            Ok(ConversionCount::default()),
            "a computation hole checks against F Integer"
        );
        assert!(
            check_value(&mut context, unit, integer).is_err(),
            "the unit is no integer"
        );
        assert!(
            check_value(&mut context, marked, integer).is_ok(),
            "a marked unit is not judged again"
        );
        let found = synthesise_value(&mut context, marked).unwrap();
        assert_eq!(
            context.arena().value_type(found.produced().id()),
            Some(&ValueType::Unknown),
            "a mark synthesises the unknown type"
        );
    }

    #[test]
    fn an_introduction_against_the_unknown_type_checks_its_parts()
    {
        let mut arena = CoreArena::new();
        let unknown_value = arena.value_type_unknown();
        let unknown_comp = arena.comp_type_unknown();
        let zero = arena.value_literal(integer_literal());
        let unit = arena.value_unit();
        let returned = arena.computation_return(zero);
        let thunk = arena.value_thunk(returned);
        let pair = arena.value_pair(zero, thunk);
        let injected = arena.value_injection(Side::Left, pair);
        let static_lambda = arena.value_static_lambda(zero);
        let innermost = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returns_innermost = arena.computation_return(innermost);
        let lambda = arena.computation_lambda(returns_innermost);
        let forced = arena.computation_force(unit);
        let ill_thunk = arena.value_thunk(forced);
        let ill_pair = arena.value_pair(zero, ill_thunk);
        let nil = arena.value_list_nil();
        let cons = arena.value_list_cons(zero, nil);
        let stack = arena.value_reify(
            [
                gandr_core_term::control::StackFrame::Apply(zero),
                gandr_core_term::control::StackFrame::Project(Side::Left),
            ]
            .into(),
        );
        let lazy = arena.computation_with(returned, returned);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let unknown_value = form_value_type(&mut context, unknown_value).unwrap();
        let unknown_comp = form_comp_type(&mut context, unknown_comp).unwrap();

        for (term, message) in [
            (
                thunk,
                "a thunk against the unknown type checks its body against the unknown",
            ),
            (
                pair,
                "a pair against the unknown type checks both components",
            ),
            (
                injected,
                "an injection against the unknown type checks its body",
            ),
            (
                static_lambda,
                "a static lambda against the unknown type checks its body",
            ),
            (nil, "nil against the unknown type reads an unknown element"),
            (
                cons,
                "a cell against the unknown type checks its head and tail",
            ),
            (
                stack,
                "a stack against the unknown type runs its frames over unknowns",
            ),
        ] {
            assert!(
                check_value(&mut context, term, unknown_value).is_ok(),
                "{message}"
            );
        }
        for (term, message) in [
            (
                lambda,
                "a lambda binds the unknown domain and checks its body",
            ),
            (
                returned,
                "a return against the unknown type checks its value",
            ),
            (
                lazy,
                "a lazy pair against the unknown type checks both components",
            ),
        ] {
            assert!(
                check_comp(&mut context, term, unknown_comp).is_ok(),
                "{message}"
            );
        }
        assert!(
            matches!(
                check_value(&mut context, ill_pair, unknown_value),
                Err(CheckRefusal::ShapeMismatch { .. })
            ),
            "the parts are still judged: a force of the unit inside is refused"
        );
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        #[test]
        fn the_faces_agree_on_free_terms(
            recipe in term_recipe(),
            constants in vec(type_recipe(), 4),
            expected in type_recipe(),
        )
        {
            let mut arena = CoreArena::new();
            let terms = recipe.build(&mut arena);
            let constant_types: Vec<_> = constants.iter().map(|constant| constant.build(&mut arena)).collect();
            let (expected_value, expected_comp) = expected.build_both(&mut arena);
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            seed(&mut context, &constant_types);
            let expected_value = form_value_type(&mut context, expected_value).unwrap();
            let expected_comp = form_comp_type(&mut context, expected_comp).unwrap();
            for &term in &terms.values {
                let node = context.arena().value(term).cloned().unwrap();
                let synthesised = synthesise_value(&mut context, term);
                if let Ok(found) = synthesised {
                    prop_assert!(
                        check_value(&mut context, term, found.produced()).is_ok(),
                        "a synthesising value checks against its synthesised type"
                    );
                }
                let checked = check_value(&mut context, term, expected_value);
                match node {
                    | Value::Thunk(_) => prop_assert_eq!(
                        synthesised,
                        Err(CheckRefusal::NotSynthesisable { form: CheckingForm::Thunk(term) }),
                        "a thunk does not synthesise"
                    ),
                    | Value::Primitive { .. } | Value::Variable { .. } | Value::Constant(_) | Value::Unit | Value::Literal(_) => {
                        let bridged = synthesised.and_then(|found| {
                            let mut tally = found.conversions();
                            value_bridge(&mut context, term, found.produced().id(), expected_value.id(), &mut tally)
                                .map(|()| tally)
                        });
                        prop_assert_eq!(
                            checked.map(|evidence| evidence.conversions()),
                            bridged,
                            "a synthesising value checks exactly as it synthesises, then crosses the value bridge"
                        );
                    },
                    | Value::PathRefl(_)
                    | Value::Constructor { .. } | Value::Record(_)
                    | Value::Reify(_)
                    | Value::PathProduct(..)
                    | Value::PathEquiv {..}
                    | Value::Pair(..)
                    | Value::ListNil | Value::ListCons(..)
                    | Value::Injection(..)
                    | Value::Lift { .. }
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticLambda(_)
                    | Value::StaticApplication(..)
                    | Value::Hole(_)
                    | Value::Mark { .. } => {
                        prop_assert!(false, "the recipe mints no pair, injection, lift, quote, static operator, hole or mark");
                    },
                }
                prop_assert_eq!(
                    context.binders().depth(Zone::Intuitionistic),
                    BinderDepth::from(0_usize),
                    "every run leaves the binders where it found them"
                );
            }
            for &term in &terms.comps {
                let node = context.arena().computation(term).cloned().unwrap();
                let synthesised = synthesise_comp(&mut context, term);
                if let Ok(found) = synthesised {
                    prop_assert!(
                        check_comp(&mut context, term, found.produced()).is_ok(),
                        "a synthesising computation checks against its synthesised type"
                    );
                }
                let checked = check_comp(&mut context, term, expected_comp);
                match node {
                    | Computation::Lambda(_) => prop_assert_eq!(
                        synthesised,
                        Err(CheckRefusal::NotSynthesisable { form: CheckingForm::Lambda(term) }),
                        "a lambda does not synthesise"
                    ),
                    | Computation::Return(_) => prop_assert_eq!(
                        synthesised,
                        Err(CheckRefusal::NotSynthesisable { form: CheckingForm::Return(term) }),
                        "a return does not synthesise"
                    ),
                    | Computation::Fixpoint { .. } => prop_assert!(false, "the free recipe mints no fixpoint"),
                    | Computation::Primitive { .. } | Computation::Force(_) | Computation::Application(..) => {
                        let bridged = synthesised.and_then(|found| {
                            let mut tally = found.conversions();
                            comp_bridge(&mut context, term, found.produced().id(), expected_comp.id(), &mut tally)
                                .map(|()| tally)
                        });
                        prop_assert_eq!(
                            checked.map(|evidence| evidence.conversions()),
                            bridged,
                            "a synthesising computation checks exactly as it synthesises, then crosses the computation bridge"
                        );
                    },
                    | Computation::Transport(..) | Computation::Bind(..) | Computation::DataCase { .. } | Computation::RecordProjection(..) => {
                        prop_assert!(false, "the free recipe mints no bind or native eliminator");
                    },
                    | Computation::ListFold { .. } | Computation::Case { .. }
                    | Computation::Perform { .. } | Computation::Handle { .. } | Computation::Resume(..)
                    | Computation::Reset(_) | Computation::Shift(_) | Computation::With(..) | Computation::Project(..)
                    | Computation::Hole(_) | Computation::Mark { .. } => {
                        prop_assert!(false, "the recipe mints no former outside the fragment, no hole and no mark");
                    },
                }
                prop_assert_eq!(
                    context.binders().depth(Zone::Intuitionistic),
                    BinderDepth::from(0_usize),
                    "every run leaves the binders where it found them"
                );
            }
        }

        #[test]
        fn well_typed_terms_synthesise_and_check_their_type(recipe in typed_recipe())
        {
            let mut arena = CoreArena::new();
            let terms = recipe.build(&mut arena);
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            seed(&mut context, &terms.constants);
            for &(term, built, mode) in &terms.values {
                let expected = form_value_type(&mut context, built).unwrap();
                prop_assert!(
                    check_value(&mut context, term, expected).is_ok(),
                    "a well-typed value checks against its type"
                );
                let synthesised = synthesise_value(&mut context, term);
                match mode {
                    | Mode::Synthesising => {
                        let found = synthesised.unwrap();
                        let mut scratch = ConversionCount::default();
                        prop_assert!(
                            value_bridge(&mut context, term, found.produced().id(), built, &mut scratch).is_ok(),
                            "a well-typed synthesising value synthesises its type"
                        );
                    },
                    | Mode::Checking => prop_assert!(
                        matches!(synthesised, Err(CheckRefusal::NotSynthesisable { .. })),
                        "a well-typed checking value is refused in synthesis"
                    ),
                }
            }
            for &(term, built, mode) in &terms.comps {
                let expected = form_comp_type(&mut context, built).unwrap();
                prop_assert!(
                    check_comp(&mut context, term, expected).is_ok(),
                    "a well-typed computation checks against its type"
                );
                let synthesised = synthesise_comp(&mut context, term);
                match mode {
                    | Mode::Synthesising => {
                        let found = synthesised.unwrap();
                        let mut scratch = ConversionCount::default();
                        prop_assert!(
                            comp_bridge(&mut context, term, found.produced().id(), built, &mut scratch).is_ok(),
                            "a well-typed synthesising computation synthesises its type"
                        );
                    },
                    | Mode::Checking => prop_assert!(
                        matches!(synthesised, Err(CheckRefusal::NotSynthesisable { .. })),
                        "a well-typed checking computation is refused in synthesis"
                    ),
                }
            }
        }
    }
}
