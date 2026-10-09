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
use gandr_core_term::instantiate_comp_type;
use gandr_core_term::shift_comp_type;
use gandr_core_term::shift_value_type;
use gandr_core_term::strengthen_comp_type;
use gandr_kernel_term::BaseType;
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
pub fn form(
    context: &mut CheckingContext<'_>,
    node: TypeNode,
) -> Result<(), CheckRefusal>
{
    let (produced, conversions) = Machine::run(context, Goal::Form(node))?;
    checked(produced, conversions).map(|_| ())
}

/// A judgement the machine is to run.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Goal
{
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

/// A rule waiting on the judgement of one of its subterms.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Frame
{
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
/// and the allowance left.
struct Machine<'context, 'arena>
{
    /// The context the run reads and goes under binders in.
    context: &'context mut CheckingContext<'arena>,
    /// The rules waiting on subterms, innermost last.
    frames: Vec<Frame>,
    /// The crossings of the conversion boundary so far.
    conversions: ConversionCount,
    /// The steps left before the run refuses.
    remaining: usize,
}

impl<'context, 'arena> Machine<'context, 'arena>
{
    /// Run `goal` to its result in `context`.
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
    fn run(
        context: &'context mut CheckingContext<'arena>,
        goal: Goal,
    ) -> Result<(Produced, ConversionCount), CheckRefusal>
    {
        let entry = context.binders().depth(Zone::Intuitionistic);
        let remaining = usize::from(context.budget());
        let mut machine = Machine {
            context,
            frames: Vec::new(),
            conversions: ConversionCount::default(),
            remaining,
        };
        match machine.drive(goal) {
            | Ok(produced) => Ok((produced, machine.conversions)),
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
    fn drive(
        &mut self,
        goal: Goal,
    ) -> Result<Produced, CheckRefusal>
    {
        let mut step = Step::Descend(goal);
        loop {
            self.charge()?;
            step = match step {
                | Step::Descend(goal) => self.descend(goal)?,
                | Step::Ascend(produced) => match self.frames.pop() {
                    | Some(frame) => self.resume(frame, produced)?,
                    | None => return Ok(produced),
                },
            };
        }
    }

    /// Spend one step of the allowance.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one fewer step remains.
    /// - fails: [`CheckRefusal::BudgetExceeded`] when none remains.
    /// - panics: none.
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
    fn descend(
        &mut self,
        goal: Goal,
    ) -> Result<Step, CheckRefusal>
    {
        match goal {
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
    ///   the unit value and an integer or string literal their atom; a quote
    ///   awaits its type's formation; a pair awaits its components' types and
    ///   has their eager product; a static application awaits its head's type
    ///   and meets each argument in turn. A leaf ascends with the frames as
    ///   found; every other rule descends above a new frame.
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
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| match ret {
            | Ok(Step::Ascend(_)) => self.frames.len() == depth,
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
            | Value::Injection(..) => Err(unadmitted_value(term, UnadmittedFormer::Injection)),
            | Value::Lift { .. } => Err(unadmitted_value(term, UnadmittedFormer::ValueLift)),
            | Value::StaticLambda(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::StaticLambda(term),
            }),
            | Value::StaticApplication(..) => self.static_application(term),
        }
    }

    /// Start a quote of `quoted`: the quoted type's formation is the next
    /// goal, with the quote's frame awaiting it.
    ///
    /// # Specification
    /// trivial.
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
    /// - ensures: a thunk's body checks against the body of a thunk type at
    ///   `expected`'s weak head; a pair's components check against the factors
    ///   of an eager product there; a static lambda opens a binder of the
    ///   domain of a static Pi there and its body checks against the codomain
    ///   shifted past the binder; a synthesising value synthesises, then
    ///   crosses the value bridge to `expected`. Every rule descends.
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
    ///
    /// # Judgement
    /// - expected: `expected`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| ret.is_err()
            || (matches!(ret, Ok(Step::Descend(_))) && self.frames.len() >= depth),
    )]
    fn check_value(
        &mut self,
        term: ValueId,
        expected: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        match *self.value(term)? {
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
            | Value::Injection(..) => Err(unadmitted_value(term, UnadmittedFormer::Injection)),
            | Value::Lift { .. } => Err(unadmitted_value(term, UnadmittedFormer::ValueLift)),
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
            | Value::Variable { .. }
            | Value::Unit
            | Value::Literal(_)
            | Value::Pair(..)
            | Value::Injection(..)
            | Value::Thunk(_)
            | Value::Lift { .. }
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::StaticApplication(..) => false,
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
    ///   awaits its head's; a bind awaits its bound computation's.
    /// - fails: [`CheckRefusal::NotSynthesisable`] for a lambda or a return;
    ///   [`CheckRefusal::OutOfFragment`] for a case.
    /// - panics: none.
    fn synthesise_comp(
        &mut self,
        term: ComputationId,
    ) -> Result<Step, CheckRefusal>
    {
        match *self.computation(term)? {
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
            | Computation::Bind(bound, body) => {
                Ok(self.bind(term, bound, body, Direction::Synthesise))
            },
            | Computation::Case { .. } => Err(unadmitted_comp(term, UnadmittedFormer::Case)),
        }
    }

    /// The checking rules over computations.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: a lambda opens a binder of the domain of the arrow or the
    ///   dependent arrow at `expected`'s weak head, and its body checks against
    ///   the codomain — an arrow's shifted past the binder, a dependent arrow's
    ///   as it stands; a return's value checks against the returner's result; a
    ///   bind awaits its bound computation's synthesised type, then checks its
    ///   body against `expected` shifted past its binder; a synthesising
    ///   computation synthesises, then crosses the computation bridge to
    ///   `expected`.
    /// - fails: [`CheckRefusal::ShapeMismatch`] for a lambda against no arrow
    ///   or a return against no returner; [`CheckRefusal::OutOfFragment`] for a
    ///   case.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    fn check_comp(
        &mut self,
        term: ComputationId,
        expected: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        match *self.computation(term)? {
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
            | Computation::Force(_) | Computation::Application(..) => {
                self.frames.push(Frame::CompBridge { at: term, expected });
                Ok(Step::Descend(Goal::Computation {
                    term,
                    direction: Direction::Synthesise,
                }))
            },
            | Computation::Bind(bound, body) => {
                Ok(self.bind(term, bound, body, Direction::Check(expected)))
            },
            | Computation::Case { .. } => Err(unadmitted_comp(term, UnadmittedFormer::Case)),
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

    /// The body a thunk checks against: the expected type's, when it is a
    /// thunk type at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the body of `expected` when it is `U C` at its weak head.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a thunk type,
    ///   for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    fn thunk_expected(
        &mut self,
        at: ValueId,
        expected: ValueTypeId,
    ) -> Result<CompTypeId, CheckRefusal>
    {
        let head = self.context.whnf_value_type(expected)?;
        match value_type_view(self.context.arena(), head)? {
            | ValueTypeView::Thunk(body) => Ok(body),
            | ValueTypeView::Integer
            | ValueTypeView::String
            | ValueTypeView::Unit
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Lift { .. }
            | ValueTypeView::Element { .. }
            | ValueTypeView::Product(..)
            | ValueTypeView::StaticPi { .. } => Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(at),
                wanted: ExpectedShape::Thunk,
                found: TypeNode::Value(expected),
            }),
        }
    }

    /// The factors a pair's components check against: the expected type's,
    /// when it is an eager product at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: both factors of `expected` when it is `A × B` at its weak
    ///   head, each resolving in the arena.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting an eager
    ///   product, for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a pair against a product and against an
    ///   atom.
    /// - witness: `judgement::tests::a_pair_synthesises_its_eager_product_and_checks_against_one`
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
        if let ValueTypeView::Product(first, second) = value_type_view(self.context.arena(), head)?
        {
            return Ok((first, second));
        }
        Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(at),
            wanted: ExpectedShape::Product,
            found: TypeNode::Value(expected),
        })
    }

    /// The domain and codomain a static lambda's body checks against: the
    /// expected type's, when it is a static Pi at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the domain of `expected`, and its codomain shifted past the
    ///   lambda's binder: a static Pi's codomain stands in the ambient context.
    ///   Both resolve in the arena.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a static Pi,
    ///   for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a static lambda against a static Pi and
    ///   against an atom.
    /// - witness: `judgement::tests::a_static_lambda_checks_only_against_a_static_pi`
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
        if let ValueTypeView::StaticPi { domain, codomain } =
            value_type_view(self.context.arena(), head)?
        {
            let scoped = shift_value_type(self.context.arena_mut(), codomain, Binders::from(1_u32));
            return Ok((domain, scoped));
        }
        Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(at),
            wanted: ExpectedShape::StaticPi,
            found: TypeNode::Value(expected),
        })
    }

    /// The domain and codomain a lambda's body checks against: the expected
    /// type's, when it is an arrow or a dependent arrow at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the domain of `expected`, and its codomain read under the
    ///   lambda's binder — an arrow's shifted past it, a dependent arrow's as
    ///   it stands.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting an arrow, for
    ///   any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    fn arrow_expected(
        &mut self,
        at: ComputationId,
        expected: CompTypeId,
    ) -> Result<(ValueTypeId, CompTypeId), CheckRefusal>
    {
        let head = self.context.whnf_comp_type(expected)?;
        match comp_type_view(self.context.arena(), head)? {
            | CompTypeView::Arrow { domain, codomain } => {
                let scoped =
                    shift_comp_type(self.context.arena_mut(), codomain, Binders::from(1_u32));
                Ok((domain, scoped))
            },
            | CompTypeView::Pi { domain, codomain } => Ok((domain, codomain)),
            | CompTypeView::Returner(_) | CompTypeView::Element { .. } => {
                Err(CheckRefusal::ShapeMismatch {
                    at: TermNode::Computation(at),
                    wanted: ExpectedShape::Arrow,
                    found: TypeNode::Computation(expected),
                })
            },
        }
    }

    /// The result type a return checks its value against: the expected
    /// type's, when it is a returner at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the result of `expected` when it is `F A` at its weak head.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a returner,
    ///   for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    fn returner_expected(
        &mut self,
        at: ComputationId,
        expected: CompTypeId,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let head = self.context.whnf_comp_type(expected)?;
        match comp_type_view(self.context.arena(), head)? {
            | CompTypeView::Returner(result) => Ok(result),
            | CompTypeView::Arrow { .. }
            | CompTypeView::Pi { .. }
            | CompTypeView::Element { .. } => Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Returner,
                found: TypeNode::Computation(expected),
            }),
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
            | Ok(Step::Ascend(_)) => self.frames.len() == depth,
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
            | ValueTypeView::Integer | ValueTypeView::String | ValueTypeView::Unit => {
                Ok(Step::Ascend(Produced::Checked))
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
            | ValueTypeView::Product(first, second) => {
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
    ///   type.
    /// - fails: the view's refusal for a dangling id.
    /// - panics: none.
    fn form_comp_type(
        &mut self,
        at: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        match comp_type_view(self.context.arena(), at)? {
            | CompTypeView::Returner(result) => {
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
        }
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
    fn quoted(
        &mut self,
        quoted: TypeNode,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let level = level_of(self.context.arena(), quoted)?;
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
        if bool::from(level_of(arena, TypeNode::Value(inner))?.lt(target)) {
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
                | ValueTypeView::Universe { .. } | ValueTypeView::StaticPi { .. } => {},
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
                | ValueTypeView::Integer
                | ValueTypeView::String
                | ValueTypeView::Unit
                | ValueTypeView::Thunk(_)
                | ValueTypeView::Universe { .. }
                | ValueTypeView::Lift { .. }
                | ValueTypeView::Product(..)
                | ValueTypeView::StaticPi { .. } => return Err(CheckRefusal::MachineInvariant),
            },
            | TypeNode::Computation(at) => match comp_type_view(arena, at)? {
                | CompTypeView::Element { code, target } => {
                    (code, target.clone(), GroundSort::Computation)
                },
                | CompTypeView::Returner(_)
                | CompTypeView::Arrow { .. }
                | CompTypeView::Pi { .. } => {
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
            | (Frame::Force { value }, Produced::ValueType(synthesised)) => {
                let head = self.context.whnf_value_type(synthesised)?;
                match value_type_view(self.context.arena(), head)? {
                    | ValueTypeView::Thunk(body) => Ok(Step::Ascend(Produced::CompType(body))),
                    | ValueTypeView::Integer
                    | ValueTypeView::String
                    | ValueTypeView::Unit
                    | ValueTypeView::Universe { .. }
                    | ValueTypeView::Lift { .. }
                    | ValueTypeView::Element { .. }
                    | ValueTypeView::Product(..)
                    | ValueTypeView::StaticPi { .. } => Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Value(value),
                        wanted: ExpectedShape::Thunk,
                        found: TypeNode::Value(synthesised),
                    }),
                }
            },
            | (Frame::ApplicationHead { head, argument }, Produced::CompType(synthesised)) => {
                let read = self.context.whnf_comp_type(synthesised)?;
                let (domain, codomain) = match comp_type_view(self.context.arena(), read)? {
                    | CompTypeView::Arrow { domain, codomain } => {
                        (domain, Codomain::Ambient(codomain))
                    },
                    | CompTypeView::Pi { domain, codomain } => {
                        (domain, Codomain::Dependent(codomain))
                    },
                    | CompTypeView::Returner(_) | CompTypeView::Element { .. } => {
                        return Err(CheckRefusal::ShapeMismatch {
                            at: TermNode::Computation(head),
                            wanted: ExpectedShape::Arrow,
                            found: TypeNode::Computation(synthesised),
                        });
                    },
                };
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
                let CompTypeView::Returner(result) = comp_type_view(self.context.arena(), read)?
                else {
                    return Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Computation(bound),
                        wanted: ExpectedShape::Returner,
                        found: TypeNode::Computation(synthesised),
                    });
                };
                let direction = match direction {
                    | Direction::Synthesise => Direction::Synthesise,
                    | Direction::Check(expected) => Direction::Check(shift_comp_type(
                        self.context.arena_mut(),
                        expected,
                        Binders::from(1_u32),
                    )),
                };
                self.context.binders().open(Zone::Intuitionistic, result);
                self.frames.push(Frame::BindBody { at });
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction,
                }))
            },
            | (Frame::BindBody { at }, Produced::CompType(synthesised)) => {
                let Maybe::Present(lowered) =
                    strengthen_comp_type(self.context.arena_mut(), synthesised)
                else {
                    return Err(CheckRefusal::DependentBind { at, synthesised });
                };
                self.close()?;
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
                let product = self.context.arena_mut().value_type_product(first, second);
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
                let ValueTypeView::StaticPi { domain, codomain } =
                    value_type_view(self.context.arena(), head)?
                else {
                    return Err(CheckRefusal::FamilyArity {
                        at,
                        expected: StaticArity::from(u32::from(position)),
                        actual: spine,
                    });
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
            | (
                Frame::Force { .. }
                | Frame::ValueBridge { .. }
                | Frame::FormElement(_)
                | Frame::PairFirstSynthesised { .. }
                | Frame::PairSecondSynthesised { .. }
                | Frame::StaticSpine { .. }
                | Frame::StaticArgument { .. },
                Produced::CompType(_) | Produced::Checked,
            )
            | (
                Frame::ApplicationHead { .. } | Frame::CompBridge { .. } | Frame::BindBound { .. },
                Produced::ValueType(_) | Produced::Checked,
            )
            | (
                Frame::ApplicationArgument { .. }
                | Frame::LambdaBody
                | Frame::FormBinder
                | Frame::Quote(_)
                | Frame::FormNext(_)
                | Frame::FormPi { .. }
                | Frame::FormLift(_)
                | Frame::FormStaticPi(_)
                | Frame::PairSecond { .. }
                | Frame::StaticOperand { .. },
                Produced::ValueType(_) | Produced::CompType(_),
            )
            | (Frame::BindBody { .. }, Produced::ValueType(_)) => {
                Err(CheckRefusal::MachineInvariant)
            },
        }
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

/// The refusal of a computation former the fragment has no rule for.
///
/// # Specification
/// trivial.
const fn unadmitted_comp(
    term: ComputationId,
    former: UnadmittedFormer,
) -> CheckRefusal
{
    CheckRefusal::OutOfFragment {
        at: CoreNode::Term(TermNode::Computation(term)),
        former,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_term::BinderDepth;
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
    use super::Produced;
    use super::check_comp;
    use super::check_value;
    use super::checked;
    use super::synthesise_comp;
    use super::synthesise_value;
    use super::unadmitted_comp;
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
                Err(unadmitted_value(injection, UnadmittedFormer::Injection)),
                unit_type,
                Err(unadmitted_value(injection, UnadmittedFormer::Injection)),
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
        let product = arena.value_type_product(unit_type, integer);
        let checking_only = arena.value_type_product(suspended, integer);
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
        let Some(&ValueType::Product(first, second)) = context.arena().value_type(synthesised)
        else {
            panic!("a pair synthesises an eager product");
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
        let rows: [Row<ComputationId, CompTypeId>; 6] = [
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
            (
                case,
                Err(unadmitted_comp(case, UnadmittedFormer::Case)),
                returns_integer,
                Err(unadmitted_comp(case, UnadmittedFormer::Case)),
            ),
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
            conversions: ConversionCount::default(),
            remaining: 1_usize,
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

    /// The universe a judged type stands at, read off the arena.
    ///
    /// # Specification
    /// trivial.
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
                    | Value::Variable { .. } | Value::Constant(_) | Value::Unit | Value::Literal(_) => {
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
                    | Value::Pair(..)
                    | Value::Injection(..)
                    | Value::Lift { .. }
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticLambda(_)
                    | Value::StaticApplication(..) => {
                        prop_assert!(false, "the recipe mints no pair, injection, lift, quote or static operator");
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
                    | Computation::Force(_) | Computation::Application(..) => {
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
                    | Computation::Bind(..) => {
                        prop_assert!(false, "the free recipe mints no bind");
                    },
                    | Computation::Case { .. } => {
                        prop_assert!(false, "the recipe mints no former outside the fragment");
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
