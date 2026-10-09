//! The judgement: four directed faces over one machine.
//!
//! # The former decides the mode
//!
//! Every term former has one mode. Leaves and eliminations synthesise —
//! their type is read out of the context, the signature table, an atom, or
//! the type of the term they eliminate — and introductions check against a
//! type handed in, because nothing in an introduction alone fixes its type:
//!
//! |Former|Mode|Rule|
//! |---|---|---|
//! |variable|synthesise|the type its binder declared|
//! |constant|synthesise|the type its declaration supplied|
//! |unit, integer and string literal|synthesise|the atom|
//! |thunk|check against `U C`|its body checks against `C`|
//! |force|synthesise|the forced value synthesises `U C`; the force has `C`|
//! |application|synthesise|the head synthesises `A → C`, the argument checks against `A`; the application has `C`|
//! |bind|either|the bound computation synthesises `F A`; opens a binder of `A`; the body is judged in the bind's own mode, and the bind has what the body has|
//! |lambda|check against `A → C`|opens a binder of `A`; the body checks against `C`|
//! |return|check against `F A`|the value checks against `A`|
//!
//! A bind is the one former of either mode: it eliminates the returner its
//! bound computation synthesises, so that half synthesises, and it hands its
//! type through from its body, so the body is judged in whichever mode the
//! bind was asked for. A bound computation that only checks — a bare
//! `return` — is refused as not synthesisable rather than given a guessed type.
//!
//! A synthesising term in checking position synthesises, then its type crosses
//! the conversion boundary to the expected type; that is the only place a
//! type meets a type. A checking form in synthesis position is refused, naming
//! the form: the judgement never guesses a type an introduction did not
//! carry.
//!
//! # One machine, no recursion
//!
//! The four faces all run [`Machine`]: an explicit goal and a stack of frames,
//! one step per transition, charged against the context's allowance. A term
//! as deep as memory holds is judged without a native stack, and the
//! allowance bounds the run whatever sharing the term has.
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

use gandr_core_term::BinderDepth;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::ContextError;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::BaseType;
use quenchant_shape::shape::Maybe;

use crate::context::Atom;
use crate::context::CheckingContext;
use crate::conversion::ConversionCount;
use crate::conversion::comp_bridge;
use crate::conversion::value_bridge;
use crate::formation::FormedCompType;
use crate::formation::FormedValueType;
use crate::refusal::CheckRefusal;
use crate::refusal::CheckingForm;
use crate::refusal::CoreNode;
use crate::refusal::ExpectedShape;
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
}

/// What a finished judgement hands to the frame awaiting it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Produced
{
    /// A synthesised value type.
    ValueType(ValueTypeId),
    /// A synthesised computation type.
    CompType(CompTypeId),
    /// A check that succeeded.
    Checked,
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
    /// arrow; the argument then checks against the domain.
    ApplicationHead
    {
        /// The head.
        head: ComputationId,
        /// The argument still to check.
        argument: ValueId,
    },
    /// An application waits on its argument's check; it then has the
    /// codomain.
    ApplicationArgument
    {
        /// The arrow's codomain.
        codomain: CompTypeId,
    },
    /// A lambda waits on its body's check, then closes the binder it opened.
    LambdaBody,
    /// A bind waits on the type its bound computation synthesises, which must
    /// be a returner; it then opens a binder of the returned type and judges
    /// its body in the bind's own direction.
    BindBound
    {
        /// The bound computation.
        bound: ComputationId,
        /// The body still to judge.
        body: ComputationId,
        /// The bind's own direction, which the body takes.
        direction: Direction<CompTypeId>,
    },
    /// A bind waits on its body's judgement, then closes the binder it opened
    /// and hands the body's result on.
    BindBody,
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

    /// Start the judgement `goal`, by its direction.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the rule of the goal's direction for its term's former runs.
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
    ) -> Result<&'arena Value, CheckRefusal>
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
    ) -> Result<&'arena Computation, CheckRefusal>
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
    /// - ensures: a variable has the type its binder declared, a constant the
    ///   type its declaration supplied, the unit value and an integer or string
    ///   literal their atom.
    /// - fails: [`CheckRefusal::NotSynthesisable`] for a thunk;
    ///   [`CheckRefusal::UnboundIndex`] for a variable past its zone's binders;
    ///   [`CheckRefusal::UnknownConstant`] for a constant with no type;
    ///   [`CheckRefusal::OutOfFragment`] for a numeric literal, a pair, an
    ///   injection or a value lift.
    /// - panics: none.
    fn synthesise_value(
        &mut self,
        term: ValueId,
    ) -> Result<Step, CheckRefusal>
    {
        let produced = |found: FormedValueType| Ok(Step::Ascend(Produced::ValueType(found.id())));
        match *self.value(term)? {
            | Value::Variable { zone, index } => {
                match self.context.binders().occurrence(zone, index) {
                    | Ok(declared) => Ok(Step::Ascend(Produced::ValueType(declared))),
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
            | Value::Thunk(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Thunk(term),
            }),
            | Value::Pair(..) => Err(unadmitted_value(term, UnadmittedFormer::Pair)),
            | Value::Injection(..) => Err(unadmitted_value(term, UnadmittedFormer::Injection)),
            | Value::Lift { .. } => Err(unadmitted_value(term, UnadmittedFormer::ValueLift)),
        }
    }

    /// The checking rules over values.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: a thunk's body checks against the body of a thunk type; a
    ///   synthesising value synthesises, then crosses the value bridge to
    ///   `expected`.
    /// - fails: [`CheckRefusal::ShapeMismatch`] for a thunk against no thunk
    ///   type; [`CheckRefusal::OutOfFragment`] for a pair, an injection or a
    ///   value lift.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
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
            | Value::Variable { .. } | Value::Constant(_) | Value::Unit | Value::Literal(_) => {
                self.frames.push(Frame::ValueBridge { at: term, expected });
                Ok(Step::Descend(Goal::Value {
                    term,
                    direction: Direction::Synthesise,
                }))
            },
            | Value::Pair(..) => Err(unadmitted_value(term, UnadmittedFormer::Pair)),
            | Value::Injection(..) => Err(unadmitted_value(term, UnadmittedFormer::Injection)),
            | Value::Lift { .. } => Err(unadmitted_value(term, UnadmittedFormer::ValueLift)),
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
            | Computation::Bind(bound, body) => Ok(self.bind(bound, body, Direction::Synthesise)),
            | Computation::Case { .. } => Err(unadmitted_comp(term, UnadmittedFormer::Case)),
        }
    }

    /// The checking rules over computations.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: a lambda opens a binder of the arrow's domain and its body
    ///   checks against the codomain; a return's value checks against the
    ///   returner's result; a bind awaits its bound computation's synthesised
    ///   type, then checks its body against `expected`; a synthesising
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
                Ok(self.bind(bound, body, Direction::Check(expected)))
            },
            | Computation::Case { .. } => Err(unadmitted_comp(term, UnadmittedFormer::Case)),
        }
    }

    /// Start a bind of `bound` into `body`, judged in `direction`.
    ///
    /// # Specification
    /// - requires: `bound` and `body` are the two halves of one bind.
    /// - ensures: the bound computation's synthesis is the next goal, with the
    ///   bind's frame awaiting its type and holding the direction the body is
    ///   judged in.
    /// - provides: the one rule both computation faces share.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the rule's surfaces are the two directions and the
    ///   returner test, separated by a bind synthesising its body's type, a
    ///   bind checked against its body's type, and a bind of an arrow-typed
    ///   computation, each asserted as the exact type, check or refusal.
    /// - witness: `judgement::tests::a_bind_synthesises_its_continuations_type`
    /// - witness: `judgement::tests::a_bind_checks_against_the_expected_computation`
    /// - witness: `judgement::tests::a_bind_of_a_non_returner_is_a_shape_mismatch`
    fn bind(
        &mut self,
        bound: ComputationId,
        body: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Step
    {
        self.frames.push(Frame::BindBound {
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
    /// thunk type.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the body of `expected` when it is `U C`.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a thunk type,
    ///   for any other former.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    fn thunk_expected(
        &self,
        at: ValueId,
        expected: ValueTypeId,
    ) -> Result<CompTypeId, CheckRefusal>
    {
        match value_type_view(self.context.arena(), expected)? {
            | ValueTypeView::Thunk(body) => Ok(body),
            | ValueTypeView::Integer | ValueTypeView::String | ValueTypeView::Unit => {
                Err(CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::Thunk,
                    found: TypeNode::Value(expected),
                })
            },
        }
    }

    /// The domain and codomain a lambda checks against: the expected type's,
    /// when it is an arrow.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the domain and codomain of `expected` when it is `A → C`.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting an arrow, for
    ///   a returner.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    fn arrow_expected(
        &self,
        at: ComputationId,
        expected: CompTypeId,
    ) -> Result<(ValueTypeId, CompTypeId), CheckRefusal>
    {
        match comp_type_view(self.context.arena(), expected)? {
            | CompTypeView::Arrow { domain, codomain } => Ok((domain, codomain)),
            | CompTypeView::Returner(_) => Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Arrow,
                found: TypeNode::Computation(expected),
            }),
        }
    }

    /// The result type a return checks its value against: the expected
    /// type's, when it is a returner.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the result of `expected` when it is `F A`.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a returner,
    ///   for an arrow.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    fn returner_expected(
        &self,
        at: ComputationId,
        expected: CompTypeId,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        match comp_type_view(self.context.arena(), expected)? {
            | CompTypeView::Returner(result) => Ok(result),
            | CompTypeView::Arrow { .. } => Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Returner,
                found: TypeNode::Computation(expected),
            }),
        }
    }

    /// Hand `produced` to the rule `frame` holds.
    ///
    /// # Specification
    /// - requires: `frame` was pushed by a rule of this run.
    /// - ensures: a force has the body of its value's thunk type; an
    ///   application checks its argument against its head's domain, then has
    ///   the codomain; a bind opens a binder of its bound computation's
    ///   returned type and judges its body, then closes the binder and has what
    ///   the body had; a lambda closes its binder; a bridge frame crosses its
    ///   bridge and the check succeeds.
    /// - fails: [`CheckRefusal::ShapeMismatch`] for a forced value of no thunk
    ///   type, a head of no arrow type, or a bound computation of no returner
    ///   type; [`CheckRefusal::TypeMismatch`] at a bridge;
    ///   [`CheckRefusal::MachineInvariant`] when `produced` is not the kind the
    ///   frame awaits.
    /// - panics: none.
    fn resume(
        &mut self,
        frame: Frame,
        produced: Produced,
    ) -> Result<Step, CheckRefusal>
    {
        let arena = self.context.arena();
        match (frame, produced) {
            | (Frame::Force { value }, Produced::ValueType(synthesised)) => {
                match value_type_view(arena, synthesised)? {
                    | ValueTypeView::Thunk(body) => Ok(Step::Ascend(Produced::CompType(body))),
                    | ValueTypeView::Integer | ValueTypeView::String | ValueTypeView::Unit => {
                        Err(CheckRefusal::ShapeMismatch {
                            at: TermNode::Value(value),
                            wanted: ExpectedShape::Thunk,
                            found: TypeNode::Value(synthesised),
                        })
                    },
                }
            },
            | (Frame::ApplicationHead { head, argument }, Produced::CompType(synthesised)) => {
                match comp_type_view(arena, synthesised)? {
                    | CompTypeView::Arrow { domain, codomain } => {
                        self.frames.push(Frame::ApplicationArgument { codomain });
                        Ok(Step::Descend(Goal::Value {
                            term: argument,
                            direction: Direction::Check(domain),
                        }))
                    },
                    | CompTypeView::Returner(_) => Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Computation(head),
                        wanted: ExpectedShape::Arrow,
                        found: TypeNode::Computation(synthesised),
                    }),
                }
            },
            | (Frame::ApplicationArgument { codomain }, Produced::Checked) => {
                Ok(Step::Ascend(Produced::CompType(codomain)))
            },
            | (Frame::LambdaBody, Produced::Checked) => {
                match self.context.binders().close(Zone::Intuitionistic) {
                    | Ok(_) => Ok(Step::Ascend(Produced::Checked)),
                    | Err(_) => Err(CheckRefusal::MachineInvariant),
                }
            },
            | (
                Frame::BindBound {
                    bound,
                    body,
                    direction,
                },
                Produced::CompType(synthesised),
            ) => match comp_type_view(arena, synthesised)? {
                | CompTypeView::Returner(result) => {
                    self.context.binders().open(Zone::Intuitionistic, result);
                    self.frames.push(Frame::BindBody);
                    Ok(Step::Descend(Goal::Computation {
                        term: body,
                        direction,
                    }))
                },
                | CompTypeView::Arrow { .. } => Err(CheckRefusal::ShapeMismatch {
                    at: TermNode::Computation(bound),
                    wanted: ExpectedShape::Returner,
                    found: TypeNode::Computation(synthesised),
                }),
            },
            | (Frame::BindBody, Produced::CompType(_) | Produced::Checked) => {
                match self.context.binders().close(Zone::Intuitionistic) {
                    | Ok(_) => Ok(Step::Ascend(produced)),
                    | Err(_) => Err(CheckRefusal::MachineInvariant),
                }
            },
            | (Frame::ValueBridge { at, expected }, Produced::ValueType(synthesised)) => {
                value_bridge(arena, at, synthesised, expected, &mut self.conversions)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            | (Frame::CompBridge { at, expected }, Produced::CompType(synthesised)) => {
                comp_bridge(arena, at, synthesised, expected, &mut self.conversions)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            | (
                Frame::Force { .. } | Frame::ValueBridge { .. },
                Produced::CompType(_) | Produced::Checked,
            )
            | (
                Frame::ApplicationHead { .. } | Frame::CompBridge { .. } | Frame::BindBound { .. },
                Produced::ValueType(_) | Produced::Checked,
            )
            | (
                Frame::ApplicationArgument { .. } | Frame::LambdaBody,
                Produced::ValueType(_) | Produced::CompType(_),
            )
            | (Frame::BindBody, Produced::ValueType(_)) => Err(CheckRefusal::MachineInvariant),
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
    use gandr_core_term::Value;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
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
        let pair = arena.value_pair(unit, unit);
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
        let rows: [Row<ValueId, ValueTypeId>; 11] = [
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
                pair,
                Err(unadmitted_value(pair, UnadmittedFormer::Pair)),
                unit_type,
                Err(unadmitted_value(pair, UnadmittedFormer::Pair)),
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
            let expected = form_value_type(&context, expected).unwrap();
            assert_eq!(
                check_value(&mut context, term, expected).map(|evidence| evidence.conversions()),
                checked,
                "{term:?} checks by its former's rule"
            );
        }
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
            let expected = form_comp_type(&context, expected).unwrap();
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
        let expected = form_comp_type(&context, returns_integer).unwrap();
        let wrong = form_comp_type(&context, returns_string).unwrap();

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
        let expected = form_comp_type(&context, returns_integer).unwrap();
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
        let expected = form_value_type(&context, string).unwrap();
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
        let expected = form_comp_type(&context, returns_string).unwrap();
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
        let formed_integer = form_value_type(&context, integer).unwrap();
        let formed_returner = form_comp_type(&context, returns_integer).unwrap();
        let formed_arrow = form_comp_type(&context, arrow).unwrap();
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
        let expected = form_value_type(&context, thunk_arrow).unwrap();
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
        let budget = CheckBudget::from(3_usize);
        let mut context = CheckingContext::new(&mut arena, budget);
        let expected = form_value_type(&context, thunk_arrow).unwrap();
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
        let expected = form_comp_type(&context, outer).unwrap();
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
            let expected_value = form_value_type(&context, expected_value).unwrap();
            let expected_comp = form_comp_type(&context, expected_comp).unwrap();
            let arena = context.arena();
            for &term in &terms.values {
                let synthesised = synthesise_value(&mut context, term);
                if let Ok(found) = synthesised {
                    prop_assert!(
                        check_value(&mut context, term, found.produced()).is_ok(),
                        "a synthesising value checks against its synthesised type"
                    );
                }
                let checked = check_value(&mut context, term, expected_value);
                match *arena.value(term).unwrap() {
                    | Value::Thunk(_) => prop_assert_eq!(
                        synthesised,
                        Err(CheckRefusal::NotSynthesisable { form: CheckingForm::Thunk(term) }),
                        "a thunk does not synthesise"
                    ),
                    | Value::Variable { .. } | Value::Constant(_) | Value::Unit | Value::Literal(_) => {
                        let bridged = synthesised.and_then(|found| {
                            let mut tally = found.conversions();
                            value_bridge(arena, term, found.produced().id(), expected_value.id(), &mut tally)
                                .map(|()| tally)
                        });
                        prop_assert_eq!(
                            checked.map(|evidence| evidence.conversions()),
                            bridged,
                            "a synthesising value checks exactly as it synthesises, then crosses the value bridge"
                        );
                    },
                    | Value::Pair(..) | Value::Injection(..) | Value::Lift { .. } => {
                        prop_assert!(false, "the recipe mints no former outside the fragment");
                    },
                }
                prop_assert_eq!(
                    context.binders().depth(Zone::Intuitionistic),
                    BinderDepth::from(0_usize),
                    "every run leaves the binders where it found them"
                );
            }
            for &term in &terms.comps {
                let synthesised = synthesise_comp(&mut context, term);
                if let Ok(found) = synthesised {
                    prop_assert!(
                        check_comp(&mut context, term, found.produced()).is_ok(),
                        "a synthesising computation checks against its synthesised type"
                    );
                }
                let checked = check_comp(&mut context, term, expected_comp);
                match *arena.computation(term).unwrap() {
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
                            comp_bridge(arena, term, found.produced().id(), expected_comp.id(), &mut tally)
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
            let arena = context.arena();
            for &(term, built, mode) in &terms.values {
                let expected = form_value_type(&context, built).unwrap();
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
                            value_bridge(arena, term, found.produced().id(), built, &mut scratch).is_ok(),
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
                let expected = form_comp_type(&context, built).unwrap();
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
                            comp_bridge(arena, term, found.produced().id(), built, &mut scratch).is_ok(),
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
