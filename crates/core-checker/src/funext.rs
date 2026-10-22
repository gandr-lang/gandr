//! Function extensionality in the core: `funext(f, g)`, decided by
//! computation and replayed by the kernel as a higher or a quantified
//! evaluation.
//!
//! # The rule
//!
//! `funext(f, g)` synthesises `Path(U (A → F B), f, g)` when `f` synthesises
//! the thunk type `U (A → F B)` of a pure non-dependent arrow, `g` checks
//! against it, both functions are closed, and at every input the coverage of
//! `A` reaches the two agree. The coverage is the kernel's: the unit value, a
//! fresh variable at a base atom, each injection of a binary sum's coverages,
//! each pairing of a binary product's, and at a function argument of type `T`
//! two functions and their identity, `f₀ f₁ : T, p : Path(T, f₀, f₁)`, the
//! left input reading `f₀` and the right `f₁` — in the kernel's order, each
//! input standing under its own pattern binders.
//!
//! At an input under `n` binders the normaliser reads `thunk (λⁿ. force f v₀)`
//! and `thunk (λⁿ. force g v₁)` to their normal forms, every admitted
//! definition unfolding. Both may return, `thunk (λⁿ. return v)`, and the two
//! returned values must convert: a return step. Both may instead stick at an
//! application of the two functions one premise relates, `force f₀ a` and
//! `force f₁ a` at convertible inputs, bare or bound as `x ← force f₀ a; K`:
//! an application step. The step then covers the applied function's result
//! type and continues each side at each output `o` — `return o`, or `K` with
//! `x` at `o` — under the output's binders, until every branch returns. This is
//! evaluation under the quantifier: the body's applications of its
//! higher-order argument are the places the decision splits.
//!
//! A pair that returns different values at some input, applies its argument at
//! inputs that do not convert, or neither returns nor sticks at a related
//! application — stuck on a base variable, say — is
//! [`CheckRefusal::PointwiseDistinct`]. That is the theorem, not a gap: two
//! functions that do not agree at a covering input are not identified, and the
//! rule admits what it shows and refutes nothing it cannot, as reflexivity's
//! endpoint rule does.
//!
//! [`CheckRefusal::FunextUnsupported`] is the first-order boundary. The
//! description-code fragment is first order by a decidability choice: code
//! equality is derived structural equality, so every domain the rule decides
//! has a finite kernel coverage. Open functions fall outside it because their
//! free variables are inputs no coverage reaches; a classifier that is no
//! thunk of a pure non-dependent arrow, because dependent arrows have their own
//! reserved evaluation and an effect relates nothing pointwise; a domain or
//! result reaching a list, a universe or a certificate, because those
//! identities are observed or certified rather than covered; a function
//! argument whose own domain or result is not first order, because its inputs
//! would need function identity between them; a function-valued result,
//! because its output evidence is itself a function identity; and a coverage
//! past the kernel's allowance.
//!
//! The judgement records, for each `funext` it accepts, every step in the
//! kernel's pre-order: both evaluations of a return, both normal forms of an
//! application with the premise it applies, and the machine's trace that each
//! claim converts to what it reached. The bridge erases a record of returns
//! alone into the kernel's higher evaluation and any other into its quantified
//! evaluation; the kernel regenerates the coverage and every branch, and
//! replays every dialogue, unfolding the definitions it admitted. The core's
//! decision is never trusted.
//!
//! # Decisions
//!
//! - **Decided by computation.** The choice is the coverage the kernel replays,
//!   evaluated by the normaliser at check time. The alternatives were a
//!   postulated `funext`, which no kernel rule replays, and function conversion
//!   up to pointwise equality, which would make conversion search the domain
//!   and widen the kernel's trusted base. Reversal: none while the kernel's
//!   identity at a function type is the related-inputs product.
//! - **Higher-order arguments decided under the quantifier.** A function
//!   argument is bound generically, never sampled or tabulated, and the body's
//!   applications of it split on the applied function's result. The
//!   alternatives were tabulating the argument over its finite first-order
//!   domain, which grows with the domain's size and still owes the premise
//!   evidence, and refusing every body that applies its argument, which left
//!   `λf. f(true)` without its reflexivity. Reversal: a function argument whose
//!   domain is itself higher order, which needs nested function identity
//!   between the inputs it is applied at.
//! - **First order elsewhere.** The outer result, and the domain and result of
//!   every function argument, are built from the unit type, the base atoms and
//!   binary sums and products: the fragment where every input is a pattern and
//!   every result a first-order value the bridge translates as it stands.
//!   Reversal: a function-valued result needs the bridge to erase nested
//!   evidence for it.
//! - **Synthesised from its first function.** `f` names the classifier, so a λ
//!   written in its place does not synthesise and is refused as any such λ is.
//!   Reversal: a checking rule against `Path(T, f, g)` reads `T` from the
//!   expected type instead.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::Purity;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::code::Evaluation;
use crate::code::Reading;
use crate::code::Stalled;
use crate::code::loose_reach;
use crate::context::CheckingContext;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TermNode;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

#[cfg(test)]
mod tests;

/// One step of a function extensionality's decision, in the kernel's
/// pre-order.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Step
{
    /// Both functions return at the step.
    Return
    {
        /// The first function's evaluation.
        left: Evaluation,
        /// The second function's evaluation.
        right: Evaluation,
    },
    /// Both functions stick at an application of the two functions the
    /// premise at `fibre` relates, at convertible inputs.
    Apply
    {
        /// The premise's de Bruijn index in the step's telescope.
        fibre: DeBruijnIndex,
        /// The first function's stuck normal form.
        left: Stalled,
        /// The second function's stuck normal form.
        right: Stalled,
    },
}

/// A function extensionality the judgement decided: per input the domain's
/// coverage reaches, in the kernel's order, its tree of steps in pre-order.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Funext
{
    /// The steps, in pre-order, input after input.
    steps: Vec<Step>,
}

impl Funext
{
    /// The steps, in pre-order, input after input.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn steps(&self) -> &[Step]
    {
        &self.steps
    }
}

/// A function coordinate of a pattern: where its two functions and their
/// identity stand, and the result type its applications cover.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Coordinate
{
    /// The left function, counted from the pattern's innermost binder.
    left: DeBruijnIndex,
    /// The right function.
    right: DeBruijnIndex,
    /// Their identity, the premise relating them.
    premise: DeBruijnIndex,
    /// The type the functions return.
    result: ValueTypeId,
}

impl Coordinate
{
    /// The coordinate read beneath `binders` more binders.
    ///
    /// # Specification
    /// - ensures: every index raised by `binders`.
    /// - fails: [`CheckRefusal::MachineInvariant`] past the index range.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal::MachineInvariant`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a twice-applied body's second application finds its
    ///   premise beneath the first's output binders; an index left unraised
    ///   names the wrong premise and refuses.
    /// - witness: `funext::tests::a_higher_order_argument_is_decided_under_the_quantifier`
    #[spec(ensures: |ret| match ret {
        | Ok(found) => found.result == self.result
            && Some(u32::from(found.premise)) == u32::from(self.premise).checked_add(u32::from(binders))
            && Some(u32::from(found.left)) == u32::from(self.left).checked_add(u32::from(binders))
            && Some(u32::from(found.right)) == u32::from(self.right).checked_add(u32::from(binders)),
        | Err(refusal) => refusal == CheckRefusal::MachineInvariant,
    })]
    fn beneath(
        self,
        binders: Binders,
    ) -> Result<Self, CheckRefusal>
    {
        let raise = |index: DeBruijnIndex| {
            u32::from(index)
                .checked_add(u32::from(binders))
                .map(DeBruijnIndex::from)
                .ok_or(CheckRefusal::MachineInvariant)
        };
        Ok(Self {
            left: raise(self.left)?,
            right: raise(self.right)?,
            premise: raise(self.premise)?,
            result: self.result,
        })
    }
}

/// One input of the coverage: its two sides, which differ only at a function
/// coordinate, under the pattern binders they stand beneath.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Pattern
{
    /// How many pattern binders the input stands under.
    binders: u32,
    /// The left side's input.
    left: ValueId,
    /// The right side's input.
    right: ValueId,
    /// The function coordinates the input binds.
    coordinates: Vec<Coordinate>,
}

/// A coverage task: a type to cover, or a binary former whose two coverages
/// are ready to join.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Task
{
    /// Cover the type.
    Cover(ValueTypeId),
    /// Inject the two coverages beneath, the second on top.
    Sum,
    /// Pair the two coverages beneath, the second on top.
    Product,
}

/// One node of the decision's pre-order walk: the telescope a step stands in
/// and the two computations it reads there.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Branch
{
    /// How many binders the telescope holds.
    binders: u32,
    /// The function coordinates bound in it.
    coordinates: Vec<Coordinate>,
    /// The first function's current computation.
    left: ComputationId,
    /// The second function's current computation.
    right: ComputationId,
}

/// What a stuck application's result flows into.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Continuation
{
    /// The application is the whole computation.
    Tail,
    /// The application is bound, and this body awaits its result.
    Bind(ComputationId),
}

/// A stuck normal form read under its telescope.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Stuck
{
    /// The function variable applied.
    head: DeBruijnIndex,
    /// The input it is applied at.
    input: ValueId,
    /// What the application's result flows into.
    continuation: Continuation,
}

/// Decide `funext(f, g)` at `classifier`, the type `f` synthesised, `g`
/// already checked against it.
///
/// # Specification
/// - requires: `left` synthesised `classifier`; `right` checked against it;
///   both stand under the judgement's binders.
/// - ensures: on success, per input the coverage of the classifier's domain
///   reaches, in the kernel's order, the pre-order tree of steps the module
///   docs describe, each return's two normal forms convertible and each
///   application's two inputs convertible.
/// - provides: the decision the judgement's `funext` rule makes and the record
///   the bridge erases.
/// - fails: [`CheckRefusal::FunextUnsupported`] at `at` past the first-order
///   boundary the module docs state; [`CheckRefusal::PointwiseDistinct`] at
///   `at` when at some step the two sides return values that do not convert,
///   apply their argument at inputs that do not convert, or neither return nor
///   stick at a related application; a weak-head, view or machine refusal as
///   those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: the coverage is a `while let` worklist over the domain's finite
///   tree, and the steps a `while let` worklist per pattern, not recursion.
/// - measure: the coverage tasks left, bounded by the kernel's coverage
///   allowance; then the steps left, each charged against the same allowance.
///
/// # Adequacy
/// - hypothesis: L3 — `not ∘ not` and the identity on a binary sum of units
///   relate at both injections; `not` and the identity refuse as distinct; a
///   function of a base argument that does not return there refuses as
///   distinct; `λf. f(true)` relates to itself and to its bind form, and a body
///   applying its argument twice nests its steps; a body applying its argument
///   at another input refuses as distinct; an open function and a function
///   argument whose own domain is a function refuse as unsupported.
/// - witness: `funext::tests::pointwise_equal_functions_relate_by_computation`
/// - witness: `funext::tests::a_higher_order_argument_is_decided_under_the_quantifier`
/// - witness: `funext::tests::what_the_rule_cannot_show_it_refuses_by_name`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::FunextUnsupported { at: site, .. } | CheckRefusal::PointwiseDistinct { at: site }) => site == at,
    | Ok(_) | Err(_) => true,
})]
pub fn decide(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    functions: (ValueId, ValueId),
    classifier: ValueTypeId,
) -> Result<Funext, CheckRefusal>
{
    let unsupported = CheckRefusal::FunextUnsupported { at, classifier };
    let distinct = CheckRefusal::PointwiseDistinct { at };
    for function in [functions.0, functions.1] {
        let reach = loose_reach(context.arena(), CoreNode::Term(TermNode::Value(function)))?;
        if usize::from(reach) != 0 {
            return Err(unsupported);
        }
    }
    let Maybe::Present((domain, result)) = arrow(context, classifier)?
    else {
        return Err(unsupported);
    };
    if let Maybe::Absent(_) = first_order(context, result)? {
        return Err(unsupported);
    }
    let Maybe::Present(patterns) = coverage(context, domain)?
    else {
        return Err(unsupported);
    };
    let mut allowance = u64::from(ReplayBudget::DEFAULT);
    let mut steps = Vec::new();
    for pattern in patterns {
        let [left, right] =
            [(functions.0, pattern.left), (functions.1, pattern.right)].map(|(function, input)| {
                let arena = context.arena_mut();
                let forced = arena.computation_force(function);
                arena.computation_application(forced, input)
            });
        let mut pending = Vec::from([Branch {
            binders: pattern.binders,
            coordinates: pattern.coordinates,
            left,
            right,
        }]);
        while let Some(branch) = pending.pop() {
            allowance = allowance.checked_sub(1).ok_or(unsupported)?;
            let [left, right] = [branch.left, branch.right].map(|computation| {
                let arena = context.arena_mut();
                let mut body = computation;
                for _ in 0 .. branch.binders {
                    body = arena.computation_lambda(body);
                }
                arena.value_thunk(body)
            });
            match (context.read_claim(left)?, context.read_claim(right)?) {
                (Reading::Returned(left), Reading::Returned(right)) => {
                    if agreement(context, left.normal(), right.normal())? != Agreement::Agree {
                        return Err(distinct);
                    }
                    steps.push(Step::Return { left, right });
                },
                (Reading::Stuck(left), Reading::Stuck(right)) => {
                    let (Maybe::Present(left_stuck), Maybe::Present(right_stuck)) = (
                        stuck(context, left.normal(), Binders::from(branch.binders)),
                        stuck(context, right.normal(), Binders::from(branch.binders)),
                    )
                    else {
                        return Err(distinct);
                    };
                    let Some(&coordinate) = branch
                        .coordinates
                        .iter()
                        .find(|coordinate| coordinate.left == left_stuck.head)
                    else {
                        return Err(distinct);
                    };
                    if coordinate.right != right_stuck.head
                        || agreement(context, left_stuck.input, right_stuck.input)?
                            != Agreement::Agree
                    {
                        return Err(distinct);
                    }
                    let Maybe::Present(outputs) = coverage(context, coordinate.result)?
                    else {
                        return Err(unsupported);
                    };
                    steps.push(Step::Apply {
                        fibre: coordinate.premise,
                        left,
                        right,
                    });
                    for output in outputs.into_iter().rev() {
                        allowance = allowance.checked_sub(1).ok_or(unsupported)?;
                        let extension = Binders::from(output.binders);
                        let coordinates = branch
                            .coordinates
                            .iter()
                            .map(|coordinate| coordinate.beneath(extension))
                            .collect::<Result<Vec<_>, _>>()?;
                        let left =
                            resume(context, left_stuck.continuation, (output.left, extension));
                        let right =
                            resume(context, right_stuck.continuation, (output.right, extension));
                        pending.push(Branch {
                            binders: branch
                                .binders
                                .checked_add(output.binders)
                                .ok_or(CheckRefusal::MachineInvariant)?,
                            coordinates,
                            left,
                            right,
                        });
                    }
                },
                (Reading::Returned(_), Reading::Stuck(_))
                | (Reading::Stuck(_), Reading::Returned(_)) => return Err(distinct),
            }
        }
    }
    Ok(Funext { steps })
}

/// Whether the two values convert, under the binders they stand beneath.
///
/// # Specification
/// - ensures: [`Agreement::Agree`] exactly when the machine converts them;
///   [`Agreement::Differ`] when it refutes, declines or leaves them undecided.
/// - fails: a machine fault other than undecidedness, as it raises it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — two functions returning the same boolean agree, and
///   negation against the identity, or an argument applied at true against one
///   applied at false, differ.
/// - witness: `funext::tests::pointwise_equal_functions_relate_by_computation`
/// - witness: `funext::tests::what_the_rule_cannot_show_it_refuses_by_name`
#[spec(ensures: |ret| !matches!(ret, Err(CheckRefusal::Undecided { .. })))]
fn agreement(
    context: &CheckingContext<'_>,
    left: ValueId,
    right: ValueId,
) -> Result<Agreement, CheckRefusal>
{
    match context
        .definitions()
        .convert_terms(context.arena(), left, right)
    {
        Ok(gandr_core_nbe::MachineVerdict::Convertible) => Ok(Agreement::Agree),
        Ok(_) | Err(CheckRefusal::Undecided { .. }) => Ok(Agreement::Differ),
        Err(fault) => Err(fault),
    }
}

/// Whether two values the decision compares agree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Agreement
{
    /// The machine converts them.
    Agree,
    /// The machine does not show them convertible.
    Differ,
}

/// The domain and result of `classifier`, when it is the thunk type of a pure
/// non-dependent arrow.
///
/// # Specification
/// - requires: `classifier` is formed under the judgement's binders.
/// - ensures: `(A, B)` when `classifier`, read at its weak heads, is `U (A → F
///   B)` with a pure returner; otherwise [`outside::Absent::Former`].
/// - fails: a weak-head or view refusal as those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — the Bool function type reads its two halves, and a
///   function type over functions reads a thunk type as its domain.
/// - witness: `funext::tests::a_higher_order_argument_is_decided_under_the_quantifier`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present((domain, result))) => context.arena().value_type(domain).is_some() && context.arena().value_type(result).is_some(),
    | Ok(Maybe::Absent(reason)) => reason == outside::Absent::Former,
    | Err(_) => true,
})]
fn arrow(
    context: &mut CheckingContext<'_>,
    classifier: ValueTypeId,
) -> Result<Maybe<(ValueTypeId, ValueTypeId), outside::Absent>, CheckRefusal>
{
    let head = context.whnf_value_type(classifier)?;
    let ValueTypeView::Thunk(computation) = value_type_view(context.arena(), head)?
    else {
        return Ok(Maybe::Absent(outside::Absent::Former));
    };
    let computation = context.whnf_comp_type(computation)?;
    let CompTypeView::Arrow { domain, codomain } = comp_type_view(context.arena(), computation)?
    else {
        return Ok(Maybe::Absent(outside::Absent::Former));
    };
    let codomain = context.whnf_comp_type(codomain)?;
    let CompTypeView::Returner { result, effects } = comp_type_view(context.arena(), codomain)?
    else {
        return Ok(Maybe::Absent(outside::Absent::Former));
    };
    if effects.purity() != Purity::Pure {
        return Ok(Maybe::Absent(outside::Absent::Former));
    }
    Ok(Maybe::Present((domain, result)))
}

/// `ty`, when it is built from the unit type, the base atoms and binary sums
/// and products alone: a result the bridge translates as it stands.
///
/// # Specification
/// - requires: `ty` is formed under the judgement's binders.
/// - ensures: `ty` exactly when every type the walk reaches, read at its weak
///   head, is the unit type, a base atom, or a sum or product of exactly two;
///   otherwise [`outside::Absent::Former`].
/// - fails: a weak-head or view refusal as those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a `while let` worklist over the finite type tree, not recursion.
/// - measure: the types left, each replaced by its strictly smaller children.
///
/// # Adequacy
/// - hypothesis: L3 — a binary sum of units is first order and a thunk type is
///   not.
/// - witness: `funext::tests::what_the_rule_cannot_show_it_refuses_by_name`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present(found)) => found == ty,
    | Ok(Maybe::Absent(reason)) => reason == outside::Absent::Former,
    | Err(_) => true,
})]
fn first_order(
    context: &mut CheckingContext<'_>,
    ty: ValueTypeId,
) -> Result<Maybe<ValueTypeId, outside::Absent>, CheckRefusal>
{
    let mut pending = Vec::from([ty]);
    while let Some(part) = pending.pop() {
        let head = context.whnf_value_type(part)?;
        match value_type_view(context.arena(), head)? {
            ValueTypeView::Unit | ValueTypeView::Integer | ValueTypeView::String => {},
            ValueTypeView::Sum(&[first, second]) | ValueTypeView::Product(&[first, second]) => {
                pending.extend([first, second]);
            },
            ValueTypeView::Data { .. }
            | ValueTypeView::Record(_)
            | ValueTypeView::Stack { .. }
            | ValueTypeView::PathUniverse(..)
            | ValueTypeView::Path { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::Sum(_)
            | ValueTypeView::List(_)
            | ValueTypeView::Thunk(_)
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Lift { .. }
            | ValueTypeView::Element { .. }
            | ValueTypeView::Product(_)
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::Sigma { .. }
            | ValueTypeView::Abstract(_)
            | ValueTypeView::Staged { .. }
            | ValueTypeView::Kept { .. }
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Buffer
            | ValueTypeView::Session(_)
            | ValueTypeView::World(_)
            | ValueTypeView::Unknown => return Ok(Maybe::Absent(outside::Absent::Former)),
        }
    }
    Ok(Maybe::Present(ty))
}

/// The coverage of `domain`, as the kernel's related-input patterns lay it
/// out: the unit value; one fresh variable at a base atom; at a function type
/// whose domain and result are first order, two functions and their identity,
/// the left side reading the first and the right the second; the left
/// injections of a binary sum's first coverage, then the right injections of
/// its second; and every pairing of a binary product's first coverage with
/// its second, the first's patterns read past the second's binders.
///
/// # Specification
/// - requires: `domain` is formed under the judgement's binders.
/// - ensures: the patterns in the kernel's order, each function coordinate's
///   indices counted in its own pattern, or nothing when a type in the tree is
///   anything but the unit type, a base atom, a sum or product of exactly two,
///   or a pure non-dependent function type between first-order types, or when
///   the work passes the kernel's coverage allowance.
/// - fails: a weak-head or view refusal as those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a `while let` worklist over the finite type tree, not recursion.
/// - measure: the tasks left, each cover task replaced by strictly smaller
///   ones, every turn charged against the allowance.
///
/// # Adequacy
/// - hypothesis: L3 — a binary sum of units covers as its two injections in
///   order; the Bool function type covers as two functions and their identity;
///   a function type over functions covers as nothing.
/// - witness: `funext::tests::pointwise_equal_functions_relate_by_computation`
/// - witness: `funext::tests::a_higher_order_argument_is_decided_under_the_quantifier`
/// - witness: `funext::tests::what_the_rule_cannot_show_it_refuses_by_name`
/// - witness: `funext::tests::a_function_coordinate_keeps_distinct_sides_inside_sums_and_pairs`
/// - witness: `funext::tests::an_atom_covers_as_one_variable_and_a_dependent_or_bare_thunk_as_nothing`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present(ref patterns)) => !patterns.is_empty()
        && patterns.iter().all(|pattern| context.arena().value(pattern.left).is_some() && context.arena().value(pattern.right).is_some()),
    | Ok(Maybe::Absent(_)) | Err(_) => true,
})]
fn coverage(
    context: &mut CheckingContext<'_>,
    domain: ValueTypeId,
) -> Result<Maybe<Vec<Pattern>, outside::Absent>, CheckRefusal>
{
    let mut allowance = u64::from(ReplayBudget::DEFAULT);
    let mut tasks = Vec::from([Task::Cover(domain)]);
    let mut built: Vec<Vec<Pattern>> = Vec::new();
    while let Some(task) = tasks.pop() {
        let Some(left) = allowance.checked_sub(1)
        else {
            return Ok(Maybe::Absent(outside::Absent::Allowance));
        };
        allowance = left;
        match task {
            Task::Cover(ty) => {
                let head = context.whnf_value_type(ty)?;
                match value_type_view(context.arena(), head)? {
                    ValueTypeView::Unit => {
                        let unit = context.arena_mut().value_tuple(&[]);
                        built.push(Vec::from([Pattern {
                            binders: 0,
                            left: unit,
                            right: unit,
                            coordinates: Vec::new(),
                        }]));
                    },
                    ValueTypeView::Integer | ValueTypeView::String => {
                        let leaf = context
                            .arena_mut()
                            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                        built.push(Vec::from([Pattern {
                            binders: 1,
                            left: leaf,
                            right: leaf,
                            coordinates: Vec::new(),
                        }]));
                    },
                    ValueTypeView::Thunk(_) => {
                        let Maybe::Present((argument, result)) = arrow(context, head)?
                        else {
                            return Ok(Maybe::Absent(outside::Absent::Former));
                        };
                        for part in [argument, result] {
                            if let Maybe::Absent(reason) = first_order(context, part)? {
                                return Ok(Maybe::Absent(reason));
                            }
                        }
                        let [left, right] = [2_u32, 1].map(|index| {
                            context
                                .arena_mut()
                                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
                        });
                        built.push(Vec::from([Pattern {
                            binders: 3,
                            left,
                            right,
                            coordinates: Vec::from([Coordinate {
                                left: DeBruijnIndex::from(2_u32),
                                right: DeBruijnIndex::from(1_u32),
                                premise: DeBruijnIndex::from(0_u32),
                                result,
                            }]),
                        }]));
                    },
                    ValueTypeView::Sum(&[first, second]) => {
                        tasks.extend([Task::Sum, Task::Cover(second), Task::Cover(first)]);
                    },
                    ValueTypeView::Product(&[first, second]) => {
                        tasks.extend([Task::Product, Task::Cover(second), Task::Cover(first)]);
                    },
                    ValueTypeView::Data { .. }
                    | ValueTypeView::Record(_)
                    | ValueTypeView::Stack { .. }
                    | ValueTypeView::PathUniverse(..)
                    | ValueTypeView::Path { .. }
                    | ValueTypeView::Flow { .. }
                    | ValueTypeView::Run(_)
                    | ValueTypeView::Sum(_)
                    | ValueTypeView::List(_)
                    | ValueTypeView::Universe { .. }
                    | ValueTypeView::Lift { .. }
                    | ValueTypeView::Element { .. }
                    | ValueTypeView::Product(_)
                    | ValueTypeView::StaticPi { .. }
                    | ValueTypeView::Sigma { .. }
                    | ValueTypeView::Abstract(_)
                    | ValueTypeView::Staged { .. }
                    | ValueTypeView::Kept { .. }
                    | ValueTypeView::Capability { .. }
                    | ValueTypeView::Buffer
                    | ValueTypeView::Session(_)
                    | ValueTypeView::World(_)
                    | ValueTypeView::Unknown => return Ok(Maybe::Absent(outside::Absent::Former)),
                }
            },
            Task::Sum | Task::Product => {
                let (Some(second), Some(first)) = (built.pop(), built.pop())
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let mut joined = Vec::new();
                if task == Task::Sum {
                    for (summand, branch) in [(0_usize, first), (1_usize, second)] {
                        for pattern in branch {
                            let Some(left) = allowance.checked_sub(1)
                            else {
                                return Ok(Maybe::Absent(outside::Absent::Allowance));
                            };
                            allowance = left;
                            let arena = context.arena_mut();
                            let left = arena.value_injection(summand.into(), pattern.left);
                            let right = if pattern.left == pattern.right {
                                left
                            }
                            else {
                                arena.value_injection(summand.into(), pattern.right)
                            };
                            joined.push(Pattern {
                                left,
                                right,
                                ..pattern
                            });
                        }
                    }
                }
                else {
                    for left_pattern in &first {
                        for right_pattern in &second {
                            let Some(left) = allowance.checked_sub(1)
                            else {
                                return Ok(Maybe::Absent(outside::Absent::Allowance));
                            };
                            allowance = left;
                            let past = Binders::from(right_pattern.binders);
                            let arena = context.arena_mut();
                            let shifted_left =
                                gandr_core_term::shift_value(arena, left_pattern.left, past)
                                    .settle(arena);
                            let shifted_right = if left_pattern.left == left_pattern.right {
                                shifted_left
                            }
                            else {
                                gandr_core_term::shift_value(arena, left_pattern.right, past)
                                    .settle(arena)
                            };
                            let left = arena.value_tuple(&[shifted_left, right_pattern.left]);
                            let right = if shifted_left == shifted_right
                                && right_pattern.left == right_pattern.right
                            {
                                left
                            }
                            else {
                                arena.value_tuple(&[shifted_right, right_pattern.right])
                            };
                            let binders = left_pattern
                                .binders
                                .checked_add(right_pattern.binders)
                                .ok_or(CheckRefusal::MachineInvariant)?;
                            let mut coordinates = left_pattern
                                .coordinates
                                .iter()
                                .map(|coordinate| coordinate.beneath(past))
                                .collect::<Result<Vec<_>, _>>()?;
                            coordinates.extend_from_slice(&right_pattern.coordinates);
                            joined.push(Pattern {
                                binders,
                                left,
                                right,
                                coordinates,
                            });
                        }
                    }
                }
                built.push(joined);
            },
        }
    }
    match (built.pop(), built.is_empty()) {
        (Some(patterns), true) => Ok(Maybe::Present(patterns)),
        _ => Err(CheckRefusal::MachineInvariant),
    }
}

/// Read a closed normal form as an application of a bound function, stuck
/// beneath `binders` binders.
///
/// # Specification
/// - requires: `normal` lives in the context's arena.
/// - ensures: the applied variable, its input and its continuation when
///   `normal` is a thunk of `binders` lambdas over `force x a` or `y ← force x
///   a; K` with `x` an intuitionistic variable; otherwise
///   [`applied::Absent::Elsewhere`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a tail application and a bound one both read; a body
///   stuck on a base variable's case reads elsewhere.
/// - witness: `funext::tests::a_higher_order_argument_is_decided_under_the_quantifier`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(found) => context.arena().value(found.input).is_some(),
    | Maybe::Absent(reason) => reason == applied::Absent::Elsewhere,
})]
fn stuck(
    context: &CheckingContext<'_>,
    normal: ValueId,
    binders: Binders,
) -> Maybe<Stuck, applied::Absent>
{
    let arena = context.arena();
    let elsewhere = Maybe::Absent(applied::Absent::Elsewhere);
    let Some(&Value::Thunk(mut body)) = arena.value(normal)
    else {
        return elsewhere;
    };
    for _ in 0 .. u32::from(binders) {
        let Some(&Computation::Lambda(inner)) = arena.computation(body)
        else {
            return elsewhere;
        };
        body = inner;
    }
    let (application, continuation) = match arena.computation(body) {
        Some(&Computation::Bind(bound, rest)) => (bound, Continuation::Bind(rest)),
        _ => (body, Continuation::Tail),
    };
    let Some(&Computation::Application(forced, input)) = arena.computation(application)
    else {
        return elsewhere;
    };
    let Some(&Computation::Force(function)) = arena.computation(forced)
    else {
        return elsewhere;
    };
    let Some(&Value::Variable {
        zone: Zone::Intuitionistic,
        index,
    }) = arena.value(function)
    else {
        return elsewhere;
    };
    Maybe::Present(Stuck {
        head: index,
        input,
        continuation,
    })
}

/// The computation a stuck side continues as once its application returns
/// `output.0`, beneath `output.1` more binders.
///
/// # Specification
/// - requires: `output.0` stands under the step's telescope extended by
///   `output.1` binders; a bound continuation stands under the telescope and
///   its own binder.
/// - ensures: `return o` for a tail application; for a bound one, its body
///   weakened past the extension above its own binder, then instantiated at `o`
///   — the kernel's own continuation, read the same way.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a twice-applied body reads its second application at the
///   first's output.
/// - witness: `funext::tests::a_higher_order_argument_is_decided_under_the_quantifier`
#[spec(ensures: |ret| match continuation {
    | Continuation::Tail => context.arena().computation(ret) == Some(&Computation::Return(output.0)),
    | Continuation::Bind(_) => context.arena().computation(ret).is_some(),
})]
fn resume(
    context: &mut CheckingContext<'_>,
    continuation: Continuation,
    output: (ValueId, Binders),
) -> ComputationId
{
    let (value, extension) = output;
    let arena = context.arena_mut();
    match continuation {
        Continuation::Tail => arena.computation_return(value),
        Continuation::Bind(body) => {
            let mut carried = Vec::new();
            let weakened = gandr_core_term::shift_computation_under(
                arena,
                body,
                Binders::from(1_u32),
                extension,
            )
            .settle_traced(arena, &mut carried);
            gandr_core_term::instantiate_computation_traced(arena, weakened, value, &mut carried)
        },
    }
}

quenchant_shape::reason_enum! {
    /// Why a type has no coverage the rule decides over.
    pub mod outside {
        /// The reason the coverage stopped.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A type in the tree is outside the unit type, the base atoms,
            /// binary sums and products, and pure non-dependent function
            /// types between first-order types.
            Former,
            /// The coverage outgrew the kernel's allowance.
            Allowance,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a stuck normal form is no application of a bound function.
    pub mod applied {
        /// The reason the form was not read as one.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The form is stuck elsewhere: on a base variable, an opaque
            /// constant or an effect, or at something other than a forced
            /// variable applied once.
            Elsewhere,
        }
    }
}
