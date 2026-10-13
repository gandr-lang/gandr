//! Function extensionality in the core: `funext(f, g)`, decided by
//! computation and replayed by the kernel as a higher evaluation.
//!
//! # The rule
//!
//! `funext(f, g)` synthesises `Path(U (A → F B), f, g)` when `f` synthesises
//! the thunk type `U (A → F B)` of a pure non-dependent arrow, `g` checks
//! against it, both functions are closed, and at every input the coverage of
//! `A` reaches the two return one value. The coverage is the kernel's: the unit
//! value, a fresh variable at a base atom, each injection of a binary sum's
//! coverages, and each pairing of a binary product's, in the kernel's order,
//! each input standing under its own pattern binders. At an input `p` under
//! `n` binders the normaliser evaluates `thunk (λⁿ. force f p)` and `thunk
//! (λⁿ. force g p)`, every admitted definition unfolding; both must read back
//! to `thunk (λⁿ. return v)`, and the two normal forms must convert.
//!
//! A pair that returns different values at some input, or that does not
//! return at all there — stuck on a base variable, say — is
//! [`CheckRefusal::PointwiseDistinct`]: the rule admits what it shows and
//! refutes nothing it cannot, as reflexivity's endpoint rule does. Open
//! functions, a classifier that is no thunk of a pure non-dependent arrow, and
//! a domain or result outside the fragment below are
//! [`CheckRefusal::FunextUnsupported`].
//!
//! The judgement records, for each `funext` it accepts, both evaluations of
//! every component: the value each side returns and the machine's trace that
//! its claim converts to it. The bridge erases the record into the kernel's
//! higher evaluation, whose coverage the kernel regenerates and whose
//! dialogues it replays, unfolding the definitions it admitted. The core's
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
//! - **First order.** The domain and the result are built from the unit type,
//!   the base atoms and binary sums and products: the fragment where every
//!   input is a pattern and every result a first-order value the bridge
//!   translates as it stands. The kernel's coverage also binds a function
//!   argument, as two functions and their identity; the core does not decide
//!   that case yet, and refuses it by name. Reversal: a higher-order argument
//!   needs the core's coverage to bind the premise and the bridge to erase a
//!   nested evidence for a function-valued result.
//! - **Synthesised from its first function.** `f` names the classifier, so a λ
//!   written in its place does not synthesise and is refused as any such λ is.
//!   Reversal: a checking rule against `Path(T, f, g)` reads `T` from the
//!   expected type instead.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::Purity;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::code::Evaluation;
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

/// One covering input's two evaluations.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Component
{
    /// The first function at the input.
    left: Evaluation,
    /// The second function at the input.
    right: Evaluation,
}

impl Component
{
    /// The first function's evaluation at the input.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn left(&self) -> &Evaluation
    {
        &self.left
    }

    /// The second function's evaluation at the input.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn right(&self) -> &Evaluation
    {
        &self.right
    }
}

/// A function extensionality the judgement decided: one component per input
/// the domain's coverage reaches, in the kernel's order.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Funext
{
    /// The components, in coverage order.
    components: Vec<Component>,
}

impl Funext
{
    /// The components, in coverage order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn components(&self) -> &[Component]
    {
        &self.components
    }
}

/// One input of the coverage: a closed-under-its-binders pattern value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Pattern
{
    /// How many pattern binders the input stands under.
    binders: u32,
    /// The input.
    value: ValueId,
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

/// Decide `funext(f, g)` at `classifier`, the type `f` synthesised, `g`
/// already checked against it.
///
/// # Specification
/// - requires: `left` synthesised `classifier`; `right` checked against it;
///   both stand under the judgement's binders.
/// - ensures: on success one component per input the coverage of the
///   classifier's domain reaches, in the kernel's order, each holding both
///   functions' evaluations there, the two normal forms convertible.
/// - provides: the decision the judgement's `funext` rule makes and the record
///   the bridge erases.
/// - fails: [`CheckRefusal::FunextUnsupported`] at `at` for open functions, a
///   classifier that is no thunk of a pure non-dependent arrow, or a domain or
///   result outside the unit type, the base atoms and binary sums and products,
///   or a coverage past the kernel's allowance;
///   [`CheckRefusal::PointwiseDistinct`] at `at` when at some input either
///   function returns no value or the two values do not convert; a weak-head,
///   view or machine refusal as those raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: the coverage is a `while let` worklist over the domain's finite
///   tree and the components a `for` loop over its patterns, not recursion.
/// - measure: the tasks left, bounded by the kernel's coverage allowance; then
///   the patterns left.
///
/// # Adequacy
/// - hypothesis: L3 — `not ∘ not` and the identity on a binary sum of units
///   relate at both injections; `not` and the identity refuse as distinct; a
///   function of a base argument that does not return there refuses as
///   distinct; an open function and a function-typed domain refuse as
///   unsupported.
/// - witness: `funext::tests::pointwise_equal_functions_relate_by_computation`
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
    for function in [functions.0, functions.1] {
        let reach = loose_reach(context.arena(), CoreNode::Term(TermNode::Value(function)))?;
        if usize::from(reach) != 0 {
            return Err(unsupported);
        }
    }
    let head = context.whnf_value_type(classifier)?;
    let ValueTypeView::Thunk(computation) = value_type_view(context.arena(), head)?
    else {
        return Err(unsupported);
    };
    let computation = context.whnf_comp_type(computation)?;
    let CompTypeView::Arrow { domain, codomain } = comp_type_view(context.arena(), computation)?
    else {
        return Err(unsupported);
    };
    let codomain = context.whnf_comp_type(codomain)?;
    let CompTypeView::Returner { result, effects } = comp_type_view(context.arena(), codomain)?
    else {
        return Err(unsupported);
    };
    if effects.purity() != Purity::Pure {
        return Err(unsupported);
    }
    if let Maybe::Absent(_) = first_order(context, result)? {
        return Err(unsupported);
    }
    let Maybe::Present(patterns) = coverage(context, domain)?
    else {
        return Err(unsupported);
    };
    let mut components = Vec::with_capacity(patterns.len());
    for pattern in patterns {
        let [left, right] = [functions.0, functions.1].map(|function| {
            let arena = context.arena_mut();
            let forced = arena.computation_force(function);
            let mut body = arena.computation_application(forced, pattern.value);
            for _ in 0 .. pattern.binders {
                body = arena.computation_lambda(body);
            }
            arena.value_thunk(body)
        });
        let (Maybe::Present(left), Maybe::Present(right)) = (
            context.evaluate_claim(left)?,
            context.evaluate_claim(right)?,
        )
        else {
            return Err(CheckRefusal::PointwiseDistinct { at });
        };
        let verdict =
            context
                .definitions()
                .convert_terms(context.arena(), left.normal(), right.normal());
        match verdict {
            | Ok(gandr_core_nbe::MachineVerdict::Convertible) => {},
            | Ok(_) | Err(CheckRefusal::Undecided { .. }) => {
                return Err(CheckRefusal::PointwiseDistinct { at });
            },
            | Err(fault) => return Err(fault),
        }
        components.push(Component { left, right });
    }
    Ok(Funext { components })
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
            | ValueTypeView::Unit | ValueTypeView::Integer | ValueTypeView::String => {},
            | ValueTypeView::Sum(&[first, second]) | ValueTypeView::Product(&[first, second]) => {
                pending.extend([first, second]);
            },
            | _ => return Ok(Maybe::Absent(outside::Absent::Former)),
        }
    }
    Ok(Maybe::Present(ty))
}

/// The coverage of `domain`, as the kernel's related-input patterns lay it
/// out: the unit value; one fresh variable at a base atom; the left
/// injections of a binary sum's first coverage, then the right injections of
/// its second; and every pairing of a binary product's first coverage with
/// its second, the first's patterns read past the second's binders.
///
/// # Specification
/// - requires: `domain` is formed under the judgement's binders.
/// - ensures: the patterns in the kernel's order, or nothing when a type in the
///   tree is anything but the unit type, a base atom, or a sum or product of
///   exactly two, or when the work passes the kernel's coverage allowance.
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
///   order, and a function-typed domain covers as nothing.
/// - witness: `funext::tests::pointwise_equal_functions_relate_by_computation`
/// - witness: `funext::tests::what_the_rule_cannot_show_it_refuses_by_name`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present(ref patterns)) => !patterns.is_empty()
        && patterns.iter().all(|pattern| context.arena().value(pattern.value).is_some()),
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
            | Task::Cover(ty) => {
                let head = context.whnf_value_type(ty)?;
                match value_type_view(context.arena(), head)? {
                    | ValueTypeView::Unit => {
                        let unit = context.arena_mut().value_tuple(&[]);
                        built.push(Vec::from([Pattern {
                            binders: 0,
                            value: unit,
                        }]));
                    },
                    | ValueTypeView::Integer | ValueTypeView::String => {
                        let leaf = context
                            .arena_mut()
                            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                        built.push(Vec::from([Pattern {
                            binders: 1,
                            value: leaf,
                        }]));
                    },
                    | ValueTypeView::Sum(&[first, second]) => {
                        tasks.extend([Task::Sum, Task::Cover(second), Task::Cover(first)]);
                    },
                    | ValueTypeView::Product(&[first, second]) => {
                        tasks.extend([Task::Product, Task::Cover(second), Task::Cover(first)]);
                    },
                    | _ => return Ok(Maybe::Absent(outside::Absent::Former)),
                }
            },
            | Task::Sum | Task::Product => {
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
                            let value = context
                                .arena_mut()
                                .value_injection(summand.into(), pattern.value);
                            joined.push(Pattern { value, ..pattern });
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
                            let arena = context.arena_mut();
                            let shifted = gandr_core_term::shift_value(
                                arena,
                                left_pattern.value,
                                Binders::from(right_pattern.binders),
                            );
                            let value = arena.value_tuple(&[shifted, right_pattern.value]);
                            let binders = left_pattern
                                .binders
                                .checked_add(right_pattern.binders)
                                .ok_or(CheckRefusal::MachineInvariant)?;
                            joined.push(Pattern { binders, value });
                        }
                    }
                }
                built.push(joined);
            },
        }
    }
    match (built.pop(), built.is_empty()) {
        | (Some(patterns), true) => Ok(Maybe::Present(patterns)),
        | _ => Err(CheckRefusal::MachineInvariant),
    }
}

quenchant_shape::reason_enum! {
    /// Why a type has no coverage the rule decides over.
    pub mod outside {
        /// The reason the coverage stopped.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A type in the tree is outside the unit type, the base atoms
            /// and binary sums and products.
            Former,
            /// The coverage outgrew the kernel's allowance.
            Allowance,
        }
    }
}
