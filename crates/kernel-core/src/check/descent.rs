//! Replaying a fixpoint's structural-descent claim.
//!
//! The claim says the fixpoint is `fix x. λy. case y [C] of { c_i ↦ λf̄_i.
//! N_i }` at a function out of a nominal data application, each branch
//! opening exactly its constructor's fields, and every occurrence of `x` a
//! call `(force x) a` whose argument is a field of the scrutinised
//! constructor or the value a function field returns — the `t` of
//! `t ← (force f) ȳ`. The kernel replays it by one explicit-stack walk over
//! the body; it searches for nothing.
//!
//! # The fixpoint and its evidence
//!
//! `fix x. M` checks at every computation type `C`: its body checks at `C`
//! with `x : U C` bound innermost. Recursion goes through that binder, so a
//! body never names its own admission position and the admitted prefix stays
//! the only visible signature table. The evidence is `Partial`, no claim, or
//! `StructuralDescent`, the claim above. Admission replays the claim and
//! refuses a failed one as `DescentNotReplayed` carrying its
//! `DescentRefusal`. A partial fixpoint is admitted at any computation type,
//! including a loop at `F 1`.
//!
//! # The conversion gate
//!
//! Conversion replay unfolds a structural-descent fixpoint only where it is
//! applied to a constructor, `(fix x. M) (c v̄) ⇝ M[thunk (fix x. M)/x] (c v̄)`.
//! A partial fixpoint at that gate declines as
//! `ReplayDecline::PartialFixpoint`, so a trace that needs a partial unfolding
//! is never certified. Two stuck fixpoints compare by their bodies under one
//! self variable, whatever their evidence.
//!
//! # Decision
//!
//! **Choice.** Strict positivity and parameter uniformity, checked on the
//! native declaration, and one guarded fixpoint whose descent claim the kernel
//! replays (Eduardo Giménez, "Structural recursive definitions in type
//! theory", ICALP 1998, LNCS 1443, `doi:10.1007/BFb0055070`), rather than a
//! primitive recursor per declaration. The trusted base gains one former and
//! one replay check; every eliminator is an ordinary derived declaration that
//! the kernel re-checks.
//!
//! **Alternatives.** A primitive recursor per declaration adds a generated
//! rule per signature to the trusted base. A description universe decoded at
//! admission gives up native nominal identity inside the kernel (signatures
//! as a description theory: Ambrus Kaposi and András Kovács, "Signatures and
//! Induction Principles for Higher Inductive-Inductive Types", LMCS 16(1),
//! 2020, `doi:10.23638/LMCS-16(1:10)2020`). A size-based termination checker
//! needs sized types the kernel does not have.
//!
//! **Reversal.** Mutual blocks, indexed families, nested occurrences, or
//! descent through a non-field such as a measure each need their own formation
//! or replay rule. A measured recursion arrives as new evidence, not as a
//! widened structural check.
//!
//! # Witnesses
//!
//! The `recursive_data` integration suite: recursive blocks are admitted,
//! occurrences are refused by name, descent evidence replays or is refused by
//! name, derived eliminators are admitted, a fixpoint computes at a
//! constructor and replays, and a partial fixpoint declines at its gate.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DescentRefusal;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use quenchant_shape::shape::Maybe;

use super::Judgement;
use super::former;
use crate::error::KernelError;
use crate::rewrite::BinderDepth;

/// The binder level of the fixpoint's self reference, counted from the
/// fixpoint's body.
const SELF_LEVEL: u32 = 0;

/// The binder level of the scrutinised argument.
const ARGUMENT_LEVEL: u32 = 1;

/// The binder level of the first field, past the self binder and the
/// scrutinised argument's binder.
const FIRST_FIELD: u32 = 2;

quenchant_shape::reason_enum! {
    /// Why a value names no binder level inside the fixpoint.
    mod variable_level {
        /// The value is no variable bound inside the fixpoint.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The value is not a variable.
            NotVariable,
            /// The variable is bound outside the fixpoint.
            Outside,
        }
    }
}

/// The levels a self call may descend to beyond the branch's fields: the
/// results bound from forcing a function field, as a persistent list.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Results
{
    /// No function field's result is bound here.
    Empty,
    /// The link at this position of the result table is the innermost.
    At(ResultLink),
}

/// A position in a branch's result table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ResultLink(usize);

/// One bound function-field result and the results bound outside it.
#[derive(Clone, Copy, Debug)]
struct Link
{
    /// The binder level of the result.
    level: BinderDepth,
    /// The results bound outside it.
    outer: Results,
}

/// Whether a level is one a self call may descend to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Descent
{
    /// A field of the scrutinised constructor or a function field's result.
    Smaller,
    /// Anything else.
    Unrelated,
}

/// The fixed half of a branch walk: its field levels and the result table.
struct Branch
{
    /// One past the last field level.
    fields_end: BinderDepth,
    /// Every bound function-field result, linked innermost to outermost.
    links: Vec<Link>,
}

impl Branch
{
    /// Whether `level` is a field of the scrutinised constructor or a
    /// function field's result in scope at `results`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Smaller` exactly when `level` lies in the branch's field
    ///   range or is linked from `results`.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the `while let` loop follows outer links, each strictly
    ///   earlier in the table, not recursion.
    /// - measure: the position of the current link.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call at a field and at a function field's result
    ///   replays; a call at the scrutinee does not.
    /// - witness: `recursive_data::recursive_data::descent_evidence_replays_or_is_refused_by_name`
    #[spec(ensures: |ret| (ret == Descent::Smaller) == ((FIRST_FIELD .. u32::from(self.fields_end)).contains(&u32::from(level))
        || self.links.iter().any(|link| link.level == level)) || ret == Descent::Unrelated)]
    fn descent(
        &self,
        level: BinderDepth,
        results: Results,
    ) -> Descent
    {
        if (FIRST_FIELD .. u32::from(self.fields_end)).contains(&u32::from(level)) {
            return Descent::Smaller;
        }
        let mut cursor = results;
        while let Results::At(ResultLink(position)) = cursor {
            let Some(link) = self.links.get(position)
            else {
                return Descent::Unrelated;
            };
            if link.level == level {
                return Descent::Smaller;
            }
            cursor = link.outer;
        }
        Descent::Unrelated
    }
}

/// The binder level a value names from under `depth` binders, counted from
/// the fixpoint's body.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a variable at distance `d` names level `depth - 1 - d` when that
///   is non-negative.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the self variable is recognised at every depth the
///   derived eliminator's calls stand at, and a variable bound outside the
///   fixpoint is never mistaken for it.
/// - witness: `recursive_data::recursive_data::descent_evidence_replays_or_is_refused_by_name`
#[spec(ensures: |ret| matches!(ret, Maybe::Present(found) if u32::from(found) < u32::from(depth)) || matches!(ret, Maybe::Absent(_)))]
fn variable_level(
    arena: &TermArena,
    value: ValueId,
    depth: BinderDepth,
) -> Maybe<BinderDepth, variable_level::Absent>
{
    let Some(&Value::Variable(index)) = arena.value(value)
    else {
        return Maybe::Absent(variable_level::Absent::NotVariable);
    };
    match u32::from(depth)
        .checked_sub(u32::from(index))
        .and_then(|outer| outer.checked_sub(1))
    {
        | Some(level) => Maybe::Present(BinderDepth::from(level)),
        | None => Maybe::Absent(variable_level::Absent::Outside),
    }
}

/// Whether `bound` is `(force f) ȳ` for a field or function-field result
/// `f`: what it returns is a smaller value a self call may descend to.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Smaller` exactly when `bound` is at least one application over
///   the force of a variable whose level descends.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` loop descends application heads, not recursion.
/// - measure: the head's arena position.
///
/// # Adequacy
/// - hypothesis: L3 — a function field's hypothesis replays through the bind it
///   introduces.
/// - witness: `recursive_data::recursive_data::descent_evidence_replays_or_is_refused_by_name`
#[spec(ensures: |ret| ret == Descent::Unrelated || matches!(arena.computation(bound), Some(&Computation::Application(..))))]
fn forced_field(
    arena: &TermArena,
    branch: &Branch,
    bound: ComputationId,
    depth: BinderDepth,
    results: Results,
) -> Descent
{
    let mut focus = bound;
    let mut applications = 0_usize;
    while let Some(&Computation::Application(head, _)) = arena.computation(focus) {
        applications = applications.saturating_add(1);
        focus = head;
    }
    if applications == 0 {
        return Descent::Unrelated;
    }
    let Some(&Computation::Force(forced)) = arena.computation(focus)
    else {
        return Descent::Unrelated;
    };
    match variable_level(arena, forced, depth) {
        | Maybe::Present(level) if u32::from(level) != SELF_LEVEL => branch.descent(level, results),
        | Maybe::Present(_) | Maybe::Absent(_) => Descent::Unrelated,
    }
}

/// Walk one branch body, or the motive, for unguarded or non-descending
/// self references.
///
/// # Specification
/// - requires: `root` stands under `depth` binders counted from the fixpoint's
///   body, and `branch` names its field levels.
/// - ensures: success exactly when every occurrence of the self variable is the
///   head of a call whose argument is a field or a function field's result in
///   scope.
/// - fails: the first unguarded or non-descending occurrence the walk meets.
/// - panics: none.
///
/// # Errors
/// `UnguardedSelfReference` or `NonDescendingCall`.
///
/// # Termination
/// - reason: the `while let` worklist, not recursion.
/// - measure: the nodes left below the root along each path, finite because the
///   arena is acyclic.
///
/// # Adequacy
/// - hypothesis: L3 — a call at a field, at a function field's result and under
///   a nested binder replays; a call at the scrutinee itself and a bare forced
///   self reference refuse.
/// - witness: `recursive_data::recursive_data::descent_evidence_replays_or_is_refused_by_name`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(DescentRefusal::UnguardedSelfReference | DescentRefusal::NonDescendingCall)))]
fn walk(
    arena: &TermArena,
    branch: &mut Branch,
    root: AnyNode,
    depth: BinderDepth,
) -> Result<(), DescentRefusal>
{
    let mut pending: Vec<(AnyNode, BinderDepth, Results)> =
        Vec::from([(root, depth, Results::Empty)]);
    while let Some((node, depth, results)) = pending.pop() {
        let deeper = depth.deeper();
        match node {
            | AnyNode::Value(id) => match arena.value(id) {
                | Some(&Value::Variable(_)) => {
                    if matches!(variable_level(arena, id, depth), Maybe::Present(level) if u32::from(level) == SELF_LEVEL)
                    {
                        return Err(DescentRefusal::UnguardedSelfReference);
                    }
                },
                | Some(&Value::Constructor {
                    datatype,
                    ref fields,
                    ..
                }) => {
                    pending.push((AnyNode::ValueType(datatype), depth, results));
                    pending.extend(
                        fields
                            .iter()
                            .map(|&field| (AnyNode::Value(field), depth, results)),
                    );
                },
                | Some(&Value::Record(ref fields)) => {
                    pending.extend(
                        fields
                            .values()
                            .map(|&field| (AnyNode::Value(field), depth, results)),
                    );
                },
                | Some(&Value::SessionPath {
                    path_type,
                    payload_paths,
                    ..
                }) => {
                    pending.push((AnyNode::ValueType(path_type), depth, results));
                    pending.push((AnyNode::Value(payload_paths), depth, results));
                },
                | Some(&Value::PathEquiv {
                    path_type,
                    forward,
                    backward,
                    ..
                }) => {
                    pending.push((AnyNode::ValueType(path_type), depth, results));
                    pending.push((AnyNode::Value(forward), depth, results));
                    pending.push((AnyNode::Value(backward), depth, results));
                },
                | Some(
                    &(Value::PathProduct(first, second)
                    | Value::ListCons(first, second)
                    | Value::StaticApplication(first, second)),
                ) => {
                    pending.push((AnyNode::Value(first), depth, results));
                    pending.push((AnyNode::Value(second), depth, results));
                },
                | Some(&Value::Tuple(ref components)) => {
                    pending.extend(
                        components
                            .iter()
                            .map(|&component| (AnyNode::Value(component), depth, results)),
                    );
                },
                | Some(
                    &(Value::PathRefl(body) | Value::Injection(_, body) | Value::Lift { body, .. }),
                ) => {
                    pending.push((AnyNode::Value(body), depth, results));
                },
                | Some(&Value::Thunk(body)) => {
                    pending.push((AnyNode::Computation(body), depth, results));
                },
                | Some(&Value::Quote(quoted)) => {
                    pending.push((AnyNode::ValueType(quoted), depth, results));
                },
                | Some(&Value::QuoteComputation(quoted)) => {
                    pending.push((AnyNode::CompType(quoted), depth, results));
                },
                | Some(&(Value::Constant(_) | Value::Literal(_) | Value::ListNil)) | None => {},
            },
            | AnyNode::Computation(id) => match arena.computation(id) {
                | Some(&Computation::Application(head, argument)) => {
                    let call = matches!(arena.computation(head), Some(&Computation::Force(forced))
                        if matches!(variable_level(arena, forced, depth), Maybe::Present(level) if u32::from(level) == SELF_LEVEL));
                    if call {
                        let descends = match variable_level(arena, argument, depth) {
                            | Maybe::Present(level) => branch.descent(level, results),
                            | Maybe::Absent(_) => Descent::Unrelated,
                        };
                        if descends == Descent::Unrelated {
                            return Err(DescentRefusal::NonDescendingCall);
                        }
                    }
                    else {
                        pending.push((AnyNode::Computation(head), depth, results));
                        pending.push((AnyNode::Value(argument), depth, results));
                    }
                },
                | Some(&Computation::Bind(bound, body)) => {
                    let inner = match forced_field(arena, branch, bound, depth, results) {
                        | Descent::Smaller => {
                            let position = ResultLink(branch.links.len());
                            branch.links.push(Link {
                                level: depth,
                                outer: results,
                            });
                            Results::At(position)
                        },
                        | Descent::Unrelated => results,
                    };
                    pending.push((AnyNode::Computation(bound), depth, results));
                    pending.push((AnyNode::Computation(body), deeper, inner));
                },
                | Some(&Computation::DataCase {
                    scrutinee,
                    motive,
                    ref branches,
                }) => {
                    pending.push((AnyNode::Value(scrutinee), depth, results));
                    pending.push((AnyNode::CompType(motive), deeper, results));
                    pending.extend(
                        branches
                            .iter()
                            .map(|&case| (AnyNode::Computation(case), depth, results)),
                    );
                },
                | Some(&Computation::Case {
                    scrutinee,
                    ref branches,
                }) => {
                    pending.push((AnyNode::Value(scrutinee), depth, results));
                    pending.extend(
                        branches
                            .iter()
                            .map(|&case| (AnyNode::Computation(case), deeper, results)),
                    );
                },
                | Some(&(Computation::Lambda(body) | Computation::Fixpoint { body, .. })) => {
                    pending.push((AnyNode::Computation(body), deeper, results));
                },
                | Some(
                    &(Computation::RecordProjection(value, _)
                    | Computation::TupleProjection(value, _)
                    | Computation::Return(value)
                    | Computation::Force(value)),
                ) => {
                    pending.push((AnyNode::Value(value), depth, results));
                },
                | Some(&Computation::Transport(path, value)) => {
                    pending.push((AnyNode::Value(path), depth, results));
                    pending.push((AnyNode::Value(value), depth, results));
                },
                | Some(&Computation::ListFold {
                    element,
                    result,
                    list,
                    on_nil,
                    on_cons,
                }) => {
                    pending.push((AnyNode::ValueType(element), depth, results));
                    pending.push((AnyNode::ValueType(result), depth, results));
                    pending.push((AnyNode::Value(list), depth, results));
                    pending.push((AnyNode::Computation(on_nil), depth, results));
                    pending.push((AnyNode::Computation(on_cons), deeper.deeper(), results));
                },
                | None => {},
            },
            | AnyNode::ValueType(id) => match arena.value_type(id) {
                | Some(&ValueType::Data { ref arguments, .. }) => {
                    pending.extend(
                        arguments
                            .iter()
                            .map(|&argument| (AnyNode::Value(argument), depth, results)),
                    );
                },
                | Some(&ValueType::Record(ref fields)) => {
                    pending.extend(
                        fields
                            .values()
                            .map(|&field| (AnyNode::ValueType(field), depth, results)),
                    );
                },
                | Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                    pending.extend(
                        parts
                            .iter()
                            .map(|&part| (AnyNode::ValueType(part), depth, results)),
                    );
                },
                | Some(&ValueType::StaticPi {
                    domain: first,
                    codomain: second,
                }) => {
                    pending.push((AnyNode::ValueType(first), depth, results));
                    pending.push((AnyNode::ValueType(second), depth, results));
                },
                | Some(&ValueType::PathUniverse(source, target)) => {
                    pending.push((AnyNode::Value(source), depth, results));
                    pending.push((AnyNode::Value(target), depth, results));
                },
                | Some(&ValueType::Thunk(body)) => {
                    pending.push((AnyNode::CompType(body), depth, results));
                },
                | Some(
                    &(ValueType::Session {
                        payloads: inner, ..
                    }
                    | ValueType::Lift { inner, .. }
                    | ValueType::List(inner)),
                ) => {
                    pending.push((AnyNode::ValueType(inner), depth, results));
                },
                | Some(&ValueType::Element { code, .. }) => {
                    pending.push((AnyNode::Value(code), depth, results));
                },
                | Some(
                    &(ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_)),
                )
                | None => {},
            },
            | AnyNode::CompType(id) => match arena.comp_type(id) {
                | Some(&CompType::Returner(result)) => {
                    pending.push((AnyNode::ValueType(result), depth, results));
                },
                | Some(&CompType::Arrow { domain, codomain }) => {
                    pending.push((AnyNode::ValueType(domain), depth, results));
                    pending.push((AnyNode::CompType(codomain), depth, results));
                },
                | Some(&CompType::Pi { domain, codomain }) => {
                    pending.push((AnyNode::ValueType(domain), depth, results));
                    pending.push((AnyNode::CompType(codomain), deeper, results));
                },
                | Some(&CompType::Element { code, .. }) => {
                    pending.push((AnyNode::Value(code), depth, results));
                },
                | None => {},
            },
        }
    }
    Ok(())
}

/// Replay a fixpoint's structural-descent claim against its classifier.
///
/// # Specification
/// - requires: `body` is the fixpoint's body, scoped under its self binder, and
///   `expected` its classifier.
/// - ensures: success exactly when the classifier is a function out of a
///   nominal data application, the body is a lambda whose body is a case on
///   that lambda's variable with one branch per constructor, each branch opens
///   exactly its constructor's fields by lambdas, and every occurrence of the
///   self variable in the motive and the branches is a call at a field of the
///   scrutinised constructor or at a function field's result.
/// - provides: the ladder's first rung — a fixpoint whose claim replays unfolds
///   in conversion; the claim is checked, never searched for.
/// - fails: the first reason the walk meets, in the order above.
/// - panics: none.
///
/// # Errors
/// `DescentNotReplayed` with the reason.
///
/// # Adequacy
/// - hypothesis: L3 — every derived eliminator's fixpoint replays, including
///   one over a function field; a claim over a non-data classifier, a body that
///   does not case on its argument, a branch missing a field lambda, an
///   unguarded self reference and a call at the scrutinee itself each refuse by
///   their own reason.
/// - witness: `recursive_data::recursive_data::descent_evidence_replays_or_is_refused_by_name`
/// - witness: `recursive_data::recursive_data::derived_eliminators_are_admitted`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(KernelError::DescentNotReplayed(_))))]
pub(super) fn replay(
    arena: &TermArena,
    judgement: Judgement<'_>,
    expected: CompTypeId,
    body: ComputationId,
) -> Result<(), KernelError>
{
    let refuse = KernelError::DescentNotReplayed;
    let domain = match arena.comp_type(expected) {
        | Some(&(CompType::Arrow { domain, .. } | CompType::Pi { domain, .. })) => domain,
        | Some(&(CompType::Returner(_) | CompType::Element { .. })) | None => {
            return Err(refuse(DescentRefusal::NotOverData));
        },
    };
    let Some(&ValueType::Data { declaration, .. }) = arena.value_type(domain)
    else {
        return Err(refuse(DescentRefusal::NotOverData));
    };
    let signature = former::resolve(judgement, declaration)
        .map_err(|_not_data| refuse(DescentRefusal::NotOverData))?;
    let Some(&Computation::Lambda(inner)) = arena.computation(body)
    else {
        return Err(refuse(DescentRefusal::NotCaseOnArgument));
    };
    let Some(&Computation::DataCase {
        scrutinee,
        motive,
        ref branches,
    }) = arena.computation(inner)
    else {
        return Err(refuse(DescentRefusal::NotCaseOnArgument));
    };
    let on_argument = matches!(
        variable_level(arena, scrutinee, BinderDepth::from(FIRST_FIELD)),
        Maybe::Present(level) if u32::from(level) == ARGUMENT_LEVEL
    );
    if !on_argument || branches.len() != signature.constructors.len() {
        return Err(refuse(DescentRefusal::NotCaseOnArgument));
    }
    let mut fixed = Branch {
        fields_end: BinderDepth::from(FIRST_FIELD),
        links: Vec::new(),
    };
    walk(
        arena,
        &mut fixed,
        AnyNode::CompType(motive),
        BinderDepth::from(FIRST_FIELD).deeper(),
    )
    .map_err(refuse)?;
    for (&case, fields) in branches.iter().zip(signature.constructors) {
        let mut focus = case;
        let mut depth = BinderDepth::from(FIRST_FIELD);
        for _field in fields {
            let Some(&Computation::Lambda(opened)) = arena.computation(focus)
            else {
                return Err(refuse(DescentRefusal::BranchNotOverFields));
            };
            focus = opened;
            depth = depth.deeper();
        }
        let mut branch = Branch {
            fields_end: depth,
            links: Vec::new(),
        };
        walk(arena, &mut branch, AnyNode::Computation(focus), depth).map_err(refuse)?;
    }
    Ok(())
}
