//! Formation, family separation, sequential composition and directed replay.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;

use super::Allowance;
use super::Certificate;
use super::Family;
use super::Flow;
use super::FlowError;
use super::FlowId;
use super::FlowType;
use super::Flows;
use super::Reduct;
use super::Ride;
use super::Seam;
use super::coverage;
use crate::check::check_closed_value;
use crate::check::synth_closed_value;
use crate::conv::Convertibility;
use crate::conv::convertible_value_types;
use crate::path_universe::Dialogue;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;

/// Form a Flow, checking every reachable introduction in this invocation.
///
/// # Specification
/// - ensures: every translator checks in a fresh closed-check session and every
///   symbolic image replays positively; sequential seams match types. Explicit
///   feedback is refused, even when both endpoint types coincide. Generated
///   terms remain in `arena`; callers may restore its watermark.
/// - provides: `Flow_U source target`, never an admission capability.
/// - fails: code, typing, coverage, naturality, replay, seam or budget errors.
/// - panics: none.
///
/// # Errors
/// Any `FlowError` except family, motive and Path errors.
///
/// # Adequacy
/// - hypothesis: L3 — both terminal branches form; wrong images refuse;
///   injection followed by fold admits, but explicit feedback does not.
/// - witness: `flow_universe::tests::terminal_ride_and_stay_compute`
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
#[spec(ensures: |ret| match ret {
    Ok(classifier) => u64::from(budget) > 0 && match flows.get(root) {
        Ok(&Flow::Stay(code)) => classifier.source == classifier.target && matches!(arena.value(code), Some(&gandr_kernel_term::Value::Quote(root)) if root == classifier.source),
        Ok(&Flow::Forward { source, target, .. }) => matches!(arena.value(source), Some(&gandr_kernel_term::Value::Quote(root)) if root == classifier.source) && matches!(arena.value(target), Some(&gandr_kernel_term::Value::Quote(root)) if root == classifier.target),
        Ok(&Flow::Compose { seam: Seam::Sequence, .. }) => true,
        _ => false,
    },
    Err(FlowError::Cycle { first, second }) => flows.0.iter().any(|flow| matches!(flow, &Flow::Compose { first: a, second: b, seam: Seam::Feedback } if a == first && b == second)),
    Err(FlowError::UnknownFlow(id)) => flows.0.get(id.0).is_none(),
    Err(_) => true,
})]
#[inline]
pub fn form(
    arena: &mut TermArena,
    flows: &Flows,
    root: FlowId,
    budget: ReplayBudget,
) -> Result<FlowType, FlowError>
{
    let mut allowance = Allowance(u64::from(budget));
    let mut pending = Vec::from([(root, false)]);
    let mut formed = BTreeMap::<FlowId, FlowType>::new();
    while let Some((id, expanded)) = pending.pop() {
        allowance.charge()?;
        if formed.contains_key(&id) {
            continue;
        }
        let classifier = match flows.get(id)? {
            | &Flow::Stay(code) => {
                let source = coverage::code(arena, code, &mut allowance)?;
                FlowType {
                    source,
                    target: source,
                }
            },
            | &Flow::Forward {
                source,
                target,
                translator,
                ref images,
            } => {
                let source = coverage::code(arena, source, &mut allowance)?;
                let target = coverage::code(arena, target, &mut allowance)?;
                coverage::translator(arena, translator, source, target)?;
                coverage::forward(arena, source, target, translator, images, budget)?;
                FlowType { source, target }
            },
            | &Flow::Compose {
                first,
                second,
                seam,
            } => {
                if !expanded {
                    pending.push((id, true));
                    pending.push((second, false));
                    pending.push((first, false));
                    continue;
                }
                let left = formed.get(&first).ok_or(FlowError::UnknownFlow(first))?;
                let right = formed.get(&second).ok_or(FlowError::UnknownFlow(second))?;
                if convertible_value_types(arena, left.target, right.source)
                    != Convertibility::Convertible
                {
                    return Err(FlowError::EndpointMismatch);
                }
                if seam == Seam::Feedback {
                    if convertible_value_types(arena, right.target, left.source)
                        != Convertibility::Convertible
                    {
                        return Err(FlowError::EndpointMismatch);
                    }
                    return Err(FlowError::Cycle { first, second });
                }
                FlowType {
                    source: left.source,
                    target: right.target,
                }
            },
        };
        formed.insert(id, classifier);
    }
    formed.remove(&root).ok_or(FlowError::UnknownFlow(root))
}

/// A formed classifier retaining its independent certificate family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CertificateType
{
    /// The groupoidal classifier.
    Path(crate::path_universe::PathType),
    /// The directed classifier.
    Flow(FlowType),
}

/// Check a raw certificate against its expected family, without coercion.
///
/// # Specification
/// - ensures: only matching tags reach that family's formation rules. Native
///   paths synthesize through the ordinary checker before endpoint decoding.
/// - fails: `FamilyMismatch` in both coercion directions; `Typing` for native
///   checking failures; `Path` for a non-path classifier or invalid endpoints;
///   otherwise a Flow formation error.
/// - panics: none.
///
/// # Errors
/// `FamilyMismatch`, `Typing`, `Path`, or an error from `form`.
///
/// # Adequacy
/// - hypothesis: L3 — a valid equivalence fails as Flow, a valid forward
///   certificate fails as Path, and both retain their native classifications.
/// - witness: `flow_universe::tests::path_and_flow_never_coerce`
#[spec(ensures: |ret| match (certificate, expected, &ret) {
    (Certificate::Path(_), Family::Flow, &Err(FlowError::FamilyMismatch { expected: Family::Flow, actual: Family::Path }))
    | (Certificate::Flow(_), Family::Path, &Err(FlowError::FamilyMismatch { expected: Family::Path, actual: Family::Flow }))
    | (Certificate::Path(_), Family::Path, &Ok(CertificateType::Path(_)))
    | (Certificate::Flow(_), Family::Flow, &Ok(CertificateType::Flow(_))) => true,
    (Certificate::Path(_), Family::Path, &Err(ref error)) | (Certificate::Flow(_), Family::Flow, &Err(ref error)) => !matches!(error, &FlowError::FamilyMismatch { .. }),
    _ => false,
})]
#[inline]
pub fn form_certificate(
    arena: &mut TermArena,
    flows: &Flows,
    certificate: Certificate,
    expected: Family,
    budget: ReplayBudget,
) -> Result<CertificateType, FlowError>
{
    match (certificate, expected) {
        | (Certificate::Path(id), Family::Path) => {
            let classifier = synth_closed_value(arena, id)
                .map_err(|error| FlowError::Typing(Box::new(error)))?;
            let classifier = crate::path_universe::endpoints(arena, classifier, budget)
                .map_err(FlowError::Path)?;
            Ok(CertificateType::Path(classifier))
        },
        | (Certificate::Flow(id), Family::Flow) => {
            let classifier = form(arena, flows, id, budget)?;
            Ok(CertificateType::Flow(classifier))
        },
        | (Certificate::Path(_), Family::Flow) => Err(FlowError::FamilyMismatch {
            expected,
            actual: Family::Path,
        }),
        | (Certificate::Flow(_), Family::Path) => Err(FlowError::FamilyMismatch {
            expected,
            actual: Family::Flow,
        }),
    }
}

/// Resolve the directed eliminator's family tag.
///
/// # Specification
/// - ensures: only a Flow id reaches directed reduction or replay.
/// - fails: `FamilyMismatch` for a Path argument.
/// - panics: none.
///
/// # Errors
/// `FlowError::FamilyMismatch`.
///
/// # Adequacy
/// - hypothesis: L3 — ride cannot consume a valid equivalence.
/// - witness: `flow_universe::tests::path_and_flow_never_coerce`
#[spec(ensures: |ret| match (certificate, &ret) {
    (Certificate::Flow(id), &Ok(found)) => found == id,
    (Certificate::Path(_), &Err(FlowError::FamilyMismatch { expected: Family::Flow, actual: Family::Path })) => true,
    _ => false,
})]
fn flow_id(certificate: Certificate) -> Result<FlowId, FlowError>
{
    match certificate {
        | Certificate::Flow(id) => Ok(id),
        | Certificate::Path(_) => Err(FlowError::FamilyMismatch {
            expected: Family::Flow,
            actual: Family::Path,
        }),
    }
}

/// Elaborate `ride e v` at the canonical covariant motive `El(target)`.
///
/// # Specification
/// - ensures: the certificate forms as Flow and the input checks at its source.
/// - fails: family, formation or input-typing errors.
/// - panics: none.
///
/// # Errors
/// `FamilyMismatch`, `Typing`, or errors from `form`.
///
/// # Adequacy
/// - hypothesis: L3 — terminal transport admits both Bool constructors and
///   rejects a source value of the wrong type.
/// - witness: `flow_universe::tests::terminal_ride_and_stay_compute`
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |result| *result == term && matches!(result.certificate, Certificate::Flow(_))))]
#[inline]
pub fn elaborate(
    arena: &mut TermArena,
    flows: &Flows,
    term: Ride,
    budget: ReplayBudget,
) -> Result<Ride, FlowError>
{
    let id = flow_id(term.certificate)?;
    let classifier = form(arena, flows, id, budget)?;
    check_closed_value(arena, term.value, classifier.source)
        .map_err(|error| FlowError::Typing(Box::new(error)))?;
    Ok(term)
}

/// Lower a formed certificate to a closed forward translator without recursion.
///
/// # Specification
/// - requires: `root` passed formation in the current arena.
/// - ensures: Stay lowers to identity; Forward retains its translator; Sequence
///   uses CBPV bind in source-to-target order, with no inverse construction.
/// - fails: `UnknownFlow`, `Arena`, `Cycle` or `Budget`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — composed injection/fold acts as identity, and terminal
///   followed by an injection chooses that injection for either input.
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
#[spec(ensures: |ret| match ret {
    Ok(value) => u64::from(budget) > 0 && match flows.get(root) {
        Ok(&Flow::Forward { translator, .. }) => value == translator,
        Ok(&Flow::Stay(_) | &Flow::Compose { seam: Seam::Sequence, .. }) => matches!(arena.value(value), Some(&gandr_kernel_term::Value::Thunk(_))),
        _ => false,
    },
    Err(FlowError::Cycle { first, second }) => flows.0.iter().any(|flow| matches!(flow, &Flow::Compose { first: a, second: b, seam: Seam::Feedback } if a == first && b == second)),
    Err(_) => true,
})]
fn lower(
    arena: &mut TermArena,
    flows: &Flows,
    root: FlowId,
    budget: ReplayBudget,
) -> Result<ValueId, FlowError>
{
    let mut pending = Vec::from([(root, false)]);
    let mut lowered = BTreeMap::new();
    let mut allowance = Allowance(u64::from(budget));
    while let Some((id, expanded)) = pending.pop() {
        allowance.charge()?;
        if lowered.contains_key(&id) {
            continue;
        }
        let function = match flows.get(id)? {
            | &Flow::Stay(_) => {
                let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
                let returned = arena.computation_return(variable);
                let lambda = arena.computation_lambda(returned);
                arena.value_thunk(lambda)
            },
            | &Flow::Forward { translator, .. } => translator,
            | &Flow::Compose {
                first,
                second,
                seam,
            } => {
                if seam == Seam::Feedback {
                    return Err(FlowError::Cycle { first, second });
                }
                if !expanded {
                    pending.push((id, true));
                    pending.push((second, false));
                    pending.push((first, false));
                    continue;
                }
                let first = *lowered.get(&first).ok_or(FlowError::UnknownFlow(first))?;
                let second = *lowered.get(&second).ok_or(FlowError::UnknownFlow(second))?;
                let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
                let first = arena.computation_force(first);
                let first = arena.computation_application(first, variable);
                let second = arena.computation_force(second);
                let second = arena.computation_application(second, variable);
                // Closed translators need no shift beneath the result binder.
                let body = arena.computation_bind(first, second);
                let lambda = arena.computation_lambda(body);
                arena.value_thunk(lambda)
            },
        };
        lowered.insert(id, function);
    }
    lowered.remove(&root).ok_or(FlowError::Arena)
}

/// Fire one directed beta rule, leaving ordinary CBPV evaluation to replay.
///
/// # Specification
/// - requires: the certificate and source value have passed elaboration.
/// - ensures: Stay returns the identical value id without allocating; other
///   introductions expose their forward application as a computation.
/// - fails: family, missing syntax, feedback or construction-budget errors.
/// - panics: none.
/// - intension: Stay fires in one step and never evaluates an identity
///   translator.
///
/// # Errors
/// `FamilyMismatch`, `UnknownFlow`, `Cycle`, `Arena` or `Budget`.
///
/// # Adequacy
/// - hypothesis: L3 — Stay returns its original input at zero lowering budget;
///   forward action and composition compute their specified outputs.
/// - witness: `flow_universe::tests::terminal_ride_and_stay_compute`
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| match ret {
        Ok(Reduct::Return(value)) => value == term.value && arena.watermark() == before
            && matches!(term.certificate, Certificate::Flow(id) if matches!(flows.get(id), Ok(&Flow::Stay(_)))),
        Ok(Reduct::Compute(computation)) => matches!(arena.computation(computation), Some(&gandr_kernel_term::Computation::Application(_, value)) if value == term.value),
        Err(_) => true,
    },
)]
#[inline]
pub fn beta(
    arena: &mut TermArena,
    flows: &Flows,
    term: Ride,
    budget: ReplayBudget,
) -> Result<Reduct, FlowError>
{
    let id = flow_id(term.certificate)?;
    if matches!(flows.get(id)?, Flow::Stay(_)) {
        return Ok(Reduct::Return(term.value));
    }
    let function = lower(arena, flows, id, budget)?;
    let force = arena.computation_force(function);
    Ok(Reduct::Compute(
        arena.computation_application(force, term.value),
    ))
}

/// Re-form and replay a directed transport claim, restoring all intermediates.
///
/// # Specification
/// - ensures: source and expected result check at the formed endpoints; the
///   kernel builds the forward computation and replays the supplied dialogue.
///   The entry watermark is restored on success and every failure.
/// - fails: family, formation, typing or lowering errors; a bad dialogue
///   returns the ordinary declined or negative replay verdict, never positive
///   by default.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — terminal transport at both constructors is Convertible,
///   false output claims do not certify, and failure preserves the arena.
/// - witness: `flow_universe::tests::terminal_ride_and_stay_compute`
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
#[spec(captures: before = arena.watermark(), ensures: arena.watermark() == before)]
#[inline]
pub fn replay_ride(
    arena: &mut TermArena,
    flows: &Flows,
    term: Ride,
    expected: ComputationId,
    claim: EngineClaim,
    dialogue: &Dialogue,
    budget: ReplayBudget,
) -> Result<KernelVerdict, FlowError>
{
    let watermark = arena.watermark();
    let result = replay_checked(arena, flows, term, expected, claim, dialogue, budget);
    arena.truncate_to(watermark);
    result
}

/// Check and replay inside the public watermark-restoration boundary.
///
/// # Specification
/// - requires: the caller restores the entry watermark on every exit.
/// - ensures: the same checked verdict as `replay_ride`, retaining
///   intermediates.
/// - fails: the same errors as `replay_ride`.
/// - panics: none.
///
/// # Errors
/// As `replay_ride`.
///
/// # Adequacy
/// - hypothesis: L3 — typed expected results and source values gate replay.
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
#[spec(ensures: |ret| match term.certificate {
    Certificate::Path(_) => matches!(ret, Err(FlowError::FamilyMismatch { expected: Family::Flow, actual: Family::Path })),
    Certificate::Flow(_) => u64::from(budget) != 0 || matches!(ret, Err(FlowError::Budget)),
})]
fn replay_checked(
    arena: &mut TermArena,
    flows: &Flows,
    term: Ride,
    expected: ComputationId,
    claim: EngineClaim,
    dialogue: &Dialogue,
    budget: ReplayBudget,
) -> Result<KernelVerdict, FlowError>
{
    let id = flow_id(term.certificate)?;
    let classifier = form(arena, flows, id, budget)?;
    check_closed_value(arena, term.value, classifier.source)
        .map_err(|error| FlowError::Typing(Box::new(error)))?;
    let returner = arena.comp_type_returner(classifier.target);
    let expected_type = arena.value_type_thunk(returner);
    let expected_value = arena.value_thunk(expected);
    check_closed_value(arena, expected_value, expected_type)
        .map_err(|error| FlowError::Typing(Box::new(error)))?;
    let reduct = match beta(arena, flows, term, budget)? {
        | Reduct::Return(value) => arena.computation_return(value),
        | Reduct::Compute(computation) => computation,
    };
    Ok(crate::replay::replay(
        arena,
        &Unfoldings::new(Vec::new()),
        ReplaySides::Computations(reduct, expected),
        claim,
        dialogue.0.iter().copied(),
        budget,
    ))
}
