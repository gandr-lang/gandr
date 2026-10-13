//! Formation, family separation, sequential composition and directed replay.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use super::Allowance;
use super::Boundary;
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
use super::Variance;
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
///   feedback is refused, even when both endpoint types coincide. A function
///   introduction's endpoints are function codes over first-order codes, and
///   each boundary flow runs in the direction its [`Boundary::variance`] fixes.
///   Generated terms remain in `arena`; callers may restore its watermark. A
///   session introduction synthesizes through the ordinary closed checker,
///   which rechecks its `Flow_U` classifier, every supplied simulation pair and
///   every native payload-path obligation.
/// - provides: `Flow_U source target`, never an admission capability.
/// - fails: code, typing, coverage, naturality, replay, seam, boundary or
///   budget errors.
/// - panics: none.
///
/// # Errors
/// Code, typing, session-replay, seam, boundary or budget errors.
///
/// # Adequacy
/// - hypothesis: L3 — both terminal branches form; wrong images refuse;
///   injection followed by fold admits, but explicit feedback does not; a
///   function flow forms only with its domain boundary reversed.
/// - witness: `flow_universe::tests::terminal_ride_and_stay_compute`
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
/// - witness: `flow_universe::tests::function::directed_funext_forms_and_rides_in_variance_order`
/// - witness: `flow_universe::tests::function::symmetry_refusal_holds_at_a_thunk_code`
/// - witness: `session::tests::session_relations_replay_without_search`
#[spec(ensures: |ret| match ret {
    Ok(classifier) => u64::from(budget) > 0 && match flows.get(root) {
        Ok(&Flow::Stay(code)) => classifier.source == classifier.target && matches!(arena.value(code), Some(&gandr_kernel_term::Value::Quote(root)) if root == classifier.source),
        Ok(&Flow::Session(value)) => arena.value(value).is_some(),
        Ok(&Flow::Forward { source, target, .. } | &Flow::Function { source, target, .. }) => matches!(arena.value(source), Some(&gandr_kernel_term::Value::Quote(root)) if root == classifier.source) && matches!(arena.value(target), Some(&gandr_kernel_term::Value::Quote(root)) if root == classifier.target),
        Ok(&Flow::Compose { seam: Seam::Sequence, .. }) => true,
        _ => false,
    },
    Err(FlowError::Cycle { first, second }) => flows.0.iter().any(|flow| matches!(flow, &Flow::Compose { first: a, second: b, seam: Seam::Feedback } if a == first && b == second)),
    Err(FlowError::UnknownFlow(id)) => flows.0.get(id.0).is_none(),
    Err(FlowError::Boundary(_)) => flows.0.iter().any(|flow| matches!(flow, &Flow::Function { .. })),
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
            | &Flow::Session(value) => {
                let classifier = synth_closed_value(arena, value).map_err(|error| match error {
                    | crate::KernelError::Session(error) => FlowError::Session(error),
                    | error => FlowError::Typing(Box::new(error)),
                })?;
                super::endpoints(arena, classifier, budget)?
            },
            | &Flow::Stay(code) => {
                let source = coverage::endpoint(arena, code, &mut allowance)?;
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
            | &Flow::Function {
                source,
                target,
                domain,
                codomain,
            } => {
                if !expanded {
                    pending.push((id, true));
                    pending.push((codomain, false));
                    pending.push((domain, false));
                    continue;
                }
                let source = coverage::function(arena, source, &mut allowance)?;
                let target = coverage::function(arena, target, &mut allowance)?;
                let domain = formed.get(&domain).ok_or(FlowError::UnknownFlow(domain))?;
                boundary(
                    arena,
                    Boundary::Domain,
                    *domain,
                    source.domain,
                    target.domain,
                )?;
                let codomain = formed
                    .get(&codomain)
                    .ok_or(FlowError::UnknownFlow(codomain))?;
                boundary(
                    arena,
                    Boundary::Codomain,
                    *codomain,
                    source.codomain,
                    target.codomain,
                )?;
                FlowType {
                    source: source.code,
                    target: target.code,
                }
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

/// Check that a boundary flow runs in the direction its variance fixes.
///
/// # Specification
/// - ensures: a covariant boundary flow runs from the source function's part to
///   the target function's part; a contravariant one runs from the target's
///   part to the source's.
/// - fails: `Boundary` naming the position when either endpoint type differs.
/// - panics: none.
///
/// # Errors
/// `FlowError::Boundary`.
///
/// # Adequacy
/// - hypothesis: L3 — one certificate admits at both boundaries between codes
///   whose parts it orients, and its reverse refuses at each, naming it.
/// - witness: `flow_universe::tests::function::directed_funext_forms_and_rides_in_variance_order`
/// - witness: `flow_universe::tests::function::symmetry_refusal_holds_at_a_thunk_code`
#[spec(ensures: |ret| match ret {
    Ok(()) => true,
    Err(FlowError::Boundary(named)) => named == boundary,
    Err(_) => false,
})]
fn boundary(
    arena: &TermArena,
    boundary: Boundary,
    flow: FlowType,
    source_part: ValueTypeId,
    target_part: ValueTypeId,
) -> Result<(), FlowError>
{
    let (from, to) = match boundary.variance() {
        | Variance::Covariant => (source_part, target_part),
        | Variance::Contravariant => (target_part, source_part),
    };
    if convertible_value_types(arena, flow.source, from) == Convertibility::Convertible
        && convertible_value_types(arena, flow.target, to) == Convertibility::Convertible
    {
        Ok(())
    }
    else {
        Err(FlowError::Boundary(boundary))
    }
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
///   paths synthesize through the ordinary checker before endpoint decoding,
///   and a native value whose classifier is in the other family is refused
///   under the family it was tagged with.
/// - fails: `FamilyMismatch` in both coercion directions, by tag or by native
///   classifier; `Typing` for native checking failures; `Path` for a non-path
///   classifier or invalid endpoints; otherwise a Flow formation error.
/// - panics: none.
///
/// # Errors
/// `FamilyMismatch`, `Typing`, `Path`, or an error from `form`.
///
/// # Adequacy
/// - hypothesis: L3 — a valid equivalence fails as Flow, a valid forward
///   certificate fails as Path, and both retain their native classifications; a
///   native session flow tagged as a path and a native session path given as a
///   session flow each refuse by family.
/// - witness: `flow_universe::tests::path_and_flow_never_coerce`
/// - witness: `session::tests::session_flows_persist_and_refuse_by_family`
#[spec(ensures: |ret| match (certificate, expected, &ret) {
    (Certificate::Path(_), Family::Flow, &Err(FlowError::FamilyMismatch { expected: Family::Flow, actual: Family::Path }))
    | (Certificate::Flow(_), Family::Path, &Err(FlowError::FamilyMismatch { expected: Family::Path, actual: Family::Flow }))
    | (Certificate::Path(_), Family::Path, &Ok(CertificateType::Path(_)))
    | (Certificate::Flow(_), Family::Flow, &Ok(CertificateType::Flow(_))) => true,
    (Certificate::Path(_), Family::Path, &Err(ref error)) | (Certificate::Flow(_), Family::Flow, &Err(ref error)) => !matches!(error, &FlowError::FamilyMismatch { expected: named, .. } if named != expected),
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
            if matches!(
                arena.value_type(classifier),
                Some(&gandr_kernel_term::ValueType::FlowUniverse(..))
            ) {
                return Err(FlowError::FamilyMismatch {
                    expected,
                    actual: Family::Flow,
                });
            }
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
///   rejects a source value of the wrong type; a function flow rejects a Bool.
/// - witness: `flow_universe::tests::terminal_ride_and_stay_compute`
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
/// - witness: `flow_universe::tests::function::directed_funext_forms_and_rides_in_variance_order`
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
///   uses CBPV bind in source-to-target order, with no inverse construction. A
///   function introduction lowers to `λf. return (thunk (λa'. domain a' to a. f
///   a to b. codomain b))`: the argument boundary's translator runs before the
///   function and the result boundary's after it.
/// - fails: `UnknownFlow`, `Arena`, `Cycle` or `Budget`; session introductions
///   return `RecordedRunRequired` because no endpoint-value eliminator exists.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — composed injection/fold acts as identity, terminal then
///   injection chooses that injection, a function flow applies its boundaries
///   in variance order, and a formed session flow refuses value lowering rather
///   than manufacturing an endpoint or identity translator.
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
/// - witness: `flow_universe::tests::function::directed_funext_forms_and_rides_in_variance_order`
/// - witness: `flow_universe::rules::tests::session_lowering_requires_a_recorded_run`
#[spec(ensures: |ret| match ret {
    Ok(value) => u64::from(budget) > 0 && match flows.get(root) {
        Ok(&Flow::Forward { translator, .. }) => value == translator,
        Ok(&Flow::Stay(_) | &Flow::Compose { seam: Seam::Sequence, .. } | &Flow::Function { .. }) => matches!(arena.value(value), Some(&gandr_kernel_term::Value::Thunk(_))),
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
            | &Flow::Session(_) => return Err(FlowError::RecordedRunRequired),
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
            | &Flow::Function {
                domain, codomain, ..
            } => {
                if !expanded {
                    pending.push((id, true));
                    pending.push((codomain, false));
                    pending.push((domain, false));
                    continue;
                }
                let domain = *lowered.get(&domain).ok_or(FlowError::UnknownFlow(domain))?;
                let codomain = *lowered
                    .get(&codomain)
                    .ok_or(FlowError::UnknownFlow(codomain))?;
                // Beneath `λa'`, each bind adds one binder: the function `f`
                // sits at index 1 under `λa'` and at index 2 once `a` is bound.
                // The boundary translators are closed and need no shift.
                let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
                let function = arena.value_variable(DeBruijnIndex::from(2_u32));
                let domain = arena.computation_force(domain);
                let domain = arena.computation_application(domain, argument);
                let function = arena.computation_force(function);
                let function = arena.computation_application(function, argument);
                let codomain = arena.computation_force(codomain);
                let codomain = arena.computation_application(codomain, argument);
                let result = arena.computation_bind(function, codomain);
                let body = arena.computation_bind(domain, result);
                let lambda = arena.computation_lambda(body);
                let transported = arena.value_thunk(lambda);
                let returned = arena.computation_return(transported);
                let lambda = arena.computation_lambda(returned);
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
/// - hypothesis: L3 — Stay returns its original input at zero lowering budget,
///   at a first-order and at a function code; forward action, composition and
///   function flows compute their specified outputs.
/// - witness: `flow_universe::tests::terminal_ride_and_stay_compute`
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
/// - witness: `flow_universe::tests::function::stay_at_a_thunk_code_collapses`
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

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn session_lowering_requires_a_recorded_run()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let ty = arena.value_type_session(
            alloc::sync::Arc::new(gandr_kernel_term::session::Graph {
                root: gandr_kernel_term::session::State(0),
                nodes: alloc::vec![gandr_kernel_term::session::Node::End],
            }),
            unit,
        );
        let code = arena.value_quote(ty);
        let proofs = arena.value_unit();
        let classifier = arena.value_type_flow_universe(code, code);
        let simulation = arena.value_session_flow(
            classifier,
            alloc::sync::Arc::new(gandr_kernel_term::session::Evidence {
                pairs: [gandr_kernel_term::session::StatePair {
                    source: gandr_kernel_term::session::State(0),
                    target: gandr_kernel_term::session::State(0),
                }]
                .into(),
                payloads: Vec::new(),
            }),
            proofs,
        );
        let mut flows = Flows::new();
        let flow = flows.push(Flow::Session(simulation)).expect("raw flow");
        assert!(
            matches!(form(&mut arena, &flows, flow, ReplayBudget::DEFAULT), Ok(FlowType { source, target }) if source == ty && target == ty)
        );
        assert!(matches!(
            lower(&mut arena, &flows, flow, ReplayBudget::DEFAULT),
            Err(FlowError::RecordedRunRequired)
        ));
    }
}
