//! Boundary orientation, family separation and the directed replay entry.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::Boundary;
use super::Family;
use super::FlowError;
use super::FlowType;
use super::Variance;
use super::coverage::Arrow;
use crate::check::check_closed_value;
use crate::check::synth_closed_value;
use crate::conv::Convertibility;
use crate::conv::convertible_value_types;
use crate::error::KernelError;
use crate::path_universe::Dialogue;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;

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
/// - witness: `flow_universe::rules::tests::a_boundary_flow_agrees_at_both_of_its_ends`
#[spec(ensures: |ret| match ret {
    Ok(()) => true,
    Err(FlowError::Boundary(named)) => named == boundary,
    Err(_) => false,
})]
pub fn boundary(
    arena: &TermArena,
    boundary: Boundary,
    flow: FlowType,
    (source, target): (Arrow, Arrow),
) -> Result<(), FlowError>
{
    let (source_part, target_part) = match boundary {
        Boundary::Domain => (source.domain, target.domain),
        Boundary::Codomain => (source.codomain, target.codomain),
    };
    let (from, to) = match boundary.variance() {
        Variance::Covariant => (source_part, target_part),
        Variance::Contravariant => (target_part, source_part),
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

/// Check a native certificate against its expected family, without coercion.
///
/// # Specification
/// - ensures: the certificate synthesizes through the ordinary closed checker,
///   which replays every certificate it contains — a forward flow's images, a
///   composition's seam, a function flow's boundaries, a `stay`'s endpoints, a
///   session simulation — and its classifier names its family. A universe
///   classifier decodes its endpoints; a flow at the level-zero value universe
///   reads as its `Flow_U` classifier.
/// - fails: `Flow(FamilyMismatch)` when the classifier is in the other family;
///   `Flow(ExpectedFlow)` for a classifier in neither; `Path` for invalid path
///   endpoints; the checker's own refusal otherwise.
/// - panics: none.
///
/// # Errors
/// `KernelError::Flow` naming the family or the flow refusal the checker
/// raised, `KernelError::Path`, `KernelError::Session`, or any other checker
/// refusal.
///
/// # Adequacy
/// - hypothesis: L3 — a valid equivalence fails as Flow, a valid forward
///   certificate fails as Path, and both retain their native classifications; a
///   native session flow given as a path and a native session path given as a
///   flow each refuse by family.
/// - witness: `flow_universe::tests::path_and_flow_never_coerce`
/// - witness: `session::tests::session_flows_persist_and_refuse_by_family`
#[spec(ensures: |ret| match (expected, &ret) {
    (Family::Path, &Ok(CertificateType::Path(_))) | (Family::Flow, &Ok(CertificateType::Flow(_))) => true,
    (_, &Ok(_)) => false,
    (_, &Err(KernelError::Flow(FlowError::FamilyMismatch { expected: named, actual }))) => named == expected && actual != expected,
    (_, &Err(_)) => true,
})]
#[inline]
pub fn form_certificate(
    arena: &mut TermArena,
    certificate: ValueId,
    expected: Family,
    budget: ReplayBudget,
) -> Result<CertificateType, KernelError>
{
    let classifier = synth_closed_value(arena, certificate)?;
    let actual = match arena.value_type(classifier) {
        Some(&(ValueType::PathUniverse(..) | ValueType::Path { .. })) => Family::Path,
        Some(&(ValueType::FlowUniverse(..) | ValueType::Flow { .. })) => Family::Flow,
        Some(_) if expected == Family::Path => Family::Path,
        Some(_) => return Err(KernelError::Flow(FlowError::ExpectedFlow(classifier))),
        None => return Err(KernelError::ArenaFault),
    };
    if actual != expected {
        return Err(KernelError::Flow(FlowError::FamilyMismatch {
            expected,
            actual,
        }));
    }
    match expected {
        Family::Path => {
            let classifier =
                crate::path_universe::endpoints(arena, &crate::env::NO_ENTRIES, classifier, budget)
                    .map_err(KernelError::Path)?;
            Ok(CertificateType::Path(classifier))
        },
        Family::Flow => {
            let classifier =
                super::universe_reading(arena, &crate::env::NO_ENTRIES, classifier, budget)
                    .map_err(KernelError::Flow)?;
            Ok(CertificateType::Flow(classifier))
        },
    }
}

/// Check a closed ride and an expected result, then replay their conversion.
///
/// # Specification
/// - ensures: the ride synthesizes through the ordinary closed checker — its
///   flow formed and replayed, its motive through the covariance gate, its
///   value at the motive's source instance — and the expected result checks at
///   the ride's type. The kernel's own reading reduces the ride by the module's
///   table, and the supplied dialogue is replayed as a derivation of the two
///   sides' convertibility. The entry watermark is restored on success and
///   every failure.
/// - fails: `Flow(RecordedRunRequired)` for a ride along a session simulation,
///   which relates recorded runs rather than endpoint values; the checker's
///   refusal otherwise. A bad dialogue returns the ordinary declined or
///   negative replay verdict, never positive by default.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — terminal transport at both constructors is Convertible, a
///   false output claim does not certify, a symmetric motive refuses by name, a
///   ride along a session simulation refuses as a recorded run, and failure
///   preserves the arena.
/// - witness: `flow_universe::tests::stay_and_forward_admit_and_ride`
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
/// - witness: `flow_universe::tests::symmetry_motive_is_refused_at_ride`
/// - witness: `session::tests::session_flows_persist_and_refuse_by_family`
#[spec(captures: before = arena.watermark(), ensures: arena.watermark() == before)]
#[inline]
pub fn replay_ride(
    arena: &mut TermArena,
    ride: ComputationId,
    expected: ComputationId,
    claim: EngineClaim,
    dialogue: &Dialogue,
    budget: ReplayBudget,
) -> Result<KernelVerdict, KernelError>
{
    let watermark = arena.watermark();
    let result = replay_checked(arena, ride, expected, claim, dialogue, budget);
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
#[spec(ensures: |ret| u64::from(budget) != 0 || !matches!(ret, Ok(KernelVerdict::Convertible)))]
fn replay_checked(
    arena: &mut TermArena,
    ride: ComputationId,
    expected: ComputationId,
    claim: EngineClaim,
    dialogue: &Dialogue,
    budget: ReplayBudget,
) -> Result<KernelVerdict, KernelError>
{
    let suspended = arena.value_thunk(ride);
    let classifier = synth_closed_value(arena, suspended)?;
    if let Some(&Computation::Ride { flow, .. }) = arena.computation(ride)
        && matches!(arena.value(flow), Some(&Value::SessionFlow { .. }))
    {
        return Err(KernelError::Flow(FlowError::RecordedRunRequired));
    }
    let result = arena.value_thunk(expected);
    check_closed_value(arena, result, classifier)?;
    Ok(crate::replay::replay(
        arena,
        &Unfoldings::new(Vec::new()),
        ReplaySides::Computations(ride, expected),
        claim,
        dialogue.0.iter().copied(),
        budget,
    ))
}

/// The classifier a function flow's boundary must carry, given the flow's
/// two function codes.
///
/// # Specification
/// - ensures: the boundary's reading as a universe flow, oriented by
///   [`boundary`].
/// - fails: `Boundary` naming the position for a misdirected or mismatched
///   boundary; `FamilyMismatch` or `ExpectedFlow` for a classifier that is no
///   flow; a code-walk refusal.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a reversed domain boundary refuses as `Boundary(Domain)`
///   at admission and at readmission.
/// - witness: `flow_universe::tests::function::symmetry_refusal_holds_at_a_thunk_code`
#[spec(ensures: |ret| !matches!(ret, Err(FlowError::Boundary(named)) if named != position))]
pub fn oriented(
    arena: &mut TermArena,
    position: Boundary,
    arrows: (Arrow, Arrow),
    classifier: ValueTypeId,
    budget: ReplayBudget,
) -> Result<(), FlowError>
{
    let flow = super::universe_reading(arena, &crate::env::NO_ENTRIES, classifier, budget)?;
    boundary(arena, position, flow, arrows)
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::TermArena;

    use super::Arrow;
    use super::Boundary;
    use super::FlowError;
    use super::FlowType;
    use super::boundary;

    #[test]
    fn a_boundary_flow_agrees_at_both_of_its_ends()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let arrow = |code, codomain| Arrow {
            code,
            domain: unit,
            codomain,
        };
        let arrows = (arrow(unit, unit), arrow(integer, integer));
        let flow = |source, target| FlowType { source, target };
        assert_eq!(
            boundary(&arena, Boundary::Codomain, flow(unit, integer), arrows),
            Ok(())
        );
        for (source, target, what) in [
            (unit, unit, "the target end differs"),
            (integer, integer, "the source end differs"),
        ] {
            assert_eq!(
                boundary(&arena, Boundary::Codomain, flow(source, target), arrows),
                Err(FlowError::Boundary(Boundary::Codomain)),
                "{what}"
            );
        }
    }
}
