//! Evaluation of an overlay root.
//!
//! # The reference is erasure, then the unshared machine
//!
//! [`eval_overlay_value`] and [`eval_overlay_computation`] erase a root into
//! the core arena and run the unshared machine over the erasure in the empty
//! environment. That composition is the pipeline every sharing stance is
//! compared against, so it is pinned first: the overlay evaluator mints into
//! the core and domain arenas exactly what [`erase_value`] followed by
//! [`eval_value`] mints, node for node, and reports the same result and the
//! same unspent fuel.
//!
//! # A sharing stance evaluates its own duplicate
//!
//! [`eval_overlay_shared`] duplicates the root under the policy, erases the
//! duplicate keeping each share's erased leg, and runs the machine over the
//! erasure with those legs handed over: the first evaluation of a leg in one
//! configuration — one binding at each of its free indices — is remembered,
//! and every later occurrence read in that configuration takes it. Under the
//! spinal stance an abstraction's ribs are legs of their own, so a rib is
//! evaluated once per configuration however many times the abstraction is
//! applied. The duplicate is scratch: the overlay is truncated back to its
//! entry watermark whatever the outcome.

use alloc::collections::BTreeMap;

use anodized::spec;
use gandr_core_term::CoreArena;

use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainValueId;
use crate::closure::Environment;
use crate::domain::Glued;
use crate::duplicate::DuplicationFault;
use crate::duplicate::duplicate;
use crate::eval::Definitions;
use crate::eval::EvalFault;
use crate::eval::Fuel;
use crate::eval::eval_closed_value;
use crate::eval::eval_comp_within;
use crate::eval::eval_sharing;
#[cfg(doc)]
use crate::eval::eval_value;
use crate::free::CoreTerm;
use crate::free::Free;
use crate::free::FreeFault;
use crate::free::FreeIndices;
use crate::overlay::CoreId;
use crate::overlay::EraseFault;
use crate::overlay::Overlay;
use crate::overlay::OverlayCompId;
use crate::overlay::OverlayId;
use crate::overlay::OverlayValueId;
use crate::overlay::erase_computation;
use crate::overlay::erase_value;
use crate::overlay::erase_with_legs;
use crate::policy::DuplicationPolicy;

/// Why an overlay root could not be evaluated.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum OverlayEvalFault
{
    /// Erasure refused the root, in its own vocabulary, and left the core
    /// arena as it found it.
    Erasure(EraseFault),
    /// The machine refused the erased term, in its own vocabulary.
    Evaluation(EvalFault),
    /// The duplication walk refused the root, in its own vocabulary, before
    /// anything was erased.
    Duplication(DuplicationFault),
}

/// Evaluate a value overlay root: erase it, then run the unshared machine over
/// the erasure.
///
/// # Specification
/// - requires: `core` is the arena the overlay's opaque nodes name, and the
///   term `root` stands for is closed.
/// - ensures: on success the value the erasure of `root` evaluates to, paired
///   with the fuel left over — one unit per task the machine popped; `core`
///   then holds the erasure and `domain` what the evaluation minted, node for
///   node what [`erase_value`] followed by [`eval_value`] mint.
/// - provides: the overlay evaluator's reference: the erase-then-evaluate
///   pipeline every sharing stance is compared against. The clause states that
///   the result resolves in `domain` and that the remainder does not exceed
///   `fuel`; the byte-for-byte agreement with the composition is a relation
///   between two runs, and the witnesses below carry it.
/// - fails: [`OverlayEvalFault::Erasure`] with erasure's refusal, `core` left
///   at its entry watermark; [`OverlayEvalFault::Evaluation`] with the
///   machine's refusal, the erasure kept.
/// - panics: none.
///
/// # Errors
/// - [`OverlayEvalFault::Erasure`] — the root does not erase.
/// - [`OverlayEvalFault::Evaluation`] — the erased term does not evaluate.
///
/// # Adequacy
/// - hypothesis: L2 — the oracle is the composition of erasure and the unshared
///   machine run by the test, sharing no code path with this entry beyond the
///   two functions it composes; the core arena, the domain arena, the result
///   and the remainder are compared exactly over the deep value chain, run
///   through evaluation and through readback.
/// - witness:
///   `deep_evaluation::deep_evaluation::erase_and_clone_overlay_evaluation_is_the_erased_pipeline`
/// - witness:
///   `deep_readback::deep_readback::erase_and_clone_overlay_evaluation_is_the_erased_pipeline`
#[inline]
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|pair| {
        domain.value(pair.0).is_some() && u32::from(pair.1) <= u32::from(fuel)
    }))]
pub fn eval_overlay_value(
    overlay: &Overlay,
    core: &mut CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    root: OverlayValueId,
) -> Result<(DomainValueId, Fuel), OverlayEvalFault>
{
    let erased = erase_value(overlay, root, core).map_err(OverlayEvalFault::Erasure)?;
    eval_closed_value(core, domain, definitions, fuel, erased).map_err(OverlayEvalFault::Evaluation)
}

/// Evaluate a computation overlay root to weak head: erase it, then run the
/// unshared machine over the erasure.
///
/// # Specification
/// - requires: `core` is the arena the overlay's opaque nodes name, and the
///   term `root` stands for is closed.
/// - ensures: on success the weak head the erasure of `root` evaluates to,
///   paired with the fuel left over; `core` and `domain` hold node for node
///   what erasing `root` and evaluating the erasure in the empty environment
///   mint.
/// - provides: the computation half of the reference.
/// - fails: as [`eval_overlay_value`] fails.
/// - panics: none.
///
/// # Errors
/// - [`OverlayEvalFault::Erasure`] — the root does not erase.
/// - [`OverlayEvalFault::Evaluation`] — the erased term does not evaluate.
///
/// # Adequacy
/// - hypothesis: L2 — as for [`eval_overlay_value`], over the deep curried
///   application, the deep chain of binds over an opaque base, and the chain of
///   suspensions run through readback.
/// - witness:
///   `deep_evaluation::deep_evaluation::erase_and_clone_overlay_evaluation_is_the_erased_pipeline`
/// - witness:
///   `deep_readback::deep_readback::erase_and_clone_overlay_evaluation_is_the_erased_pipeline`
#[inline]
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|pair| {
        domain.computation(pair.0).is_some() && u32::from(pair.1) <= u32::from(fuel)
    }))]
pub fn eval_overlay_computation(
    overlay: &Overlay,
    core: &mut CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    root: OverlayCompId,
) -> Result<(DomainCompId, Fuel), OverlayEvalFault>
{
    let erased = erase_computation(overlay, root, core).map_err(OverlayEvalFault::Erasure)?;
    eval_comp_within(core, domain, definitions, fuel, erased, Environment::new())
        .map_err(OverlayEvalFault::Evaluation)
}

/// Evaluate an overlay root under a sharing policy: duplicate it, erase the
/// duplicate keeping each share's leg, and run the machine sharing those legs
/// by configuration.
///
/// # Specification
/// - requires: `core` is the arena the overlay's opaque nodes name, and the
///   term `root` stands for is closed and of an evaluation family.
/// - ensures: on success the weak head of the term `root` stands for, in its
///   polarity, paired with the fuel left over — one unit per task the machine
///   popped, a leg met again in a configuration already evaluated costing the
///   one step that popped it; `core` holds the duplicate's erasure, `domain`
///   what the evaluation minted, and the overlay is at its entry watermark
///   whatever the outcome.
/// - provides: the sharing stance's evaluator, which the certifying path
///   installs; the reference stance evaluates through [`eval_overlay_value`]
///   and [`eval_overlay_computation`] instead. The clause states the overlay's
///   restoration and the remainder's bound; that the result reads back as the
///   reference's is a relation between two runs, and the witnesses below carry
///   it.
/// - fails: [`OverlayEvalFault::Duplication`] with the walk's refusal;
///   [`OverlayEvalFault::Erasure`] with erasure's, `core` left at its entry
///   watermark; [`OverlayEvalFault::Evaluation`] with the machine's, the
///   erasure kept, [`EvalFault::DanglingTerm`] naming an erased leg that does
///   not resolve.
/// - panics: none.
///
/// # Errors
/// - [`OverlayEvalFault::Duplication`] — the root does not duplicate.
/// - [`OverlayEvalFault::Erasure`] — the duplicate does not erase.
/// - [`OverlayEvalFault::Evaluation`] — the erasure does not evaluate.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the walk's treatments and the
///   machine's configuration key, separated by a rib shared across two
///   applications, a subterm under an inner binder applied to one value at both
///   copies, and a leg read under two different binders, each read off the step
///   count against the reference run with the results read back equal.
/// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
/// - witness:
///   `full_laziness::full_laziness::a_spinal_duplicate_shares_what_full_laziness_copies`
/// - witness:
///   `full_laziness::full_laziness::an_open_configuration_is_evaluated_per_occurrence`
#[spec(
    captures: [entry = overlay.watermark()],
    ensures: |ret| overlay.watermark() == entry
        && (ret.is_err() || ret.as_ref().is_ok_and(|pair| u32::from(pair.1) <= u32::from(fuel))),
)]
pub fn eval_overlay_shared(
    overlay: &mut Overlay,
    core: &mut CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    policy: DuplicationPolicy,
    root: OverlayId,
) -> Result<(Glued, Fuel), OverlayEvalFault>
{
    let mark = overlay.watermark();
    let erased = duplicate_and_erase(overlay, core, policy, root);
    overlay.truncate_to(mark);
    let (term, legs) = erased?;
    eval_sharing(core, domain, definitions, fuel, term, legs).map_err(OverlayEvalFault::Evaluation)
}

/// Duplicate `root` under `policy`, erase the duplicate keeping each share's
/// leg, and read each leg's free indices.
///
/// # Specification
/// - requires: as [`eval_overlay_shared`].
/// - ensures: the erased duplicate and its legs, each with its free indices.
/// - provides: the half of [`eval_overlay_shared`] the overlay is restored
///   after.
/// - fails: as [`eval_overlay_shared`] fails, short of evaluation.
/// - panics: none.
///
/// # Errors
/// - [`OverlayEvalFault::Duplication`] — the root does not duplicate.
/// - [`OverlayEvalFault::Erasure`] — the duplicate does not erase.
/// - [`OverlayEvalFault::Evaluation`] — an erased leg does not resolve.
fn duplicate_and_erase(
    overlay: &mut Overlay,
    core: &mut CoreArena,
    policy: DuplicationPolicy,
    root: OverlayId,
) -> Result<(CoreTerm, BTreeMap<CoreTerm, Free>), OverlayEvalFault>
{
    let rebuilt = duplicate(overlay, core, policy, root).map_err(OverlayEvalFault::Duplication)?;
    let erased = erase_with_legs(overlay, rebuilt, core).map_err(OverlayEvalFault::Erasure)?;
    let term = core_term(erased.root())?;
    let mut free = FreeIndices::default();
    let mut legs = BTreeMap::new();
    for &leg in erased.legs() {
        let leg = core_term(leg)?;
        let answered = free.of(core, leg).map_err(|fault| {
            OverlayEvalFault::Evaluation(match fault {
                | FreeFault::Dangling => EvalFault::DanglingTerm,
                | FreeFault::MachineInvariant => EvalFault::MachineInvariant,
            })
        })?;
        legs.insert(leg, answered.clone());
    }
    Ok((term, legs))
}

/// The core term an erased evaluation node is.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the value or computation `erased` names.
/// - provides: the read from erasure's ids to the machine's.
/// - fails: [`OverlayEvalFault::Evaluation`] with
///   [`EvalFault::MachineInvariant`] for a type, which no evaluation root
///   erases to.
/// - panics: none.
///
/// # Errors
/// - [`OverlayEvalFault::Evaluation`] — `erased` is a type.
fn core_term(erased: CoreId) -> Result<CoreTerm, OverlayEvalFault>
{
    match erased {
        | CoreId::Value(id) => Ok(CoreTerm::Value(id)),
        | CoreId::Computation(id) => Ok(CoreTerm::Computation(id)),
        | CoreId::ValueType(_) | CoreId::CompType(_) => {
            Err(OverlayEvalFault::Evaluation(EvalFault::MachineInvariant))
        },
    }
}
