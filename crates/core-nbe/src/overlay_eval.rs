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

use anodized::spec;
use gandr_core_term::CoreArena;

use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainValueId;
use crate::closure::Environment;
use crate::eval::Definitions;
use crate::eval::EvalFault;
use crate::eval::Fuel;
use crate::eval::eval_closed_value;
use crate::eval::eval_comp_within;
#[cfg(doc)]
use crate::eval::eval_value;
use crate::overlay::EraseFault;
use crate::overlay::Overlay;
use crate::overlay::OverlayCompId;
use crate::overlay::OverlayValueId;
use crate::overlay::erase_computation;
use crate::overlay::erase_value;

/// Why an overlay root could not be evaluated.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum OverlayEvalFault
{
    /// Erasure refused the root, in its own vocabulary, and left the core
    /// arena as it found it.
    Erasure(EraseFault),
    /// The machine refused the erased term, in its own vocabulary.
    Evaluation(EvalFault),
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
