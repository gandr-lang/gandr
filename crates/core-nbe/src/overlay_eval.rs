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
///   through evaluation and through readback. Erasure refusals preserve both
///   arenas, while exhausted evaluation keeps its completed erasure; dropping
///   rollback or erasing after evaluation changes those boundaries.
/// - witness:
///   `deep_evaluation::deep_evaluation::erase_and_clone_overlay_evaluation_is_the_erased_pipeline`
/// - witness:
///   `deep_readback::deep_readback::erase_and_clone_overlay_evaluation_is_the_erased_pipeline`
/// - witness: `overlay_eval::tests::refusals_preserve_the_erasure_and_evaluation_boundaries`
#[inline]
#[spec(
    captures: [core_entry = core.watermark(), domain_entry = domain.watermark()],
    ensures: |ret| match ret {
        Ok((result, remaining)) => domain.value(result).is_some() && u32::from(remaining) <= u32::from(fuel),
        Err(OverlayEvalFault::Erasure(_)) => core.watermark() == core_entry && domain.watermark() == domain_entry,
        Err(OverlayEvalFault::Evaluation(_)) => true,
        Err(OverlayEvalFault::Duplication(_)) => false,
    },
)]
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
///   suspensions run through readback. The refusal witness separates erasure
///   rollback from evaluation failure after the erased computation is retained.
/// - witness:
///   `deep_evaluation::deep_evaluation::erase_and_clone_overlay_evaluation_is_the_erased_pipeline`
/// - witness:
///   `deep_readback::deep_readback::erase_and_clone_overlay_evaluation_is_the_erased_pipeline`
/// - witness: `overlay_eval::tests::refusals_preserve_the_erasure_and_evaluation_boundaries`
#[inline]
#[spec(
    captures: [core_entry = core.watermark(), domain_entry = domain.watermark()],
    ensures: |ret| match ret {
        Ok((result, remaining)) => domain.computation(result).is_some() && u32::from(remaining) <= u32::from(fuel),
        Err(OverlayEvalFault::Erasure(_)) => core.watermark() == core_entry && domain.watermark() == domain_entry,
        Err(OverlayEvalFault::Evaluation(_)) => true,
        Err(OverlayEvalFault::Duplication(_)) => false,
    },
)]
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
///   count against the reference run with the results read back equal. Removing
///   scratch restoration changes the overlay after either a refused duplication
///   or an exhausted evaluation.
/// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
/// - witness:
///   `full_laziness::full_laziness::a_spinal_duplicate_shares_what_full_laziness_copies`
/// - witness:
///   `full_laziness::full_laziness::an_open_configuration_is_evaluated_per_occurrence`
/// - witness: `overlay_eval::tests::refusals_preserve_the_erasure_and_evaluation_boundaries`
/// - witness: `overlay_eval::tests::type_roots_are_refused_before_evaluation`
#[spec(
    captures: [entry = overlay.watermark()],
    ensures: |ret| overlay.watermark() == entry && ret.as_ref().map_or(true, |&(glued, remaining)|
        u32::from(remaining) <= u32::from(fuel) && match (root, glued) {
            (OverlayId::Value(_), Glued::Value(value)) => domain.value(value).is_some(),
            (OverlayId::Computation(_), Glued::Computation(comp)) => domain.computation(comp).is_some(),
            _ => false,
        }),
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
/// # Adequacy
/// - hypothesis: L2 — configuration-sensitive legs are evaluated once per
///   matching environment and read back as the unshared result; assigning a leg
///   another leg’s free indices changes sharing across binders. The predicate
///   checks each retained leg against the free-index analysis, while the
///   end-to-end witnesses separate their environments.
/// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
/// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_what_full_laziness_copies`
/// - witness: `full_laziness::full_laziness::an_open_configuration_is_evaluated_per_occurrence`
///
/// # Errors
/// - [`OverlayEvalFault::Duplication`] — the root does not duplicate.
/// - [`OverlayEvalFault::Erasure`] — the duplicate does not erase.
/// - [`OverlayEvalFault::Evaluation`] — an erased leg does not resolve.
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(term, ref legs)| {
    let matches_root = match (root, term) {
        (OverlayId::Value(_), CoreTerm::Value(value)) => core.value(value).is_some(),
        (OverlayId::Computation(_), CoreTerm::Computation(comp)) => core.computation(comp).is_some(),
        _ => false,
    };
    let mut free = FreeIndices::default();
    matches_root && legs.iter().all(|(&leg, held)| free.of(core, leg).is_ok_and(|answer| answer == held))
}))]
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
/// # Adequacy
/// - hypothesis: L3 — evaluation retains value and computation polarity, but
///   both type families refuse before evaluation. Accepting either type changes
///   the refusal, while exchanging the two evaluation families changes the
///   independently evaluated result.
/// - witness: `overlay_eval::tests::type_roots_are_refused_before_evaluation`
/// - witness: `deep_evaluation::deep_evaluation::erase_and_clone_overlay_evaluation_is_the_erased_pipeline`
///
/// # Errors
/// - [`OverlayEvalFault::Evaluation`] — `erased` is a type.
#[spec(ensures: |ret| match erased {
    CoreId::Value(value) => ret == Ok(CoreTerm::Value(value)),
    CoreId::Computation(comp) => ret == Ok(CoreTerm::Computation(comp)),
    CoreId::ValueType(_) | CoreId::CompType(_) => ret == Err(OverlayEvalFault::Evaluation(EvalFault::MachineInvariant)),
})]
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

#[cfg(test)]
mod tests
{
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;

    use super::Definitions;
    use super::DomainArena;
    use super::DuplicationPolicy;
    use super::EvalFault;
    use super::Fuel;
    use super::Overlay;
    use super::OverlayEvalFault;
    use super::OverlayId;
    use super::eval_overlay_computation;
    use super::eval_overlay_shared;
    use super::eval_overlay_value;
    use crate::CompGraft;
    use crate::CompNode;
    use crate::CompTypeGraft;
    use crate::CompTypeNode;
    use crate::LoweredChain;
    use crate::ValueGraft;
    use crate::ValueNode;
    use crate::ValueTypeGraft;
    use crate::ValueTypeNode;

    #[test]
    fn refusals_preserve_the_erasure_and_evaluation_boundaries()
    {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut overlay = Overlay::new();
        let floor = overlay.watermark();
        let value = overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Unit))
            .expect("the unit is closed");
        let comp = overlay
            .mint_computation(CompNode::Grafted(CompGraft::Return(value)))
            .expect("the child lives");
        let preserved = overlay.clone();
        let mut value_core = CoreArena::new();
        let unit = value_core.value_unit();
        let mut comp_core = value_core.clone();
        let _returned = comp_core.computation_return(unit);
        let mut domain = DomainArena::new();
        let _existing = domain.value_unit(crate::TermFace::Reduced);
        let domain_before = domain.clone();
        let mut core = CoreArena::new();
        assert_eq!(
            Err(OverlayEvalFault::Evaluation(EvalFault::OutOfFuel)),
            eval_overlay_value(
                &overlay,
                &mut core,
                &mut domain,
                definitions,
                Fuel::from(0_u32),
                value
            )
        );
        assert_eq!(
            value_core, core,
            "evaluation refusal keeps the erased value"
        );
        assert_eq!(domain_before, domain);
        let mut core = CoreArena::new();
        assert_eq!(
            Err(OverlayEvalFault::Evaluation(EvalFault::OutOfFuel)),
            eval_overlay_computation(
                &overlay,
                &mut core,
                &mut domain,
                definitions,
                Fuel::from(0_u32),
                comp
            )
        );
        assert_eq!(
            comp_core, core,
            "evaluation refusal keeps the erased computation"
        );
        assert_eq!(domain_before, domain);
        for (root, expected) in [
            (OverlayId::Value(value), &value_core),
            (OverlayId::Computation(comp), &comp_core),
        ] {
            let mut core = CoreArena::new();
            assert_eq!(
                Err(OverlayEvalFault::Evaluation(EvalFault::OutOfFuel)),
                eval_overlay_shared(
                    &mut overlay,
                    &mut core,
                    &mut domain,
                    definitions,
                    Fuel::from(0_u32),
                    DuplicationPolicy::default(),
                    root
                )
            );
            assert_eq!(*expected, core);
            assert_eq!(domain_before, domain);
            assert_eq!(
                preserved, overlay,
                "the duplicate is scratch even when evaluation fails"
            );
        }
        overlay.truncate_to(floor);
        let missing = overlay.clone();
        let mut core = comp_core.clone();
        assert!(matches!(
            eval_overlay_value(
                &overlay,
                &mut core,
                &mut domain,
                definitions,
                Fuel::from(20_u32),
                value
            ),
            Err(OverlayEvalFault::Erasure(_))
        ));
        assert_eq!(comp_core, core);
        assert_eq!(domain_before, domain);
        assert!(matches!(
            eval_overlay_computation(
                &overlay,
                &mut core,
                &mut domain,
                definitions,
                Fuel::from(20_u32),
                comp
            ),
            Err(OverlayEvalFault::Erasure(_))
        ));
        assert_eq!(comp_core, core);
        assert_eq!(domain_before, domain);
        for root in [OverlayId::Value(value), OverlayId::Computation(comp)] {
            assert!(matches!(
                eval_overlay_shared(
                    &mut overlay,
                    &mut core,
                    &mut domain,
                    definitions,
                    Fuel::from(20_u32),
                    DuplicationPolicy::default(),
                    root
                ),
                Err(OverlayEvalFault::Duplication(_))
            ));
            assert_eq!(comp_core, core);
            assert_eq!(domain_before, domain);
            assert_eq!(missing, overlay);
        }
    }

    #[test]
    fn type_roots_are_refused_before_evaluation()
    {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut overlay = Overlay::new();
        let value_type = overlay
            .mint_value_type(ValueTypeNode::Grafted(ValueTypeGraft::Unit))
            .expect("the unit type is closed");
        let comp_type = overlay
            .mint_comp_type(CompTypeNode::Grafted(CompTypeGraft::Returner(value_type)))
            .expect("the unit child lives");
        let original = overlay.clone();
        let mut value_core = CoreArena::new();
        let unit = value_core.value_type_unit();
        let mut comp_core = value_core.clone();
        let returner = comp_core.comp_type_returner(unit);
        for erased in [
            super::CoreId::ValueType(unit),
            super::CoreId::CompType(returner),
        ] {
            assert_eq!(
                Err(OverlayEvalFault::Evaluation(EvalFault::MachineInvariant)),
                super::core_term(erased)
            );
        }
        for root in [
            OverlayId::ValueType(value_type),
            OverlayId::CompType(comp_type),
        ] {
            let mut core = CoreArena::new();
            let mut domain = DomainArena::new();
            let empty = domain.clone();
            assert_eq!(
                Err(OverlayEvalFault::Duplication(
                    super::DuplicationFault::MachineInvariant
                )),
                eval_overlay_shared(
                    &mut overlay,
                    &mut core,
                    &mut domain,
                    definitions,
                    Fuel::from(20_u32),
                    DuplicationPolicy::default(),
                    root
                )
            );
            assert_eq!(
                CoreArena::new(),
                core,
                "a type is refused before erasure or evaluation"
            );
            assert_eq!(empty, domain);
            assert_eq!(original, overlay, "the refused root leaves no duplicate");
        }
    }
}
