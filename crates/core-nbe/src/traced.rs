//! The duplication stance installed on the certifying path.
//!
//! # The finer stance installs only bound to a recording sink
//!
//! [`TracedDuplication::install`] is the one place the spinal stance installs.
//! It takes the trace sink the conversions decided under the stance record
//! into, and refuses the spinal stance with [`PolicyRefusal::Untraced`] when
//! that sink retains nothing, which [`TraceSink::ACTIVITY`] states at compile
//! time. The installation then owns every duplication, evaluation and
//! conversion run under the stance, and the policy it holds never leaves it,
//! so a verdict over a domain value the spinal stance shaped carries the
//! derivation the kernel replays by construction rather than by a caller's
//! care.
//!
//! The kernel replays a derivation over the original core terms, sequentially
//! and sharing nothing. A shared evaluation that answered differently from the
//! unshared one surfaces there as a refused trace, never as a verdict the
//! kernel accepted. The erase-and-clone stance installs here with any sink,
//! and evaluates through the reference pipeline.

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_conversion_trace::SinkActivity;
use gandr_kernel_conversion_trace::TraceSink;

use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainValueId;
use crate::conv::ConversionFault;
use crate::domain::Glued;
use crate::duplicate::DuplicationFault;
use crate::duplicate::duplicate_computation;
use crate::duplicate::duplicate_value;
use crate::eval::Definitions;
use crate::eval::EvalFault;
use crate::eval::Fuel;
use crate::machine::MachineReport;
use crate::machine::MachineSettings;
use crate::machine::Problem;
use crate::machine::ProcessId;
use crate::machine::TraceNode;
use crate::machine::decide;
use crate::overlay::Overlay;
use crate::overlay::OverlayCompId;
use crate::overlay::OverlayId;
use crate::overlay::OverlayValueId;
use crate::overlay_eval::OverlayEvalFault;
use crate::overlay_eval::eval_overlay_computation;
use crate::overlay_eval::eval_overlay_shared;
use crate::overlay_eval::eval_overlay_value;
use crate::policy::DuplicationPolicy;
use crate::policy::DuplicationStance;
use crate::policy::PolicyRefusal;
use crate::resharing::GoalSupport;

/// A duplication stance installed bound to the trace sink every conversion
/// decided under it records into.
#[derive(Debug)]
pub struct TracedDuplication<'sink, S>
{
    /// The installed policy, which never leaves this value.
    policy: DuplicationPolicy,
    /// The sink every conversion decided under the policy records into.
    sink: &'sink mut S,
}

impl<'sink, S> TracedDuplication<'sink, S>
where
    S: TraceSink<TraceNode>,
{
    /// Install `stance` bound to `sink`.
    ///
    /// # Specification
    /// - requires: nothing — every stance and every sink is admissible input.
    /// - ensures: on success an installation at `stance` holding `sink`; the
    ///   erase-and-clone stance installs with any sink, the spinal stance only
    ///   with a sink that retains every decision.
    /// - provides: the certifying gate: the one route by which a sharing stance
    ///   reaches an evaluation, and only together with the sink its verdicts
    ///   are recorded into.
    /// - fails: [`PolicyRefusal::Untraced`] for the spinal stance bound to a
    ///   sink that retains nothing, naming the stance it refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PolicyRefusal::Untraced`] — the spinal stance needs a sink that
    ///   records, and this one discards.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the stance against the sink's
    ///   activity, separated by all four pairings, each asserted by variant,
    ///   with the refusal asserted to name the stance and the sinkless
    ///   installation still refusing the spinal stance.
    /// - witness: `traced::tests::the_spinal_stance_installs_only_bound_to_a_recording_sink`
    #[inline]
    #[spec(ensures: |ret| match (stance, S::ACTIVITY) {
        | (DuplicationStance::Spinal, SinkActivity::Inactive) => {
            matches!(ret, Err(PolicyRefusal::Untraced { stance: refused }) if refused == stance)
        },
        | (DuplicationStance::EraseAndClone, _) | (DuplicationStance::Spinal, SinkActivity::Active) => {
            ret.as_ref().is_ok_and(|installed| installed.stance() == stance)
        },
    })]
    pub fn install(
        stance: DuplicationStance,
        sink: &'sink mut S,
    ) -> Result<Self, PolicyRefusal>
    {
        match (stance, S::ACTIVITY) {
            | (DuplicationStance::Spinal, SinkActivity::Inactive) => {
                Err(PolicyRefusal::Untraced { stance })
            },
            | (DuplicationStance::EraseAndClone, _)
            | (DuplicationStance::Spinal, SinkActivity::Active) => Ok(Self {
                policy: DuplicationPolicy::bound_to_trace(stance),
                sink,
            }),
        }
    }

    /// The installed stance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn stance(&self) -> DuplicationStance
    {
        self.policy.stance()
    }

    /// Duplicate a value overlay root under the installed stance.
    ///
    /// # Specification
    /// - requires: as [`duplicate_value`].
    /// - ensures: as [`duplicate_value`] under the installed policy.
    /// - provides: the duplication entry for an installed stance.
    /// - fails: as [`duplicate_value`] fails.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`duplicate_value`].
    ///
    /// # Adequacy
    /// - hypothesis: L1 — as [`duplicate_value`], whose property runs through
    ///   this entry under both stances.
    /// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
    #[inline]
    pub fn duplicate_value(
        &self,
        overlay: &mut Overlay,
        core: &CoreArena,
        root: OverlayValueId,
    ) -> Result<OverlayValueId, DuplicationFault>
    {
        duplicate_value(overlay, core, self.policy, root)
    }

    /// Duplicate a computation overlay root under the installed stance.
    ///
    /// # Specification
    /// - requires: as [`duplicate_computation`].
    /// - ensures: as [`duplicate_computation`] under the installed policy.
    /// - provides: the computation half of the duplication entry for an
    ///   installed stance.
    /// - fails: as [`duplicate_computation`] fails.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`duplicate_computation`].
    ///
    /// # Adequacy
    /// - hypothesis: L1 — as [`duplicate_computation`], whose property runs
    ///   through this entry under both stances.
    /// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
    #[inline]
    pub fn duplicate_computation(
        &self,
        overlay: &mut Overlay,
        core: &CoreArena,
        root: OverlayCompId,
    ) -> Result<OverlayCompId, DuplicationFault>
    {
        duplicate_computation(overlay, core, self.policy, root)
    }

    /// Evaluate a value overlay root under the installed stance.
    ///
    /// # Specification
    /// - requires: `core` is the arena the overlay's opaque nodes name, and the
    ///   term `root` stands for is closed.
    /// - ensures: under the erase-and-clone stance, exactly
    ///   [`eval_overlay_value`]; under the spinal stance,
    ///   [`eval_overlay_shared`] over the value root, whose ribs are evaluated
    ///   once per configuration. The overlay is at its entry watermark whatever
    ///   the outcome.
    /// - provides: the overlay evaluator for an installed stance.
    /// - fails: as [`eval_overlay_shared`] fails, and as [`eval_overlay_value`]
    ///   fails under the reference stance.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`OverlayEvalFault::Duplication`] — the root does not duplicate.
    /// - [`OverlayEvalFault::Erasure`] — the root or its duplicate does not
    ///   erase.
    /// - [`OverlayEvalFault::Evaluation`] — the erasure does not evaluate.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the oracle is the reference pipeline, and the result
    ///   of each stance's run is read back and compared with it as a tree over
    ///   the deep value chain.
    /// - witness:
    ///   `deep_evaluation::deep_evaluation::a_spinal_value_chain_evaluates_as_the_erased_one`
    /// - witness:
    ///   `deep_readback::deep_readback::a_spinal_value_chain_reads_back_as_the_erased_one`
    #[inline]
    #[spec(
        captures: [entry = overlay.watermark()],
        ensures: |ret| overlay.watermark() == entry
            && (ret.is_err() || ret.as_ref().is_ok_and(|pair| u32::from(pair.1) <= u32::from(fuel))),
    )]
    pub fn eval_overlay_value(
        &self,
        overlay: &mut Overlay,
        core: &mut CoreArena,
        domain: &mut DomainArena,
        definitions: Definitions<'_>,
        fuel: Fuel,
        root: OverlayValueId,
    ) -> Result<(DomainValueId, Fuel), OverlayEvalFault>
    {
        match self.policy.stance() {
            | DuplicationStance::EraseAndClone => {
                eval_overlay_value(overlay, core, domain, definitions, fuel, root)
            },
            | DuplicationStance::Spinal => {
                let (produced, left) = eval_overlay_shared(
                    overlay,
                    core,
                    domain,
                    definitions,
                    fuel,
                    self.policy,
                    OverlayId::Value(root),
                )?;
                match produced {
                    | Glued::Value(value) => Ok((value, left)),
                    | Glued::Computation(_) => {
                        Err(OverlayEvalFault::Evaluation(EvalFault::MachineInvariant))
                    },
                }
            },
        }
    }

    /// Evaluate a computation overlay root to weak head under the installed
    /// stance.
    ///
    /// # Specification
    /// - requires: as [`TracedDuplication::eval_overlay_value`].
    /// - ensures: as [`TracedDuplication::eval_overlay_value`], for a
    ///   computation root and [`eval_overlay_computation`].
    /// - provides: the computation half of the overlay evaluator for an
    ///   installed stance.
    /// - fails: as [`TracedDuplication::eval_overlay_value`] fails.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`TracedDuplication::eval_overlay_value`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`TracedDuplication::eval_overlay_value`], over
    ///   the deep curried application and bind chain, and the suspension chain
    ///   run through readback; L3 for the sharing, read off the step count.
    /// - witness:
    ///   `deep_evaluation::deep_evaluation::a_spinal_curried_application_evaluates_as_the_erased_one`
    /// - witness:
    ///   `deep_evaluation::deep_evaluation::a_spinal_bind_chain_evaluates_as_the_erased_one`
    /// - witness:
    ///   `deep_readback::deep_readback::a_spinal_suspension_chain_reads_back_as_the_erased_one`
    /// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
    #[inline]
    #[spec(
        captures: [entry = overlay.watermark()],
        ensures: |ret| overlay.watermark() == entry
            && (ret.is_err() || ret.as_ref().is_ok_and(|pair| u32::from(pair.1) <= u32::from(fuel))),
    )]
    pub fn eval_overlay_computation(
        &self,
        overlay: &mut Overlay,
        core: &mut CoreArena,
        domain: &mut DomainArena,
        definitions: Definitions<'_>,
        fuel: Fuel,
        root: OverlayCompId,
    ) -> Result<(DomainCompId, Fuel), OverlayEvalFault>
    {
        match self.policy.stance() {
            | DuplicationStance::EraseAndClone => {
                eval_overlay_computation(overlay, core, domain, definitions, fuel, root)
            },
            | DuplicationStance::Spinal => {
                let (produced, left) = eval_overlay_shared(
                    overlay,
                    core,
                    domain,
                    definitions,
                    fuel,
                    self.policy,
                    OverlayId::Computation(root),
                )?;
                match produced {
                    | Glued::Computation(comp) => Ok((comp, left)),
                    | Glued::Value(_) => {
                        Err(OverlayEvalFault::Evaluation(EvalFault::MachineInvariant))
                    },
                }
            },
        }
    }

    /// Decide a conversion problem over domain values evaluated under the
    /// installed stance, recording into the bound sink.
    ///
    /// # Specification
    /// - requires: as [`decide`].
    /// - ensures: as [`decide`] with the bound sink, which receives the winning
    ///   derivation in preorder whenever the stance is spinal.
    /// - provides: the conversion entry for an installed stance: the one route
    ///   by which a verdict over a spinal evaluation is reached, and it
    ///   records.
    /// - fails: as [`decide`] fails.
    /// - panics: none.
    ///
    /// # Errors
    /// Every variant of [`ConversionFault`]; see its documentation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the oracle is the kernel's sequential replay over the
    ///   original core terms: every catalogue and ladder pair, evaluated under
    ///   the spinal stance and decided here, is replayed to the same verdict,
    ///   and a decline under a starving schedule stays a decline through the
    ///   kernel.
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::an_unlucky_spinal_schedule_declines_and_the_kernel_with_it`
    #[inline]
    pub fn decide<M>(
        &mut self,
        core: &CoreArena,
        domain: &mut DomainArena,
        definitions: Definitions<'_>,
        settings: MachineSettings,
        problem: Problem,
    ) -> Result<MachineReport, ConversionFault>
    where
        M: CheckMemo<GoalSupport, ProcessId> + Default,
    {
        decide::<S, M>(core, domain, definitions, settings, problem, self.sink)
    }
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_conversion_trace::NullSink;
    use gandr_kernel_conversion_trace::TraceLog;

    use super::DuplicationPolicy;
    use super::DuplicationStance;
    use super::PolicyRefusal;
    use super::TraceNode;
    use super::TracedDuplication;

    #[test]
    fn the_spinal_stance_installs_only_bound_to_a_recording_sink()
    {
        let mut discarding = NullSink;
        assert_eq!(
            Some(PolicyRefusal::Untraced {
                stance: DuplicationStance::Spinal,
            }),
            TracedDuplication::<NullSink>::install(DuplicationStance::Spinal, &mut discarding)
                .err(),
            "a sink that keeps nothing cannot carry the spinal stance's derivations"
        );
        assert_eq!(
            Ok(DuplicationStance::EraseAndClone),
            TracedDuplication::install(DuplicationStance::EraseAndClone, &mut discarding)
                .map(|installed| installed.stance()),
            "the reference stance needs no trace, so any sink carries it"
        );
        let mut log = TraceLog::<TraceNode>::new();
        assert_eq!(
            Ok(DuplicationStance::Spinal),
            TracedDuplication::install(DuplicationStance::Spinal, &mut log)
                .map(|installed| installed.stance()),
            "a recording sink carries the spinal stance"
        );
        assert_eq!(
            Ok(DuplicationStance::EraseAndClone),
            TracedDuplication::install(DuplicationStance::EraseAndClone, &mut log)
                .map(|installed| installed.stance()),
            "and the reference stance with it"
        );
        assert_eq!(
            Err(PolicyRefusal::StanceGated {
                stance: DuplicationStance::Spinal,
            }),
            DuplicationPolicy::new(DuplicationStance::Spinal),
            "the sinkless installation still refuses the spinal stance"
        );
    }
}
