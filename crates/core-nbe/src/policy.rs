//! The three policy parameters the value domain and its conversion machine
//! are written against: the scheduling policy, the duplication policy and the
//! channel-granularity policy.
//!
//! Each is a parameter rather than a constant, because fixing one costs the
//! shape of what it governs: a scheduler that hardcodes one share is rewritten
//! rather than reconfigured, a duplication rule baked into the value
//! representation is not a rule that can be replaced, and a machine minting
//! channels at one fixed grain moves to a finer one only by a rewrite.
//!
//! # A share never forecloses a proof
//!
//! A definitional height is a prior about which side of a conversion is cheaper
//! to unfold. As a **gate** on which reductions are attempted it can foreclose
//! the short proof, which is the failure the fair-interleaving design exists to
//! avoid. As a **share** it changes only how fast each process runs, so the set
//! of proofs the search can find is unchanged and the accumulated tuning is
//! retained.
//!
//! That is the property this module enforces rather than describes: every
//! stance returns a **strictly positive** share for every height, so no stance
//! can starve a process to a standstill and thereby gate what it was only meant
//! to weight.
//!
//! The non-uniform-share bound the parameter is motivated by remains its
//! source's conjecture. It motivates the parameter; it does not commit it,
//! which is why the default stance is the uniform one.
//!
//! # The spinal duplication stance enters under the testing stance
//!
//! The erase-and-clone stance is the baseline and the reference the spinal
//! stance is tested against. Both install through [`DuplicationPolicy::new`].
//! The spinal stance enters as a sharing mechanism enters the kernel: assumed
//! to hold, checked by a property test against its reference, and admitted
//! with an informal simulation argument rather than a proof. That is the
//! testing reading of a judgement's meaning (Dybjer 2012): a generated root is
//! the input, its evaluation and readback under both stances the run, and
//! agreement modulo erasure the observation that corroborates or refutes it.
//! A verdict decided under the stance through [`TracedDuplication`] still
//! records the derivation the kernel replays.
//!
//! # Scheduling share
//!
//! A definitional height is a prior about which side of a conversion is cheaper
//! to unfold. As a gate on which reductions run it can foreclose the short
//! proof; as a share it changes only how fast each process runs.
//! `SchedulingPolicy::share` returns a strictly positive `Share` for every
//! height under every stance, so no stance starves a process.
//! `SchedulingStance::UniformFair` is the default;
//! `SchedulingStance::HeightWeighted` weights shallow goals ahead of deep ones
//! without stopping the deep ones. The conversion machine reads a share as a
//! period: a process takes one turn per `share` visits of the run queue, a goal
//! at the share of the taller defined head it compares and a channel at the
//! share of the definition it evaluates, so under the weighted stance a deeper
//! process advances more slowly and never stops. Never stopping is not
//! finishing within a budget: a refutation sixteen unfoldings deep beside a
//! shallow divergence answers within a 2,000-step budget under the fair stance,
//! and under the weighted one spends the same budget on the divergence and
//! declines; the kernel's replay declines with it rather than reading the
//! decline as either verdict.
//!
//! # Duplication stance
//!
//! `DuplicationPolicy::copies` answers, per part of a shared value, whether a
//! duplication copies it. `DuplicationStance::EraseAndClone` copies everything
//! and is the unshared reference output the spinal stance is tested against.
//! `DuplicationStance::Spinal` copies the binder-to-occurrence spine and shares
//! the ribs. `DuplicationPolicy::new` installs either, and
//! `DuplicationPolicy::default` is the reference, so every check runs the
//! copying stance until a measurement moves the default. `duplicate_value` and
//! `duplicate_computation` take either policy; the run that evaluates each
//! shared leg once per configuration is `TracedDuplication`'s, bound to a sink
//! that records (see `traced`).
//!
//! # The property
//!
//! `tests::duplication::spinal_evaluation_agrees_with_the_copying_stance`
//! generates overlay roots of both evaluation families — abstractions shared
//! among several occurrences, shares nested in legs and bodies, occurrences of
//! outer shares inside legs, opaque core terms reading the binders around them
//! — evaluates and reads back each under both stances, and requires the same
//! tree, compared over the core arena, or the same refusal. Each case runs a
//! closed root and an open body applied to two different arguments, so a share
//! inside the body evaluates its leg under two bindings of the body's binder.
//! Closed roots alone rarely reach that: a remembered leg keyed without its
//! bindings passes 256 of them and fails the applied roots on every run. That
//! agreement modulo erasure is the whole certifying property. Step counts are a
//! measurement, not part of it.
//!
//! # The simulation argument
//!
//! A spinal run follows the reference run over the same erased term, each
//! later evaluation of a shared leg replaced by a recall:
//!
//! - **Duplication.** The spinal walk copies each spine and keeps each rib as a
//!   share, and the duplicate erases to the tree its input erases to
//!   (`tests::duplication::spinal_duplication_is_invisible_to_erasure`), so
//!   both runs evaluate one term.
//! - **Erasure.** Erasing the duplicate keeps each share's leg with its free
//!   indices and otherwise gives the reference's erasure, the leg standing
//!   unshifted at each occurrence, so a free index names at each occurrence the
//!   binder it reaches from there.
//! - **Evaluation.** The machine evaluates the erasure as the reference does,
//!   except at a leg: its first evaluation in a configuration — one binding at
//!   each of its free indices, in both zones — is remembered, and a later
//!   occurrence in that configuration takes it. The invariant is that a
//!   remembered weak head is the one the reference computes for that leg there.
//!   It holds because evaluation is deterministic and a leg reads its
//!   environment only at its free indices, so two occurrences in one
//!   configuration evaluate one closed instance. A leg with an index the
//!   environment does not bind is never remembered.
//! - **Readback** reads the same weak heads, so it reads back the same tree. A
//!   refusal met inside a leg is met at the leg's first evaluation in its
//!   configuration, where the reference meets it too.
//!
//! The argument rests on the test in two places: that the free indices a leg
//! is keyed by are exactly those its evaluation reads (the property's applied
//! roots), and that a configuration tells the zones apart and ignores the
//! bindings a leg does not read
//! (`eval::tests::shared_configurations_distinguish_zones_but_ignore_unused_bindings`).
//! It holds for runs that finish: the two stances spend different fuel, so at
//! a budget's edge one may decline where the other answers, and the kernel
//! reads a decline as neither verdict.
//!
//! # What the stance costs
//!
//! Over 1,000 generated roots every root agrees, 365 on a tree and 635 on a
//! refusal (the generator is untyped). The spinal run spends fewer steps on 6,
//! as many on 330 and more on 29, at most two more and at most a quarter over.
//! Remembering a configuration costs the step that pops the remembering task,
//! and a recall the step that pops it: a leg of `c` steps met `k` times costs
//! `k·c` in the reference and `c + k` spinal, so the sharing saves
//! `(k − 1)(c − 1) − 1` steps and loses one on a one-step leg.
//! The generator's legs are a few steps long. The full-laziness witnesses'
//! legs cost more than the remembering, and there the step count's slope
//! shows each rib evaluated once (`tests::full_laziness`). Spinal and ordinary
//! full laziness are both β-optimal for weak reduction (Balabonski 2013), so
//! the stance pays only under strong reduction and stays a measured choice:
//! the default moves only when a measurement moves it.
//!
//! # Granularity stance
//!
//! `GranularityPolicy` says how finely the conversion machine shares the
//! evaluations its goals demand. `GranularityStance::Skeleton`, the default,
//! mints one evaluation channel per distinct definition body, keyed by the
//! body's subterm-table entry index in a dense side vector, so two unfoldings
//! of one body — of one definition, or of two the table gave one body — read
//! one evaluation. Re-applying a neutral's spine to that body, entering a thunk
//! and opening a binder under a fresh variable are each one channel per
//! neutral, closure, or closure and level. `GranularityStance::Spinal` would
//! mint channels along spines as well, sharing partial applications between
//! unfoldings; `GranularityPolicy::new` refuses it with
//! `PolicyRefusal::GranularityGated`, because a finer sharing changes which
//! evaluations a derivation reads, and it installs only once a replayed trace
//! certifies its runs.
//!
//! Alternatives: no parameter, with the skeleton hard-wired, which leaves the
//! finer stance no seam to arrive through; and one channel per neutral with no
//! body sharing, which evaluates a body once per distinct spine and loses the
//! table's own deduplication. Reversal: when certified spinal runs show the
//! parameter costs more than the sharing it buys, the parameter goes and the
//! skeleton is the machine's only shape.
//!
//! # References
//!
//! - `Dybjer-2012-program_testing_meaning_explanations_intuitionistic_type_theory`
//!   — background: § 1.4 reads the meaning explanations as a testing manual,
//!   a judgement corroborated or refuted by running it on generated input and
//!   observing the result; the spinal stance enters on that reading, its
//!   property the observation.
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — background: § 6 — the
//!   kernel replicates the sharing mechanisms, each entering on a property test
//!   against its reference and an informal simulation argument.

use anodized::spec;
use gandr_core_term::DefinitionHeight;

#[cfg(doc)]
use crate::traced::TracedDuplication;

/// A process's share of the scheduler's attention.
///
/// Strictly positive by construction: the constructor is private and every
/// stance's arithmetic starts from one, so a zero share is not representable
/// and cannot be reached.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Share(u32);

impl From<Share> for u32
{
    /// Read the share back out as a `u32`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the carried count, which is strictly positive because the
    ///   type admits no zero share.
    /// - provides: the weight a scheduler divides its attention by, with the
    ///   nonzero guarantee carried out of the newtype.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — shares obtained at zero, ordinary and maximal
    ///   definition heights under both scheduling stances are observed as
    ///   positive weights; a zero result, a changed payload or a wrapped
    ///   ceiling changes the scheduler weights.
    /// - witness: `policy::tests::every_stance_gives_every_height_a_positive_share`
    /// - witness: `policy::tests::the_weighted_stance_rises_with_the_height`
    #[inline]
    #[spec(ensures: |ret| ret == share.0 && ret > 0_u32)]
    fn from(share: Share) -> Self
    {
        share.0
    }
}

/// The stances the scheduling parameter can take.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SchedulingStance
{
    /// Every process receives the same share: round-robin over the active
    /// queue, which is the design's own fairness result and the default.
    #[default]
    UniformFair,
    /// A process's share is weighted by the definitional height of what it is
    /// working on, so a shallow goal advances faster than a deep one without
    /// the deep one stopping.
    HeightWeighted,
}

/// The scheduling policy: which stance decides a process's share.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SchedulingPolicy
{
    /// The installed stance.
    stance: SchedulingStance,
}

impl SchedulingPolicy
{
    /// Install a stance.
    ///
    /// Both stances install: the height-weighted one sits behind the uniform
    /// default rather than behind a gate, because a share cannot change which
    /// proofs exist and so needs no certification to be safe.
    ///
    /// # Specification
    /// - requires: nothing; both stances install.
    /// - ensures: the policy carries exactly the stance offered.
    /// - provides: the total installation the paragraph above justifies — the
    ///   contrast with [`GranularityPolicy::new`], which gates one of its own
    ///   stances.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both installed scheduling stances are observed
    ///   through their shares at zero, ordinary and maximal heights; selecting
    ///   the other stance changes constancy or strict growth.
    /// - witness: `policy::tests::every_stance_gives_every_height_a_positive_share`
    /// - witness: `policy::tests::the_uniform_stance_ignores_the_height`
    /// - witness: `policy::tests::the_weighted_stance_rises_with_the_height`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.stance == stance)]
    pub fn new(stance: SchedulingStance) -> Self
    {
        Self { stance }
    }

    /// The installed stance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn stance(&self) -> SchedulingStance
    {
        self.stance
    }

    /// The share a process working at `height` receives.
    ///
    /// # Specification
    /// - requires: nothing — every height is admissible input, including the
    ///   floor and the ceiling.
    /// - ensures: a **strictly positive** share under every stance and every
    ///   height, so a share can slow a process and never stop one; the uniform
    ///   stance answers the same share at every height, and the height-weighted
    ///   stance is non-decreasing in the height.
    /// - provides: the scheduler's per-process weight, which is where a
    ///   definitional height is allowed to live.
    /// - fails: never — the height-weighted arithmetic saturates at the share
    ///   ceiling rather than overflowing, and saturation preserves both the
    ///   positivity and the monotonicity.
    /// - panics: the mirrored `ensures` predicate is an assertion rather than a
    ///   returned refusal, so a stance that ever answered a zero share would
    ///   abort here instead of handing one back. Neither stance defined here
    ///   can reach it at any height; the assertion exists so that a stance
    ///   added later fails at its first call rather than at a review.
    /// - intension: the share is a function of the stance and the height alone.
    ///   It does not read the queue, the goal, or any prior call, so two
    ///   processes at one height receive one share whatever order they were
    ///   scheduled in — which is what makes the weighting a share rather than a
    ///   history-dependent gate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the stance match and the
    ///   height arithmetic, separated by the floor height, an ordinary height
    ///   and the height ceiling under both stances, with positivity asserted at
    ///   every point, constancy asserted for the uniform stance and strict
    ///   growth asserted for the weighted one. Removing saturation, returning
    ///   zero or flattening the weighted stance changes one of those
    ///   observations.
    /// - witness: `policy::tests::every_stance_gives_every_height_a_positive_share`
    /// - witness: `policy::tests::the_uniform_stance_ignores_the_height`
    /// - witness: `policy::tests::the_weighted_stance_rises_with_the_height`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| u32::from(ret) > 0_u32)]
    pub fn share(
        &self,
        height: DefinitionHeight,
    ) -> Share
    {
        match self.stance {
            SchedulingStance::UniformFair => Share(1_u32),
            SchedulingStance::HeightWeighted => Share(u32::from(height).saturating_add(1_u32)),
        }
    }
}

/// The stances the duplication parameter can take.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DuplicationStance
{
    /// Erase the sharing and clone the whole value. The conservative baseline,
    /// and the reference output the spinal stance is tested against.
    #[default]
    EraseAndClone,
    /// Copy the binder-to-occurrence paths and leave the maximal subexpressions
    /// free of the duplicated binder shared. Finer than full laziness, and
    /// admitted under the testing stance: a property test checks it against
    /// the erase-and-clone stance modulo erasure (see the module doc).
    Spinal,
}

/// A part of a shared value, as a duplication walk classifies it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SharedPart
{
    /// A direct path from the duplicated binder to one of its occurrences.
    Spine,
    /// A maximal subexpression free of the duplicated binder.
    Rib,
}

/// What a duplication does to a part.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Copied
{
    /// The part is copied into the duplicate.
    Copied,
    /// The part stays shared between the original and the duplicate.
    Shared,
}

/// Why a policy could not be installed.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PolicyRefusal
{
    /// The granularity stance installs only behind a certification trace,
    /// which this crate does not take: a finer sharing changes which
    /// evaluations a derivation reads.
    GranularityGated
    {
        /// The stance that was refused.
        stance: GranularityStance,
    },
    /// A traced installation of the spinal stance was asked for over a sink
    /// that retains nothing, so its verdicts would carry no derivation for the
    /// kernel to replay.
    Untraced
    {
        /// The stance that was refused.
        stance: DuplicationStance,
    },
}

/// The duplication policy: which part of a shared value a duplication copies.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DuplicationPolicy
{
    /// The installed stance.
    stance: DuplicationStance,
}

impl DuplicationPolicy
{
    /// Install a stance.
    ///
    /// Both stances install: the spinal one under the testing stance, checked
    /// against the erase-and-clone reference by the property the module doc
    /// names.
    ///
    /// # Specification
    /// - requires: nothing; both stances install.
    /// - ensures: a policy at `stance`.
    /// - provides: the installation point a measurement moves.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both stances are installed and observed after
    ///   installation; installing one in the other's place changes the observed
    ///   stance.
    /// - witness: `policy::tests::every_duplication_stance_installs`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!((stance, ret.stance), (DuplicationStance::EraseAndClone, DuplicationStance::EraseAndClone) | (DuplicationStance::Spinal, DuplicationStance::Spinal)))]
    pub const fn new(stance: DuplicationStance) -> Self
    {
        Self { stance }
    }

    /// The installed stance.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the installed stance.
    /// - provides: the stance a duplication walk over the sharing overlay
    ///   consults, so the overlay itself decides nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the default and both installed stances are observed;
    ///   confusing the baseline with the spinal stance changes the result.
    /// - witness: `policy::tests::every_duplication_stance_installs`
    /// - witness: `traced::tests::the_spinal_stance_installs_only_bound_to_a_recording_sink`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == self.stance)]
    pub fn stance(&self) -> DuplicationStance
    {
        self.stance
    }

    /// What a duplication under this policy does to a part of a shared value.
    ///
    /// This is the whole observable content of a stance, and it is what a
    /// duplication walk over the sharing overlay consults; the overlay holds
    /// syntax and decides nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the baseline stance copies every part, which is what makes it
    ///   the erasure — it produces the fully unshared value and therefore the
    ///   reference output; the spinal stance copies the spine and leaves the
    ///   ribs shared, which is the full-laziness property retained at a finer
    ///   grain.
    /// - provides: the per-part decision a duplication walk asks the parameter.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the stance-by-part table,
    ///   separated by both parts under both stances, all four asserted exactly,
    ///   which is the whole table. Swapping either part or stance, copying the
    ///   spinal rib or sharing a required spine changes at least one entry.
    /// - witness: `policy::tests::the_stances_differ_only_on_the_ribs`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match (self.stance, part) {
        | (DuplicationStance::EraseAndClone, SharedPart::Spine | SharedPart::Rib)
        | (DuplicationStance::Spinal, SharedPart::Spine) => ret == Copied::Copied,
        | (DuplicationStance::Spinal, SharedPart::Rib) => ret == Copied::Shared,
    })]
    pub fn copies(
        &self,
        part: SharedPart,
    ) -> Copied
    {
        match (self.stance, part) {
            (DuplicationStance::EraseAndClone, _)
            | (DuplicationStance::Spinal, SharedPart::Spine) => Copied::Copied,
            (DuplicationStance::Spinal, SharedPart::Rib) => Copied::Shared,
        }
    }
}

/// Where a conversion run mints its evaluation channels.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum GranularityStance
{
    /// One channel per distinct subterm-table entry a definition body names:
    /// two unfoldings of one body share one evaluation of it, whichever
    /// definitions name it. The default, and the skeleton every finer stance
    /// replays against.
    #[default]
    Skeleton,
    /// Channels minted along spines as well, so a partial application shared
    /// by two unfoldings is evaluated once. Representable so the parameter
    /// admits it, and gated: it changes which evaluations are shared, so it
    /// installs only behind the conversion trace that certifies it by replay.
    Spinal,
}

/// The channel-granularity policy: how finely a conversion run shares the
/// evaluations its processes demand.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GranularityPolicy
{
    /// The installed stance.
    stance: GranularityStance,
}

impl GranularityPolicy
{
    /// Install a stance.
    ///
    /// # Specification
    /// - requires: nothing — every stance is admissible input, and the gated
    ///   one is refused rather than unrepresentable.
    /// - ensures: on success a policy at `stance`.
    /// - provides: the installation point the transcription is built against
    ///   from the start, so the finer stance arrives as a policy move rather
    ///   than a rewrite of the machine.
    /// - fails: [`PolicyRefusal::GranularityGated`] for the spinal stance,
    ///   naming the stance it refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PolicyRefusal::GranularityGated`] — the stance needs a certification
    ///   trace, and installation takes none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the gate, separated by
    ///   installing the skeleton stance and the gated one, each asserted by
    ///   variant, with the refusal asserted to name the stance it refused.
    ///   Admitting the spinal branch, refusing the skeleton or losing the
    ///   refused stance changes an observation.
    /// - witness: `policy::tests::the_finer_granularity_stance_is_gated`
    #[inline]
    #[spec(ensures: |ret| match stance {
        | GranularityStance::Skeleton => {
            ret.as_ref().is_ok_and(|policy| policy.stance() == stance)
        },
        | GranularityStance::Spinal => {
            matches!(ret, Err(PolicyRefusal::GranularityGated { stance: refused }) if refused == stance)
        },
    })]
    pub fn new(stance: GranularityStance) -> Result<Self, PolicyRefusal>
    {
        match stance {
            GranularityStance::Skeleton => Ok(Self { stance }),
            GranularityStance::Spinal => Err(PolicyRefusal::GranularityGated { stance }),
        }
    }

    /// The installed stance.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the installed stance, which is
    ///   [`GranularityStance::Skeleton`] for every policy that exists, since
    ///   [`GranularityPolicy::new`] refuses the other.
    /// - provides: the stance the machine's channel minting consults.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the accepted skeleton stance is read back and the
    ///   spinal installation is refused by its exact reason; substituting a
    ///   stance or admitting the gated branch changes the observations.
    /// - witness: `policy::tests::the_finer_granularity_stance_is_gated`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == self.stance && ret == GranularityStance::Skeleton)]
    pub fn stance(&self) -> GranularityStance
    {
        self.stance
    }
}

#[cfg(test)]
mod tests;
