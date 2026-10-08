//! The two policy parameters the value domain is written against: the
//! scheduling policy and the duplication policy.
//!
//! Both are parameters from the moment the domain exists rather than after a
//! measurement asks for them, because retrofitting either costs the domain's
//! shape: a scheduler that hardcodes one share is rewritten rather than
//! reconfigured, and a duplication rule baked into the value representation is
//! not a rule that can be replaced.
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
//! # The finer duplication stance is gated, and the gate is the point
//!
//! The erase-and-clone stance is the baseline and the reference every later
//! stance replays against. The spinal stance is representable here — the
//! parameter's shape has to admit it or the parameter buys nothing — and it is
//! **refused at installation** until the certification trace that would make it
//! checkable exists. Installing an uncertified strategy is precisely the
//! inversion the trace-before-strategy ordering forbids, so the refusal is the
//! ordering made mechanical rather than a note in a design document.

use anodized::spec;
use gandr_core_term::DefinitionHeight;

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
    #[inline]
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
    ///   contrast with [`DuplicationPolicy::new`], which gates one of its own
    ///   stances.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
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
    ///   growth asserted for the weighted one.
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
            | SchedulingStance::UniformFair => Share(1_u32),
            | SchedulingStance::HeightWeighted => Share(u32::from(height).saturating_add(1_u32)),
        }
    }
}

/// The stances the duplication parameter can take.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DuplicationStance
{
    /// Erase the sharing and clone the whole value. The conservative baseline,
    /// and the reference byte-for-byte output every later stance replays
    /// against.
    #[default]
    EraseAndClone,
    /// Copy the binder-to-occurrence paths and leave the maximal subexpressions
    /// free of the duplicated binder shared. Finer than full laziness, and
    /// gated: the results that would certify it are stated over simply-typed
    /// systems that type no fragment of this language, so it installs only
    /// behind the conversion trace that makes it checkable by replay.
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
    /// The stance is gated behind a certification trace that does not exist
    /// yet. Installing it would put an uncertified strategy where the design
    /// requires evidence, which is the ordering the gate makes mechanical.
    StanceGated
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
    /// # Specification
    /// - requires: nothing — every stance is admissible input, and the gated
    ///   one is refused rather than unrepresentable. The parameter has to
    ///   *admit* the finer stance or it fixes nothing; what it withholds is the
    ///   installation.
    /// - ensures: on success a policy at `stance`.
    /// - provides: the installation point a measurement moves, and the gate
    ///   that keeps an uncertified stance out of it.
    /// - fails: [`PolicyRefusal::StanceGated`] for the spinal stance, naming
    ///   the stance it refused, until the conversion trace that certifies it
    ///   exists.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PolicyRefusal::StanceGated`] — the stance needs a certification
    ///   trace that has not been built.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the gate, separated by
    ///   installing the baseline stance and the gated one, each asserted by
    ///   variant, with the refusal asserted to name the stance it refused.
    /// - witness: `policy::tests::the_finer_duplication_stance_is_gated`
    #[inline]
    #[spec(ensures: |ret| match stance {
        | DuplicationStance::EraseAndClone => {
            ret.as_ref().is_ok_and(|policy| policy.stance() == stance)
        },
        | DuplicationStance::Spinal => {
            matches!(ret, Err(PolicyRefusal::StanceGated { stance: refused }) if refused == stance)
        },
    })]
    pub fn new(stance: DuplicationStance) -> Result<Self, PolicyRefusal>
    {
        match stance {
            | DuplicationStance::EraseAndClone => Ok(Self { stance }),
            | DuplicationStance::Spinal => Err(PolicyRefusal::StanceGated { stance }),
        }
    }

    /// The installed stance.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the installed stance, which is
    ///   [`DuplicationStance::EraseAndClone`] for every policy that exists,
    ///   since [`DuplicationPolicy::new`] refuses the other.
    /// - provides: the stance the sharing overlay consults rather than deciding
    ///   for itself.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn stance(&self) -> DuplicationStance
    {
        self.stance
    }

    /// What a duplication under this policy does to a part of a shared value.
    ///
    /// This is the whole observable content of a stance, and it is what the
    /// sharing overlay consults rather than deciding for itself.
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
    ///   which is the whole table.
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
            | (DuplicationStance::EraseAndClone, _)
            | (DuplicationStance::Spinal, SharedPart::Spine) => Copied::Copied,
            | (DuplicationStance::Spinal, SharedPart::Rib) => Copied::Shared,
        }
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::DefinitionHeight;

    use super::Copied;
    use super::DuplicationPolicy;
    use super::DuplicationStance;
    use super::PolicyRefusal;
    use super::SchedulingPolicy;
    use super::SchedulingStance;
    use super::SharedPart;

    /// The floor, an ordinary height, and the ceiling.
    const HEIGHTS: [u32; 3] = [0_u32, 5_u32, u32::MAX];

    #[test]
    fn every_stance_gives_every_height_a_positive_share()
    {
        for stance in [
            SchedulingStance::UniformFair,
            SchedulingStance::HeightWeighted,
        ] {
            let policy = SchedulingPolicy::new(stance);
            for height in HEIGHTS {
                let share = policy.share(DefinitionHeight::from(height));
                assert!(
                    u32::from(share) > 0_u32,
                    "a share slows a process and never stops one, so no stance may answer zero"
                );
            }
        }
    }

    #[test]
    fn the_uniform_stance_ignores_the_height()
    {
        let policy = SchedulingPolicy::default();
        assert_eq!(
            SchedulingStance::UniformFair,
            policy.stance(),
            "the uniform stance is the default"
        );
        let floor = policy.share(DefinitionHeight::from(0_u32));
        for height in HEIGHTS {
            assert_eq!(
                floor,
                policy.share(DefinitionHeight::from(height)),
                "round-robin gives one share whatever the goal's height"
            );
        }
    }

    #[test]
    fn the_weighted_stance_rises_with_the_height()
    {
        let policy = SchedulingPolicy::new(SchedulingStance::HeightWeighted);
        let floor = policy.share(DefinitionHeight::from(0_u32));
        let ordinary = policy.share(DefinitionHeight::from(5_u32));
        let ceiling = policy.share(DefinitionHeight::from(u32::MAX));
        assert!(floor < ordinary, "a taller goal receives a larger share");
        assert!(
            ordinary < ceiling,
            "and the growth continues up to the saturation point"
        );
        assert_eq!(
            ceiling,
            policy.share(DefinitionHeight::from(u32::MAX.saturating_sub(1_u32))),
            "and the last two heights answer one share, which is the saturation itself \
             rather than a restatement of the same call"
        );
        assert_eq!(
            floor,
            SchedulingPolicy::default().share(DefinitionHeight::from(0_u32)),
            "and at the floor the two stances agree, so the parameter is inert on a flat corpus"
        );
    }

    #[test]
    fn the_finer_duplication_stance_is_gated()
    {
        let baseline = DuplicationPolicy::new(DuplicationStance::EraseAndClone);
        assert_eq!(
            Ok(DuplicationStance::EraseAndClone),
            baseline.map(|policy| policy.stance()),
            "the conservative stance installs and is the default"
        );
        assert_eq!(
            DuplicationStance::EraseAndClone,
            DuplicationPolicy::default().stance()
        );
        assert_eq!(
            Err(PolicyRefusal::StanceGated {
                stance: DuplicationStance::Spinal,
            }),
            DuplicationPolicy::new(DuplicationStance::Spinal),
            "the finer stance is representable and refused: the gate is the ordering, mechanized"
        );
    }

    #[test]
    fn the_stances_differ_only_on_the_ribs()
    {
        let baseline = DuplicationPolicy::default();
        assert_eq!(Copied::Copied, baseline.copies(SharedPart::Spine));
        assert_eq!(
            Copied::Copied,
            baseline.copies(SharedPart::Rib),
            "the erasure copies everything, which is what makes it the unshared reference"
        );

        // The gated stance's table is still the parameter's shape, so it is
        // asserted here through the stance rather than through an installation
        // the gate refuses.
        let spinal = DuplicationPolicy {
            stance: DuplicationStance::Spinal,
        };
        assert_eq!(Copied::Copied, spinal.copies(SharedPart::Spine));
        assert_eq!(
            Copied::Shared,
            spinal.copies(SharedPart::Rib),
            "the spinal stance keeps the ribs shared, which is the whole difference"
        );
    }
}
