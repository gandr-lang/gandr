//! Guarded templates: one certificate standing for a family of certificates
//! that fire the same cells at the same positions from peaks differing only
//! below what those cells read.
//!
//! [`anti_unify_tracelets`] folds such a family into a [`GuardedTemplate`]:
//! the least general generalization of the members' peaks and joins, taken
//! jointly by the alphabet's anti-unifier, the shared paths, and at every
//! point where the members differ an entry holding one guarded arm per
//! distinct member subterm. A template is emitted only where it pays: its size
//! `s` must stand below its expansion factor `f = ⌊F / s⌋`, with `F` the plain
//! size of the family it replaces, which gives `s < F` and `s · s < F` at once.
//! Every arm of a paying template is then admitted by an inheritance check —
//! the shared paths replayed from the generalized peak with that arm in place
//! — memoized per content triple of region, entry and arm body in an
//! [`InheritanceCache`] that lives for one run.
//!
//! A template is compression, not trust. [`GuardedTemplate::instantiate`]
//! rebuilds a member from its peak's substitution, and admitting the member is
//! replaying what was rebuilt ([`GuardedTemplate::admit`]): a cache entry that
//! lies about a triple lets a template through, never a member that replay
//! refuses.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::Generalization;
use gandr_theory_cell_complexes::PatternSize;
use gandr_theory_coherent_resolutions::ReplayPathOutcome;
use gandr_theory_coherent_resolutions::StuckStep;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::TraceletReplay;
use quenchant_shape::shape::Maybe;

use crate::boundary::AdmissionCount;
use crate::boundary::CacheHitCount;
use crate::boundary::EntryIndex;
use crate::boundary::ExpansionFactor;
use crate::boundary::GuardId;
use crate::boundary::LegStepIndex;
use crate::boundary::MemberCount;
use crate::boundary::MemberIndex;
use crate::boundary::NodeCount;
use crate::boundary::ReplayStepCount;
use crate::boundary::TripleCount;
use crate::flow::FlowObstruction;
use crate::flow::TraceletFlow;
use crate::flow::tracelet_flow;
use crate::normal_form::ContentDigest;
use crate::normal_form::ContentHasher;

/// The domain separator mixed in before a template region's content.
const REGION_DOMAIN: &[u8] = b"gandr.template.region.v1";

/// The domain separator mixed in before an arm body's content, so an arm
/// address cannot collide with a region address.
const ARM_DOMAIN: &[u8] = b"gandr.template.arm.v1";

quenchant_shape::reason_enum! {
    /// Why an inheritance cache holds no verdict for a triple.
    pub mod inheritance_lookup {
        /// The reason the lookup missed.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No check of the triple has run in this cache, and none was
            /// recorded into it.
            Unchecked,
        }
    }
}

/// The content address of a template's region: its generalized peak and
/// join and its two recorded paths.
///
/// It keys the inheritance cache and nothing else; it is build-local, like
/// every address of the crate, and no identity witness.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TemplateAddress(ContentDigest);

/// The content address of an arm's body: the substitution that puts it in
/// place.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArmAddress(ContentDigest);

/// The triple an inheritance check is memoized under: a template region, one
/// of its entries, and the body of one arm at that entry.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InheritanceKey
{
    /// The region the arm is checked in.
    pub region: TemplateAddress,
    /// The entry the arm fills.
    pub entry: EntryIndex,
    /// The arm's body.
    pub body: ArmAddress,
}

/// One leg of a certificate.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TemplateLeg
{
    /// The first recorded path.
    PathA,
    /// The second recorded path.
    PathB,
}

/// What an inheritance check found for one triple.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum InheritanceVerdict
{
    /// Both legs fire every recorded step from the peak with the arm in place
    /// and land on the join with it in place.
    Inherited,
    /// A leg stopped at a recorded step that did not fire.
    Stuck
    {
        /// The leg that stopped.
        leg: TemplateLeg,
        /// The step it stopped at, counted from the peak.
        step: LegStepIndex,
        /// Why the step did not fire.
        reason: StuckStep,
    },
    /// A leg fired every recorded step and landed off the join.
    MissesTheJoin
    {
        /// The leg that missed.
        leg: TemplateLeg,
    },
}

/// The inheritance verdicts of one producer run, keyed by content triple.
///
/// The cache is evidence, not a warrant: [`InheritanceCache::record`] writes
/// any verdict for any triple, and a template emitted over a lying entry still
/// admits a member only when the member's own replay fires.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct InheritanceCache
{
    /// The verdict of every triple checked or recorded.
    verdicts: BTreeMap<InheritanceKey, InheritanceVerdict>,
    /// How many triples a producer checked through this cache.
    checked: TripleCount,
    /// How many lookups a producer answered from this cache.
    hits: CacheHitCount,
}

impl InheritanceCache
{
    /// An empty cache.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// How many distinct triples the cache holds a verdict for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn distinct_triples(&self) -> TripleCount
    {
        TripleCount::from(self.verdicts.len())
    }

    /// How many triples a producer checked through this cache, each once.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn checked(&self) -> TripleCount
    {
        self.checked
    }

    /// How many lookups a producer answered from this cache without a check.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn hits(&self) -> CacheHitCount
    {
        self.hits
    }

    /// The verdict held for `key`, without counting a hit.
    ///
    /// # Specification
    /// - ensures: the verdict last checked or recorded for `key`.
    /// - provides: [`inheritance_lookup::Absent::Unchecked`] when none was.
    /// - panics: none.
    #[inline]
    pub fn get(
        &self,
        key: &InheritanceKey,
    ) -> Maybe<&InheritanceVerdict, inheritance_lookup::Absent>
    {
        self.verdicts.get(key).map_or(
            Maybe::Absent(inheritance_lookup::Absent::Unchecked),
            Maybe::Present,
        )
    }

    /// Records `verdict` for `key`, replacing any verdict held for it, without
    /// counting a check.
    ///
    /// # Specification
    /// - ensures: [`InheritanceCache::get`] answers `verdict` for `key` from
    ///   now on; the check and hit counts are unchanged.
    /// - panics: none.
    /// - intension: the cache is untrusted evidence a caller may seed; a seeded
    ///   lie is caught at admission, not here.
    #[inline]
    pub fn record(
        &mut self,
        key: InheritanceKey,
        verdict: InheritanceVerdict,
    )
    {
        self.verdicts.insert(key, verdict);
    }

    /// Every triple the cache holds, with its verdict, in key order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = (&InheritanceKey, &InheritanceVerdict)> + '_
    {
        self.verdicts.iter()
    }

    /// The verdict held for `key`, counted as a hit.
    ///
    /// # Specification
    /// - ensures: as [`InheritanceCache::get`], owned, and the hit count is one
    ///   higher when a verdict is held.
    /// - provides: [`inheritance_lookup::Absent::Unchecked`] when none is, the
    ///   counts unchanged.
    /// - panics: none.
    fn lookup(
        &mut self,
        key: &InheritanceKey,
    ) -> Maybe<InheritanceVerdict, inheritance_lookup::Absent>
    {
        let Some(verdict) = self.verdicts.get(key)
        else {
            return Maybe::Absent(inheritance_lookup::Absent::Unchecked);
        };
        self.hits = CacheHitCount::from(usize::from(self.hits).saturating_add(1));
        Maybe::Present(*verdict)
    }

    /// Records the verdict a check found for `key`, counted as a check.
    ///
    /// # Specification
    /// - ensures: as [`InheritanceCache::record`], and the check count is one
    ///   higher.
    /// - panics: none.
    fn record_check(
        &mut self,
        key: InheritanceKey,
        verdict: InheritanceVerdict,
    )
    {
        self.checked = TripleCount::from(usize::from(self.checked).saturating_add(1));
        self.verdicts.insert(key, verdict);
    }
}

/// One guarded arm of an entry: a member subterm the entry may hold.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TemplateArm<A: CellAlphabet>
{
    /// The nominal atom that guards the arm.
    pub guard: GuardId,
    /// The substitution binding the entry's metavariable to the arm's body.
    pub binding: A::Subst,
    /// The body's node count.
    pub size: PatternSize,
}

/// One point where a template's members differ, with every arm a member
/// holds there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TemplateEntry<A: CellAlphabet>
{
    /// The metavariable that stands at the point in the generalized peak.
    pub var: A::Var,
    /// The arms, keyed by the content address of their bodies.
    pub arms: BTreeMap<ArmAddress, TemplateArm<A>>,
}

/// What producing one template cost: the inheritance checks its run spent
/// and the lookups the cache answered.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct ProductionCounts
{
    /// The distinct triples the run checked.
    pub triples_checked: TripleCount,
    /// The lookups the run answered from the cache.
    pub cache_hits: CacheHitCount,
    /// The recorded steps the run's checks fired.
    pub replayed_steps: ReplayStepCount,
}

/// A family of certificates folded into one: the generalized certificate,
/// one entry per point where the members differ, and the sizes that licensed
/// its emission.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GuardedTemplate<A: CellAlphabet>
{
    /// The first member with its peak and join replaced by their
    /// generalizations: the skeleton every member shares.
    carrier: Tracelet<A>,
    /// The entries, in the order the generalization met their points.
    entries: Vec<TemplateEntry<A>>,
    /// The region's content address.
    region: TemplateAddress,
    /// The template's size `s`.
    size: NodeCount,
    /// The family's plain size `F`.
    plain_size: NodeCount,
    /// How many members the family held.
    members: MemberCount,
    /// What the run that produced the template spent.
    production: ProductionCounts,
}

/// The cost of a family with its template and without: the sizes, the
/// inheritance cache's two counts, and the replay each way.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct FamilyCostReport
{
    /// How many members the family holds.
    pub members: MemberCount,
    /// The family's plain size `F`: every member's peak, join and steps.
    pub plain_size: NodeCount,
    /// The template's size `s`: the skeleton, every arm and one guard per arm.
    pub template_size: NodeCount,
    /// `F / s`, rounded down.
    pub expansion_factor: ExpansionFactor,
    /// The distinct triples the producing run checked.
    pub triples_checked: TripleCount,
    /// The lookups the producing run answered from the cache.
    pub cache_hits: CacheHitCount,
    /// How many members the template admits.
    pub admissions: AdmissionCount,
    /// The recorded steps the producing run's checks fired.
    pub replayed_steps: ReplayStepCount,
    /// The recorded steps replaying every member on its own would fire.
    pub plain_replayed_steps: ReplayStepCount,
}

/// Why a family yields no template.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TemplateRefusal
{
    /// The family has no member.
    EmptyFamily,
    /// A member's overlap cells, kind, seam or recorded paths differ from the
    /// first member's.
    SkeletonDivergence
    {
        /// The first member that differs.
        member: MemberIndex,
    },
    /// The alphabet's anti-unifier refused the members' peaks and joins.
    Ungeneralizable,
    /// A point stands in the generalized join and not in the generalized
    /// peak, so a member's peak does not determine its arm there.
    EntryOutsidePeak
    {
        /// The entry whose point is outside the peak.
        entry: EntryIndex,
    },
    /// Two different arm bodies of one entry share a content address.
    ArmAddressCollision
    {
        /// The entry the collision is at.
        entry: EntryIndex,
    },
    /// The template would not pay: its size is not below its expansion
    /// factor.
    DoesNotPay
    {
        /// The template's size `s`.
        template_size: NodeCount,
        /// The family's plain size `F`.
        plain_size: NodeCount,
    },
    /// An arm's inheritance check, run or read from the cache, did not
    /// admit it.
    NotInherited
    {
        /// The triple whose verdict refused.
        key: InheritanceKey,
        /// The verdict.
        verdict: InheritanceVerdict,
    },
}

/// Why a template does not rebuild a certificate.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TemplateObstruction
{
    /// The peak is not an instance of the template's generalized peak.
    PeakNotAnInstance,
    /// The substitution leaves an entry's metavariable unbound.
    UnboundEntry
    {
        /// The entry left unbound.
        entry: EntryIndex,
    },
    /// The substitution binds an entry to a body the template holds no arm
    /// for.
    ArmOutsideTemplate
    {
        /// The entry whose body is outside the template.
        entry: EntryIndex,
    },
}

/// The plain size of one certificate: its peak's and join's node counts and
/// one node per recorded step of either leg.
///
/// # Specification
/// trivial.
fn plain_size<A>(tracelet: &Tracelet<A>) -> NodeCount
where
    A: CellAlphabet,
{
    NodeCount::from(
        usize::from(A::cmd_size(&tracelet.overlap.peak))
            .saturating_add(usize::from(A::cmd_size(&tracelet.joins_at)))
            .saturating_add(tracelet.path_a.len())
            .saturating_add(tracelet.path_b.len()),
    )
}

/// The content address of a template region.
///
/// # Specification
/// - ensures: a digest over the carrier's peak, join and two paths behind the
///   region domain; equal regions have equal addresses.
/// - panics: none.
fn region_address<A>(carrier: &Tracelet<A>) -> TemplateAddress
where
    A: CellAlphabet,
{
    let mut hasher = ContentHasher::new();
    core::hash::Hasher::write(&mut hasher, REGION_DOMAIN);
    core::hash::Hash::hash(&carrier.overlap.peak, &mut hasher);
    core::hash::Hash::hash(&carrier.joins_at, &mut hasher);
    core::hash::Hash::hash(&carrier.path_a, &mut hasher);
    core::hash::Hash::hash(&carrier.path_b, &mut hasher);
    TemplateAddress(hasher.digest())
}

/// The content address of an arm body.
///
/// # Specification
/// - ensures: a digest over the binding behind the arm domain; equal bindings
///   have equal addresses.
/// - panics: none.
fn arm_address<A>(binding: &A::Subst) -> ArmAddress
where
    A: CellAlphabet,
{
    let mut hasher = ContentHasher::new();
    core::hash::Hasher::write(&mut hasher, ARM_DOMAIN);
    core::hash::Hash::hash(binding, &mut hasher);
    ArmAddress(hasher.digest())
}

/// The inheritance check of one arm: the carrier's paths replayed from its
/// peak with the arm in place, against its join with the arm in place.
///
/// # Specification
/// - ensures: [`InheritanceVerdict::Inherited`] exactly when both legs fire
///   every recorded step and land on the join; otherwise the first leg, in leg
///   order, that stopped or missed; and the number of steps both legs fired.
/// - panics: none.
/// - intension: every other point stays a metavariable, which replay
///   skolemizes, so a step that reads into another entry does not fire.
fn inheritance_check<A>(
    carrier: &Tracelet<A>,
    binding: &A::Subst,
    store: &CellStore<A>,
) -> (InheritanceVerdict, ReplayStepCount)
where
    A: CellAlphabet,
{
    let mut probe = carrier.clone();
    probe.overlap.peak = A::apply_subst(binding, &carrier.overlap.peak);
    probe.joins_at = A::apply_subst(binding, &carrier.joins_at);
    let trace = probe.replay_trace(store);
    let fired = ReplayStepCount::from(
        trace
            .path_a
            .steps
            .len()
            .saturating_add(trace.path_b.steps.len()),
    );
    let verdict = [
        (TemplateLeg::PathA, &trace.path_a),
        (TemplateLeg::PathB, &trace.path_b),
    ]
    .into_iter()
    .find_map(|(leg, path)| match path.outcome {
        | ReplayPathOutcome::Stuck { reason, .. } => Some(InheritanceVerdict::Stuck {
            leg,
            step: LegStepIndex::from(path.steps.len()),
            reason,
        }),
        | ReplayPathOutcome::Reached(ref reached) if *reached != trace.joins_at => {
            Some(InheritanceVerdict::MissesTheJoin { leg })
        },
        | ReplayPathOutcome::Reached(_) => None,
    })
    .unwrap_or(InheritanceVerdict::Inherited);
    (verdict, fired)
}

/// Folds a family of certificates into a guarded template, or says why it
/// does not.
///
/// # Specification
/// - requires: `cache` holds verdicts of this store alone; a verdict recorded
///   from elsewhere is trusted here and caught only at admission.
/// - ensures: a template whose carrier is the first member with its peak and
///   join replaced by the least general generalization of every member's peak
///   and join; one entry per point of that generalization, in the
///   generalization's order, holding one arm per distinct member body, each
///   guarded by its own atom numbered in minting order; its size `s` is the
///   carrier's plain size plus every arm's node count plus one per arm, its
///   plain size `F` the members' plain sizes summed, and `s < ⌊F / s⌋`.
/// - ensures: every member's body at every entry was admitted by an inheritance
///   verdict — looked up in `cache` and counted as a hit, or checked, recorded
///   in `cache` and counted as a check — so each distinct triple of region,
///   entry and body is checked at most once per cache.
/// - fails: [`TemplateRefusal::EmptyFamily`] for no member;
///   [`TemplateRefusal::SkeletonDivergence`] for the first member whose overlap
///   cells, kind, seam or recorded paths differ from the first member's;
///   [`TemplateRefusal::Ungeneralizable`] when the anti-unifier refuses;
///   [`TemplateRefusal::EntryOutsidePeak`] for the first point absent from the
///   generalized peak; [`TemplateRefusal::ArmAddressCollision`] when two bodies
///   of one entry share an address; [`TemplateRefusal::DoesNotPay`] when `s` is
///   not below `⌊F / s⌋`, and then no check runs;
///   [`TemplateRefusal::NotInherited`] for the first triple, entry by entry and
///   member by member, whose verdict is not [`InheritanceVerdict::Inherited`].
/// - panics: none.
/// - intension: the price is taken before any check, so a family that cannot
///   pay costs one anti-unification and no replay.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L1 — over generated families of both alphabets, every template
///   emitted has `s < ⌊F / s⌋` with `F` summed independently, and every member
///   is admitted exactly as its plain replay decides, also under a cache seeded
///   with lies. L3 — a skeleton-divergent family, a family with a member whose
///   body a cell discriminates on, and a family sharing nothing below the
///   skeleton each yield no template while a near miss of each does; a family
///   of 64 members checks each distinct triple once.
/// - witness: `tests::template::a_template_is_emitted_only_below_its_expansion_factor`
/// - witness: `tests::template::every_member_admits_as_its_plain_replay`
/// - witness: `tests::template::a_skeleton_divergent_family_yields_no_template`
/// - witness: `tests::template::an_entry_a_cell_discriminates_on_yields_no_template`
/// - witness: `tests::template::a_family_with_no_shared_content_yields_no_template`
/// - witness: `tests::template::the_inheritance_check_runs_once_per_distinct_triple`
/// - witness: `tests::template::a_poisoned_inheritance_entry_is_caught_at_admission`
#[inline]
pub fn anti_unify_tracelets<A>(
    family: &[Tracelet<A>],
    store: &CellStore<A>,
    cache: &mut InheritanceCache,
) -> Result<GuardedTemplate<A>, TemplateRefusal>
where
    A: CellAlphabet,
{
    let Some((first, rest)) = family.split_first()
    else {
        return Err(TemplateRefusal::EmptyFamily);
    };
    if let Some(index) = rest.iter().position(|member| {
        member.overlap.left != first.overlap.left
            || member.overlap.right != first.overlap.right
            || member.overlap.kind != first.overlap.kind
            || member.overlap.seam != first.overlap.seam
            || member.path_a != first.path_a
            || member.path_b != first.path_b
    }) {
        return Err(TemplateRefusal::SkeletonDivergence {
            member: MemberIndex::from(index.saturating_add(1)),
        });
    }
    let boundaries: Vec<[A::Cmd; 2]> = family
        .iter()
        .map(|member| [member.overlap.peak.clone(), member.joins_at.clone()])
        .collect();
    let members: Vec<&[A::Cmd]> = boundaries.iter().map(<[A::Cmd; 2]>::as_slice).collect();
    let Maybe::Present(Generalization { patterns, points }) = A::anti_unify_cmd(&members)
    else {
        return Err(TemplateRefusal::Ungeneralizable);
    };
    let mut generalized = patterns.into_iter();
    let (Some(peak), Some(joins_at), None) =
        (generalized.next(), generalized.next(), generalized.next())
    else {
        return Err(TemplateRefusal::Ungeneralizable);
    };
    let peak_vars = A::metavariables(&peak);
    let mut carrier = first.clone();
    carrier.overlap.peak = peak;
    carrier.joins_at = joins_at;
    let region = region_address(&carrier);

    let mut entries: Vec<TemplateEntry<A>> = Vec::with_capacity(points.len());
    let mut columns: Vec<Vec<ArmAddress>> = Vec::with_capacity(points.len());
    let mut minted = 0_usize;
    let mut size = usize::from(plain_size(&carrier));
    for (index, point) in points.into_iter().enumerate() {
        let entry = EntryIndex::from(index);
        if !peak_vars.contains(&point.var) {
            return Err(TemplateRefusal::EntryOutsidePeak { entry });
        }
        let mut arms: BTreeMap<ArmAddress, TemplateArm<A>> = BTreeMap::new();
        let mut column = Vec::with_capacity(point.arms.len());
        for arm in point.arms {
            let address = arm_address::<A>(&arm.binding);
            match arms.get(&address) {
                | Some(guarded) if guarded.binding == arm.binding => {},
                | Some(_) => return Err(TemplateRefusal::ArmAddressCollision { entry }),
                | None => {
                    size = size.saturating_add(usize::from(arm.size)).saturating_add(1);
                    arms.insert(address, TemplateArm {
                        guard: GuardId::from(minted),
                        binding: arm.binding,
                        size: arm.size,
                    });
                    minted = minted.saturating_add(1);
                },
            }
            column.push(address);
        }
        entries.push(TemplateEntry {
            var: point.var,
            arms,
        });
        columns.push(column);
    }

    let plain = family
        .iter()
        .map(plain_size)
        .fold(0_usize, |total, member| {
            total.saturating_add(usize::from(member))
        });
    if plain.checked_div(size).is_none_or(|factor| size >= factor) {
        return Err(TemplateRefusal::DoesNotPay {
            template_size: NodeCount::from(size),
            plain_size: NodeCount::from(plain),
        });
    }

    let (checked_before, hits_before) = (usize::from(cache.checked()), usize::from(cache.hits()));
    let mut replayed = 0_usize;
    for (index, (entry, column)) in entries.iter().zip(&columns).enumerate() {
        for &body in column {
            let key = InheritanceKey {
                region,
                entry: EntryIndex::from(index),
                body,
            };
            let verdict = match cache.lookup(&key) {
                | Maybe::Present(verdict) => verdict,
                | Maybe::Absent(inheritance_lookup::Absent::Unchecked) => {
                    // Every address of a column was inserted into its entry's
                    // arms above, so the lookup finds the arm; a miss could
                    // only be an address resolving to another body.
                    let Some(arm) = entry.arms.get(&body)
                    else {
                        return Err(TemplateRefusal::ArmAddressCollision {
                            entry: EntryIndex::from(index),
                        });
                    };
                    let (verdict, fired) = inheritance_check(&carrier, &arm.binding, store);
                    replayed = replayed.saturating_add(usize::from(fired));
                    cache.record_check(key, verdict);
                    verdict
                },
            };
            if verdict != InheritanceVerdict::Inherited {
                return Err(TemplateRefusal::NotInherited { key, verdict });
            }
        }
    }

    Ok(GuardedTemplate {
        carrier,
        entries,
        region,
        size: NodeCount::from(size),
        plain_size: NodeCount::from(plain),
        members: MemberCount::from(family.len()),
        production: ProductionCounts {
            triples_checked: TripleCount::from(
                usize::from(cache.checked()).saturating_sub(checked_before),
            ),
            cache_hits: CacheHitCount::from(usize::from(cache.hits()).saturating_sub(hits_before)),
            replayed_steps: ReplayStepCount::from(replayed),
        },
    })
}

impl<A: CellAlphabet> GuardedTemplate<A>
{
    /// The skeleton every member shares: the first member with its peak and
    /// join generalized.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn carrier(&self) -> &Tracelet<A>
    {
        &self.carrier
    }

    /// The entries, in the order the generalization met their points.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn entries(&self) -> &[TemplateEntry<A>]
    {
        &self.entries
    }

    /// The region's content address.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn region(&self) -> TemplateAddress
    {
        self.region
    }

    /// The template's size `s`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn size(&self) -> NodeCount
    {
        self.size
    }

    /// The plain size `F` of the family the template replaces.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn plain_size(&self) -> NodeCount
    {
        self.plain_size
    }

    /// The expansion factor `F / s`, rounded down.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn expansion_factor(&self) -> ExpansionFactor
    {
        ExpansionFactor::from(
            usize::from(self.plain_size)
                .checked_div(usize::from(self.size))
                .unwrap_or_default(),
        )
    }

    /// What the run that produced the template spent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn production(&self) -> ProductionCounts
    {
        self.production
    }

    /// The substitution under which the generalized peak is `peak`.
    ///
    /// # Specification
    /// - ensures: a substitution instantiating the generalized peak to `peak`,
    ///   binding every entry's metavariable to `peak`'s subterm at its point.
    /// - fails: [`TemplateObstruction::PeakNotAnInstance`] when the alphabet's
    ///   matcher refuses.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — every member's peak yields a substitution that
    ///   rebuilds the member. L3 — a peak of another shape is refused by name.
    /// - witness: `tests::template::every_member_admits_as_its_plain_replay`
    /// - witness: `tests::template::a_certificate_outside_the_template_is_refused_by_name`
    #[inline]
    pub fn peak_substitution(
        &self,
        peak: &A::Cmd,
    ) -> Result<A::Subst, TemplateObstruction>
    {
        let mut substitution = A::Subst::default();
        if bool::from(A::match_cmd(
            &self.carrier.overlap.peak,
            peak,
            &mut substitution,
        )) {
            Ok(substitution)
        }
        else {
            Err(TemplateObstruction::PeakNotAnInstance)
        }
    }

    /// The certificate the template holds for one choice of arms: the carrier
    /// with each entry's arm, chosen by `substitution`, put in place in its
    /// peak and its join.
    ///
    /// # Specification
    /// - ensures: for every entry, the arm whose binding equals `substitution`
    ///   restricted to the entry's metavariable, applied to the carrier's peak
    ///   and join; the carrier's paths and overlap otherwise unchanged. The
    ///   bodies put in place are the template's own arms.
    /// - fails: [`TemplateObstruction::UnboundEntry`] for the first entry
    ///   `substitution` leaves unbound;
    ///   [`TemplateObstruction::ArmOutsideTemplate`] for the first entry whose
    ///   bound body is not one of its arms.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — every member rebuilds to its own peak and join and
    ///   replays as its plain replay. L3 — a body outside the template and an
    ///   unbound entry are each refused by name.
    /// - witness: `tests::template::every_member_admits_as_its_plain_replay`
    /// - witness: `tests::template::a_certificate_outside_the_template_is_refused_by_name`
    #[inline]
    pub fn instantiate(
        &self,
        substitution: &A::Subst,
    ) -> Result<Tracelet<A>, TemplateObstruction>
    {
        let mut instance = self.carrier.clone();
        for (index, entry) in self.entries.iter().enumerate() {
            let bound = A::restrict_subst(substitution, core::slice::from_ref(&entry.var));
            if bound == A::Subst::default() {
                return Err(TemplateObstruction::UnboundEntry {
                    entry: EntryIndex::from(index),
                });
            }
            let arm = match entry.arms.get(&arm_address::<A>(&bound)) {
                | Some(arm) if arm.binding == bound => arm,
                | Some(_) | None => {
                    return Err(TemplateObstruction::ArmOutsideTemplate {
                        entry: EntryIndex::from(index),
                    });
                },
            };
            instance.overlap.peak = A::apply_subst(&arm.binding, &instance.overlap.peak);
            instance.joins_at = A::apply_subst(&arm.binding, &instance.joins_at);
        }
        Ok(instance)
    }

    /// Admits the certificate at `peak` through the template: rebuilds it and
    /// replays what was rebuilt.
    ///
    /// # Specification
    /// - ensures: [`Tracelet::replay`] over `store` of
    ///   [`GuardedTemplate::instantiate`] under
    ///   [`GuardedTemplate::peak_substitution`] of `peak`; no inheritance
    ///   verdict is consulted.
    /// - fails: as [`GuardedTemplate::peak_substitution`] and
    ///   [`GuardedTemplate::instantiate`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — every member of a generated family is admitted
    ///   exactly as its plain replay decides. L3 — under a cache seeded with a
    ///   lie, the member the lie covers is still refused.
    /// - witness: `tests::template::every_member_admits_as_its_plain_replay`
    /// - witness: `tests::template::a_poisoned_inheritance_entry_is_caught_at_admission`
    #[inline]
    pub fn admit(
        &self,
        peak: &A::Cmd,
        store: &CellStore<A>,
    ) -> Result<TraceletReplay, TemplateObstruction>
    {
        let substitution = self.peak_substitution(peak)?;
        Ok(self.instantiate(&substitution)?.replay(store))
    }

    /// The template's flow: the carrier's, the identity of the whole family.
    ///
    /// # Specification
    /// - ensures: [`tracelet_flow`] of the carrier over `store`.
    /// - fails: as [`tracelet_flow`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over the sequent alphabet, whose only command
    ///   position is the root, every member of an emitted family has the
    ///   template's flow on both legs.
    /// - witness: `tests::template::a_template_has_one_flow_for_its_family`
    #[inline]
    pub fn flow(
        &self,
        store: &CellStore<A>,
    ) -> Result<TraceletFlow<A>, FlowObstruction<A>>
    {
        tracelet_flow(&self.carrier, store)
    }

    /// The cost of `family` with this template and without.
    ///
    /// # Specification
    /// - ensures: the template's member count, sizes and expansion factor and
    ///   its production counts; the members of `family` it admits; and the
    ///   recorded steps of both legs of every member of `family`, which plain
    ///   replay of each would fire.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a 64-member family reports two checks per entry, the
    ///   remaining lookups as hits, every member admitted, and fewer steps
    ///   replayed than plain replay fires.
    /// - witness: `tests::template::the_inheritance_check_runs_once_per_distinct_triple`
    #[inline]
    #[must_use]
    pub fn cost_report(
        &self,
        family: &[Tracelet<A>],
        store: &CellStore<A>,
    ) -> FamilyCostReport
    {
        let admissions = family
            .iter()
            .filter(|member| matches!(self.admit(&member.overlap.peak, store), Ok(replay) if bool::from(replay)))
            .count();
        let plain_replayed_steps = family.iter().fold(0_usize, |total, member| {
            total
                .saturating_add(member.path_a.len())
                .saturating_add(member.path_b.len())
        });
        FamilyCostReport {
            members: self.members,
            plain_size: self.plain_size,
            template_size: self.size,
            expansion_factor: self.expansion_factor(),
            triples_checked: self.production.triples_checked,
            cache_hits: self.production.cache_hits,
            admissions: AdmissionCount::from(admissions),
            replayed_steps: self.production.replayed_steps,
            plain_replayed_steps: ReplayStepCount::from(plain_replayed_steps),
        }
    }
}
