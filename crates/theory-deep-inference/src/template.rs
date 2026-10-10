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

use anodized::spec;
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

impl TemplateAddress
{
    /// Address domain-specific certificate content within one run.
    ///
    /// # Specification
    /// - provides: a region-domain hash of domain-specific content. The address
    ///   is build-local and does not prove that two inputs are identical.
    /// - panics: only if the supplied `Hash` implementation panics.
    /// - executable: none — an opaque `Hash` implementation and a lossy digest
    ///   have no independent inverse predicate over the original content.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — changing a region or body must separate cached
    ///   verdicts in the finite corpus; this is not collision freedom.
    /// - witness: `template::tests::cache_transitions_keep_checks_hits_and_seeds_distinct`
    #[inline]
    pub fn of<T>(content: &T) -> Self
    where
        T: core::hash::Hash,
    {
        let mut hasher = ContentHasher::new();
        core::hash::Hasher::write(&mut hasher, REGION_DOMAIN);
        core::hash::Hash::hash(content, &mut hasher);
        Self(hasher.digest())
    }
}

impl ArmAddress
{
    /// Address a substitution body within one run.
    ///
    /// # Specification
    /// - provides: an arm-domain hash of substitution content. The address is
    ///   build-local and does not prove that two inputs are identical.
    /// - panics: only if the supplied `Hash` implementation panics.
    /// - executable: none — an opaque `Hash` implementation and a lossy digest
    ///   have no independent inverse predicate over the original content.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — changing a region or body must separate cached
    ///   verdicts in the finite corpus; this is not collision freedom.
    /// - witness: `template::tests::cache_transitions_keep_checks_hits_and_seeds_distinct`
    #[inline]
    pub fn of<T>(content: &T) -> Self
    where
        T: core::hash::Hash,
    {
        let mut hasher = ContentHasher::new();
        core::hash::Hasher::write(&mut hasher, ARM_DOMAIN);
        core::hash::Hash::hash(content, &mut hasher);
        Self(hasher.digest())
    }
}

/// Price any certificate family before inheritance replay.
///
/// # Specification
/// - ensures: succeeds exactly when s < floor(F / s); zero size is refused.
/// - fails: `DoesNotPay` retains both supplied sizes.
/// - panics: none.
///
/// # Errors
/// Returns `TemplateRefusal::DoesNotPay` at or above the strict boundary.
///
/// # Adequacy
/// - hypothesis: L3 — zero, equality and either side of the integer gate
///   distinguish division rounding and a weakened comparison.
/// - witness: `template::tests::price_boundary_is_strict`
#[spec(ensures: |output| output.is_ok() == usize::from(plain_size)
    .checked_div(usize::from(template_size))
    .is_some_and(|factor| usize::from(template_size) < factor))]
#[inline]
pub fn price_family(
    template_size: NodeCount,
    plain_size: NodeCount,
) -> Result<ExpansionFactor, TemplateRefusal>
{
    match usize::from(plain_size).checked_div(usize::from(template_size)) {
        | Some(factor) if usize::from(template_size) < factor => Ok(ExpansionFactor::from(factor)),
        | Some(_) | None => Err(TemplateRefusal::DoesNotPay {
            template_size,
            plain_size,
        }),
    }
}

/// Why the distinct-triple price cannot establish both strict bounds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MemoizedPriceRefusal
{
    /// Sizes, triple count and per-check cost must all be positive.
    EmptyCost,
    /// The supplied per-check bound exceeds the template's node bound.
    CheckExceedsTemplate,
    /// Machine arithmetic cannot represent the conservative charge.
    Overflow,
    /// Template storage plus distinct-triple work reaches the plain cost.
    DoesNotPay
    {
        /// Combined storage and check-work charge.
        charged: NodeCount,
        /// Plain family cost.
        plain_size: NodeCount,
    },
}

/// Price storage and cold-cache inheritance work without replacing the original
/// gate.
///
/// # Specification
/// - requires: `check_bound` bounds one inheritance check in the caller's
///   declared node-cost model; `triples` counts every distinct obligation
///   before replay.
/// - ensures: succeeds exactly when all costs are positive, c <= s, and s + T*c
///   < F with representable arithmetic. The result is s + T*c. Hence both s < F
///   and T*c < F hold strictly.
/// - fails: named zero-cost, invalid-bound, overflow or strict-price refusal.
/// - panics: none.
/// - intension: this price assumes a run-local memo that checks each triple at
///   most once; it discounts no triple merely because the cache is warm.
///
/// # Errors
/// Returns `MemoizedPriceRefusal` with the failed boundary.
///
/// # Adequacy
/// - hypothesis: L1/L3 — an independent widened-arithmetic observer checks both
///   inequalities; equality, invalid bounds and machine overflow refuse.
/// - witness: `template::tests::memoized_price_preserves_strict_storage_and_work_bounds`
#[spec(ensures: |output| {
    let s = usize::from(template_size);
    let c = usize::from(check_bound);
    let t = usize::from(triples);
    output.is_ok() == (s > 0 && c > 0 && t > 0 && c <= s
        && t.checked_mul(c).and_then(|work| s.checked_add(work))
            .is_some_and(|charged| charged < usize::from(plain_size)))
})]
#[inline]
pub fn price_family_memoized(
    template_size: NodeCount,
    plain_size: NodeCount,
    triples: TripleCount,
    check_bound: NodeCount,
) -> Result<NodeCount, MemoizedPriceRefusal>
{
    let s = usize::from(template_size);
    let c = usize::from(check_bound);
    let t = usize::from(triples);
    if s == 0 || c == 0 || t == 0 {
        return Err(MemoizedPriceRefusal::EmptyCost);
    }
    if c > s {
        return Err(MemoizedPriceRefusal::CheckExceedsTemplate);
    }
    let work = t.checked_mul(c).ok_or(MemoizedPriceRefusal::Overflow)?;
    let charged = s.checked_add(work).ok_or(MemoizedPriceRefusal::Overflow)?;
    if charged >= usize::from(plain_size) {
        return Err(MemoizedPriceRefusal::DoesNotPay {
            charged: NodeCount::from(charged),
            plain_size,
        });
    }
    Ok(NodeCount::from(charged))
}

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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — any cache key, including an absent key and a replaced
    ///   seed. Borrowed lookup, neighboring verdicts and counters separate
    ///   missed overwrites, fabricated presence and reads counted as hits.
    /// - witness: `template::tests::cache_transitions_keep_checks_hits_and_seeds_distinct`
    #[spec(ensures: |output| match output {
        Maybe::Present(verdict) => self.verdicts.get(key) == Some(verdict),
        Maybe::Absent(inheritance_lookup::Absent::Unchecked) => !self.verdicts.contains_key(key),
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh and occupied keys with positive or negative
    ///   seeds. The overwritten verdict, distinct-key count and unchanged
    ///   counters reject treating a seed as a check or retaining an earlier
    ///   verdict.
    /// - witness: `template::tests::cache_transitions_keep_checks_hits_and_seeds_distinct`
    #[spec(captures: [checked = self.checked, hits = self.hits], ensures:
        self.verdicts.get(&key) == Some(&verdict)
            && self.checked == checked && self.hits == hits)]
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
    ///   higher, saturating, when a verdict is held.
    /// - provides: [`inheritance_lookup::Absent::Unchecked`] when none is, the
    ///   counts unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — missing, seeded and checked entries. The returned
    ///   verdict and exact counter transitions distinguish an absent lookup
    ///   from a hit without counting either as a new check.
    /// - witness: `template::tests::cache_transitions_keep_checks_hits_and_seeds_distinct`
    #[spec(captures: [held = self.verdicts.get(key).copied(), checked = self.checked, hits = self.hits],
        ensures: |output| self.checked == checked
            && self.verdicts.get(key).copied() == held
            && usize::from(self.hits) == usize::from(hits).saturating_add(usize::from(held.is_some()))
            && match output {
                Maybe::Present(verdict) => held == Some(verdict),
                Maybe::Absent(inheritance_lookup::Absent::Unchecked) => held.is_none(),
            })]
    #[inline]
    pub fn lookup(
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
    ///   higher, saturating; the hit count is unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh checked key beside seeded keys. Its verdict,
    ///   the one-check increment, preserved hit count and later counted lookup
    ///   distinguish checks from seeds and cache hits.
    /// - witness: `template::tests::cache_transitions_keep_checks_hits_and_seeds_distinct`
    #[spec(captures: [checked = self.checked, hits = self.hits], ensures:
        self.verdicts.get(&key) == Some(&verdict) && self.hits == hits
            && usize::from(self.checked) == usize::from(checked).saturating_add(1))]
    #[inline]
    pub fn record_check(
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
/// - ensures: the saturating sum of the two boundary node counts and both
///   recorded path lengths.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — generated sequent and toy certificates. The independently
///   counted boundaries and recorded steps reject an omitted boundary, an
///   omitted leg or counting only one step per leg.
/// - witness: `tests::template::a_template_is_emitted_only_below_its_expansion_factor`
#[spec(ensures: |output| usize::from(output) == [
    usize::from(A::cmd_size(&tracelet.overlap.peak)),
    usize::from(A::cmd_size(&tracelet.joins_at)),
    tracelet.path_a.len(), tracelet.path_b.len(),
].into_iter().fold(0_usize, usize::saturating_add))]
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
///
/// # Adequacy
/// - hypothesis: L1 — lawful alphabets and carriers with shared paths but
///   varying bodies. The domain-framed content observer and cache reuse
///   separate omitted fields or domains from identical-region reuse; no
///   collision-freedom claim is made.
/// - witness: `tests::template::the_inheritance_check_runs_once_per_distinct_triple`
#[spec(ensures: |output| {
    let mut observer = ContentHasher::new();
    core::hash::Hasher::write(&mut observer, REGION_DOMAIN);
    core::hash::Hash::hash(&carrier.overlap.peak, &mut observer);
    core::hash::Hash::hash(&carrier.joins_at, &mut observer);
    core::hash::Hash::hash(&carrier.path_a, &mut observer);
    core::hash::Hash::hash(&carrier.path_b, &mut observer);
    output == TemplateAddress(observer.digest())
})]
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
///
/// # Adequacy
/// - hypothesis: L1 — substitution bodies from generated families, including
///   repeated and distinct arms. The domain-framed binding digest and
///   distinct-triple counts reject omitting the domain or body and treating
///   repeated arms as fresh; hashes are not assumed collision-free.
/// - witness: `tests::template::the_inheritance_check_runs_once_per_distinct_triple`
#[spec(ensures: |output| {
    let mut observer = ContentHasher::new();
    core::hash::Hasher::write(&mut observer, ARM_DOMAIN);
    core::hash::Hash::hash(binding, &mut observer);
    output == ArmAddress(observer.digest())
})]
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
///
/// # Adequacy
/// - hypothesis: L3 — complete, missing-cell, stopped and wrong-join replays of
///   the same carrier. First-leg verdicts and fired-step counts separate
///   skipping a leg, reversing refusal precedence and counting a refused step;
///   the predicate checks the verdict-dependent count bounds.
/// - witness: `tests::template::inheritance_refusals_preserve_leg_and_step_boundaries`
#[spec(ensures: |output| {
    let fired = usize::from(output.1);
    let left = carrier.path_a.len();
    let right = carrier.path_b.len();
    match output.0 {
        InheritanceVerdict::Inherited
        | InheritanceVerdict::MissesTheJoin { leg: TemplateLeg::PathB } => fired == left.saturating_add(right),
        InheritanceVerdict::MissesTheJoin { leg: TemplateLeg::PathA } => fired >= left && fired <= left.saturating_add(right),
        InheritanceVerdict::Stuck { leg: TemplateLeg::PathA, step, .. } => {
            let step = usize::from(step);
            step < left && fired >= step && fired <= step.saturating_add(right)
        },
        InheritanceVerdict::Stuck { leg: TemplateLeg::PathB, step, .. } => {
            let step = usize::from(step);
            step < right && fired == left.saturating_add(step)
        },
    }
})]
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
/// - hypothesis: L1 — generated sequent and toy families, including an
///   untrusted cache. Independent size sums and plain replay observe price and
///   admission; L3 — empty, divergent, discriminated and unshared families
///   separate refusal precedence, charging checks before price and admitting
///   stale evidence. Repeated 64- and 256-member families distinguish checks
///   from hits.
/// - witness: `tests::template::a_template_is_emitted_only_below_its_expansion_factor`
/// - witness: `tests::template::every_member_admits_as_its_plain_replay`
/// - witness: `tests::template::a_skeleton_divergent_family_yields_no_template`
/// - witness: `tests::template::an_entry_a_cell_discriminates_on_yields_no_template`
/// - witness: `tests::template::a_family_with_no_shared_content_yields_no_template`
/// - witness: `tests::template::the_inheritance_check_runs_once_per_distinct_triple`
/// - witness: `tests::template::a_poisoned_inheritance_entry_is_caught_at_admission`
/// - witness: `tests::template::empty_input_and_report_inputs_do_not_rewrite_production_counts`
#[spec(captures: [checked = cache.checked, hits = cache.hits], ensures: |output| {
    let unchanged = cache.checked == checked && cache.hits == hits;
    match family.split_first() {
        None => matches!(output, Err(TemplateRefusal::EmptyFamily)) && unchanged,
        Some((first, rest)) => {
            let divergence = rest.iter().position(|member| {
                member.overlap.left != first.overlap.left
                    || member.overlap.right != first.overlap.right
                    || member.overlap.kind != first.overlap.kind
                    || member.overlap.seam != first.overlap.seam
                    || member.path_a != first.path_a || member.path_b != first.path_b
            });
            if let Some(index) = divergence {
                matches!(output, Err(TemplateRefusal::SkeletonDivergence { member })
                    if usize::from(member) == index.saturating_add(1)) && unchanged
            } else {
                let plain = family.iter().fold(0_usize, |sum, member|
                    sum.saturating_add(usize::from(plain_size(member))));
                match output.as_ref() {
                    Ok(template) => {
                        let size = template.entries.iter().flat_map(|entry| entry.arms.values())
                            .fold(usize::from(plain_size(&template.carrier)), |sum, arm|
                                sum.saturating_add(usize::from(arm.size)).saturating_add(1));
                        usize::from(template.members) == family.len()
                            && usize::from(template.plain_size) == plain
                            && usize::from(template.size) == size
                            && plain.checked_div(size).is_some_and(|factor| size < factor)
                            && template.region == region_address(&template.carrier)
                            && template.carrier.overlap.left == first.overlap.left
                            && template.carrier.overlap.right == first.overlap.right
                            && template.carrier.overlap.kind == first.overlap.kind
                            && template.carrier.overlap.seam == first.overlap.seam
                            && template.carrier.overlap.unifier == first.overlap.unifier
                            && template.carrier.overlap.right_renamed() == first.overlap.right_renamed()
                            && template.carrier.path_a == first.path_a && template.carrier.path_b == first.path_b
                            && usize::from(template.production.triples_checked)
                                == usize::from(cache.checked).saturating_sub(usize::from(checked))
                            && usize::from(template.production.cache_hits)
                                == usize::from(cache.hits).saturating_sub(usize::from(hits))
                            && template.entries.iter().enumerate().all(|(index, entry)|
                                entry.arms.iter().all(|(body, arm)| {
                                    let key = InheritanceKey { region: template.region,
                                        entry: EntryIndex::from(index), body: *body };
                                    *body == arm_address::<A>(&arm.binding)
                                        && cache.verdicts.get(&key) == Some(&InheritanceVerdict::Inherited)
                                }))
                    },
                    Err(&TemplateRefusal::DoesNotPay { template_size, plain_size }) => {
                        let size = usize::from(template_size);
                        usize::from(plain_size) == plain && unchanged
                            && plain.checked_div(size).is_none_or(|factor| size >= factor)
                    },
                    Err(&TemplateRefusal::NotInherited { key, verdict }) =>
                        verdict != InheritanceVerdict::Inherited && cache.verdicts.get(&key) == Some(&verdict),
                    Err(&(TemplateRefusal::Ungeneralizable | TemplateRefusal::EntryOutsidePeak { .. }
                        | TemplateRefusal::ArmAddressCollision { .. })) => unchanged,
                    Err(&(TemplateRefusal::EmptyFamily | TemplateRefusal::SkeletonDivergence { .. })) => false,
                }
            }
        },
    }
})]
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
    price_family(NodeCount::from(size), NodeCount::from(plain))?;

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
    /// - hypothesis: L1 — generated family peaks rebuild through the returned
    ///   substitution; L3 — a different peak shape is refused by name. These
    ///   observers separate a wrong binding from accepting a failed match.
    /// - witness: `tests::template::every_member_admits_as_its_plain_replay`
    /// - witness: `tests::template::a_certificate_outside_the_template_is_refused_by_name`
    #[spec(ensures: |output| match output.as_ref() {
        Ok(substitution) => A::apply_subst(substitution, &self.carrier.overlap.peak) == *peak,
        Err(&TemplateObstruction::PeakNotAnInstance) => {
            let mut observer = A::Subst::default();
            !bool::from(A::match_cmd(&self.carrier.overlap.peak, peak, &mut observer))
        },
        Err(&(TemplateObstruction::UnboundEntry { .. } | TemplateObstruction::ArmOutsideTemplate { .. })) => false,
    })]
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
    /// - hypothesis: L1 — member substitutions reconstruct both boundaries and
    ///   preserve the recorded skeleton; L3 — absent bindings and external
    ///   bodies identify the first offending entry. Boundary, skeleton and
    ///   typed-refusal observers reject applying only to the peak, choosing
    ///   another arm or skipping an unbound entry.
    /// - witness: `tests::template::every_member_admits_as_its_plain_replay`
    /// - witness: `tests::template::a_certificate_outside_the_template_is_refused_by_name`
    #[spec(ensures: |output| {
        let expected = self.entries.iter().enumerate().try_fold(
            (self.carrier.overlap.peak.clone(), self.carrier.joins_at.clone()),
            |(peak, join), (index, entry)| {
                let bound = A::restrict_subst(substitution, core::slice::from_ref(&entry.var));
                if bound == A::Subst::default() {
                    return Err(TemplateObstruction::UnboundEntry { entry: EntryIndex::from(index) });
                }
                entry.arms.values().find(|arm| arm.binding == bound)
                    .ok_or_else(|| TemplateObstruction::ArmOutsideTemplate { entry: EntryIndex::from(index) })
                    .map(|arm| (A::apply_subst(&arm.binding, &peak), A::apply_subst(&arm.binding, &join)))
            });
        match (output.as_ref(), expected) {
            (Ok(instance), Ok((peak, join))) => instance.overlap.peak == peak && instance.joins_at == join
                && instance.path_a == self.carrier.path_a && instance.path_b == self.carrier.path_b
                && instance.overlap.left == self.carrier.overlap.left
                && instance.overlap.right == self.carrier.overlap.right
                && instance.overlap.kind == self.carrier.overlap.kind
                && instance.overlap.unifier == self.carrier.overlap.unifier
                && instance.overlap.seam == self.carrier.overlap.seam
                && instance.overlap.right_renamed() == self.carrier.overlap.right_renamed(),
            (Err(actual), Err(expected)) => *actual == expected,
            (Ok(_), Err(_)) | (Err(_), Ok(_)) => false,
        }
    })]
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
    /// - hypothesis: L1 — generated members are compared with plain replay. L3
    ///   — the deliberately poisoned cache still refuses its bad member. The
    ///   rebuilt-boundary and replay observers reject trusting a cached
    ///   verdict, omitting reconstruction or accepting a failed leg.
    /// - witness: `tests::template::every_member_admits_as_its_plain_replay`
    /// - witness: `tests::template::a_poisoned_inheritance_entry_is_caught_at_admission`
    #[spec(ensures: |output| output == self.peak_substitution(peak)
        .and_then(|substitution| self.instantiate(&substitution))
        .map(|instance| instance.replay(store)))]
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
    /// - hypothesis: L3 — generated sequent members, whose sole command
    ///   position is the root. Canonical port and incidence observers compare
    ///   both member legs with the carrier, rejecting projection of one leg
    ///   only or substitution-dependent family identity.
    /// - witness: `tests::template::a_template_has_one_flow_for_its_family`
    #[spec(ensures: |output| output == tracelet_flow(&self.carrier, store))]
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
    ///   recorded steps of both legs of every member of `family`, regardless of
    ///   whether its replay would finish.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — full, empty, singleton and external-body report
    ///   inputs for one produced template. Exact stored production counters,
    ///   admission counts and recorded path lengths reject recomputing
    ///   production from the report input or counting an obstructed peak as
    ///   admitted.
    /// - witness: `tests::template::the_inheritance_check_runs_once_per_distinct_triple`
    /// - witness: `tests::template::empty_input_and_report_inputs_do_not_rewrite_production_counts`
    #[spec(ensures: |output| (
        output.members, output.plain_size, output.template_size, output.expansion_factor,
        output.triples_checked, output.cache_hits, output.replayed_steps,
    ) == (
        self.members, self.plain_size, self.size, self.expansion_factor(),
        self.production.triples_checked, self.production.cache_hits, self.production.replayed_steps,
    )
        && usize::from(output.admissions) == family.iter().filter(|member|
            self.admit(&member.overlap.peak, store).is_ok_and(bool::from)).count()
        && usize::from(output.plain_replayed_steps) == family.iter().fold(0_usize, |sum, member|
            sum.saturating_add(member.path_a.len()).saturating_add(member.path_b.len())))]
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

#[cfg(test)]
mod tests
{
    #[test]
    fn price_boundary_is_strict()
    {
        for size in 0_usize ..= 16 {
            for plain in 0_usize ..= 300 {
                let expected =
                    size > 0 && plain.checked_div(size).is_some_and(|factor| size < factor);
                assert_eq!(
                    super::price_family(
                        super::NodeCount::from(size),
                        super::NodeCount::from(plain)
                    )
                    .is_ok(),
                    expected
                );
            }
        }
    }

    #[test]
    fn memoized_price_preserves_strict_storage_and_work_bounds()
    {
        use super::MemoizedPriceRefusal;
        use super::NodeCount;
        use super::TripleCount;
        use super::price_family_memoized;
        for s in 0_usize ..= 16 {
            for c in 0_usize ..= 16 {
                for t in 0_usize ..= 8 {
                    for f in 0_usize ..= 128 {
                        let total = u128::try_from(s).unwrap()
                            + u128::try_from(t).unwrap() * u128::try_from(c).unwrap();
                        let expected =
                            s > 0 && c > 0 && t > 0 && c <= s && total < u128::try_from(f).unwrap();
                        let result = price_family_memoized(
                            NodeCount::from(s),
                            NodeCount::from(f),
                            TripleCount::from(t),
                            NodeCount::from(c),
                        );
                        assert_eq!(result.is_ok(), expected);
                        if let Ok(charged) = result {
                            assert_eq!(u128::try_from(usize::from(charged)).unwrap(), total);
                            assert!(s < f && t * c < f);
                        }
                    }
                }
            }
        }
        assert_eq!(
            price_family_memoized(
                NodeCount::from(63),
                NodeCount::from(1116),
                TripleCount::from(8),
                NodeCount::from(63)
            ),
            Ok(NodeCount::from(567))
        );
        assert!(super::price_family(NodeCount::from(63), NodeCount::from(1116)).is_err());
        assert_eq!(
            price_family_memoized(
                NodeCount::from(4),
                NodeCount::from(12),
                TripleCount::from(2),
                NodeCount::from(4)
            ),
            Err(MemoizedPriceRefusal::DoesNotPay {
                charged: NodeCount::from(12),
                plain_size: NodeCount::from(12)
            })
        );
        assert_eq!(
            price_family_memoized(
                NodeCount::from(1),
                NodeCount::from(9),
                TripleCount::from(1),
                NodeCount::from(2)
            ),
            Err(MemoizedPriceRefusal::CheckExceedsTemplate)
        );
        assert_eq!(
            price_family_memoized(
                NodeCount::from(usize::MAX),
                NodeCount::from(usize::MAX),
                TripleCount::from(2),
                NodeCount::from(usize::MAX)
            ),
            Err(MemoizedPriceRefusal::Overflow)
        );
    }

    use super::ArmAddress;
    use super::EntryIndex;
    use super::InheritanceCache;
    use super::InheritanceKey;
    use super::InheritanceVerdict;
    use super::LegStepIndex;
    use super::Maybe;
    use super::StuckStep;
    use super::TemplateAddress;
    use super::TemplateLeg;

    #[test]
    fn cache_transitions_keep_checks_hits_and_seeds_distinct()
    {
        let seeded = InheritanceKey {
            region: TemplateAddress::of(&0_u64),
            entry: EntryIndex::from(0),
            body: ArmAddress::of(&0_u64),
        };
        let neighbor = InheritanceKey {
            region: TemplateAddress::of(&1_u64),
            ..seeded
        };
        let checked = InheritanceKey {
            body: ArmAddress::of(&1_u64),
            ..seeded
        };
        let missing = InheritanceKey {
            region: neighbor.region,
            body: checked.body,
            ..seeded
        };
        let negative = InheritanceVerdict::MissesTheJoin {
            leg: TemplateLeg::PathA,
        };
        let stopped = InheritanceVerdict::Stuck {
            leg: TemplateLeg::PathB,
            step: LegStepIndex::from(0),
            reason: StuckStep::UnissuedCell,
        };
        let mut cache = InheritanceCache::new();
        assert!(matches!(cache.lookup(&missing), Maybe::Absent(_)));
        cache.record(seeded, negative);
        cache.record(neighbor, InheritanceVerdict::Inherited);
        assert_eq!(
            (usize::from(cache.checked), usize::from(cache.hits)),
            (0, 0)
        );
        assert_eq!(cache.get(&seeded), Maybe::Present(&negative));
        assert_eq!(usize::from(cache.hits), 0);
        assert_eq!(cache.lookup(&seeded), Maybe::Present(negative));
        cache.record(seeded, InheritanceVerdict::Inherited);
        assert_eq!(
            (
                cache.verdicts.len(),
                usize::from(cache.checked),
                usize::from(cache.hits)
            ),
            (2, 0, 1)
        );
        cache.record_check(checked, stopped);
        assert_eq!(
            (
                cache.verdicts.len(),
                usize::from(cache.checked),
                usize::from(cache.hits)
            ),
            (3, 1, 1)
        );
        assert_eq!(cache.lookup(&checked), Maybe::Present(stopped));
        assert!(matches!(cache.lookup(&missing), Maybe::Absent(_)));
        assert_eq!(
            (usize::from(cache.checked), usize::from(cache.hits)),
            (1, 2)
        );
        assert_eq!(
            cache.get(&seeded),
            Maybe::Present(&InheritanceVerdict::Inherited)
        );
        assert_eq!(
            cache.get(&neighbor),
            Maybe::Present(&InheritanceVerdict::Inherited)
        );
        assert_eq!(cache.get(&checked), Maybe::Present(&stopped));
        assert!(matches!(cache.get(&missing), Maybe::Absent(_)));
        let missing_entry = InheritanceKey {
            entry: EntryIndex::from(1),
            ..seeded
        };
        assert!(matches!(cache.get(&missing_entry), Maybe::Absent(_)));
    }
}
