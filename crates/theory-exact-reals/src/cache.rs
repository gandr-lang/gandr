//! The checked-result cache: the certificate of each settled obligation,
//! under an exact key.
//!
//! A [`Cache`] holds the certificate of each settled obligation that a run
//! records. Its key is the canonical bytes of the plan that the obligation's
//! node roots, and the demand. Two plans that hold the same subterm share its
//! entry, whatever position the subterm takes in each. An entry holds its
//! certificate with its nodes moved to the positions of the rooted plan, so a
//! hit reads no bytes.
//!
//! A hit is evidence and never a verdict. [`Cache::lookup`] moves the stored
//! certificate to the positions of the plan that asks, and it replays the
//! certificate in [`crate::certificate::check`] before it hands it back.
//! [`Cache::store`] replays a certificate too, so the cache holds checked
//! results alone. An entry whose replay fails leaves the cache, and its
//! [`CacheRefusal`] names why. The cache never holds a suspension, a
//! cancellation or an exhausted budget.
//!
//! A cache holds at most its [`CacheBound`] of entries. Past the bound it
//! evicts its oldest entry, which changes the work of a later run and never
//! its outcome.
//!
//! # Items
//!
//! - [`Cache`], [`CacheBound`] — the cache and its bound.
//! - [`Lookup`], [`CacheRefusal`] — what a lookup gives, and why an entry
//!   leaves.
//! - [`CacheTally`] — the hits, the misses, the refusals and the evictions.

use alloc::collections::VecDeque;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::fmt;
use core::num::NonZeroUsize;

use foldhash::fast::FixedState;
use hashbrown::Equivalent;
use hashbrown::HashMap;
use num_bigint::BigInt;

use crate::certificate::Certificate;
use crate::certificate::CertificateRefusal;
use crate::certificate::CheckerQuotas;
use crate::certificate::Conclusion;
use crate::certificate::FormatVersion;
use crate::certificate::check;
use crate::dyadic::Dyadic;
use crate::dyadic::Precision;
use crate::dyadic::Rounding;
use crate::interval::Endpoint;
use crate::plan::NodeId;
use crate::plan::PlanError;
use crate::semidecision::Demand;
use crate::semidecision::Obligation;
use crate::validate::ValidatedPlan;

/// The most entries that a cache holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CacheBound(NonZeroUsize);

impl From<NonZeroUsize> for CacheBound
{
    /// The bound of `entries` entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(entries: NonZeroUsize) -> Self
    {
        return Self(entries);
    }
}

/// Why a cache entry leaves the cache, or why a certificate does not enter
/// it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CacheRefusal
{
    /// The obligation's node roots no plan.
    Plan(PlanError),
    /// A step names a node outside the plan that the obligation's node roots.
    Foreign,
    /// The certificate does not replay against the plan that asks.
    Replay(CertificateRefusal),
    /// The certificate concludes another judgement than the obligation asks
    /// for.
    Mismatch,
}

impl fmt::Display for CacheRefusal
{
    /// Write the refusal as one line.
    ///
    /// # Specification
    /// - ensures: writes one line per variant, a replay's refusal after its
    ///   phrase.
    /// - fails: passes the formatter's own write failure on unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant renders a distinct phrase.
    /// - witness: `tests::cache::refusals_render_distinct_phrases`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        return match *self {
            Self::Plan(error) => write!(f, "the obligation's node roots no plan: {error}"),
            Self::Foreign => f.write_str("a step names a node outside the rooted plan"),
            Self::Replay(refusal) => write!(f, "the cached certificate does not replay: {refusal}"),
            Self::Mismatch => {
                f.write_str("the certificate concludes another judgement than the obligation asks")
            },
        };
    }
}

impl core::error::Error for CacheRefusal
{
}

/// What a lookup gives.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Lookup
{
    /// The stored certificate, at the positions of the plan that asks, which
    /// replays to the evidence that the obligation asks for.
    Hit(Certificate),
    /// The cache holds no entry for the obligation.
    Miss,
    /// The entry left the cache, for the reason named.
    Refused(CacheRefusal),
}

/// The counts of a cache's work since it was made.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct CacheTally
{
    /// Lookups that gave a certificate.
    pub hits: u64,
    /// Lookups that found no entry.
    pub misses: u64,
    /// Entries that left the cache because they did not replay.
    pub refusals: u64,
    /// Entries that left the cache past its bound.
    pub evictions: u64,
    /// Entries that the cache holds now.
    pub held: u64,
}

/// The exact key of an entry.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Key
{
    /// The canonical bytes of the plan that the obligation's node roots.
    plan: Rc<[u8]>,
    /// The demand.
    demand: Demand,
}

/// A key borrowed for a lookup, which hashes as the key it equals.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Probe<'bytes>
{
    /// The canonical bytes of the rooted plan.
    plan: &'bytes [u8],
    /// The demand.
    demand: Demand,
}

impl Equivalent<Key> for Probe<'_>
{
    /// Whether the probe names `key`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn equivalent(
        &self,
        key: &Key,
    ) -> bool
    {
        return *self.plan == *key.plan && self.demand == key.demand;
    }
}

/// The checked-result cache.
///
/// # Specification
/// - invariant: each entry's certificate replays against its rooted plan to the
///   evidence that its demand asks for. The order holds each key of the entries
///   once, the oldest first, and the entries number at most the bound.
#[derive(Clone, Debug)]
pub struct Cache
{
    /// The entries, by key.
    entries: HashMap<Key, Certificate, FixedState>,
    /// The keys of the entries, the oldest first.
    order: VecDeque<Key>,
    /// The most entries that the cache holds.
    bound: CacheBound,
    /// The counts of the cache's work.
    tally: CacheTally,
}

impl Cache
{
    /// An empty cache that holds at most `bound` entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(bound: CacheBound) -> Self
    {
        return Self {
            entries: HashMap::default(),
            order: VecDeque::new(),
            bound,
            tally: CacheTally::default(),
        };
    }

    /// The counts of the cache's work, and the entries that it holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn tally(&self) -> CacheTally
    {
        return CacheTally {
            held: u64::try_from(self.entries.len()).unwrap_or(u64::MAX),
            ..self.tally
        };
    }

    /// The certificate that the cache holds for `obligation` over `plan`,
    /// replayed within `quotas`.
    ///
    /// # Specification
    /// - ensures: a hit is a certificate at the positions of `plan` that
    ///   [`crate::certificate::check`] replays to the evidence that the
    ///   obligation asks for. A miss leaves the cache as it was.
    /// - fails: an entry that names a node outside the rooted plan, does not
    ///   replay, or concludes another judgement leaves the cache, and the
    ///   lookup names the refusal.
    /// - panics: none.
    /// - executable: none — the clause speaks of the certificate's replay.
    /// - intension: one walk of the nodes that the obligation's node reaches,
    ///   one hash of their canonical bytes, and one replay on a hit.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every obligation of the machine's test corpus answers
    ///   alike from the cache and from a run. L3 — a hit in another plan that
    ///   holds the same subterm, a miss, and an entry that a narrower quota
    ///   refuses.
    /// - witness: `tests::cache::the_corpus_answers_alike_cached_and_uncached`
    /// - witness: `tests::cache::an_entry_that_does_not_replay_leaves_by_name`
    #[inline]
    pub fn lookup(
        &mut self,
        plan: &ValidatedPlan,
        obligation: Obligation,
        quotas: &CheckerQuotas,
    ) -> Lookup
    {
        let (rooted, origin) = match plan.plan().rooted(obligation.node()) {
            Ok(rooted) => rooted,
            Err(error) => return Lookup::Refused(CacheRefusal::Plan(error)),
        };
        let bytes = rooted.encode();
        let probe = Probe {
            plan: bytes.as_ref(),
            demand: obligation.demand(),
        };
        let Some(stored) = self.entries.get(&probe)
        else {
            self.tally.misses = self.tally.misses.saturating_add(1);
            return Lookup::Miss;
        };
        let answer =
            moved(stored, |id| origin.get(usize::from(id)).copied()).and_then(|certificate| {
                answers(plan, obligation, &certificate, quotas)?;
                return Ok(certificate);
            });
        return match answer {
            Ok(certificate) => {
                self.tally.hits = self.tally.hits.saturating_add(1);
                Lookup::Hit(certificate)
            },
            Err(refusal) => {
                let _removed = self.entries.remove(&probe);
                self.order.retain(|held| !probe.equivalent(held));
                self.tally.refusals = self.tally.refusals.saturating_add(1);
                Lookup::Refused(refusal)
            },
        };
    }

    /// Store `certificate`, the evidence that `obligation` over `plan` asks
    /// for, once it replays within `quotas`.
    ///
    /// # Specification
    /// - ensures: the cache holds the certificate under the key of the plan
    ///   that the obligation's node roots and of its demand, its nodes at that
    ///   plan's positions. A key that the cache holds already takes the new
    ///   certificate. Past its bound the cache evicts its oldest entries.
    /// - fails: refuses a certificate that does not replay, that concludes
    ///   another judgement, or that names a node outside the rooted plan, and
    ///   leaves the cache as it was.
    /// - panics: none.
    /// - executable: none — the clause speaks of the certificate's replay.
    /// - intension: one replay, one walk of the rooted plan's nodes, one table
    ///   of `plan`'s positions, and one copy of the certificate.
    ///
    /// # Errors
    /// - [`CacheRefusal`]: the certificate is no checked evidence for the
    ///   obligation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every certificate of the machine's test corpus enters
    ///   and answers its obligation again. L3 — a certificate of another
    ///   obligation, and the eviction of the oldest entry past the bound.
    /// - witness: `tests::cache::the_corpus_answers_alike_cached_and_uncached`
    /// - witness: `tests::cache::the_oldest_entry_leaves_past_the_bound`
    #[inline]
    pub fn store(
        &mut self,
        plan: &ValidatedPlan,
        obligation: Obligation,
        certificate: &Certificate,
        quotas: &CheckerQuotas,
    ) -> Result<(), CacheRefusal>
    {
        answers(plan, obligation, certificate, quotas)?;
        let (rooted, origin) = plan
            .plan()
            .rooted(obligation.node())
            .map_err(CacheRefusal::Plan)?;
        let mut place: Vec<Option<NodeId>> =
            alloc::vec![None; usize::from(plan.plan().node_count())];
        for (index, &id) in origin.iter().enumerate() {
            let fresh = NodeId::try_from(index).map_err(CacheRefusal::Plan)?;
            let slot = place
                .get_mut(usize::from(id))
                .ok_or(CacheRefusal::Foreign)?;
            *slot = Some(fresh);
        }
        let local = moved(certificate, |id| {
            place.get(usize::from(id)).copied().flatten()
        })?;
        let key = Key {
            plan: Rc::from(rooted.encode().as_ref()),
            demand: obligation.demand(),
        };
        if self.entries.insert(key.clone(), local).is_none() {
            self.order.push_back(key);
        }
        while self.entries.len() > self.bound.0.get() {
            let Some(oldest) = self.order.pop_front()
            else {
                break;
            };
            if self.entries.remove(&oldest).is_some() {
                self.tally.evictions = self.tally.evictions.saturating_add(1);
            }
        }
        return Ok(());
    }
}

/// The certificate with each node that it names moved by `rename`.
///
/// # Specification
/// - ensures: a certificate in the same format, each step moved by
///   [`crate::certificate::Step::renamed`].
/// - fails: refuses a step whose node `rename` has no place for as
///   [`CacheRefusal::Foreign`].
/// - panics: none.
/// - executable: none — the clause restates the move.
///
/// # Errors
/// - [`CacheRefusal::Foreign`]: a step names a node outside the map.
///
/// # Adequacy
/// - hypothesis: L2 — every certificate of the corpus moves to its rooted plan
///   and back to itself.
/// - witness: `tests::cache::a_certificate_moves_to_the_rooted_plan_and_back`
fn moved<Rename>(
    certificate: &Certificate,
    rename: Rename,
) -> Result<Certificate, CacheRefusal>
where
    Rename: Fn(NodeId) -> Option<NodeId>,
{
    let steps = certificate
        .steps()
        .iter()
        .map(|step| step.renamed(&rename).ok_or(CacheRefusal::Foreign))
        .collect::<Result<Vec<_>, CacheRefusal>>()?;
    return Ok(Certificate::new(FormatVersion::CURRENT, steps));
}

/// Check that `certificate` replays against `plan` within `quotas` to the
/// evidence that `obligation` asks for.
///
/// # Specification
/// - ensures: succeeds when the replay concludes that the node holds or fails
///   as asked, or encloses the node no wider than the width asked.
/// - fails: refuses a certificate that does not replay as
///   [`CacheRefusal::Replay`], and one that concludes another judgement as
///   [`CacheRefusal::Mismatch`].
/// - panics: none.
/// - executable: none — the clause speaks of the certificate's replay.
///
/// # Errors
/// - [`CacheRefusal::Replay`]: the certificate does not replay.
/// - [`CacheRefusal::Mismatch`]: it concludes another judgement.
///
/// # Adequacy
/// - hypothesis: L3 — a certificate of each demand, one of another node, and
///   one that a narrower quota refuses.
/// - witness: `tests::cache::an_entry_that_does_not_replay_leaves_by_name`
/// - witness: `tests::cache::the_corpus_answers_alike_cached_and_uncached`
fn answers(
    plan: &ValidatedPlan,
    obligation: Obligation,
    certificate: &Certificate,
    quotas: &CheckerQuotas,
) -> Result<(), CacheRefusal>
{
    let checked = check(plan, certificate, quotas).map_err(CacheRefusal::Replay)?;
    let node = obligation.node();
    let answered = match (checked.conclusion(), obligation.demand()) {
        (&Conclusion::Holds { open }, Demand::Holds)
        | (&Conclusion::Fails { open }, Demand::Fails) => open == node,
        (&Conclusion::Encloses { real, ref interval }, Demand::Encloses { width }) => {
            real == node
                && gap(interval)
                    .zip(Dyadic::new(BigInt::from(1_u8), width).ok())
                    .is_some_and(|(gap, target)| gap <= target)
        },
        (
            &(Conclusion::Holds { .. } | Conclusion::Fails { .. } | Conclusion::Encloses { .. }),
            _,
        ) => false,
    };
    if answered {
        return Ok(());
    }
    return Err(CacheRefusal::Mismatch);
}

/// The exact width of `interval`, or `None` for an infinite end.
///
/// # Specification
/// trivial.
fn gap(interval: &crate::interval::NumericInterval) -> Option<Dyadic>
{
    let (&Endpoint::Finite(ref lower), &Endpoint::Finite(ref upper)) =
        (&interval.lower().endpoint, &interval.upper().endpoint)
    else {
        return None;
    };
    return upper
        .sub(lower, Precision::MAX, Rounding::Ceiling)
        .ok()
        .map(crate::dyadic::Rounded::into_value);
}
