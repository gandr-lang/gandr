//! The kernel verdicts a process recalls and records.
//!
//! A driver that keeps the kernel's verdicts installs one [`VerdictCache`]
//! before its walk: the policy naming whose receipts it believes, where
//! receipts are read from and kept, and the key this installation signs with.
//! Every readmission the composition makes then admits under the cache's
//! recall, and one that crossed whole has the kernel sign what it checked and
//! keeps the receipt. `gandr check` keeps its receipts in a store on disk,
//! which a later process reads ([`VerdictCache::new`]). The language server
//! and the hub keep them in the same store and in the process
//! ([`VerdictCache::lasting`]). So a later readmission of the process reads
//! them, and a later process reads them from the store. A server that finds no
//! store keeps them in the process alone ([`VerdictCache::held`]). A process
//! that installs none — the sweeps, `gandr check --recheck`, every test —
//! rechecks every declaration.
//!
//! # Eviction
//!
//! No policy evicts a receipt from the store. The store grows by one receipt
//! for each readmission that checks a declaration. That receipt holds at most
//! two records for each declaration it checked, one under each key the
//! admission has. A process reads every receipt when it opens the store, so
//! the time of the open and the memory of the index are linear in the records
//! that the store holds (#6734). The operator evicts every receipt when they
//! remove the cache directory's `receipts`. The receipts that a process keeps
//! after the open keep to the bound of [`crate::held`]: past 65,536 records,
//! the oldest receipt goes from the process, and the store still holds it.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — tests and audits run under the full re-check, so
//!   only a cache a driver installs recalls; a recalled verdict is the kernel's
//!   own, under its whole input.

use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use core::fmt;
use core::num::NonZeroUsize;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::sync::LazyLock;
use std::sync::OnceLock;

use gandr_core_checker::Polled;
use gandr_core_checker::Retirement;
use gandr_core_checker::bridge;
use gandr_core_term::CoreArena;
use gandr_kernel_core::fork::SharedFork;
use gandr_kernel_core::speculation::Speculation;
use gandr_kernel_core::verdict::KernelIdentity;
use gandr_kernel_core::verdict::KernelSigner;
use gandr_kernel_core::verdict::StoredReceipt;
use gandr_kernel_core::verdict::TrustPolicy;
use gandr_kernel_core::verdict::VerdictKey;
use gandr_kernel_core::verdict::VerdictSource;
use quenchant_shape::shape::Maybe;

use crate::compose::Reuse;
use crate::entry::report::SourceCount;
use crate::held::Held;
use crate::held::HeldVerdicts;
use crate::pool::Pool;
use crate::receipts::StoredVerdicts;
use crate::walk::Walk;
use crate::width::Threads;
use crate::width::Width;

/// The recall of a process that installed no cache.
static RECHECK: LazyLock<bridge::Recall> = LazyLock::new(bridge::Recall::recheck);

/// The cache this process installed.
// economy: one cache per process, read where every readmission funnels; a
// host that needs two at once (the language server's background kernel)
// threads one through the composition's admission instead.
static INSTALLED: OnceLock<VerdictCache> = OnceLock::new();

/// The fork this process installed for the obligations of each kernel check.
// economy: one fork per process, read where every readmission funnels, as
// the verdict cache is. #2802 threads the fork through the admission when
// the frames of a check fork.
static FORKING: OnceLock<SharedFork> = OnceLock::new();

/// The speculation group this process installed for each readmission.
// One group for each process: the driver sets it by the kind of run, and it
// is read where every readmission funnels, as the fork is.
static SPECULATION: OnceLock<Speculation> = OnceLock::new();

/// The pool this process installed for the checks of each readmission.
// One pool for each process: the checks of every readmission share the
// threads of the process, read where every readmission funnels.
static SCHEDULING: OnceLock<Arc<Pool>> = OnceLock::new();

/// The pool of a process that installed none: one thread, so each
/// readmission runs each check on the calling thread.
static SERIAL: Pool = Pool::new(Width::SERIAL);

/// Where a cache keeps the receipts its kernel signs, and reads them from.
#[derive(Debug)]
enum Kept
{
    /// A store on disk, which a later process reads at open.
    Stored(Arc<StoredVerdicts>),
    /// The process's own source, which a later readmission of the process
    /// reads.
    Held(HeldVerdicts),
    /// A store on disk, which a later process reads at open, and the
    /// receipts kept after the open, which a later readmission of the process
    /// reads.
    Lasting
    {
        /// The store, with the receipts it read at open.
        store: Arc<StoredVerdicts>,
        /// The receipts this process kept after the open.
        held: HeldVerdicts,
    },
}

/// The receipts a readmission under a lasting cache recalls from: those the
/// process kept after the store opened, and those the store read at open.
///
/// # Specification
/// - ensures: [`VerdictSource::receipts`] answers, for a key, the receipts the
///   process held when the readmission started whose records hold it, or else
///   those the store read at open.
/// - executable: none — a pair of sources; each one's answer is its own.
///
/// # Adequacy
/// - hypothesis: L3 — as [`VerdictCache`].
/// - witness: `verdicts::tests::a_lasting_cache_recalls_its_own_and_the_store_s_6623`
#[derive(Debug)]
struct Layered
{
    /// The receipts the process kept after the open, as the readmission
    /// found them.
    held: Arc<Held>,
    /// The store, with the receipts it read at open.
    store: Arc<StoredVerdicts>,
}

impl VerdictSource for Layered
{
    /// The receipts the process kept whose records hold `key`, or else those
    /// the store read at open: any one of them attests the same record.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn receipts(
        &self,
        key: VerdictKey,
    ) -> &[Arc<StoredReceipt>]
    {
        let held = self.held.receipts(key);
        if held.is_empty() {
            self.store.receipts(key)
        }
        else {
            held
        }
    }
}

/// Where a process's kernel verdicts are recalled from and recorded to.
///
/// # Specification
/// - ensures: installed, every readmission admits under the cache's policy and
///   source, and each one that crossed whole keeps the receipt its kernel signs
///   for what it checked; the next readmission of a held or a lasting cache
///   reads that receipt, and a later cache over the same store reads it from
///   the store.
/// - executable: none — the store and the counts are shared state.
///
/// # Adequacy
/// - hypothesis: L3 — a module readmitted under one cache records what its
///   kernel checked, and readmitted under a second over the same store recalls
///   each of those declarations, to the same outcomes; readmitted twice under
///   one held or lasting cache, it recalls them the second time.
/// - witness: `verdicts::tests::a_second_cache_recalls_what_the_first_recorded_2799`
/// - witness: `verdicts::tests::a_held_cache_recalls_what_its_process_recorded_6566`
/// - witness: `verdicts::tests::a_lasting_cache_recalls_its_own_and_the_store_s_6623`
#[derive(Debug)]
pub struct VerdictCache
{
    /// Whose receipts a readmission believes.
    policy: TrustPolicy,
    /// Where receipts are kept and read.
    kept: Kept,
    /// This installation's key.
    signer: KernelSigner,
    /// Admissions a recorded verdict answered.
    recalled: AtomicUsize,
    /// Admissions whose verdicts a kept receipt holds, each once whatever
    /// number of keys it is kept under.
    recorded: AtomicUsize,
    /// Receipts the store could not keep.
    unwritten: AtomicUsize,
}

impl VerdictCache
{
    /// The cache believing the receipts `policy` trusts from `store`, and
    /// signing with `signer`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        policy: TrustPolicy,
        store: StoredVerdicts,
        signer: KernelSigner,
    ) -> Self
    {
        Self::keeping(policy, Kept::Stored(Arc::new(store)), signer)
    }

    /// The cache of a process with no store on disk: it believes the receipts
    /// `signer` gives alone, and keeps them in the process.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn held(signer: KernelSigner) -> Self
    {
        Self::keeping(
            TrustPolicy::Trusted(BTreeSet::from([signer.identity()])),
            Kept::Held(HeldVerdicts::default()),
            signer,
        )
    }

    /// The cache of a process that readmits many times over its life, a
    /// language server or a hub. It believes the receipts `policy` trusts from
    /// `store` and from what the process kept after the open. It keeps each
    /// receipt it signs with `signer` in both.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn lasting(
        policy: TrustPolicy,
        store: StoredVerdicts,
        signer: KernelSigner,
    ) -> Self
    {
        Self::keeping(
            policy,
            Kept::Lasting {
                store: Arc::new(store),
                held: HeldVerdicts::default(),
            },
            signer,
        )
    }

    /// The cache under `policy`, keeping receipts in `kept`, signing with
    /// `signer`.
    ///
    /// # Specification
    /// trivial.
    fn keeping(
        policy: TrustPolicy,
        kept: Kept,
        signer: KernelSigner,
    ) -> Self
    {
        Self {
            policy,
            kept,
            signer,
            recalled: AtomicUsize::new(0),
            recorded: AtomicUsize::new(0),
            unwritten: AtomicUsize::new(0),
        }
    }

    /// The recall a readmission that starts now admits under: the cache's
    /// policy over its store, over the receipts the process holds now, or over
    /// both.
    ///
    /// # Specification
    /// trivial.
    fn recall(&self) -> bridge::Recall
    {
        let source: Arc<dyn VerdictSource> = match self.kept {
            Kept::Stored(ref store) => Arc::<StoredVerdicts>::clone(store),
            Kept::Held(ref held) => held.snapshot(),
            Kept::Lasting {
                ref store,
                ref held,
            } => Arc::new(Layered {
                held: held.snapshot(),
                store: Arc::clone(store),
            }),
        };
        bridge::Recall::trusting(self.policy.clone(), source)
            .forking(forking())
            .speculating(speculation())
    }

    /// Count what `readmission` recalled, and keep the receipt for what it
    /// checked.
    ///
    /// # Specification
    /// trivial.
    fn settle(
        &self,
        readmission: &bridge::Readmission,
    )
    {
        let environment = readmission.environment();
        let _before = self
            .recalled
            .fetch_add(usize::from(environment.recalls()), Ordering::Relaxed);
        if let Maybe::Present(receipt) = environment.receipt(&self.signer) {
            let records = usize::from(environment.recorded());
            let kept = match self.kept {
                Kept::Stored(ref store) => store.keep(&receipt).is_ok(),
                Kept::Held(ref held) => {
                    held.keep(receipt);
                    true
                },
                Kept::Lasting {
                    ref store,
                    ref held,
                } => {
                    // The process recalls the receipt even when the store
                    // cannot keep it, and the tally counts it unwritten.
                    let written = store.keep(&receipt).is_ok();
                    held.keep(receipt);
                    written
                },
            };
            let _before = if kept {
                self.recorded.fetch_add(records, Ordering::Relaxed)
            }
            else {
                self.unwritten.fetch_add(1, Ordering::Relaxed)
            };
        }
    }

    /// The readmission that `reuse` asks for under this cache's recall,
    /// timing each admission by `stopwatch`, settling a whole readmission into
    /// the cache.
    ///
    /// # Specification
    /// - ensures: the readmission [`readmit_as`] gives under the cache's policy
    ///   over its source as it stands now; a whole one adds what it recalled to
    ///   the tally, and the cache keeps the receipt its kernel signs for what
    ///   it checked.
    /// - panics: none.
    /// - executable: none — the store and the counts are shared state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`VerdictCache`].
    /// - witness: `verdicts::tests::a_second_cache_recalls_what_the_first_recorded_2799`
    /// - witness: `verdicts::tests::a_held_cache_recalls_what_its_process_recorded_6566`
    fn readmit<Poll, Watch>(
        &self,
        arena: &mut CoreArena,
        report: &gandr_core_checker::ModuleReport,
        reuse: Reuse<'_>,
        timing: (&Poll, &mut Watch),
    ) -> bridge::Readmitting<Poll::Retired>
    where
        Poll: Retirement,
        Watch: bridge::Stopwatch,
    {
        let polled = readmit_as(arena, report, reuse, &self.recall(), timing);
        if let Polled::Whole((ref readmission, _)) = polled {
            self.settle(readmission);
        }
        polled
    }

    /// What this cache recalled and recorded so far, and the key it signs
    /// with.
    ///
    /// # Specification
    /// trivial.
    fn tally(&self) -> VerdictTally
    {
        VerdictTally {
            recalled: self.recalled.load(Ordering::Relaxed),
            recorded: self.recorded.load(Ordering::Relaxed),
            unwritten: self.unwritten.load(Ordering::Relaxed),
            signer: self.signer.identity(),
        }
    }
}

/// A process-wide install was made already: the verdict cache's or the
/// admission policy's.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AlreadyInstalled;

/// Install `cache` for every readmission this process makes after, unless a
/// cache is installed already, which stays.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`AlreadyInstalled`].
#[inline]
pub fn install_verdict_cache(cache: VerdictCache) -> Result<(), AlreadyInstalled>
{
    INSTALLED.set(cache).map_err(|_refused| AlreadyInstalled)
}

/// The fork this process installed for the obligations of each kernel check,
/// or the serial drain.
///
/// # Specification
/// trivial.
fn forking() -> SharedFork
{
    FORKING.get().cloned().unwrap_or_default()
}

/// The speculation group this process installed, or the group off.
///
/// # Specification
/// trivial.
fn speculation() -> Speculation
{
    SPECULATION.get().copied().unwrap_or(Speculation::OFF)
}

/// Install what a run at `pool`'s width spends its width on, for each
/// readmission this process makes after.
///
/// Wider than one thread, the checks of each readmission run on `pool` under
/// the speculation group on, the rank among it (#7335). The last drain of each
/// kernel check forks its obligations on `pool` when `walk` holds fewer
/// sources than threads: in a wider run the other sources keep each worker
/// busy. A serial run installs nothing and predicts nothing, as the release in
/// serial order (gandr #3476). What a process installed first stays.
///
/// The driver and the benchmark series both install through this call, so a
/// series measures the policy that a run of the driver takes.
///
/// # Specification
/// trivial.
#[inline]
pub fn install_width(
    pool: &Arc<Pool>,
    walk: &Walk,
)
{
    let threads = pool.width().threads();
    if threads == Threads::ONE {
        return;
    }
    let _pool = SCHEDULING.set(Arc::clone(pool));
    let _speculation = SPECULATION.set(Speculation::ON);
    let spare = SourceCount::from(NonZeroUsize::from(threads).get());
    if walk.sources_up_to(spare) < spare {
        let _fork = FORKING.set(SharedFork::through(Arc::<Pool>::clone(pool)));
    }
}

/// The pool this process installed for the checks of each readmission, or
/// the serial one.
///
/// # Specification
/// trivial.
fn scheduling() -> &'static Pool
{
    SCHEDULING.get().map_or(&SERIAL, |pool| pool)
}

/// [`bridge::readmit_retiring`] for [`Reuse::Leading`], or
/// [`bridge::readmit_keeping`] for [`Reuse::Keeping`], under `recall`, on
/// the installed readmission pool.
///
/// # Specification
/// trivial.
fn readmit_as<Poll, Watch>(
    arena: &mut CoreArena,
    report: &gandr_core_checker::ModuleReport,
    reuse: Reuse<'_>,
    recall: &bridge::Recall,
    (retirement, stopwatch): (&Poll, &mut Watch),
) -> bridge::Readmitting<Poll::Retired>
where
    Poll: Retirement,
    Watch: bridge::Stopwatch,
{
    match reuse {
        Reuse::Leading(boundary, crossed) => bridge::readmit_retiring(
            arena,
            report,
            (boundary, crossed),
            recall,
            retirement,
            stopwatch,
            scheduling(),
        ),
        Reuse::Keeping(keys, record) => bridge::readmit_keeping(
            arena,
            report,
            (keys, record),
            recall,
            retirement,
            stopwatch,
            scheduling(),
        ),
    }
}

quenchant_shape::reason_enum! {
    /// Why a process has no verdict tally.
    pub mod tallied {
        /// The reason there is none.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No cache was installed.
            Uninstalled,
        }
    }
}

/// What the installed cache recalled and recorded so far, and the key it
/// signs with.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct VerdictTally
{
    /// Admissions a recorded verdict answered.
    recalled: usize,
    /// Admissions whose verdicts a kept receipt holds, each once whatever
    /// number of keys it is kept under.
    recorded: usize,
    /// Receipts the store could not keep.
    unwritten: usize,
    /// The public half of this installation's key, as another installation's
    /// `kernel.trusted` lists it.
    signer: KernelIdentity,
}

impl fmt::Display for VerdictTally
{
    /// `<n> recalled, <n> recorded, <n> unwritten; signed by <key>`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{} recalled, {} recorded, {} unwritten; signed by {}",
            self.recalled, self.recorded, self.unwritten, self.signer
        )
    }
}

/// The installed cache's tally.
///
/// # Specification
/// trivial.
#[inline]
pub fn verdict_tally() -> Maybe<VerdictTally, tallied::Absent>
{
    INSTALLED
        .get()
        .map_or(Maybe::Absent(tallied::Absent::Uninstalled), |cache| {
            Maybe::Present(cache.tally())
        })
}

/// The readmission that `reuse` asks for ([`readmit_as`]) under the
/// installed cache's recall, settling a whole readmission into the cache;
/// under [`bridge::Recall::recheck`] when none is installed. The checks run on
/// the installed readmission pool, and `stopwatch` times each one. A whole
/// readmission adds the admitted results its kernel took to the process's
/// tally.
///
/// # Specification
/// trivial.
pub fn readmit<Poll, Watch>(
    arena: &mut CoreArena,
    report: &gandr_core_checker::ModuleReport,
    reuse: Reuse<'_>,
    timing: (&Poll, &mut Watch),
) -> bridge::Readmitting<Poll::Retired>
where
    Poll: Retirement,
    Watch: bridge::Stopwatch,
{
    let polled = match INSTALLED.get() {
        Some(cache) => cache.readmit(arena, report, reuse, timing),
        None => readmit_as(
            arena,
            report,
            reuse,
            &RECHECK
                .clone()
                .forking(forking())
                .speculating(speculation()),
            timing,
        ),
    };
    if let Polled::Whole((ref readmission, _)) = polled {
        crate::tier::took(readmission.environment().admitted());
    }
    polled
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::sync::Arc;

    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::Unretired;
    use gandr_core_checker::bridge;
    use gandr_core_checker::check_module;
    use gandr_core_term::CoreArena;
    use gandr_kernel_core::verdict::KernelSigner;
    use gandr_kernel_core::verdict::NoVerdicts;
    use gandr_kernel_core::verdict::StoredReceipt;
    use gandr_kernel_core::verdict::TrustPolicy;
    use gandr_storage_store::Register;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::lower_module;
    use gandr_surface_lowering::namespace::Recognition;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Kept;
    use super::VerdictCache;
    use crate::compose::KernelTier;
    use crate::compose::adapt;
    use crate::compose::tiers;
    use crate::receipts::StoredVerdicts;

    /// The fixture: two definitions, the second reading the first.
    const READMITTED: &str = include_str!("verdicts/fixtures/readmitted.gandr");

    /// The fixture with its second definition changed.
    const CHANGED: &str = include_str!("verdicts/fixtures/changed.gandr");

    /// The fixture with its first definition changed, so each key differs.
    const FOREIGN: &str = include_str!("verdicts/fixtures/foreign.gandr");

    /// The arena and the checker's report of the module `text` spells.
    ///
    /// # Specification
    /// trivial.
    fn reported(text: SourceText<'_>) -> (CoreArena, gandr_core_checker::ModuleReport)
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let tree = parse(&grammar, text).expect("parses").into_tree();
        let mut arena = CoreArena::new();
        let module = lower_module(
            &grammar,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .expect("the module lowers");
        let declarations = adapt(&module, &arena);
        let report = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &declarations,
        );
        (arena, report)
    }

    /// The readmission `cache` gives the module `text` spells.
    ///
    /// # Specification
    /// trivial.
    fn readmission_from(
        cache: &VerdictCache,
        text: SourceText<'_>,
    ) -> bridge::Readmission
    {
        let (mut arena, report) = reported(text);
        cache
            .readmit(
                &mut arena,
                &report,
                crate::compose::Reuse::Leading(
                    bridge::LeadingCount::NONE,
                    Maybe::Absent(bridge::crossed::Absent::Unasked),
                ),
                (&Unretired, &mut bridge::Untimed),
            )
            .whole()
            .0
    }

    /// The outcomes of `readmission`, in its order.
    ///
    /// # Specification
    /// trivial.
    fn outcomes(readmission: &bridge::Readmission) -> Vec<bridge::Outcome>
    {
        readmission
            .readmitted()
            .iter()
            .map(|readmitted| readmitted.outcome().clone())
            .collect()
    }

    /// The kernel tiers of `readmission`, in its order.
    ///
    /// # Specification
    /// trivial.
    fn tiered(readmission: &bridge::Readmission) -> Vec<KernelTier>
    {
        tiers(readmission)
            .into_iter()
            .map(|(_, tier)| tier)
            .collect()
    }

    /// The outcomes `cache` readmits the module `text` spells to.
    ///
    /// # Specification
    /// trivial.
    fn readmitted_from(
        cache: &VerdictCache,
        text: SourceText<'_>,
    ) -> Vec<bridge::Outcome>
    {
        outcomes(&readmission_from(cache, text))
    }

    /// A lasting cache over the store at `directory`, as a process opens it,
    /// believing `trusted` and signing with `signer`, and the store's
    /// register.
    ///
    /// # Specification
    /// trivial.
    fn lasting(
        directory: &std::path::Path,
        trusted: &[&KernelSigner],
        signer: &KernelSigner,
    ) -> (VerdictCache, Register)
    {
        let (store, register) = StoredVerdicts::open(directory).expect("the store opens");
        (
            VerdictCache::lasting(
                TrustPolicy::Trusted(trusted.iter().map(|key| key.identity()).collect()),
                store,
                signer.clone(),
            ),
            register,
        )
    }

    /// The outcomes `cache` readmits the fixture to.
    ///
    /// # Specification
    /// trivial.
    fn readmitted(cache: &VerdictCache) -> Vec<bridge::Outcome>
    {
        readmitted_from(cache, SourceText::from(READMITTED))
    }

    /// The receipt `signer` gives over a cold readmission of the module
    /// `text` spells.
    ///
    /// # Specification
    /// trivial.
    fn receipt(
        signer: &KernelSigner,
        text: SourceText<'_>,
    ) -> StoredReceipt
    {
        let (mut arena, report) = reported(text);
        let recall = bridge::Recall::trusting(
            TrustPolicy::Trusted(BTreeSet::from([signer.identity()])),
            Arc::new(NoVerdicts),
        );
        let (readmission, _) = bridge::readmit_retiring(
            &mut arena,
            &report,
            (
                bridge::LeadingCount::NONE,
                Maybe::Absent(bridge::crossed::Absent::Unasked),
            ),
            &recall,
            &Unretired,
            &mut bridge::Untimed,
            &gandr_core_fork::Serial,
        )
        .whole();
        let Maybe::Present(receipt) = readmission.environment().receipt(signer)
        else {
            panic!("a cold readmission under keys gives a receipt");
        };
        receipt
    }

    /// #2799: a module readmitted under a cache keeps what its kernel
    /// checked; under a second cache over the same store it recalls every one
    /// of those declarations, to the same outcomes, and keeps nothing more.
    #[test]
    fn a_second_cache_recalls_what_the_first_recorded_2799()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-dispatcher-verdicts-{}", std::process::id()));
        drop(std::fs::remove_dir_all(&directory));
        let signer = KernelSigner::from([3_u8; 32]);
        let cache = || {
            let (store, register) = StoredVerdicts::open(&directory).expect("the store opens");
            (
                VerdictCache::new(
                    TrustPolicy::Trusted(BTreeSet::from([signer.identity()])),
                    store,
                    signer.clone(),
                ),
                register,
            )
        };
        let (cold, mut register) = cache();
        let checked = readmitted(&cold);
        let recorded = cold.tally();
        assert_eq!(
            (recorded.recalled, recorded.unwritten),
            (0_usize, 0_usize),
            "{recorded}"
        );
        assert!(recorded.recorded > 0_usize, "{recorded}");
        register.drain().expect("the register names each receipt");

        let (warm, _register) = cache();
        let recalled = readmitted(&warm);
        let tally = warm.tally();
        assert_eq!(
            (tally.recalled, tally.recorded, tally.unwritten),
            (recorded.recorded, 0_usize, 0_usize),
            "{tally}"
        );
        assert_eq!(
            recalled, checked,
            "a recalled verdict admits as a checked one"
        );
        drop(std::fs::remove_dir_all(&directory));
    }

    /// #6566: a module readmitted twice under one held cache recalls, the
    /// second time, every declaration the first checked, to the same outcomes.
    #[test]
    fn a_held_cache_recalls_what_its_process_recorded_6566()
    {
        let cache = VerdictCache::held(KernelSigner::from([3_u8; 32]));
        let checked = readmitted(&cache);
        let recorded = cache.tally();
        assert_eq!(recorded.recalled, 0_usize, "{recorded}");
        assert!(recorded.recorded > 0_usize, "{recorded}");
        let recalled = readmitted(&cache);
        let tally = cache.tally();
        assert_eq!(
            (tally.recalled, tally.recorded),
            (recorded.recorded, recorded.recorded),
            "{tally}"
        );
        assert_eq!(
            recalled, checked,
            "a recalled verdict admits as a checked one"
        );
    }

    /// #6566: under a held cache, a declaration whose text changed is checked
    /// again, and the one before it, unchanged, is recalled.
    #[test]
    fn a_changed_declaration_is_checked_again_6566()
    {
        let cache = VerdictCache::held(KernelSigner::from([3_u8; 32]));
        let _cold = readmitted(&cache);
        let before = cache.tally();
        let changed = readmitted_from(&cache, SourceText::from(CHANGED));
        let after = cache.tally();
        assert!(
            changed
                .iter()
                .all(|outcome| matches!(outcome, bridge::Outcome::Defined { .. })),
            "{changed:?}"
        );
        assert_eq!(
            (
                after.recalled.saturating_sub(before.recalled),
                after.recorded.saturating_sub(before.recorded)
            ),
            (1_usize, 1_usize),
            "the unchanged definition is recalled and the changed one checked: {after}"
        );
    }

    /// #6566: a held source that answers a receipt from a signer the policy
    /// does not list, or one over keys the module's chain does not produce,
    /// admits no declaration on it.
    #[test]
    fn a_foreign_signer_or_key_admits_nothing_6566()
    {
        let signer = KernelSigner::from([3_u8; 32]);
        let cache = VerdictCache::held(signer.clone());
        let Kept::Held(ref held) = cache.kept
        else {
            panic!("a held cache keeps its receipts in the process");
        };
        held.keep(receipt(
            &KernelSigner::from([5_u8; 32]),
            SourceText::from(READMITTED),
        ));
        held.keep(receipt(&signer, SourceText::from(FOREIGN)));
        let _checked = readmitted(&cache);
        let tally = cache.tally();
        assert_eq!(
            tally.recalled, 0_usize,
            "neither receipt admits a declaration of the module: {tally}"
        );
        assert!(tally.recorded > 0_usize, "{tally}");
    }

    /// #6623: a lasting cache recalls, on its second readmission, what its
    /// first checked. A second process over the same store recalls each of
    /// those declarations as attested, to the same outcomes, and checks
    /// nothing.
    #[test]
    fn a_lasting_cache_recalls_its_own_and_the_store_s_6623()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-dispatcher-lasting-{}", std::process::id()));
        drop(std::fs::remove_dir_all(&directory));
        let signer = KernelSigner::from([3_u8; 32]);
        let (first, mut register) = lasting(&directory, &[&signer], &signer);
        let cold = readmission_from(&first, SourceText::from(READMITTED));
        let checked = first.tally();
        assert_eq!(
            (checked.recalled, checked.unwritten),
            (0_usize, 0_usize),
            "{checked}"
        );
        assert!(checked.recorded > 0_usize, "{checked}");
        assert!(
            tiered(&cold)
                .iter()
                .all(|&tier| tier == KernelTier::Replayed),
            "a cold readmission replays each declaration"
        );
        let _again = readmitted(&first);
        let held = first.tally();
        assert_eq!(
            (held.recalled, held.recorded),
            (checked.recorded, checked.recorded),
            "the process recalls what it kept after the open: {held}"
        );

        register.drain().expect("the register names each receipt");
        let (second, _register) = lasting(&directory, &[&signer], &signer);
        let warm = readmission_from(&second, SourceText::from(READMITTED));
        let tally = second.tally();
        assert_eq!(
            (tally.recalled, tally.recorded, tally.unwritten),
            (checked.recorded, 0_usize, 0_usize),
            "{tally}"
        );
        assert_eq!(
            outcomes(&warm),
            outcomes(&cold),
            "a recalled verdict admits as a checked one"
        );
        assert!(
            tiered(&warm)
                .iter()
                .all(|&tier| tier == KernelTier::Attested),
            "each declaration the store recalls is attested"
        );
        drop(std::fs::remove_dir_all(&directory));
    }

    /// #6623: a store that holds a receipt over records its signer did not
    /// sign admits nothing, and the process checks each declaration again.
    #[test]
    fn a_record_its_signer_did_not_sign_admits_nothing_6623()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-dispatcher-unsigned-{}", std::process::id()));
        drop(std::fs::remove_dir_all(&directory));
        let signer = KernelSigner::from([3_u8; 32]);
        // The receipt is ours, signed over the records of another text; the
        // records are those of the module's text, which no one signed.
        let signed = receipt(&signer, SourceText::from(FOREIGN));
        let unsigned = receipt(
            &KernelSigner::from([5_u8; 32]),
            SourceText::from(READMITTED),
        );
        let forged = StoredReceipt::new(signed.receipt(), unsigned.records().to_vec());
        let (store, mut register) = StoredVerdicts::open(&directory).expect("the store opens");
        store.keep(&forged).expect("the receipt is written");
        register.drain().expect("the register names the receipt");
        let (cache, _register) = lasting(&directory, &[&signer], &signer);
        let readmission = readmission_from(&cache, SourceText::from(READMITTED));
        let tally = cache.tally();
        assert_eq!(
            (tally.recalled, tally.recorded),
            (0_usize, readmission.readmitted().len()),
            "the forged records admit nothing, so each declaration is checked: {tally}"
        );
        drop(std::fs::remove_dir_all(&directory));
    }

    /// #6623: the records of a foreign installation's store admit nothing
    /// while the owner does not list its key, and admit each declaration once
    /// the owner lists it.
    #[test]
    fn a_foreign_store_s_record_admits_only_when_listed_6623()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-dispatcher-foreign-{}", std::process::id()));
        drop(std::fs::remove_dir_all(&directory));
        let (ours, theirs) = (
            KernelSigner::from([3_u8; 32]),
            KernelSigner::from([5_u8; 32]),
        );
        let (foreign, mut register) = lasting(&directory, &[&theirs], &theirs);
        let _checked = readmitted(&foreign);
        let kept = foreign.tally().recorded;
        assert!(kept > 0_usize, "the foreign store keeps its records");
        register.drain().expect("the register names each receipt");
        // Both caches open the store before either keeps a receipt of ours.
        let (unlisted, _unlisted_register) = lasting(&directory, &[&ours], &ours);
        let (listed, _listed_register) = lasting(&directory, &[&ours, &theirs], &ours);
        let _unlisted = readmitted(&unlisted);
        let refused = unlisted.tally();
        assert_eq!(
            (refused.recalled, refused.recorded),
            (0_usize, kept),
            "an unlisted key admits nothing: {refused}"
        );
        let _listed = readmitted(&listed);
        let believed = listed.tally();
        assert_eq!(
            (believed.recalled, believed.recorded),
            (kept, 0_usize),
            "a listed key admits each record: {believed}"
        );
        drop(std::fs::remove_dir_all(&directory));
    }

    /// #6623: a stale store, which holds the verdicts of an earlier text of
    /// the module, recalls nothing, and the process checks each declaration
    /// again under its own keys.
    #[test]
    fn a_stale_store_is_checked_again_6623()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-dispatcher-stale-{}", std::process::id()));
        drop(std::fs::remove_dir_all(&directory));
        let signer = KernelSigner::from([3_u8; 32]);
        let (earlier, mut register) = lasting(&directory, &[&signer], &signer);
        let _earlier = readmitted_from(&earlier, SourceText::from(FOREIGN));
        assert!(
            earlier.tally().recorded > 0_usize,
            "the earlier session keeps its records"
        );
        register.drain().expect("the register names each receipt");
        let (later, _register) = lasting(&directory, &[&signer], &signer);
        let readmission = readmission_from(&later, SourceText::from(READMITTED));
        let tally = later.tally();
        assert_eq!(
            (tally.recalled, tally.recorded),
            (0_usize, readmission.readmitted().len()),
            "no key of the earlier text is the module's: {tally}"
        );
        assert!(
            tiered(&readmission)
                .iter()
                .all(|&tier| tier == KernelTier::Replayed),
            "each declaration is replayed"
        );
        drop(std::fs::remove_dir_all(&directory));
    }
}
