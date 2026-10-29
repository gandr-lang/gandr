//! The kernel verdicts a process recalls and records.
//!
//! A driver that keeps the kernel's verdicts installs one [`VerdictCache`]
//! before its walk: the policy naming whose receipts it believes, the store
//! receipts are read from and written to, and the key this installation signs
//! with. Every readmission the composition makes then admits under the
//! cache's recall, and one that crossed whole has the kernel sign what it
//! checked and keeps the receipt. A process that installs none — the language
//! server, the sweeps, every test — rechecks every declaration.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — tests and audits run under the full re-check, so
//!   only a cache a driver installs recalls.

use alloc::sync::Arc;
use core::fmt;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::sync::LazyLock;
use std::sync::OnceLock;

use gandr_core_checker::Polled;
use gandr_core_checker::Retirement;
use gandr_core_checker::bridge;
use gandr_core_incremental::FileVerdictStore;
use gandr_core_term::CoreArena;
use gandr_kernel_core::verdict::KernelIdentity;
use gandr_kernel_core::verdict::KernelSigner;
use gandr_kernel_core::verdict::TrustPolicy;
use gandr_kernel_core::verdict::VerdictSource;
use quenchant_shape::shape::Maybe;

/// The recall of a process that installed no cache.
static RECHECK: LazyLock<bridge::Recall> = LazyLock::new(bridge::Recall::recheck);

/// The cache this process installed.
// economy: one cache per process, read where every readmission funnels; a
// host that needs two at once (the language server's background kernel)
// threads one through the composition's admission instead.
static INSTALLED: OnceLock<VerdictCache> = OnceLock::new();

/// Where a process's kernel verdicts are recalled from and recorded to.
///
/// # Specification
/// - ensures: installed, every readmission admits under the cache's policy and
///   store, and each one that crossed whole keeps the receipt its kernel signs
///   for what it checked.
/// - executable: none — the store and the counts are shared state.
///
/// # Adequacy
/// - hypothesis: L3 — a module readmitted under one cache records what its
///   kernel checked, and readmitted under a second over the same store recalls
///   each of those declarations, to the same outcomes.
/// - witness: `verdicts::tests::a_second_cache_recalls_what_the_first_recorded_2799`
#[derive(Debug)]
pub struct VerdictCache
{
    /// The policy and store a fresh readmission admits under.
    recall: bridge::Recall,
    /// Where receipts are kept.
    store: Arc<FileVerdictStore>,
    /// This installation's key.
    signer: KernelSigner,
    /// Admissions a recorded verdict answered.
    recalled: AtomicUsize,
    /// Verdicts kept in a receipt.
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
        store: FileVerdictStore,
        signer: KernelSigner,
    ) -> Self
    {
        let store = Arc::new(store);
        let source: Arc<dyn VerdictSource> = Arc::<FileVerdictStore>::clone(&store);
        Self {
            recall: bridge::Recall::trusting(policy, source),
            store,
            signer,
            recalled: AtomicUsize::new(0),
            recorded: AtomicUsize::new(0),
            unwritten: AtomicUsize::new(0),
        }
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
            let _before = match self.store.keep(&receipt) {
                Ok(()) => self
                    .recorded
                    .fetch_add(receipt.records().len(), Ordering::Relaxed),
                Err(_unwritten) => self.unwritten.fetch_add(1, Ordering::Relaxed),
            };
        }
    }

    /// [`bridge::readmit_retiring`] under this cache's recall, timing each
    /// admission by `stopwatch`, settling a whole readmission into the cache.
    ///
    /// # Specification
    /// - ensures: the readmission [`bridge::readmit_retiring`] gives under the
    ///   cache's policy and store; a whole one adds what it recalled to the
    ///   tally, and the store keeps the receipt its kernel signs for what it
    ///   checked.
    /// - panics: none.
    /// - executable: none — the store and the counts are shared state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`VerdictCache`].
    /// - witness: `verdicts::tests::a_second_cache_recalls_what_the_first_recorded_2799`
    fn readmit<Poll, Watch>(
        &self,
        arena: &mut CoreArena,
        report: &gandr_core_checker::ModuleReport,
        leading: (
            bridge::LeadingCount,
            Maybe<&bridge::Crossed, bridge::crossed::Absent>,
        ),
        (retirement, stopwatch): (&Poll, &mut Watch),
    ) -> bridge::Readmitting<Poll::Retired>
    where
        Poll: Retirement,
        Watch: bridge::Stopwatch,
    {
        let polled =
            bridge::readmit_retiring(arena, report, leading, &self.recall, retirement, stopwatch);
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
    /// Verdicts kept in a receipt.
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

/// [`bridge::readmit_retiring`] under the installed cache's recall, settling
/// a whole readmission into the cache; under [`bridge::Recall::recheck`] when
/// none is installed. Each admission is timed by `stopwatch`. A whole
/// readmission adds the admitted results its kernel took to the process's
/// tally.
///
/// # Specification
/// trivial.
pub fn readmit<Poll, Watch>(
    arena: &mut CoreArena,
    report: &gandr_core_checker::ModuleReport,
    leading: (
        bridge::LeadingCount,
        Maybe<&bridge::Crossed, bridge::crossed::Absent>,
    ),
    (retirement, stopwatch): (&Poll, &mut Watch),
) -> bridge::Readmitting<Poll::Retired>
where
    Poll: Retirement,
    Watch: bridge::Stopwatch,
{
    let polled = match INSTALLED.get() {
        Some(cache) => cache.readmit(arena, report, leading, (retirement, stopwatch)),
        None => bridge::readmit_retiring(arena, report, leading, &RECHECK, retirement, stopwatch),
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

    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::Unretired;
    use gandr_core_checker::bridge;
    use gandr_core_checker::check_module;
    use gandr_core_incremental::FileVerdictStore;
    use gandr_core_term::CoreArena;
    use gandr_kernel_core::verdict::KernelSigner;
    use gandr_kernel_core::verdict::TrustPolicy;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::lower_module;
    use gandr_surface_lowering::namespace::Recognition;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::VerdictCache;
    use crate::compose::adapt;

    /// The outcomes `cache` readmits a module of two definitions to, the
    /// second reading the first.
    ///
    /// # Specification
    /// trivial.
    fn readmitted(cache: &VerdictCache) -> Vec<bridge::Outcome>
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let source = SourceText::from("def answer = 42 ;\ndef again = answer ;\n");
        let tree = parse(&grammar, source).expect("parses").into_tree();
        let mut arena = CoreArena::new();
        let module = lower_module(
            &grammar,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .expect("the module lowers");
        let report = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &adapt(&module),
        );
        cache
            .readmit(
                &mut arena,
                &report,
                (
                    bridge::LeadingCount::NONE,
                    Maybe::Absent(bridge::crossed::Absent::Unasked),
                ),
                (&Unretired, &mut bridge::Untimed),
            )
            .whole()
            .0
            .readmitted()
            .iter()
            .map(|readmitted| readmitted.outcome().clone())
            .collect()
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
            VerdictCache::new(
                TrustPolicy::Trusted(BTreeSet::from([signer.identity()])),
                FileVerdictStore::open(&directory).expect("the store opens"),
                signer.clone(),
            )
        };
        let cold = cache();
        let checked = readmitted(&cold);
        let recorded = cold.tally();
        assert_eq!(
            (recorded.recalled, recorded.unwritten),
            (0_usize, 0_usize),
            "{recorded}"
        );
        assert!(recorded.recorded > 0_usize, "{recorded}");

        let warm = cache();
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
}
