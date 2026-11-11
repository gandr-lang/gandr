//! The kernel verdicts a process recalls and records.
//!
//! A driver that keeps the kernel's verdicts installs one [`VerdictCache`]
//! before its walk: the policy naming whose receipts it believes, where
//! receipts are read from and kept, and the key this installation signs with.
//! Every readmission the composition makes then admits under the cache's
//! recall, and one that crossed whole has the kernel sign what it checked and
//! keeps the receipt. `gandr check` keeps its receipts in a store on disk,
//! which a later process reads. The language server keeps them in the process
//! ([`VerdictCache::held`]), which a later readmission of the process reads. A
//! process that installs none — the sweeps, `gandr check --recheck`, every
//! test — rechecks every declaration.
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
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::sync::LazyLock;
use std::sync::OnceLock;

use gandr_core_checker::Polled;
use gandr_core_checker::Retirement;
use gandr_core_checker::bridge;
use gandr_core_term::CoreArena;
use gandr_kernel_core::verdict::KernelIdentity;
use gandr_kernel_core::verdict::KernelSigner;
use gandr_kernel_core::verdict::TrustPolicy;
use gandr_kernel_core::verdict::VerdictSource;
use quenchant_shape::shape::Maybe;

use crate::held::HeldVerdicts;
use crate::receipts::StoredVerdicts;

/// The recall of a process that installed no cache.
static RECHECK: LazyLock<bridge::Recall> = LazyLock::new(bridge::Recall::recheck);

/// The cache this process installed.
// economy: one cache per process, read where every readmission funnels; a
// host that needs two at once (the language server's background kernel)
// threads one through the composition's admission instead.
static INSTALLED: OnceLock<VerdictCache> = OnceLock::new();

/// Where a cache keeps the receipts its kernel signs, and reads them from.
#[derive(Debug)]
enum Kept
{
    /// A store on disk, which a later process reads at open.
    Stored(Arc<StoredVerdicts>),
    /// The process's own source, which a later readmission of the process
    /// reads.
    Held(HeldVerdicts),
}

/// Where a process's kernel verdicts are recalled from and recorded to.
///
/// # Specification
/// - ensures: installed, every readmission admits under the cache's policy and
///   source, and each one that crossed whole keeps the receipt its kernel signs
///   for what it checked; a held cache's next readmission reads that receipt.
/// - executable: none — the store and the counts are shared state.
///
/// # Adequacy
/// - hypothesis: L3 — a module readmitted under one cache records what its
///   kernel checked, and readmitted under a second over the same store recalls
///   each of those declarations, to the same outcomes; readmitted twice under
///   one held cache, it recalls them the second time.
/// - witness: `verdicts::tests::a_second_cache_recalls_what_the_first_recorded_2799`
/// - witness: `verdicts::tests::a_held_cache_recalls_what_its_process_recorded_6566`
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
    /// policy over its store, or over the receipts the process holds now.
    ///
    /// # Specification
    /// trivial.
    fn recall(&self) -> bridge::Recall
    {
        let source: Arc<dyn VerdictSource> = match self.kept {
            Kept::Stored(ref store) => Arc::<StoredVerdicts>::clone(store),
            Kept::Held(ref held) => held.snapshot(),
        };
        bridge::Recall::trusting(self.policy.clone(), source)
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
            };
            let _before = if kept {
                self.recorded.fetch_add(records, Ordering::Relaxed)
            }
            else {
                self.unwritten.fetch_add(1, Ordering::Relaxed)
            };
        }
    }

    /// [`bridge::readmit_retiring`] under this cache's recall, timing each
    /// admission by `stopwatch`, settling a whole readmission into the cache.
    ///
    /// # Specification
    /// - ensures: the readmission [`bridge::readmit_retiring`] gives under the
    ///   cache's policy over its source as it stands now; a whole one adds what
    ///   it recalled to the tally, and the cache keeps the receipt its kernel
    ///   signs for what it checked.
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
        let polled = bridge::readmit_retiring(
            arena,
            report,
            leading,
            &self.recall(),
            retirement,
            stopwatch,
        );
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
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::lower_module;
    use gandr_surface_lowering::namespace::Recognition;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Kept;
    use super::VerdictCache;
    use crate::compose::adapt;
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

    /// The outcomes `cache` readmits the module `text` spells to.
    ///
    /// # Specification
    /// trivial.
    fn readmitted_from(
        cache: &VerdictCache,
        text: SourceText<'_>,
    ) -> Vec<bridge::Outcome>
    {
        let (mut arena, report) = reported(text);
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
            VerdictCache::new(
                TrustPolicy::Trusted(BTreeSet::from([signer.identity()])),
                StoredVerdicts::open(&directory).expect("the store opens"),
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
}
