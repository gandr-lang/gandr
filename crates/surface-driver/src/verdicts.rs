//! The kernel verdict cache a `check`, a language server or a hub installs:
//! this installation's key, read or minted, the store under the cache
//! directory's `receipts`, and the policy the user's configuration names
//! (`config` § The kernel's key and its verdicts). The stratum store beside a
//! `check`'s cache believes the same policy and signs with the same key, and
//! holds its strata in a store under the cache directory's `strata`. A
//! language server or a hub keeps its verdicts in the same store and in the
//! process, so a later session recalls what an earlier one checked. With no
//! directory named, it holds them in the process alone, under a key the
//! process mints for itself.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — the receipt is the kernel's signature, made with
//!   the installation's key, and the policy is the operator's setting.
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — the
//!   strata persist in the store, which a `check` installs beside the verdict
//!   cache.
//! - `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — lineage: §
//!   build-owner-store — the receipts and the strata each sit in a store under
//!   the cache directory, the one store the storage tier opens.

use alloc::collections::BTreeSet;
use core::fmt;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use gandr_core_publish::Access;
use gandr_core_publish::Contents;
use gandr_core_publish::Placement;
use gandr_core_publish::Step;
use gandr_core_publish::Unpublished;
use gandr_core_publish::publish_as;
use gandr_kernel_core::verdict::KernelIdentity;
use gandr_kernel_core::verdict::KernelSigner;
use gandr_kernel_core::verdict::TrustPolicy;
use gandr_surface_dispatcher::StoredStrata;
use gandr_surface_dispatcher::StoredVerdicts;
use gandr_surface_dispatcher::VerdictCache;
use gandr_surface_dispatcher::install_stratum_store;
use gandr_surface_dispatcher::install_verdict_cache;

use crate::config;

/// Why no cache was installed: the path, and what went wrong there.
#[derive(Debug)]
pub struct Uninstalled
{
    /// The key file or the store's directory.
    path: PathBuf,
    /// What went wrong, in words.
    why: String,
}

impl fmt::Display for Uninstalled
{
    /// `<path>: <why>; every declaration is checked`.
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
            "{}: {}; every declaration is checked",
            self.path.display(),
            self.why
        )
    }
}

/// Install the cache `kernel` asks for, and the stratum store beside it,
/// unless it asks to recheck or no directory is named for the key or the
/// store.
///
/// # Specification
/// - requires: called once, before the walk.
/// - ensures: under [`config::Kernel::Trusting`], with both directories named,
///   the process's readmissions recall what this installation's key or a listed
///   one signed from the store under the cache directory's `receipts`, and keep
///   there what they check under this installation's key; its contexts recall
///   the strata such a key signed from the store under the cache directory's
///   `strata`, and keep there what they certify; otherwise nothing is installed
///   and every declaration and stratum is checked.
/// - fails: the key cannot be read or minted, or the store cannot be opened.
/// - panics: none.
/// - executable: none — the key, the store and the installation are external
///   state.
///
/// # Errors
/// [`Uninstalled`], naming the path that failed.
///
/// # Adequacy
/// - hypothesis: L3 — a second `check` over one cache recalls what the first
///   recorded and replays the strata it kept; `--recheck` and a key the policy
///   does not list recall nothing.
/// - witness: `tests::cli::a_second_check_recalls_what_the_first_recorded_2799`
/// - witness: `tests::cli::a_second_check_replays_the_strata_the_first_kept_4034`
pub fn install(kernel: config::Kernel) -> Result<(), Uninstalled>
{
    let config::Kernel::Trusting(trusted) = kernel
    else {
        return Ok(());
    };
    let (Some(key), Some(directory)) = (config::kernel_key(), config::verdicts())
    else {
        return Ok(());
    };
    let (policy, store, signer) = opened(trusted, key, &directory)?;
    let strata = StoredStrata::new(policy.clone(), directory.join("strata"), signer.clone());
    install_verdict_cache(VerdictCache::new(policy, store, signer))
        .and_then(|()| install_stratum_store(strata))
        .map_err(|_installed| Uninstalled {
            path: directory,
            why: String::from("a cache is already installed"),
        })
}

/// The policy, the store and the key a cache keeps its verdicts under: this
/// installation's key at `key`, read or minted and trusted beside `trusted`,
/// and the store under `directory`'s `receipts`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Uninstalled`], naming the path that failed.
fn opened(
    mut trusted: BTreeSet<KernelIdentity>,
    key: PathBuf,
    directory: &Path,
) -> Result<(TrustPolicy, StoredVerdicts, KernelSigner), Uninstalled>
{
    let signer = match signer(&key) {
        Ok(signer) => signer,
        Err(error) => {
            return Err(Uninstalled {
                path: key,
                why: error.to_string(),
            });
        },
    };
    let _own = trusted.insert(signer.identity());
    let receipts = directory.join("receipts");
    let Ok(store) = StoredVerdicts::open(&receipts)
    else {
        return Err(Uninstalled {
            path: receipts,
            why: String::from("cannot be opened"),
        });
    };
    Ok((TrustPolicy::Trusted(trusted), store, signer))
}

/// Why a language server or a hub holds no verdicts: what went wrong.
#[repr(transparent)]
#[derive(Debug)]
pub struct Unheld
{
    /// What went wrong, in words.
    why: String,
}

impl fmt::Display for Unheld
{
    /// `the process holds no kernel verdicts: <why>; every declaration is
    /// checked`.
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
            "the process holds no kernel verdicts: {}; every declaration is checked",
            self.why
        )
    }
}

/// Install the cache a language server or a hub keeps its kernel's verdicts
/// in, unless `kernel` asks to recheck.
///
/// # Specification
/// - requires: called once, before the first session.
/// - ensures: as [`holding`] at the key and the cache directory the
///   configuration names.
/// - fails: as [`holding`].
/// - panics: none.
/// - executable: none — the directories and the installation are external
///   state.
///
/// # Errors
/// [`Unheld`], saying why.
///
/// # Adequacy
/// - hypothesis: L3 — as [`holding`].
/// - witness: `verdicts::tests::a_server_keeps_its_verdicts_in_the_installation_s_store_6623`
#[inline]
pub fn hold(kernel: config::Kernel) -> Result<(), Unheld>
{
    holding(kernel, config::kernel_key().zip(config::verdicts()))
}

/// Install the cache a language server or a hub keeps its kernel's verdicts
/// in, with the key's path and the cache directory that `at` names, unless
/// `kernel` asks to recheck.
///
/// # Specification
/// - requires: called once, before the first session.
/// - ensures: under [`config::Kernel::Trusting`], with `at` present, the
///   process's readmissions recall from the store under the cache directory's
///   `receipts` what this installation's key or a listed one signed. They also
///   recall what an earlier readmission of the process checked. They keep what
///   they check, under this installation's key, in the store and in the
///   process. With `at` absent, they recall what an earlier readmission of the
///   process checked, under a key the process mints from the operating system's
///   entropy and trusts alone. Otherwise nothing is installed and every
///   declaration is checked.
/// - fails: the key cannot be read or minted, the store cannot be opened, the
///   entropy cannot be read, or a cache is installed already.
/// - panics: none.
/// - executable: none — the key, the store, the entropy and the installation
///   are external state.
///
/// # Errors
/// [`Unheld`], saying why.
///
/// # Adequacy
/// - hypothesis: L3 — a trusting process installs its cache once, so a second
///   call finds it installed; a rechecking one installs none; one that names
///   its directories mints its key there and opens its store there.
/// - witness: `verdicts::tests::a_trusting_process_holds_its_verdicts_once_6566`
/// - witness: `verdicts::tests::a_rechecking_process_holds_no_verdicts_6566`
/// - witness: `verdicts::tests::a_server_keeps_its_verdicts_in_the_installation_s_store_6623`
fn holding(
    kernel: config::Kernel,
    at: Option<(PathBuf, PathBuf)>,
) -> Result<(), Unheld>
{
    let config::Kernel::Trusting(trusted) = kernel
    else {
        return Ok(());
    };
    let cache = if let Some((key, directory)) = at {
        let (policy, store, signer) =
            opened(trusted, key, &directory).map_err(|uninstalled| Unheld {
                why: format!("{}: {}", uninstalled.path.display(), uninstalled.why),
            })?;
        VerdictCache::lasting(policy, store, signer)
    }
    else {
        let mut seed = [0_u8; 32];
        getrandom::fill(&mut seed).map_err(|error| Unheld {
            why: error.to_string(),
        })?;
        VerdictCache::held(KernelSigner::from(seed))
    };
    install_verdict_cache(cache).map_err(|_installed| Unheld {
        why: String::from("a cache is already installed"),
    })
}

/// The key at `path`, minted there when there is none.
///
/// # Specification
/// trivial.
fn signer(path: &Path) -> io::Result<KernelSigner>
{
    match stored(path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => minted(path),
        Ok(signer) => Ok(signer),
        Err(error) => Err(error),
    }
}

/// The key whose seed the file at `path` holds.
///
/// # Specification
/// trivial.
fn stored(path: &Path) -> io::Result<KernelSigner>
{
    <[u8; 32]>::try_from(std::fs::read(path)?.as_slice())
        .map(KernelSigner::from)
        .map_err(|_short| io::Error::new(io::ErrorKind::InvalidData, "is not a kernel key"))
}

/// Mint a key from the operating system's entropy and publish it at `path`,
/// readable by its owner alone; when another process published one first,
/// that one.
///
/// # Specification
/// trivial.
fn minted(path: &Path) -> io::Result<KernelSigner>
{
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let mut seed = [0_u8; 32];
    getrandom::fill(&mut seed).map_err(|error| io::Error::other(error.to_string()))?;
    // Kept, not replaced: a reader never sees a partial key, and the link
    // refuses to replace one another process published first.
    match publish_as(path, Contents(&seed), Placement::Keep, &Access::Owner) {
        Ok(()) => Ok(KernelSigner::from(seed)),
        Err(Unpublished {
            step: Step::Link,
            kind: io::ErrorKind::AlreadyExists,
            ..
        }) => stored(path),
        Err(refused) => Err(io::Error::from(refused.kind)),
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;

    use gandr_kernel_core::verdict::KernelSigner;
    use gandr_surface_dispatcher::VerdictCache;
    use gandr_surface_dispatcher::install_verdict_cache;

    use super::holding;
    use crate::config;

    /// #6566: a trusting process installs its held cache, so a second call
    /// finds a cache installed and says so.
    #[test]
    fn a_trusting_process_holds_its_verdicts_once_6566()
    {
        let trusting = || config::Kernel::Trusting(BTreeSet::new());
        assert!(
            holding(trusting(), None).is_ok(),
            "the first call installs the cache"
        );
        let again = holding(trusting(), None);
        assert!(
            again.is_err_and(|unheld| unheld.to_string().contains("already installed")),
            "the second call finds the cache installed"
        );
    }

    /// #6566: a process whose policy rechecks installs no cache, so another
    /// cache still installs after it.
    #[test]
    fn a_rechecking_process_holds_no_verdicts_6566()
    {
        assert!(holding(config::Kernel::Rechecking, None).is_ok());
        assert!(
            install_verdict_cache(VerdictCache::held(KernelSigner::from([3_u8; 32]))).is_ok(),
            "no cache was installed before"
        );
    }

    /// #6623: a server that names its directories mints this installation's
    /// key there and opens the store under the cache directory's `receipts`,
    /// the one a `check` keeps its receipts in.
    #[test]
    fn a_server_keeps_its_verdicts_in_the_installation_s_store_6623()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-driver-held-{}", std::process::id()));
        drop(std::fs::remove_dir_all(&directory));
        let (key, verdicts) = (directory.join("kernel.key"), directory.join("verdicts"));
        assert!(
            holding(
                config::Kernel::Trusting(BTreeSet::new()),
                Some((key.clone(), verdicts.clone()))
            )
            .is_ok(),
            "the cache installs over the store"
        );
        assert!(key.is_file(), "the installation's key is minted");
        assert!(
            verdicts.join("receipts").is_dir(),
            "the store opens under `receipts`"
        );
        drop(std::fs::remove_dir_all(&directory));
    }
}
