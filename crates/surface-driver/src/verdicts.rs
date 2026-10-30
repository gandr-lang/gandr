//! The kernel verdict cache a `check` installs: this installation's key, read
//! or minted, the store under the cache directory's `receipts`, and the policy
//! the user's configuration names (`config` § The kernel's key and its
//! verdicts). The stratum store beside it believes the same policy and signs
//! with the same key, and holds its strata in a store under the cache
//! directory's `strata`.
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
    let config::Kernel::Trusting(mut trusted) = kernel
    else {
        return Ok(());
    };
    let (Some(key), Some(directory)) = (config::kernel_key(), config::verdicts())
    else {
        return Ok(());
    };
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
    let policy = TrustPolicy::Trusted(trusted);
    let strata = StoredStrata::new(policy.clone(), directory.join("strata"), signer.clone());
    install_verdict_cache(VerdictCache::new(policy, store, signer))
        .and_then(|()| install_stratum_store(strata))
        .map_err(|_installed| Uninstalled {
            path: directory,
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
