//! The kernel verdict cache a `check` installs: this installation's key, read
//! or minted, the store under the cache directory, and the policy the user's
//! configuration names (`config` § The kernel's key and its verdicts).
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — the receipt is the kernel's signature, made with
//!   the installation's key, and the policy is the operator's setting.

use core::fmt;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use gandr_core_incremental::FileVerdictStore;
use gandr_kernel_core::verdict::KernelSigner;
use gandr_kernel_core::verdict::TrustPolicy;
use gandr_surface_dispatcher::VerdictCache;
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

/// Install the cache `kernel` asks for, unless it asks to recheck or no
/// directory is named for the key or the store.
///
/// # Specification
/// - requires: called once, before the walk.
/// - ensures: under [`config::Kernel::Trusting`], with both directories named,
///   the process's readmissions recall what this installation's key or a listed
///   one signed, and keep what they check under this installation's key;
///   otherwise nothing is installed and every declaration is checked.
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
///   recorded; `--recheck` and a key the policy does not list recall nothing.
/// - witness: `tests::cli::a_second_check_recalls_what_the_first_recorded_2799`
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
    let Ok(store) = FileVerdictStore::open(&directory)
    else {
        return Err(Uninstalled {
            path: directory,
            why: String::from("cannot be opened"),
        });
    };
    install_verdict_cache(VerdictCache::new(
        TrustPolicy::Trusted(trusted),
        store,
        signer,
    ))
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
    let process = std::process::id();
    let nonce = core::hash::BuildHasher::hash_one(&std::hash::RandomState::new(), process);
    let private = path.with_extension(format!("key.{process}-{nonce:016x}"));
    // Written whole into a file this call creates under a private name, then
    // linked into place: a reader never sees a partial key, and a link refuses
    // to replace one another process published first.
    let mut options = std::fs::OpenOptions::new();
    let _writing = options.write(true).create_new(true);
    #[cfg(unix)]
    {
        let _private = std::os::unix::fs::OpenOptionsExt::mode(&mut options, 0o600);
    }
    let published = options
        .open(&private)
        .and_then(|mut file| {
            io::Write::write_all(&mut file, &seed)?;
            file.sync_all()
        })
        .and_then(|()| std::fs::hard_link(&private, path));
    drop(std::fs::remove_file(&private));
    match published {
        Ok(()) => Ok(KernelSigner::from(seed)),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => stored(path),
        Err(error) => Err(error),
    }
}
