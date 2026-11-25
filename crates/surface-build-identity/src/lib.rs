//! The identities of the build that the driver passes down: the kernel's
//! build identity, which each verdict key binds, and the build of the theory
//! sites, which each stratum key binds.
//!
//! The build script digests what each library compiles, as `src/digest.rs`
//! states, and this crate compiles the two digests in. The driver alone
//! depends on the crate. So a change that moves a digest compiles this crate
//! and the driver again, and no library between them. The kernel and the
//! sites take each identity as a value from their caller.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — the key binds each input of the verdict, so the
//!   kernel's identity covers each file that its library compiles.
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — a
//!   stored stratum's key binds the build of the sites.

#[cfg(test)]
extern crate alloc;

use gandr_kernel_core_base::verdict::BuildIdentity;
use gandr_theory_sites::SitesBuild;

/// The theory crates' build identity, which `build.rs` writes.
const SITES_BUILD: &[u8; 32] = include_bytes!(concat!(env!("OUT_DIR"), "/sites-build"));

#[cfg(test)]
mod digest;

/// The kernel's build identity: the digest of each file that the kernel
/// library compiles and of each package that it locks.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn kernel() -> BuildIdentity
{
    BuildIdentity::from(*include_bytes!(concat!(env!("OUT_DIR"), "/kernel-build")))
}

/// The build of the theory sites: the digest of each file that the sites
/// library compiles and of each package that it locks.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn sites() -> SitesBuild
{
    SitesBuild::from(*SITES_BUILD)
}
