//! The store a hub reads for its renderers: the account of the store under
//! its data directory, as one card.
//!
//! A [`Stored`] names the directory of the store and keeps its account
//! between readings. Each reading opens the store, refreshes the account and
//! lets the store go, so the images that a walk read do not stay in memory.
//! Only the account's rows and the in-degree of each chunk stay. The identities
//! the account reads are the pointers that the lock of each package records,
//! for each package that holds an open document.
//!
//! The card names each cell that no layer fills yet, with its unit, and the
//! store's refusal to open when it does not open.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-store gives the store pane that the card feeds.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::num::NonZeroU32;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;

use gandr_surface_dispatcher::Lock;
use gandr_surface_dispatcher::Owed;
use gandr_surface_dispatcher::Package;
use gandr_surface_dispatcher::StoreAccount;
use gandr_surface_dispatcher::StoredKind;
use gandr_surface_dispatcher::StoredRow;
use gandr_surface_render_remote::Count;
use gandr_surface_render_remote::OwedCell;
use gandr_surface_render_remote::StoreCard;
use gandr_surface_render_remote::StoreKey;
use gandr_surface_render_remote::StoreKind;
use gandr_surface_render_remote::StoreResidence;
use gandr_surface_render_remote::StoreRow;
use gandr_surface_render_remote::UnitNumber;
use quenchant_shape::shape::Maybe;

use crate::hub::lock;

/// The store under a hub's data directory, and its account as the hub read
/// it last.
#[derive(Debug)]
pub struct Stored
{
    /// The directory of the store.
    directory: PathBuf,
    /// The account as the hub read it last.
    account: Mutex<StoreAccount>,
}

impl Stored
{
    /// The store at `directory`, its account not read yet.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn at(directory: PathBuf) -> Self
    {
        Self {
            directory,
            account: Mutex::new(StoreAccount::default()),
        }
    }

    /// The card of the store, read again for the open documents at `paths`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the rows of the account after [`StoreAccount::read`] of the
    ///   store's directory, the identities those that the locks of the packages
    ///   of `paths` record; each cell of [`Owed::ALL`] with its unit; and the
    ///   store's refusal when it did not open, the rows then as the hub read
    ///   them last.
    /// - provides: the card that a renderer is sent as it attaches.
    /// - fails: never; a refusal is the card's.
    /// - panics: none.
    /// - executable: none — the card depends on the file system.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a renderer attached to a hub whose store holds two
    ///   values hears the card of both after the greeting, with each owed
    ///   cell's unit.
    /// - witness: `hub::tests::an_attached_view_hears_the_store_6296`
    pub(crate) fn card(
        &self,
        paths: &[PathBuf],
    ) -> StoreCard
    {
        let identities: BTreeSet<_> = locks(paths).iter().flat_map(Lock::pointers).collect();
        let mut account = lock(&self.account);
        let refused = account
            .read(&self.directory, &identities)
            .err()
            .map(|fault| fault.to_string());
        let rows = account.rows().map(row).collect();
        drop(account);
        StoreCard {
            rows,
            owed: Owed::ALL
                .into_iter()
                .map(|owed| OwedCell {
                    column: String::from(<&str>::from(owed)),
                    unit: UnitNumber::from(NonZeroU32::from(owed)),
                })
                .collect(),
            refused,
        }
    }
}

/// The lock of each package that holds one of `paths`, each package once.
///
/// # Specification
/// trivial.
fn locks(paths: &[PathBuf]) -> Vec<Lock>
{
    let mut roots: BTreeSet<&Path> = BTreeSet::new();
    let mut packages = Vec::new();
    for path in paths {
        if let Maybe::Present(package) = Package::discover(path) {
            packages.push(package);
        }
    }
    let mut locks = Vec::new();
    for package in &packages {
        if roots.insert(package.root())
            && let Maybe::Present(lock) = Lock::read(package)
        {
            locks.push(lock);
        }
    }
    locks
}

/// The card's row of `stored`.
///
/// # Specification
/// trivial.
fn row(stored: StoredRow<'_>) -> StoreRow
{
    let digest = stored.pointer.digest();
    let offset = u32::from(stored.pointer.offset());
    let key = if offset == 0 {
        digest.to_string()
    }
    else {
        alloc::format!("{digest}+{offset}")
    };
    StoreRow {
        key: StoreKey::from(key),
        kind: match stored.kind {
            StoredKind::Receipt => StoreKind::Receipt,
            StoredKind::Stratum => StoreKind::Stratum,
            StoredKind::Export => StoreKind::Export,
            StoredKind::Identity => StoreKind::Identity,
        },
        residence: match stored.residence {
            Ok(resident) => StoreResidence::Cam {
                bytes: Count(u64::from(resident.bytes)),
                chunks: Count(u64::try_from(usize::from(resident.chunks)).unwrap_or(u64::MAX)),
                shared: Count(u64::try_from(usize::from(resident.shared)).unwrap_or(u64::MAX)),
            },
            Err(fault) => StoreResidence::Refused {
                why: fault.to_string(),
            },
        },
    }
}
