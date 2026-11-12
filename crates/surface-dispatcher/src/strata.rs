//! The certified strata a process recalls and keeps.
//!
//! A driver that keeps the kernel's verdicts installs one [`StoredStrata`]
//! beside its verdict cache, under the cache's own policy and key. Every
//! context a composition makes is then handed the store
//! ([`gandr_core_checker::CheckingContext::keep_strata_in`]). A stratum a
//! context certifies is committed by content and named by a root keyed by
//! its bound, its catalogue family with a sub-site's profiles, its degree,
//! its level and the site's build. Its record carries a receipt the
//! installation's key signs. A later read believes the record only under the
//! policy, and the checker replays the image's structure before it uses
//! it. A process that installs none, `check --recheck` among them, certifies
//! each stratum in each context that names it.
//!
//! The store opens with the stratum store, and its register goes to the
//! thread that installs it. A keep commits the stratum on the caller's thread
//! and hands the root's naming to that register with no lock. The stratum
//! store holds each stratum it kept by its key, in tables of slots that are
//! set once, so a recall in the same process reads it before the register's
//! next drain, with no lock.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — the key binds the whole input, the record is
//!   attested, and a full re-check is always available.
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — the
//!   strata persist in the store.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::path::Path;
use std::sync::Mutex;
use std::sync::OnceLock;

use gandr_core_checker::ua::NoStratumStore;
use gandr_core_checker::ua::StratumAt;
use gandr_core_checker::ua::StratumLevel;
use gandr_core_checker::ua::StratumStore;
use gandr_core_checker::ua::recalled;
use gandr_kernel_core::verdict::Attestation;
use gandr_kernel_core::verdict::KernelIdentity;
use gandr_kernel_core::verdict::KernelSigner;
use gandr_kernel_core::verdict::Receipt;
use gandr_kernel_core::verdict::ReceiptSignature;
use gandr_kernel_core::verdict::StratumBytes;
use gandr_kernel_core::verdict::StratumKey;
use gandr_kernel_core::verdict::TrustPolicy;
use gandr_storage_store::ContentPtr;
use gandr_storage_store::Namer;
use gandr_storage_store::Register;
use gandr_storage_store::RootName;
use gandr_storage_store::Store;
use gandr_storage_store::StoreError;
use gandr_storage_store::Stored;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::TokenBytes;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_theory_sites::Family;
use gandr_theory_sites::SitesBuild;
use gandr_theory_sites::StratumImage;
use gandr_theory_sites::Unreplayed;
use quenchant_shape::shape::Maybe;

use crate::verdicts::AlreadyInstalled;
use crate::verdicts::tallied;

/// The tag a kept stratum opens with, and its codec's identifier.
const KEPT: u8 = 0x20_u8;

/// The context a stratum's key derives under.
const KEY_CONTEXT: &str = "gandr checker stratum key 2026-10-30";

/// The store this process installed.
// economy: one store per process, as the verdict cache; a host that needs
// two hands each context its own instead.
static INSTALLED: OnceLock<Arc<StoredStrata>> = OnceLock::new();

/// A stratum's key: the site's build, the bound, the catalogue family with a
/// sub-site's profiles in order, the degree and the level, digested.
///
/// # Specification
/// trivial.
fn key_of(
    family: &Family,
    at: StratumAt,
    level: StratumLevel,
) -> StratumKey
{
    let word = |count: usize| u64::try_from(count).unwrap_or(u64::MAX).to_le_bytes();
    let mut hasher = blake3::Hasher::new_derive_key(KEY_CONTEXT);
    let _site = hasher
        .update(&<[u8; 32]>::from(SitesBuild::current()))
        .update(&word(usize::from(at.bound)));
    match *family {
        Family::Wirings => {
            let _family = hasher.update(&word(0));
        },
        Family::Chains => {
            let _family = hasher.update(&word(1));
        },
        Family::Profiles(ref profiles) => {
            let _family = hasher.update(&word(2)).update(&word(profiles.len()));
            for profile in profiles {
                let _profile = hasher
                    .update(&word(usize::from(profile.inputs)))
                    .update(&word(usize::from(profile.outputs)));
            }
        },
    }
    StratumKey::from(
        *hasher
            .update(&word(usize::from(at.degree)))
            .update(level.to_string().as_bytes())
            .finalize()
            .as_bytes(),
    )
}

/// The prefix of every root naming a stratum.
pub const STRATUM_ROOTS: &str = "stratum/";

/// The root a stratum is named by: its level, its bound, its degree and its
/// key, which digests its catalogue family.
///
/// # Specification
/// trivial.
fn root_of(
    at: StratumAt,
    level: StratumLevel,
    key: StratumKey,
) -> RootName
{
    RootName::new(format!(
        "{STRATUM_ROOTS}{level}/{}/{}/{key}",
        usize::from(at.bound),
        usize::from(at.degree)
    ))
}

/// A stratum as the store holds it: its image and the receipt over it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Kept
{
    /// The stratum's canonical image.
    image: StratumImage,
    /// The installation's receipt over the key and the image.
    receipt: Receipt,
}

impl CanonicalValue for Kept
{
    /// One constructor: the image, the signer and the signature, as bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        sink.open(ConstructorTag::from(KEPT))?;
        sink.bytes(TokenBytes::from(self.image.as_ref()))?;
        sink.bytes(TokenBytes::from(
            &<[u8; 32]>::from(self.receipt.signer())[..],
        ))?;
        sink.bytes(TokenBytes::from(
            &<[u8; 64]>::from(self.receipt.signature())[..],
        ))?;
        sink.close()
    }

    /// The stratum [`Kept::emit_tokens`] wrote.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// A [`ValueError`] when the stream is not one kept stratum.
    #[inline]
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let position = reader.position();
        let found = reader.read_tag()?;
        if found != ConstructorTag::from(KEPT) {
            return Err(ValueError::UnexpectedConstructor { found, position });
        }
        let image = StratumImage::from(Vec::from(<&[u8]>::from(reader.read_bytes()?)));
        let position = reader.position();
        let signer = <[u8; 32]>::try_from(<&[u8]>::from(reader.read_bytes()?))
            .map_err(|_short| ValueError::UnexpectedConstructor { found, position })?;
        let position = reader.position();
        let signature = <[u8; 64]>::try_from(<&[u8]>::from(reader.read_bytes()?))
            .map_err(|_short| ValueError::UnexpectedConstructor { found, position })?;
        reader.read_close()?;
        Ok(Self {
            image,
            receipt: Receipt::new(
                KernelIdentity::from(signer),
                ReceiptSignature::from(signature),
            ),
        })
    }
}

impl Stored for Kept
{
    /// # Specification
    /// trivial.
    #[inline]
    fn codec() -> CodecIdentity
    {
        CodecIdentity::new(CodecId::from(u16::from(KEPT)), CodecVersion::from(1_u16))
    }
}

/// Where a process's certified strata are recalled from and kept to.
///
/// # Specification
/// - ensures: a stratum kept under one installation's key is recalled by a
///   later store over the same directory whose policy lists that key, and by no
///   other.
/// - executable: none — the store and the counts are shared state.
///
/// # Adequacy
/// - hypothesis: L3 — a second store over one directory recalls the image the
///   first kept, a store whose policy lists another key recalls nothing, and a
///   damaged record recalls nothing.
/// - witness: `strata::tests::a_second_store_recalls_what_the_first_kept_4034`
#[derive(Debug)]
pub struct StoredStrata
{
    /// The signers believed: the verdict cache's policy.
    policy: TrustPolicy,
    /// This installation's key: the verdict cache's key.
    signer: KernelSigner,
    /// The store.
    store: Store,
    /// The namer that hands each stratum's root to the store's register.
    namer: Namer,
    /// The strata this store kept, which a recall reads before the
    /// register's snapshot.
    pending: Pending,
    /// Images answered.
    answered: AtomicUsize,
    /// Strata certified and handed to keep.
    certified: AtomicUsize,
    /// Images held under a receipt the policy does not believe.
    unattested: AtomicUsize,
    /// Strata the store could not keep.
    unwritten: AtomicUsize,
    /// Each answered image that did not replay, and why.
    refused: Mutex<Vec<(StratumAt, StratumLevel, Unreplayed)>>,
}

impl StoredStrata
{
    /// The strata believing the receipts `policy` trusts from the store at
    /// `root`, and signing with `signer`, with the store's register.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the store at `root` stands, and the register's
    ///   drain names each stratum that a keep commits.
    /// - fails: the store's faults on opening.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`StoredStrata`].
    /// - witness: `strata::tests::a_second_store_recalls_what_the_first_kept_4034`
    #[inline]
    pub fn open(
        policy: TrustPolicy,
        root: &Path,
        signer: KernelSigner,
    ) -> Result<(Self, Register), StoreError>
    {
        let (store, register) = Store::open(root)?;
        Ok((
            Self {
                policy,
                signer,
                store,
                namer: register.namer(),
                pending: Pending::default(),
                answered: AtomicUsize::new(0),
                certified: AtomicUsize::new(0),
                unattested: AtomicUsize::new(0),
                unwritten: AtomicUsize::new(0),
                refused: Mutex::new(Vec::new()),
            },
            register,
        ))
    }

    /// What this store recalled, certified and refused so far, and the key it
    /// signs with.
    ///
    /// # Specification
    /// trivial.
    fn tally(&self) -> StrataTally
    {
        let refused = self.refused.lock().map_or_else(
            |poisoned| poisoned.into_inner().clone(),
            |held| held.clone(),
        );
        StrataTally {
            recalled: self
                .answered
                .load(Ordering::Relaxed)
                .saturating_sub(refused.len()),
            certified: self.certified.load(Ordering::Relaxed),
            unattested: self.unattested.load(Ordering::Relaxed),
            unwritten: self.unwritten.load(Ordering::Relaxed),
            refused,
            signer: self.signer.identity(),
        }
    }
}

/// The slots of the first table of pending strata. Each later table holds
/// twice the slots of the table before it.
const FIRST_SLOTS: usize = 16_usize;

/// The most tables of pending strata: 16 tables hold more than a million
/// strata, far more than a process keeps.
const TABLES: usize = 16_usize;

/// A stratum that a store kept, by its key, and the pointer that its register
/// names.
type Slot = OnceLock<(StratumKey, ContentPtr)>;

/// The strata that a store kept and handed to its register, by key. A recall
/// reads them before the register's snapshot, so the process recalls a
/// stratum it kept before the register drains. A keep sets one slot, and
/// nothing clears a slot, so neither a keep nor a recall takes a lock. A
/// stratum stays here after the drain that names it, where the snapshot
/// answers it too.
#[repr(transparent)]
#[derive(Debug, Default)]
struct Pending([OnceLock<Box<[Slot]>>; TABLES]);

impl Pending
{
    /// Hold that `key`'s stratum stands at `pointer`.
    ///
    /// # Specification
    /// - requires: `pointer` is the pointer of `key`'s kept stratum.
    /// - ensures: [`Pending::find`] of `key` answers a pointer of `key`'s
    ///   stratum, unless every table is full.
    /// - provides: the hold of a kept stratum until the register names it.
    /// - fails: never; a full map holds nothing more, and a recall misses.
    /// - panics: none.
    /// - executable: none — the slots are shared state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the store that keeps a stratum recalls it before and
    ///   after its register drains.
    /// - witness: `strata::tests::a_second_store_recalls_what_the_first_kept_4034`
    fn hold(
        &self,
        key: StratumKey,
        pointer: ContentPtr,
    )
    {
        let mut slots = FIRST_SLOTS;
        for table in &self.0 {
            let table =
                table.get_or_init(|| core::iter::repeat_with(Slot::new).take(slots).collect());
            if rotated(table, key).any(|slot| slot.get_or_init(|| (key, pointer)).0 == key) {
                return;
            }
            slots = slots.saturating_mul(2);
        }
    }

    /// The pointer that a keep of this store held for `key`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Present` with a pointer that [`Pending::hold`] held for
    ///   `key`; `Absent` when no hold of `key` finished before the read.
    /// - provides: the read of a kept stratum before the register names it.
    /// - fails: never; a key that no keep held is the typed absence.
    /// - panics: none.
    /// - executable: none — the slots are shared state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the store that keeps a stratum recalls it before its
    ///   register drains, and a store opened later does not.
    /// - witness: `strata::tests::a_second_store_recalls_what_the_first_kept_4034`
    fn find(
        &self,
        key: StratumKey,
    ) -> Maybe<ContentPtr, recalled::Absent>
    {
        for table in &self.0 {
            let Some(table) = table.get()
            else {
                break;
            };
            for slot in rotated(table, key) {
                match slot.get() {
                    None => return Maybe::Absent(recalled::Absent::Unkept),
                    Some(&(held, pointer)) if held == key => return Maybe::Present(pointer),
                    Some(_) => {},
                }
            }
        }
        Maybe::Absent(recalled::Absent::Unkept)
    }
}

/// The slots of `table`, from the one that `key`'s first eight bytes choose,
/// round to the slot before it.
///
/// # Specification
/// trivial.
fn rotated(
    table: &[Slot],
    key: StratumKey,
) -> impl Iterator<Item = &Slot>
{
    let bytes = <[u8; 32]>::from(key);
    let word = bytes
        .first_chunk::<8>()
        .map_or(0_u64, |head| u64::from_le_bytes(*head));
    let length = u64::try_from(table.len()).unwrap_or(u64::MAX);
    let start = word
        .checked_rem(length)
        .and_then(|start| usize::try_from(start).ok())
        .unwrap_or(0_usize);
    table.iter().skip(start).chain(table.iter().take(start))
}

impl StratumStore for StoredStrata
{
    /// The image the store names at the stratum's root, when its receipt is
    /// one the policy believes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn recall(
        &self,
        family: &Family,
        at: StratumAt,
        level: StratumLevel,
    ) -> Maybe<StratumImage, recalled::Absent>
    {
        let key = key_of(family, at, level);
        let pointer = match self.pending.find(key) {
            Maybe::Present(pointer) => pointer,
            Maybe::Absent(_) => {
                let Maybe::Present(pointer) = self.store.roots().root(&root_of(at, level, key))
                else {
                    return Maybe::Absent(recalled::Absent::Unkept);
                };
                pointer
            },
        };
        let Ok(kept) = self.store.deref::<Kept>(pointer)
        else {
            return Maybe::Absent(recalled::Absent::Unkept);
        };
        match self.policy.believes_stratum(
            &kept.receipt,
            key,
            StratumBytes::from(kept.image.as_ref()),
        ) {
            Attestation::Attested => {
                let _before = self.answered.fetch_add(1, Ordering::Relaxed);
                Maybe::Present(kept.image)
            },
            Attestation::Refused => {
                let _before = self.unattested.fetch_add(1, Ordering::Relaxed);
                Maybe::Absent(recalled::Absent::Unattested)
            },
        }
    }

    /// Commit the stratum's image under this installation's receipt, and hand
    /// its naming by the stratum's root to the store's register.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn keep(
        &self,
        family: &Family,
        at: StratumAt,
        level: StratumLevel,
        image: &StratumImage,
    )
    {
        let _before = self.certified.fetch_add(1, Ordering::Relaxed);
        let key = key_of(family, at, level);
        let kept = Kept {
            receipt: self
                .signer
                .sign_stratum(key, StratumBytes::from(image.as_ref())),
            image: image.clone(),
        };
        let written = self
            .store
            .commit(&kept)
            .and_then(|pointer| {
                self.pending.hold(key, pointer);
                self.namer.name(root_of(at, level, key), pointer)
            })
            .is_ok();
        if !written {
            let _before = self.unwritten.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// Hold the refusal, for the tally to name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn refuse(
        &self,
        _family: &Family,
        at: StratumAt,
        level: StratumLevel,
        why: Unreplayed,
    )
    {
        match self.refused.lock() {
            Ok(mut refused) => refused.push((at, level, why)),
            Err(poisoned) => poisoned.into_inner().push((at, level, why)),
        }
    }
}

/// Install `strata` for every context this process's compositions make
/// after, unless a store is installed already, which stays.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`AlreadyInstalled`].
#[inline]
pub fn install_stratum_store(strata: StoredStrata) -> Result<(), AlreadyInstalled>
{
    INSTALLED
        .set(Arc::new(strata))
        .map_err(|_refused| AlreadyInstalled)
}

/// The store each context is handed: the one installed, or one holding
/// nothing.
///
/// # Specification
/// trivial.
pub fn stratum_store() -> Arc<dyn StratumStore>
{
    match INSTALLED.get() {
        Some(installed) => Arc::<StoredStrata>::clone(installed),
        None => Arc::new(NoStratumStore),
    }
}

/// What the installed store recalled, certified and refused so far, and the
/// key it signs with.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StrataTally
{
    /// Images that replayed in place of a certification.
    recalled: usize,
    /// Strata certified and handed to keep.
    certified: usize,
    /// Images held under a receipt the policy does not believe.
    unattested: usize,
    /// Strata the store could not keep.
    unwritten: usize,
    /// Each answered image that did not replay, and why.
    refused: Vec<(StratumAt, StratumLevel, Unreplayed)>,
    /// The public half of this installation's key.
    signer: KernelIdentity,
}

impl StrataTally
{
    /// Whether any stratum was asked for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn asked(&self) -> Asking
    {
        if self.recalled == 0
            && self.certified == 0
            && self.unattested == 0
            && self.refused.is_empty()
        {
            Asking::Unasked
        }
        else {
            Asking::Asked
        }
    }

    /// Each refusal, as one line naming the stratum and why its image did not
    /// replay.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn refusals(&self) -> impl Iterator<Item = String>
    {
        self.refused.iter().map(|&(ref at, level, why)| {
            format!(
                "refused the stored stratum of level {level} at bound {}, degree {}: {why}",
                usize::from(at.bound),
                usize::from(at.degree)
            )
        })
    }
}

/// Whether a run asked its store for any stratum.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Asking
{
    /// No stratum was asked for.
    Unasked,
    /// At least one was.
    Asked,
}

impl fmt::Display for StrataTally
{
    /// `<n> recalled, <n> certified, <n> refused, <n> unattested, <n>
    /// unwritten; signed by <key>`.
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
            "{} recalled, {} certified, {} refused, {} unattested, {} unwritten; signed by {}",
            self.recalled,
            self.certified,
            self.refused.len(),
            self.unattested,
            self.unwritten,
            self.signer
        )
    }
}

/// The installed store's tally.
///
/// # Specification
/// trivial.
#[inline]
pub fn strata_tally() -> Maybe<StrataTally, tallied::Absent>
{
    INSTALLED
        .get()
        .map_or(Maybe::Absent(tallied::Absent::Uninstalled), |strata| {
            Maybe::Present(strata.tally())
        })
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::sync::Arc;
    use std::path::Path;

    use gandr_core_checker::ua::StratumAt;
    use gandr_core_checker::ua::StratumLevel;
    use gandr_core_checker::ua::StratumStore as _;
    use gandr_core_checker::ua::recalled;
    use gandr_kernel_core::verdict::KernelSigner;
    use gandr_kernel_core::verdict::TrustPolicy;
    use gandr_theory_sites::Catalogue;
    use gandr_theory_sites::Degree;
    use gandr_theory_sites::Family;
    use gandr_theory_sites::PortCount;
    use gandr_theory_sites::Profile;
    use gandr_theory_sites::SegalStratum;
    use gandr_theory_sites::ShapeBudget;
    use gandr_theory_sites::ShapeSize;
    use gandr_theory_sites::StratumImage;
    use quenchant_shape::shape::Maybe;

    use super::StoredStrata;

    /// The policy trusting `signer` alone.
    ///
    /// # Specification
    /// trivial.
    fn trusting(signer: &KernelSigner) -> TrustPolicy
    {
        TrustPolicy::Trusted(BTreeSet::from([signer.identity()]))
    }

    /// The profile of `inputs` input legs and one output leg.
    ///
    /// # Specification
    /// trivial.
    fn operation(inputs: PortCount) -> Profile
    {
        Profile {
            inputs,
            outputs: PortCount::from(1_usize),
        }
    }

    /// #4034: a stratum kept under one key is recalled by a second store over
    /// the same directory that believes the key, as the image the first kept.
    /// A store believing another key recalls nothing, and so does one asked
    /// for another degree or, #4035, another sub-site. #4123: the store keeps
    /// level one and level two at one stratum under two keys. #6899: the store
    /// that keeps a stratum recalls it before its register drains, and a store
    /// opened before the drain does not.
    #[test]
    fn a_second_store_recalls_what_the_first_kept_4034()
    {
        let directory = std::env::temp_dir().join(format!(
            "gandr-strata-{}-{}",
            std::process::id(),
            "a_second_store_recalls_what_the_first_kept_4034"
        ));
        let _cleared = std::fs::remove_dir_all(&directory);
        let root = Path::new(&directory).to_path_buf();
        let signer = KernelSigner::from([7_u8; 32]);
        let profiles = BTreeSet::from([
            operation(PortCount::from(2_usize)),
            operation(PortCount::from(0_usize)),
        ]);
        let at = StratumAt {
            bound: ShapeSize::from(4_usize),
            degree: Degree::from(2_usize),
        };
        let catalogue = Arc::new(
            Catalogue::profiles(at.bound, profiles.clone(), ShapeBudget::EVERY)
                .expect("the magma's sub-site at size four builds"),
        );
        let family = Family::Profiles(profiles);
        let stratum = SegalStratum::certify(catalogue, at.degree).expect("degree two is certified");

        let (first, mut register) = StoredStrata::open(trusting(&signer), &root, signer.clone())
            .expect("the stratum store opens");
        let one = StratumLevel::One;
        assert!(matches!(
            first.recall(&family, at, one),
            Maybe::Absent(recalled::Absent::Unkept)
        ));
        first.keep(&family, at, one, &stratum.image());
        let two = StratumImage::from(Vec::from([2_u8]));
        first.keep(&family, at, StratumLevel::Two, &two);
        assert_eq!(
            first.recall(&family, at, one),
            Maybe::Present(stratum.image()),
            "the store that kept the stratum recalls it before the drain"
        );
        let (early, _register) = StoredStrata::open(trusting(&signer), &root, signer.clone())
            .expect("the stratum store opens before the drain");
        assert!(
            matches!(
                early.recall(&family, at, one),
                Maybe::Absent(recalled::Absent::Unkept)
            ),
            "a store opened before the drain reads no root of the stratum"
        );
        register.drain().expect("the register names both strata");
        assert_eq!(
            first.recall(&family, at, one),
            Maybe::Present(stratum.image()),
            "the store that kept the stratum recalls it after the drain"
        );

        let (second, _register) = StoredStrata::open(trusting(&signer), &root, signer.clone())
            .expect("the stratum store opens again");
        assert_eq!(
            second.recall(&family, at, one),
            Maybe::Present(stratum.image()),
            "the second store recalls the image the first kept"
        );
        assert_eq!(
            second.recall(&family, at, StratumLevel::Two),
            Maybe::Present(two),
            "level two is another root"
        );
        assert!(
            matches!(
                second.recall(
                    &family,
                    StratumAt {
                        degree: Degree::from(3_usize),
                        ..at
                    },
                    one
                ),
                Maybe::Absent(recalled::Absent::Unkept)
            ),
            "another degree is another root"
        );
        assert!(
            matches!(
                second.recall(
                    &Family::Profiles(BTreeSet::from([operation(PortCount::from(2_usize))])),
                    at,
                    one
                ),
                Maybe::Absent(recalled::Absent::Unkept)
            ),
            "another sub-site is another root"
        );
        assert!(
            matches!(
                second.recall(&Family::Wirings, at, one),
                Maybe::Absent(recalled::Absent::Unkept)
            ),
            "the whole catalogue is another root"
        );

        let other = KernelSigner::from([8_u8; 32]);
        let (foreign, _register) = StoredStrata::open(trusting(&other), &root, other.clone())
            .expect("the stratum store opens a third time");
        assert!(
            matches!(
                foreign.recall(&family, at, one),
                Maybe::Absent(recalled::Absent::Unattested)
            ),
            "a store believing another key recalls nothing"
        );
        let _cleared = std::fs::remove_dir_all(&directory);
    }

    /// #4437: the store keeps one image per level at one stratum, levels one
    /// to four, and a second store recalls each level's own. Levels one and
    /// two keep the roots they had before levels three and four, so a store
    /// written then still recalls them.
    #[test]
    fn each_level_keeps_its_own_root_and_the_first_two_keep_theirs_4437()
    {
        let directory = std::env::temp_dir().join(format!(
            "gandr-strata-{}-{}",
            std::process::id(),
            "each_level_keeps_its_own_root_and_the_first_two_keep_theirs_4437"
        ));
        let _cleared = std::fs::remove_dir_all(&directory);
        let root = Path::new(&directory).to_path_buf();
        let signer = KernelSigner::from([7_u8; 32]);
        let at = StratumAt {
            bound: ShapeSize::from(9_usize),
            degree: Degree::from(5_usize),
        };
        let levels = [
            StratumLevel::One,
            StratumLevel::Two,
            StratumLevel::Three,
            StratumLevel::Four,
        ];
        let image = |level: StratumLevel| StratumImage::from(level.to_string().into_bytes());
        let (first, mut register) = StoredStrata::open(trusting(&signer), &root, signer.clone())
            .expect("the stratum store opens");
        for level in levels {
            first.keep(&Family::Chains, at, level, &image(level));
        }
        register.drain().expect("the register names each level");
        let (second, _register) = StoredStrata::open(trusting(&signer), &root, signer.clone())
            .expect("the stratum store opens again");
        for level in levels {
            assert_eq!(
                second.recall(&Family::Chains, at, level),
                Maybe::Present(image(level)),
                "level {level} recalls its own image"
            );
        }
        for (level, spelled) in [(StratumLevel::One, "1"), (StratumLevel::Two, "2")] {
            let key = super::key_of(&Family::Chains, at, level);
            assert_eq!(
                super::root_of(at, level, key),
                super::RootName::new(format!("stratum/{spelled}/9/5/{key}")),
                "level {spelled} keeps the root it had before level three"
            );
        }
        let _cleared = std::fs::remove_dir_all(&directory);
    }
}
