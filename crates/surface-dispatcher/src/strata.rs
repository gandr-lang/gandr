//! The certified strata a process recalls and keeps.
//!
//! A driver that keeps the kernel's verdicts installs one [`StoredStrata`]
//! beside its verdict cache, under the cache's own policy and key. Every
//! context a composition makes is then handed the store
//! ([`gandr_core_checker::CheckingContext::keep_strata_in`]). A stratum a
//! context certifies is committed by content and named by a root keyed by
//! its bound, its catalogue family with a sub-site's profiles, its degree and
//! the site's build.
//! Its record carries a receipt
//! the installation's key signs. A later read believes the record only under
//! the policy, and the checker replays the image's structure before it uses
//! it. A process that installs none, `check --recheck` among them, certifies
//! each stratum in each context that names it.
//!
//! The store opens on the first stratum a context asks for, so a run that
//! names none never touches it.
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
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::OnceLock;

use gandr_core_checker::ua::NoStratumStore;
use gandr_core_checker::ua::StratumAt;
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
use gandr_theory_sites::SegalStratum;
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
/// sub-site's profiles in order, and the degree, digested.
///
/// # Specification
/// trivial.
fn key_of(
    family: &Family,
    at: StratumAt,
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
            .finalize()
            .as_bytes(),
    )
}

/// The root a stratum is named by: its bound, its degree and its key, which
/// digests its catalogue family.
///
/// # Specification
/// trivial.
fn root_of(
    at: StratumAt,
    key: StratumKey,
) -> RootName
{
    RootName::new(format!(
        "stratum/{}/{}/{key}",
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
    /// The store's directory.
    root: PathBuf,
    /// The store, opened on first use.
    store: OnceLock<Result<Mutex<Store>, StoreError>>,
    /// Images answered.
    answered: AtomicUsize,
    /// Strata certified and handed to keep.
    certified: AtomicUsize,
    /// Images held under a receipt the policy does not believe.
    unattested: AtomicUsize,
    /// Strata the store could not keep.
    unwritten: AtomicUsize,
    /// Each answered image that did not replay, and why.
    refused: Mutex<Vec<(StratumAt, Unreplayed)>>,
}

impl StoredStrata
{
    /// The strata believing the receipts `policy` trusts from the store at
    /// `root`, and signing with `signer`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        policy: TrustPolicy,
        root: PathBuf,
        signer: KernelSigner,
    ) -> Self
    {
        Self {
            policy,
            signer,
            root,
            store: OnceLock::new(),
            answered: AtomicUsize::new(0),
            certified: AtomicUsize::new(0),
            unattested: AtomicUsize::new(0),
            unwritten: AtomicUsize::new(0),
            refused: Mutex::new(Vec::new()),
        }
    }

    /// The store, opened on first use; absent when it does not open.
    ///
    /// # Specification
    /// trivial.
    fn store(&self) -> Option<&Mutex<Store>>
    {
        self.store
            .get_or_init(|| Store::open(&self.root).map(Mutex::new))
            .as_ref()
            .ok()
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
    ) -> Maybe<StratumImage, recalled::Absent>
    {
        let key = key_of(family, at);
        let kept = self.store().and_then(|store| {
            let store = store.lock().ok()?;
            let Maybe::Present(pointer) = store.roots().root(&root_of(at, key))
            else {
                return None;
            };
            store.deref::<Kept>(pointer).ok()
        });
        let Some(kept) = kept
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

    /// Commit the stratum's image under this installation's receipt, and name
    /// it by the stratum's root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn keep(
        &self,
        family: &Family,
        at: StratumAt,
        stratum: &SegalStratum,
    )
    {
        let _before = self.certified.fetch_add(1, Ordering::Relaxed);
        let key = key_of(family, at);
        let image = stratum.image();
        let kept = Kept {
            receipt: self
                .signer
                .sign_stratum(key, StratumBytes::from(image.as_ref())),
            image,
        };
        let written = self.store().is_some_and(|store| {
            store.lock().is_ok_and(|mut store| {
                store
                    .commit(&kept)
                    .and_then(|pointer| store.set_root(root_of(at, key), pointer))
                    .is_ok()
            })
        });
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
        why: Unreplayed,
    )
    {
        match self.refused.lock() {
            Ok(mut refused) => refused.push((at, why)),
            Err(poisoned) => poisoned.into_inner().push((at, why)),
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
    refused: Vec<(StratumAt, Unreplayed)>,
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
        self.refused.iter().map(|&(ref at, why)| {
            format!(
                "refused the stored stratum at bound {}, degree {}: {why}",
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
    /// for another degree or, #4035, another sub-site.
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

        let first = StoredStrata::new(trusting(&signer), root.clone(), signer.clone());
        assert!(matches!(
            first.recall(&family, at),
            Maybe::Absent(recalled::Absent::Unkept)
        ));
        first.keep(&family, at, &stratum);

        let second = StoredStrata::new(trusting(&signer), root.clone(), signer.clone());
        assert_eq!(
            second.recall(&family, at),
            Maybe::Present(stratum.image()),
            "the second store recalls the image the first kept"
        );
        assert!(
            matches!(
                second.recall(&family, StratumAt {
                    degree: Degree::from(3_usize),
                    ..at
                }),
                Maybe::Absent(recalled::Absent::Unkept)
            ),
            "another degree is another root"
        );
        assert!(
            matches!(
                second.recall(
                    &Family::Profiles(BTreeSet::from([operation(PortCount::from(2_usize))])),
                    at
                ),
                Maybe::Absent(recalled::Absent::Unkept)
            ),
            "another sub-site is another root"
        );
        assert!(
            matches!(
                second.recall(&Family::Wirings, at),
                Maybe::Absent(recalled::Absent::Unkept)
            ),
            "the whole catalogue is another root"
        );

        let other = KernelSigner::from([8_u8; 32]);
        let foreign = StoredStrata::new(trusting(&other), root, other.clone());
        assert!(
            matches!(
                foreign.recall(&family, at),
                Maybe::Absent(recalled::Absent::Unattested)
            ),
            "a store believing another key recalls nothing"
        );
        let _cleared = std::fs::remove_dir_all(&directory);
    }
}
