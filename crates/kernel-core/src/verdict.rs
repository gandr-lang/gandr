//! Verdicts the kernel recalls instead of replaying: a key over its whole
//! input, a receipt its signer attests, and a policy naming the signers a run
//! believes.
//!
//! A key is a BLAKE3 chain. It starts at the kernel's build identity, a digest
//! of every kernel crate's files and the workspace lock, and each admission
//! extends it by the declaration's canonical segment, so a key closes over
//! the whole admitted prefix. Equal keys are equal kernel inputs. A recall is
//! integrity, never validity: the record names bytes the kernel judged, and
//! the receipt names the kernel that judged them. The kernel signs only what
//! it checked itself ([`Environment::receipt`](crate::Environment::receipt)),
//! and admits a recalled declaration only when a receipt from a signer the
//! [`TrustPolicy`] lists verifies over the record. Under
//! [`TrustPolicy::Recheck`] nothing is keyed and nothing is recalled.
//!
//! A rejection, a bypass, a mutual block or an open seal ends the chain. A
//! refusal is never recorded. [`Environment::handed_on`] hands the chain to a
//! resumed run without its records.
//!
//! [`Environment::handed_on`]: crate::Environment::handed_on
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — the key binds the kernel's whole input under a
//!   collision-resistant hash, the record is attested, and a full re-check is
//!   always available.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;

use ed25519_dalek::Signer as _;
use gandr_kernel_term::EncodedArtifact;
use gandr_kernel_term::SegmentEncoder;
use gandr_kernel_term::StagedPosition;
use gandr_kernel_term::TermArena;
use quenchant_shape::shape::Maybe;

use crate::check::occurrence::Accessibility;
use crate::check::occurrence::Stratification;
use crate::check::occurrence::Variance;

/// The kernel's build identity, which `build.rs` writes.
const KERNEL_BUILD: &[u8; 32] = include_bytes!(concat!(env!("OUT_DIR"), "/kernel-build"));

/// The context a verdict key's digest derives under.
const KEY_CONTEXT: &str = "gandr kernel verdict key 2026-10-27";

/// The context a receipt's message derives under.
const RECEIPT_CONTEXT: &str = "gandr kernel verdict receipt 2026-10-27";

/// The version byte every encoded verdict leads with.
const VERDICT_VERSION: u8 = 1;

/// A key over the kernel's whole input for one admission: its build, and every
/// declaration admitted up to and including this one.
///
/// # Specification
/// - ensures: two keys are equal exactly when, up to a BLAKE3 collision, they
///   chain the same build identity over the same canonical segments.
/// - provides: the identity a recorded verdict is recalled by.
/// - panics: none.
/// - executable: none — collision resistance is BLAKE3's.
///
/// # Adequacy
/// - hypothesis: L3 — a recorded verdict is recalled under its own key and not
///   after one name changes.
/// - witness: `tests::verdicts::a_verdict_is_recalled_only_under_its_own_key`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct VerdictKey([u8; 32]);

impl From<[u8; 32]> for VerdictKey
{
    /// The key whose digest is `bytes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; 32]) -> Self
    {
        Self(bytes)
    }
}

impl From<VerdictKey> for [u8; 32]
{
    /// The digest of `key`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(key: VerdictKey) -> Self
    {
        key.0
    }
}

impl VerdictKey
{
    /// The key before any declaration: this kernel's build identity alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn start() -> Self
    {
        Self(
            *blake3::Hasher::new_derive_key(KEY_CONTEXT)
                .update(KERNEL_BUILD)
                .finalize()
                .as_bytes(),
        )
    }

    /// The key of the declaration whose canonical segment is `segment`,
    /// admitted after the ones this key closes over.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn after(
        self,
        segment: &EncodedArtifact,
    ) -> Self
    {
        Self(
            *blake3::Hasher::new_derive_key(KEY_CONTEXT)
                .update(&self.0)
                .update(segment.as_ref())
                .finalize()
                .as_bytes(),
        )
    }
}

/// A verdict's canonical bytes: what an admission read of the declaration.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct EncodedVerdict(Vec<u8>);

impl AsRef<[u8]> for EncodedVerdict
{
    /// The bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

impl EncodedVerdict
{
    /// Append `stratification`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn put_stratification(
        &mut self,
        stratification: Stratification,
    )
    {
        self.0.push(match stratification {
            Stratification::Positive => 0,
            Stratification::Stratified => 1,
        });
    }

    /// Append the variances of a reading's parameters, counted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn put_variances(
        &mut self,
        variances: &[Variance],
    )
    {
        self.0.extend_from_slice(
            &u64::try_from(variances.len())
                .unwrap_or(u64::MAX)
                .to_le_bytes(),
        );
        self.0
            .extend(variances.iter().map(|variance| match *variance {
                Variance::StrictlyPositive => 0_u8,
                Variance::NotStrictlyPositive => 1_u8,
            }));
    }

    /// Append the position a definition's result follows, when it follows
    /// one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn put_following(
        &mut self,
        following: Maybe<StagedPosition, following::Absent>,
    )
    {
        match following {
            Maybe::Present(position) => {
                self.0.push(1);
                self.0.extend_from_slice(
                    &u64::try_from(usize::from(position))
                        .unwrap_or(u64::MAX)
                        .to_le_bytes(),
                );
            },
            Maybe::Absent(following::Absent::Plain) => self.0.push(0),
        }
    }
}

/// A verdict's bytes as a store holds them, read back.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct VerdictImage<'bytes>
{
    /// The bytes not yet read.
    rest: &'bytes [u8],
}

impl<'bytes> From<&'bytes [u8]> for VerdictImage<'bytes>
{
    /// The image of `bytes`, read from its start.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'bytes [u8]) -> Self
    {
        Self { rest: bytes }
    }
}

quenchant_shape::reason_enum! {
    /// Why a verdict image holds no reading.
    pub mod verdict_image {
        /// The reason no reading is read.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The bytes are not a verdict this kernel writes.
            Malformed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a definition's recorded result follows no parameter's stage.
    pub mod following {
        /// The reason the result follows none.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The result's type is refined at no stage.
            Plain,
        }
    }
}

impl VerdictImage<'_>
{
    /// Read the next byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn tag(&mut self) -> Maybe<VerdictTag, verdict_image::Absent>
    {
        let Some((&first, rest)) = self.rest.split_first()
        else {
            return Maybe::Absent(verdict_image::Absent::Malformed);
        };
        self.rest = rest;
        Maybe::Present(VerdictTag(first))
    }

    /// Read the next little-endian count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn count(&mut self) -> Maybe<VerdictCount, verdict_image::Absent>
    {
        let Some((head, rest)) = self.rest.split_first_chunk::<8>()
        else {
            return Maybe::Absent(verdict_image::Absent::Malformed);
        };
        self.rest = rest;
        usize::try_from(u64::from_le_bytes(*head))
            .map_or(Maybe::Absent(verdict_image::Absent::Malformed), |count| {
                Maybe::Present(VerdictCount(count))
            })
    }

    /// Read a stratification.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn stratification(&mut self) -> Maybe<Stratification, verdict_image::Absent>
    {
        match self.tag() {
            Maybe::Present(VerdictTag(0)) => Maybe::Present(Stratification::Positive),
            Maybe::Present(VerdictTag(1)) => Maybe::Present(Stratification::Stratified),
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(verdict_image::Absent::Malformed),
        }
    }

    /// Read a reading's counted parameter variances.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn variances(&mut self) -> Maybe<Vec<Variance>, verdict_image::Absent>
    {
        let Maybe::Present(VerdictCount(count)) = self.count()
        else {
            return Maybe::Absent(verdict_image::Absent::Malformed);
        };
        if count > self.rest.len() {
            return Maybe::Absent(verdict_image::Absent::Malformed);
        }
        let mut variances = Vec::with_capacity(count);
        for _ in 0 .. count {
            match self.tag() {
                Maybe::Present(VerdictTag(0)) => variances.push(Variance::StrictlyPositive),
                Maybe::Present(VerdictTag(1)) => variances.push(Variance::NotStrictlyPositive),
                Maybe::Present(_) | Maybe::Absent(_) => {
                    return Maybe::Absent(verdict_image::Absent::Malformed);
                },
            }
        }
        Maybe::Present(variances)
    }

    /// Read the position a definition's result follows, itself absent as
    /// [`following::Absent::Plain`] when it follows none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn following(
        &mut self
    ) -> Maybe<Maybe<StagedPosition, following::Absent>, verdict_image::Absent>
    {
        match self.tag() {
            Maybe::Present(VerdictTag(0)) => {
                Maybe::Present(Maybe::Absent(following::Absent::Plain))
            },
            Maybe::Present(VerdictTag(1)) => match self.count() {
                Maybe::Present(VerdictCount(position)) => {
                    Maybe::Present(Maybe::Present(StagedPosition::from(position)))
                },
                Maybe::Absent(absent) => Maybe::Absent(absent),
            },
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(verdict_image::Absent::Malformed),
        }
    }
}

/// One byte of a verdict image.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct VerdictTag(u8);

/// A count or position a verdict image holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct VerdictCount(usize);

/// One recorded verdict: the key the kernel computed for a declaration it
/// admitted, and what its admission read.
///
/// # Specification
/// - ensures: [`VerdictRecord::decode`] of a record's key and
///   [`VerdictRecord::encoded`] bytes is the record.
/// - provides: what a store keeps per declaration and a receipt attests.
/// - panics: none.
/// - executable: none — the fields are private and set by the kernel or by
///   [`VerdictRecord::decode`].
///
/// # Adequacy
/// - hypothesis: L3 — a record round-trips through its bytes and a truncated or
///   retagged image is refused.
/// - witness: `tests::verdicts::a_record_reads_back_and_a_damaged_one_is_refused`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerdictRecord
{
    /// The key over the kernel's input for the admission.
    key: VerdictKey,
    /// What the admission read of the declaration.
    accessibility: Accessibility,
}

impl VerdictRecord
{
    /// The key over the kernel's input for the admission.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn key(&self) -> VerdictKey
    {
        self.key
    }

    /// The verdict's canonical bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn encoded(&self) -> EncodedVerdict
    {
        let mut out = EncodedVerdict(Vec::from([VERDICT_VERSION]));
        self.accessibility.write(&mut out);
        out
    }

    /// The record of `key` whose verdict bytes are `image`.
    ///
    /// # Specification
    /// - ensures: present exactly when `image` is one this kernel's
    ///   [`VerdictRecord::encoded`] writes, whole.
    /// - fails: never; malformed bytes are absent as
    ///   [`verdict_image::Absent::Malformed`].
    /// - panics: none.
    /// - executable: none — "the bytes this kernel writes" is the encoder's
    ///   whole range, which only the round trip the witness runs states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`VerdictRecord`].
    /// - witness: `tests::verdicts::a_record_reads_back_and_a_damaged_one_is_refused`
    #[inline]
    pub fn decode(
        key: VerdictKey,
        mut image: VerdictImage<'_>,
    ) -> Maybe<Self, verdict_image::Absent>
    {
        if !matches!(image.tag(), Maybe::Present(VerdictTag(VERDICT_VERSION))) {
            return Maybe::Absent(verdict_image::Absent::Malformed);
        }
        let Maybe::Present(accessibility) = Accessibility::read(&mut image)
        else {
            return Maybe::Absent(verdict_image::Absent::Malformed);
        };
        if !image.rest.is_empty() {
            return Maybe::Absent(verdict_image::Absent::Malformed);
        }
        Maybe::Present(Self { key, accessibility })
    }
}

/// A kernel installation's public identity: the key its receipts verify
/// under.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct KernelIdentity([u8; 32]);

impl From<[u8; 32]> for KernelIdentity
{
    /// The identity whose public key is `bytes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; 32]) -> Self
    {
        Self(bytes)
    }
}

impl From<KernelIdentity> for [u8; 32]
{
    /// The public key of `identity`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(identity: KernelIdentity) -> Self
    {
        identity.0
    }
}

impl core::fmt::Display for KernelIdentity
{
    /// The public key as 64 lowercase hexadecimal digits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        self.0.iter().try_for_each(|byte| write!(f, "{byte:02x}"))
    }
}

/// A receipt's Ed25519 signature.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ReceiptSignature([u8; 64]);

impl From<[u8; 64]> for ReceiptSignature
{
    /// The signature whose bytes are `bytes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; 64]) -> Self
    {
        Self(bytes)
    }
}

impl From<ReceiptSignature> for [u8; 64]
{
    /// The bytes of `signature`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(signature: ReceiptSignature) -> Self
    {
        signature.0
    }
}

/// A kernel's attestation of a set of verdict records: who signed, and the
/// signature over the records' digest.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Receipt
{
    /// The kernel that signed.
    signer: KernelIdentity,
    /// Its signature over the records' digest.
    signature: ReceiptSignature,
}

impl Receipt
{
    /// The receipt `signer` gave as `signature`, as a store read it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        signer: KernelIdentity,
        signature: ReceiptSignature,
    ) -> Self
    {
        Self { signer, signature }
    }

    /// The kernel that signed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn signer(&self) -> KernelIdentity
    {
        self.signer
    }

    /// The signature.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn signature(&self) -> ReceiptSignature
    {
        self.signature
    }

    /// Whether this receipt's signature verifies over `records`' digest under
    /// its signer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn attests(
        &self,
        records: &[VerdictRecord],
    ) -> Attestation
    {
        let Ok(signer) = ed25519_dalek::VerifyingKey::from_bytes(&self.signer.0)
        else {
            return Attestation::Refused;
        };
        let signature = ed25519_dalek::Signature::from_bytes(&self.signature.0);
        match signer.verify_strict(&ReceiptMessage::of(records).0, &signature) {
            Ok(()) => Attestation::Attested,
            Err(_) => Attestation::Refused,
        }
    }
}

/// Whether a receipt attests its records.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Attestation
{
    /// The signature verifies.
    Attested,
    /// The signer's key or the signature does not verify.
    Refused,
}

/// The message a receipt signs: a digest over its records in key order, each
/// as its key and its counted verdict bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ReceiptMessage([u8; 32]);

impl ReceiptMessage
{
    /// The message over `records`, which every receipt holds in key order
    /// ([`StoredReceipt::new`], [`Verdicts::receipt`]).
    ///
    /// # Specification
    /// trivial.
    fn of(records: &[VerdictRecord]) -> Self
    {
        let mut hasher = blake3::Hasher::new_derive_key(RECEIPT_CONTEXT);
        for record in records {
            let encoded = record.encoded();
            let _hashed = hasher
                .update(&record.key.0)
                .update(
                    &u64::try_from(encoded.0.len())
                        .unwrap_or(u64::MAX)
                        .to_le_bytes(),
                )
                .update(&encoded.0);
        }
        Self(*hasher.finalize().as_bytes())
    }
}

/// A kernel installation's signing key, which the installation's
/// configuration holds.
///
/// # Specification
/// trivial.
#[derive(Clone)]
#[repr(transparent)]
pub struct KernelSigner(ed25519_dalek::SigningKey);

impl core::fmt::Debug for KernelSigner
{
    /// The signer's public identity, never its secret.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.debug_tuple("KernelSigner")
            .field(&self.identity())
            .finish()
    }
}

impl From<[u8; 32]> for KernelSigner
{
    /// The signer whose secret key is `secret`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(secret: [u8; 32]) -> Self
    {
        Self(ed25519_dalek::SigningKey::from_bytes(&secret))
    }
}

impl KernelSigner
{
    /// The identity this signer's receipts verify under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn identity(&self) -> KernelIdentity
    {
        KernelIdentity(self.0.verifying_key().to_bytes())
    }

    /// A receipt over `records`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn sign(
        &self,
        records: &[VerdictRecord],
    ) -> Receipt
    {
        Receipt {
            signer: self.identity(),
            signature: ReceiptSignature(self.0.sign(&ReceiptMessage::of(records).0).to_bytes()),
        }
    }
}

/// Which recorded verdicts a run believes.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TrustPolicy
{
    /// None: every declaration is replayed, nothing is keyed and nothing is
    /// recorded.
    Recheck,
    /// Those a receipt from one of these signers attests.
    Trusted(BTreeSet<KernelIdentity>),
}

/// A receipt and the records it attests, as a store holds them, the records
/// in key order.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StoredReceipt
{
    /// The receipt.
    receipt: Receipt,
    /// The records it attests, in key order.
    records: Vec<VerdictRecord>,
}

impl StoredReceipt
{
    /// The receipt `receipt` over `records`, put in key order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        receipt: Receipt,
        mut records: Vec<VerdictRecord>,
    ) -> Self
    {
        records.sort_by_key(|record| record.key);
        Self { receipt, records }
    }

    /// The receipt.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn receipt(&self) -> Receipt
    {
        self.receipt
    }

    /// The records it attests.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn records(&self) -> &[VerdictRecord]
    {
        &self.records
    }
}

quenchant_shape::reason_enum! {
    /// Why a store holds no receipt for a key.
    pub mod stored {
        /// The reason no receipt is found.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No receipt the store holds attests a record of the key.
            Unrecorded,
        }
    }
}

/// Where recorded verdicts are found: a store answering, for a key, every
/// receipt it holds that attests a record of it.
///
/// # Specification
/// - requires: nothing; what a source answers is verified before it is
///   believed.
/// - ensures: an implementor answers the receipts whose records include `key`,
///   in any order, and none when it holds none.
/// - provides: the one way recorded verdicts reach an admission.
/// - panics: none.
/// - executable: none — a trait whose implementors are untrusted.
///
/// # Adequacy
/// - hypothesis: L3 — a source answering a receipt of an unlisted signer, or a
///   tampered record, recalls nothing; one answering such a receipt beside a
///   trusted one, in either order, recalls under the trusted one.
/// - witness: `tests::verdicts::an_unlisted_signer_recalls_nothing`
/// - witness: `tests::verdicts::a_tampered_record_recalls_nothing`
/// - witness: `tests::verdicts::a_trusted_receipt_is_found_beside_a_foreign_one`
pub trait VerdictSource: core::fmt::Debug + Send + Sync
{
    /// Every receipt that attests a record of `key`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as the trait.
    /// - panics: none.
    /// - executable: none — a required method.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a foreign receipt answered beside a trusted one hides
    ///   nothing, as the trait's witnesses show.
    /// - declaration-only: the obligation is each implementation's answer; the
    ///   trait's witnesses run its implementors.
    fn receipts(
        &self,
        key: VerdictKey,
    ) -> &[Arc<StoredReceipt>];
}

/// A source holding nothing, for a run with no store.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct NoVerdicts;

impl VerdictSource for NoVerdicts
{
    /// None.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn receipts(
        &self,
        _key: VerdictKey,
    ) -> &[Arc<StoredReceipt>]
    {
        &[]
    }
}

quenchant_shape::reason_enum! {
    /// Why an admission computes no verdict key.
    pub mod keyed {
        /// The reason no key is computed.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The environment recalls nothing: its policy rechecks.
            Rechecking,
            /// An earlier admission was not keyed, so no later key would bind
            /// the whole input.
            Ended,
        }
    }
}

/// The chain of keys over the admissions so far.
#[derive(Clone, Debug)]
struct Chain
{
    /// The segments' encoder, holding what the admitted segments assigned.
    encoder: SegmentEncoder,
    /// The key of the last admission, or the start.
    last: VerdictKey,
}

/// An environment's verdict state: the policy, the source, the key chain,
/// the receipts verified so far and the records this kernel checked itself.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub(crate) struct Verdicts
{
    /// The signers believed.
    trusted: BTreeSet<KernelIdentity>,
    /// Where recorded verdicts are found.
    source: Arc<dyn VerdictSource>,
    /// The key chain; absent once an admission was not keyed.
    chain: Maybe<Chain, keyed::Absent>,
    /// The receipts already verified, each with whether it attested.
    verified: BTreeMap<Receipt, Attestation>,
    /// The readings of the records a verified receipt attested, by key.
    recalled: BTreeMap<VerdictKey, Accessibility>,
    /// The records this kernel checked itself, in admission order.
    checked: Vec<VerdictRecord>,
    /// How many admissions a recorded verdict answered.
    recalls: usize,
}

impl Default for Verdicts
{
    /// The state of an environment that recalls nothing.
    ///
    /// # Specification
    /// trivial.
    fn default() -> Self
    {
        Self::under(TrustPolicy::Recheck, Arc::new(NoVerdicts))
    }
}

impl Verdicts
{
    /// The state a run under `policy`, finding recorded verdicts in `source`,
    /// starts with.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn under(
        policy: TrustPolicy,
        source: Arc<dyn VerdictSource>,
    ) -> Self
    {
        let (trusted, chain) = match policy {
            TrustPolicy::Recheck => (BTreeSet::new(), Maybe::Absent(keyed::Absent::Rechecking)),
            TrustPolicy::Trusted(trusted) => (
                trusted,
                Maybe::Present(Chain {
                    encoder: SegmentEncoder::default(),
                    last: VerdictKey::start(),
                }),
            ),
        };
        Self {
            trusted,
            source,
            chain,
            verified: BTreeMap::new(),
            recalled: BTreeMap::new(),
            checked: Vec::new(),
            recalls: 0,
        }
    }

    /// This state for a later run that resumes the environment: the policy,
    /// the source, the chain and the receipts verified, without the records
    /// checked or the recalls counted, which are this run's.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn handed_on(&self) -> Self
    {
        Self {
            trusted: self.trusted.clone(),
            source: Arc::clone(&self.source),
            chain: self.chain.clone(),
            verified: self.verified.clone(),
            recalled: self.recalled.clone(),
            checked: Vec::new(),
            recalls: 0,
        }
    }

    /// The key of `declaration`, admitted next over `arena`, extending the
    /// chain; the chain ends when the declaration cannot be keyed.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn key(
        &mut self,
        arena: &TermArena,
        declaration: &gandr_kernel_term::Declaration,
    ) -> Maybe<VerdictKey, keyed::Absent>
    {
        let Maybe::Present(ref mut chain) = self.chain
        else {
            return match self.chain {
                Maybe::Absent(absent) => Maybe::Absent(absent),
                Maybe::Present(_) => Maybe::Absent(keyed::Absent::Ended),
            };
        };
        let marked = gandr_kernel_term::MarkedDeclaration::new(
            gandr_kernel_term::AdmissionMark::Checked,
            declaration.clone(),
        );
        match chain.encoder.segment(arena, &marked) {
            Maybe::Present(segment) => {
                chain.last = chain.last.after(&segment);
                Maybe::Present(chain.last)
            },
            Maybe::Absent(gandr_kernel_term::encoded_prefix::Absent::OpenSeal) => {
                self.end();
                Maybe::Absent(keyed::Absent::Ended)
            },
        }
    }

    /// End the chain: no later admission is keyed.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn end(&mut self)
    {
        if let Maybe::Present(_) = self.chain {
            self.chain = Maybe::Absent(keyed::Absent::Ended);
        }
    }

    /// The reading a verified receipt attests for `key`, trying each receipt
    /// the source answers for it until one a trusted signer gave attests it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn recall(
        &mut self,
        key: VerdictKey,
    ) -> Maybe<Accessibility, stored::Absent>
    {
        let Self {
            ref trusted,
            ref source,
            ref mut verified,
            ref mut recalled,
            ref mut recalls,
            ..
        } = *self;
        if !recalled.contains_key(&key) {
            for stored in source.receipts(key) {
                if verified.contains_key(&stored.receipt) {
                    continue;
                }
                let fresh = if trusted.contains(&stored.receipt.signer) {
                    stored.receipt.attests(&stored.records)
                }
                else {
                    Attestation::Refused
                };
                let _first = verified.insert(stored.receipt, fresh);
                if fresh == Attestation::Attested {
                    recalled.extend(
                        stored
                            .records
                            .iter()
                            .map(|record| (record.key, record.accessibility.clone())),
                    );
                    if recalled.contains_key(&key) {
                        break;
                    }
                }
            }
        }
        recalled
            .get(&key)
            .map_or(Maybe::Absent(stored::Absent::Unrecorded), |accessibility| {
                *recalls = recalls.saturating_add(1);
                Maybe::Present(accessibility.clone())
            })
    }

    /// Keep the record of an admission this kernel checked itself.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn checked(
        &mut self,
        key: VerdictKey,
        accessibility: Accessibility,
    )
    {
        self.checked.push(VerdictRecord { key, accessibility });
    }

    /// A receipt over the records this kernel checked itself, signed by
    /// `signer`, and those records; absent when it checked none.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn receipt(
        &self,
        signer: &KernelSigner,
    ) -> Maybe<StoredReceipt, stored::Absent>
    {
        if self.checked.is_empty() {
            return Maybe::Absent(stored::Absent::Unrecorded);
        }
        let mut records = self.checked.clone();
        records.sort_by_key(|record| record.key);
        Maybe::Present(StoredReceipt {
            receipt: signer.sign(&records),
            records,
        })
    }

    /// How many admissions a recorded verdict answered.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn recalls(&self) -> RecallCount
    {
        RecallCount(self.recalls)
    }
}

/// How many admissions a recorded verdict answered.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecallCount(usize);

impl From<RecallCount> for usize
{
    /// The count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: RecallCount) -> Self
    {
        count.0
    }
}
