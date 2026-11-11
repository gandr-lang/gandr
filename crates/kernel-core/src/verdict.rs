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
//! A bypass, a mutual block or an open seal ends the chain. A rejected
//! declaration enters no environment, so the chain steps back over it and
//! keys the next declaration as if the rejected one had never been offered. A
//! refusal is never recorded. [`Environment::handed_on`] hands the chain to a
//! resumed run without its records, and the resumed run reads the source of
//! its own readmission ([`Environment::reading`]).
//!
//! An entry key narrows the input to what the declaration reads. It covers
//! the declaration's segment written alone, with each position it names
//! written by where the segment first names it. It also covers the entry keys
//! of those positions in that order, the keys of the types of words over each
//! sort its references reach, and the keys of the atoms it reads as
//! representations. A generative entry also covers a count of the earlier
//! entries with the same key. So an edit re-keys only the declarations that
//! read the edited one, and a declaration keeps its key at a new position. A
//! recall tries the entry key first and then the chain key. A checked record
//! is kept under both keys. A bypass, an open seal or an input with no entry
//! key gives no entry key.
//!
//! An installation's key also signs a stratum of the checker's site, which
//! the checker certified, under a derivation context no admission receipt
//! uses ([`KernelSigner::sign_stratum`]). A run believes a stored stratum
//! under the same [`TrustPolicy`] as a recorded verdict
//! ([`TrustPolicy::believes_stratum`]), and the checker replays its structure
//! before it uses it.
//!
//! [`Environment::handed_on`]: crate::Environment::handed_on
//! [`Environment::reading`]: crate::Environment::reading
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — the key binds the kernel's whole input under a
//!   collision-resistant hash, the record is attested, and a full re-check is
//!   always available.
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — the
//!   strata persist in the store, under a receipt the installation's key signs.

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

/// The context an entry key's digest derives under. It is not
/// [`KEY_CONTEXT`], so no entry key is a chain key.
const ENTRY_KEY_CONTEXT: &str = "gandr kernel entry key 2026-11-11";

/// The context a receipt's message derives under.
const RECEIPT_CONTEXT: &str = "gandr kernel verdict receipt 2026-10-27";

/// The context a stratum receipt's message derives under.
const STRATUM_CONTEXT: &str = "gandr checker stratum receipt 2026-10-30";

/// The version byte every encoded verdict leads with.
const VERDICT_VERSION: u8 = 1;

/// A key for one admission.
///
/// An entry key covers what the declaration reads, each position it names by
/// that entry's key. A chain key covers the kernel's whole input: its build,
/// and every declaration admitted up to and including this one.
///
/// # Specification
/// - ensures: two entry keys are equal exactly when, up to a BLAKE3 collision,
///   they cover the same build identity, keyed segments, named keys, manifest
///   atoms, types of words and generative index. Two chain keys are equal
///   exactly when they chain the same build identity over the same canonical
///   segments. No entry key is a chain key, because the two derive under two
///   contexts.
/// - provides: the identity a recorded verdict is recalled by.
/// - panics: none.
/// - executable: none — collision resistance is BLAKE3's.
///
/// # Adequacy
/// - hypothesis: L3 — a recorded verdict is recalled under its own key and not
///   after one name changes; an edit re-keys only what reads the edited
///   declaration.
/// - witness: `tests::verdicts::a_verdict_is_recalled_only_under_its_own_key`
/// - witness: `tests::verdicts::an_edit_re_keys_only_what_reads_it_6568`
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

    /// The key of a generative entry whose content key is `self`, after
    /// `earlier` entries with the same content key: two entries with one
    /// content are two types, so they take two keys.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn generative(
        self,
        earlier: KeyedCount,
    ) -> Self
    {
        let mut keyer = EntryKeyer::tagged(EntryTag::Generative);
        keyer.key(self);
        keyer.count(earlier);
        keyer.finish()
    }

    /// The key of the member at `ordinal` in the mutual block whose key is
    /// `self`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn member(
        self,
        ordinal: KeyedCount,
    ) -> Self
    {
        let mut keyer = EntryKeyer::tagged(EntryTag::Member);
        keyer.key(self);
        keyer.count(ordinal);
        keyer.finish()
    }
}

/// A count an entry key writes: a run's length, a place or an index.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct KeyedCount(usize);

impl From<usize> for KeyedCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

/// What an entry key's digest starts with after the build identity, so the
/// three forms of the key never read one another's bytes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EntryTag
{
    /// The key of what one admission reads: a lone declaration, or a mutual
    /// block whole.
    Content,
    /// A generative entry's key, over its content key and its index.
    Generative,
    /// A block member's key, over the block's key and the member's place.
    Member,
}

/// An entry key as it is written: the build identity, a tag, then what the
/// admission reads in a fixed order, with each run after its length.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub(crate) struct EntryKeyer(blake3::Hasher);

impl EntryKeyer
{
    /// A key under `tag`, over this kernel's build identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn tagged(tag: EntryTag) -> Self
    {
        let mut hasher = blake3::Hasher::new_derive_key(ENTRY_KEY_CONTEXT);
        let _written = hasher.update(KERNEL_BUILD).update(&[match tag {
            EntryTag::Content => 0,
            EntryTag::Generative => 1,
            EntryTag::Member => 2,
        }]);
        Self(hasher)
    }

    /// Write `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn count(
        &mut self,
        count: KeyedCount,
    )
    {
        let _written = self
            .0
            .update(&u64::try_from(count.0).unwrap_or(u64::MAX).to_le_bytes());
    }

    /// Write `segment`'s bytes after their length.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn segment(
        &mut self,
        segment: &EncodedArtifact,
    )
    {
        self.count(KeyedCount(segment.as_ref().len()));
        let _written = self.0.update(segment.as_ref());
    }

    /// Write `key`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn key(
        &mut self,
        key: VerdictKey,
    )
    {
        let _written = self.0.update(&key.0);
    }

    /// The key the written bytes digest to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn finish(&self) -> VerdictKey
    {
        VerdictKey(*self.0.finalize().as_bytes())
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
        self.verifies(ReceiptMessage::of(records))
    }

    /// Whether this receipt's signature verifies over `message` under its
    /// signer.
    ///
    /// # Specification
    /// trivial.
    fn verifies(
        &self,
        message: ReceiptMessage,
    ) -> Attestation
    {
        let Ok(signer) = ed25519_dalek::VerifyingKey::from_bytes(&self.signer.0)
        else {
            return Attestation::Refused;
        };
        let signature = ed25519_dalek::Signature::from_bytes(&self.signature.0);
        match signer.verify_strict(&message.0, &signature) {
            Ok(()) => Attestation::Attested,
            Err(_) => Attestation::Refused,
        }
    }
}

/// Whether a receipt attests what it is read beside.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Attestation
{
    /// The signature verifies, under a signer the policy lists.
    Attested,
    /// The policy lists no such signer, or the signer's key or the signature
    /// does not verify.
    Refused,
}

/// The key a stored stratum of the checker's site is recalled by: a digest of
/// the build that certifies it, its bound and its degree.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StratumKey([u8; 32]);

impl From<[u8; 32]> for StratumKey
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

impl From<StratumKey> for [u8; 32]
{
    /// The digest of `key`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(key: StratumKey) -> Self
    {
        key.0
    }
}

impl core::fmt::Display for StratumKey
{
    /// The digest as 64 lowercase hexadecimal digits.
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

/// The canonical image of a stratum the checker certified, as a stratum
/// receipt signs it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StratumBytes<'image>(&'image [u8]);

impl<'image> From<&'image [u8]> for StratumBytes<'image>
{
    /// The image whose bytes are `bytes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'image [u8]) -> Self
    {
        Self(bytes)
    }
}

/// The message a receipt signs: a digest over its records in key order, each
/// as its key and its counted verdict bytes, or over a stratum's key and its
/// counted image under a context no admission receipt uses.
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

    /// The message over the stratum of `key` whose image is `image`.
    ///
    /// # Specification
    /// trivial.
    fn of_stratum(
        key: StratumKey,
        image: StratumBytes<'_>,
    ) -> Self
    {
        Self(
            *blake3::Hasher::new_derive_key(STRATUM_CONTEXT)
                .update(&key.0)
                .update(
                    &u64::try_from(image.0.len())
                        .unwrap_or(u64::MAX)
                        .to_le_bytes(),
                )
                .update(image.0)
                .finalize()
                .as_bytes(),
        )
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

    /// A receipt over the stratum of `key` whose canonical image is `image`,
    /// which the checker certified in this process.
    ///
    /// # Specification
    /// - requires: the checker certified the stratum `image` holds, at the
    ///   build, bound and degree `key` digests.
    /// - ensures: a receipt [`TrustPolicy::believes_stratum`] believes over
    ///   `key` and `image` under a policy listing this signer, and over no
    ///   other key or image; it verifies as no admission receipt.
    /// - panics: none.
    /// - executable: none — the signature is Ed25519's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stratum receipt is believed under its own signer
    ///   and refused over a changed image, under an unlisted signer and under
    ///   the recheck policy.
    /// - witness: `tests::verdicts::a_stratum_receipt_is_believed_only_as_signed_4034`
    #[inline]
    #[must_use]
    pub fn sign_stratum(
        &self,
        key: StratumKey,
        image: StratumBytes<'_>,
    ) -> Receipt
    {
        Receipt {
            signer: self.identity(),
            signature: ReceiptSignature(
                self.0
                    .sign(&ReceiptMessage::of_stratum(key, image).0)
                    .to_bytes(),
            ),
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

impl TrustPolicy
{
    /// Whether this policy believes `receipt` over the stored stratum of `key`
    /// whose image is `image`.
    ///
    /// # Specification
    /// - requires: nothing; what a store answers is verified here before it is
    ///   believed.
    /// - ensures: [`Attestation::Attested`] exactly when the policy lists the
    ///   receipt's signer and its signature verifies over `key` and `image` as
    ///   [`KernelSigner::sign_stratum`] signs them; under
    ///   [`TrustPolicy::Recheck`], [`Attestation::Refused`].
    /// - panics: none.
    /// - executable: none — the signature is Ed25519's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`KernelSigner::sign_stratum`].
    /// - witness: `tests::verdicts::a_stratum_receipt_is_believed_only_as_signed_4034`
    #[inline]
    #[must_use]
    pub fn believes_stratum(
        &self,
        receipt: &Receipt,
        key: StratumKey,
        image: StratumBytes<'_>,
    ) -> Attestation
    {
        match *self {
            Self::Trusted(ref trusted) if trusted.contains(&receipt.signer) => {
                receipt.verifies(ReceiptMessage::of_stratum(key, image))
            },
            Self::Recheck | Self::Trusted(_) => Attestation::Refused,
        }
    }
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
            /// The bypass admitted the declaration, so no check read it.
            Bypassed,
            /// The declaration is an abstract type sealed to the end of the
            /// sequence, so its segment is not written.
            OpenSeal,
            /// An input of the admission has no entry key: a position it
            /// names, a type of words its references reach or an atom it reads
            /// as a representation.
            Unkeyed,
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
    /// The key before the last admission, which a refusal steps back to.
    before: VerdictKey,
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
    /// How many admissions this kernel checked and recorded, each under
    /// every key it has.
    recorded: usize,
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

/// Whether an environment keys its admissions.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Keying
{
    /// The policy trusts some signers, so each admission is keyed.
    Keys,
    /// The policy rechecks every admission, so nothing is keyed.
    Rechecks,
}

impl Verdicts
{
    /// Whether the policy keys admissions: under [`TrustPolicy::Recheck`] an
    /// admission computes no key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn keying(&self) -> Keying
    {
        match self.chain {
            Maybe::Absent(keyed::Absent::Rechecking) => Keying::Rechecks,
            Maybe::Present(_)
            | Maybe::Absent(
                keyed::Absent::Ended
                | keyed::Absent::Bypassed
                | keyed::Absent::OpenSeal
                | keyed::Absent::Unkeyed,
            ) => Keying::Keys,
        }
    }

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
                    before: VerdictKey::start(),
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
            recorded: 0,
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
            recorded: 0,
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
                chain.before = chain.last;
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

    /// Step the chain back over the declaration [`Self::key`] keyed last,
    /// which the kernel refused: it enters no environment, so the next
    /// declaration's input does not read it, and the arena mints its nodes'
    /// ids again.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn refused(&mut self)
    {
        if let Maybe::Present(ref mut chain) = self.chain {
            chain.encoder.forget();
            chain.last = chain.before;
        }
    }

    /// Read recorded verdicts from `source` from now on, as a resumed run reads
    /// the source of the readmission that resumes it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn reading(
        &mut self,
        source: Arc<dyn VerdictSource>,
    )
    {
        self.source = source;
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

    /// Keep the record of an admission this kernel checked itself, under its
    /// entry key and under its chain key, as the two are present.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn checked(
        &mut self,
        entry: Maybe<VerdictKey, keyed::Absent>,
        chain: Maybe<VerdictKey, keyed::Absent>,
        accessibility: Accessibility,
    )
    {
        let before = self.checked.len();
        if let Maybe::Present(key) = entry {
            self.checked.push(VerdictRecord {
                key,
                accessibility: accessibility.clone(),
            });
        }
        if let Maybe::Present(key) = chain {
            self.checked.push(VerdictRecord { key, accessibility });
        }
        if self.checked.len() > before {
            self.recorded = self.recorded.saturating_add(1);
        }
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
        // Two entries with one content share a key, and one record answers
        // both.
        records.dedup();
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

    /// How many admissions this kernel checked and recorded.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn recorded(&self) -> RecordCount
    {
        RecordCount(self.recorded)
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

/// How many admissions a receipt records: each admission once, whether its
/// verdict is kept under one key or two.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecordCount(usize);

impl From<RecordCount> for usize
{
    /// The count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: RecordCount) -> Self
    {
        count.0
    }
}
