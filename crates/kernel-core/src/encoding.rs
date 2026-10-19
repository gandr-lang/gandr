//! The **canonical content encoding**, the table that names each distinct
//! record once, and the memo key built as a name in that table.
//!
//! # The key is content, and that is what makes it position-free
//!
//! A support keyed on an arena id means the same obligation arising at two
//! arena positions takes two keys, so a re-minted spine re-checks a leaf it
//! already knows. Keying on content dissolves that: two structurally equal
//! nodes are one question wherever they sit.
//!
//! Content is named by a [`ContentId`], assigned by [`ContentTable`], which
//! interns each node's **one-level record** — its tag, its inline payload, and
//! its children's already-assigned content ids — bottom-up. Two nodes receive
//! one id exactly when their reachable content is structurally identical, and
//! the assignment is **exact**: no hash decides it.
//!
//! **The table is scoped to one checking session and that is deliberate.** It
//! is threaded through the checking entry beside the reach cache rather than
//! held anywhere, so a key never outlives the call that built it. The memo's
//! one-call lifetime is therefore a property of the surface rather than a
//! discipline a caller has to remember, and a support built against one session
//! is meaningless in another rather than silently wrong in it.
//!
//! # The key is a name built from names
//!
//! A memo key is the [`ContentId`] of a **goal record**: the goal's direction,
//! its obligation's id, its expected type's id, and the id of its **cover** —
//! the set of binders the goal reads, each a **pair** of a de Bruijn index and
//! its binder type's id, written in index order. Pair, cover and goal records
//! join the node records in one table under tags no node uses, so each sub-key
//! is built once and every goal that selects it shares it, and two goals take
//! one id exactly when every member agrees down to the leaves. This is the
//! hereditarily finite set reading of a support: the records fix which sets
//! exist and how they compose, and no set's numeric code is ever formed.
//!
//! # The digest is a positive fast path and never a decision
//!
//! **Equal digests never decide agreement.** A collision would be a silent
//! false *agree*, which is the one failure a memo must not admit. The table
//! files each record under its digest and decides by comparing the record's
//! bytes in the stream, so records sharing a digest keep their own ids. The
//! memo's bucket digest is read off the goal's id, and agreement compares ids,
//! which the table assigned exactly. Collapsing every digest to one constant
//! changes no verdict and no count — it costs a linear scan — so only the
//! digests' own unit witnesses distinguish it.
//!
//! # The encoding is injective by construction
//!
//! Prefix-free, tagged, length-prefixed, and mirroring the term relation
//! exactly. Four families of confusion are ruled out structurally rather than
//! by testing, and each has a trap-pair witness riding on the record encoder:
//!
//! - **two field orders** — a former's children are emitted in a fixed order,
//!   so `A × B` and `B × A` take two ids;
//! - **two families with one payload** — the node tag is drawn from the
//!   format's single global alphabet, so the unit *value* and the unit *type*
//!   take two ids;
//! - **signed zeroes** — the literal payloads carry their sign, and the term
//!   crate pins negative zero to non-negative before it is ever encoded, so two
//!   spellings of one number cannot produce two ids;
//! - **the length-prefix ambiguity pair** — every text payload and every record
//!   is length-prefixed, so no two component splittings concatenate alike.
//!
//! Key collision is the one obligation a randomized differential cannot probe,
//! which is why these ride as static witnesses on the derivation itself. A
//! trap pair exhibits its ambiguity inside one framed unit: the length-prefix
//! pair is stated over a numeric literal, which carries two text payloads in
//! one record, so `1.23` and `12.3` concatenate to the same digits. Over two
//! text literals the record framing would separate them whatever their
//! payloads do, and the pair would test nothing.
//!
//! # Cost
//!
//! Each distinct node is encoded once per session, so deriving every key of one
//! check costs one pass over the distinct nodes — the "hash every node" price
//! the content key is adopted at, and linear rather than quadratic even on a
//! chain-deep term a decoder built from bytes. A goal adds a pair per read
//! binder, one cover and one goal record, each built once per session. Asking
//! about content the table already holds allocates nothing. What the content
//! key buys over an identity key on a real corpus is unmeasured; a measurement
//! showing that pass dominating the reuse payoff re-keys the memo.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::DigestWord;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelOffset;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Sign;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::WireTag;
use quenchant_arith::arith;
use quenchant_shape::shape::Maybe;

use crate::rewrite::BinderDepth;

/// A 64-bit quantity written into an encoding as a minimal unsigned varint.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct EncodedWord(u64);

/// The canonical number of one distinct content within a [`ContentTable`].
///
/// Two nodes carry one content id exactly when their reachable content is
/// structurally identical. The assignment is decided by interning the nodes'
/// one-level records, so it is exact rather than probabilistic — nothing here
/// is a hash.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ContentId(u64);

impl From<ContentId> for DigestWord
{
    /// A content id as one digest word. Within its table an id names exactly
    /// one content, so the word is a function of content.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: ContentId) -> Self
    {
        Self::from(id.0)
    }
}

/// Borrowed text offered to a content encoding.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct EncodedText<'content>(&'content str);

/// The reserved tag marking a node reference that resolved to nothing.
///
/// A dangling id is unreachable under the arena's minting invariant. The tag
/// exists so the encoding stays **total** — a walk that could not read a node
/// still produces a record — and merging two unreadable references is safe for
/// a sharper reason than rarity: a goal whose own subject is unreadable
/// refuses, a goal that would reach an unreadable descendant refuses for the
/// same reason, and a goal that never reaches one has an answer independent of
/// it. No entry keyed through this tag can serve an answer the other reference
/// would not have given.
///
/// # Specification
/// trivial.
fn record_dangling() -> WireTag
{
    WireTag::from(DANGLING_TAG)
}

/// The byte the dangling record reserves out of the node-tag alphabet: the
/// top of the byte range, as far from the block as the alphabet allows.
const DANGLING_TAG: u8 = 0xFF;

/// The tag of a staged value type's record.
///
/// A stage is admission's alone and never on the wire, so its record takes a
/// byte no node tag takes: one below the dangling sentinel. A staged type and
/// its base are different goals' types, and its record keeps them apart.
///
/// # Specification
/// trivial.
fn record_staged() -> WireTag
{
    WireTag::from(STAGED_TAG)
}

/// The byte a staged type's record reserves out of the node-tag alphabet.
const STAGED_TAG: u8 = 0xFE;

/// The tag of an exact stage inside a staged type's record.
///
/// # Specification
/// trivial.
fn stage_exact() -> WireTag
{
    WireTag::from(0x00_u8)
}

/// The tag of a bound inside a staged type's record.
///
/// # Specification
/// trivial.
fn stage_bound() -> WireTag
{
    WireTag::from(0x01_u8)
}

/// Keep the dangling and staged sentinels, and the key records' tags, outside
/// every admitted node tag.
///
/// # Specification
/// - ensures: compilation refuses a table row that uses a reserved byte.
/// - panics: no runtime path; a violation fails constant evaluation.
/// - executable: none — this is an evaluated compile-time assertion, not a
///   callable boundary.
///
/// # Adequacy
/// - hypothesis: L3 — sparse native tags and unreadable references encode
///   separately; adding a row at a reserved byte fails compilation.
/// - witness: `encoding::tests::an_unreadable_reference_still_encodes`
/// - witness: `encoding::tests::a_stage_is_part_of_a_type_s_content`
const _: () = {
    let mut rows = gandr_kernel_term::NODE_TAG_TABLE.as_slice();
    while let &[row, ref rest @ ..] = rows {
        assert!(row.tag.0 < GOAL_TAG, "node tag overlaps a reserved byte");
        rows = rest;
    }
};

/// The byte a pair record reserves: one read binder, its index beside its
/// type's content.
const PAIR_TAG: u8 = 0xFD;

/// The byte a cover record reserves: the set of pairs one goal reads.
const COVER_TAG: u8 = 0xFC;

/// The byte a context record reserves: a whole context's types, outermost
/// first.
const CONTEXT_TAG: u8 = 0xFB;

/// The byte a goal record reserves: one question, the memo's key. The lowest
/// reserved byte; every node tag sits below it.
const GOAL_TAG: u8 = 0xFA;

/// The tag distinguishing an absent optional component from a present one.
///
/// # Specification
/// trivial.
fn component_absent() -> WireTag
{
    WireTag::from(0x00_u8)
}

/// The tag marking a present optional component.
///
/// # Specification
/// trivial.
fn component_present() -> WireTag
{
    WireTag::from(0x01_u8)
}

/// The four records the memo key adds to a [`ContentTable`], beside the
/// nodes' own.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum KeyRecord
{
    /// One read binder: its index and its type.
    Pair,
    /// The set of pairs one goal reads.
    Cover,
    /// A whole context, for a goal whose reads are not known.
    Context,
    /// One question: its direction, subject, expected type and binders.
    Goal,
}

impl KeyRecord
{
    /// This record's tag.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn tag(self) -> WireTag
    {
        WireTag::from(match self {
            Self::Pair => PAIR_TAG,
            Self::Cover => COVER_TAG,
            Self::Context => CONTEXT_TAG,
            Self::Goal => GOAL_TAG,
        })
    }
}

/// Which family an unreadable reference belonged to.
///
/// Written beside [`record_dangling`] so an unreadable value and an unreadable
/// computation stay two records rather than one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DanglingFamily
{
    /// A value reference.
    Value,
    /// A computation reference.
    Computation,
    /// A value-type reference.
    ValueType,
    /// A computation-type reference.
    CompType,
}

impl DanglingFamily
{
    /// This family's byte.
    ///
    /// # Specification
    /// trivial.
    fn tag(self) -> WireTag
    {
        match self {
            Self::Value => WireTag::from(0x00_u8),
            Self::Computation => WireTag::from(0x01_u8),
            Self::ValueType => WireTag::from(0x02_u8),
            Self::CompType => WireTag::from(0x03_u8),
        }
    }
}

/// An owned canonical content encoding: one record's bytes.
///
/// Records compare equal exactly when their content does, so this type is the
/// interning's whole vocabulary. It is ordered so a table can be keyed on it.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContentEncoding(Vec<u8>);

impl AsRef<[u8]> for ContentEncoding
{
    /// The encoding's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

impl ContentEncoding
{
    /// An empty encoding.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn new() -> Self
    {
        Self(Vec::new())
    }

    /// Append one tag byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn put_tag(
        &mut self,
        tag: WireTag,
    )
    {
        self.0.push(u8::from(tag));
    }

    /// Append the minimal unsigned varint image of `value`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends the little-endian base-128 image with no continuation
    ///   byte past the highest set group, so a value has exactly one image and
    ///   two encodings differ whenever the values they carry differ.
    /// - provides: the encoder's integer primitive, and with it the
    ///   length-prefix framing that makes the encoding prefix-free.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — the predicate fixes every appended payload group,
    ///   continuation bit and minimal width. Exact images at 0, 127, 128 and
    ///   `u64::MAX` separate zero, the first group transition and the ceiling;
    ///   these finite cases do not enumerate every word.
    /// - witness: `encoding::tests::varint_images_are_minimal_at_the_boundaries`
    #[spec(
        captures: entry_len = self.0.len(),
        ensures: self.0.get(entry_len..).is_some_and(|image|
            usize::try_from(64_u32.saturating_sub(value.0.leading_zeros()).max(1).div_ceil(7))
                .is_ok_and(|groups| image.len() == groups)
            && image.iter().enumerate().all(|(group, &byte)|
                value.0.checked_shr(u32::try_from(group.saturating_mul(7)).unwrap_or(u32::MAX))
                    .is_some_and(|remaining| u64::from(byte & 0x7f) == (remaining & 0x7f)
                        && ((byte & 0x80) != 0) == (group.saturating_add(1) < image.len()))))
    )]
    fn put_word(
        &mut self,
        value: EncodedWord,
    )
    {
        let mut remaining = value.0;
        loop {
            let low = u8::try_from(remaining & 0x7f).unwrap_or(0_u8);
            remaining = u64::from(arith::div(
                arith::Int::from(remaining),
                arith::Int::from(128_u64),
            ));
            if remaining == 0_u64 {
                self.0.push(low);
                return;
            }
            self.0.push(low | 0x80);
        }
    }

    /// Append a content id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn put_content(
        &mut self,
        id: ContentId,
    )
    {
        self.put_word(EncodedWord(id.0));
    }

    /// Append a byte length as a varint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn put_length(
        &mut self,
        length: EncodingLength,
    )
    {
        self.put_word(EncodedWord(u64::try_from(length.0).unwrap_or(u64::MAX)));
    }

    /// Append a component count as a varint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn put_count(
        &mut self,
        count: ComponentCount,
    )
    {
        self.put_word(EncodedWord(u64::try_from(count.0).unwrap_or(u64::MAX)));
    }

    /// Append length-prefixed text.
    ///
    /// The length prefix is the whole point: without it `"ab"` beside `"c"` and
    /// `"a"` beside `"bc"` would produce one byte string, and two distinct
    /// literals would take one content id.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends the text's byte length and then its bytes, so two
    ///   adjacent text components cannot be re-split — `"a"` beside `"bc"` and
    ///   `"ab"` beside `"c"` take different images.
    /// - provides: the framing that keeps the encoding injective over text
    ///   payloads, and so keeps two literals from taking one content id.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — the appended suffix contains the original UTF-8
    ///   bytes after their minimal byte-length prefix. Empty, multi-byte and
    ///   127/128-byte text separates character counting, missing framing and
    ///   prefix loss; adjacent split pairs separate ambiguous concatenation.
    /// - witness: `encoding::tests::text_frames_count_bytes_and_preserve_component_boundaries`
    #[inline]
    #[spec(
        captures: entry_len = self.0.len(),
        ensures: self.0.get(entry_len..).and_then(|image| image.strip_suffix(text.0.as_bytes()))
            .is_some_and(|prefix| {
                let length = text.0.len();
                usize::try_from(usize::BITS.saturating_sub(length.leading_zeros()).max(1).div_ceil(7))
                    .is_ok_and(|groups| prefix.len() == groups)
                && prefix.iter().enumerate().all(|(group, &byte)|
                    ((byte & 0x80) != 0) == (group.saturating_add(1) < prefix.len()))
                && prefix.iter().rev().fold(0_u128, |value, &byte|
                    value.saturating_mul(128).saturating_add(u128::from(byte & 0x7f)))
                    == u128::try_from(length).unwrap_or(u128::MAX)
            })
    )]
    fn put_text(
        &mut self,
        text: EncodedText<'_>,
    )
    {
        let bytes = text.0.as_bytes();
        self.put_length(EncodingLength(bytes.len()));
        self.0.extend_from_slice(bytes);
    }

    /// Append `record` framed by its own byte length.
    ///
    /// # Specification
    /// - requires: nothing; the record may be empty or contain arbitrary bytes.
    /// - ensures: appends the record's minimal byte-length varint followed by
    ///   its complete bytes, without changing the preceding encoding.
    /// - provides: unambiguous record boundaries in the canonical stream.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — the suffix predicate checks the minimal prefix and
    ///   complete payload. Empty, binary and 128-byte records witness framing
    ///   and preservation of an existing prefix; not every length is sampled.
    /// - witness: `encoding::tests::record_frames_preserve_binary_payloads_at_the_group_boundary`
    #[inline]
    #[spec(
        captures: entry_len = self.0.len(),
        ensures: self.0.get(entry_len..).and_then(|image| image.strip_suffix(record.0.as_slice()))
            .is_some_and(|prefix| {
                let length = (record.0.as_slice()).len();
                usize::try_from(usize::BITS.saturating_sub(length.leading_zeros()).max(1).div_ceil(7))
                    .is_ok_and(|groups| prefix.len() == groups)
                && prefix.iter().enumerate().all(|(group, &byte)|
                    ((byte & 0x80) != 0) == (group.saturating_add(1) < prefix.len()))
                && prefix.iter().rev().fold(0_u128, |value, &byte|
                    value.saturating_mul(128).saturating_add(u128::from(byte & 0x7f)))
                    == u128::try_from(length).unwrap_or(u128::MAX)
            })
    )]
    fn put_record(
        &mut self,
        record: &Self,
    )
    {
        self.put_length(record.length());
        self.0.extend_from_slice(record.0.as_slice());
    }

    /// The 128-bit digest of these bytes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the high and low words of FNV-1a-128 over these bytes, using
    ///   its offset basis and prime modulo 2^128. Equal encodings have equal
    ///   digests; unequal encodings are not promised unequal digests.
    /// - provides: the positive fast path a memo buckets on, and the content
    ///   identity a refusal's type witness carries. The executable fold states
    ///   the algorithm, not collision freedom: byte equality still decides.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — the fold fixes the recurrence and word split;
    ///   empty and single-byte known answers separate the basis, multiplication
    ///   and word order. Byte-change and transposition witnesses reject a
    ///   constant or order-insensitive digest, not every possible collision.
    /// - witness: `encoding::tests::the_digest_separates_a_one_byte_difference`
    /// - witness: `encoding::tests::the_digest_separates_a_transposition`
    #[inline]
    #[must_use]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the check folds the bytes once, as the body does"
        )
    )]
    #[spec(ensures: |ret| {
        let fingerprint = self.0.iter().fold(0x6c62_272e_07bb_0142_62b8_2175_6295_c58d_u128,
            |state, &byte| (state ^ u128::from(byte))
                .wrapping_mul(0x0000_0000_0100_0000_0000_0000_0000_013b_u128));
        ret == ContentDigest::new(
            DigestWord::from(u64::try_from(fingerprint >> 64_u32).unwrap_or(u64::MAX)),
            DigestWord::from(u64::try_from(fingerprint & u128::from(u64::MAX)).unwrap_or(u64::MAX)))
    })]
    pub fn digest(&self) -> ContentDigest
    {
        // FNV-1a over 128 bits: order-sensitive by construction, so a
        // transposition moves it, and wrapping arithmetic because a hash is the
        // one place bare modular arithmetic is the intended semantics.
        const BASIS: u128 = 0x6c62_272e_07bb_0142_62b8_2175_6295_c58d_u128;
        const PRIME: u128 = 0x0000_0000_0100_0000_0000_0000_0000_013b_u128;
        let mut state = BASIS;
        for &byte in &self.0 {
            state ^= u128::from(byte);
            // reason: FNV-1a multiplies modulo 2^128.
            state = u128::from(arith::wrapping_mul(
                arith::Int::from(state),
                arith::Int::from(PRIME),
            ));
        }
        let high = u128::from(arith::div(
            arith::Int::from(state),
            arith::Int::from(0x0000_0000_0000_0001_0000_0000_0000_0000_u128),
        ));
        let high = u64::try_from(high).unwrap_or(u64::MAX);
        let low = u64::try_from(state & u128::from(u64::MAX)).unwrap_or(u64::MAX);
        ContentDigest::new(DigestWord::from(high), DigestWord::from(low))
    }

    /// How many bytes this encoding holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn length(&self) -> EncodingLength
    {
        EncodingLength(self.0.len())
    }
}

/// The byte length of a [`ContentEncoding`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EncodingLength(usize);

/// How many components a composite position of an encoding carries.
///
/// Distinct from [`EncodingLength`] because the two are different quantities
/// that both spell as one machine word: a byte length frames a payload, and a
/// component count says how many entries follow.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ComponentCount(usize);

impl From<usize> for ComponentCount
{
    /// The count of `count` components.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<ComponentCount> for usize
{
    /// How many components `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ComponentCount) -> Self
    {
        count.0
    }
}

impl From<EncodingLength> for usize
{
    /// The same measurement as a component count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: EncodingLength) -> Self
    {
        length.0
    }
}

/// One step of the iterative encoding walk.
#[derive(Clone, Copy, Debug)]
enum EncodeTask
{
    /// Ensure this node's children hold content ids, then close it.
    Open(AnyNode),
    /// Assign this node's content id now that its children hold theirs.
    Close(AnyNode),
}

/// The session's canonical content numbering: one id per **distinct content**,
/// assigned in post-order first-completion order.
///
/// The table is keyed on a record's own bytes, so two structurally equal
/// subterms at different arena positions receive one id — which is exactly what
/// makes a re-minted spine's untouched leaf reuse its answer, and what a memo
/// keyed on arena identity forfeits. Beside the nodes' records it holds the
/// memo key's — pairs, covers, contexts and goals — so a goal's key is a name
/// in the same merged graph, built from its members' names.
///
/// Every record's bytes are held once, in the stream; the index maps a record's
/// digest to its id, and a lookup compares the bytes there. Records are built
/// in one reused buffer and walks run on one reused stack, so asking about
/// content the table already holds allocates nothing.
#[derive(Clone, Debug, Default)]
pub struct ContentTable
{
    /// The framed record stream, in id order: every record's bytes, once.
    stream: ContentEncoding,
    /// Where each record's bytes sit in the stream, by id.
    spans: Vec<RecordSpan>,
    /// The first id whose record has each digest.
    interned: BTreeMap<ContentDigest, ContentId>,
    /// The next id whose record shares this id's digest; empty unless two
    /// records' digests collide.
    colliding: BTreeMap<ContentId, ContentId>,
    /// The id already assigned to each arena node.
    placed: BTreeMap<AnyNode, ContentId>,
    /// How many records the stream holds.
    records: u64,
    /// The record being built.
    scratch: ContentEncoding,
    /// The members of the cover or context being built.
    members: Vec<ContentId>,
    /// The placement walk's task stack.
    tasks: Vec<EncodeTask>,
}

/// Where one record's bytes sit in a [`ContentTable`]'s stream.
#[derive(Clone, Copy, Debug)]
struct RecordSpan
{
    /// The offset of the record's first byte.
    start: usize,
    /// The offset past its last byte.
    end: usize,
}

quenchant_shape::reason_enum! {
    /// Why a table holds no id for a record.
    mod record_held {
        /// The table has not seen the record.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// No record the table holds has these bytes.
            Fresh,
        }
    }
}

impl ContentTable
{
    /// A fresh table, holding no records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The framed record stream: the canonical encoding of everything this
    /// table has been asked about, in assignment order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn stream(&self) -> &ContentEncoding
    {
        &self.stream
    }

    /// Assign `node` and everything it reaches a content id, returning its own.
    ///
    /// # Specification
    /// - requires: `arena` is the one this table has been used with, and it has
    ///   only grown since — a session's arena is append-only until the choke
    ///   point truncates, which is after the session ends.
    /// - ensures: two nodes receive one id exactly when their reachable content
    ///   is structurally identical. The walk is iterative over an explicit task
    ///   stack, so it is total on any term depth, and each distinct node is
    ///   recorded once however many times it occurs or is asked about.
    /// - provides: the sharing-aware key derivation. The predicate fixes the
    ///   returned placement and preserves counts on a repeated node; arena
    ///   provenance and equality across distinct graphs remain witnessed.
    /// - fails: never — an unreadable node takes the reserved dangling record.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the walk is a loop over an explicit task stack, not recursion.
    /// - measure: lexicographically, reachable nodes not yet opened and pending
    ///   tasks. A first open reduces the former; a close or repeated open
    ///   consumes a task. Depth-first processing closes a node before another
    ///   path opens it.
    /// - boundedness: the finite arena is minted child-before-parent across all
    ///   families, so its dependency graph is acyclic.
    /// - input recursion: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — one append-only arena supplies the input graph.
    ///   The predicate checks placement and repeated-node stability; a shared
    ///   depth-16 graph, its repeated query and its re-minted spelling separate
    ///   occurrence expansion, lost reuse and arena-identity numbering.
    /// - witness: `encoding::tests::one_table_records_each_distinct_node_once`
    /// - witness: `encoding::tests::structurally_equal_nodes_encode_alike`
    #[spec(
        captures: [held = self.placed.get(&node).copied(), records_before = self.records,
            stream_before = self.stream.0.len(), placed_before = self.placed.len()],
        ensures: |ret| self.placed.get(&node) == Some(&ret) && ret.0 < self.records
            && self.records >= records_before && self.placed.len() >= placed_before
            && held.is_none_or(|prior| ret == prior && self.records == records_before
                && self.stream.0.len() == stream_before && self.placed.len() == placed_before)
    )]
    fn place(
        &mut self,
        arena: &TermArena,
        node: AnyNode,
    ) -> ContentId
    {
        if let Some(&held) = self.placed.get(&node) {
            return held;
        }
        let mut tasks = core::mem::take(&mut self.tasks);
        tasks.clear();
        tasks.push(EncodeTask::Open(node));
        while let Some(task) = tasks.pop() {
            match task {
                EncodeTask::Open(open) => {
                    if self.placed.contains_key(&open) {
                        continue;
                    }
                    tasks.push(EncodeTask::Close(open));
                    push_children(arena, open, &mut tasks);
                },
                EncodeTask::Close(close) => {
                    if self.placed.contains_key(&close) {
                        continue;
                    }
                    let mut record = core::mem::take(&mut self.scratch);
                    self.write_record(&mut record, arena, close);
                    self.scratch = record;
                    let id = self.intern_scratch();
                    let _prior = self.placed.insert(close, id);
                },
            }
        }
        self.tasks = tasks;
        self.content_of(node)
    }

    /// The content id already assigned to `node`.
    ///
    /// Every node this table is asked about has been placed by the walk above,
    /// so the fallback is unreachable; it keeps the read total rather than
    /// partial.
    ///
    /// # Specification
    /// - requires: `node` has been placed by this table's own walk.
    /// - ensures: returns the content id assigned to `node` by this table.
    /// - provides: the total read every record's children are written through.
    ///   The fallback is unreachable, since a record is built only after its
    ///   children are placed, and it keeps the read total rather than partial.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — the caller supplies a placed node. Lookup identity
    ///   is executable; transposed products and shared/re-minted graphs
    ///   exercise distinct child ids and reused ids, not arbitrary corrupted
    ///   tables.
    /// - witness: `encoding::tests::a_transposed_product_encodes_differently`
    /// - witness: `encoding::tests::one_table_records_each_distinct_node_once`
    #[inline]
    #[spec(
        requires: self.placed.contains_key(&node),
        ensures: |ret| self.placed.get(&node) == Some(&ret)
    )]
    fn content_of(
        &self,
        node: AnyNode,
    ) -> ContentId
    {
        self.placed.get(&node).copied().unwrap_or(ContentId(0))
    }

    /// The id this table holds for `record`, found by its digest `digest` and
    /// decided by its bytes.
    ///
    /// # Specification
    /// - requires: `digest` is `record`'s digest.
    /// - ensures: the id whose record is byte-equal to `record`, or
    ///   [`record_held::Absent::Fresh`] when the table holds none. A digest
    ///   narrows the search and never decides it: every record sharing it is
    ///   compared byte for byte.
    /// - provides: the lookup every interning step goes through; it reads the
    ///   stream in place and allocates nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two records filed under one digest stay two ids and
    ///   are each found again; a record asked twice is found by its first id.
    /// - witness: `encoding::tests::records_sharing_a_digest_keep_their_own_ids`
    /// - witness: `encoding::tests::one_table_records_each_distinct_node_once`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(id) => id.0 < self.records,
        Maybe::Absent(record_held::Absent::Fresh) => true,
    })]
    fn held(
        &self,
        record: &ContentEncoding,
        digest: ContentDigest,
    ) -> Maybe<ContentId, record_held::Absent>
    {
        let mut cursor = self.interned.get(&digest).copied();
        while let Some(id) = cursor {
            let bytes = usize::try_from(id.0)
                .ok()
                .and_then(|index| self.spans.get(index))
                .and_then(|span| self.stream.0.get(span.start .. span.end));
            if bytes == Some(record.0.as_slice()) {
                return Maybe::Present(id);
            }
            cursor = self.colliding.get(&id).copied();
        }
        Maybe::Absent(record_held::Absent::Fresh)
    }

    /// Assign the record in the scratch buffer an id, reusing the one its bytes
    /// already hold.
    ///
    /// # Specification
    /// - requires: the scratch buffer holds one complete record whose members'
    ///   ids are already assigned.
    /// - ensures: as [`Self::admit`] under the record's own digest.
    /// - provides: the canonical content numbering every record goes through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::admit`].
    /// - witness: `encoding::tests::one_table_records_each_distinct_node_once`
    /// - witness: `encoding::tests::one_key_record_per_distinct_question`
    #[inline]
    #[spec(captures: records_before = self.records,
        ensures: |ret| ret.0 < self.records && self.records >= records_before)]
    fn intern_scratch(&mut self) -> ContentId
    {
        let digest = self.scratch.digest();
        self.admit(digest)
    }

    /// Assign the record in the scratch buffer an id under the digest `digest`,
    /// reusing the one its bytes already hold.
    ///
    /// # Specification
    /// - requires: the scratch buffer holds one complete record whose members'
    ///   ids are already assigned.
    /// - ensures: the id this table already holds for those exact bytes, or a
    ///   fresh id whose record is appended to the stream and filed under
    ///   `digest` — first under it, or at the end of the records already
    ///   sharing it. Ids are assigned in stream order, byte-equal records take
    ///   one id however many nodes spell them, and records sharing a digest
    ///   keep their own ids. The record count is at most the stream's byte
    ///   length: each fresh record appends a nonempty length-prefixed image
    ///   before the count advances. On supported targets that allocation is
    ///   bounded by `isize::MAX`, below `u64::MAX`; no representable table
    ///   overflows it.
    /// - provides: the step that makes a re-minted spine reuse its untouched
    ///   leaf, which an arena-identity key forfeits. A held record is found in
    ///   place; only a fresh one grows the stream, the spans and the index.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — complete records with placed children enter a
    ///   valid table. Fresh ids, exact-byte reuse and count/stream bounds are
    ///   executable; shared and re-minted depth-16 graphs exercise both
    ///   branches, and two records forced under one digest exercise the
    ///   collision chain, not an unallocatable u64 ceiling.
    /// - witness: `encoding::tests::one_table_records_each_distinct_node_once`
    /// - witness: `encoding::tests::records_sharing_a_digest_keep_their_own_ids`
    #[spec(
        captures: [held = self.held(&self.scratch, digest), records_before = self.records,
            stream_before = self.stream.0.len()],
        ensures: |ret| u128::try_from(self.stream.0.len())
            .is_ok_and(|bytes| u128::from(self.records) <= bytes)
            && u64::try_from(self.spans.len()) == Ok(self.records) && ret.0 < self.records
            && self.held(&self.scratch, digest) == Maybe::Present(ret)
            && match held {
                Maybe::Present(prior) => ret == prior && self.records == records_before
                    && self.stream.0.len() == stream_before,
                Maybe::Absent(_) => ret.0 == records_before
                    && records_before.checked_add(1) == Some(self.records),
            }
    )]
    fn admit(
        &mut self,
        digest: ContentDigest,
    ) -> ContentId
    {
        if let Maybe::Present(held) = self.held(&self.scratch, digest) {
            return held;
        }
        let id = ContentId(self.records);
        self.stream.put_record(&self.scratch);
        let end = self.stream.0.len();
        self.spans.push(RecordSpan {
            start: end.saturating_sub(self.scratch.0.len()),
            end,
        });
        // Each record occupies memory, so the allocated table bounds this count.
        self.records = u64::from(arith::add(
            arith::Int::from(self.records),
            arith::Int::from(1_u64),
        ));
        match self.interned.get(&digest).copied() {
            None => {
                let _prior = self.interned.insert(digest, id);
            },
            Some(first) => {
                let mut tail = first;
                while let Some(&next) = self.colliding.get(&tail) {
                    tail = next;
                }
                let _prior = self.colliding.insert(tail, id);
            },
        }
        id
    }

    /// Name one read binder: the index `index` beside its type's content
    /// `binder`.
    ///
    /// # Specification
    /// - requires: `binder` is an id this table assigned.
    /// - ensures: two pairs take one id exactly when their indices and their
    ///   types' contents are equal.
    /// - provides: the pair layer of the key, built once for every cover that
    ///   reads a type of that content at that position.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one type read at two positions, and two types read at
    ///   one, key apart; one type at one position keys alike.
    /// - witness: `encoding::tests::the_read_positions_are_part_of_the_key`
    #[inline]
    #[spec(requires: binder.0 < self.records, ensures: |ret| ret.0 < self.records)]
    fn pair(
        &mut self,
        index: DeBruijnIndex,
        binder: ContentId,
    ) -> ContentId
    {
        self.scratch.0.clear();
        self.scratch.put_tag(KeyRecord::Pair.tag());
        self.scratch
            .put_word(EncodedWord(u64::from(u32::from(index))));
        self.scratch.put_content(binder);
        self.intern_scratch()
    }

    /// Name the set of binders one goal reads: the pair of each read index
    /// with its binder's type.
    ///
    /// # Specification
    /// - requires: `read`'s indices ascend strictly, and each type is a node of
    ///   `arena`. A read out of order names another cover, which can only split
    ///   a support and never merge two.
    /// - ensures: two reads take one id exactly when they read the same
    ///   positions and find types of equal content at each. Members are written
    ///   in index order, which is canonical because a cover reads each index
    ///   once.
    /// - provides: the cover layer of the key, built once for every goal whose
    ///   node reads the same binders.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty read, one read at two positions, two types
    ///   swapped between two positions, and the same read under two subjects
    ///   separate a dropped member, a position-blind member and a lost share.
    /// - witness: `encoding::tests::the_read_positions_are_part_of_the_key`
    /// - witness: `encoding::tests::one_key_record_per_distinct_question`
    #[spec(ensures: |ret| ret.0 < self.records
        && read.iter().all(|&(_, entry)| self.placed.contains_key(&AnyNode::ValueType(entry))))]
    fn cover(
        &mut self,
        arena: &TermArena,
        read: &[(DeBruijnIndex, ValueTypeId)],
    ) -> ContentId
    {
        let mut members = core::mem::take(&mut self.members);
        members.clear();
        for &(index, entry) in read {
            let binder = self.place(arena, AnyNode::ValueType(entry));
            members.push(self.pair(index, binder));
        }
        self.scratch.0.clear();
        self.scratch.put_tag(KeyRecord::Cover.tag());
        self.scratch.put_count(ComponentCount(members.len()));
        for &member in &members {
            self.scratch.put_content(member);
        }
        self.members = members;
        self.intern_scratch()
    }

    /// Name a whole context: its types' contents, outermost first.
    ///
    /// # Specification
    /// - requires: each type is a node of `arena`.
    /// - ensures: two contexts take one id exactly when they have one length
    ///   and types of equal content at every position; never the id of a cover.
    /// - provides: the key's binders for a goal whose reads are not known.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a permuted context, a longer one and a read one of
    ///   the same types key apart.
    /// - witness: `encoding::tests::the_telescope_is_folded_in_order`
    /// - witness: `encoding::tests::the_read_positions_are_part_of_the_key`
    #[spec(ensures: |ret| ret.0 < self.records
        && context.iter().all(|&entry| self.placed.contains_key(&AnyNode::ValueType(entry))))]
    fn context(
        &mut self,
        arena: &TermArena,
        context: &[ValueTypeId],
    ) -> ContentId
    {
        let mut members = core::mem::take(&mut self.members);
        members.clear();
        for &entry in context {
            members.push(self.place(arena, AnyNode::ValueType(entry)));
        }
        self.scratch.0.clear();
        self.scratch.put_tag(KeyRecord::Context.tag());
        self.scratch.put_count(ComponentCount(members.len()));
        for &member in &members {
            self.scratch.put_content(member);
        }
        self.members = members;
        self.intern_scratch()
    }

    /// Write the one-level record of `node` into `record`, replacing what it
    /// held: its tag, its inline payload, and its children's already-assigned
    /// content ids.
    ///
    /// # Specification
    /// - requires: every child of `node` has already been placed.
    /// - ensures: `record` holds the node's own one-level record — its tag, its
    ///   inline payload, and its children's content ids — or the reserved
    ///   dangling record for a reference that resolved to nothing, tagged with
    ///   the family it belonged to.
    /// - provides: the record [`Self::intern_scratch`] numbers, so a walk that
    ///   cannot read a node still produces a record and stays total; written
    ///   into a buffer the table reuses.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — children of readable nodes are placed. Readability
    ///   selects a node record or the exact family-specific dangling record;
    ///   all four unreadable families, transposed products and case children
    ///   separate wrong dispatch and lost payloads without enumerating graphs.
    /// - witness: `encoding::tests::an_unreadable_reference_still_encodes`
    /// - witness: `encoding::tests::a_transposed_product_encodes_differently`
    /// - witness: `encoding::tests::each_case_child_changes_canonical_content`
    #[spec(ensures: {
        let (readable, family) = match node { AnyNode::Value(id) => (arena.value(id).is_some(), 0_u8),
AnyNode::Computation(id) => (arena.computation(id).is_some(), 1_u8),
AnyNode::ValueType(id) => (arena.value_type(id).is_some(), 2_u8),
AnyNode::CompType(id) => (arena.comp_type(id).is_some(), 3_u8), };
        if readable {
            record.0.first().is_some_and(|&tag| tag != DANGLING_TAG)
        } else {
            record.0.len() == 2 && record.0.first() == Some(&DANGLING_TAG)
                && record.0.get(1) == Some(&family)
        }
    })]
    fn write_record(
        &self,
        record: &mut ContentEncoding,
        arena: &TermArena,
        node: AnyNode,
    )
    {
        record.0.clear();
        match node {
            AnyNode::Value(id) => match arena.value(id) {
                None => put_dangling(record, DanglingFamily::Value),
                Some(value) => self.put_value(record, value),
            },
            AnyNode::Computation(id) => match arena.computation(id) {
                None => put_dangling(record, DanglingFamily::Computation),
                Some(computation) => self.put_computation(record, computation),
            },
            AnyNode::ValueType(id) => match arena.value_type(id) {
                None => put_dangling(record, DanglingFamily::ValueType),
                Some(value_type) => self.put_value_type(record, value_type),
            },
            AnyNode::CompType(id) => match arena.comp_type(id) {
                None => put_dangling(record, DanglingFamily::CompType),
                Some(comp_type) => self.put_comp_type(record, comp_type),
            },
        }
    }

    /// Write a value node's record.
    ///
    /// # Specification
    /// - requires: every child of `value` has already been placed.
    /// - ensures: writes the former's own node tag, then its inline payload —
    ///   an index, a constant position, a literal, an injection's summand, or a
    ///   level — then each child's content id in the order the format writes
    ///   them; distinct formers write distinct tags, so no two write one
    ///   record.
    /// - provides: the value arm of the record vocabulary.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — children are already placed in this session. The
    ///   predicate checks every required child and the appended node tag.
    ///   Tuple, signed-literal and injection fixtures separate selected tags
    ///   and payloads; they do not enumerate every value.
    /// - witness: `encoding::tests::one_table_records_each_distinct_node_once`
    /// - witness: `encoding::tests::signed_zeroes_collapse_and_signed_ones_do_not`
    /// - witness: `encoding::tests::each_case_child_changes_canonical_content`
    /// - witness: `encoding::tests::two_families_with_one_payload_encode_differently`
    /// - witness: `path_universe::tests::certificate_identity_stays_out_of_conversion`
    #[spec(
        requires: match *value {
            Value::Constructor { datatype, ref fields, .. } => self.placed.contains_key(&AnyNode::ValueType(datatype)) && fields.iter().all(|id| self.placed.contains_key(&AnyNode::Value(*id))),
            Value::Record(ref fields) => fields.values().all(|id| self.placed.contains_key(&AnyNode::Value(*id))),
            Value::SessionPath { path_type: classifier, payload_paths, .. } | Value::SessionFlow { flow_type: classifier, payload_paths, .. } => self.placed.contains_key(&AnyNode::ValueType(classifier)) && self.placed.contains_key(&AnyNode::Value(payload_paths)),
            Value::PathEquiv { path_type, forward, backward, .. } => self.placed.contains_key(&AnyNode::ValueType(path_type)) && self.placed.contains_key(&AnyNode::Value(forward)) && self.placed.contains_key(&AnyNode::Value(backward)),
            Value::ListNil | Value::Variable(_) | Value::Constant(_) | Value::Literal(_) => true,
            Value::Tuple(ref components) => components.iter().all(|id| self.placed.contains_key(&AnyNode::Value(*id))),
            Value::ListCons(first, second) | Value::PathProduct(first, second) | Value::FlowProduct(first, second) | Value::StaticApplication(first, second) | Value::Then { first, second, .. } => self.placed.contains_key(&AnyNode::Value(first))
                            && self.placed.contains_key(&AnyNode::Value(second)),
            Value::PathRefl(body) | Value::Univalence(body) | Value::Here { point: body, .. } | Value::Stay { point: body, .. } | Value::Injection(_, body) | Value::Lift { body, .. } => self.placed.contains_key(&AnyNode::Value(body)),
            Value::ForwardFlow { flow_type, translator, ref outputs, .. } => self.placed.contains_key(&AnyNode::ValueType(flow_type)) && self.placed.contains_key(&AnyNode::Value(translator)) && outputs.iter().all(|id| self.placed.contains_key(&AnyNode::Value(*id))),
            Value::FunctionFlow { flow_type, domain, codomain } => self.placed.contains_key(&AnyNode::ValueType(flow_type)) && self.placed.contains_key(&AnyNode::Value(domain)) && self.placed.contains_key(&AnyNode::Value(codomain)),
            Value::Higher { ref evidence, .. } => evidence.iter().all(|id| self.placed.contains_key(&AnyNode::Value(*id))),
            Value::HigherEvaluation { ref components, .. } => components.iter().all(|component| [component.left, component.right, component.evidence].iter().all(|id| self.placed.contains_key(&AnyNode::Value(*id)))),
            Value::QuantifiedEvaluation { ref children, .. } => children.iter().all(|id| self.placed.contains_key(&AnyNode::Value(*id))),
            Value::Thunk(body) | Value::Returned(body) => self.placed.contains_key(&AnyNode::Computation(body)),
            Value::Quote(quoted) => self.placed.contains_key(&AnyNode::ValueType(quoted)),
            Value::QuoteComputation(quoted) => self.placed.contains_key(&AnyNode::CompType(quoted)),
        },
        captures: entry_len = record.0.len(),
        ensures: record.0.get(entry_len) == Some(&u8::from(match *value {
            Value::Constructor { .. } => gandr_kernel_term::NODE_V_CONSTRUCTOR,
            Value::Record(_) => gandr_kernel_term::NODE_V_RECORD,
            Value::SessionPath { .. } => gandr_kernel_term::NODE_V_SESSION_PATH,
            Value::SessionFlow { .. } => gandr_kernel_term::NODE_V_SESSION_FLOW,
            Value::PathRefl(_) => gandr_kernel_term::NODE_V_PATH_REFL,
            Value::PathProduct(..) => gandr_kernel_term::NODE_V_PATH_PRODUCT,
            Value::PathEquiv { .. } => gandr_kernel_term::NODE_V_PATH_EQUIV,
            Value::Univalence { .. } => gandr_kernel_term::NODE_V_UNIVALENCE,
            Value::Here { .. } => gandr_kernel_term::NODE_V_HERE,
            Value::Stay { .. } => gandr_kernel_term::NODE_V_STAY,
            Value::ForwardFlow { .. } => gandr_kernel_term::NODE_V_FORWARD_FLOW,
            Value::FunctionFlow { .. } => gandr_kernel_term::NODE_V_FUNCTION_FLOW,
            Value::Then { .. } => gandr_kernel_term::NODE_V_THEN,
            Value::FlowProduct(..) => gandr_kernel_term::NODE_V_FLOW_PRODUCT,
            Value::Returned(_) => gandr_kernel_term::NODE_V_RETURNED,
            Value::Higher { .. } => gandr_kernel_term::NODE_V_HIGHER,
            Value::HigherEvaluation { .. } => gandr_kernel_term::NODE_V_HIGHER_EVALUATION,
            Value::QuantifiedEvaluation { .. } => gandr_kernel_term::NODE_V_QUANTIFIED_EVALUATION,
            Value::Variable(..) => gandr_kernel_term::NODE_V_VARIABLE,
            Value::Constant(..) => gandr_kernel_term::NODE_V_CONSTANT,
            Value::ListNil => gandr_kernel_term::NODE_V_LIST_NIL,
            Value::ListCons(..) => gandr_kernel_term::NODE_V_LIST_CONS,
            Value::Literal(..) => gandr_kernel_term::NODE_V_LITERAL,
            Value::Tuple(..) => gandr_kernel_term::NODE_V_TUPLE,
            Value::Injection(..) => gandr_kernel_term::NODE_V_INJECTION,
            Value::Thunk(..) => gandr_kernel_term::NODE_V_THUNK,
            Value::Lift { .. } => gandr_kernel_term::NODE_V_LIFT,
            Value::Quote(..) => gandr_kernel_term::NODE_V_QUOTE,
            Value::QuoteComputation(..) => gandr_kernel_term::NODE_V_QUOTE_COMPUTATION,
            Value::StaticApplication(..) => gandr_kernel_term::NODE_V_STATIC_APPLICATION,
        }))
    )]
    fn put_value(
        &self,
        record: &mut ContentEncoding,
        value: &Value,
    )
    {
        match *value {
            Value::Constructor {
                datatype,
                tag,
                ref fields,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_CONSTRUCTOR);
                record.put_count(ComponentCount(usize::from(tag)));
                record.put_count(ComponentCount(fields.len()));
                record.put_content(self.content_of(AnyNode::ValueType(datatype)));
                for field in fields {
                    record.put_content(self.content_of(AnyNode::Value(*field)));
                }
            },
            Value::Record(ref fields) => {
                record.put_tag(gandr_kernel_term::NODE_V_RECORD);
                record.put_count(ComponentCount(fields.len()));
                for (label, value) in fields {
                    record.put_text(EncodedText(label.as_ref()));
                    record.put_content(self.content_of(AnyNode::Value(*value)));
                }
            },
            Value::ListNil => record.put_tag(gandr_kernel_term::NODE_V_LIST_NIL),
            Value::ListCons(head, tail) => {
                record.put_tag(gandr_kernel_term::NODE_V_LIST_CONS);
                record.put_content(self.content_of(AnyNode::Value(head)));
                record.put_content(self.content_of(AnyNode::Value(tail)));
            },
            Value::SessionPath {
                path_type,
                payload_paths,
                ref evidence,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_SESSION_PATH);
                evidence.write(|word| record.put_word(EncodedWord(word.0)));
                record.put_content(self.content_of(AnyNode::ValueType(path_type)));
                record.put_content(self.content_of(AnyNode::Value(payload_paths)));
            },
            Value::SessionFlow {
                flow_type,
                payload_paths,
                ref evidence,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_SESSION_FLOW);
                evidence.write(|word| record.put_word(EncodedWord(word.0)));
                record.put_content(self.content_of(AnyNode::ValueType(flow_type)));
                record.put_content(self.content_of(AnyNode::Value(payload_paths)));
            },
            Value::PathRefl(code) => {
                record.put_tag(gandr_kernel_term::NODE_V_PATH_REFL);
                record.put_content(self.content_of(AnyNode::Value(code)));
            },
            Value::PathProduct(first, second) => {
                record.put_tag(gandr_kernel_term::NODE_V_PATH_PRODUCT);
                record.put_content(self.content_of(AnyNode::Value(first)));
                record.put_content(self.content_of(AnyNode::Value(second)));
            },
            Value::PathEquiv {
                path_type,
                forward,
                backward,
                ref evidence,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_PATH_EQUIV);
                for word in evidence.words() {
                    record.put_word(EncodedWord(word.0));
                }
                record.put_content(self.content_of(AnyNode::ValueType(path_type)));
                record.put_content(self.content_of(AnyNode::Value(forward)));
                record.put_content(self.content_of(AnyNode::Value(backward)));
            },
            Value::Univalence(equivalence) => {
                record.put_tag(gandr_kernel_term::NODE_V_UNIVALENCE);
                record.put_content(self.content_of(AnyNode::Value(equivalence)));
            },
            Value::Here {
                point,
                ref dialogues,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_HERE);
                for word in gandr_kernel_term::endpoint_words(dialogues) {
                    record.put_word(EncodedWord(word.0));
                }
                record.put_content(self.content_of(AnyNode::Value(point)));
            },
            Value::Stay {
                point,
                ref dialogues,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_STAY);
                for word in gandr_kernel_term::endpoint_words(dialogues) {
                    record.put_word(EncodedWord(word.0));
                }
                record.put_content(self.content_of(AnyNode::Value(point)));
            },
            Value::ForwardFlow {
                flow_type,
                translator,
                ref outputs,
                ref dialogues,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_FORWARD_FLOW);
                for word in gandr_kernel_term::forward_words(dialogues) {
                    record.put_word(EncodedWord(word.0));
                }
                record.put_content(self.content_of(AnyNode::ValueType(flow_type)));
                record.put_content(self.content_of(AnyNode::Value(translator)));
                for output in outputs {
                    record.put_content(self.content_of(AnyNode::Value(*output)));
                }
            },
            Value::FunctionFlow {
                flow_type,
                domain,
                codomain,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_FUNCTION_FLOW);
                record.put_content(self.content_of(AnyNode::ValueType(flow_type)));
                record.put_content(self.content_of(AnyNode::Value(domain)));
                record.put_content(self.content_of(AnyNode::Value(codomain)));
            },
            Value::Then {
                first,
                second,
                seam,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_THEN);
                record.put_tag(match seam {
                    gandr_kernel_term::Seam::Sequence => gandr_kernel_term::SEAM_SEQUENCE,
                    gandr_kernel_term::Seam::Feedback => gandr_kernel_term::SEAM_FEEDBACK,
                });
                record.put_content(self.content_of(AnyNode::Value(first)));
                record.put_content(self.content_of(AnyNode::Value(second)));
            },
            Value::FlowProduct(first, second) => {
                record.put_tag(gandr_kernel_term::NODE_V_FLOW_PRODUCT);
                record.put_content(self.content_of(AnyNode::Value(first)));
                record.put_content(self.content_of(AnyNode::Value(second)));
            },
            Value::Returned(computation) => {
                record.put_tag(gandr_kernel_term::NODE_V_RETURNED);
                record.put_content(self.content_of(AnyNode::Computation(computation)));
            },
            Value::Higher {
                ref program,
                ref evidence,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_HIGHER);
                for word in program.words() {
                    record.put_word(EncodedWord(word.0));
                }
                for layer in evidence {
                    record.put_content(self.content_of(AnyNode::Value(*layer)));
                }
            },
            Value::HigherEvaluation {
                ref dialogues,
                ref components,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_HIGHER_EVALUATION);
                for word in gandr_kernel_term::evaluation_words(dialogues) {
                    record.put_word(EncodedWord(word.0));
                }
                for component in components {
                    for child in [component.left, component.right, component.evidence] {
                        record.put_content(self.content_of(AnyNode::Value(child)));
                    }
                }
            },
            Value::QuantifiedEvaluation {
                ref steps,
                ref children,
            } => {
                record.put_tag(gandr_kernel_term::NODE_V_QUANTIFIED_EVALUATION);
                for word in gandr_kernel_term::quantified_words(steps) {
                    record.put_word(EncodedWord(word.0));
                }
                for child in children {
                    record.put_content(self.content_of(AnyNode::Value(*child)));
                }
            },
            Value::Variable(index) => {
                record.put_tag(gandr_kernel_term::NODE_V_VARIABLE);
                record.put_word(EncodedWord(u64::from(u32::from(index))));
            },
            Value::Constant(index) => {
                record.put_tag(gandr_kernel_term::NODE_V_CONSTANT);
                record.put_count(ComponentCount(usize::from(index)));
            },
            Value::Literal(ref literal) => {
                record.put_tag(gandr_kernel_term::NODE_V_LITERAL);
                put_literal(record, literal);
            },
            Value::Tuple(ref components) => {
                record.put_tag(gandr_kernel_term::NODE_V_TUPLE);
                record.put_count(ComponentCount(components.len()));
                for component in components {
                    record.put_content(self.content_of(AnyNode::Value(*component)));
                }
            },
            Value::Injection(summand, body) => {
                record.put_tag(gandr_kernel_term::NODE_V_INJECTION);
                record.put_count(ComponentCount(usize::from(summand)));
                record.put_content(self.content_of(AnyNode::Value(body)));
            },
            Value::Thunk(body) => {
                record.put_tag(gandr_kernel_term::NODE_V_THUNK);
                record.put_content(self.content_of(AnyNode::Computation(body)));
            },
            Value::Lift { ref target, body } => {
                record.put_tag(gandr_kernel_term::NODE_V_LIFT);
                put_level(record, target);
                record.put_content(self.content_of(AnyNode::Value(body)));
            },
            Value::Quote(quoted) => {
                record.put_tag(gandr_kernel_term::NODE_V_QUOTE);
                record.put_content(self.content_of(AnyNode::ValueType(quoted)));
            },
            Value::QuoteComputation(quoted) => {
                record.put_tag(gandr_kernel_term::NODE_V_QUOTE_COMPUTATION);
                record.put_content(self.content_of(AnyNode::CompType(quoted)));
            },
            Value::StaticApplication(head, argument) => {
                record.put_tag(gandr_kernel_term::NODE_V_STATIC_APPLICATION);
                record.put_content(self.content_of(AnyNode::Value(head)));
                record.put_content(self.content_of(AnyNode::Value(argument)));
            },
        }
    }

    /// Write a computation node's record.
    ///
    /// # Specification
    /// - requires: every child of `computation` has already been placed.
    /// - ensures: writes the former's own node tag and then each child's
    ///   content id in format order; distinct formers write distinct tags.
    /// - provides: the computation arm of the record vocabulary.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — children are already placed in this session. The
    ///   predicate checks every required child and the appended node tag. Case
    ///   fixtures change each of its children independently and descend through
    ///   returns; other forms retain executable tag and placement checks.
    /// - witness: `encoding::tests::each_case_child_changes_canonical_content`
    #[spec(
        requires: match *computation {
            Computation::DataCase { scrutinee, motive, ref branches } => self.placed.contains_key(&AnyNode::Value(scrutinee)) && self.placed.contains_key(&AnyNode::CompType(motive)) && branches.iter().all(|id| self.placed.contains_key(&AnyNode::Computation(*id))),
            Computation::SigmaSplit { scrutinee, motive, body } => [AnyNode::Value(scrutinee), AnyNode::CompType(motive), AnyNode::Computation(body)].iter().all(|child| self.placed.contains_key(child)),
            Computation::RecordProjection(record, _) | Computation::TupleProjection(record, _) => self.placed.contains_key(&AnyNode::Value(record)),
            Computation::ListFold { element, result, list, on_nil, on_cons } => [AnyNode::ValueType(element), AnyNode::ValueType(result), AnyNode::Value(list), AnyNode::Computation(on_nil), AnyNode::Computation(on_cons)].iter().all(|child| self.placed.contains_key(child)),
            Computation::Transport(path, value) => self.placed.contains_key(&AnyNode::Value(path)) && self.placed.contains_key(&AnyNode::Value(value)),
            Computation::PathTransport { motive, path, value } | Computation::Ride { motive, flow: path, value } => self.placed.contains_key(&AnyNode::ValueType(motive)) && self.placed.contains_key(&AnyNode::Value(path)) && self.placed.contains_key(&AnyNode::Value(value)),
            Computation::TelescopeTransport { motive, path, start, over, value } | Computation::TelescopeRide { motive, flow: path, start, over, value } => [AnyNode::CompType(motive), AnyNode::Value(path), AnyNode::Value(start), AnyNode::Value(over), AnyNode::Value(value)].iter().all(|child| self.placed.contains_key(child)),
            Computation::RelatedApplication { path, left, right, evidence, body } => [AnyNode::Value(path), AnyNode::Value(left), AnyNode::Value(right), AnyNode::Value(evidence), AnyNode::Computation(body)].iter().all(|child| self.placed.contains_key(child)),
            Computation::Lambda(body) | Computation::Fixpoint { body, .. } => self.placed.contains_key(&AnyNode::Computation(body)),
            Computation::Application(head, argument) => self.placed.contains_key(&AnyNode::Computation(head))
                            && self.placed.contains_key(&AnyNode::Value(argument)),
            Computation::Return(value) | Computation::Force(value) => self.placed.contains_key(&AnyNode::Value(value)),
            Computation::Bind(bound, body) | Computation::With(bound, body) => self.placed.contains_key(&AnyNode::Computation(bound))
                            && self.placed.contains_key(&AnyNode::Computation(body)),
            Computation::Project(_, pair) => self.placed.contains_key(&AnyNode::Computation(pair)),
            Computation::Case { scrutinee, ref branches } => self.placed.contains_key(&AnyNode::Value(scrutinee))
                            && branches.iter().all(|id| self.placed.contains_key(&AnyNode::Computation(*id))),
        },
        captures: entry_len = record.0.len(),
        ensures: record.0.get(entry_len) == Some(&u8::from(match *computation {
            Computation::DataCase { .. } => gandr_kernel_term::NODE_C_DATA_CASE,
            Computation::SigmaSplit { .. } => gandr_kernel_term::NODE_C_SIGMA_SPLIT,
            Computation::RecordProjection(..) => gandr_kernel_term::NODE_C_RECORD_PROJECTION,
            Computation::TupleProjection(..) => gandr_kernel_term::NODE_C_TUPLE_PROJECTION,
            Computation::Transport(..) => gandr_kernel_term::NODE_C_TRANSPORT,
            Computation::PathTransport { .. } => gandr_kernel_term::NODE_C_PATH_TRANSPORT,
            Computation::TelescopeTransport { .. } => gandr_kernel_term::NODE_C_TELESCOPE_TRANSPORT,
            Computation::Ride { .. } => gandr_kernel_term::NODE_C_RIDE,
            Computation::TelescopeRide { .. } => gandr_kernel_term::NODE_C_TELESCOPE_RIDE,
            Computation::RelatedApplication { .. } => gandr_kernel_term::NODE_C_RELATED_APPLICATION,
            Computation::ListFold { .. } => gandr_kernel_term::NODE_C_LIST_FOLD,
            Computation::Lambda(..) => gandr_kernel_term::NODE_C_LAMBDA,
            Computation::Fixpoint { .. } => gandr_kernel_term::NODE_C_FIXPOINT,
            Computation::Application(..) => gandr_kernel_term::NODE_C_APPLICATION,
            Computation::Return(..) => gandr_kernel_term::NODE_C_RETURN,
            Computation::Bind(..) => gandr_kernel_term::NODE_C_BIND,
            Computation::Force(..) => gandr_kernel_term::NODE_C_FORCE,
            Computation::Case { .. } => gandr_kernel_term::NODE_C_CASE,
            Computation::With(..) => gandr_kernel_term::NODE_C_WITH,
            Computation::Project(..) => gandr_kernel_term::NODE_C_PROJECT,
        }))
    )]
    fn put_computation(
        &self,
        record: &mut ContentEncoding,
        computation: &Computation,
    )
    {
        match *computation {
            Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
            } => {
                record.put_tag(gandr_kernel_term::NODE_C_DATA_CASE);
                record.put_count(ComponentCount(branches.len()));
                record.put_content(self.content_of(AnyNode::Value(scrutinee)));
                record.put_content(self.content_of(AnyNode::CompType(motive)));
                for branch in branches {
                    record.put_content(self.content_of(AnyNode::Computation(*branch)));
                }
            },
            Computation::SigmaSplit {
                scrutinee,
                motive,
                body,
            } => {
                record.put_tag(gandr_kernel_term::NODE_C_SIGMA_SPLIT);
                for child in [
                    AnyNode::Value(scrutinee),
                    AnyNode::CompType(motive),
                    AnyNode::Computation(body),
                ] {
                    record.put_content(self.content_of(child));
                }
            },
            Computation::RecordProjection(value, ref label) => {
                record.put_tag(gandr_kernel_term::NODE_C_RECORD_PROJECTION);
                record.put_text(EncodedText(label.as_ref()));
                record.put_content(self.content_of(AnyNode::Value(value)));
            },
            Computation::TupleProjection(value, component) => {
                record.put_tag(gandr_kernel_term::NODE_C_TUPLE_PROJECTION);
                record.put_count(ComponentCount(usize::from(component)));
                record.put_content(self.content_of(AnyNode::Value(value)));
            },
            Computation::ListFold {
                element,
                result,
                list,
                on_nil,
                on_cons,
            } => {
                record.put_tag(gandr_kernel_term::NODE_C_LIST_FOLD);
                for child in [
                    AnyNode::ValueType(element),
                    AnyNode::ValueType(result),
                    AnyNode::Value(list),
                    AnyNode::Computation(on_nil),
                    AnyNode::Computation(on_cons),
                ] {
                    record.put_content(self.content_of(child));
                }
            },
            Computation::Transport(path, value) => {
                record.put_tag(gandr_kernel_term::NODE_C_TRANSPORT);
                record.put_content(self.content_of(AnyNode::Value(path)));
                record.put_content(self.content_of(AnyNode::Value(value)));
            },
            Computation::PathTransport {
                motive,
                path,
                value,
            } => {
                record.put_tag(gandr_kernel_term::NODE_C_PATH_TRANSPORT);
                record.put_content(self.content_of(AnyNode::ValueType(motive)));
                record.put_content(self.content_of(AnyNode::Value(path)));
                record.put_content(self.content_of(AnyNode::Value(value)));
            },
            Computation::TelescopeTransport {
                motive,
                path,
                start,
                over,
                value,
            } => {
                record.put_tag(gandr_kernel_term::NODE_C_TELESCOPE_TRANSPORT);
                for child in [
                    AnyNode::CompType(motive),
                    AnyNode::Value(path),
                    AnyNode::Value(start),
                    AnyNode::Value(over),
                    AnyNode::Value(value),
                ] {
                    record.put_content(self.content_of(child));
                }
            },
            Computation::Ride {
                motive,
                flow,
                value,
            } => {
                record.put_tag(gandr_kernel_term::NODE_C_RIDE);
                record.put_content(self.content_of(AnyNode::ValueType(motive)));
                record.put_content(self.content_of(AnyNode::Value(flow)));
                record.put_content(self.content_of(AnyNode::Value(value)));
            },
            Computation::TelescopeRide {
                motive,
                flow,
                start,
                over,
                value,
            } => {
                record.put_tag(gandr_kernel_term::NODE_C_TELESCOPE_RIDE);
                for child in [
                    AnyNode::CompType(motive),
                    AnyNode::Value(flow),
                    AnyNode::Value(start),
                    AnyNode::Value(over),
                    AnyNode::Value(value),
                ] {
                    record.put_content(self.content_of(child));
                }
            },
            Computation::RelatedApplication {
                path,
                left,
                right,
                evidence,
                body,
            } => {
                record.put_tag(gandr_kernel_term::NODE_C_RELATED_APPLICATION);
                for child in [
                    AnyNode::Value(path),
                    AnyNode::Value(left),
                    AnyNode::Value(right),
                    AnyNode::Value(evidence),
                    AnyNode::Computation(body),
                ] {
                    record.put_content(self.content_of(child));
                }
            },
            Computation::Lambda(body) => {
                record.put_tag(gandr_kernel_term::NODE_C_LAMBDA);
                record.put_content(self.content_of(AnyNode::Computation(body)));
            },
            Computation::Fixpoint { body, evidence } => {
                record.put_tag(gandr_kernel_term::NODE_C_FIXPOINT);
                record.put_tag(match evidence {
                    gandr_kernel_term::FixpointEvidence::Partial => {
                        gandr_kernel_term::FIXPOINT_PARTIAL
                    },
                    gandr_kernel_term::FixpointEvidence::StructuralDescent => {
                        gandr_kernel_term::FIXPOINT_STRUCTURAL_DESCENT
                    },
                    gandr_kernel_term::FixpointEvidence::Staged { .. } => {
                        gandr_kernel_term::FIXPOINT_STAGED
                    },
                });
                if let gandr_kernel_term::FixpointEvidence::Staged { position } = evidence {
                    record.put_word(EncodedWord(
                        u64::try_from(usize::from(position)).unwrap_or(u64::MAX),
                    ));
                }
                record.put_content(self.content_of(AnyNode::Computation(body)));
            },
            Computation::Application(head, argument) => {
                record.put_tag(gandr_kernel_term::NODE_C_APPLICATION);
                record.put_content(self.content_of(AnyNode::Computation(head)));
                record.put_content(self.content_of(AnyNode::Value(argument)));
            },
            Computation::Return(value) => {
                record.put_tag(gandr_kernel_term::NODE_C_RETURN);
                record.put_content(self.content_of(AnyNode::Value(value)));
            },
            Computation::Bind(bound, body) => {
                record.put_tag(gandr_kernel_term::NODE_C_BIND);
                record.put_content(self.content_of(AnyNode::Computation(bound)));
                record.put_content(self.content_of(AnyNode::Computation(body)));
            },
            Computation::Force(value) => {
                record.put_tag(gandr_kernel_term::NODE_C_FORCE);
                record.put_content(self.content_of(AnyNode::Value(value)));
            },
            Computation::Case {
                scrutinee,
                ref branches,
            } => {
                record.put_tag(gandr_kernel_term::NODE_C_CASE);
                record.put_count(ComponentCount(branches.len()));
                record.put_content(self.content_of(AnyNode::Value(scrutinee)));
                for branch in branches {
                    record.put_content(self.content_of(AnyNode::Computation(*branch)));
                }
            },
            Computation::With(left, right) => {
                record.put_tag(gandr_kernel_term::NODE_C_WITH);
                record.put_content(self.content_of(AnyNode::Computation(left)));
                record.put_content(self.content_of(AnyNode::Computation(right)));
            },
            Computation::Project(side, pair) => {
                record.put_tag(gandr_kernel_term::NODE_C_PROJECT);
                record.put_tag(match side {
                    gandr_kernel_term::Side::Left => gandr_kernel_term::SIDE_LEFT,
                    gandr_kernel_term::Side::Right => gandr_kernel_term::SIDE_RIGHT,
                });
                record.put_content(self.content_of(AnyNode::Computation(pair)));
            },
        }
    }

    /// Write a value-type node's record.
    ///
    /// # Specification
    /// - requires: every child of `value_type` has already been placed.
    /// - ensures: writes the former's own node tag, then its inline payload — a
    ///   base atom, a level, or a sealed-atom position — then each child's
    ///   content id in format order; distinct formers write distinct tags.
    /// - provides: the value-type arm of the record vocabulary.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — children are already placed in this session. The
    ///   predicate checks every required child and the appended node tag.
    ///   Unit/base and transposed-product fixtures separate family tags and
    ///   ordered child ids; no exhaustive graph domain is claimed.
    /// - witness: `encoding::tests::a_transposed_product_encodes_differently`
    /// - witness: `path_universe::tests::certificate_identity_stays_out_of_conversion`
    /// - witness: `encoding::tests::two_families_with_one_payload_encode_differently`
    #[spec(
        requires: match *value_type {
            ValueType::Data { ref arguments, .. } => arguments.iter().all(|id| self.placed.contains_key(&AnyNode::Value(*id))),
            ValueType::Record(ref fields) => fields.values().all(|id| self.placed.contains_key(&AnyNode::ValueType(*id))),
            ValueType::Session { payloads, .. } => self.placed.contains_key(&AnyNode::ValueType(payloads)),
            ValueType::PathUniverse(source, target) | ValueType::FlowUniverse(source, target) => self.placed.contains_key(&AnyNode::Value(source)) && self.placed.contains_key(&AnyNode::Value(target)),
            ValueType::Path { domain, left, right } | ValueType::Flow { domain, source: left, target: right } | ValueType::Bridge { domain, left, right } => self.placed.contains_key(&AnyNode::ValueType(domain)) && self.placed.contains_key(&AnyNode::Value(left)) && self.placed.contains_key(&AnyNode::Value(right)),
            ValueType::Base(_) | ValueType::Universe { sort: GroundSort::Value, .. } | ValueType::Universe { sort: GroundSort::Computation, .. } | ValueType::Abstract(_) => true,
            ValueType::Product(ref parts) | ValueType::Sum(ref parts) => parts.iter().all(|id| self.placed.contains_key(&AnyNode::ValueType(*id))),
            ValueType::StaticPi { domain: first, codomain: second } | ValueType::Sigma { first, second } => self.placed.contains_key(&AnyNode::ValueType(first))
                            && self.placed.contains_key(&AnyNode::ValueType(second)),
            ValueType::Thunk(body) => self.placed.contains_key(&AnyNode::CompType(body)),
            ValueType::Lift { inner, .. } | ValueType::List(inner) | ValueType::Staged { base: inner, .. } => self.placed.contains_key(&AnyNode::ValueType(inner)),
            ValueType::Element { code, .. } => self.placed.contains_key(&AnyNode::Value(code)),
        },
        captures: entry_len = record.0.len(),
        ensures: record.0.get(entry_len) == Some(&u8::from(match *value_type {
            ValueType::Data { .. } => gandr_kernel_term::NODE_VT_DATA,
            ValueType::Record(_) => gandr_kernel_term::NODE_VT_RECORD,
            ValueType::Session { .. } => gandr_kernel_term::NODE_VT_SESSION,
            ValueType::PathUniverse(..) => gandr_kernel_term::NODE_VT_PATH_UNIVERSE,
            ValueType::FlowUniverse(..) => gandr_kernel_term::NODE_VT_FLOW_UNIVERSE,
            ValueType::Path { .. } => gandr_kernel_term::NODE_VT_PATH,
            ValueType::Flow { .. } => gandr_kernel_term::NODE_VT_FLOW,
            ValueType::Bridge { .. } => gandr_kernel_term::NODE_VT_BRIDGE,
            ValueType::List(_) => gandr_kernel_term::NODE_VT_LIST,
            ValueType::Base(..) => gandr_kernel_term::NODE_VT_BASE,
            ValueType::Universe { sort: GroundSort::Value, .. } => gandr_kernel_term::NODE_VT_UNIVERSE,
            ValueType::Universe { sort: GroundSort::Computation, .. } => gandr_kernel_term::NODE_VT_COMPUTATION_UNIVERSE,
            ValueType::Product(..) => gandr_kernel_term::NODE_VT_PRODUCT,
            ValueType::Sum(..) => gandr_kernel_term::NODE_VT_SUM,
            ValueType::Thunk(..) => gandr_kernel_term::NODE_VT_THUNK,
            ValueType::Lift { .. } => gandr_kernel_term::NODE_VT_LIFT,
            ValueType::Element { .. } => gandr_kernel_term::NODE_VT_ELEMENT,
            ValueType::Abstract(..) => gandr_kernel_term::NODE_VT_ABSTRACT,
            ValueType::StaticPi { .. } => gandr_kernel_term::NODE_VT_STATIC_PI,
            ValueType::Sigma { .. } => gandr_kernel_term::NODE_VT_SIGMA,
            ValueType::Staged { .. } => record_staged(),
        }))
    )]
    fn put_value_type(
        &self,
        record: &mut ContentEncoding,
        value_type: &ValueType,
    )
    {
        match *value_type {
            ValueType::Data {
                declaration,
                ref arguments,
            } => {
                record.put_tag(gandr_kernel_term::NODE_VT_DATA);
                record.put_count(ComponentCount(usize::from(declaration)));
                record.put_count(ComponentCount(arguments.len()));
                for argument in arguments {
                    record.put_content(self.content_of(AnyNode::Value(*argument)));
                }
            },
            ValueType::Record(ref fields) => {
                record.put_tag(gandr_kernel_term::NODE_VT_RECORD);
                record.put_count(ComponentCount(fields.len()));
                for (label, ty) in fields {
                    record.put_text(EncodedText(label.as_ref()));
                    record.put_content(self.content_of(AnyNode::ValueType(*ty)));
                }
            },
            ValueType::PathUniverse(source, target) => {
                record.put_tag(gandr_kernel_term::NODE_VT_PATH_UNIVERSE);
                record.put_content(self.content_of(AnyNode::Value(source)));
                record.put_content(self.content_of(AnyNode::Value(target)));
            },
            ValueType::FlowUniverse(source, target) => {
                record.put_tag(gandr_kernel_term::NODE_VT_FLOW_UNIVERSE);
                record.put_content(self.content_of(AnyNode::Value(source)));
                record.put_content(self.content_of(AnyNode::Value(target)));
            },
            ValueType::Path {
                domain,
                left,
                right,
            } => {
                record.put_tag(gandr_kernel_term::NODE_VT_PATH);
                record.put_content(self.content_of(AnyNode::ValueType(domain)));
                record.put_content(self.content_of(AnyNode::Value(left)));
                record.put_content(self.content_of(AnyNode::Value(right)));
            },
            ValueType::Flow {
                domain,
                source,
                target,
            } => {
                record.put_tag(gandr_kernel_term::NODE_VT_FLOW);
                record.put_content(self.content_of(AnyNode::ValueType(domain)));
                record.put_content(self.content_of(AnyNode::Value(source)));
                record.put_content(self.content_of(AnyNode::Value(target)));
            },
            ValueType::Bridge {
                domain,
                left,
                right,
            } => {
                record.put_tag(gandr_kernel_term::NODE_VT_BRIDGE);
                record.put_content(self.content_of(AnyNode::ValueType(domain)));
                record.put_content(self.content_of(AnyNode::Value(left)));
                record.put_content(self.content_of(AnyNode::Value(right)));
            },
            ValueType::Base(base) => {
                record.put_tag(gandr_kernel_term::NODE_VT_BASE);
                record.put_tag(base_tag(base));
            },
            ValueType::Universe {
                sort: GroundSort::Value,
                ref level,
            } => {
                record.put_tag(gandr_kernel_term::NODE_VT_UNIVERSE);
                put_level(record, level);
            },
            ValueType::Universe {
                sort: GroundSort::Computation,
                ref level,
            } => {
                record.put_tag(gandr_kernel_term::NODE_VT_COMPUTATION_UNIVERSE);
                put_level(record, level);
            },
            ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                record.put_tag(match *value_type {
                    ValueType::Product(_) => gandr_kernel_term::NODE_VT_PRODUCT,
                    ValueType::Data { .. }
                    | ValueType::Record(_)
                    | ValueType::Session { .. }
                    | ValueType::PathUniverse(..)
                    | ValueType::FlowUniverse(..)
                    | ValueType::Path { .. }
                    | ValueType::Flow { .. }
                    | ValueType::Bridge { .. }
                    | ValueType::Base(_)
                    | ValueType::Sigma { .. }
                    | ValueType::Sum(_)
                    | ValueType::List(_)
                    | ValueType::Thunk(_)
                    | ValueType::Universe { .. }
                    | ValueType::Lift { .. }
                    | ValueType::Element { .. }
                    | ValueType::Abstract(_)
                    | ValueType::StaticPi { .. }
                    | ValueType::Staged { .. } => gandr_kernel_term::NODE_VT_SUM,
                });
                record.put_count(ComponentCount(parts.len()));
                for part in parts {
                    record.put_content(self.content_of(AnyNode::ValueType(*part)));
                }
            },
            ValueType::Thunk(body) => {
                record.put_tag(gandr_kernel_term::NODE_VT_THUNK);
                record.put_content(self.content_of(AnyNode::CompType(body)));
            },
            ValueType::Session {
                ref graph,
                payloads,
            } => {
                record.put_tag(gandr_kernel_term::NODE_VT_SESSION);
                graph.write(|word| record.put_word(EncodedWord(word.0)));
                record.put_content(self.content_of(AnyNode::ValueType(payloads)));
            },
            ValueType::List(element) => {
                record.put_tag(gandr_kernel_term::NODE_VT_LIST);
                record.put_content(self.content_of(AnyNode::ValueType(element)));
            },
            ValueType::Lift { inner, ref target } => {
                record.put_tag(gandr_kernel_term::NODE_VT_LIFT);
                record.put_content(self.content_of(AnyNode::ValueType(inner)));
                put_level(record, target);
            },
            ValueType::Element { code, ref target } => {
                record.put_tag(gandr_kernel_term::NODE_VT_ELEMENT);
                put_level(record, target);
                record.put_content(self.content_of(AnyNode::Value(code)));
            },
            ValueType::Abstract(atom) => {
                record.put_tag(gandr_kernel_term::NODE_VT_ABSTRACT);
                record.put_count(ComponentCount(usize::from(atom)));
            },
            ValueType::StaticPi { domain, codomain } => {
                record.put_tag(gandr_kernel_term::NODE_VT_STATIC_PI);
                record.put_content(self.content_of(AnyNode::ValueType(domain)));
                record.put_content(self.content_of(AnyNode::ValueType(codomain)));
            },
            ValueType::Sigma { first, second } => {
                record.put_tag(gandr_kernel_term::NODE_VT_SIGMA);
                record.put_content(self.content_of(AnyNode::ValueType(first)));
                record.put_content(self.content_of(AnyNode::ValueType(second)));
            },
            // A stage is part of a type's identity within the judgement that
            // minted it: `A^s` and `A` are different goals' types, and so are
            // `A` at two stages.
            ValueType::Staged { base, stage } => {
                record.put_tag(record_staged());
                record.put_content(self.content_of(AnyNode::ValueType(base)));
                match stage {
                    gandr_kernel_term::Stage::At(exact) => {
                        record.put_tag(stage_exact());
                        record.put_count(ComponentCount(usize::from(exact)));
                    },
                    gandr_kernel_term::Stage::Below { anchor, depth } => {
                        record.put_tag(stage_bound());
                        record.put_count(ComponentCount(usize::from(anchor)));
                        record.put_word(EncodedWord(u64::from(u32::from(depth))));
                    },
                }
            },
        }
    }

    /// Write a computation-type node's record.
    ///
    /// # Specification
    /// - requires: every child of `comp_type` has already been placed.
    /// - ensures: writes the former's own node tag and then each child's
    ///   content id in format order. The dependent arrow and the arrow carry
    ///   the same two children and differ in their tag alone, which is exactly
    ///   why the two tags are separate: sharing one would collapse two types
    ///   onto a single content id.
    /// - provides: the computation-type arm of the record vocabulary.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — children are already placed in this session. The
    ///   predicate checks every required child and the appended node tag.
    ///   Returner, arrow, dependent arrow and neutral element fixtures separate
    ///   every computation-type tag; the arrows share identical children.
    /// - witness: `encoding::tests::computation_type_formers_keep_distinct_content`
    #[spec(
        requires: match *comp_type {
            CompType::Returner(result) => self.placed.contains_key(&AnyNode::ValueType(result)),
            CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain } => self.placed.contains_key(&AnyNode::ValueType(domain))
                            && self.placed.contains_key(&AnyNode::CompType(codomain)),
            CompType::Element { code, .. } => self.placed.contains_key(&AnyNode::Value(code)),
            CompType::With(left, right) => self.placed.contains_key(&AnyNode::CompType(left))
                            && self.placed.contains_key(&AnyNode::CompType(right)),
        },
        captures: entry_len = record.0.len(),
        ensures: record.0.get(entry_len) == Some(&u8::from(match *comp_type {
            CompType::Returner(..) => gandr_kernel_term::NODE_CT_RETURNER,
            CompType::Arrow { .. } => gandr_kernel_term::NODE_CT_ARROW,
            CompType::Pi { .. } => gandr_kernel_term::NODE_CT_PI,
            CompType::Element { .. } => gandr_kernel_term::NODE_CT_ELEMENT,
            CompType::With(..) => gandr_kernel_term::NODE_CT_WITH,
        }))
    )]
    fn put_comp_type(
        &self,
        record: &mut ContentEncoding,
        comp_type: &CompType,
    )
    {
        match *comp_type {
            CompType::Returner(result) => {
                record.put_tag(gandr_kernel_term::NODE_CT_RETURNER);
                record.put_content(self.content_of(AnyNode::ValueType(result)));
            },
            CompType::Arrow { domain, codomain } => {
                record.put_tag(gandr_kernel_term::NODE_CT_ARROW);
                record.put_content(self.content_of(AnyNode::ValueType(domain)));
                record.put_content(self.content_of(AnyNode::CompType(codomain)));
            },
            // The dependent arrow's record differs from the arrow's in its tag
            // alone, which is the whole reason the two are separate tags: the
            // children are the same two nodes and the scoping is what
            // distinguishes them, so a shared tag would collapse two types onto
            // one content id.
            CompType::Pi { domain, codomain } => {
                record.put_tag(gandr_kernel_term::NODE_CT_PI);
                record.put_content(self.content_of(AnyNode::ValueType(domain)));
                record.put_content(self.content_of(AnyNode::CompType(codomain)));
            },
            CompType::Element { code, ref target } => {
                record.put_tag(gandr_kernel_term::NODE_CT_ELEMENT);
                put_level(record, target);
                record.put_content(self.content_of(AnyNode::Value(code)));
            },
            CompType::With(left, right) => {
                record.put_tag(gandr_kernel_term::NODE_CT_WITH);
                record.put_content(self.content_of(AnyNode::CompType(left)));
                record.put_content(self.content_of(AnyNode::CompType(right)));
            },
        }
    }
}

/// Push `node`'s children as open tasks, in the order the format writes them.
///
/// # Specification
/// - requires: nothing; an unreadable node pushes nothing.
/// - ensures: pushes one open task per child, in the order the format writes
///   them, so each child is placed before the parent's record is built.
/// - provides: the scheduling half of the numbering walk, which is what keeps
///   the record of a node a function of its children's ids.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L3 — the predicate checks the exact appended open-task
///   sequence for every readable former and no tasks for unreadable roots.
///   Shared depth-16 pairs and independently varied case children exercise zero
///   through three children and mixed families, not every graph.
/// - witness: `encoding::tests::one_table_records_each_distinct_node_once`
/// - witness: `encoding::tests::a_transposed_product_encodes_differently`
/// - witness: `session::tests::session_relations_replay_without_search`
/// - witness: `encoding::tests::each_case_child_changes_canonical_content`
/// - witness: `encoding::tests::an_unreadable_reference_still_encodes`
#[spec(captures: entry_len = tasks.len(), ensures: tasks.get(entry_len..).is_some_and(|added| {
    let opened = added.iter().map(|task| match *task { EncodeTask::Open(node) => Some(node), EncodeTask::Close(_) => None });
    match node {
        AnyNode::Value(id) => match arena.value(id) { Some(matched_native_node) => match *matched_native_node {
Value::Constructor { datatype, ref fields, .. } => opened.eq((core::iter::once(AnyNode::ValueType(datatype)).chain(fields.iter().copied().map(AnyNode::Value))).map(Some)),
Value::Record(ref fields) => opened.eq((fields.values().copied().map(AnyNode::Value)).map(Some)),
Value::ListNil | Value::Variable(_) | Value::Constant(_) | Value::Literal(_) => opened.eq((core::iter::empty()).map(Some)),
Value::Tuple(ref components) => opened.eq((components.iter().copied().map(AnyNode::Value)).map(Some)),
Value::SessionPath { path_type: classifier, payload_paths, .. } | Value::SessionFlow { flow_type: classifier, payload_paths, .. } => opened.eq(([AnyNode::ValueType(classifier), AnyNode::Value(payload_paths)].into_iter()).map(Some)),
Value::PathEquiv { path_type, forward, backward, .. } => opened.eq(([AnyNode::ValueType(path_type), AnyNode::Value(forward), AnyNode::Value(backward)].into_iter()).map(Some)),
Value::ListCons(a,b) | Value::PathProduct(a,b) | Value::FlowProduct(a,b) | Value::StaticApplication(a,b) | Value::Then { first: a, second: b, .. } => opened.eq(([AnyNode::Value(a), AnyNode::Value(b)].into_iter()).map(Some)),
Value::PathRefl(body) | Value::Univalence(body) | Value::Here { point: body, .. } | Value::Stay { point: body, .. } | Value::Injection(_,body) | Value::Lift {body,..} => opened.eq((core::iter::once(AnyNode::Value(body))).map(Some)),
Value::ForwardFlow { flow_type, translator, ref outputs, .. } => opened.eq(([AnyNode::ValueType(flow_type), AnyNode::Value(translator)].into_iter().chain(outputs.iter().copied().map(AnyNode::Value))).map(Some)),
Value::FunctionFlow { flow_type, domain, codomain } => opened.eq(([AnyNode::ValueType(flow_type), AnyNode::Value(domain), AnyNode::Value(codomain)].into_iter()).map(Some)),
Value::Higher { ref evidence, .. } => opened.eq((evidence.iter().copied().map(AnyNode::Value)).map(Some)),
Value::HigherEvaluation { ref components, .. } => opened.eq((components.iter().flat_map(|component| [component.left, component.right, component.evidence]).map(AnyNode::Value)).map(Some)),
Value::QuantifiedEvaluation { ref children, .. } => opened.eq((children.iter().copied().map(AnyNode::Value)).map(Some)),
Value::Thunk(body) | Value::Returned(body) => opened.eq((core::iter::once(AnyNode::Computation(body))).map(Some)),
Value::Quote(quoted) => opened.eq((core::iter::once(AnyNode::ValueType(quoted))).map(Some)),
Value::QuoteComputation(quoted) => opened.eq((core::iter::once(AnyNode::CompType(quoted))).map(Some)),
},
None => opened.eq((core::iter::empty()).map(Some)),
},
        AnyNode::Computation(id) => match arena.computation(id) {
            Some(&Computation::ListFold { element, result, list, on_nil, on_cons }) => opened.eq([AnyNode::ValueType(element), AnyNode::ValueType(result), AnyNode::Value(list), AnyNode::Computation(on_nil), AnyNode::Computation(on_cons)].into_iter().map(Some)),
            Some(&Computation::DataCase {scrutinee,motive,ref branches}) => opened.eq(([AnyNode::Value(scrutinee), AnyNode::CompType(motive)].into_iter().chain(branches.iter().copied().map(AnyNode::Computation))).map(Some)),
            Some(&Computation::SigmaSplit {scrutinee,motive,body}) => opened.eq(([AnyNode::Value(scrutinee), AnyNode::CompType(motive), AnyNode::Computation(body)].into_iter()).map(Some)),
            Some(&(Computation::RecordProjection(record,_) | Computation::TupleProjection(record,_))) => opened.eq((core::iter::once(AnyNode::Value(record))).map(Some)),
            None => opened.eq((core::iter::empty()).map(Some)),
            Some(&Computation::Transport(a,b)) => opened.eq(([AnyNode::Value(a),AnyNode::Value(b)].into_iter()).map(Some)),
            Some(&(Computation::PathTransport { motive, path, value } | Computation::Ride { motive, flow: path, value })) => opened.eq(([AnyNode::ValueType(motive), AnyNode::Value(path), AnyNode::Value(value)].into_iter()).map(Some)),
            Some(&(Computation::TelescopeTransport { motive, path, start, over, value } | Computation::TelescopeRide { motive, flow: path, start, over, value })) => opened.eq(([AnyNode::CompType(motive), AnyNode::Value(path), AnyNode::Value(start), AnyNode::Value(over), AnyNode::Value(value)].into_iter()).map(Some)),
            Some(&Computation::RelatedApplication { path, left, right, evidence, body }) => opened.eq(([AnyNode::Value(path), AnyNode::Value(left), AnyNode::Value(right), AnyNode::Value(evidence), AnyNode::Computation(body)].into_iter()).map(Some)),
            Some(&Computation::Lambda(body) | &Computation::Fixpoint { body, .. }) => opened.eq((core::iter::once(AnyNode::Computation(body))).map(Some)),
            Some(&Computation::Application(head,argument)) => opened.eq(([AnyNode::Computation(head),AnyNode::Value(argument)].into_iter()).map(Some)),
            Some(&Computation::Return(value) | &Computation::Force(value)) => opened.eq((core::iter::once(AnyNode::Value(value))).map(Some)),
            Some(&(Computation::Bind(bound,body) | Computation::With(bound,body))) => opened.eq(([AnyNode::Computation(bound),AnyNode::Computation(body)].into_iter()).map(Some)),
            Some(&Computation::Project(_,pair)) => opened.eq((core::iter::once(AnyNode::Computation(pair))).map(Some)),
            Some(&Computation::Case {scrutinee,ref branches}) => opened.eq((core::iter::once(AnyNode::Value(scrutinee)).chain(branches.iter().copied().map(AnyNode::Computation))).map(Some)),
        },
        AnyNode::ValueType(id) => match arena.value_type(id) { Some(matched_native_node) => match *matched_native_node {
ValueType::Data {ref arguments,..} => opened.eq((arguments.iter().copied().map(AnyNode::Value)).map(Some)),
ValueType::Record(ref fields) => opened.eq((fields.values().copied().map(AnyNode::ValueType)).map(Some)),
ValueType::Base(_) | ValueType::Universe {..} | ValueType::Abstract(_) => opened.eq((core::iter::empty()).map(Some)),
ValueType::Session {payloads: inner,..} | ValueType::List(inner) | ValueType::Lift {inner,..} | ValueType::Staged {base: inner,..} => opened.eq((core::iter::once(AnyNode::ValueType(inner))).map(Some)),
ValueType::PathUniverse(a,b) | ValueType::FlowUniverse(a,b) => opened.eq(([AnyNode::Value(a), AnyNode::Value(b)].into_iter()).map(Some)),
ValueType::Path { domain, left, right } | ValueType::Flow { domain, source: left, target: right } | ValueType::Bridge { domain, left, right } => opened.eq(([AnyNode::ValueType(domain), AnyNode::Value(left), AnyNode::Value(right)].into_iter()).map(Some)),
ValueType::Product(ref parts) | ValueType::Sum(ref parts) => opened.eq((parts.iter().copied().map(AnyNode::ValueType)).map(Some)),
ValueType::StaticPi {domain:a,codomain:b} | ValueType::Sigma {first:a,second:b} => opened.eq(([AnyNode::ValueType(a),AnyNode::ValueType(b)].into_iter()).map(Some)),
ValueType::Thunk(body) => opened.eq((core::iter::once(AnyNode::CompType(body))).map(Some)),
ValueType::Element {code,..} => opened.eq((core::iter::once(AnyNode::Value(code))).map(Some)),
},
None => opened.eq((core::iter::empty()).map(Some)),
},
        AnyNode::CompType(id) => match arena.comp_type(id) {
            None => opened.eq((core::iter::empty()).map(Some)),
            Some(&CompType::Returner(result)) => opened.eq((core::iter::once(AnyNode::ValueType(result))).map(Some)),
            Some(&CompType::Arrow{domain,codomain} | &CompType::Pi {domain,codomain}) => opened.eq(([AnyNode::ValueType(domain),AnyNode::CompType(codomain)].into_iter()).map(Some)),
            Some(&CompType::Element {code,..}) => opened.eq((core::iter::once(AnyNode::Value(code))).map(Some)),
            Some(&CompType::With(left,right)) => opened.eq(([AnyNode::CompType(left),AnyNode::CompType(right)].into_iter()).map(Some)),
        },
    }
}))]
fn push_children(
    arena: &TermArena,
    node: AnyNode,
    tasks: &mut Vec<EncodeTask>,
)
{
    match node {
        AnyNode::Value(id) => match arena.value(id) {
            Some(&Value::Constructor {
                datatype,
                ref fields,
                ..
            }) => tasks.extend(
                (core::iter::once(AnyNode::ValueType(datatype))
                    .chain(fields.iter().copied().map(AnyNode::Value)))
                .map(EncodeTask::Open),
            ),
            Some(&Value::Record(ref fields)) => {
                tasks.extend((fields.values().copied().map(AnyNode::Value)).map(EncodeTask::Open));
            },
            None
            | Some(
                &Value::ListNil | &Value::Variable(_) | &Value::Constant(_) | &Value::Literal(_),
            ) => {},
            Some(&Value::Tuple(ref components)) => {
                tasks.extend(
                    components
                        .iter()
                        .copied()
                        .map(AnyNode::Value)
                        .map(EncodeTask::Open),
                );
            },
            Some(&Value::PathEquiv {
                path_type,
                forward,
                backward,
                ..
            }) => {
                tasks.push(EncodeTask::Open(AnyNode::ValueType(path_type)));
                tasks.push(EncodeTask::Open(AnyNode::Value(forward)));
                tasks.push(EncodeTask::Open(AnyNode::Value(backward)));
            },
            Some(
                &Value::SessionPath {
                    path_type,
                    payload_paths,
                    ..
                }
                | &Value::SessionFlow {
                    flow_type: path_type,
                    payload_paths,
                    ..
                },
            ) => {
                tasks.push(EncodeTask::Open(AnyNode::ValueType(path_type)));
                tasks.push(EncodeTask::Open(AnyNode::Value(payload_paths)));
            },
            Some(
                &Value::PathRefl(code)
                | &Value::Univalence(code)
                | &Value::Here { point: code, .. }
                | &Value::Stay { point: code, .. },
            ) => {
                tasks.push(EncodeTask::Open(AnyNode::Value(code)));
            },
            Some(
                &Value::Higher {
                    evidence: ref values,
                    ..
                }
                | &Value::QuantifiedEvaluation {
                    children: ref values,
                    ..
                },
            ) => {
                tasks.extend(
                    values
                        .iter()
                        .copied()
                        .map(AnyNode::Value)
                        .map(EncodeTask::Open),
                );
            },
            Some(&Value::HigherEvaluation { ref components, .. }) => tasks.extend(
                components
                    .iter()
                    .flat_map(|component| [component.left, component.right, component.evidence])
                    .map(AnyNode::Value)
                    .map(EncodeTask::Open),
            ),
            Some(&Value::ForwardFlow {
                flow_type,
                translator,
                ref outputs,
                ..
            }) => {
                tasks.push(EncodeTask::Open(AnyNode::ValueType(flow_type)));
                tasks.push(EncodeTask::Open(AnyNode::Value(translator)));
                tasks.extend(
                    outputs
                        .iter()
                        .copied()
                        .map(AnyNode::Value)
                        .map(EncodeTask::Open),
                );
            },
            Some(&Value::FunctionFlow {
                flow_type,
                domain,
                codomain,
            }) => {
                tasks.push(EncodeTask::Open(AnyNode::ValueType(flow_type)));
                tasks.push(EncodeTask::Open(AnyNode::Value(domain)));
                tasks.push(EncodeTask::Open(AnyNode::Value(codomain)));
            },
            Some(
                &Value::PathProduct(first, second)
                | &Value::FlowProduct(first, second)
                | &Value::ListCons(first, second)
                | &Value::StaticApplication(first, second)
                | &Value::Then { first, second, .. },
            ) => {
                tasks.push(EncodeTask::Open(AnyNode::Value(first)));
                tasks.push(EncodeTask::Open(AnyNode::Value(second)));
            },
            Some(&Value::Injection(_, body) | &Value::Lift { body, .. }) => {
                tasks.push(EncodeTask::Open(AnyNode::Value(body)));
            },
            Some(&(Value::Thunk(body) | Value::Returned(body))) => {
                tasks.push(EncodeTask::Open(AnyNode::Computation(body)));
            },
            Some(&Value::Quote(quoted)) => {
                tasks.push(EncodeTask::Open(AnyNode::ValueType(quoted)));
            },
            Some(&Value::QuoteComputation(quoted)) => {
                tasks.push(EncodeTask::Open(AnyNode::CompType(quoted)));
            },
        },
        AnyNode::Computation(id) => match arena.computation(id) {
            Some(&Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
            }) => tasks.extend(
                ([AnyNode::Value(scrutinee), AnyNode::CompType(motive)]
                    .into_iter()
                    .chain(branches.iter().copied().map(AnyNode::Computation)))
                .map(EncodeTask::Open),
            ),
            Some(&Computation::SigmaSplit {
                scrutinee,
                motive,
                body,
            }) => tasks.extend(
                [
                    AnyNode::Value(scrutinee),
                    AnyNode::CompType(motive),
                    AnyNode::Computation(body),
                ]
                .map(EncodeTask::Open),
            ),
            Some(
                &(Computation::RecordProjection(record, _)
                | Computation::TupleProjection(record, _)),
            ) => {
                tasks.extend((core::iter::once(AnyNode::Value(record))).map(EncodeTask::Open));
            },
            None => {},
            Some(&Computation::ListFold {
                element,
                result,
                list,
                on_nil,
                on_cons,
            }) => {
                for child in [
                    AnyNode::ValueType(element),
                    AnyNode::ValueType(result),
                    AnyNode::Value(list),
                    AnyNode::Computation(on_nil),
                    AnyNode::Computation(on_cons),
                ] {
                    tasks.push(EncodeTask::Open(child));
                }
            },
            Some(&Computation::Transport(path, value)) => {
                tasks.push(EncodeTask::Open(AnyNode::Value(path)));
                tasks.push(EncodeTask::Open(AnyNode::Value(value)));
            },
            Some(
                &Computation::PathTransport {
                    motive,
                    path,
                    value,
                }
                | &Computation::Ride {
                    motive,
                    flow: path,
                    value,
                },
            ) => {
                tasks.push(EncodeTask::Open(AnyNode::ValueType(motive)));
                tasks.push(EncodeTask::Open(AnyNode::Value(path)));
                tasks.push(EncodeTask::Open(AnyNode::Value(value)));
            },
            Some(
                &Computation::TelescopeTransport {
                    motive,
                    path,
                    start,
                    over,
                    value,
                }
                | &Computation::TelescopeRide {
                    motive,
                    flow: path,
                    start,
                    over,
                    value,
                },
            ) => {
                for child in [
                    AnyNode::CompType(motive),
                    AnyNode::Value(path),
                    AnyNode::Value(start),
                    AnyNode::Value(over),
                    AnyNode::Value(value),
                ] {
                    tasks.push(EncodeTask::Open(child));
                }
            },
            Some(&Computation::RelatedApplication {
                path,
                left,
                right,
                evidence,
                body,
            }) => {
                for child in [
                    AnyNode::Value(path),
                    AnyNode::Value(left),
                    AnyNode::Value(right),
                    AnyNode::Value(evidence),
                    AnyNode::Computation(body),
                ] {
                    tasks.push(EncodeTask::Open(child));
                }
            },
            Some(&Computation::Lambda(body) | &Computation::Fixpoint { body, .. }) => {
                tasks.push(EncodeTask::Open(AnyNode::Computation(body)));
            },
            Some(&Computation::Application(head, argument)) => {
                tasks.push(EncodeTask::Open(AnyNode::Computation(head)));
                tasks.push(EncodeTask::Open(AnyNode::Value(argument)));
            },
            Some(&Computation::Return(value) | &Computation::Force(value)) => {
                tasks.push(EncodeTask::Open(AnyNode::Value(value)));
            },
            Some(&(Computation::Bind(bound, body) | Computation::With(bound, body))) => {
                tasks.push(EncodeTask::Open(AnyNode::Computation(bound)));
                tasks.push(EncodeTask::Open(AnyNode::Computation(body)));
            },
            Some(&Computation::Project(_, pair)) => {
                tasks.push(EncodeTask::Open(AnyNode::Computation(pair)));
            },
            Some(&Computation::Case {
                scrutinee,
                ref branches,
            }) => {
                tasks.push(EncodeTask::Open(AnyNode::Value(scrutinee)));
                tasks.extend(
                    branches
                        .iter()
                        .copied()
                        .map(AnyNode::Computation)
                        .map(EncodeTask::Open),
                );
            },
        },
        AnyNode::ValueType(id) => match arena.value_type(id) {
            Some(&ValueType::Data { ref arguments, .. }) => {
                tasks.extend((arguments.iter().copied().map(AnyNode::Value)).map(EncodeTask::Open));
            },
            Some(&ValueType::Record(ref fields)) => tasks
                .extend((fields.values().copied().map(AnyNode::ValueType)).map(EncodeTask::Open)),
            None
            | Some(&ValueType::Base(_) | &ValueType::Universe { .. } | &ValueType::Abstract(_)) => {
            },
            Some(&ValueType::Product(ref parts) | &ValueType::Sum(ref parts)) => {
                tasks.extend(
                    parts
                        .iter()
                        .copied()
                        .map(AnyNode::ValueType)
                        .map(EncodeTask::Open),
                );
            },
            Some(
                &ValueType::StaticPi {
                    domain: first,
                    codomain: second,
                }
                | &ValueType::Sigma { first, second },
            ) => {
                tasks.push(EncodeTask::Open(AnyNode::ValueType(first)));
                tasks.push(EncodeTask::Open(AnyNode::ValueType(second)));
            },
            Some(
                &ValueType::PathUniverse(source, target) | &ValueType::FlowUniverse(source, target),
            ) => {
                tasks.push(EncodeTask::Open(AnyNode::Value(source)));
                tasks.push(EncodeTask::Open(AnyNode::Value(target)));
            },
            Some(
                &ValueType::Path {
                    domain,
                    left,
                    right,
                }
                | &ValueType::Flow {
                    domain,
                    source: left,
                    target: right,
                }
                | &ValueType::Bridge {
                    domain,
                    left,
                    right,
                },
            ) => {
                tasks.push(EncodeTask::Open(AnyNode::ValueType(domain)));
                tasks.push(EncodeTask::Open(AnyNode::Value(left)));
                tasks.push(EncodeTask::Open(AnyNode::Value(right)));
            },
            Some(&ValueType::Thunk(body)) => {
                tasks.push(EncodeTask::Open(AnyNode::CompType(body)));
            },
            Some(
                &ValueType::Session {
                    payloads: inner, ..
                }
                | &ValueType::Lift { inner, .. }
                | &ValueType::List(inner)
                | &ValueType::Staged { base: inner, .. },
            ) => {
                tasks.push(EncodeTask::Open(AnyNode::ValueType(inner)));
            },
            Some(&ValueType::Element { code, .. }) => {
                tasks.push(EncodeTask::Open(AnyNode::Value(code)));
            },
        },
        AnyNode::CompType(id) => match arena.comp_type(id) {
            None => {},
            Some(&CompType::Returner(result)) => {
                tasks.push(EncodeTask::Open(AnyNode::ValueType(result)));
            },
            Some(&CompType::Arrow { domain, codomain } | &CompType::Pi { domain, codomain }) => {
                tasks.push(EncodeTask::Open(AnyNode::ValueType(domain)));
                tasks.push(EncodeTask::Open(AnyNode::CompType(codomain)));
            },
            Some(&CompType::Element { code, .. }) => {
                tasks.push(EncodeTask::Open(AnyNode::Value(code)));
            },
            Some(&CompType::With(left, right)) => {
                tasks.push(EncodeTask::Open(AnyNode::CompType(left)));
                tasks.push(EncodeTask::Open(AnyNode::CompType(right)));
            },
        },
    }
}

/// Write the reserved record of a reference that resolved to nothing.
///
/// # Specification
/// trivial.
#[inline]
fn put_dangling(
    record: &mut ContentEncoding,
    family: DanglingFamily,
)
{
    record.put_tag(record_dangling());
    record.put_tag(family.tag());
}

/// The format's tag for a base-type atom.
///
/// # Specification
/// trivial.
#[inline]
const fn base_tag(base: BaseType) -> WireTag
{
    match base {
        BaseType::Integer => gandr_kernel_term::BASE_INTEGER,
        BaseType::String => gandr_kernel_term::BASE_STRING,
        BaseType::Numeric => gandr_kernel_term::BASE_NUMERIC,
    }
}

/// The format's tag for a literal's sign.
///
/// The sign is written even for a zero magnitude. That costs nothing and states
/// the obligation the term crate discharges upstream: a negative zero is pinned
/// non-negative before it can be encoded, so two spellings of one number cannot
/// produce two ids.
///
/// # Specification
/// trivial.
#[inline]
const fn sign_tag(sign: Sign) -> WireTag
{
    match sign {
        Sign::NonNegative => gandr_kernel_term::SIGN_NON_NEGATIVE,
        Sign::Negative => gandr_kernel_term::SIGN_NEGATIVE,
    }
}

/// Write a literal's canonical payload, every text component length-prefixed.
///
/// # Specification
/// - requires: `literal` is in the canonical form the term crate admits, a
///   non-negative zero included.
/// - ensures: writes the literal's kind tag, then its sign where it has one,
///   then each text component length-prefixed, so two literals whose components
///   merely concatenate alike take different images.
/// - provides: the literal payload of a value record, which is where two
///   spellings of one number would otherwise become two content ids.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L3 — canonical literals enter. Kind, sign and final text
///   payload are executable; zero/one sign pairs and the numeric split pair
///   separate sign loss and ambiguous component framing, not every literal.
/// - witness: `encoding::tests::signed_zeroes_collapse_and_signed_ones_do_not`
/// - witness: `encoding::tests::the_length_prefix_separates_a_split_pair`
#[spec(
    captures: entry_len = record.0.len(),
    ensures: match *literal {
        Literal::Integer(ref integer) => record.0.get(entry_len) == Some(&u8::from(gandr_kernel_term::LITERAL_INTEGER))
            && record.0.get(entry_len.saturating_add(1)) == Some(&u8::from(sign_tag(integer.sign())))
            && record.0.ends_with(integer.magnitude().as_ref().as_bytes()),
        Literal::Text(ref text) => record.0.get(entry_len) == Some(&u8::from(gandr_kernel_term::LITERAL_TEXT))
            && record.0.ends_with(text.as_ref().as_bytes()),
        Literal::Numeric(ref numeric) => record.0.get(entry_len) == Some(&u8::from(gandr_kernel_term::LITERAL_NUMERIC))
            && record.0.get(entry_len.saturating_add(1)) == Some(&u8::from(sign_tag(numeric.sign())))
            && record.0.ends_with(numeric.fraction().as_ref().as_bytes()),
    }
)]
fn put_literal(
    record: &mut ContentEncoding,
    literal: &Literal,
)
{
    match *literal {
        Literal::Integer(ref integer) => {
            record.put_tag(gandr_kernel_term::LITERAL_INTEGER);
            record.put_tag(sign_tag(integer.sign()));
            record.put_text(EncodedText(integer.magnitude().as_ref()));
        },
        Literal::Text(ref text) => {
            record.put_tag(gandr_kernel_term::LITERAL_TEXT);
            record.put_text(EncodedText(text.as_ref()));
        },
        Literal::Numeric(ref numeric) => {
            record.put_tag(gandr_kernel_term::LITERAL_NUMERIC);
            record.put_tag(sign_tag(numeric.sign()));
            record.put_text(EncodedText(numeric.integer_part().as_ref()));
            record.put_text(EncodedText(numeric.fraction().as_ref()));
        },
    }
}

/// Write a canonical level: its constant part, then its atoms in canonical
/// order, each a variable and an offset.
///
/// The level type is always in canonical form, so its atom order is a function
/// of the level rather than of how it was built.
///
/// # Specification
/// - requires: `level` is in canonical form, which the level type maintains.
/// - ensures: writes the constant part, then the atom count, then each atom's
///   variable index and offset in the level's own canonical order — so the
///   image is a function of the level rather than of how it was built.
/// - provides: the level payload of every record that carries one.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L3 — canonical levels enter. The predicate fixes the
///   constant, atom count, indices and offsets as a byte sequence without
///   collecting atoms. Empty/constant and two-atom fixtures vary each component
///   and reverse construction order; they do not enumerate the level algebra.
/// - witness: `encoding::tests::level_frames_are_canonical_and_include_each_component`
#[spec(
    captures: entry_len = record.0.len(),
    ensures: {
        let words = core::iter::once(u64::from(level.constant_part()))
            .chain(core::iter::once(u64::try_from(level.atoms().count()).unwrap_or(u64::MAX)))
            .chain(level.atoms().flat_map(|(variable, offset)|
                [u64::from(u32::from(variable.index())), u64::from(offset)]));
        let expected = words.flat_map(|word| {
    let groups = u64::BITS.saturating_sub(word.leading_zeros()).max(1).div_ceil(7);
    (0 .. groups).map(move |group| {
        let remaining = word.checked_shr(group.saturating_mul(7)).unwrap_or(0);
        let low = u8::try_from(remaining & 0x7f).unwrap_or(0);
        low | if group.saturating_add(1) < groups { 0x80 } else { 0 }
    })
});
        record.0.get(entry_len..).is_some_and(|image| image.iter().copied().eq(expected))
    }
)]
fn put_level(
    record: &mut ContentEncoding,
    level: &Level,
)
{
    record.put_word(EncodedWord(u64::from(level.constant_part())));
    let atoms: Vec<(LevelVar, LevelOffset)> = level.atoms().collect();
    record.put_count(ComponentCount(atoms.len()));
    for (variable, offset) in atoms {
        record.put_word(EncodedWord(u64::from(u32::from(variable.index()))));
        record.put_word(EncodedWord(u64::from(offset)));
    }
}

/// Which question one goal expansion asks, in the vocabulary the memo key is
/// derived from.
///
/// The variants are the two machines' goals: the checker's four directions over
/// terms, and the type-formation walk's two over types.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SupportGoal
{
    /// Synthesize a value's type.
    SynthValue(
        /// The value node.
        ValueId,
    ),
    /// Check a value against an expected value type.
    CheckValue(
        /// The value node.
        ValueId,
        /// The expected type.
        ValueTypeId,
    ),
    /// Synthesize a computation's type.
    SynthComp(
        /// The computation node.
        ComputationId,
    ),
    /// Check a computation against an expected computation type.
    CheckComp(
        /// The computation node.
        ComputationId,
        /// The expected type.
        CompTypeId,
    ),
    /// Form a value type and read off its universe level.
    ValueTypeLevel(
        /// The value-type node.
        ValueTypeId,
    ),
    /// Form a computation type and read off its universe level.
    CompTypeLevel(
        /// The computation-type node.
        CompTypeId,
    ),
}

quenchant_shape::reason_enum! {
    /// Why a support goal carries no expected type.
    mod expected_type {
        /// The goal derives an answer rather than checking against a supplied type.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// A synthesis goal has no supplied expected type.
            Synthesis,
            /// A formation goal asks for a universe level.
            Formation,
        }
    }
}

impl SupportGoal
{
    /// The direction tag this goal writes into a support's encoding.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn direction(self) -> WireTag
    {
        match self {
            Self::SynthValue(_) => WireTag::from(0x00_u8),
            Self::CheckValue(..) => WireTag::from(0x01_u8),
            Self::SynthComp(_) => WireTag::from(0x02_u8),
            Self::CheckComp(..) => WireTag::from(0x03_u8),
            Self::ValueTypeLevel(_) => WireTag::from(0x04_u8),
            Self::CompTypeLevel(_) => WireTag::from(0x05_u8),
        }
    }

    /// The obligation node this goal is about.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn subject(self) -> AnyNode
    {
        match self {
            Self::SynthValue(id) | Self::CheckValue(id, _) => AnyNode::Value(id),
            Self::SynthComp(id) | Self::CheckComp(id, _) => AnyNode::Computation(id),
            Self::ValueTypeLevel(id) => AnyNode::ValueType(id),
            Self::CompTypeLevel(id) => AnyNode::CompType(id),
        }
    }

    /// The expected type this goal checks against, if it checks at all.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: checking retains the supplied type and its family; synthesis
    ///   and formation return their respective absence reasons.
    /// - provides: the checked type, or [`Absent`] with `Synthesis` for a
    ///   synthesis goal and `Formation` for a universe-formation goal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — the const predicate fixes family and absence
    ///   reason for all six goal variants. Checking-key pairs vary the expected
    ///   type in both families; synthesis/checking and formation fixtures
    ///   exercise presence without claiming exhaustive content equality.
    /// - witness: `encoding::tests::the_direction_is_part_of_the_key`
    /// - witness: `encoding::tests::expected_type_content_changes_checking_keys`
    /// - witness: `encoding::tests::computation_type_formers_keep_distinct_content`
    ///
    /// [`Absent`]: expected_type::Absent
    #[inline]
    #[spec(ensures: |ret| matches!((self, ret),
        (Self::CheckValue(..), Maybe::Present(AnyNode::ValueType(_)))
        | (Self::CheckComp(..), Maybe::Present(AnyNode::CompType(_)))
        | (Self::SynthValue(_) | Self::SynthComp(_), Maybe::Absent(expected_type::Absent::Synthesis))
        | (Self::ValueTypeLevel(_) | Self::CompTypeLevel(_), Maybe::Absent(expected_type::Absent::Formation))))]
    const fn expected(self) -> Maybe<AnyNode, expected_type::Absent>
    {
        match self {
            Self::CheckValue(_, expected) => Maybe::Present(AnyNode::ValueType(expected)),
            Self::CheckComp(_, expected) => Maybe::Present(AnyNode::CompType(expected)),
            Self::SynthValue(_) | Self::SynthComp(_) => {
                Maybe::Absent(expected_type::Absent::Synthesis)
            },
            Self::ValueTypeLevel(_) | Self::CompTypeLevel(_) => {
                Maybe::Absent(expected_type::Absent::Formation)
            },
        }
    }
}

/// The binders a support folds in.
#[derive(Clone, Copy, Debug)]
pub enum Telescope<'context>
{
    /// The binders the goal reads: each read index beside the type of the
    /// binder it names, the indices ascending.
    Read(&'context [(DeBruijnIndex, ValueTypeId)]),
    /// Every binder of the context, outermost first: the goal's reads are not
    /// known, or one names no binder of the context.
    Whole(&'context [ValueTypeId]),
}

impl Telescope<'_>
{
    /// The binder types the telescope folds in.
    ///
    /// # Specification
    /// trivial.
    fn types(self) -> Vec<ValueTypeId>
    {
        match self {
            Self::Read(read) => read.iter().map(|&(_, entry)| entry).collect(),
            Self::Whole(context) => context.to_vec(),
        }
    }
}

/// Name one goal's whole support: the goal record of its direction, its
/// obligation's content, its expected type's content and its binders.
///
/// The key is a name in the session's merged graph, built from its members'
/// names: a goal names its subject, its expected type and its cover; a cover
/// names its pairs; a pair names a type. Each record is interned once, so a
/// type, a pair or a cover recurring under many goals is built once and shared
/// by every goal that reads it, and two goals take one name exactly when every
/// member agrees, down to the leaves.
///
/// # Specification
/// - requires: `table` is this checking session's; a [`Telescope::Read`] holds
///   every binder the goal's node reads, ascending by index, and a
///   [`Telescope::Whole`] the whole context, outermost first. A whole context
///   in place of the reads is admissible and can only split a support, never
///   merge two.
/// - ensures: two goals take one id exactly when they ask the same direction of
///   subjects of equal content, against expected types of equal content,
///   reading the same positions and finding types of equal content there — or
///   under whole contexts of equal content. No arena id, allocation order or
///   binder the node does not read reaches the id.
/// - provides: the memo key. The predicate checks that every component was
///   placed; equality across goals has the finite witnesses below rather than
///   another content walk.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L2/L3 — one append-only session and the supplied telescope
///   bound the domain. Component placement is executable. Finite trap pairs
///   separate field order, family, sign normalization and text framing; other
///   pairs vary the direction, expected types, the read positions and telescope
///   order, re-mint equal content, and ask one question twice. They do not
///   enumerate every support graph.
/// - witness: `encoding::tests::a_transposed_product_encodes_differently`
/// - witness: `encoding::tests::two_families_with_one_payload_encode_differently`
/// - witness: `encoding::tests::signed_zeroes_collapse_and_signed_ones_do_not`
/// - witness: `encoding::tests::the_length_prefix_separates_a_split_pair`
/// - witness: `encoding::tests::the_direction_is_part_of_the_key`
/// - witness: `encoding::tests::the_telescope_is_folded_in_order`
/// - witness: `encoding::tests::the_read_positions_are_part_of_the_key`
/// - witness: `encoding::tests::structurally_equal_nodes_encode_alike`
/// - witness: `encoding::tests::an_unreadable_reference_still_encodes`
/// - witness: `encoding::tests::expected_type_content_changes_checking_keys`
/// - witness: `encoding::tests::one_key_record_per_distinct_question`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.0 < table.records
    && table.placed.contains_key(&goal.subject())
    && match goal.expected() {
        Maybe::Present(node) => table.placed.contains_key(&node),
        Maybe::Absent(_) => true,
    }
    && telescope.types().iter().all(|&entry| table.placed.contains_key(&AnyNode::ValueType(entry))))]
pub fn support_key(
    table: &mut ContentTable,
    arena: &TermArena,
    goal: SupportGoal,
    telescope: Telescope<'_>,
) -> ContentId
{
    let subject = table.place(arena, goal.subject());
    let expected = goal.expected().map(|node| table.place(arena, node));
    let binders = match telescope {
        Telescope::Read(read) => table.cover(arena, read),
        Telescope::Whole(context) => table.context(arena, context),
    };
    let record = &mut table.scratch;
    record.0.clear();
    record.put_tag(KeyRecord::Goal.tag());
    record.put_tag(goal.direction());
    record.put_content(subject);
    match expected {
        Maybe::Present(id) => {
            record.put_tag(component_present());
            record.put_content(id);
        },
        Maybe::Absent(expected_type::Absent::Synthesis | expected_type::Absent::Formation) => {
            record.put_tag(component_absent());
        },
    }
    record.put_content(binders);
    table.intern_scratch()
}

/// One rewrite obligation, as the key derivation names it.
///
/// A rewrite's answer depends on the node's content, on how many binders the
/// walk has crossed to reach it, and on the rewrite's own parameter — the shift
/// amount, or the replacement value's content. Nothing else: the arena the walk
/// mints into is append-only for the session's whole life, so no allocation
/// order reaches the key.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RewriteGoal
{
    /// Raise every free index at or above the cutoff by the amount.
    Shift
    {
        /// The node being rewritten.
        subject: AnyNode,
        /// The binder depth the walk has reached, which the cutoff is measured
        /// from.
        depth: BinderDepth,
        /// The base cutoff: indices below it are bound outside the rewrite.
        cutoff: BinderDepth,
        /// The amount every free index at or above the cutoff rises by.
        amount: BinderDepth,
    },
    /// Replace the innermost binder's variable by a value and lower everything
    /// outside it by one.
    Substitute
    {
        /// The node being rewritten.
        subject: AnyNode,
        /// The binder depth the walk has reached, which names the index the
        /// replacement stands for.
        depth: BinderDepth,
        /// The replacement value, in the context outside the binder.
        replacement: ValueId,
    },
    /// Replace every occurrence of a constant by the variable at a fixed index
    /// counted from the root, raised under every binder crossed.
    Abstract
    {
        /// The node being rewritten.
        subject: AnyNode,
        /// The binder depth the walk has reached, which the index rises by.
        depth: BinderDepth,
        /// The constant replaced.
        constant: gandr_kernel_term::ConstantIndex,
        /// The variable it reads as at the root.
        index: gandr_kernel_term::DeBruijnIndex,
    },
}

impl RewriteGoal
{
    /// The direction tag this goal writes into its encoding.
    ///
    /// Drawn from the same byte alphabet as [`SupportGoal::direction`] and
    /// disjoint from it. The two key types index two different memos and could
    /// not collide through the type system alone, so the disjointness is
    /// defence in depth against a later merge of the two vocabularies.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn direction(self) -> WireTag
    {
        match self {
            Self::Shift { .. } => WireTag::from(0x06_u8),
            Self::Substitute { .. } => WireTag::from(0x07_u8),
            Self::Abstract { .. } => WireTag::from(0x08_u8),
        }
    }

    /// The node this goal rewrites.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn subject(self) -> AnyNode
    {
        match self {
            Self::Shift { subject, .. }
            | Self::Substitute { subject, .. }
            | Self::Abstract { subject, .. } => subject,
        }
    }
}

/// Encode one rewrite obligation's whole key: the direction, the subject's
/// content, the binder depth, and the rewrite's own parameter.
///
/// # Specification
/// - requires: `table` is this session's, and `arena` is the one it has been
///   used with.
/// - ensures: a byte string that is a function of content and binder depth
///   alone. Two rewrite goals encode alike exactly when they rewrite the same
///   content the same way, so an entry can only answer for a goal that would
///   have produced it.
/// - provides: the rewrite memo's key. Direction and required placements are
///   executable; session provenance and equality across rewrite content and
///   binder parameters are exercised by the bounded witness below.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L3 — one append-only session supplies the subject and any
///   replacement. Direction and placements are executable. Shifts at depths 0/1
///   and amounts 1/2, a substitution, and a re-minted subject separate lost key
///   components without exhausting rewrite semantics.
/// - witness: `encoding::tests::a_rewrite_key_separates_on_each_component`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.0.first() == Some(&u8::from(goal.direction()))
    && table.placed.contains_key(&goal.subject())
    && match goal {
        RewriteGoal::Shift { .. } | RewriteGoal::Abstract { .. } => true,
        RewriteGoal::Substitute { replacement, .. } => table.placed.contains_key(&AnyNode::Value(replacement)),
    })]
pub fn encode_rewrite(
    table: &mut ContentTable,
    arena: &TermArena,
    goal: RewriteGoal,
) -> ContentEncoding
{
    let subject = table.place(arena, goal.subject());
    let mut encoding = ContentEncoding::new();
    encoding.put_tag(goal.direction());
    encoding.put_content(subject);
    match goal {
        RewriteGoal::Shift {
            depth,
            cutoff,
            amount,
            ..
        } => {
            encoding.put_count(ComponentCount(usize::from(depth)));
            encoding.put_count(ComponentCount(usize::from(cutoff)));
            encoding.put_count(ComponentCount(usize::from(amount)));
        },
        RewriteGoal::Substitute {
            depth, replacement, ..
        } => {
            let replacement = table.place(arena, AnyNode::Value(replacement));
            encoding.put_count(ComponentCount(usize::from(depth)));
            encoding.put_content(replacement);
        },
        RewriteGoal::Abstract {
            depth,
            constant,
            index,
            ..
        } => {
            encoding.put_count(ComponentCount(usize::from(depth)));
            encoding.put_count(ComponentCount(usize::from(constant)));
            encoding.put_word(EncodedWord(u64::from(u32::from(index))));
        },
    }
    encoding
}

/// The absolute content digest of one node: the digest of the canonical record
/// stream of everything it reaches, built in a table of its own.
///
/// Session-independent on purpose. A refusal outlives the session that produced
/// it, so the type witness it carries has to identify a type by content and not
/// by a number some table happened to assign. Nothing decides on this digest —
/// it identifies a type in a diagnostic — so a collision costs a reader
/// precision and never costs a verdict.
///
/// # Specification
/// - requires: nothing — an unreadable node digests as the dangling record.
/// - ensures: equal reachable content produces equal digests, in any arena and
///   any session.
/// - provides: content identity for refusal witnesses. The predicate fixes the
///   digest of every family-specific dangling record without rebuilding the
///   graph. Cross-arena content equality remains a witnessed relational law.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L3 — any root, including an unreadable one, is admitted.
///   The exact dangling-stream digest is executable for all four families;
///   same-head distinct types and re-minted products separate lost content and
///   accidental arena dependence, not every possible hash collision.
/// - witness: `witness::tests::two_types_of_one_head_are_still_separated`
/// - witness: `encoding::tests::an_absolute_digest_ignores_arena_position`
/// - witness: `encoding::tests::an_unreadable_reference_still_encodes`
#[inline]
#[must_use]
#[spec(ensures: |ret| {
    let (readable, family) = match node { AnyNode::Value(id) => (arena.value(id).is_some(), 0_u8),
AnyNode::Computation(id) => (arena.computation(id).is_some(), 1_u8),
AnyNode::ValueType(id) => (arena.value_type(id).is_some(), 2_u8),
AnyNode::CompType(id) => (arena.comp_type(id).is_some(), 3_u8), };
    readable || {
        let fingerprint = [2_u8, DANGLING_TAG, family].iter()
            .fold(0x6c62_272e_07bb_0142_62b8_2175_6295_c58d_u128,
                |state, &byte| (state ^ u128::from(byte))
                    .wrapping_mul(0x0000_0000_0100_0000_0000_0000_0000_013b_u128));
        ret == ContentDigest::new(
            DigestWord::from(u64::try_from(fingerprint >> 64_u32).unwrap_or(u64::MAX)),
            DigestWord::from(u64::try_from(fingerprint & u128::from(u64::MAX)).unwrap_or(u64::MAX)))
    }
})]
pub fn content_digest(
    arena: &TermArena,
    node: AnyNode,
) -> ContentDigest
{
    let mut table = ContentTable::new();
    let _placed = table.place(arena, node);
    table.stream().digest()
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec;

    use anodized::spec;
    use gandr_kernel_term::AnyNode;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::FractionDigits;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::NumericLiteral;
    use gandr_kernel_term::Sign;
    use gandr_kernel_term::StringLiteral;
    use gandr_kernel_term::TermArena;

    use super::BinderDepth;
    use super::ContentEncoding;
    use super::ContentTable;
    use super::EncodedWord;
    use super::RewriteGoal;
    use super::SupportGoal;
    use super::Telescope;
    use super::content_digest;
    use super::encode_rewrite;
    use super::support_key;

    /// A magnitude from digit text, for a literal fixture.
    ///
    /// # Specification
    /// - requires: `digits` is nonempty ASCII decimal text.
    /// - ensures: the magnitude those digits denote.
    /// - provides: the literal fixtures the encoding cases are built from.
    /// - fails: never.
    /// - panics: when `digits` is not decimal text.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — the input grammar is executable. Zero/one and
    ///   numeric split-pair fixtures exercise valid decimal magnitudes, not
    ///   every decimal string or the rejected-input panic path.
    /// - witness: `encoding::tests::signed_zeroes_collapse_and_signed_ones_do_not`
    /// - witness: `encoding::tests::the_length_prefix_separates_a_split_pair`
    #[spec(requires: !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()))]
    fn magnitude(digits: String) -> Magnitude
    {
        Magnitude::from_decimal_text(digits).expect("the fixture digits are decimal")
    }

    /// A fractional-digit sequence, for a numeric literal fixture.
    ///
    /// # Specification
    /// - requires: `digits` contains only ASCII decimal digits; empty is valid.
    /// - ensures: the fractional-digit sequence those digits denote.
    /// - provides: the numeric-literal fixtures the encoding cases are built
    ///   from.
    /// - fails: never.
    /// - panics: when `digits` is not decimal text.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — ASCII decimal text, including empty, is the
    ///   domain. The grammar is executable; the fractional parts 23 and 3
    ///   participate in the framed numeric ambiguity pair, not an exhaustive
    ///   parser corpus.
    /// - witness: `encoding::tests::the_length_prefix_separates_a_split_pair`
    #[spec(requires: digits.bytes().all(|byte| byte.is_ascii_digit()))]
    fn fraction(digits: String) -> FractionDigits
    {
        FractionDigits::from_decimal_text(digits).expect("the fixture digits are decimal")
    }

    /// A text literal fixture.
    ///
    /// # Specification
    /// trivial.
    fn text(content: String) -> Literal
    {
        Literal::Text(StringLiteral::new(content))
    }

    #[test]
    fn varint_images_are_minimal_at_the_boundaries()
    {
        let image_of = |value: u64| {
            let mut out = ContentEncoding::new();
            out.put_word(EncodedWord(value));
            out.0
        };
        assert_eq!(vec![0x00_u8], image_of(0));
        assert_eq!(vec![0x7f_u8], image_of(127));
        assert_eq!(vec![0x80_u8, 0x01], image_of(128));
        assert_eq!(
            vec![
                0xff_u8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01
            ],
            image_of(u64::MAX)
        );
    }

    #[test]
    fn text_frames_count_bytes_and_preserve_component_boundaries()
    {
        let cases = [
            (String::new(), vec![0x00]),
            (String::from("\u{e9}\0"), vec![0x03]),
            ("x".repeat(127), vec![0x7f]),
            ("x".repeat(128), vec![0x80, 0x01]),
        ];
        for (text, prefix) in cases {
            let mut encoded = ContentEncoding(vec![0x7e]);
            encoded.put_text(super::EncodedText(&text));
            let mut expected = vec![0x7e];
            expected.extend_from_slice(&prefix);
            expected.extend_from_slice(text.as_bytes());
            assert_eq!(encoded.0, expected);
        }
        let mut split_one = ContentEncoding::new();
        split_one.put_text(super::EncodedText("a"));
        split_one.put_text(super::EncodedText("bc"));
        let mut split_two = ContentEncoding::new();
        split_two.put_text(super::EncodedText("ab"));
        split_two.put_text(super::EncodedText("c"));
        assert_ne!(split_one, split_two);
    }

    #[test]
    fn record_frames_preserve_binary_payloads_at_the_group_boundary()
    {
        let cases = [
            (vec![], vec![0x00]),
            (vec![0xff, 0x00], vec![0x02]),
            (vec![0xff; 128], vec![0x80, 0x01]),
        ];
        for (bytes, prefix) in cases {
            let record = ContentEncoding(bytes);
            let mut encoded = ContentEncoding(vec![0x7e]);
            encoded.put_record(&record);
            let mut expected = vec![0x7e];
            expected.extend_from_slice(&prefix);
            expected.extend_from_slice(&record.0);
            assert_eq!(encoded.0, expected);
        }
    }

    #[test]
    fn the_digest_separates_a_one_byte_difference()
    {
        let mut first = ContentEncoding::new();
        first.put_word(EncodedWord(1));
        let mut second = ContentEncoding::new();
        second.put_word(EncodedWord(2));
        assert_ne!(
            first.digest(),
            second.digest(),
            "a one-byte difference moves the digest, so the fast path prunes"
        );
        assert_eq!(
            ContentEncoding::new().digest(),
            gandr_kernel_check_memo::ContentDigest::new(
                gandr_kernel_check_memo::DigestWord::from(0x6c62_272e_07bb_0142_u64),
                gandr_kernel_check_memo::DigestWord::from(0x62b8_2175_6295_c58d_u64)
            ),
        );
        assert_eq!(
            ContentEncoding(vec![0x61]).digest(),
            gandr_kernel_check_memo::ContentDigest::new(
                gandr_kernel_check_memo::DigestWord::from(0xd228_cb69_6f1a_8caf_u64),
                gandr_kernel_check_memo::DigestWord::from(0x7891_2b70_4e4a_8964_u64)
            ),
        );
    }

    #[test]
    fn the_digest_separates_a_transposition()
    {
        let mut forward = ContentEncoding::new();
        forward.put_word(EncodedWord(1));
        forward.put_word(EncodedWord(2));
        let mut backward = ContentEncoding::new();
        backward.put_word(EncodedWord(2));
        backward.put_word(EncodedWord(1));
        assert_ne!(
            forward.digest(),
            backward.digest(),
            "the fold is order-sensitive, so an order-insensitive digest is not what this is"
        );
    }

    /// Trap pair — **two field orders**. A former's children are written in a
    /// fixed order, so a product and its transpose take two content ids.
    #[test]
    fn a_transposed_product_encodes_differently()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let forward = arena.value_type_product(&[unit, base]);
        let backward = arena.value_type_product(&[base, unit]);
        let mut table = ContentTable::new();
        assert_ne!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::ValueTypeLevel(forward),
                Telescope::Whole(&[])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::ValueTypeLevel(backward),
                Telescope::Whole(&[])
            ),
            "A x B and B x A are different types and must be different keys"
        );
    }

    /// Trap set — **a stage is identity within a judgement**. A recursion's
    /// goals at `A`, at `A^ι` and at `A^{<ι}` are different questions, so a
    /// memo keyed on content never answers one with another's verdict; two
    /// mints of one stage over one base are one key.
    #[test]
    fn a_stage_is_part_of_a_type_s_content()
    {
        let mut arena = TermArena::new();
        let base = arena.value_type_base(BaseType::Integer);
        let root = gandr_kernel_term::StageId::from(0_usize);
        let other = gandr_kernel_term::StageId::from(1_usize);
        let at = gandr_kernel_term::Stage::At(root);
        let below = gandr_kernel_term::Stage::Below {
            anchor: root,
            depth: gandr_kernel_term::StageDepth::ONE,
        };
        let types = [
            base,
            arena.value_type_staged(base, at),
            arena.value_type_staged(base, below),
            arena.value_type_staged(base, gandr_kernel_term::Stage::At(other)),
            arena.value_type_staged(base, gandr_kernel_term::Stage::Below {
                anchor: root,
                depth: gandr_kernel_term::StageDepth::ONE.deeper(),
            }),
        ];
        let again = arena.value_type_staged(base, at);
        let mut table = ContentTable::new();
        let keys: alloc::vec::Vec<_> = types
            .iter()
            .map(|&id| {
                support_key(
                    &mut table,
                    &arena,
                    SupportGoal::ValueTypeLevel(id),
                    Telescope::Whole(&[]),
                )
            })
            .collect();
        for (index, key) in keys.iter().enumerate() {
            for later in keys.iter().skip(index.saturating_add(1)) {
                assert_ne!(key, later, "two stages, or a stage and none, are two keys");
            }
        }
        assert_eq!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::ValueTypeLevel(again),
                Telescope::Whole(&[])
            ),
            keys[1],
            "one stage over one base is one key"
        );
    }

    /// Trap pair — **two families with one payload**. The node tags are drawn
    /// from the format's single global alphabet, so the unit value and the unit
    /// type cannot collide even though both are payload-free leaves.
    #[test]
    fn two_families_with_one_payload_encode_differently()
    {
        let mut arena = TermArena::new();
        let unit_value = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let mut table = ContentTable::new();
        assert_ne!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(unit_value),
                Telescope::Whole(&[])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::ValueTypeLevel(unit_type),
                Telescope::Whole(&[])
            ),
            "a payload-free value and a payload-free type are different questions"
        );
        assert_ne!(
            content_digest(&arena, AnyNode::Value(unit_value)),
            content_digest(&arena, AnyNode::ValueType(unit_type)),
            "and the absolute digests separate them too, so the record tags carry it"
        );
    }

    /// Trap pair — **signed zeroes**. The term crate pins a negative zero to
    /// non-negative before it can be encoded, so the two spellings take one
    /// content id; a genuinely signed pair takes two.
    #[test]
    fn signed_zeroes_collapse_and_signed_ones_do_not()
    {
        let mut arena = TermArena::new();
        let positive_zero = arena.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            magnitude(String::from("0")),
        )));
        let negative_zero = arena.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::Negative,
            magnitude(String::from("0")),
        )));
        let positive_one = arena.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            magnitude(String::from("1")),
        )));
        let negative_one = arena.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::Negative,
            magnitude(String::from("1")),
        )));
        let mut table = ContentTable::new();
        assert_eq!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(positive_zero),
                Telescope::Whole(&[])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(negative_zero),
                Telescope::Whole(&[])
            ),
            "one number has one key, whichever way it was spelled"
        );
        assert_ne!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(positive_one),
                Telescope::Whole(&[])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(negative_one),
                Telescope::Whole(&[])
            ),
            "and the sign is genuinely in the key where it changes the value"
        );
    }

    /// Trap pair — **the length-prefix ambiguity pair**. Two texts that
    /// concatenate alike must not encode alike.
    #[test]
    fn the_length_prefix_separates_a_split_pair()
    {
        let mut arena = TermArena::new();
        // The pair has to sit inside **one record**, because the record framing
        // separates two records on its own — a pair of literals would pass
        // whether or not their payloads were length-prefixed, and would witness
        // nothing. A numeric literal carries two text payloads in one record,
        // so `1.23` and `12.3` concatenate to the same digits and are separated
        // by the prefixes alone.
        let first = arena.value_literal(Literal::Numeric(NumericLiteral::new(
            Sign::NonNegative,
            magnitude(String::from("1")),
            fraction(String::from("23")),
        )));
        let second = arena.value_literal(Literal::Numeric(NumericLiteral::new(
            Sign::NonNegative,
            magnitude(String::from("12")),
            fraction(String::from("3")),
        )));
        let mut table = ContentTable::new();
        assert_ne!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(first),
                Telescope::Whole(&[])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(second),
                Telescope::Whole(&[])
            ),
            "the two splittings concatenate alike and must still key apart"
        );

        // The two-record spelling is kept beside it as the case that does *not*
        // witness the prefix, so a reader is not misled about which mechanism
        // separates which pair.
        let left = arena.value_literal(text(String::from("ab")));
        let right = arena.value_literal(text(String::from("c")));
        let joined = arena.value_tuple(&[left, right]);
        let left = arena.value_literal(text(String::from("a")));
        let right = arena.value_literal(text(String::from("bc")));
        let split = arena.value_tuple(&[left, right]);
        assert_ne!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(joined),
                Telescope::Whole(&[])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(split),
                Telescope::Whole(&[])
            ),
            "and two literals in two records are separated by the record framing"
        );
    }

    #[test]
    fn the_direction_is_part_of_the_key()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let mut table = ContentTable::new();
        assert_ne!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(unit),
                Telescope::Whole(&[])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::CheckValue(unit, unit_type),
                Telescope::Whole(&[])
            ),
            "synthesizing a value and checking it are different questions"
        );
    }

    /// A rewrite key separates on each of its three components and collapses on
    /// content, which is the whole of what makes an entry answerable only for
    /// the goal that would have produced it.
    #[test]
    fn a_rewrite_key_separates_on_each_component()
    {
        let mut arena = TermArena::new();
        let subject = arena.value_variable(DeBruijnIndex::from(0_u32));
        let other_spelling = arena.value_variable(DeBruijnIndex::from(0_u32));
        let replacement = arena.value_unit();
        let mut table = ContentTable::new();
        let base = |depth, cutoff, amount| RewriteGoal::Shift {
            subject: AnyNode::Value(subject),
            depth,
            cutoff,
            amount,
        };
        let none = BinderDepth::from(0_u32);
        let one = BinderDepth::from(1_u32);
        let key = encode_rewrite(&mut table, &arena, base(none, none, one));
        assert_ne!(
            key,
            encode_rewrite(&mut table, &arena, base(one, none, one)),
            "the binder depth is part of the key"
        );
        assert_ne!(
            key,
            encode_rewrite(&mut table, &arena, base(none, one, one)),
            "and so is the cutoff"
        );
        assert_ne!(
            key,
            encode_rewrite(
                &mut table,
                &arena,
                base(none, none, BinderDepth::from(2_u32))
            ),
            "and so is the amount"
        );
        assert_ne!(
            key,
            encode_rewrite(&mut table, &arena, RewriteGoal::Substitute {
                subject: AnyNode::Value(subject),
                depth: none,
                replacement,
            },),
            "and the direction separates the two rewrites"
        );
        assert_eq!(
            key,
            encode_rewrite(&mut table, &arena, RewriteGoal::Shift {
                subject: AnyNode::Value(other_spelling),
                depth: none,
                cutoff: none,
                amount: one,
            },),
            "while two arena spellings of one content are one question"
        );
    }

    #[test]
    fn the_telescope_is_folded_in_order()
    {
        let mut arena = TermArena::new();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let unit = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let mut table = ContentTable::new();
        assert_ne!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(variable),
                Telescope::Whole(&[unit, base])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(variable),
                Telescope::Whole(&[base, unit])
            ),
            "dependency order is part of the content, so a permuted telescope is another key"
        );
        assert_ne!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(variable),
                Telescope::Whole(&[unit])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(variable),
                Telescope::Whole(&[unit, base])
            ),
            "and a longer telescope is another key, since the length is written"
        );
    }

    #[test]
    fn the_read_positions_are_part_of_the_key()
    {
        let mut arena = TermArena::new();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let unit = arena.value_type_unit();
        let base = arena.value_type_base(BaseType::Integer);
        let at = DeBruijnIndex::from;
        let mut table = ContentTable::new();
        let mut key = |telescope: Telescope<'_>| {
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(variable),
                telescope,
            )
        };
        let innermost = key(Telescope::Read(&[(at(0_u32), unit)]));
        assert_eq!(
            innermost,
            key(Telescope::Read(&[(at(0_u32), unit)])),
            "one binder of one type read at one position is one key"
        );
        assert_ne!(
            innermost,
            key(Telescope::Read(&[(at(1_u32), unit)])),
            "the same type read one binder further out is another key"
        );
        assert_ne!(
            innermost,
            key(Telescope::Read(&[(at(64_u32), unit)])),
            "and so at a distant one"
        );
        assert_ne!(
            innermost,
            key(Telescope::Read(&[])),
            "reading nothing is another key"
        );
        assert_ne!(
            key(Telescope::Read(&[(at(0_u32), unit), (at(1_u32), base)])),
            key(Telescope::Read(&[(at(0_u32), base), (at(1_u32), unit)])),
            "each type is keyed at its own position"
        );
        assert_ne!(
            innermost,
            key(Telescope::Whole(&[unit])),
            "and a whole context is never a read one"
        );
    }

    #[test]
    fn records_sharing_a_digest_keep_their_own_ids()
    {
        let forced = gandr_kernel_check_memo::ContentDigest::new(
            gandr_kernel_check_memo::DigestWord::from(7_u64),
            gandr_kernel_check_memo::DigestWord::from(7_u64),
        );
        let admit = |table: &mut ContentTable, tag: u8| {
            table.scratch = ContentEncoding::new();
            table.scratch.put_tag(super::WireTag::from(tag));
            table.admit(forced)
        };
        let mut table = ContentTable::new();
        let first = admit(&mut table, 0x01);
        let second = admit(&mut table, 0x02);
        let third = admit(&mut table, 0x03);
        assert_ne!(first, second, "one digest never merges two records");
        assert_ne!(second, third, "nor a third filed behind them");
        assert_eq!(
            admit(&mut table, 0x03),
            third,
            "the end of the chain is found again"
        );
        assert_eq!(admit(&mut table, 0x01), first, "and so is its head");
        assert_eq!(admit(&mut table, 0x02), second, "and its middle");
        assert_eq!(table.records, 3_u64, "and asking again adds no record");
    }

    #[test]
    fn one_key_record_per_distinct_question()
    {
        let mut arena = TermArena::new();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let pair = arena.value_tuple(&[variable, variable]);
        let unit = arena.value_type_unit();
        let read = [(DeBruijnIndex::from(0_u32), unit)];
        let mut table = ContentTable::new();
        let first = support_key(
            &mut table,
            &arena,
            SupportGoal::SynthValue(variable),
            Telescope::Read(&read),
        );
        assert_eq!(
            table.records, 5_u64,
            "the subject, the binder's type, its pair, the cover and the goal"
        );
        assert_eq!(
            first,
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(variable),
                Telescope::Read(&read)
            ),
            "asking again names the same goal"
        );
        assert_eq!(table.records, 5_u64, "and adds no record");
        let checked = support_key(
            &mut table,
            &arena,
            SupportGoal::CheckValue(variable, unit),
            Telescope::Read(&read),
        );
        assert_ne!(checked, first, "checking is another question");
        assert_eq!(
            table.records, 6_u64,
            "whose expected type and cover are already named: only its goal record is new"
        );
        let _reading = support_key(
            &mut table,
            &arena,
            SupportGoal::SynthValue(pair),
            Telescope::Read(&read),
        );
        assert_eq!(
            table.records, 8_u64,
            "another subject reading the same binder adds its node and its goal, and shares the \
             pair and the cover"
        );
    }

    #[test]
    fn structurally_equal_nodes_encode_alike()
    {
        let mut arena = TermArena::new();
        let first = arena.value_unit();
        let second = arena.value_unit();
        assert_ne!(first, second, "the fixture mints two distinct arena nodes");
        let mut table = ContentTable::new();
        assert_eq!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(first),
                Telescope::Whole(&[])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(second),
                Telescope::Whole(&[])
            ),
            "equal content is one key however many arena nodes spell it - which is what an \
             identity key forfeits and what makes a re-minted spine's leaf collapse"
        );
    }

    #[test]
    fn an_unreadable_reference_still_encodes()
    {
        let mut arena = TermArena::new();
        let floor = arena.watermark();
        let value = arena.value_unit();
        let comp = arena.computation_return(value);
        let value_type = arena.value_type_unit();
        let comp_type = arena.comp_type_returner(value_type);
        arena.truncate_to(floor);
        let cases = [
            (AnyNode::Value(value), SupportGoal::SynthValue(value), 0_u8),
            (
                AnyNode::Computation(comp),
                SupportGoal::SynthComp(comp),
                1_u8,
            ),
            (
                AnyNode::ValueType(value_type),
                SupportGoal::ValueTypeLevel(value_type),
                2_u8,
            ),
            (
                AnyNode::CompType(comp_type),
                SupportGoal::CompTypeLevel(comp_type),
                3_u8,
            ),
        ];
        let mut table = ContentTable::new();
        let keys = cases.map(|(node, goal, family)| {
            let key = support_key(&mut table, &arena, goal, Telescope::Whole(&[]));
            let mut record = ContentEncoding::new();
            table.write_record(&mut record, &arena, node);
            assert_eq!(record.as_ref(), &[0xff_u8, family]);
            assert_eq!(
                content_digest(&arena, node),
                ContentEncoding(vec![2_u8, 0xff, family]).digest()
            );
            key
        });
        for (index, key) in keys.iter().enumerate() {
            for other in keys.iter().skip(index.saturating_add(1)) {
                assert_ne!(key, other, "unreadable families remain separate questions");
            }
        }
    }

    #[test]
    fn each_case_child_changes_canonical_content()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let left = arena.value_injection(gandr_kernel_term::Side::Left.into(), unit);
        let right = arena.value_injection(gandr_kernel_term::Side::Right.into(), unit);
        let returns_unit = arena.computation_return(unit);
        let returns_variable = arena.computation_return(variable);
        let roots = [
            arena.computation_case(left, &[returns_unit, returns_unit]),
            arena.computation_case(right, &[returns_unit, returns_unit]),
            arena.computation_case(left, &[returns_variable, returns_unit]),
            arena.computation_case(left, &[returns_unit, returns_variable]),
        ];
        let mut table = ContentTable::new();
        let keys = roots.map(|root| {
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthComp(root),
                Telescope::Whole(&[]),
            )
        });
        for (index, key) in keys.iter().enumerate() {
            for other in keys.iter().skip(index.saturating_add(1)) {
                assert_ne!(
                    key, other,
                    "scrutinee and both branch positions affect content"
                );
            }
        }
    }

    #[test]
    fn computation_type_formers_keep_distinct_content()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let arrow = arena.comp_type_arrow(unit, returner);
        let dependent = arena.comp_type_pi(unit, returner);
        let code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let element = arena.comp_type_element(code, super::Level::zero());
        let mut table = ContentTable::new();
        let keys = [returner, arrow, dependent, element].map(|root| {
            support_key(
                &mut table,
                &arena,
                SupportGoal::CompTypeLevel(root),
                Telescope::Whole(&[]),
            )
        });
        for (index, key) in keys.iter().enumerate() {
            for other in keys.iter().skip(index.saturating_add(1)) {
                assert_ne!(
                    key, other,
                    "computation-type heads remain distinct, including the two arrows"
                );
            }
        }
    }

    #[test]
    fn expected_type_content_changes_checking_keys()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let comp = arena.computation_return(unit);
        let unit_type = arena.value_type_unit();
        let integer_type = arena.value_type_base(BaseType::Integer);
        let unit_returner = arena.comp_type_returner(unit_type);
        let integer_returner = arena.comp_type_returner(integer_type);
        let mut table = ContentTable::new();
        assert_ne!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::CheckValue(unit, unit_type),
                Telescope::Whole(&[])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::CheckValue(unit, integer_type),
                Telescope::Whole(&[])
            )
        );
        assert_ne!(
            support_key(
                &mut table,
                &arena,
                SupportGoal::CheckComp(comp, unit_returner),
                Telescope::Whole(&[])
            ),
            support_key(
                &mut table,
                &arena,
                SupportGoal::CheckComp(comp, integer_returner),
                Telescope::Whole(&[])
            )
        );
    }

    #[test]
    fn level_frames_are_canonical_and_include_each_component()
    {
        let image = |level: &super::Level| {
            let mut record = ContentEncoding(vec![0x7e]);
            super::put_level(&mut record, level);
            record
        };
        let zero = super::Level::zero();
        let constant = super::Level::constant(gandr_kernel_strata::LevelConstant::from(2_u64));
        assert_eq!(image(&zero).0, [0x7e_u8, 0, 0]);
        assert_eq!(image(&constant).0, [0x7e_u8, 2, 0]);
        let low = super::Level::var(super::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(0_u32),
        ));
        let high = super::Level::var(super::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(2_u32),
        ))
        .succ()
        .expect("the unit offset fits");
        let forward = low.max(&high);
        let reverse = high.max(&low);
        assert_eq!(image(&forward).0, [0x7e_u8, 0, 2, 0, 0, 2, 1]);
        assert_eq!(image(&reverse), image(&forward));
        assert_eq!(image(&forward.max(&constant)).0, [
            0x7e_u8, 2, 2, 0, 0, 2, 1
        ]);
        assert_eq!(
            image(&low.max(&high.succ().expect("the next offset fits"))).0,
            [0x7e_u8, 0, 2, 0, 0, 2, 2]
        );
        let next = super::Level::var(super::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(3_u32),
        ))
        .succ()
        .expect("the unit offset fits");
        assert_eq!(image(&low.max(&next)).0, [0x7e_u8, 0, 2, 0, 0, 3, 1]);
    }

    #[test]
    fn an_absolute_digest_ignores_arena_position()
    {
        let mut arena = TermArena::new();
        let first_unit = arena.value_type_unit();
        let second_unit = arena.value_type_unit();
        let first = arena.value_type_product(&[first_unit, first_unit]);
        let second = arena.value_type_product(&[second_unit, second_unit]);
        assert_ne!(first, second, "the fixture mints two distinct arena nodes");
        assert_eq!(
            content_digest(&arena, AnyNode::ValueType(first)),
            content_digest(&arena, AnyNode::ValueType(second)),
            "the absolute digest is a function of content, so it survives relocation"
        );
        let other = arena.value_type_base(BaseType::Integer);
        assert_ne!(
            content_digest(&arena, AnyNode::ValueType(first)),
            content_digest(&arena, AnyNode::ValueType(other)),
            "and it separates different content"
        );
    }

    #[test]
    fn one_table_records_each_distinct_node_once()
    {
        let mut arena = TermArena::new();
        let mut body = arena.value_unit();
        for _step in 0 .. 16_u32 {
            body = arena.value_tuple(&[body, body]);
        }
        let mut table = ContentTable::new();
        let key = support_key(
            &mut table,
            &arena,
            SupportGoal::SynthValue(body),
            Telescope::Whole(&[]),
        );
        // The 17 distinct nodes, then the key's empty context and its goal.
        assert_eq!(table.records, 19_u64);
        assert_eq!(table.interned.len(), 19_usize);
        assert_eq!(table.placed.len(), 17_usize);
        let length = usize::from(table.stream().length());
        assert!(
            length < 512,
            "a 65536-occurrence composite records its 17 distinct nodes, not its occurrences: \
             {length} bytes"
        );
        // Asking again costs nothing: the session's table already holds it.
        let before = usize::from(table.stream().length());
        let again = support_key(
            &mut table,
            &arena,
            SupportGoal::SynthValue(body),
            Telescope::Whole(&[]),
        );
        assert_eq!(again, key);
        assert_eq!(table.records, 19_u64);
        assert_eq!(table.placed.len(), 17_usize);
        assert_eq!(
            before,
            usize::from(table.stream().length()),
            "a second question about the same content adds no record, which is what keeps key \
             derivation linear across a whole check"
        );
        let mut reminted = arena.value_unit();
        for _step in 0 .. 16_u32 {
            reminted = arena.value_tuple(&[reminted, reminted]);
        }
        let reminted_key = support_key(
            &mut table,
            &arena,
            SupportGoal::SynthValue(reminted),
            Telescope::Whole(&[]),
        );
        assert_eq!(reminted_key, key);
        assert_eq!(table.records, 19_u64);
        assert_eq!(table.interned.len(), 19_usize);
        assert_eq!(table.placed.len(), 34_usize);
        assert_eq!(usize::from(table.stream().length()), before);
    }

    #[test]
    fn a_rewrite_under_an_inactive_memo_encodes_nothing_487()
    {
        let mut arena = TermArena::new();
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let unit = arena.value_unit();
        let subject = arena.value_tuple(&[variable, unit]);
        let mut table = ContentTable::new();
        let shifted = crate::rewrite::shift_value(
            &mut arena,
            &mut table,
            &mut gandr_kernel_check_memo::NullMemo,
            subject,
            BinderDepth::NONE,
            BinderDepth::from(1_u32),
        );
        assert_ne!(shifted, subject, "the free variable rises");
        assert_eq!(
            (table.records, table.placed.len()),
            (0_u64, 0_usize),
            "a memo that keeps nothing is keyed by nothing: the walk encodes no node"
        );
        let mut memo = crate::rewrite::RewriteMemo::new();
        let _shifted = crate::rewrite::shift_value(
            &mut arena,
            &mut table,
            &mut memo,
            subject,
            BinderDepth::NONE,
            BinderDepth::from(1_u32),
        );
        assert!(
            table.records > 0,
            "a memo that keeps its answers is keyed by their content"
        );
    }
}
