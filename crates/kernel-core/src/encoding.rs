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
//! # A definition is named by its content
//!
//! A table told an environment's admitted declarations names a reference to
//! a **plain definition** — admitted checked, alone, outside every atom's
//! minting admission, monomorphic, and carrying no laws, relations,
//! operation rules, stages, presentation or sealing provenance — by a
//! **definition record**: its declared type's id, its body's id and its
//! **rank**, the number of earlier plain definitions of the environment with
//! the same type and body. A key over such a reference then reads what the
//! definition is, not where the environment admitted it, so two environments
//! that admitted the same declarations in another order build the same
//! records. The rank keeps the names injective: the kernel compares two
//! constants by their positions without unfolding either, so two definitions
//! of one content are two constants to it, and a key that merged them could
//! answer for one with a term naming the other. Admission ranks a definition
//! by comparing digests, then the two definitions exactly. Every other
//! constant reference is named by its admission position, as is every
//! reference in a table told nothing.
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
//!
//! # References
//!
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: a key is the
//!   kernel's whole input only when the constants it reaches are named by
//!   content (§ kernel-reassessment-design item 2), and those names are
//!   table-local, agreeing across tables by re-interned records (item 10), as
//!   the definition record is.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_check_memo::DigestWord;
use gandr_kernel_check_memo::HashIndex;
use gandr_kernel_check_memo::Probe;
use gandr_kernel_check_memo::TableHash;
use gandr_kernel_check_memo::TablePosition;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelOffset;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::ArenaLength;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerWidth;
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

impl From<TablePosition> for ContentId
{
    /// The id of the record at `position` in its table's stream: ids are
    /// assigned in stream order, so a record's position is its id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: TablePosition) -> Self
    {
        Self(u64::try_from(usize::from(position)).unwrap_or(u64::MAX))
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
        assert!(
            row.tag.0 < DEFINITION_TAG,
            "node tag overlaps a reserved byte"
        );
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

/// The byte a goal record reserves: one question, the memo's key.
const GOAL_TAG: u8 = 0xFA;

/// The byte a definition record reserves: a reference to a plain definition,
/// named by its declared type and body. The lowest reserved byte; every node
/// tag sits below it.
const DEFINITION_TAG: u8 = 0xF9;

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

/// How a table names one admitted constant when a reference reaches it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ConstantName
{
    /// By its admission position.
    Position,
    /// By its content: a plain definition's declared type and body, and its
    /// rank among the earlier ones with the same two.
    Definition
    {
        /// The declared value type's root.
        declared: ValueTypeId,
        /// The body's root.
        body: ValueId,
        /// How many earlier plain definitions of the environment carry the
        /// same declared type and body.
        rank: DefinitionRank,
        /// The digest of the declared type and body, which admission compares
        /// before it compares the two exactly; no record holds it.
        digest: ContentDigest,
    },
}

/// How many earlier plain definitions of one environment carry a definition's
/// declared type and body.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct DefinitionRank(usize);

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
/// Every record's bytes are held once, in the stream; the index files each
/// record's id under its digest's hash, and a lookup compares the bytes there.
/// Each arena node's id sits in a dense column for its family. Records are
/// built in one reused buffer and walks run on one reused stack, so asking
/// about content the table already holds allocates nothing.
#[derive(Clone, Debug, Default)]
pub struct ContentTable
{
    /// The framed record stream, in id order: every record's bytes, once.
    stream: ContentEncoding,
    /// Where each record's bytes sit in the stream, by id.
    spans: Vec<RecordSpan>,
    /// Each record's id, filed under its digest's hash.
    interned: HashIndex,
    /// The id already assigned to each arena node.
    placed: Placements,
    /// How many records the stream holds.
    records: u64,
    /// The record being built.
    scratch: ContentEncoding,
    /// The members of the cover or context being built.
    members: Vec<ContentId>,
    /// The placement walk's task stack.
    tasks: Vec<EncodeTask>,
    /// How each admitted constant is named, by admission position; a position
    /// past the end is named by itself.
    constants: Vec<ConstantName>,
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

/// The content id each arena node was assigned: one dense column per node
/// family, read at the node's offset.
///
/// A column is paged. A page of [`PLACEMENT_PAGE_SLOTS`] slots is allocated
/// the first time a node on it is placed, so a table asked about a few nodes
/// of a wide arena holds a few pages rather than the arena's width.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a node holds at most one id, the one last placed for it; nodes of
///   distinct families or offsets never share a slot.
/// - provides: an untouched read and write per node in place of an ordered
///   search.
/// - panics: none.
/// - executable: none — a data declaration; its operations carry the
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — one offset in two families, offsets on two pages, and a
///   repeated placement separate a family-blind column, a page-blind slot and a
///   double count.
/// - witness: `encoding::tests::placements_keep_families_and_pages_apart`
#[derive(Clone, Debug, Default)]
struct Placements
{
    /// Ids placed for value nodes.
    values: PlacementColumn,
    /// Ids placed for computation nodes.
    computations: PlacementColumn,
    /// Ids placed for value-type nodes.
    value_types: PlacementColumn,
    /// Ids placed for computation-type nodes.
    comp_types: PlacementColumn,
    /// How many nodes hold an id.
    count: PlacementCount,
}

/// One family's column of placements, in pages allocated on first write.
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
struct PlacementColumn
{
    /// The pages, by page number; an empty page has never been written.
    pages: Vec<Vec<PlacementSlot>>,
}

/// One node's slot in its column.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Placement
{
    /// The node has not been placed.
    Unplaced,
    /// The node was placed with this id.
    Placed(ContentId),
}

/// How many nodes a [`Placements`] holds an id for.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct PlacementCount(usize);

/// One node's slot as a column page stores it: the placed id, or
/// [`PlacementSlot::UNPLACED`], an id no table assigns.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PlacementSlot(ContentId);

impl PlacementSlot
{
    /// The slot of a node not yet placed. A table's ids count its records,
    /// which allocated memory bounds far below this one.
    const UNPLACED: Self = Self(ContentId(u64::MAX));

    /// The placement the slot stores.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn placement(self) -> Placement
    {
        if self == Self::UNPLACED {
            Placement::Unplaced
        }
        else {
            Placement::Placed(self.0)
        }
    }
}

/// How many offsets one column page covers.
const PLACEMENT_PAGE_SLOTS: usize = 128;

/// The shift from an offset to its page number: the page size's logarithm.
const PLACEMENT_PAGE_SHIFT: u32 = PLACEMENT_PAGE_SLOTS.trailing_zeros();

/// The mask from an offset to its slot within its page.
const PLACEMENT_SLOT_MASK: usize = PLACEMENT_PAGE_SLOTS.saturating_sub(1);

quenchant_shape::reason_enum! {
    /// Why a table holds no id for a node.
    mod placement {
        /// The node has no id yet.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The table's walk has not placed the node.
            Unplaced,
        }
    }
}

impl PlacementColumn
{
    /// The slot at `offset`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the placement last written at `offset`, or
    ///   [`Placement::Unplaced`] when its page or slot was never written.
    /// - provides: the column read.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Placements`].
    /// - witness: `encoding::tests::placements_keep_families_and_pages_apart`
    #[inline]
    #[spec(ensures: |ret| matches!(ret, Placement::Unplaced)
        || usize::from(offset).checked_shr(PLACEMENT_PAGE_SHIFT)
            .and_then(|page| self.pages.get(page))
            .and_then(|page| page.get(usize::from(offset) & PLACEMENT_SLOT_MASK))
            .map(|slot| slot.placement()) == Some(ret))]
    fn get(
        &self,
        offset: ArenaLength,
    ) -> Placement
    {
        let offset = usize::from(offset);
        offset
            .checked_shr(PLACEMENT_PAGE_SHIFT)
            .and_then(|page| self.pages.get(page))
            .and_then(|page| page.get(offset & PLACEMENT_SLOT_MASK))
            .map_or(Placement::Unplaced, |slot| slot.placement())
    }

    /// Write `id` at `offset`, returning what the slot held.
    ///
    /// # Specification
    /// - requires: `offset` is an arena offset, below `u32::MAX`, and `id` an
    ///   id the table assigned, so never [`PlacementSlot::UNPLACED`]'s.
    /// - ensures: [`PlacementColumn::get`] answers `Placed(id)` at `offset`;
    ///   every other offset reads as before. The slot's previous placement is
    ///   returned.
    /// - provides: the column write; it allocates the offset's page the first
    ///   time the page is written.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Placements`].
    /// - witness: `encoding::tests::placements_keep_families_and_pages_apart`
    #[inline]
    #[spec(ensures: |ret| self.get(offset) == Placement::Placed(id))]
    fn set(
        &mut self,
        offset: ArenaLength,
        id: ContentId,
    ) -> Placement
    {
        let offset = usize::from(offset);
        let number = offset.checked_shr(PLACEMENT_PAGE_SHIFT).unwrap_or(0);
        if self.pages.len() <= number {
            self.pages.resize_with(number.saturating_add(1), Vec::new);
        }
        let Some(page) = self.pages.get_mut(number)
        else {
            return Placement::Unplaced;
        };
        if page.is_empty() {
            page.resize(PLACEMENT_PAGE_SLOTS, PlacementSlot::UNPLACED);
        }
        page.get_mut(offset & PLACEMENT_SLOT_MASK)
            .map_or(Placement::Unplaced, |slot| {
                core::mem::replace(slot, PlacementSlot(id)).placement()
            })
    }
}

impl Placements
{
    /// The column `node`'s family is placed in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn column(
        &self,
        node: AnyNode,
    ) -> &PlacementColumn
    {
        match node {
            AnyNode::Value(_) => &self.values,
            AnyNode::Computation(_) => &self.computations,
            AnyNode::ValueType(_) => &self.value_types,
            AnyNode::CompType(_) => &self.comp_types,
        }
    }

    /// The id placed for `node`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the id last placed for `node`, or
    ///   [`placement::Absent::Unplaced`] when none was.
    /// - provides: the placement read every record's children go through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Placements`].
    /// - witness: `encoding::tests::placements_keep_families_and_pages_apart`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Maybe::Present(id) => self.column(node).get(node.offset()) == Placement::Placed(id),
        Maybe::Absent(placement::Absent::Unplaced) => self.column(node).get(node.offset()) == Placement::Unplaced,
    })]
    fn get(
        &self,
        node: AnyNode,
    ) -> Maybe<ContentId, placement::Absent>
    {
        match self.column(node).get(node.offset()) {
            Placement::Placed(id) => Maybe::Present(id),
            Placement::Unplaced => Maybe::Absent(placement::Absent::Unplaced),
        }
    }

    /// Place `node` with `id`.
    ///
    /// # Specification
    /// - requires: `node` belongs to the arena every other placement does.
    /// - ensures: [`Placements::get`] answers `id` for `node`; the count rises
    ///   by one exactly when `node` held no id before.
    /// - provides: the placement write.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Placements`].
    /// - witness: `encoding::tests::placements_keep_families_and_pages_apart`
    #[inline]
    #[spec(
        captures: [held = self.get(node), count_before = self.count],
        ensures: self.get(node) == Maybe::Present(id) && match held {
            Maybe::Present(_) => self.count == count_before,
            Maybe::Absent(_) => self.count.0 == count_before.0.saturating_add(1),
        }
    )]
    fn insert(
        &mut self,
        node: AnyNode,
        id: ContentId,
    )
    {
        let column = match node {
            AnyNode::Value(_) => &mut self.values,
            AnyNode::Computation(_) => &mut self.computations,
            AnyNode::ValueType(_) => &mut self.value_types,
            AnyNode::CompType(_) => &mut self.comp_types,
        };
        if column.set(node.offset(), id) == Placement::Unplaced {
            self.count = PlacementCount(self.count.0.saturating_add(1));
        }
    }

    /// How many nodes hold an id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn count(&self) -> PlacementCount
    {
        self.count
    }
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

    /// Name the constants of `entries` past those already named: each plain
    /// definition by its content, every other constant by its position.
    ///
    /// # Specification
    /// - requires: `entries` extends the entries this table was told before,
    ///   and every root a plain definition among them names lives in the arena
    ///   the table places nodes of.
    /// - ensures: the table names exactly the constants `entries` holds, each
    ///   as its admission named it; the names it held before are unchanged.
    /// - provides: the reading a session's keys take of every constant
    ///   reference, set before the session places a node.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the predicate checks the count named; a definition
    ///   and an axiom referent each admitted before and after another
    ///   definition separate reading by content from reading by position.
    /// - witness: `encoding::tests::a_definition_reference_reads_alike_in_either_admission_order`
    /// - witness: `encoding::tests::an_axiom_reference_keeps_its_position`
    #[spec(captures: named_before = self.constants.len(),
        ensures: self.constants.len() == named_before.max(usize::from(entries.len())))]
    pub(crate) fn name_constants(
        &mut self,
        entries: &crate::env::Entries,
    )
    {
        let named = self.constants.len();
        self.constants.extend(
            entries
                .iter()
                .skip(named)
                .map(crate::env::AdmittedDeclaration::key_name),
        );
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
    ///   families, so its dependency graph is acyclic. A definition record's
    ///   children are the declared type and body of a definition admitted
    ///   checked, whose body names only constants admitted before it, so
    ///   following references descends in admission order.
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
        captures: [held = self.placed.get(node), records_before = self.records,
            stream_before = self.stream.0.len(), placed_before = self.placed.count()],
        ensures: |ret| self.placed.get(node) == Maybe::Present(ret) && ret.0 < self.records
            && self.records >= records_before && self.placed.count() >= placed_before
            && match held {
                Maybe::Present(prior) => ret == prior && self.records == records_before
                    && self.stream.0.len() == stream_before
                    && self.placed.count() == placed_before,
                Maybe::Absent(placement::Absent::Unplaced) => true,
            }
    )]
    fn place(
        &mut self,
        arena: &TermArena,
        node: AnyNode,
    ) -> ContentId
    {
        if let Maybe::Present(held) = self.placed.get(node) {
            return held;
        }
        let mut tasks = core::mem::take(&mut self.tasks);
        tasks.clear();
        tasks.push(EncodeTask::Open(node));
        while let Some(task) = tasks.pop() {
            match task {
                EncodeTask::Open(open) => {
                    if let Maybe::Present(_) = self.placed.get(open) {
                        continue;
                    }
                    tasks.push(EncodeTask::Close(open));
                    push_children(arena, &self.constants, open, &mut tasks);
                },
                EncodeTask::Close(close) => {
                    if let Maybe::Present(_) = self.placed.get(close) {
                        continue;
                    }
                    let mut record = core::mem::take(&mut self.scratch);
                    self.write_record(&mut record, arena, close);
                    self.scratch = record;
                    let id = self.intern_scratch();
                    self.placed.insert(close, id);
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
        requires: matches!(self.placed.get(node), Maybe::Present(_)),
        ensures: |ret| self.placed.get(node) == Maybe::Present(ret)
    )]
    fn content_of(
        &self,
        node: AnyNode,
    ) -> ContentId
    {
        match self.placed.get(node) {
            Maybe::Present(id) => id,
            Maybe::Absent(placement::Absent::Unplaced) => ContentId(0),
        }
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
        match self.probe_record(record, TableHash::of(&digest)) {
            Probe::Found(position) => Maybe::Present(ContentId::from(position)),
            Probe::Vacant(_) => Maybe::Absent(record_held::Absent::Fresh),
        }
    }

    /// The probe for `record`, whose digest hashes to `hash`: the position of
    /// the byte-equal record, or the slot a fresh one is filed at.
    ///
    /// # Specification
    /// - requires: `hash` is the table hash of `record`'s digest.
    /// - ensures: [`Probe::Found`] the position of the record whose bytes equal
    ///   `record`'s, or [`Probe::Vacant`] the slot it would be filed at.
    /// - provides: the one probe lookups and admissions decide over; it reads
    ///   the stream in place and allocates nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::held`].
    /// - witness: `encoding::tests::records_sharing_a_digest_keep_their_own_ids`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Probe::Found(position) => self.spans.get(usize::from(position))
            .and_then(|span| self.stream.0.get(span.start .. span.end))
            == Some(record.0.as_slice()),
        Probe::Vacant(_) => true,
    })]
    fn probe_record(
        &self,
        record: &ContentEncoding,
        hash: TableHash,
    ) -> Probe
    {
        self.interned.probe(hash, |position| {
            self.spans
                .get(usize::from(position))
                .and_then(|span| self.stream.0.get(span.start .. span.end))
                == Some(record.0.as_slice())
        })
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
    ///   `digest`'s hash. Ids are assigned in stream order, byte-equal records
    ///   take one id however many nodes spell them, and records sharing a
    ///   digest keep their own ids. The record count is at most the stream's
    ///   byte length: each fresh record appends a nonempty length-prefixed
    ///   image before the count advances. On supported targets that allocation
    ///   is bounded by `isize::MAX`, below `u64::MAX`; no representable table
    ///   overflows it. Past `u32::MAX` records the index files no more, so a
    ///   record equal to a later one takes its own id: sharing stops there, and
    ///   nothing else does.
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
    ///   branches, and two records forced under one digest exercise records
    ///   filed under one hash, not an unallocatable u64 ceiling.
    /// - witness: `encoding::tests::one_table_records_each_distinct_node_once`
    /// - witness: `encoding::tests::records_sharing_a_digest_keep_their_own_ids`
    #[spec(
        captures: [held = self.held(&self.scratch, digest), records_before = self.records,
            stream_before = self.stream.0.len()],
        ensures: |ret| u128::try_from(self.stream.0.len())
            .is_ok_and(|bytes| u128::from(self.records) <= bytes)
            && u64::try_from(self.spans.len()) == Ok(self.records) && ret.0 < self.records
            && (self.held(&self.scratch, digest) == Maybe::Present(ret)
                || ret.0 >= u64::from(u32::MAX))
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
        let hash = TableHash::of(&digest);
        let slot = match self.probe_record(&self.scratch, hash) {
            Probe::Found(position) => return ContentId::from(position),
            Probe::Vacant(slot) => slot,
        };
        let id = ContentId(self.records);
        let filed = TablePosition::try_from(self.spans.len());
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
        // Past the index's position ceiling a record is held but not filed:
        // a later equal record takes a fresh id, which costs sharing alone.
        if let Ok(position) = filed {
            self.interned.insert(slot, hash, position);
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
        && read.iter().all(|&(_, entry)| matches!(self.placed.get(AnyNode::ValueType(entry)), Maybe::Present(_))))]
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
        && context.iter().all(|&entry| matches!(self.placed.get(AnyNode::ValueType(entry)), Maybe::Present(_))))]
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
    ///   record. A reference to a constant the table names by its content
    ///   writes the definition tag, then the declared type's and the body's ids
    ///   and the definition's rank, and no position.
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
    /// - witness: `encoding::tests::a_definition_reference_reads_alike_in_either_admission_order`
    /// - witness: `encoding::tests::two_definitions_of_one_content_keep_two_names`
    #[spec(
        requires: match *value {
            Value::Constructor { datatype, ref fields, .. } => matches!(self.placed.get(AnyNode::ValueType(datatype)), Maybe::Present(_)) && fields.iter().all(|id| matches!(self.placed.get(AnyNode::Value(*id)), Maybe::Present(_))),
            Value::Record(ref fields) => fields.values().all(|id| matches!(self.placed.get(AnyNode::Value(*id)), Maybe::Present(_))),
            Value::SessionPath { path_type: classifier, payload_paths, .. } | Value::SessionFlow { flow_type: classifier, payload_paths, .. } => matches!(self.placed.get(AnyNode::ValueType(classifier)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(payload_paths)), Maybe::Present(_)),
            Value::PathEquiv { path_type, forward, backward, .. } => matches!(self.placed.get(AnyNode::ValueType(path_type)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(forward)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(backward)), Maybe::Present(_)),
            Value::ListNil | Value::Variable(_) | Value::Literal(_) => true,
            Value::Constant(index) => match constant_name(&self.constants, index) {
                ConstantName::Definition { declared, body, .. } => matches!(self.placed.get(AnyNode::ValueType(declared)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(body)), Maybe::Present(_)),
                ConstantName::Position => true,
            },
            Value::Tuple(ref components) => components.iter().all(|id| matches!(self.placed.get(AnyNode::Value(*id)), Maybe::Present(_))),
            Value::ListCons(first, second) | Value::PathProduct(first, second) | Value::FlowProduct(first, second) | Value::StaticApplication(first, second) | Value::Then { first, second, .. } => matches!(self.placed.get(AnyNode::Value(first)), Maybe::Present(_))
                            && matches!(self.placed.get(AnyNode::Value(second)), Maybe::Present(_)),
            Value::PathRefl(body) | Value::Univalence(body) | Value::Here { point: body, .. } | Value::Stay { point: body, .. } | Value::Injection(_, body) | Value::Lift { body, .. } => matches!(self.placed.get(AnyNode::Value(body)), Maybe::Present(_)),
            Value::ForwardFlow { flow_type, translator, ref outputs, .. } => matches!(self.placed.get(AnyNode::ValueType(flow_type)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(translator)), Maybe::Present(_)) && outputs.iter().all(|id| matches!(self.placed.get(AnyNode::Value(*id)), Maybe::Present(_))),
            Value::FunctionFlow { flow_type, domain, codomain } => matches!(self.placed.get(AnyNode::ValueType(flow_type)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(domain)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(codomain)), Maybe::Present(_)),
            Value::Higher { ref evidence, .. } => evidence.iter().all(|id| matches!(self.placed.get(AnyNode::Value(*id)), Maybe::Present(_))),
            Value::HigherEvaluation { ref components, .. } => components.iter().all(|component| [component.left, component.right, component.evidence].iter().all(|id| matches!(self.placed.get(AnyNode::Value(*id)), Maybe::Present(_)))),
            Value::QuantifiedEvaluation { ref children, .. } => children.iter().all(|id| matches!(self.placed.get(AnyNode::Value(*id)), Maybe::Present(_))),
            Value::Thunk(body) | Value::Returned(body) => matches!(self.placed.get(AnyNode::Computation(body)), Maybe::Present(_)),
            Value::Quote(quoted) => matches!(self.placed.get(AnyNode::ValueType(quoted)), Maybe::Present(_)),
            Value::QuoteComputation(quoted) => matches!(self.placed.get(AnyNode::CompType(quoted)), Maybe::Present(_)),
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
            Value::Constant(index) => match constant_name(&self.constants, index) {
                ConstantName::Definition { .. } => WireTag::from(DEFINITION_TAG),
                ConstantName::Position => gandr_kernel_term::NODE_V_CONSTANT,
            },
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
            Value::Constant(index) => match constant_name(&self.constants, index) {
                ConstantName::Definition {
                    declared,
                    body,
                    rank: DefinitionRank(rank),
                    ..
                } => {
                    record.put_tag(WireTag::from(DEFINITION_TAG));
                    record.put_content(self.content_of(AnyNode::ValueType(declared)));
                    record.put_content(self.content_of(AnyNode::Value(body)));
                    record.put_count(ComponentCount(rank));
                },
                ConstantName::Position => {
                    record.put_tag(gandr_kernel_term::NODE_V_CONSTANT);
                    record.put_count(ComponentCount(usize::from(index)));
                },
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
            Computation::DataCase { scrutinee, motive, ref branches, .. } => matches!(self.placed.get(AnyNode::Value(scrutinee)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::CompType(motive)), Maybe::Present(_)) && branches.iter().all(|id| matches!(self.placed.get(AnyNode::Computation(*id)), Maybe::Present(_))),
            Computation::SigmaSplit { scrutinee, motive, body } => [AnyNode::Value(scrutinee), AnyNode::CompType(motive), AnyNode::Computation(body)].iter().all(|child| matches!(self.placed.get(*child), Maybe::Present(_))),
            Computation::RecordProjection(record, _) | Computation::TupleProjection(record, _) => matches!(self.placed.get(AnyNode::Value(record)), Maybe::Present(_)),
            Computation::ListFold { element, result, list, on_nil, on_cons } => [AnyNode::ValueType(element), AnyNode::ValueType(result), AnyNode::Value(list), AnyNode::Computation(on_nil), AnyNode::Computation(on_cons)].iter().all(|child| matches!(self.placed.get(*child), Maybe::Present(_))),
            Computation::ListCase { list, on_nil, on_cons } => [AnyNode::Value(list), AnyNode::Computation(on_nil), AnyNode::Computation(on_cons)].iter().all(|child| matches!(self.placed.get(*child), Maybe::Present(_))),
            Computation::Transport(path, value) => matches!(self.placed.get(AnyNode::Value(path)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(value)), Maybe::Present(_)),
            Computation::PathTransport { motive, path, value } | Computation::Ride { motive, flow: path, value } => matches!(self.placed.get(AnyNode::ValueType(motive)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(path)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(value)), Maybe::Present(_)),
            Computation::TelescopeTransport { motive, path, start, over, value } | Computation::TelescopeRide { motive, flow: path, start, over, value } => [AnyNode::CompType(motive), AnyNode::Value(path), AnyNode::Value(start), AnyNode::Value(over), AnyNode::Value(value)].iter().all(|child| matches!(self.placed.get(*child), Maybe::Present(_))),
            Computation::RelatedApplication { path, left, right, evidence, body } => [AnyNode::Value(path), AnyNode::Value(left), AnyNode::Value(right), AnyNode::Value(evidence), AnyNode::Computation(body)].iter().all(|child| matches!(self.placed.get(*child), Maybe::Present(_))),
            Computation::Lambda(body) | Computation::Fixpoint { body, .. } => matches!(self.placed.get(AnyNode::Computation(body)), Maybe::Present(_)),
            Computation::Application(head, argument) => matches!(self.placed.get(AnyNode::Computation(head)), Maybe::Present(_))
                            && matches!(self.placed.get(AnyNode::Value(argument)), Maybe::Present(_)),
            Computation::Return(value) | Computation::Force(value) => matches!(self.placed.get(AnyNode::Value(value)), Maybe::Present(_)),
            Computation::Bind(bound, body) => matches!(self.placed.get(AnyNode::Computation(bound)), Maybe::Present(_))
                            && matches!(self.placed.get(AnyNode::Computation(body)), Maybe::Present(_)),
            Computation::With(ref components) => components.iter().all(|id| matches!(self.placed.get(AnyNode::Computation(*id)), Maybe::Present(_))),
            Computation::Project(_, pair) => matches!(self.placed.get(AnyNode::Computation(pair)), Maybe::Present(_)),
            Computation::Case { scrutinee, ref branches } => matches!(self.placed.get(AnyNode::Value(scrutinee)), Maybe::Present(_))
                            && branches.iter().all(|id| matches!(self.placed.get(AnyNode::Computation(*id)), Maybe::Present(_))),
        },
        captures: entry_len = record.0.len(),
        ensures: record.0.get(entry_len) == Some(&u8::from(match *computation {
            Computation::DataCase { equations, .. } => if equations == gandr_kernel_term::EquationCount::NONE { gandr_kernel_term::NODE_C_DATA_CASE } else { gandr_kernel_term::NODE_C_INDEXED_DATA_CASE },
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
            Computation::ListCase { .. } => gandr_kernel_term::NODE_C_LIST_CASE,
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
                equations,
            } => {
                if equations == gandr_kernel_term::EquationCount::NONE {
                    record.put_tag(gandr_kernel_term::NODE_C_DATA_CASE);
                    record.put_count(ComponentCount(branches.len()));
                }
                else {
                    record.put_tag(gandr_kernel_term::NODE_C_INDEXED_DATA_CASE);
                    record.put_count(ComponentCount(branches.len()));
                    record.put_count(ComponentCount(usize::from(equations)));
                }
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
            Computation::ListCase {
                list,
                on_nil,
                on_cons,
            } => {
                record.put_tag(gandr_kernel_term::NODE_C_LIST_CASE);
                for child in [
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
            Computation::With(ref components) => {
                record.put_tag(gandr_kernel_term::NODE_C_WITH);
                record.put_count(ComponentCount(components.len()));
                for component in components {
                    record.put_content(self.content_of(AnyNode::Computation(*component)));
                }
            },
            Computation::Project(component, pair) => {
                record.put_tag(gandr_kernel_term::NODE_C_PROJECT);
                record.put_count(ComponentCount(usize::from(component)));
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
            ValueType::Data { ref arguments, .. } => arguments.iter().all(|id| matches!(self.placed.get(AnyNode::Value(*id)), Maybe::Present(_))),
            ValueType::Record(ref fields) => fields.values().all(|id| matches!(self.placed.get(AnyNode::ValueType(*id)), Maybe::Present(_))),
            ValueType::Session { payloads, .. } => matches!(self.placed.get(AnyNode::ValueType(payloads)), Maybe::Present(_)),
            ValueType::PathUniverse(source, target) | ValueType::FlowUniverse(source, target) => matches!(self.placed.get(AnyNode::Value(source)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(target)), Maybe::Present(_)),
            ValueType::Path { domain, left, right } | ValueType::Flow { domain, source: left, target: right } | ValueType::Bridge { domain, left, right } => matches!(self.placed.get(AnyNode::ValueType(domain)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(left)), Maybe::Present(_)) && matches!(self.placed.get(AnyNode::Value(right)), Maybe::Present(_)),
            ValueType::Base(_) | ValueType::Universe { sort: GroundSort::Value, .. } | ValueType::Universe { sort: GroundSort::Computation, .. } | ValueType::Abstract(_) => true,
            ValueType::Product(ref parts) | ValueType::Sum(ref parts) => parts.iter().all(|id| matches!(self.placed.get(AnyNode::ValueType(*id)), Maybe::Present(_))),
            ValueType::StaticPi { domain: first, codomain: second } | ValueType::Sigma { first, second } => matches!(self.placed.get(AnyNode::ValueType(first)), Maybe::Present(_))
                            && matches!(self.placed.get(AnyNode::ValueType(second)), Maybe::Present(_)),
            ValueType::Thunk(body) => matches!(self.placed.get(AnyNode::CompType(body)), Maybe::Present(_)),
            ValueType::Lift { inner, .. } | ValueType::List(inner) | ValueType::Staged { base: inner, .. } => matches!(self.placed.get(AnyNode::ValueType(inner)), Maybe::Present(_)),
            ValueType::Element { code, .. } => matches!(self.placed.get(AnyNode::Value(code)), Maybe::Present(_)),
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
            CompType::Returner(result) => matches!(self.placed.get(AnyNode::ValueType(result)), Maybe::Present(_)),
            CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain } => matches!(self.placed.get(AnyNode::ValueType(domain)), Maybe::Present(_))
                            && matches!(self.placed.get(AnyNode::CompType(codomain)), Maybe::Present(_)),
            CompType::Element { code, .. } => matches!(self.placed.get(AnyNode::Value(code)), Maybe::Present(_)),
            CompType::With(ref components) => components.iter().all(|id| matches!(self.placed.get(AnyNode::CompType(*id)), Maybe::Present(_))),
            CompType::Codata { ref arguments, .. } => arguments.iter().all(|id| matches!(self.placed.get(AnyNode::Value(*id)), Maybe::Present(_))),
        },
        captures: entry_len = record.0.len(),
        ensures: record.0.get(entry_len) == Some(&u8::from(match *comp_type {
            CompType::Returner(..) => gandr_kernel_term::NODE_CT_RETURNER,
            CompType::Arrow { .. } => gandr_kernel_term::NODE_CT_ARROW,
            CompType::Pi { .. } => gandr_kernel_term::NODE_CT_PI,
            CompType::Element { .. } => gandr_kernel_term::NODE_CT_ELEMENT,
            CompType::With(..) => gandr_kernel_term::NODE_CT_WITH,
            CompType::Codata { .. } => gandr_kernel_term::NODE_CT_CODATA,
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
            CompType::With(ref components) => {
                record.put_tag(gandr_kernel_term::NODE_CT_WITH);
                record.put_count(ComponentCount(components.len()));
                for component in components {
                    record.put_content(self.content_of(AnyNode::CompType(*component)));
                }
            },
            CompType::Codata {
                declaration,
                ref arguments,
            } => {
                record.put_tag(gandr_kernel_term::NODE_CT_CODATA);
                record.put_count(ComponentCount(usize::from(declaration)));
                record.put_count(ComponentCount(arguments.len()));
                for argument in arguments {
                    record.put_content(self.content_of(AnyNode::Value(*argument)));
                }
            },
        }
    }
}

/// How `constants` names the constant at `index`: its name there, or its
/// position for an index past the end.
///
/// # Specification
/// trivial.
fn constant_name(
    constants: &[ConstantName],
    index: ConstantIndex,
) -> ConstantName
{
    constants
        .get(usize::from(index))
        .copied()
        .unwrap_or(ConstantName::Position)
}

/// Push `node`'s children as open tasks, in the order the format writes them.
///
/// # Specification
/// - requires: nothing; an unreadable node pushes nothing.
/// - ensures: pushes one open task per child, in the order the format writes
///   them, so each child is placed before the parent's record is built. A
///   reference to a constant `constants` names by its content has that
///   definition's declared type and body as its children.
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
/// - witness: `encoding::tests::a_definition_reference_reads_alike_in_either_admission_order`
#[spec(captures: entry_len = tasks.len(), ensures: tasks.get(entry_len..).is_some_and(|added| {
    let opened = added.iter().map(|task| match *task { EncodeTask::Open(node) => Some(node), EncodeTask::Close(_) => None });
    match node {
        AnyNode::Value(id) => match arena.value(id) { Some(matched_native_node) => match *matched_native_node {
Value::Constructor { datatype, ref fields, .. } => opened.eq((core::iter::once(AnyNode::ValueType(datatype)).chain(fields.iter().copied().map(AnyNode::Value))).map(Some)),
Value::Record(ref fields) => opened.eq((fields.values().copied().map(AnyNode::Value)).map(Some)),
Value::ListNil | Value::Variable(_) | Value::Literal(_) => opened.eq((core::iter::empty()).map(Some)),
Value::Constant(index) => match constant_name(constants, index) {
    ConstantName::Definition { declared, body, .. } => opened.eq([AnyNode::ValueType(declared), AnyNode::Value(body)].into_iter().map(Some)),
    ConstantName::Position => opened.eq((core::iter::empty()).map(Some)),
},
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
            Some(&Computation::ListCase { list, on_nil, on_cons }) => opened.eq([AnyNode::Value(list), AnyNode::Computation(on_nil), AnyNode::Computation(on_cons)].into_iter().map(Some)),
            Some(&Computation::DataCase {scrutinee,motive,ref branches,..}) => opened.eq(([AnyNode::Value(scrutinee), AnyNode::CompType(motive)].into_iter().chain(branches.iter().copied().map(AnyNode::Computation))).map(Some)),
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
            Some(&Computation::Bind(bound,body)) => opened.eq(([AnyNode::Computation(bound),AnyNode::Computation(body)].into_iter()).map(Some)),
            Some(&Computation::With(ref components)) => opened.eq((components.iter().copied().map(AnyNode::Computation)).map(Some)),
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
            Some(&CompType::With(ref components)) => opened.eq((components.iter().copied().map(AnyNode::CompType)).map(Some)),
            Some(&CompType::Codata {ref arguments,..}) => opened.eq((arguments.iter().copied().map(AnyNode::Value)).map(Some)),
        },
    }
}))]
fn push_children(
    arena: &TermArena,
    constants: &[ConstantName],
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
            None | Some(&Value::ListNil | &Value::Variable(_) | &Value::Literal(_)) => {},
            Some(&Value::Constant(index)) => match constant_name(constants, index) {
                ConstantName::Definition { declared, body, .. } => {
                    tasks.push(EncodeTask::Open(AnyNode::ValueType(declared)));
                    tasks.push(EncodeTask::Open(AnyNode::Value(body)));
                },
                ConstantName::Position => {},
            },
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
                ..
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
            Some(&Computation::ListCase {
                list,
                on_nil,
                on_cons,
            }) => {
                for child in [
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
            Some(&Computation::Bind(bound, body)) => {
                tasks.push(EncodeTask::Open(AnyNode::Computation(bound)));
                tasks.push(EncodeTask::Open(AnyNode::Computation(body)));
            },
            Some(&Computation::With(ref components)) => {
                tasks.extend(
                    components
                        .iter()
                        .copied()
                        .map(AnyNode::Computation)
                        .map(EncodeTask::Open),
                );
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
            Some(&CompType::With(ref components)) => {
                tasks.extend(
                    components
                        .iter()
                        .copied()
                        .map(AnyNode::CompType)
                        .map(EncodeTask::Open),
                );
            },
            Some(&CompType::Codata { ref arguments, .. }) => {
                tasks.extend((arguments.iter().copied().map(AnyNode::Value)).map(EncodeTask::Open));
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
        BaseType::Character => gandr_kernel_term::BASE_CHARACTER,
        BaseType::Float64 => gandr_kernel_term::BASE_FLOAT64,
        BaseType::Fixed(IntegerWidth::U32) => gandr_kernel_term::BASE_U32,
        BaseType::Fixed(IntegerWidth::U64) => gandr_kernel_term::BASE_U64,
        BaseType::Fixed(IntegerWidth::I32) => gandr_kernel_term::BASE_I32,
        BaseType::Fixed(IntegerWidth::I64) => gandr_kernel_term::BASE_I64,
    }
}

/// The format's literal kind for a width literal.
///
/// # Specification
/// trivial.
#[inline]
const fn fixed_kind(width: IntegerWidth) -> WireTag
{
    match width {
        IntegerWidth::U32 => gandr_kernel_term::LITERAL_U32,
        IntegerWidth::U64 => gandr_kernel_term::LITERAL_U64,
        IntegerWidth::I32 => gandr_kernel_term::LITERAL_I32,
        IntegerWidth::I64 => gandr_kernel_term::LITERAL_I64,
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
///   merely concatenate alike take different images; a floating-point literal
///   writes its bit pattern as one word, and a width literal its width's kind
///   and its bit pattern as a word.
/// - provides: the literal payload of a value record, which is where two
///   spellings of one number would otherwise become two content ids.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L3 — canonical literals enter. Kind, sign and final text
///   payload are executable; zero/one sign pairs and the numeric split pair
///   separate sign loss and ambiguous component framing, not every literal; a
///   character and the one-scalar string of the same scalar separate a kind tag
///   lost between the two, and one value at two widths and as an unbounded
///   integer separates a width lost from the key.
/// - witness: `encoding::tests::signed_zeroes_collapse_and_signed_ones_do_not`
/// - witness: `encoding::tests::the_length_prefix_separates_a_split_pair`
/// - witness: `encoding::tests::a_character_is_not_its_one_scalar_string`
/// - witness: `encoding::tests::a_width_literal_keys_by_its_width`
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
        Literal::Character(ref character) => record.0.get(entry_len) == Some(&u8::from(gandr_kernel_term::LITERAL_CHARACTER))
            && record.0.ends_with(character.to_text().as_bytes()),
        Literal::Float64(_) => record.0.get(entry_len) == Some(&u8::from(gandr_kernel_term::LITERAL_FLOAT64)),
        Literal::Fixed(fixed) => record.0.get(entry_len) == Some(&u8::from(fixed_kind(fixed.width()))),
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
        Literal::Character(ref character) => {
            record.put_tag(gandr_kernel_term::LITERAL_CHARACTER);
            record.put_text(EncodedText(character.to_text().as_str()));
        },
        Literal::Float64(float) => {
            record.put_tag(gandr_kernel_term::LITERAL_FLOAT64);
            record.put_word(EncodedWord(u64::from(float)));
        },
        Literal::Fixed(fixed) => {
            record.put_tag(fixed_kind(fixed.width()));
            record.put_word(EncodedWord(u64::from(fixed)));
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
    && matches!(table.placed.get(goal.subject()), Maybe::Present(_))
    && match goal.expected() {
        Maybe::Present(node) => matches!(table.placed.get(node), Maybe::Present(_)),
        Maybe::Absent(_) => true,
    }
    && telescope.types().iter().all(|&entry| matches!(table.placed.get(AnyNode::ValueType(entry)), Maybe::Present(_))))]
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
    && matches!(table.placed.get(goal.subject()), Maybe::Present(_))
    && match goal {
        RewriteGoal::Shift { .. } | RewriteGoal::Abstract { .. } => true,
        RewriteGoal::Substitute { replacement, .. } => matches!(table.placed.get(AnyNode::Value(replacement)), Maybe::Present(_)),
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

/// The name of a plain definition of `declared` and `body` about to be
/// admitted after `entries`: its two roots and its rank among the earlier
/// definitions named by the same two, each constant they reach read by its
/// position.
///
/// # Specification
/// - requires: the roots, and those of every definition `entries` names by
///   content, live in `arena`.
/// - ensures: a definition name over `declared` and `body`, ranked by the
///   earlier entries whose declared types and bodies are identical in reachable
///   content. A digest filters the entries and one table decides each
///   candidate, so no digest decides.
/// - provides: admission's naming of a plain definition, injective on the
///   environment's positions.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two definitions of one type and body admitted into one
///   environment are ranked apart; the predicate checks the roots kept.
/// - witness: `encoding::tests::two_definitions_of_one_content_keep_two_names`
#[must_use]
#[spec(ensures: |ret| matches!(ret, ConstantName::Definition { declared: kept_declared, body: kept_body, .. }
    if kept_declared == declared && kept_body == body))]
pub(crate) fn name_definition(
    arena: &TermArena,
    entries: &crate::env::Entries,
    declared: ValueTypeId,
    body: ValueId,
) -> ConstantName
{
    let digest = {
        let mut table = ContentTable::new();
        let _declared = table.place(arena, AnyNode::ValueType(declared));
        let _body = table.place(arena, AnyNode::Value(body));
        table.stream().digest()
    };
    let rank = entries
        .iter()
        .filter(|entry| match entry.key_name() {
            ConstantName::Definition {
                declared: earlier_declared,
                body: earlier_body,
                digest: earlier_digest,
                ..
            } => {
                earlier_digest == digest && {
                    let mut table = ContentTable::new();
                    table.place(arena, AnyNode::ValueType(declared))
                        == table.place(arena, AnyNode::ValueType(earlier_declared))
                        && table.place(arena, AnyNode::Value(body))
                            == table.place(arena, AnyNode::Value(earlier_body))
                }
            },
            ConstantName::Position => false,
        })
        .count();
    ConstantName::Definition {
        declared,
        body,
        rank: DefinitionRank(rank),
        digest,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_kernel_term::AnyNode;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::FractionDigits;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::NumericLiteral;
    use gandr_kernel_term::Sign;
    use gandr_kernel_term::StringLiteral;
    use gandr_kernel_term::TermArena;
    use quenchant_shape::shape::Maybe;

    use super::BinderDepth;
    use super::ContentEncoding;
    use super::ContentId;
    use super::ContentTable;
    use super::EncodedWord;
    use super::PlacementCount;
    use super::Placements;
    use super::RewriteGoal;
    use super::SupportGoal;
    use super::Telescope;
    use super::content_digest;
    use super::encode_rewrite;
    use super::placement;
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

    /// Trap pair — **a character beside its one-scalar string**. The two
    /// payloads are the same UTF-8 bytes, so only the kind tag keys them
    /// apart; one character spelled twice keys alike.
    #[test]
    fn a_character_is_not_its_one_scalar_string()
    {
        let mut arena = TermArena::new();
        let character =
            |scalar| Literal::Character(gandr_kernel_term::CharacterLiteral::from(scalar));
        let letter = arena.value_literal(character('é'));
        let again = arena.value_literal(character('é'));
        let string = arena.value_literal(text(String::from("é")));
        let other = arena.value_literal(character('e'));
        let mut table = ContentTable::new();
        let mut key = |value| {
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(value),
                Telescope::Whole(&[]),
            )
        };
        let letter = key(letter);
        assert_eq!(letter, key(again), "one character has one key");
        assert_ne!(
            letter,
            key(string),
            "the character is not its one-scalar string"
        );
        assert_ne!(letter, key(other), "and the scalar is in the key");
    }

    /// Trap pair — **one value at two widths**. `1u32`, `1i32`, `1u64` and the
    /// unbounded `1` share a value, so only the kind keys them apart; `-1i32`
    /// and `4294967295u32` share a bit pattern, so the kind keys them apart
    /// too.
    #[test]
    fn a_width_literal_keys_by_its_width()
    {
        use gandr_kernel_term::FixedInteger;
        let mut arena = TermArena::new();
        let fixed = |literal| Literal::Fixed(literal);
        let one = gandr_kernel_term::Magnitude::from_decimal_text(String::from("1"))
            .expect("one is decimal");
        let values = [
            arena.value_literal(fixed(FixedInteger::U32(1))),
            arena.value_literal(fixed(FixedInteger::I32(1))),
            arena.value_literal(fixed(FixedInteger::U64(1))),
            arena.value_literal(fixed(FixedInteger::I64(1))),
            arena.value_literal(Literal::Integer(gandr_kernel_term::IntegerLiteral::new(
                Sign::NonNegative,
                one,
            ))),
            arena.value_literal(fixed(FixedInteger::I32(-1))),
            arena.value_literal(fixed(FixedInteger::U32(u32::MAX))),
        ];
        let again = arena.value_literal(fixed(FixedInteger::U32(1)));
        let mut table = ContentTable::new();
        let mut key = |value| {
            support_key(
                &mut table,
                &arena,
                SupportGoal::SynthValue(value),
                Telescope::Whole(&[]),
            )
        };
        let keys: alloc::vec::Vec<_> = values.into_iter().map(&mut key).collect();
        assert_eq!(
            keys.first(),
            Some(&key(again)),
            "one width literal has one key"
        );
        for (index, left) in keys.iter().enumerate() {
            for right in keys.iter().skip(index.saturating_add(1)) {
                assert_ne!(left, right, "a width or a kind is lost from the key");
            }
        }
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
        assert_ne!(second, third, "nor a third filed beside them");
        assert_eq!(
            admit(&mut table, 0x03),
            third,
            "the last filed is found again"
        );
        assert_eq!(admit(&mut table, 0x01), first, "and so is the first");
        assert_eq!(admit(&mut table, 0x02), second, "and the one between");
        assert_eq!(table.records, 3_u64, "and asking again adds no record");
    }

    #[test]
    fn placements_keep_families_and_pages_apart()
    {
        let mut arena = TermArena::new();
        let values: Vec<_> = (0_u32 .. 600)
            .map(|index| arena.value_variable(DeBruijnIndex::from(index)))
            .collect();
        let first_type = arena.value_type_unit();
        let (Some(&first_value), Some(&far_value)) = (values.first(), values.get(599))
        else {
            panic!("six hundred values were minted");
        };
        let mut placements = Placements::default();
        let near = AnyNode::Value(first_value);
        let far = AnyNode::Value(far_value);
        let other_family = AnyNode::ValueType(first_type);
        assert_eq!(
            near.offset(),
            other_family.offset(),
            "one offset, two families"
        );
        placements.insert(near, ContentId(10));
        placements.insert(far, ContentId(20));
        assert_eq!(placements.get(near), Maybe::Present(ContentId(10)));
        assert_eq!(placements.get(far), Maybe::Present(ContentId(20)));
        assert_eq!(
            placements.get(other_family),
            Maybe::Absent(placement::Absent::Unplaced),
            "a family's column is its own"
        );
        assert_eq!(placements.count(), PlacementCount(2));
        placements.insert(far, ContentId(30));
        assert_eq!(placements.get(far), Maybe::Present(ContentId(30)));
        assert_eq!(
            placements.count(),
            PlacementCount(2),
            "placing a node again counts it once"
        );
        placements.insert(other_family, ContentId(40));
        assert_eq!(placements.get(near), Maybe::Present(ContentId(10)));
        assert_eq!(placements.count(), PlacementCount(3));
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
        assert_eq!(table.placed.count(), PlacementCount(17));
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
        assert_eq!(table.placed.count(), PlacementCount(17));
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
        assert_eq!(table.placed.count(), PlacementCount(34));
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
            (table.records, table.placed.count()),
            (0_u64, PlacementCount(0)),
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

    /// Where a naming fixture admits its referent beside the unrelated pair.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum ReferentOrder
    {
        /// The referent, then the pair.
        First,
        /// The pair, then the referent.
        Second,
    }

    /// Admit `referent` and a pair definition in `order`, then
    /// `c : Unit = referent`; return the record stream a table told the
    /// environment's entries builds for `c`'s body.
    ///
    /// # Specification
    /// - requires: `referent` admits one declaration at the unit type.
    /// - ensures: the stream of every record `c`'s body reaches, in the order
    ///   the walk assigns them.
    /// - provides: the admission-order fixtures the constant naming cases
    ///   compare.
    /// - fails: never.
    /// - panics: when an admission refuses.
    /// - executable: none — the cases compare two calls' streams, which no
    ///   single call's predicate states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition and an axiom referent each admitted
    ///   before and after an unrelated definition.
    /// - witness: `encoding::tests::a_definition_reference_reads_alike_in_either_admission_order`
    /// - witness: `encoding::tests::an_axiom_reference_keeps_its_position`
    fn reference_stream(
        referent: &dyn Fn(&mut crate::env::Environment) -> ConstantIndex,
        order: ReferentOrder,
    ) -> ContentEncoding
    {
        let mut environment = crate::env::Environment::new();
        let pair = |environment: &mut crate::env::Environment| {
            let mut staging = environment.stage();
            let unit = staging.arena().value_type_unit();
            let declared = staging.arena().value_type_product(&[unit, unit]);
            let one = staging.arena().value_unit();
            let body = staging.arena().value_tuple(&[one, one]);
            let staged = staging.def(LevelSignature::monomorphic(), declared, body);
            environment.add_decl(staged).expect("the pair admits")
        };
        let reached = match order {
            ReferentOrder::First => {
                let reached = referent(&mut environment);
                let _pair = pair(&mut environment);
                reached
            },
            ReferentOrder::Second => {
                let _pair = pair(&mut environment);
                referent(&mut environment)
            },
        };
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_unit();
        let reference = staging.arena().value_constant(reached);
        let staged = staging.def(LevelSignature::monomorphic(), declared, reference);
        let _c = environment.add_decl(staged).expect("the reference admits");
        let mut table = ContentTable::new();
        table.name_constants(environment.entries());
        let _id = table.place(environment.arena(), AnyNode::Value(reference));
        table.stream().clone()
    }

    /// Admit `name : Unit = ()`.
    ///
    /// # Specification
    /// - ensures: the definition's position.
    /// - provides: the plain definition the naming cases reference.
    /// - fails: never.
    /// - panics: when the admission refuses.
    /// - executable: none — the position is the environment's, which the cases
    ///   read back through its entries.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the unit definition admits in every environment.
    /// - witness: `encoding::tests::a_definition_reference_reads_alike_in_either_admission_order`
    /// - witness: `encoding::tests::two_definitions_of_one_content_keep_two_names`
    fn unit_definition(environment: &mut crate::env::Environment) -> ConstantIndex
    {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_unit();
        let body = staging.arena().value_unit();
        let staged = staging.def(LevelSignature::monomorphic(), declared, body);
        environment
            .add_decl(staged)
            .expect("the unit definition admits")
            .position()
    }

    #[test]
    fn a_definition_reference_reads_alike_in_either_admission_order()
    {
        let first = reference_stream(&unit_definition, ReferentOrder::First);
        let second = reference_stream(&unit_definition, ReferentOrder::Second);
        assert_eq!(
            first, second,
            "a plain definition's reference reads its content, not where it was admitted"
        );
    }

    #[test]
    fn an_axiom_reference_keeps_its_position()
    {
        let axiom = |environment: &mut crate::env::Environment| {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let staged = staging.axiom(LevelSignature::monomorphic(), declared);
            environment
                .add_decl(staged)
                .expect("the axiom admits")
                .position()
        };
        let first = reference_stream(&axiom, ReferentOrder::First);
        let second = reference_stream(&axiom, ReferentOrder::Second);
        assert_ne!(
            first, second,
            "an axiom has no body to name it by, so its reference reads its position"
        );
    }

    #[test]
    fn two_definitions_of_one_content_keep_two_names()
    {
        let mut environment = crate::env::Environment::new();
        let left = unit_definition(&mut environment);
        let right = unit_definition(&mut environment);
        let ranks = [left, right].map(|position| {
            match environment
                .entries()
                .get(usize::from(position))
                .map(crate::env::AdmittedDeclaration::key_name)
            {
                Some(super::ConstantName::Definition { rank, .. }) => rank,
                Some(super::ConstantName::Position) | None => {
                    panic!("a plain definition is named by its content")
                },
            }
        });
        assert_eq!(
            ranks,
            [super::DefinitionRank(0), super::DefinitionRank(1)],
            "the second definition of one type and body is ranked behind the first"
        );
        let mut staging = environment.stage();
        let left = staging.arena().value_constant(left);
        let right = staging.arena().value_constant(right);
        let unit = staging.arena().value_type_unit();
        let declared = staging.arena().value_type_product(&[unit, unit]);
        let pair = staging.arena().value_tuple(&[left, right]);
        let staged = staging.def(LevelSignature::monomorphic(), declared, pair);
        let _pair = environment
            .add_decl(staged)
            .expect("the pair of references admits");
        let mut table = ContentTable::new();
        table.name_constants(environment.entries());
        assert_ne!(
            table.place(environment.arena(), AnyNode::Value(left)),
            table.place(environment.arena(), AnyNode::Value(right)),
            "two definitions keep two names however alike their content: a key \
             never answers for one with the other"
        );
    }
}
