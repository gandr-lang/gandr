//! The deterministic encoder: an admission-ordered declaration sequence over
//! one arena, written as canonical bytes.
//!
//! # The subterm table, and what makes it canonical
//!
//! Each declaration segment carries a **subterm table** rather than an expanded
//! tree. Nodes are interned bottom-up, children before parents, with
//! **content-keyed deduplication**: a node's key is its own encoded entry bytes
//! — the node tag, its children's already-assigned global indices, and its
//! canonical inline payload — so two structurally equal nodes collapse to one
//! global index whether they were shared within a declaration, shared across
//! declarations, or merely coincident. Because children are already indices the
//! key does not recursively embed child entries. Tree-map lookups still have
//! logarithmic cost, and key comparisons and serialization depend on payload
//! byte lengths as well as the number of nodes.
//!
//! Deduplication is content-keyed and **never id-keyed**, and the reason is a
//! canonicality property rather than a performance one: an id-keyed
//! deduplication would make the bytes depend on decode history, and the bytes
//! must be a function of the abstract environment alone.
//!
//! The first completion of a node assigns the next free global index and
//! appends its entry to the *current* declaration's segment; a later occurrence
//! reuses the index without appending. That is **post-order first-completion
//! order**. The fixed child traversal selects one topological order; other
//! child-before-parent orders exist but are not this encoder’s canonical
//! order. Earlier-child indices make the table streaming-decodable.
//!
//! # The walk is sharing-aware, and that is load-bearing twice
//!
//! An arena node is visited once, memoized by id, so re-encoding a decoded DAG
//! avoids walking the expanded tree. That matters for
//! the encoder's own cost, and it matters more for the decoder, which uses this
//! encoder as its canonical-form oracle: **a re-encoder that walked the graph
//! as a tree would itself be an amplification vector**, turning the defence
//! into the vulnerability.
//!
//! # The encoder is untrusted
//!
//! It feeds no typing judgement and is not an admission fast path. The
//! decoder validates framing and budgets, then compares the input with this
//! encoder’s output. That checks agreement with this implementation, not an
//! independent proof of the wire format; shared encoder/decoder mistakes need
//! independent wire fixtures to expose them.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — background: §
//!   kernel-verdict-reuse — a verdict key reads each declaration's segment as
//!   [`keyed_segment`] writes it, so the canonical bytes are the key's input.
//! - `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — newest: §
//!   storage-programme-gluing — a reference names its target by content, so
//!   [`encode_named`] writes each named place by its content key, and each
//!   entry of an earlier segment by that segment's place and its offset there.

use alloc::alloc::Global;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;

use anodized::spec;
use gandr_kernel_data::Shared;
use gandr_kernel_data::SmallVec;
use gandr_kernel_data::ThinShared;
use gandr_kernel_strata::ConstraintRelation;
use gandr_kernel_strata::Level;
use quenchant_shape::shape::Maybe;

use crate::Declaration;
use crate::arena::AnyNode;
use crate::arena::TermArena;
use crate::base::BaseType;
use crate::base::IntegerWidth;
use crate::base::Literal;
use crate::base::Sign;
use crate::budget::GlobalIndex;
use crate::decl::AdmissionMark;
use crate::decl::DeclarationContent;
use crate::decl::LevelSignature;
use crate::decl::MarkedDeclaration;
use crate::decl::MintedAtom;
use crate::decl::SealExtent;
use crate::decl::SealScope;
use crate::decl::StructuredName;
use crate::error::MalformedSite;
use crate::tags;
use crate::term::Computation;
use crate::term::ConstantIndex;
use crate::term::Value;
use crate::types::CompType;
use crate::types::GroundSort;
use crate::types::ValueType;
use crate::wire::ArtifactImage;
use crate::wire::ArtifactText;
use crate::wire::ByteCount;
use crate::wire::EncodedArtifact;
use crate::wire::WireTag;
use crate::wire::WireU64;
use crate::wire::WireUsize;

/// The canonical bytes of one encoded subterm-table entry, which are also its
/// deduplication key.
///
/// # Specification
/// - requires: the encoder supplies the state described by the consuming
///   operations.
/// - ensures: retains candidate entry bytes as a shallow lexicographic content
///   key; this wrapper does not validate entry completeness.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; new and
///   interning or entry-encoding operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 observes literal entry bytes for every frozen former, every
///   base atom, both injection sides, nonzero inline levels and distinguishable
///   one-, two- and three-child index sequences crossing varint boundaries.
///   This separates tag reassignment, child permutation, missing payloads and
///   lost high bits. It covers live nodes and supplied global assignments, not
///   formation or inputs outside the live, acyclic graph domain.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct EncodedEntry(EncodedArtifact);

/// An entry's bytes beside the key of each named place the bytes write, in the
/// order they write them: what the content deduplication compares. The bytes
/// write each named place by its first place among those keys, and never by
/// its segment's table of names. So equal content in two segments is one
/// entry, and equal bytes that name two places stay two.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct EntryContent
{
    /// The entry's bytes, each named place written by its first place among
    /// `names`.
    bytes: EncodedEntry,
    /// The key of each named place the bytes write, in order.
    names: Box<[ConstantKey]>,
}

/// What an encoding of a sequence's leading declarations assigned, frozen for
/// every encoding that resumes after them.
///
/// # Specification
/// - requires: built from an interner that continued none, once its
///   declarations are written.
/// - ensures: holds that interner's node memo, its content deduplication and
///   its next free global index.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary;
///   [`encode_prefix`] builds it and [`Interner::after`] reads it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`encode_after`].
/// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
#[derive(Debug)]
struct Assigned
{
    /// Arena node to its assigned global index.
    by_node: BTreeMap<AnyNode, GlobalIndex>,
    /// Entry content to its global index.
    by_content: BTreeMap<EntryContent, GlobalIndex>,
    /// The next free global index.
    next: GlobalIndex,
    /// The first global index of each segment, by place.
    bases: SmallVec<GlobalIndex, 0, Global>,
}

/// The content-keyed subterm interner, carrying the global index counter and
/// both memos across declaration segments.
///
/// # Specification
/// - requires: the encoder supplies the state described by the consuming
///   operations.
/// - ensures: retains node memoization and byte-content deduplication across
///   segments with a saturating global counter; it belongs to one unchanged
///   arena. An interner that continues the frozen assignments of a leading run
///   answers from both, and records only what it assigns itself.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; new and
///   interning or entry-encoding operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 observes exact segment entries, assigned indices and memo
///   state across repeated ids, distinct equal nodes, a new parent, a second
///   segment and reversed children. This separates id-keyed deduplication, memo
///   loss, redundant entries and incorrect post-order assignment. Deep and
///   differently shared integration fixtures supplement these bounded
///   transitions; a shared encode/decode round trip is not an independent
///   format oracle.
/// - witness: `encode::tests::interning_reuses_content_across_segments_without_losing_order`
/// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
/// - witness: `tests::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
/// - witness: `tests::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
#[derive(Clone, Debug)]
struct Interner
{
    /// The frozen assignments of an encoding of the sequence's leading
    /// declarations, which this one continues; none for a whole encoding.
    base: Option<Shared<Assigned, Global>>,
    /// Arena node to its assigned global index: the sharing-aware memo, so an
    /// in-arena shared node is walked once.
    by_node: BTreeMap<AnyNode, GlobalIndex>,
    /// Entry content to its global index: the content deduplication, so
    /// structurally equal nodes collapse.
    by_content: BTreeMap<EntryContent, GlobalIndex>,
    /// The next free global index.
    next: GlobalIndex,
    /// How the segments write an admission position.
    positions: Positions,
    /// Where the current segment's references stand.
    frame: Frame,
}

/// Where the current segment's references stand: its own entries from its
/// base on, and the entries of earlier segments it reads through its imports.
///
/// A reference to an entry of the segment is twice the entry's offset from the
/// base. A reference to an entry of an earlier segment is one more than twice
/// its import's place in `imports`, and the import names that segment's place
/// and the entry's offset inside it. So a reference reads no global index, and
/// an insertion before the segment moves none of its bytes.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default)]
struct Frame
{
    /// The first global index of each segment this interner wrote, in order,
    /// past the segments of its base.
    bases: SmallVec<GlobalIndex, 0, Global>,
    /// The current segment's first global index.
    base: GlobalIndex,
    /// The entries of earlier segments that the current segment reads, first
    /// read first: each one's segment by its place, and its offset there.
    imports: SmallVec<(usize, u32), 0, Global>,
    /// The place in `imports` of each entry the current segment reads, by
    /// global index, beside the count of the segment that read it: a place of
    /// an earlier segment is stale. A slot for each entry keeps the lookup to
    /// one load, and a segment allocates nothing to forget the reads before it.
    imported: SmallVec<(usize, usize), 0, Global>,
}

/// How a segment writes an admission position.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
enum Positions
{
    /// Each position as an artifact's segment writes it: by the key of its
    /// place in the segment's table of names, or by its place.
    Artifact(Placing),
    /// Each position by where the segment first names it, so the bytes read
    /// no admission order.
    Ordinal(Ordinals),
}

impl Default for Positions
{
    /// Each position as its own place, with no place named.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the empty names, setup.
    #[inline]
    fn default() -> Self
    {
        Self::Artifact(Placing::default())
    }
}

/// How an artifact's segments write each admission position.
///
/// A position stands at its place: the position itself, or its place in rank
/// order in the export of a kept environment. A place that `names` names is
/// written as twice the entry of its key in the segment's table of names. Any
/// other place is written as one more than twice the place.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default)]
struct Placing
{
    /// The place of each position in rank order; none when each position is
    /// its own place.
    places: Option<Places>,
    /// The key of each place.
    names: Names,
    /// The keys the current segment names, first named first.
    table: SmallVec<ConstantKey, 0, Global>,
    /// The entry in `table` of each named place's key, by place, beside the
    /// count of the segment that wrote it: an entry of an earlier segment is
    /// stale. A slot for each place keeps the lookup to one load, and a
    /// segment allocates nothing to forget the entries before it.
    entries: SmallVec<(usize, usize), 0, Global>,
    /// The count of the segments opened, which marks the current segment's
    /// entries.
    segment: usize,
    /// The keys the entry being written names, in order.
    named: SmallVec<ConstantKey, 0, Global>,
    /// How the entry being written names a key.
    naming: EntryNaming,
}

/// How an entry being written names a key.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum EntryNaming
{
    /// By its entry in the segment's table of names, as the segment writes it.
    #[default]
    Table,
    /// By its first place among the entry's own keys, as the content
    /// deduplication compares it; the segment's table stays as it is.
    Local,
}

/// The place of each live admission position in rank order: what the export
/// of a kept environment writes for each position it names.
///
/// A kept environment holds retired positions, and positions whose order is
/// not their rank order. Its export writes each live position as its place
/// in rank order. Thus it writes the artifact that a fresh admission of the
/// same source writes, and a replay admits each declaration at its place.
///
/// # Specification
/// - requires: built by [`Places::new`].
/// - ensures: answers the place [`Places::new`] gives each position, and no
///   place for any other position.
/// - panics: none.
/// - executable: none — the field is private and set only by [`Places::new`],
///   whose specification states it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`encode_placed`].
/// - witness: `encode::tests::a_placed_encoding_writes_each_position_as_its_place_6845`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Places(ThinShared<(), Option<ConstantIndex>, Global>);

impl Places
{
    /// The places of `order`, the live positions in rank order, among the
    /// first `length` positions.
    ///
    /// # Specification
    /// - requires: each position of `order` is below `length`, and no position
    ///   repeats.
    /// - ensures: each position of `order` has its index in `order` as its
    ///   place; no other position has a place.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the places of the first `length` positions, growth within
    ///   `length`
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`encode_placed`].
    /// - witness: `encode::tests::a_placed_encoding_writes_each_position_as_its_place_6845`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| usize::from(length) == ret.0.len())]
    pub fn new<Order>(
        order: Order,
        length: ConstantIndex,
    ) -> Self
    where
        Order: IntoIterator<Item = ConstantIndex>,
    {
        let mut places =
            SmallVec::<_, 0, Global>::from_iter(core::iter::repeat_n(None, usize::from(length)));
        for (place, position) in order.into_iter().enumerate() {
            if let Some(slot) = places.get_mut(usize::from(position)) {
                *slot = Some(ConstantIndex::from(place));
            }
        }
        Self(ThinShared::from_header_and_iter((), places))
    }

    /// The place of `position` in rank order, or none for a position with no
    /// place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn place(
        &self,
        position: ConstantIndex,
    ) -> Option<ConstantIndex>
    {
        self.0.get(usize::from(position)).copied().flatten()
    }
}

/// The width of a [`ConstantKey`]: a whole content key.
pub const CONSTANT_KEY_LEN: usize = 32;

/// The least width of a key in a segment's table of names: one word, which a
/// decoder compares in one load.
pub const KEY_WIDTH_FLOOR: usize = 8;

/// The content key of a constant, as the table of names at the head of a
/// segment holds it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstantKey([u8; CONSTANT_KEY_LEN]);

impl From<[u8; CONSTANT_KEY_LEN]> for ConstantKey
{
    /// The key with these bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; CONSTANT_KEY_LEN]) -> Self
    {
        Self(bytes)
    }
}

impl From<ConstantKey> for [u8; CONSTANT_KEY_LEN]
{
    /// The key's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(key: ConstantKey) -> Self
    {
        key.0
    }
}

impl AsRef<[u8]> for ConstantKey
{
    /// The key's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// The key of each place of an artifact: what its segments write in the
/// place of an admission position.
///
/// A key names the first place that holds it. A later place that holds the
/// same key is not named, so the segments write it by the place itself, and a
/// place never loses its key to a place after it.
///
/// # Specification
/// - requires: built by [`Names::new`].
/// - ensures: answers each place the key that names it alone, and each such key
///   its place.
/// - panics: none.
/// - executable: none — the fields are private and set only by [`Names::new`],
///   whose specification states them.
///
/// # Adequacy
/// - hypothesis: L3 — as [`encode_named`].
/// - witness: `encode::tests::a_named_encoding_writes_each_named_place_by_its_key_7340`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Names
{
    /// The key of each place as given, a repeat included.
    keys: ThinShared<(), Option<ConstantKey>, Global>,
    /// The key that names each place alone: none for a place with no key or
    /// with the key of an earlier place.
    named: ThinShared<(), Option<ConstantKey>, Global>,
    /// Each distinct key beside the first place that holds it, in the order of
    /// the keys: one contiguous run that a binary search reads, which a prefix
    /// of a table entry resolves against.
    places: ThinShared<(), (ConstantKey, ConstantIndex), Global>,
    /// How many first bytes keep its keys apart: one more than the longest run
    /// of first bytes that two of its keys share, or none for fewer than two.
    apart: usize,
}

impl Names
{
    /// The names of an artifact whose place `n` has the `n`th of `keys`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each place is named by its key unless an earlier place holds
    ///   the same key; no other place is named. Each place's key is held as
    ///   given. The width keeps the distinct keys apart.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the names hold private maps, which a clause would
    ///   restate.
    ///
    /// # Cost
    /// - allocation: the keys, the key that names each place and the first
    ///   places, growth within the places.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`encode_named`].
    /// - witness: `encode::tests::a_named_encoding_writes_each_named_place_by_its_key_7340`
    #[inline]
    #[must_use]
    pub fn new<Keys>(keys: Keys) -> Self
    where
        Keys: IntoIterator<Item = Option<ConstantKey>>,
    {
        let keys: ThinShared<(), Option<ConstantKey>, Global> = keys.into_iter().collect();
        let mut places: SmallVec<(ConstantKey, ConstantIndex), 0, Global> = keys
            .iter()
            .enumerate()
            .filter_map(|(place, key)| key.map(|key| (key, ConstantIndex::from(place))))
            .collect();
        // A stable sort keeps the first place of each key before its repeats,
        // and the deduplication keeps that first place alone.
        places.sort_by_key(|&(key, _)| key);
        let mut last = None;
        places.retain(|&(key, _)| last.replace(key) != Some(key));
        let apart = places
            .windows(2)
            .filter_map(|pair| {
                let (first, second) = (pair.first()?, pair.get(1)?);
                Some(
                    first
                        .0
                        .0
                        .iter()
                        .zip(&second.0.0)
                        .take_while(|&(left, right)| left == right)
                        .count()
                        .saturating_add(1),
                )
            })
            .max()
            .unwrap_or_default();
        let mut named: SmallVec<Option<ConstantKey>, 0, Global> =
            core::iter::repeat_n(None, keys.len()).collect();
        for &(key, place) in &places {
            if let Some(slot) = named.get_mut(usize::from(place)) {
                *slot = Some(key);
            }
        }
        Self {
            keys,
            named: named.into(),
            places: places.into(),
            apart,
        }
    }

    /// The names of an artifact whose place `n` has the `n`th of `keys`, when
    /// every place has a key; otherwise no place is named.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Names::new`] of `keys` when each holds a key, and the names
    ///   of no place when one holds none.
    /// - provides: the names an export writes. A store keeps an artifact named
    ///   whole or bare, so a writer names each place or none.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Names::new`].
    ///
    /// # Cost
    /// - allocation: the keys and their first places, growth within the places.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an export with a place the kernel keys not writes
    ///   every place bare, and one with every place keyed names each.
    /// - witness: `encode::tests::a_named_encoding_writes_each_named_place_by_its_key_7340`
    #[inline]
    #[must_use]
    pub fn whole<Keys>(keys: Keys) -> Self
    where
        Keys: IntoIterator<Item = Option<ConstantKey>>,
    {
        keys.into_iter()
            .collect::<Option<SmallVec<ConstantKey, 0, Global>>>()
            .map_or_else(Self::default, |keys| Self::new(keys.into_iter().map(Some)))
    }

    /// The key of each place as given, a repeat included.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn keys(&self) -> &[Option<ConstantKey>]
    {
        &self.keys
    }

    /// The key that names `place` alone, if one does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn key(
        &self,
        place: ConstantIndex,
    ) -> Option<ConstantKey>
    {
        self.named.get(usize::from(place)).copied().flatten()
    }

    /// The place that `key` names, if it names one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn place(
        &self,
        key: &ConstantKey,
    ) -> Option<ConstantIndex>
    {
        self.places
            .binary_search_by(|entry| entry.0.cmp(key))
            .ok()
            .and_then(|at| self.places.get(at))
            .map(|&(_, place)| place)
    }

    /// The width of a key in each table of names of an artifact under these
    /// names: the least from one word up that keeps the distinct keys apart.
    ///
    /// # Specification
    /// - ensures: at least [`KEY_WIDTH_FLOOR`] and at most
    ///   [`CONSTANT_KEY_LEN`]; no two distinct keys share that many first
    ///   bytes, and two share one byte fewer unless the width is the floor.
    /// - panics: none.
    /// - executable: none — the width reads the names' private keys, which a
    ///   clause would restate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — names whose keys share their first word write a wider
    ///   table, and the decoder resolves it.
    /// - witness: `encode::tests::keys_that_share_a_word_widen_every_table_7340`
    #[inline]
    pub(crate) fn width(&self) -> ByteCount
    {
        ByteCount::from(self.apart.clamp(KEY_WIDTH_FLOOR, CONSTANT_KEY_LEN))
    }

    /// The place of the one key that begins with `prefix`.
    ///
    /// # Specification
    /// - requires: `prefix` is no longer than a key.
    /// - ensures: the first place of the one key that begins with `prefix`;
    ///   refused as [`MalformedSite::UnplacedName`] when no key does, and as
    ///   [`MalformedSite::SharedPrefix`] when two do.
    /// - panics: none.
    /// - executable: none — the place reads the names' private keys, which a
    ///   clause would restate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a table entry that begins two names is refused, and
    ///   one that begins none.
    /// - witness: `encode::tests::keys_that_share_a_word_widen_every_table_7340`
    #[expect(
        clippy::big_endian_bytes,
        reason = "the keys sort by their bytes, so a first word read big-endian sorts as its key"
    )]
    #[inline]
    pub(crate) fn place_of_prefix(
        &self,
        prefix: ArtifactImage<'_>,
    ) -> Result<ConstantIndex, MalformedSite>
    {
        let prefix = prefix.as_ref();
        // The keys stand in order, so those that begin with `prefix` form one
        // run. A key's first word, read big-endian, keeps that order, so the
        // search compares one integer for each key it visits.
        let Some(head) = prefix
            .first_chunk::<KEY_WIDTH_FLOOR>()
            .map(|word| u64::from_be_bytes(*word))
        else {
            return Err(MalformedSite::UnplacedName);
        };
        let tail = prefix.get(KEY_WIDTH_FLOOR ..).unwrap_or_default();
        let first_word = |key: &ConstantKey| {
            key.0
                .first_chunk::<KEY_WIDTH_FLOOR>()
                .map_or(0, |word| u64::from_be_bytes(*word))
        };
        let from = self
            .places
            .partition_point(|entry| first_word(&entry.0) < head);
        let mut begun = self
            .places
            .get(from ..)
            .unwrap_or_default()
            .iter()
            .take_while(|entry| first_word(&entry.0) == head)
            .filter(|entry| {
                entry
                    .0
                    .0
                    .get(KEY_WIDTH_FLOOR ..)
                    .is_some_and(|rest| rest.starts_with(tail))
            })
            .map(|&(_, place)| place);
        match (begun.next(), begun.next()) {
            (Some(place), None) => Ok(place),
            (None, _) => Err(MalformedSite::UnplacedName),
            (Some(_), Some(_)) => Err(MalformedSite::SharedPrefix),
        }
    }
}

/// The positions a keyed segment names, in the order it first names them,
/// and the mutual block whose members it names by their place in it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
struct Ordinals
{
    /// The positions named outside the block, first named first.
    named: SmallVec<ConstantIndex, 0, Global>,
    /// Each of them, to its place in `named`.
    places: BTreeMap<ConstantIndex, usize>,
    /// The members of the block the declaration belongs to.
    block: core::ops::Range<ConstantIndex>,
}

impl Positions
{
    /// The position a segment writes for `position`.
    ///
    /// # Specification
    /// - ensures: under [`Positions::Artifact`], twice the entry of the key of
    ///   its place in the segment's table when the names name that place, and
    ///   one more than twice its place otherwise; its place is its place in
    ///   rank order, or `position` itself for a position with no place. Under
    ///   [`Positions::Ordinal`], one more than twice its place in the block for
    ///   a member of the block, and twice the place the segment first names it
    ///   at for any other position.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the entry depends on the positions the segment
    ///   named before.
    ///
    /// # Cost
    /// - allocation: the ordinals and the table, growth within the segment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`keyed_segment`], [`encode_placed`] and
    ///   [`encode_named`].
    /// - witness: `encode::tests::a_keyed_segment_writes_no_admission_order_6568`
    /// - witness: `encode::tests::a_placed_encoding_writes_each_position_as_its_place_6845`
    /// - witness: `encode::tests::a_named_encoding_writes_each_named_place_by_its_key_7340`
    #[inline]
    fn rename(
        &mut self,
        position: ConstantIndex,
    ) -> ConstantIndex
    {
        let ordinals = match *self {
            Self::Artifact(ref mut placing) => return placing.rename(position),
            Self::Ordinal(ref mut ordinals) => ordinals,
        };
        if ordinals.block.contains(&position) {
            let place = usize::from(position).saturating_sub(usize::from(ordinals.block.start));
            return ConstantIndex::from(place.saturating_mul(2).saturating_add(1));
        }
        let next = ordinals.named.len();
        let place = *ordinals.places.entry(position).or_insert(next);
        if place == next {
            ordinals.named.push(position);
        }
        ConstantIndex::from(place.saturating_mul(2))
    }

    /// The position a segment writes for `place`, the place of a segment it
    /// imports from: as [`Self::rename`] writes a position at that place.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the table and the entry's keys, growth within the segment.
    #[inline]
    fn name_place(
        &mut self,
        place: ConstantIndex,
    ) -> ConstantIndex
    {
        match *self {
            Self::Artifact(ref mut placing) => placing.name_place(place),
            // A lone segment reads no earlier segment, so this arm is never
            // reached; it writes the place bare.
            Self::Ordinal(_) => {
                ConstantIndex::from(usize::from(place).saturating_mul(2).saturating_add(1))
            },
        }
    }

    /// Start a segment: its table of names holds no key yet.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn open_segment(&mut self)
    {
        if let Self::Artifact(ref mut placing) = *self {
            placing.table.clear();
            placing.segment = placing.segment.wrapping_add(1);
        }
    }

    /// The keys the current segment names, first named first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn table(&self) -> &[ConstantKey]
    {
        match *self {
            Self::Artifact(ref placing) => &placing.table,
            Self::Ordinal(_) => &[],
        }
    }

    /// The width of a key in each table of names: the names' width for an
    /// artifact, and one word for a keyed segment, which writes no table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn width(&self) -> ByteCount
    {
        match *self {
            Self::Artifact(ref placing) => placing.names.width(),
            Self::Ordinal(_) => ByteCount::from(KEY_WIDTH_FLOOR),
        }
    }

    /// Start an entry: it names no key yet. An entry under
    /// [`EntryNaming::Local`] writes each key by its first place among the
    /// entry's own keys and adds nothing to its segment's table, as the
    /// content deduplication compares it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn open_entry(
        &mut self,
        naming: EntryNaming,
    )
    {
        if let Self::Artifact(ref mut placing) = *self {
            placing.named.clear();
            placing.naming = naming;
        }
    }

    /// The keys the entry being written names, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn entry_names(&self) -> &[ConstantKey]
    {
        match *self {
            Self::Artifact(ref placing) => &placing.named,
            Self::Ordinal(_) => &[],
        }
    }
}

impl Placing
{
    /// The writing of each position at its place in `places`, with no place
    /// named.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the empty names, setup.
    #[inline]
    fn placed(places: &Places) -> Self
    {
        Self {
            places: Some(places.clone()),
            ..Self::default()
        }
    }

    /// The position a segment writes for `position`, as
    /// [`Positions::rename`] states it for [`Positions::Artifact`].
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the table and the entry's keys, growth within the segment.
    #[inline]
    fn rename(
        &mut self,
        position: ConstantIndex,
    ) -> ConstantIndex
    {
        let place = self
            .places
            .as_ref()
            .and_then(|places| places.place(position))
            .unwrap_or(position);
        self.name_place(place)
    }

    /// The position a segment writes for `place`: twice the entry of its key
    /// in the segment's table when the names name it, and one more than twice
    /// the place otherwise.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the table and the entry's keys, growth within the segment.
    #[inline]
    fn name_place(
        &mut self,
        place: ConstantIndex,
    ) -> ConstantIndex
    {
        let Some(key) = self.names.key(place)
        else {
            return ConstantIndex::from(usize::from(place).saturating_mul(2).saturating_add(1));
        };
        let entry = if self.naming == EntryNaming::Local {
            self.named
                .iter()
                .position(|named| *named == key)
                .unwrap_or(self.named.len())
        }
        else {
            let at = usize::from(place);
            if self.entries.len() <= at {
                self.entries
                    .resize(gandr_kernel_data::Count::from(at.saturating_add(1)), (0, 0));
            }
            let (stamp, next) = (self.segment, self.table.len());
            match self.entries.get_mut(at) {
                Some(&mut (segment, entry)) if segment == stamp => entry,
                slot => {
                    if let Some(slot) = slot {
                        *slot = (stamp, next);
                    }
                    self.table.push(key);
                    next
                },
            }
        };
        self.named.push(key);
        ConstantIndex::from(entry.saturating_mul(2))
    }
}

impl Interner
{
    /// A fresh interner over an empty index space.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns an interner holding no node and no content and
    ///   continuing none, with the next free global index at zero.
    /// - provides: the empty index space one artifact's encoding fills, so no
    ///   index from an earlier encoding can be reused.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes exact segment entries, assigned indices and
    ///   memo state across repeated ids, distinct equal nodes, a new parent, a
    ///   second segment and reversed children. This separates id-keyed
    ///   deduplication, memo loss, redundant entries and incorrect post-order
    ///   assignment. Deep and differently shared integration fixtures
    ///   supplement these bounded transitions; a shared encode/decode round
    ///   trip is not an independent format oracle.
    /// - witness: `encode::tests::interning_reuses_content_across_segments_without_losing_order`
    /// - witness: `tests::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
    /// - witness: `tests::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
    #[spec(
        ensures: |ret| ret.base.is_none()
                && ret.by_node.is_empty()
                && ret.by_content.is_empty()
                && u32::from(ret.next) == 0,
    )]
    #[inline]
    fn new() -> Self
    {
        Self {
            base: None,
            by_node: BTreeMap::new(),
            by_content: BTreeMap::new(),
            next: GlobalIndex::default(),
            positions: Positions::default(),
            frame: Frame::default(),
        }
    }

    /// An interner continuing `base`, the frozen assignments of an encoding of
    /// the sequence's leading declarations.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: answers every node and content `base` assigned as `base`
    ///   does, holds nothing of its own, and assigns from `base`'s next free
    ///   index.
    /// - provides: the resumed encoding's index space, shared rather than
    ///   copied, so resuming costs nothing in the prefix's size.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every split of mixed and shared sequences, resumed
    ///   after its prefix, writes the whole encoding's bytes.
    /// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
    #[spec(
        captures: [kept = Shared::as_ptr(&base), next = base.next],
        ensures: |ret| ret.by_node.is_empty()
                && ret.by_content.is_empty()
                && ret.base.as_ref().is_some_and(|held| Shared::as_ptr(held) == kept)
                && ret.next == next,
    )]
    #[inline]
    fn after(base: Shared<Assigned, Global>) -> Self
    {
        Self {
            next: base.next,
            base: Some(base),
            by_node: BTreeMap::new(),
            by_content: BTreeMap::new(),
            positions: Positions::default(),
            frame: Frame::default(),
        }
    }

    /// The assignments this interner made, frozen for an encoding that
    /// resumes after them.
    ///
    /// # Specification
    /// - requires: the interner continues none.
    /// - ensures: its node memo, content deduplication and next free index,
    ///   moved rather than copied.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`encode_after`].
    /// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
    #[spec(
        requires: self.base.is_none(),
        captures: [nodes = self.by_node.len(), contents = self.by_content.len(), next = self.next],
        ensures: |ret| ret.by_node.len() == nodes
                && ret.by_content.len() == contents
                && ret.next == next,
    )]
    #[inline]
    fn freeze(self) -> Assigned
    {
        Assigned {
            by_node: self.by_node,
            by_content: self.by_content,
            next: self.next,
            bases: self.frame.bases,
        }
    }

    /// The global index an earlier root assigned `node`, here or in the base.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn node(
        &self,
        node: AnyNode,
    ) -> Option<GlobalIndex>
    {
        self.by_node
            .get(&node)
            .copied()
            .or_else(|| self.base.as_ref()?.by_node.get(&node).copied())
    }

    /// Name `node` by `global`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn assign(
        &mut self,
        node: AnyNode,
        global: GlobalIndex,
    )
    {
        let _prior = self.by_node.insert(node, global);
    }

    /// The global index the entry with `entry`'s bytes took, here or in the
    /// base.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn content(
        &self,
        entry: &EntryContent,
    ) -> Option<GlobalIndex>
    {
        self.by_content
            .get(entry)
            .copied()
            .or_else(|| self.base.as_ref()?.by_content.get(entry).copied())
    }

    /// Open the next segment: its entries take global indices from the next
    /// free one on, and it reads no earlier entry yet.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the segment's base, growth within the segments.
    #[inline]
    fn open_segment(&mut self)
    {
        self.frame.bases.push(self.next);
        self.frame.base = self.next;
        self.frame.imports.clear();
    }

    /// The reference that the current segment writes for the entry at
    /// `global`: twice its offset from the segment's base for an entry of the
    /// segment, and one more than twice its import's place for an entry of an
    /// earlier segment, imported when the segment first reads it.
    ///
    /// # Specification
    /// - ensures: even exactly when `global` stands at or past the segment's
    ///   base; the same odd reference for each read of the same earlier entry.
    /// - panics: none.
    /// - executable: none — an import's place depends on the reads before it.
    ///
    /// # Cost
    /// - allocation: the import of an earlier segment's entry and its slot,
    ///   growth within the segment's reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a segment that reads an entry of the segment before
    ///   it writes the import once, and each local child by its offset.
    /// - witness: `encode::tests::interning_reuses_content_across_segments_without_losing_order`
    #[inline]
    fn reference(
        &mut self,
        global: GlobalIndex,
    ) -> WireU64
    {
        let at = u64::from(u32::from(global));
        let base = u64::from(u32::from(self.frame.base));
        if at >= base {
            return WireU64::from(at.saturating_sub(base).saturating_mul(2));
        }
        self.imported_reference(global)
    }

    /// The reference that the current segment writes for the entry at
    /// `global` of an earlier segment: one more than twice its import's place,
    /// imported when the segment first reads it. Kept apart from
    /// [`Self::reference`], so the reference to an entry of the segment stays
    /// a few instructions inline in each caller.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the import, growth within the segment's reads, and a slot
    ///   for each entry up to the one read, growth within the entries.
    #[cold]
    #[inline(never)]
    fn imported_reference(
        &mut self,
        global: GlobalIndex,
    ) -> WireU64
    {
        let slot = usize::try_from(u32::from(global)).unwrap_or(usize::MAX);
        if self.frame.imported.len() <= slot {
            self.frame.imported.resize(
                gandr_kernel_data::Count::from(slot.saturating_add(1)),
                (0, 0),
            );
        }
        // Each segment pushes its base, so the count of the bases marks it.
        let (stamp, next) = (self.frame.bases.len(), self.frame.imports.len());
        let known = self
            .frame
            .imported
            .get(slot)
            .filter(|&&(segment, _)| segment == stamp)
            .map(|&(_, import)| import);
        let import = known.unwrap_or_else(|| {
            if let Some(read) = self.frame.imported.get_mut(slot) {
                *read = (stamp, next);
            }
            self.push_import(global);
            next
        });
        WireU64::from(
            u64::try_from(import)
                .unwrap_or(u64::MAX)
                .saturating_mul(2)
                .saturating_add(1),
        )
    }

    /// Import the entry at `global` into the current segment: the place of the
    /// segment that holds it, from the segments of the base or from the
    /// segments this interner wrote after them, and its offset there.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the import, growth within the segment's reads.
    #[inline]
    fn push_import(
        &mut self,
        global: GlobalIndex,
    )
    {
        let earlier = self
            .base
            .as_ref()
            .map_or(&[][..], |base| base.bases.as_slice());
        let own = self
            .frame
            .bases
            .first()
            .is_some_and(|&first| global >= first);
        let (bases, first) = if own {
            (self.frame.bases.as_slice(), earlier.len())
        }
        else {
            (earlier, 0)
        };
        let at = bases
            .partition_point(|&start| start <= global)
            .saturating_sub(1);
        let start = bases.get(at).copied().unwrap_or_default();
        let import = (
            first.saturating_add(at),
            u32::from(global).saturating_sub(u32::from(start)),
        );
        self.frame.imports.push(import);
    }
}

/// Encode an admission-ordered declaration sequence over `arena` into canonical
/// bytes.
///
/// # Specification
/// - requires: every reachable id resolves in arena; the graph is acyclic,
///   respects the arena’s truncation discipline and fits the global-index
///   space. The supplied declaration order defines admission positions.
/// - ensures: writes the magic, version, derived atom positions and declaration
///   count, then content-deduplicated segments in first-completion order. Equal
///   abstract input graphs produce equal bytes regardless of in-memory sharing.
/// - provides: a deterministic wire candidate, not admission or typing
///   evidence. Live roots are checked directly and each visited node is checked
///   before entry encoding. Missing negative-family nodes have no unit
///   substitute, so stale ids are a domain violation rather than a promised
///   recovery.
/// - fails: never within the live, acyclic input domain; decode budgets and
///   producer-metadata truth are not checked here.
/// - panics: none within that domain. Enabled specification checks reject a
///   missing root or visited node.
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, including names, admission
///   marks, shared globals, root order and reserved slots. A separate position
///   model and a nonempty provenance fixture distinguish declaration positions
///   from table indices and preserve claimed order. Existing refusal and
///   differently shared fixtures cover table disagreements and canonical
///   deduplication. The finite examples do not prove typing, provenance truth
///   or independent correctness through round-trip self-agreement. The enforced
///   stale-root witness checks the live-ID boundary, not recovery of an invalid
///   arena.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
/// - witness: `encode::tests::stale_roots_violate_the_encoding_domain`
/// - witness: `tests::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `tests::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
#[inline]
#[must_use]
#[spec(requires: declarations.iter().all(|marked| { let declaration = marked.declaration(); arena.value_type(declaration.declared_id()).is_some() && match *declaration.content() { DeclarationContent::Def { body, .. } => arena.value(body).is_some(), DeclarationContent::Data { ref parameters, ref constructors, .. } => parameters.iter().chain(constructors.iter().flatten()).all(|id| arena.value_type(*id).is_some()), DeclarationContent::Codata { ref parameters, ref observations, .. } => parameters.iter().all(|id| arena.value_type(*id).is_some()) && observations.iter().all(|id| arena.comp_type(*id).is_some()), DeclarationContent::Axiom { .. } | DeclarationContent::LiteralIdentity { .. } | DeclarationContent::AbstractType { .. } => true } }),
ensures: |ret| ret.as_image().as_ref().starts_with(tags::MAGIC.as_slice())
    && ret
        .as_image()
        .as_ref()
        .get(tags::MAGIC.len() ..)
        .is_some_and(|rest| rest.starts_with(&u16::from(tags::FORMAT_VERSION).to_le_bytes())))]
pub fn encode(
    arena: &TermArena,
    declarations: &[MarkedDeclaration],
) -> EncodedArtifact
{
    encode_sequence(arena, declarations, Positions::default())
}

/// [`encode`] of `declarations`, the live entries of a kept environment in
/// rank order, with each admission position written as its place in
/// `places`.
///
/// # Specification
/// - requires: as [`encode`]; `places` gives each position that `declarations`
///   name a place, and gives each declaration's own position its index in
///   `declarations`.
/// - ensures: the bytes [`encode`] writes for `declarations` with each position
///   renamed to its place: the artifact of the sequence that a fresh admission
///   of the same source admits.
/// - provides: the export of an environment that a readmission keeps by
///   retiring and keeping entries, byte for byte the export of a whole
///   readmission.
/// - fails: never within [`encode`]'s domain.
/// - panics: none within that domain.
///
/// # Adequacy
/// - hypothesis: L3 — a sequence whose positions are renamed by their places
///   writes the bytes of the renamed sequence written raw, and the raw writing
///   of the unrenamed sequence differs. The kernel's kept environments witness
///   the same for each class of edit.
/// - witness: `encode::tests::a_placed_encoding_writes_each_position_as_its_place_6845`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.as_image().as_ref().starts_with(tags::MAGIC.as_slice()))]
pub fn encode_placed(
    arena: &TermArena,
    declarations: &[MarkedDeclaration],
    places: &Places,
) -> EncodedArtifact
{
    encode_sequence(
        arena,
        declarations,
        Positions::Artifact(Placing::placed(places)),
    )
}

/// [`encode`] of `declarations`, or [`encode_placed`] with `places`, with each
/// position whose place `names` names written by its key.
///
/// # Specification
/// - requires: as [`encode`]; with `places`, as [`encode_placed`]; `names`
///   holds the key of each place in the order of `declarations`.
/// - ensures: the bytes [`encode`] writes, or [`encode_placed`] with `places`,
///   except at each position whose place `names` names: there the segment
///   writes twice the entry of the place's key in its table of names, and its
///   table holds each key it names, first named first.
/// - provides: segments whose bytes read the keys of the constants they name,
///   and no admission position of a named constant.
/// - fails: never within [`encode`]'s domain.
/// - panics: none within that domain.
///
/// # Cost
/// - allocation: the artifact's bytes, growth within the declarations.
///
/// # Adequacy
/// - hypothesis: L3 — a sequence whose two constants are named writes each
///   reference by its key, and the same sequence with one more declaration
///   before them writes the segments that read them byte for byte.
/// - witness: `encode::tests::a_named_encoding_writes_each_named_place_by_its_key_7340`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.as_image().as_ref().starts_with(tags::MAGIC.as_slice()))]
pub fn encode_named(
    arena: &TermArena,
    declarations: &[MarkedDeclaration],
    places: Option<&Places>,
    names: &Names,
) -> EncodedArtifact
{
    encode_sequence(
        arena,
        declarations,
        Positions::Artifact(Placing {
            places: places.cloned(),
            names: names.clone(),
            ..Placing::default()
        }),
    )
}

/// [`encode`] of `declarations`, with each admission position written as
/// `positions` writes it.
///
/// # Specification
/// - requires: as [`encode`].
/// - ensures: the header with the width of each table's keys, the minted atom
///   table, the count and each declaration's segment in order, each position
///   written as `positions` writes it.
/// - fails: never within [`encode`]'s domain.
/// - panics: none within that domain.
/// - executable: none — [`encode`] and [`encode_placed`] state the bytes for
///   each kind of `positions`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`encode`] and [`encode_placed`].
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::a_placed_encoding_writes_each_position_as_its_place_6845`
#[inline]
fn encode_sequence(
    arena: &TermArena,
    declarations: &[MarkedDeclaration],
    positions: Positions,
) -> EncodedArtifact
{
    let mut out = EncodedArtifact::new();
    out.put_image(ArtifactImage::from(tags::MAGIC.as_slice()));
    out.put_version(tags::FORMAT_VERSION);
    let width = positions.width();
    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(width))));
    let mut interner = Interner {
        positions,
        ..Interner::new()
    };
    encode_minted_atom_table(
        &mut out,
        &mut interner.positions,
        minted_places(declarations, ConstantIndex::from(0_usize)),
        width,
    );
    out.put_uvarint(WireU64::from(WireUsize::from(declarations.len())));
    let mut scratch = EncodedArtifact::new();
    for (position, declaration) in declarations.iter().enumerate() {
        let remaining = SealExtent::from(
            declarations
                .len()
                .saturating_sub(position)
                .saturating_sub(1),
        );
        encode_segment(&mut scratch, arena, &mut interner, declaration, remaining);
        put_segment(&mut out, &mut interner, width, &scratch);
    }
    out
}

/// The encoding of an admission-ordered sequence's leading declarations, which
/// an encoding of any sequence leading with them resumes.
///
/// # Specification
/// - requires: constructed by [`encode_prefix`].
/// - ensures: holds the leading declarations' segments as [`encode`] writes
///   them, each table's keys whole and apart from the rest of its segment, the
///   minted atoms among them, and the interner their encoding left, frozen.
/// - panics: none.
/// - executable: none — the fields are private and set only by
///   [`encode_prefix`], whose specification states them.
///
/// # Adequacy
/// - hypothesis: L3 — as [`encode_after`].
/// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
#[derive(Clone, Debug)]
pub struct EncodedPrefix
{
    /// The keys of each leading segment's table of names, whole, segment after
    /// segment, so that an encoding resumed after them writes each at its own
    /// width.
    keys: SmallVec<ConstantKey, 0, Global>,
    /// The bytes of each leading segment past its table: its imports and its
    /// declaration, segment after segment.
    rests: EncodedArtifact,
    /// Where each leading segment ends, in `keys` and in `rests`.
    cuts: SmallVec<(usize, usize), 0, Global>,
    /// The admission positions of the abstract types among them.
    atoms: SmallVec<MintedAtom, 0, Global>,
    /// How many declarations lead.
    count: usize,
    /// What their encoding assigned, shared by every encoding resumed after it.
    assigned: Shared<Assigned, Global>,
}

impl EncodedPrefix
{
    /// The admission position the first declaration after the prefix takes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn end(&self) -> ConstantIndex
    {
        ConstantIndex::from(self.count)
    }
}

quenchant_shape::reason_enum! {
    /// Why a sequence's leading declarations have no encoding to resume.
    pub mod encoded_prefix {
        /// The reason no prefix is encoded.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// An abstract type among them is sealed to the end of the
            /// sequence, so its segment depends on what follows.
            OpenSeal,
        }
    }
}

/// The encoding of `declarations`, the leading declarations of a sequence over
/// `arena`, for [`encode_after`] to resume.
///
/// # Specification
/// - requires: as [`encode`].
/// - ensures: absent as [`encoded_prefix::Absent::OpenSeal`] when an abstract
///   type among `declarations` has an open seal; otherwise the segments
///   [`encode`] writes for `declarations` after its header, each table's keys
///   whole, ending at `declarations`' length, and the interner those segments
///   left.
/// - provides: what an editor's admission encodes once for a document's import
///   closure, so that each revision of the document encodes its own
///   declarations alone.
/// - fails: never within [`encode`]'s domain.
/// - panics: none within that domain.
///
/// # Cost
/// - allocation: the segments and the interner, growth within the prefix.
///
/// # Adequacy
/// - hypothesis: L3 — every split of mixed and shared sequences, resumed after
///   its prefix, writes the whole encoding's bytes, bare or under names; a
///   prefix with an open seal is refused.
/// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
/// - witness: `encode::tests::a_prefix_with_an_open_seal_is_not_encoded_776`
#[inline]
#[spec(ensures: |ret| match ret {
    Maybe::Present(ref prefix) => usize::from(prefix.end()) == declarations.len()
        && prefix.atoms == minted_atoms(declarations),
    Maybe::Absent(encoded_prefix::Absent::OpenSeal) => declarations.iter().any(|marked| matches!(
        *marked.declaration().content(),
        DeclarationContent::AbstractType { scope: SealScope::Open, .. }
    )),
})]
pub fn encode_prefix(
    arena: &TermArena,
    declarations: &[MarkedDeclaration],
    names: &Names,
) -> Maybe<EncodedPrefix, encoded_prefix::Absent>
{
    if declarations.iter().any(|marked| {
        matches!(
            *marked.declaration().content(),
            DeclarationContent::AbstractType {
                scope: SealScope::Open,
                ..
            }
        )
    }) {
        return Maybe::Absent(encoded_prefix::Absent::OpenSeal);
    }
    let mut keys = SmallVec::<_, 0, Global>::new();
    let mut rests = EncodedArtifact::new();
    let mut cuts =
        SmallVec::<_, 0, Global>::with_capacity(gandr_kernel_data::Count::from(declarations.len()));
    let mut interner = Interner {
        positions: Positions::Artifact(Placing {
            names: names.clone(),
            ..Placing::default()
        }),
        ..Interner::new()
    };
    let mut scratch = EncodedArtifact::new();
    for declaration in declarations {
        // No seal is open, so no segment reads how many declarations follow.
        encode_segment(
            &mut scratch,
            arena,
            &mut interner,
            declaration,
            SealExtent::from(0_usize),
        );
        keys.extend_from_slice(interner.positions.table());
        put_imports(&mut rests, &mut interner);
        rests.put_image(scratch.as_image());
        cuts.push((keys.len(), rests.as_image().as_ref().len()));
    }
    Maybe::Present(EncodedPrefix {
        keys,
        rests,
        cuts,
        atoms: minted_atoms(declarations),
        count: declarations.len(),
        assigned: Shared::new(interner.freeze()),
    })
}

/// [`encode`] of the sequence `prefix`'s declarations lead and `after`
/// follows, writing `prefix`'s segments as they were encoded and encoding
/// `after`'s alone.
///
/// # Specification
/// - requires: `prefix` was encoded by [`encode_prefix`] over an arena whose
///   nodes `arena` holds at the same ids, and under `names` for its places, and
///   `after` follows the declarations it encoded; the sequence is in
///   [`encode`]'s domain.
/// - ensures: [`encode_named`]'s bytes under `names` for the whole sequence:
///   its header, then `prefix`'s segments, then `after`'s.
/// - provides: an encoding whose cost is `after`'s, and a copy of `prefix`'s
///   bytes.
/// - fails: never within [`encode`]'s domain.
/// - panics: none within that domain.
///
/// # Cost
/// - allocation: the artifact's bytes, growth within the declarations.
///
/// # Adequacy
/// - hypothesis: L3 — every split of mixed and shared sequences, resumed after
///   its prefix, writes the whole encoding's bytes, bare or under names.
/// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.as_image().as_ref().starts_with(tags::MAGIC.as_slice())
    && ret.as_image().as_ref().len() > prefix.rests.as_image().as_ref().len())]
pub fn encode_after(
    prefix: &EncodedPrefix,
    arena: &TermArena,
    after: &[MarkedDeclaration],
    names: &Names,
) -> EncodedArtifact
{
    let mut out = EncodedArtifact::new();
    out.put_image(ArtifactImage::from(tags::MAGIC.as_slice()));
    out.put_version(tags::FORMAT_VERSION);
    let width = names.width();
    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(width))));
    let mut interner = Interner::after(Shared::clone(&prefix.assigned));
    interner.positions = Positions::Artifact(Placing {
        names: names.clone(),
        ..Placing::default()
    });
    encode_minted_atom_table(
        &mut out,
        &mut interner.positions,
        prefix
            .atoms
            .iter()
            .map(|&atom| ConstantIndex::from(usize::from(atom)))
            .chain(minted_places(after, prefix.end())),
        width,
    );
    out.put_uvarint(WireU64::from(WireUsize::from(
        prefix.count.saturating_add(after.len()),
    )));
    let rests_image = prefix.rests.as_image();
    let rests = rests_image.as_ref();
    let (mut keys_from, mut rests_from) = (0_usize, 0_usize);
    for &(keys_to, rests_to) in &prefix.cuts {
        put_table(
            &mut out,
            prefix.keys.get(keys_from .. keys_to).unwrap_or_default(),
            width,
        );
        out.put_image(ArtifactImage::from(
            rests.get(rests_from .. rests_to).unwrap_or_default(),
        ));
        (keys_from, rests_from) = (keys_to, rests_to);
    }
    let mut scratch = EncodedArtifact::new();
    for (position, declaration) in after.iter().enumerate() {
        let remaining = SealExtent::from(after.len().saturating_sub(position).saturating_sub(1));
        encode_segment(&mut scratch, arena, &mut interner, declaration, remaining);
        put_segment(&mut out, &mut interner, width, &scratch);
    }
    out
}

/// Encode `declaration`'s segment past its table of names and its imports: the
/// declaration as [`encode_declaration`] writes it into `scratch`. The
/// segment's table and imports stay in `interner`.
///
/// # Specification
/// - requires: as [`encode_declaration`].
/// - ensures: `scratch` holds the declaration's bytes, and `interner` the
///   segment's imports, first read first. The positions' table holds each key
///   the segment names, first named first, the key of each import's segment
///   among them.
/// - provides: what [`put_segment`] writes, and the whole keys an encoded
///   prefix keeps.
/// - fails: never within [`encode`]'s domain.
/// - panics: none within that domain.
/// - executable: none — the bytes are [`encode_declaration`]'s, which a clause
///   would restate.
///
/// # Adequacy
/// - hypothesis: L3 — as [`encode_named`].
/// - witness: `encode::tests::a_named_encoding_writes_each_named_place_by_its_key_7340`
#[inline]
fn encode_segment(
    scratch: &mut EncodedArtifact,
    arena: &TermArena,
    interner: &mut Interner,
    declaration: &MarkedDeclaration,
    remaining: SealExtent,
)
{
    scratch.clear();
    interner.positions.open_segment();
    interner.open_segment();
    encode_declaration(scratch, arena, interner, declaration, remaining);
    // Naming an import's segment may add its key to the table, so each import
    // is named before the table is written.
    for &(place, _) in &interner.frame.imports {
        let _entry = interner.positions.name_place(ConstantIndex::from(place));
    }
}

/// Write a segment to `out`: its table of names, each key cut to `width`
/// bytes, then its imports and `scratch`, which [`encode_segment`] filled.
///
/// # Specification
/// - requires: `width` is at most a whole key, and [`encode_segment`] filled
///   `interner` and `scratch`.
/// - ensures: `out` gains the table, then the imports, then `scratch`'s bytes.
/// - panics: none.
/// - executable: none — as [`put_table`].
///
/// # Adequacy
/// - hypothesis: L3 — a segment writes its table at the header's width, then
///   its imports and its entries, and decodes back to its declaration.
/// - witness: `encode::tests::keys_that_share_a_word_widen_every_table_7340`
/// - witness: `encode::tests::a_segment_reads_an_earlier_entry_by_its_import_7340`
#[inline]
fn put_segment(
    out: &mut EncodedArtifact,
    interner: &mut Interner,
    width: ByteCount,
    scratch: &EncodedArtifact,
)
{
    put_table(out, interner.positions.table(), width);
    put_imports(out, interner);
    out.put_image(scratch.as_image());
}

/// Write the current segment's imports to `out`: their count, then for each,
/// the position of its segment's place and the entry's offset there, first
/// read first.
///
/// # Specification
/// - requires: [`encode_segment`] named each import's place, so naming it again
///   adds no key to the table.
/// - ensures: `out` gains the count of the imports, then each one's position
///   and offset.
/// - panics: none.
/// - executable: none — a position depends on the table, which a clause would
///   restate.
///
/// # Adequacy
/// - hypothesis: L3 — a segment that reads an earlier entry writes its import
///   once, at its place and offset, and decodes back to its declaration.
/// - witness: `encode::tests::a_segment_reads_an_earlier_entry_by_its_import_7340`
#[inline]
fn put_imports(
    out: &mut EncodedArtifact,
    interner: &mut Interner,
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(interner.frame.imports.len())));
    for &(place, offset) in &interner.frame.imports {
        let written = interner.positions.name_place(ConstantIndex::from(place));
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(written))));
        out.put_uvarint(WireU64::from(u64::from(offset)));
    }
}

/// Write a segment's table of names to `out`: the count of its keys, then the
/// first `width` bytes of each, in order.
///
/// # Specification
/// - requires: `width` is at most a whole key.
/// - ensures: `out` gains the count of `table`, then each key's first `width`
///   bytes.
/// - panics: none.
/// - executable: none — the bytes join a growing artifact, which a clause would
///   read back whole.
///
/// # Adequacy
/// - hypothesis: L3 — a table under keys that share their first word is written
///   wide enough to keep them apart, and one under the floor is written one
///   word wide.
/// - witness: `encode::tests::keys_that_share_a_word_widen_every_table_7340`
#[inline]
fn put_table(
    out: &mut EncodedArtifact,
    table: &[ConstantKey],
    width: ByteCount,
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(table.len())));
    for key in table {
        out.put_image(ArtifactImage::from(
            key.as_ref().get(.. usize::from(width)).unwrap_or_default(),
        ));
    }
}

/// One declaration's segment as a verdict key reads it.
///
/// The segment is written alone, and each admission position by where the
/// segment first names it, so the bytes read no admission order. The
/// positions are kept in that order.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KeyedSegment
{
    /// The segment's bytes.
    image: EncodedArtifact,
    /// The positions the segment names outside its block, first named first.
    named: SmallVec<ConstantIndex, 0, Global>,
}

impl KeyedSegment
{
    /// The segment's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn image(&self) -> &EncodedArtifact
    {
        &self.image
    }

    /// The positions the segment names outside its block, in the order it
    /// first names them: the position the bytes write as twice `n` is the
    /// `n`th.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn named(&self) -> &[ConstantIndex]
    {
        &self.named
    }
}

/// `declaration`'s keyed segment over `arena`.
///
/// The segment is written alone, as the first of a sequence. Each position
/// outside `block` is written as twice where the segment first names it, and
/// each member of `block` as one more than twice its place in the block.
///
/// # Specification
/// - requires: the nodes of `declaration` live in `arena`.
/// - ensures: absent as [`encoded_prefix::Absent::OpenSeal`] when `declaration`
///   is an abstract type sealed to the end of the sequence; otherwise the
///   segment, and each position it names outside `block`, once.
/// - provides: bytes that read no admission position, for a key that reads each
///   named position as the key of its entry.
/// - fails: never.
/// - panics: none within [`encode`]'s domain.
///
/// # Adequacy
/// - hypothesis: L3 — one declaration over two constants admitted in two orders
///   writes one image, the positions listed in the order the image first names
///   them; a member of the block is written by its place in it.
/// - witness: `encode::tests::a_keyed_segment_writes_no_admission_order_6568`
#[inline]
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(encoded_prefix::Absent::OpenSeal)) == matches!(
    *declaration.declaration().content(),
    DeclarationContent::AbstractType { scope: SealScope::Open, .. }
))]
pub fn keyed_segment(
    arena: &TermArena,
    declaration: &MarkedDeclaration,
    block: core::ops::Range<ConstantIndex>,
) -> Maybe<KeyedSegment, encoded_prefix::Absent>
{
    if let DeclarationContent::AbstractType {
        scope: SealScope::Open,
        ..
    } = *declaration.declaration().content()
    {
        return Maybe::Absent(encoded_prefix::Absent::OpenSeal);
    }
    let mut interner = Interner {
        positions: Positions::Ordinal(Ordinals {
            named: SmallVec::<_, 0, Global>::new(),
            places: BTreeMap::new(),
            block,
        }),
        ..Interner::new()
    };
    let mut image = EncodedArtifact::new();
    encode_declaration(
        &mut image,
        arena,
        &mut interner,
        declaration,
        SealExtent::from(0_usize),
    );
    let named = match interner.positions {
        Positions::Ordinal(ordinals) => ordinals.named,
        Positions::Artifact(_) => SmallVec::<_, 0, Global>::new(),
    };
    Maybe::Present(KeyedSegment { image, named })
}

/// The admission positions of the abstract-type declarations in a sequence,
/// ascending: the canonical content of the minted-atom table.
///
/// # Specification
/// - requires: `declarations` is in admission order.
/// - ensures: the strictly ascending positions of exactly the abstract-type
///   declarations.
/// - provides: the table the encoder writes and the decoder independently
///   re-derives, which is what makes the table refutable rather than believed.
///   Admission order stays prose: a position is the sequence index itself, so
///   the order is definitional rather than an observation.
/// - fails: never.
/// - panics: none.
///
/// # Cost
/// - allocation: the positions of the atoms, growth within the declarations.
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, including names, admission
///   marks, shared globals, root order and reserved slots. A separate position
///   model and a nonempty provenance fixture distinguish declaration positions
///   from table indices and preserve claimed order. Existing refusal and
///   differently shared fixtures cover table disagreements and canonical
///   deduplication. The finite examples do not prove typing, provenance truth
///   or independent correctness through round-trip self-agreement.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
#[must_use]
#[spec(ensures: |ret| ret.iter().copied().eq(declarations.iter().enumerate().filter_map(
    |(position, declaration)| matches!(
        *declaration.declaration().content(),
        DeclarationContent::AbstractType { .. }
    )
    .then_some(MintedAtom::from(position)),
)))]
pub fn minted_atoms(declarations: &[MarkedDeclaration]) -> SmallVec<MintedAtom, 0, Global>
{
    minted_places(declarations, ConstantIndex::from(0_usize))
        .map(|place| MintedAtom::from(usize::from(place)))
        .collect()
}

/// The place of each abstract-type declaration among `declarations`, the first
/// of which stands at `first`, in order.
///
/// # Specification
/// trivial.
#[inline]
fn minted_places(
    declarations: &[MarkedDeclaration],
    first: ConstantIndex,
) -> impl Iterator<Item = ConstantIndex> + Clone + '_
{
    declarations
        .iter()
        .enumerate()
        .filter(|entry| {
            matches!(
                *entry.1.declaration().content(),
                DeclarationContent::AbstractType { .. }
            )
        })
        .map(move |entry| ConstantIndex::from(usize::from(first).saturating_add(entry.0)))
}

/// Write the minted-atom table: the count of `atoms`, then, when it holds an
/// atom, a table of names and each atom's place as a segment writes a
/// position.
///
/// The table is deliberately derivable from the declarations that follow it.
/// That is not redundancy for its own sake: a table the decoder can recompute
/// is a table the decoder can *refute*, and refutability is the whole
/// difference between freshness as a checked property and freshness as
/// something the producer asserts. An atom whose place the names name is
/// written by its key, so an insertion before it leaves its bytes.
///
/// # Specification
/// - requires: `atoms` are the places of the abstract types of the sequence,
///   ascending, and `width` is at most a whole key.
/// - ensures: appends the count of `atoms`. When the count is above zero, it
///   then appends the table of the keys of the named atoms at `width`, and each
///   atom's place as [`Positions::name_place`] writes it, in order.
/// - provides: the table a decoder recomputes and compares, which is what makes
///   freshness a checked property rather than a producer's assertion.
/// - panics: none.
/// - executable: none — a written place depends on the table, which a clause
///   would restate.
///
/// # Cost
/// - allocation: the table of the atoms' keys, growth within the atoms.
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, bare and under names. A
///   named atom past an insertion keeps its bytes. Existing refusal fixtures
///   cover table disagreements.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
/// - witness: `encode::tests::a_named_atom_keeps_its_table_past_an_insertion_7340`
#[inline]
fn encode_minted_atom_table<Atoms>(
    out: &mut EncodedArtifact,
    positions: &mut Positions,
    atoms: Atoms,
    width: ByteCount,
) where
    Atoms: Iterator<Item = ConstantIndex> + Clone,
{
    let count = atoms.clone().count();
    out.put_uvarint(WireU64::from(WireUsize::from(count)));
    if count == 0 {
        return;
    }
    // Naming an atom's place may add its key to the table, so each atom is
    // named before the table is written.
    positions.open_segment();
    for place in atoms.clone() {
        let _entry = positions.name_place(place);
    }
    put_table(out, positions.table(), width);
    for place in atoms {
        let written = positions.name_place(place);
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(written))));
    }
}

/// Write one declaration segment: its admission mark, kind, name record, level
/// signature, the entries it introduces, and its root references.
///
/// # Specification
/// - requires: the interner carries assignments from earlier segments of this
///   unchanged acyclic arena; assignments fit its index space. Dangling value
///   and value-type roots are admitted. `remaining` counts the declarations
///   after this one in the sequence.
/// - ensures: writes the mark, kind, name and level interface, then only newly
///   completed entries, in first-completion order. Definitions write
///   declared/body roots and four annotation slots, and a definition relating
///   endpoints writes [`tags::KIND_DEF_RELATING`] and closes with the pair
///   count and each pair's roots and dialogue; a definition resting on laws
///   writes [`tags::KIND_DEF_LAWFUL`] and closes with the pair block, its count
///   possibly zero, then the law count and each law's position; a definition
///   carrying an operation's rules writes [`tags::KIND_DEF_RULED`] and closes
///   with the pair block and the law block, both counts possibly zero, then the
///   rule count and each rule's two sides; a definition holding a role writes
///   [`tags::KIND_DEF_ROLED`] and closes with the pair, law, rule and cover
///   blocks, each count possibly zero, then the role's tag; a datatype holding
///   a role and no indices, rules or cells writes [`tags::KIND_DATA_ROLED`] and
///   closes with the role's tag; a coinductive datatype with no indices, rules
///   or cells writes [`tags::KIND_DATA_COINDUCTIVE`] and the datatype fields
///   alone; a data declaration presenting rules writes
///   [`tags::KIND_DATA_PRESENTED`] and closes with the rule count and each
///   rule's two sides; a type of words writes [`tags::KIND_DATA_WORDS`] and
///   closes with the rule block, its count possibly zero, then the sort's
///   position, the cell count and each cell's two endpoints as rule sides; a
///   type of words over cells above dimension one writes
///   [`tags::KIND_DATA_WORDS_HIGHER`] and the same block, how many times the
///   point is wrapped, less one, after the sort's position; an indexed data
///   declaration writes [`tags::KIND_DATA_INDEXED`] and closes with the index
///   count, each index classifier's root and each constructor's result roots,
///   and one that presents rules writes [`tags::KIND_DATA_INDEXED_PRESENTED`]
///   and closes with the rule block after them; a codata declaration writes
///   [`tags::KIND_CODATA`] and closes with its parameter count and roots, then
///   its observation count and roots; abstract types write their kind and
///   representation roots and the extent of their scope, an open scope as
///   `remaining`, and an interfaced one writes
///   [`tags::KIND_ABSTRACT_INTERFACED`] and closes with its relation's and its
///   reflexivity's roots, or, when its interface states a law,
///   [`tags::KIND_ABSTRACT_LAWFUL`] and the law's root after them; a literal
///   identity test writes [`tags::KIND_LITERAL_IDENTITY`] and closes with its
///   base's atom byte and its polarity byte; the other kinds write one root and
///   no slots.
/// - provides: one segment with cross-declaration sharing. The predicate checks
///   the mark/kind bytes, root memo presence and global-counter transition;
///   literal segment fixtures observe field order and slot framing.
/// - fails: never.
/// - panics: none within the acyclic domain.
///
/// # Cost
/// - allocation: the segment's entries, growth within the declaration.
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, including names, admission
///   marks, shared globals, root order and reserved slots. A separate position
///   model and a nonempty provenance fixture distinguish declaration positions
///   from table indices and preserve claimed order. Existing refusal and
///   differently shared fixtures cover table disagreements and canonical
///   deduplication. The finite examples do not prove typing, provenance truth
///   or independent correctness through round-trip self-agreement.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
/// - witness: `encode::tests::a_relating_definition_closes_its_segment_with_its_pairs`
/// - witness: `encode::tests::a_lawful_definition_closes_its_segment_with_its_laws`
/// - witness: `encode::tests::a_ruled_definition_closes_its_segment_with_its_rules`
/// - witness: `encode::tests::a_presented_data_declaration_closes_its_segment_with_its_rules`
/// - witness: `encode::tests::a_type_of_words_closes_its_segment_with_its_cells`
/// - witness: `encode::tests::an_interfaced_atom_closes_its_segment_with_its_interface`
/// - witness: `encode::tests::a_literal_identity_test_closes_its_segment_with_its_base_and_polarity`
/// - witness: `encode::tests::an_indexed_data_declaration_closes_its_segment_with_its_indices`
/// - witness: `encode::tests::a_codata_declaration_closes_its_segment_with_its_observations`
#[spec(
    captures: entry = (out.as_image().as_ref().len(), interner.by_content.len(), interner.next),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        bytes.get(entry.0).copied() == Some(u8::from(match marked.mark() { AdmissionMark::Checked => tags::ADMISSION_CHECKED, AdmissionMark::UncheckedBypass => tags::ADMISSION_UNCHECKED }))
            && bytes.get(entry.0.saturating_add(1)).copied() == Some(u8::from(kind_tag(marked.declaration())))
            && interner.node(AnyNode::ValueType(marked.declaration().declared_id())).is_some()
            && match *marked.declaration().content() { DeclarationContent::Def { body, .. } => interner.node(AnyNode::Value(body)).is_some(), DeclarationContent::Codata { ref observations, .. } => observations.iter().all(|id| interner.node(AnyNode::CompType(*id)).is_some()), DeclarationContent::AbstractType { interface: Maybe::Present(interface), .. } => interner.node(AnyNode::Value(interface.relation())).is_some() && interner.node(AnyNode::Value(interface.reflexivity())).is_some() && match interface.law() { Maybe::Present(law) => interner.node(AnyNode::Value(law)).is_some(), Maybe::Absent(_) => true }, DeclarationContent::Data { .. } | DeclarationContent::Axiom { .. } | DeclarationContent::LiteralIdentity { .. } | DeclarationContent::AbstractType { .. } => true }
            && marked.declaration().related().iter().all(|related| interner.node(AnyNode::Value(related.left)).is_some() && interner.node(AnyNode::Value(related.right)).is_some())
            && marked.declaration().covers().iter().all(|covered| interner.node(AnyNode::Computation(covered.root)).is_some())
            && interner.by_content.len() >= entry.1
            && u32::from(interner.next) == u32::from(entry.2).saturating_add(u32::try_from(interner.by_content.len().saturating_sub(entry.1)).unwrap_or(u32::MAX)) },
)]
fn encode_declaration(
    out: &mut EncodedArtifact,
    arena: &TermArena,
    interner: &mut Interner,
    marked: &MarkedDeclaration,
    remaining: SealExtent,
)
{
    out.put_tag(match marked.mark() {
        AdmissionMark::Checked => tags::ADMISSION_CHECKED,
        AdmissionMark::UncheckedBypass => tags::ADMISSION_UNCHECKED,
    });
    let declaration = marked.declaration();
    let content = declaration.content();
    let kind = kind_tag(declaration);
    out.put_tag(kind);
    encode_structured_name(out, declaration.name());
    encode_level_signature(out, declaration.levels());

    let mut segment: SmallVec<EncodedEntry, 0, Global> = SmallVec::<_, 0, Global>::new();
    let mut data_roots = SmallVec::<_, 0, Global>::new();
    let mut index_roots = SmallVec::<_, 0, Global>::new();
    let mut related_roots = SmallVec::<_, 0, Global>::new();
    let mut cover_roots = SmallVec::<_, 0, Global>::new();
    let mut interface_roots = None;
    let mut observation_roots = SmallVec::<_, 0, Global>::new();
    let (root_declared, root_body, root_sealed) = match *content {
        DeclarationContent::Data {
            kind,
            ref parameters,
            ref indices,
            ref constructors,
            ref results,
        } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(kind));
            for group in core::iter::once(parameters).chain(constructors.iter()) {
                let roots = group
                    .iter()
                    .map(|id| intern(arena, interner, &mut segment, AnyNode::ValueType(*id)))
                    .collect::<SmallVec<_, 0, Global>>();
                data_roots.push(roots);
            }
            // The indices after the constructors, so a family indexed by
            // nothing interns exactly what it did before the kind existed.
            index_roots.extend(
                indices
                    .iter()
                    .map(|id| intern(arena, interner, &mut segment, AnyNode::ValueType(*id))),
            );
            for result in results.iter().flatten() {
                index_roots.push(intern(
                    arena,
                    interner,
                    &mut segment,
                    AnyNode::Value(*result),
                ));
            }
            (declared, None, None)
        },
        // A codata declaration writes its kind as its declared root, then its
        // parameter roots in the data roots' first group and its observations'
        // computation-type roots after them.
        DeclarationContent::Codata {
            kind,
            ref parameters,
            ref observations,
        } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(kind));
            data_roots.push(
                parameters
                    .iter()
                    .map(|id| intern(arena, interner, &mut segment, AnyNode::ValueType(*id)))
                    .collect::<SmallVec<_, 0, Global>>(),
            );
            observation_roots = observations
                .iter()
                .map(|id| intern(arena, interner, &mut segment, AnyNode::CompType(*id)))
                .collect();
            (declared, None, None)
        },
        DeclarationContent::Def { declared, body } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(declared));
            let body = intern(arena, interner, &mut segment, AnyNode::Value(body));
            // The related endpoints after the body, so a definition relating
            // none interns exactly what it did before the kind existed.
            for related in declaration.related() {
                let left = intern(arena, interner, &mut segment, AnyNode::Value(related.left));
                let right = intern(arena, interner, &mut segment, AnyNode::Value(related.right));
                related_roots.push((left, right));
            }
            // The covered roots after the related endpoints, so a definition
            // covering none interns exactly what it did before the kind
            // existed. A root lies in the body, so it adds no entry.
            for covered in declaration.covers() {
                cover_roots.push(intern(
                    arena,
                    interner,
                    &mut segment,
                    AnyNode::Computation(covered.root),
                ));
            }
            (declared, Some(body), None)
        },
        DeclarationContent::Axiom { declared }
        | DeclarationContent::LiteralIdentity { declared, .. } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(declared));
            (declared, None, None)
        },
        // An abstract type writes its kind as its declared root, its
        // representation as a second value-type root, and its scope's extent.
        // The representation is on the wire because the kernel re-reads it
        // inside the minting admission when it replays the artifact; outside
        // that admission no rule reads it. An interface's two roots come after
        // the representation, so an atom with none interns exactly what it
        // did before the kind existed.
        DeclarationContent::AbstractType {
            kind,
            representation,
            scope,
            interface,
        } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(kind));
            let representation = intern(
                arena,
                interner,
                &mut segment,
                AnyNode::ValueType(representation),
            );
            if let Maybe::Present(interface) = interface {
                let relation = intern(
                    arena,
                    interner,
                    &mut segment,
                    AnyNode::Value(interface.relation()),
                );
                let reflexivity = intern(
                    arena,
                    interner,
                    &mut segment,
                    AnyNode::Value(interface.reflexivity()),
                );
                let law = match interface.law() {
                    Maybe::Present(law) => {
                        Some(intern(arena, interner, &mut segment, AnyNode::Value(law)))
                    },
                    Maybe::Absent(_) => None,
                };
                interface_roots = Some((relation, reflexivity, law));
            }
            let extent = match scope {
                SealScope::Open => remaining,
                SealScope::Closed(extent) => extent,
            };
            (declared, None, Some((representation, extent)))
        },
    };
    out.put_uvarint(WireU64::from(WireUsize::from(segment.len())));
    for entry in &segment {
        out.put_image(entry.0.as_image());
    }
    let declared_reference = interner.reference(root_declared);
    out.put_uvarint(declared_reference);
    if let DeclarationContent::LiteralIdentity { test, .. } = *content {
        out.put_tag(identity_base_tag(test.base()));
        out.put_tag(match test.polarity() {
            crate::Polarity::Same => tags::IDENTITY_SAME,
            crate::Polarity::Different => tags::IDENTITY_DIFFERENT,
        });
    }
    if let Some((representation, extent)) = root_sealed {
        let written = interner.reference(representation);
        out.put_uvarint(written);
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(extent))));
    }
    if let Some((relation, reflexivity, law)) = interface_roots {
        let relation = interner.reference(relation);
        out.put_uvarint(relation);
        let reflexivity = interner.reference(reflexivity);
        out.put_uvarint(reflexivity);
        if let Some(law) = law {
            let law = interner.reference(law);
            out.put_uvarint(law);
        }
    }
    if let DeclarationContent::Data {
        ref indices,
        ref constructors,
        ..
    } = *(content)
    {
        for (index, group) in data_roots.iter().enumerate() {
            if index == 1 {
                out.put_uvarint(WireU64::from(WireUsize::from(constructors.len())));
            }
            out.put_uvarint(WireU64::from(WireUsize::from(group.len())));
            for root in group {
                let written = interner.reference(*root);
                out.put_uvarint(written);
            }
        }
        if constructors.is_empty() {
            out.put_uvarint(WireU64::from(0_u64));
        }
        if !indices.is_empty() {
            out.put_uvarint(WireU64::from(WireUsize::from(indices.len())));
            for root in &index_roots {
                let written = interner.reference(*root);
                out.put_uvarint(written);
            }
        }
    }
    if let DeclarationContent::Codata { .. } = *content {
        for group in [
            data_roots.first().map_or(&[][..], SmallVec::as_slice),
            &observation_roots,
        ] {
            out.put_uvarint(WireU64::from(WireUsize::from(group.len())));
            for root in group {
                let written = interner.reference(*root);
                out.put_uvarint(written);
            }
        }
    }
    if let Some(root_body) = root_body {
        let written = interner.reference(root_body);
        out.put_uvarint(written);
        // The four per-definition annotation slots. The first, erasure, carries
        // the stages the signature quantifies over; modes and grades, and
        // directedness and variance stay reserved and empty; the third is the
        // sealing-provenance slot, and it carries the atoms this declaration's
        // projection rebound. A choke point re-derives them from the declared
        // type rather than believing them.
        encode_stage_signature(out, declaration.stages());
        out.put_uvarint(WireU64::from(0_u64));
        let renamed: SmallVec<ConstantIndex, 0, Global> = declaration
            .provenance()
            .iter()
            .map(|&atom| interner.positions.rename(atom))
            .collect();
        encode_sealing_provenance(out, &renamed);
        out.put_uvarint(WireU64::from(0_u64));
    }
    // The relating block closes a definition's segment: a pair count of at
    // least one, since a definition relating none wrote the plain kind, then
    // each pair's roots and its dialogue. A lawful definition writes the block
    // whatever its count, and its laws after it: a count of at least one and
    // each law's position. A ruled definition writes both blocks whatever
    // their counts, then its rules: a count of at least one and each rule's
    // two sides. A covered definition writes the three blocks whatever their
    // counts, then its covers. A held definition writes all four blocks
    // whatever their counts, then its role.
    let held = kind == tags::KIND_DEF_ROLED;
    let laws = declaration.laws();
    let operation_rules = declaration.operation_rules().rules();
    let covered = !cover_roots.is_empty();
    if held
        || !related_roots.is_empty()
        || !laws.is_empty()
        || !operation_rules.is_empty()
        || covered
    {
        out.put_uvarint(WireU64::from(WireUsize::from(related_roots.len())));
        for (&(left, right), related) in related_roots.iter().zip(declaration.related()) {
            let left = interner.reference(left);
            out.put_uvarint(left);
            let right = interner.reference(right);
            out.put_uvarint(right);
            out.put_uvarint(WireU64::from(WireUsize::from(related.dialogue.len())));
            for &decision in &related.dialogue {
                out.put_uvarint(WireU64::from(crate::term::decision_word(decision).0));
            }
        }
    }
    if held || !laws.is_empty() || !operation_rules.is_empty() || covered {
        out.put_uvarint(WireU64::from(WireUsize::from(laws.len())));
        for &law in laws {
            let written = interner.positions.rename(law);
            out.put_uvarint(WireU64::from(WireUsize::from(usize::from(written))));
        }
    }
    if held || !operation_rules.is_empty() || covered {
        out.put_uvarint(WireU64::from(WireUsize::from(operation_rules.len())));
        for rule in operation_rules {
            encode_operation_side(out, rule.left(), &mut interner.positions);
            encode_operation_side(out, rule.right(), &mut interner.positions);
        }
    }
    // The cover block closes a covered definition's segment: a cover count of
    // at least one, since a definition covering none wrote another kind, then
    // each cover's root and its steps. A held definition writes the block
    // whatever its count.
    if held || covered {
        out.put_uvarint(WireU64::from(WireUsize::from(cover_roots.len())));
        for (&root, covered) in cover_roots.iter().zip(declaration.covers()) {
            let written = interner.reference(root);
            out.put_uvarint(written);
            encode_cover(out, &covered.cover, &mut interner.positions);
        }
    }
    // The rule block closes a presented data declaration's segment: a rule
    // count of at least one, since a free type wrote the plain kind, then each
    // rule's left and right sides, a node count and the nodes in pre-order. A
    // type of words writes the block whatever its count, then its sort's
    // position and its cells, each endpoint a side as a rule's are. An indexed
    // type writes the block after its results when it presents a rule, under
    // its own kind, and it writes no cells, which admission refuses.
    let presentation = declaration.presentation();
    let rules = presentation.rules();
    let cells = presentation.cells();
    let indexed =
        matches!(*content, DeclarationContent::Data { ref indices, .. } if !indices.is_empty());
    if !rules.is_empty() || cells.is_some() && !indexed {
        out.put_uvarint(WireU64::from(WireUsize::from(rules.len())));
        for rule in rules {
            encode_rule_side(out, rule.left());
            encode_rule_side(out, rule.right());
        }
    }
    if indexed {
        return;
    }
    if let Some(cells) = cells {
        let sort = interner.positions.rename(cells.sort());
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(sort))));
        // Cells above dimension one write how many times their point is
        // wrapped, less one, so every count the kind reads is canonical.
        if let Some(above) = usize::from(cells.reflexivities()).checked_sub(1) {
            out.put_uvarint(WireU64::from(WireUsize::from(above)));
        }
        out.put_uvarint(WireU64::from(WireUsize::from(cells.cells().len())));
        for cell in cells.cells() {
            encode_rule_side(out, cell.source());
            encode_rule_side(out, cell.target());
        }
    }
    // A holder's segment closes with its role's tag.
    if let Maybe::Present(role) = declaration.role()
        && (kind == tags::KIND_DATA_ROLED || held)
    {
        out.put_tag(role_tag(role));
    }
}

/// The base-type atom byte a literal identity test's base writes.
///
/// # Specification
/// trivial.
#[inline]
const fn identity_base_tag(base: crate::IdentityBase) -> WireTag
{
    match base {
        crate::IdentityBase::Integer => tags::BASE_INTEGER,
        crate::IdentityBase::Text => tags::BASE_STRING,
    }
}

/// The kind tag that `declaration`'s segment opens with: the first kind, in
/// this order, whose fields the declaration has.
///
/// # Specification
/// - ensures: a definition holding a role is [`tags::KIND_DEF_ROLED`], whose
///   segment writes the pair, law, rule and cover blocks whatever their counts.
///   A coinductive datatype with no indices, rules or cells is
///   [`tags::KIND_DATA_COINDUCTIVE`], and it writes no role. A datatype holding
///   a role and no indices, rules or cells is [`tags::KIND_DATA_ROLED`]. A
///   datatype holder or a coinductive datatype with them writes that richer
///   kind and no role or mark. No canonical holder or coinductive datatype has
///   them, and the kernel refuses one that has them, so its mark never crosses.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each kind's fixture writes its own tag, and a holder
///   writes the role kind.
/// - witness: `encode::tests::a_role_closes_a_holder_s_segment_5304`
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
#[inline]
#[spec(ensures: |ret| (ret == tags::KIND_DEF_ROLED) == (matches!(declaration.role(), Maybe::Present(_)) && matches!(*declaration.content(), DeclarationContent::Def { .. })))]
fn kind_tag(declaration: &Declaration) -> WireTag
{
    let held = matches!(declaration.role(), Maybe::Present(_));
    match *declaration.content() {
        DeclarationContent::Data { ref indices, .. }
            if !indices.is_empty() && !declaration.presentation().rules().is_empty() =>
        {
            tags::KIND_DATA_INDEXED_PRESENTED
        },
        DeclarationContent::Data { ref indices, .. } if !indices.is_empty() => {
            tags::KIND_DATA_INDEXED
        },
        DeclarationContent::Data { .. }
            if declaration
                .presentation()
                .cells()
                .is_some_and(|cells| usize::from(cells.reflexivities()) != 0) =>
        {
            tags::KIND_DATA_WORDS_HIGHER
        },
        DeclarationContent::Data { .. } if declaration.presentation().cells().is_some() => {
            tags::KIND_DATA_WORDS
        },
        DeclarationContent::Data { .. } if !declaration.presentation().rules().is_empty() => {
            tags::KIND_DATA_PRESENTED
        },
        DeclarationContent::Data { .. }
            if declaration.fixpoint() == crate::DataFixpoint::Greatest =>
        {
            tags::KIND_DATA_COINDUCTIVE
        },
        DeclarationContent::Data { .. } if held => tags::KIND_DATA_ROLED,
        DeclarationContent::Data { .. } => tags::KIND_DATA,
        DeclarationContent::Codata { .. } => tags::KIND_CODATA,
        DeclarationContent::Def { .. } if held => tags::KIND_DEF_ROLED,
        DeclarationContent::Def { .. } if !declaration.covers().is_empty() => {
            tags::KIND_DEF_COVERED
        },
        DeclarationContent::Def { .. } if !declaration.operation_rules().rules().is_empty() => {
            tags::KIND_DEF_RULED
        },
        DeclarationContent::Def { .. } if !declaration.laws().is_empty() => tags::KIND_DEF_LAWFUL,
        DeclarationContent::Def { .. } if !declaration.related().is_empty() => {
            tags::KIND_DEF_RELATING
        },
        DeclarationContent::Def { .. } => tags::KIND_DEF,
        DeclarationContent::Axiom { .. } => tags::KIND_AXIOM,
        DeclarationContent::LiteralIdentity { .. } => tags::KIND_LITERAL_IDENTITY,
        DeclarationContent::AbstractType {
            interface: Maybe::Present(ref interface),
            ..
        } if matches!(interface.law(), Maybe::Present(_)) => tags::KIND_ABSTRACT_LAWFUL,
        DeclarationContent::AbstractType {
            interface: Maybe::Present(_),
            ..
        } => tags::KIND_ABSTRACT_INTERFACED,
        DeclarationContent::AbstractType { .. } => tags::KIND_ABSTRACT_TYPE,
    }
}

/// The tag that `role` is written as.
///
/// # Specification
/// trivial.
#[inline]
const fn role_tag(role: crate::Builtin) -> WireTag
{
    match role {
        crate::Builtin::IrSignature => tags::ROLE_IR_SIGNATURE,
        crate::Builtin::IrArgs => tags::ROLE_IR_ARGS,
        crate::Builtin::IrDecode => tags::ROLE_IR_DECODE,
        crate::Builtin::IrPair => tags::ROLE_IR_PAIR,
    }
}

/// Write a definition's stage signature into its erasure slot: the binder
/// count, zero for a signature binding none; then each binder's bound, zero
/// for none and one past the earlier binder's ordinal otherwise; then the
/// mark count and each mark's binder, reach — zero at the binder, the depth
/// below it — path length and steps.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a signature binding no stage writes the one byte an empty slot
///   writes, so a definition quantified over none crosses as it did before the
///   slot was live.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a signature with a bound binder and two marks writes its
///   literal bytes and decodes to itself; an empty one writes zero.
/// - witness: `encode::tests::a_stage_signature_fills_the_erasure_slot`
#[spec(
    captures: entry = out.as_image().as_ref().len(),
    ensures: !stages.bounds().is_empty() || out.as_image().as_ref().get(entry ..) == Some(&[0_u8][..]),
)]
fn encode_stage_signature(
    out: &mut EncodedArtifact,
    stages: &crate::stage_signature::StageSignature,
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(stages.bounds().len())));
    if stages.bounds().is_empty() {
        return;
    }
    for &bound in stages.bounds() {
        out.put_uvarint(WireU64::from(WireUsize::from(match bound {
            crate::stage_signature::StageBound::Unbounded => 0_usize,
            crate::stage_signature::StageBound::Below(binder) => {
                usize::from(binder).saturating_add(1)
            },
        })));
    }
    out.put_uvarint(WireU64::from(WireUsize::from(stages.marks().len())));
    for mark in stages.marks() {
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(mark.binder()))));
        out.put_uvarint(WireU64::from(match mark.reach() {
            crate::stage_signature::StageReach::At => 0_u64,
            crate::stage_signature::StageReach::Below(depth) => u64::from(u32::from(depth)),
        }));
        out.put_uvarint(WireU64::from(WireUsize::from(mark.path().len())));
        for &step in mark.path() {
            out.put_uvarint(WireU64::from(WireUsize::from(usize::from(step))));
        }
    }
}

/// Write one rule side: its node count, then each node's tag and ordinal in
/// pre-order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the count and every node are written, in order, and nothing else.
/// - provides: the one spelling of a side, a rule's and a cell's endpoint
///   alike, that `decode_rule_side` reads back.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a presented declaration and a type of words round-trip
///   every side.
/// - witness: `encode::tests::a_presented_data_declaration_closes_its_segment_with_its_rules`
/// - witness: `encode::tests::a_type_of_words_closes_its_segment_with_its_cells`
#[spec(captures: before = out.as_image().as_ref().len(), ensures: out.as_image().as_ref().len() > before)]
fn encode_rule_side(
    out: &mut EncodedArtifact,
    side: &[crate::presented::RuleNode],
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(side.len())));
    for &node in side {
        let (tag, ordinal) = match node {
            crate::presented::RuleNode::Constructor(tag) => (
                tags::RULE_CONSTRUCTOR,
                WireU64::from(WireUsize::from(usize::from(tag))),
            ),
            crate::presented::RuleNode::Variable(variable) => (
                tags::RULE_VARIABLE,
                WireU64::from(u64::from(u32::from(variable))),
            ),
        };
        out.put_tag(tag);
        out.put_uvarint(ordinal);
    }
}

/// Write one side of an operation's rule: its node count, then each node's
/// tag and payload in pre-order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the count and every node are written, in order, and nothing else:
///   an operation as its position and arity, a constructor as its data
///   declaration's position and its ordinal, a results tuple as its count, a
///   variable as its ordinal.
/// - provides: the one spelling of an operation's side, which
///   `decode_operation_side` reads back.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a ruled definition round-trips every side.
/// - witness: `encode::tests::a_ruled_definition_closes_its_segment_with_its_rules`
#[spec(captures: before = out.as_image().as_ref().len(), ensures: out.as_image().as_ref().len() > before)]
fn encode_operation_side(
    out: &mut EncodedArtifact,
    side: &[crate::operation_rules::OperationNode],
    positions: &mut Positions,
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(side.len())));
    for &node in side {
        match node {
            crate::operation_rules::OperationNode::Operation { constant, arity } => {
                out.put_tag(tags::RULE_OPERATION);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(
                    positions.rename(constant),
                ))));
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(arity))));
            },
            crate::operation_rules::OperationNode::Constructor { family, tag } => {
                out.put_tag(tags::RULE_CONSTRUCTOR);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(
                    positions.rename(family),
                ))));
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(tag))));
            },
            crate::operation_rules::OperationNode::Results(count) => {
                out.put_tag(tags::RULE_RESULTS);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(count))));
            },
            crate::operation_rules::OperationNode::Variable(variable) => {
                out.put_tag(tags::RULE_VARIABLE);
                out.put_uvarint(WireU64::from(u64::from(u32::from(variable))));
            },
        }
    }
}

/// Write the structured-name record: a segment count, then each segment as
/// length-prefixed UTF-8.
///
/// An unnamed declaration writes a zero count and nothing else, so its segment
/// is the same bytes whatever names its neighbours carry.
///
/// # Specification
/// - requires: nothing — a segment's constructor already refused the separator.
/// - ensures: appends the segment count and then each segment's byte length and
///   bytes, outermost segment first.
/// - provides: the record a reader rebuilds the name from, segment by segment,
///   so no dotted string is ever the wire form of a name.
/// - fails: never.
/// - panics: none.
///
/// # Cost
/// - allocation: the minted-atom table of abstract-type positions, growth
///   within the sequence's declarations
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, including names, admission
///   marks, shared globals, root order and reserved slots. A separate position
///   model and a nonempty provenance fixture distinguish declaration positions
///   from table indices and preserve claimed order. Existing refusal and
///   differently shared fixtures cover table disagreements and canonical
///   deduplication. The finite examples do not prove typing, provenance truth
///   or independent correctness through round-trip self-agreement.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
/// - witness: `decl::tests::names_classify_the_separator_without_normalizing_unicode`
/// - witness: `tests::sharing_format::a_structured_name_round_trips_as_segments`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        let count = u64::try_from(name.segments().len()).unwrap_or(u64::MAX);
        let fields = name.segments().iter().fold(0_usize,
        |total, segment| total.saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from((segment.as_ref()).len()).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX).saturating_add((segment.as_ref()).len())));
        bytes.len() == start.saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(fields)
            && { let scalar = count;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }
            && name.segments().last().is_none_or(|segment| bytes.ends_with(segment.as_ref().as_bytes())) },
)]
fn encode_structured_name(
    out: &mut EncodedArtifact,
    name: &StructuredName,
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(name.segments().len())));
    for segment in name.segments() {
        encode_text(out, ArtifactText::from(segment.as_ref()));
    }
}

/// Write the sealing-provenance slot: a count followed by admission positions.
///
/// A declaration no projection touched writes a zero count, which is
/// byte-identical to what the slot carried while it was reserved — so filling
/// the slot moved no other field and invalidated no artifact.
///
/// # Specification
/// - requires: `provenance` holds the admission positions the declaration's
///   projection rebound, in the order the artifact carries them.
/// - ensures: appends the count and then those positions in that order; a
///   declaration no projection touched writes a zero count and nothing else.
/// - provides: the slot's filling, byte-identical to the reserved form on the
///   empty case, so filling it moved no other field.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, including names, admission
///   marks, shared globals, root order and reserved slots. A separate position
///   model and a nonempty provenance fixture distinguish declaration positions
///   from table indices and preserve claimed order. Existing refusal and
///   differently shared fixtures cover table disagreements and canonical
///   deduplication. The finite examples do not prove typing, provenance truth
///   or independent correctness through round-trip self-agreement.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        let count = u64::try_from(provenance.len()).unwrap_or(u64::MAX);
        let fields = provenance.iter().fold(0_usize,
        |total, &atom| total.saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from(usize::from(atom)).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)));
        bytes.len() == start.saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(fields)
            && { let scalar = count;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) } },
)]
fn encode_sealing_provenance(
    out: &mut EncodedArtifact,
    provenance: &[ConstantIndex],
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(provenance.len())));
    for &atom in provenance {
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(atom))));
    }
}

/// Intern a root's sub-DAG, appending each first-completed entry to `segment`,
/// and return the root's global index.
///
/// # Specification
/// - requires: all reachable ids resolve in this acyclic arena; the memo
///   belongs to earlier roots of this unchanged arena and global assignments
///   fit the index space.
/// - ensures: assigns reachable nodes globals, appends newly completed content
///   in post-order first-completion order and returns the root’s memoized
///   index; an already memoized root changes neither segment nor memo; a staged
///   value type takes its base's index and appends nothing.
/// - provides: content-keyed sharing across segments, with captured counts
///   checking reuse and one appended entry per new content key without cloning
///   either map.
/// - fails: never within the live, acyclic domain.
/// - panics: none within that domain.
/// - intension: uses a resumable heap stack rather than host recursion.
///   Tree-map lookups and byte-key comparisons add logarithmic and
///   payload-dependent costs; shared subgraphs are not expanded.
///
/// # Cost
/// - allocation: the entries, the memos and the children's references, growth
///   within the root's nodes.
///
/// # Adequacy
/// - hypothesis: L3 observes exact segment entries, assigned indices and memo
///   state across repeated ids, distinct equal nodes, a new parent, a second
///   segment and reversed children. This separates id-keyed deduplication, memo
///   loss, redundant entries and incorrect post-order assignment. Deep and
///   differently shared integration fixtures supplement these bounded
///   transitions; a shared encode/decode round trip is not an independent
///   format oracle.
/// - witness: `encode::tests::interning_reuses_content_across_segments_without_losing_order`
/// - witness: `encode::tests::a_staged_type_is_written_as_its_base`
/// - witness: `tests::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
/// - witness: `tests::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
#[spec(requires: match root { AnyNode::ValueType(id) => arena.value_type(id).is_some(), AnyNode::CompType(id) => arena.comp_type(id).is_some(), AnyNode::Value(id) => arena.value(id).is_some(), AnyNode::Computation(id) => arena.computation(id).is_some() },

    captures: entry = (interner.node(root), interner.by_node.len(), interner.by_content.len(), segment.len(), interner.next),
    ensures: |ret| interner.node(root) == Some(ret)
            && interner.by_node.len() >= entry.1
            && interner.by_content.len() >= entry.2
            && segment.len() == entry.3.saturating_add(interner.by_content.len().saturating_sub(entry.2))
            && u32::from(interner.next) == u32::from(entry.4).saturating_add(u32::try_from(interner.by_content.len().saturating_sub(entry.2)).unwrap_or(u32::MAX))
            && entry.0.is_none_or(|prior| ret == prior
            && interner.by_node.len() == entry.1
            && interner.by_content.len() == entry.2
            && segment.len() == entry.3),
)]
fn intern(
    arena: &TermArena,
    interner: &mut Interner,
    segment: &mut SmallVec<EncodedEntry, 0, Global>,
    root: AnyNode,
) -> GlobalIndex
{
    let mut stack: SmallVec<(AnyNode, usize), 0, Global> = SmallVec::<_, 0, Global>::new();
    stack.push((root, 0_usize));
    // The children's indices of the node being written, refilled per node.
    let mut child_globals: SmallVec<GlobalIndex, 0, Global> = SmallVec::<_, 0, Global>::new();
    // The children as an entry writes them, refilled per node: each global
    // index for the content deduplication, then each reference of the segment
    // for the bytes the segment writes.
    let mut child_words: SmallVec<WireU64, 0, Global> = SmallVec::<_, 0, Global>::new();
    while let Some((node, cursor)) = stack.pop() {
        if interner.node(node).is_some() {
            continue;
        }
        let children = arena.children_of(node);
        let mut next = cursor;
        let mut descended = false;
        while let Some(&child) = children.get(next) {
            if interner.node(child).is_some() {
                next = next.saturating_add(1);
            }
            else {
                stack.push((node, next.saturating_add(1)));
                stack.push((child, 0_usize));
                descended = true;
                break;
            }
        }
        if descended {
            continue;
        }
        // A stage is admission's alone: the wire holds the type it refines, so
        // a staged node takes its base's index and writes no entry.
        if let AnyNode::ValueType(id) = node
            && let Some(&ValueType::Staged { base, .. }) = arena.value_type(id)
        {
            let global = interner.node(AnyNode::ValueType(base)).unwrap_or_default();
            interner.assign(node, global);
            continue;
        }
        child_globals.clear();
        child_globals.extend(
            children
                .iter()
                .map(|&child| interner.node(child).unwrap_or_default()),
        );
        interner.positions.open_entry(EntryNaming::Local);
        // The head, the tag and the inline payload, comes before the children,
        // so the content is the head and then each child's global index.
        let EncodedEntry(mut bytes) = encode_entry(arena, node, &[], &mut interner.positions);
        let head = usize::from(bytes.as_image().length());
        for &child in &child_globals {
            bytes.put_uvarint(WireU64::from(u64::from(u32::from(child))));
        }
        let content = EntryContent {
            bytes: EncodedEntry(bytes),
            names: Box::from(interner.positions.entry_names()),
        };
        let global = if let Some(global) = interner.content(&content) {
            global
        }
        else {
            // An entry writes each child by its segment's reference, and each
            // key it names by its segment's table. A head that names no key
            // writes as the content's head does, so it is not written again.
            let written = if content.names.is_empty() {
                // A reference is rarely a byte wider than the global index it
                // stands for, so the room of the content and a byte for each
                // child holds the entry.
                let mut written = EncodedArtifact::with_capacity(ByteCount::from(
                    usize::from(content.bytes.0.as_image().length())
                        .saturating_add(child_globals.len()),
                ));
                written.put_image(ArtifactImage::from(
                    content
                        .bytes
                        .0
                        .as_image()
                        .as_ref()
                        .get(.. head)
                        .unwrap_or_default(),
                ));
                for &child in &child_globals {
                    let word = interner.reference(child);
                    written.put_uvarint(word);
                }
                EncodedEntry(written)
            }
            else {
                child_words.clear();
                for &child in &child_globals {
                    let word = interner.reference(child);
                    child_words.push(word);
                }
                interner.positions.open_entry(EntryNaming::Table);
                encode_entry(arena, node, &child_words, &mut interner.positions)
            };
            let assigned = interner.next;
            interner.next = interner.next.next();
            segment.push(written);
            let _prior = interner.by_content.insert(content, assigned);
            assigned
        };
        interner.positions.open_entry(EntryNaming::Table);
        interner.assign(node, global);
    }
    interner.node(root).unwrap_or_default()
}

/// Write one subterm-table entry: its node tag, its inline payload, then the
/// word of each child: its global index for the content deduplication, or its
/// reference in the segment for the bytes the segment writes.
///
/// Negative families have no nullary unit. An absent id is outside the encoding
/// domain, not a request to invent a substitute node or emit a partial entry.
///
/// # Specification
/// - requires: node resolves in arena, and the supplied words name its children
///   in wire-field order, or none of them for the head alone.
/// - ensures: writes that live node’s exact frozen tag, canonical inline
///   payload and supplied child words.
/// - provides: a byte-content deduplication key. The predicate checks liveness
///   and the tag; literal fixtures check payloads and distinguishable ordered
///   child fields.
/// - fails: never within the live-node domain.
/// - panics: none within that domain; enabled checks reject a missing id.
///
/// # Adequacy
/// - hypothesis: L3 observes literal entry bytes for every frozen former, every
///   base atom, both injection sides, nonzero inline levels and distinguishable
///   one-, two- and three-child index sequences crossing varint boundaries.
///   This separates tag reassignment, child permutation, missing payloads and
///   lost high bits. It covers live nodes and supplied global assignments, not
///   formation; a separate enforced boundary witness rejects stale ids in every
///   family.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
/// - witness: `encode::tests::stale_roots_violate_the_encoding_domain`
#[spec(requires: match node { AnyNode::ValueType(id) => arena.value_type(id).is_some_and(|value_type| !matches!(value_type, ValueType::Staged { .. })), AnyNode::CompType(id) => arena.comp_type(id).is_some(), AnyNode::Value(id) => arena.value(id).is_some(), AnyNode::Computation(id) => arena.computation(id).is_some() },
ensures: |ret| ret.0.as_image().as_ref().first().copied()
    == Some(u8::from(match node {
        AnyNode::ValueType(id) => match arena.value_type(id) {
            Some(&ValueType::Data { .. }) => tags::NODE_VT_DATA,
            Some(&ValueType::Record(_)) => tags::NODE_VT_RECORD,
            Some(&ValueType::PathUniverse(..)) => tags::NODE_VT_PATH_UNIVERSE,
            Some(&ValueType::FlowUniverse(..)) => tags::NODE_VT_FLOW_UNIVERSE,
            Some(&ValueType::Path { .. }) => tags::NODE_VT_PATH,
            Some(&ValueType::Flow { .. }) => tags::NODE_VT_FLOW,
            Some(&ValueType::Bridge { .. }) => tags::NODE_VT_BRIDGE,
            Some(&ValueType::Base(_)) => tags::NODE_VT_BASE,
            Some(&ValueType::Universe { sort: GroundSort::Value, .. }) => tags::NODE_VT_UNIVERSE,
            Some(&ValueType::Universe { sort: GroundSort::Computation, .. }) => {
                tags::NODE_VT_COMPUTATION_UNIVERSE
            },
            Some(&ValueType::Abstract(_)) => tags::NODE_VT_ABSTRACT,
            None | Some(&ValueType::Product(_) | &ValueType::Staged { .. }) => tags::NODE_VT_PRODUCT,
            Some(&ValueType::Sigma { .. }) => tags::NODE_VT_SIGMA,
            Some(&ValueType::Sum(..)) => tags::NODE_VT_SUM,
            Some(&ValueType::Session { .. }) => tags::NODE_VT_SESSION,
            Some(&ValueType::List(_)) => tags::NODE_VT_LIST,
            Some(&ValueType::Thunk(_)) => tags::NODE_VT_THUNK,
            Some(&ValueType::Lift { .. }) => tags::NODE_VT_LIFT,
            Some(&ValueType::Element { .. }) => tags::NODE_VT_ELEMENT,
            Some(&ValueType::StaticPi { .. }) => tags::NODE_VT_STATIC_PI,
        },
        AnyNode::CompType(id) => match arena.comp_type(id) {
            None | Some(&CompType::Returner(_)) => tags::NODE_CT_RETURNER,
            Some(&CompType::Returns(_)) => tags::NODE_CT_RETURNS,
            Some(&CompType::Arrow { .. }) => tags::NODE_CT_ARROW,
            Some(&CompType::Pi { .. }) => tags::NODE_CT_PI,
            Some(&CompType::Element { .. }) => tags::NODE_CT_ELEMENT,
            Some(&CompType::With(..)) => tags::NODE_CT_WITH,
            Some(&CompType::Codata { .. }) => tags::NODE_CT_CODATA,
        },
        AnyNode::Value(id) => match arena.value(id) {
            Some(&Value::Constructor { .. }) => tags::NODE_V_CONSTRUCTOR,
            Some(&Value::Record(_)) => tags::NODE_V_RECORD,
            Some(&Value::Restrict { .. }) => tags::NODE_V_RESTRICT,
            Some(&Value::SessionPath { .. }) => tags::NODE_V_SESSION_PATH,
            Some(&Value::SessionFlow { .. }) => tags::NODE_V_SESSION_FLOW,
            Some(&Value::Stay { .. }) => tags::NODE_V_STAY,
            Some(&Value::ForwardFlow { .. }) => tags::NODE_V_FORWARD_FLOW,
            Some(&Value::FunctionFlow { .. }) => tags::NODE_V_FUNCTION_FLOW,
            Some(&Value::Then { .. }) => tags::NODE_V_THEN,
            Some(&Value::FlowProduct(..)) => tags::NODE_V_FLOW_PRODUCT,
            Some(&Value::PathRefl(_)) => tags::NODE_V_PATH_REFL,
            Some(&Value::PathProduct(..)) => tags::NODE_V_PATH_PRODUCT,
            Some(&Value::PathEquiv { .. }) => tags::NODE_V_PATH_EQUIV,
            Some(&Value::Univalence { .. }) => tags::NODE_V_UNIVALENCE,
            Some(&Value::Here { .. }) => tags::NODE_V_HERE,
            Some(&Value::Returned(_)) => tags::NODE_V_RETURNED,
            Some(&Value::Higher { .. }) => tags::NODE_V_HIGHER,
            Some(&Value::HigherEvaluation { .. }) => tags::NODE_V_HIGHER_EVALUATION,
            Some(&Value::QuantifiedEvaluation { .. }) => tags::NODE_V_QUANTIFIED_EVALUATION,
            Some(&Value::Variable(_)) => tags::NODE_V_VARIABLE,
            Some(&Value::Constant(_)) => tags::NODE_V_CONSTANT,
            Some(&Value::Literal(_)) => tags::NODE_V_LITERAL,
            None | Some(&Value::Tuple(_)) => tags::NODE_V_TUPLE,
            Some(&Value::Injection(..)) => tags::NODE_V_INJECTION,
            Some(&Value::ListNil) => tags::NODE_V_LIST_NIL,
            Some(&Value::ListCons(..)) => tags::NODE_V_LIST_CONS,
            Some(&Value::Thunk(_)) => tags::NODE_V_THUNK,
            Some(&Value::Lift { .. }) => tags::NODE_V_LIFT,
            Some(&Value::Quote(_)) => tags::NODE_V_QUOTE,
            Some(&Value::QuoteComputation(_)) => tags::NODE_V_QUOTE_COMPUTATION,
            Some(&Value::StaticApplication(..)) => tags::NODE_V_STATIC_APPLICATION,
        },
        AnyNode::Computation(id) => match arena.computation(id) {
            Some(&Computation::DataCase { equations, .. }) => {
                if equations == crate::EquationCount::NONE {
                    tags::NODE_C_DATA_CASE
                }
                else {
                    tags::NODE_C_INDEXED_DATA_CASE
                }
            },
            Some(&Computation::SigmaSplit { .. }) => tags::NODE_C_SIGMA_SPLIT,
            Some(&Computation::RecordProjection(..)) => tags::NODE_C_RECORD_PROJECTION,
            Some(&Computation::TupleProjection(..)) => tags::NODE_C_TUPLE_PROJECTION,
            Some(&Computation::Transport(..)) => tags::NODE_C_TRANSPORT,
            Some(&Computation::PathTransport { .. }) => tags::NODE_C_PATH_TRANSPORT,
            Some(&Computation::TelescopeTransport { .. }) => tags::NODE_C_TELESCOPE_TRANSPORT,
            Some(&Computation::Ride { .. }) => tags::NODE_C_RIDE,
            Some(&Computation::TelescopeRide { .. }) => tags::NODE_C_TELESCOPE_RIDE,
            Some(&Computation::RelatedApplication { .. }) => tags::NODE_C_RELATED_APPLICATION,
            None | Some(&Computation::Return(_)) => tags::NODE_C_RETURN,
            Some(&Computation::Lambda(_)) => tags::NODE_C_LAMBDA,
            Some(&Computation::Fixpoint { .. }) => tags::NODE_C_FIXPOINT,
            Some(&Computation::Application(..)) => tags::NODE_C_APPLICATION,
            Some(&Computation::Bind(..)) => tags::NODE_C_BIND,
            Some(&Computation::ReturnAll(_)) => tags::NODE_C_RETURN_ALL,
            Some(&Computation::BindAll { .. }) => tags::NODE_C_BIND_ALL,
            Some(&Computation::Force(_)) => tags::NODE_C_FORCE,
            Some(&Computation::Case { .. }) => tags::NODE_C_CASE,
            Some(&Computation::ListFold { .. }) => tags::NODE_C_LIST_FOLD,
            Some(&Computation::ListCase { .. }) => tags::NODE_C_LIST_CASE,
            Some(&Computation::With(..)) => tags::NODE_C_WITH,
            Some(&Computation::Project(..)) => tags::NODE_C_PROJECT,
        },
    })))]
fn encode_entry(
    arena: &TermArena,
    node: AnyNode,
    children: &[WireU64],
    positions: &mut Positions,
) -> EncodedEntry
{
    let mut out = EncodedArtifact::new();
    match node {
        AnyNode::ValueType(id) => match arena.value_type(id) {
            None => {
                out.put_tag(tags::NODE_VT_PRODUCT);
                out.put_uvarint(WireU64::from(WireUsize::from(0_usize)));
            },
            Some(value_type) => match *value_type {
                ValueType::Data {
                    declaration,
                    ref arguments,
                } => {
                    out.put_tag(tags::NODE_VT_DATA);
                    let written = positions.rename(declaration);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(written))));
                    out.put_uvarint(WireU64::from(WireUsize::from(arguments.len())));
                },
                ValueType::Record(ref fields) => {
                    out.put_tag(tags::NODE_VT_RECORD);
                    out.put_uvarint(WireU64::from(WireUsize::from(fields.len())));
                    for label in fields.keys() {
                        encode_text(&mut out, ArtifactText::from(label.as_ref()));
                    }
                },
                ValueType::Base(base) => {
                    out.put_tag(tags::NODE_VT_BASE);
                    out.put_tag(base_type_tag(base));
                },
                ValueType::PathUniverse(..) => out.put_tag(tags::NODE_VT_PATH_UNIVERSE),
                ValueType::FlowUniverse(..) => out.put_tag(tags::NODE_VT_FLOW_UNIVERSE),
                ValueType::Path { .. } => out.put_tag(tags::NODE_VT_PATH),
                ValueType::Flow { .. } => out.put_tag(tags::NODE_VT_FLOW),
                ValueType::Bridge { .. } => out.put_tag(tags::NODE_VT_BRIDGE),
                ValueType::Universe {
                    sort: GroundSort::Value,
                    ref level,
                } => {
                    out.put_tag(tags::NODE_VT_UNIVERSE);
                    encode_level(&mut out, level);
                },
                ValueType::Universe {
                    sort: GroundSort::Computation,
                    ref level,
                } => {
                    out.put_tag(tags::NODE_VT_COMPUTATION_UNIVERSE);
                    encode_level(&mut out, level);
                },
                ValueType::Abstract(atom) => {
                    out.put_tag(tags::NODE_VT_ABSTRACT);
                    let written = positions.rename(atom);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(written))));
                },
                ValueType::Product(ref components) => {
                    out.put_tag(tags::NODE_VT_PRODUCT);
                    out.put_uvarint(WireU64::from(WireUsize::from(components.len())));
                },
                ValueType::Sigma { .. } => out.put_tag(tags::NODE_VT_SIGMA),
                ValueType::Sum(ref summands) => {
                    out.put_tag(tags::NODE_VT_SUM);
                    out.put_uvarint(WireU64::from(WireUsize::from(summands.len())));
                },
                ValueType::Session { ref graph, .. } => {
                    out.put_tag(tags::NODE_VT_SESSION);
                    graph.write(|word| out.put_uvarint(WireU64::from(word.0)));
                },
                ValueType::List(_) => out.put_tag(tags::NODE_VT_LIST),
                ValueType::Thunk(_) => out.put_tag(tags::NODE_VT_THUNK),
                ValueType::Lift { ref target, .. } => {
                    out.put_tag(tags::NODE_VT_LIFT);
                    encode_level(&mut out, target);
                },
                ValueType::Element { ref target, .. } => {
                    out.put_tag(tags::NODE_VT_ELEMENT);
                    encode_level(&mut out, target);
                },
                ValueType::StaticPi { .. } => out.put_tag(tags::NODE_VT_STATIC_PI),
                // Outside the encoding domain, as an absent id is: interning
                // writes a stage's base in its place.
                ValueType::Staged { .. } => {
                    out.put_tag(tags::NODE_VT_PRODUCT);
                    out.put_uvarint(WireU64::from(WireUsize::from(0_usize)));
                },
            },
        },
        AnyNode::CompType(id) => match arena.comp_type(id) {
            Some(&CompType::Returner(_)) | None => out.put_tag(tags::NODE_CT_RETURNER),
            Some(&CompType::Returns(ref results)) => {
                out.put_tag(tags::NODE_CT_RETURNS);
                out.put_uvarint(WireU64::from(WireUsize::from(results.len())));
            },
            Some(&CompType::Arrow { .. }) => out.put_tag(tags::NODE_CT_ARROW),
            Some(&CompType::Pi { .. }) => out.put_tag(tags::NODE_CT_PI),
            Some(&CompType::Element { ref target, .. }) => {
                out.put_tag(tags::NODE_CT_ELEMENT);
                encode_level(&mut out, target);
            },
            Some(&CompType::With(ref components)) => {
                out.put_tag(tags::NODE_CT_WITH);
                out.put_uvarint(WireU64::from(WireUsize::from(components.len())));
            },
            Some(&CompType::Codata {
                declaration,
                ref arguments,
            }) => {
                out.put_tag(tags::NODE_CT_CODATA);
                let written = positions.rename(declaration);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(written))));
                out.put_uvarint(WireU64::from(WireUsize::from(arguments.len())));
            },
        },
        AnyNode::Value(id) => match arena.value(id) {
            None => {
                out.put_tag(tags::NODE_V_TUPLE);
                out.put_uvarint(WireU64::from(WireUsize::from(0_usize)));
            },
            Some(value) => match *value {
                Value::Constructor {
                    family,
                    tag,
                    ref fields,
                    ..
                } => {
                    out.put_tag(tags::NODE_V_CONSTRUCTOR);
                    let written = positions.rename(family);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(written))));
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(tag))));
                    out.put_uvarint(WireU64::from(WireUsize::from(fields.len())));
                },
                Value::Record(ref fields) => {
                    out.put_tag(tags::NODE_V_RECORD);
                    out.put_uvarint(WireU64::from(WireUsize::from(fields.len())));
                    for label in fields.keys() {
                        encode_text(&mut out, ArtifactText::from(label.as_ref()));
                    }
                },
                Value::Restrict { ref fixed, .. } => {
                    out.put_tag(tags::NODE_V_RESTRICT);
                    out.put_uvarint(WireU64::from(WireUsize::from(fixed.len())));
                    for label in fixed.keys() {
                        encode_text(&mut out, ArtifactText::from(label.as_ref()));
                    }
                },
                Value::Variable(index) => {
                    out.put_tag(tags::NODE_V_VARIABLE);
                    out.put_uvarint(WireU64::from(u64::from(u32::from(index))));
                },
                Value::Constant(index) => {
                    out.put_tag(tags::NODE_V_CONSTANT);
                    let written = positions.rename(index);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(written))));
                },
                Value::SessionPath { ref evidence, .. } => {
                    out.put_tag(tags::NODE_V_SESSION_PATH);
                    evidence.write(|word| out.put_uvarint(WireU64::from(word.0)));
                },
                Value::SessionFlow { ref evidence, .. } => {
                    out.put_tag(tags::NODE_V_SESSION_FLOW);
                    evidence.write(|word| out.put_uvarint(WireU64::from(word.0)));
                },
                Value::Stay { ref dialogues, .. } => {
                    out.put_tag(tags::NODE_V_STAY);
                    for word in crate::identity::endpoint_words(dialogues) {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::ForwardFlow { ref dialogues, .. } => {
                    out.put_tag(tags::NODE_V_FORWARD_FLOW);
                    for word in crate::identity::forward_words(dialogues) {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::FunctionFlow { .. } => out.put_tag(tags::NODE_V_FUNCTION_FLOW),
                Value::Then { seam, .. } => {
                    out.put_tag(tags::NODE_V_THEN);
                    out.put_tag(seam_tag(seam));
                },
                Value::FlowProduct(..) => out.put_tag(tags::NODE_V_FLOW_PRODUCT),
                Value::PathRefl(_) => out.put_tag(tags::NODE_V_PATH_REFL),
                Value::PathProduct(..) => out.put_tag(tags::NODE_V_PATH_PRODUCT),
                Value::PathEquiv { ref evidence, .. } => {
                    out.put_tag(tags::NODE_V_PATH_EQUIV);
                    for word in evidence.words() {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::Univalence { .. } => out.put_tag(tags::NODE_V_UNIVALENCE),
                Value::Here { ref dialogues, .. } => {
                    out.put_tag(tags::NODE_V_HERE);
                    for word in crate::identity::endpoint_words(dialogues) {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::Returned(_) => out.put_tag(tags::NODE_V_RETURNED),
                Value::Higher { ref program, .. } => {
                    out.put_tag(tags::NODE_V_HIGHER);
                    for word in program.words() {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::HigherEvaluation { ref dialogues, .. } => {
                    out.put_tag(tags::NODE_V_HIGHER_EVALUATION);
                    for word in crate::identity::evaluation_words(dialogues) {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::QuantifiedEvaluation { ref steps, .. } => {
                    out.put_tag(tags::NODE_V_QUANTIFIED_EVALUATION);
                    for word in crate::identity::quantified_words(steps) {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::Literal(ref literal) => {
                    out.put_tag(tags::NODE_V_LITERAL);
                    encode_literal(&mut out, literal);
                },
                Value::Tuple(ref components) => {
                    out.put_tag(tags::NODE_V_TUPLE);
                    out.put_uvarint(WireU64::from(WireUsize::from(components.len())));
                },
                Value::ListNil => out.put_tag(tags::NODE_V_LIST_NIL),
                Value::ListCons(..) => out.put_tag(tags::NODE_V_LIST_CONS),
                Value::Injection(summand, _) => {
                    out.put_tag(tags::NODE_V_INJECTION);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(summand))));
                },
                Value::Thunk(_) => out.put_tag(tags::NODE_V_THUNK),
                Value::Lift { ref target, .. } => {
                    out.put_tag(tags::NODE_V_LIFT);
                    encode_level(&mut out, target);
                },
                Value::Quote(_) => out.put_tag(tags::NODE_V_QUOTE),
                Value::QuoteComputation(_) => out.put_tag(tags::NODE_V_QUOTE_COMPUTATION),
                Value::StaticApplication(..) => out.put_tag(tags::NODE_V_STATIC_APPLICATION),
            },
        },
        AnyNode::Computation(id) => match arena.computation(id) {
            Some(&Computation::DataCase {
                ref branches,
                equations,
                ..
            }) => {
                if equations == crate::EquationCount::NONE {
                    out.put_tag(tags::NODE_C_DATA_CASE);
                    out.put_uvarint(WireU64::from(WireUsize::from(branches.len())));
                }
                else {
                    out.put_tag(tags::NODE_C_INDEXED_DATA_CASE);
                    out.put_uvarint(WireU64::from(WireUsize::from(branches.len())));
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(equations))));
                }
            },
            Some(&Computation::SigmaSplit { .. }) => out.put_tag(tags::NODE_C_SIGMA_SPLIT),
            Some(&Computation::RecordProjection(_, ref label)) => {
                out.put_tag(tags::NODE_C_RECORD_PROJECTION);
                encode_text(&mut out, ArtifactText::from(label.as_ref()));
            },
            Some(&Computation::TupleProjection(_, component)) => {
                out.put_tag(tags::NODE_C_TUPLE_PROJECTION);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(component))));
            },
            Some(&Computation::Transport(..)) => out.put_tag(tags::NODE_C_TRANSPORT),
            Some(&Computation::PathTransport { .. }) => {
                out.put_tag(tags::NODE_C_PATH_TRANSPORT);
            },
            Some(&Computation::TelescopeTransport { .. }) => {
                out.put_tag(tags::NODE_C_TELESCOPE_TRANSPORT);
            },
            Some(&Computation::Ride { .. }) => out.put_tag(tags::NODE_C_RIDE),
            Some(&Computation::TelescopeRide { .. }) => {
                out.put_tag(tags::NODE_C_TELESCOPE_RIDE);
            },
            Some(&Computation::RelatedApplication { .. }) => {
                out.put_tag(tags::NODE_C_RELATED_APPLICATION);
            },
            Some(&Computation::Lambda(_)) => out.put_tag(tags::NODE_C_LAMBDA),
            Some(&Computation::Fixpoint { evidence, .. }) => {
                out.put_tag(tags::NODE_C_FIXPOINT);
                out.put_tag(evidence_tag(evidence));
                match evidence {
                    crate::FixpointEvidence::Staged { position } => {
                        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(position))));
                    },
                    crate::FixpointEvidence::Joint { positions } => {
                        out.put_uvarint(WireU64::from(WireUsize::from(positions.iter().count())));
                        for position in positions.iter() {
                            out.put_uvarint(WireU64::from(WireUsize::from(usize::from(position))));
                        }
                    },
                    crate::FixpointEvidence::Partial
                    | crate::FixpointEvidence::StructuralDescent
                    | crate::FixpointEvidence::Guarded => {},
                }
            },
            Some(&Computation::Application(..)) => out.put_tag(tags::NODE_C_APPLICATION),
            Some(&Computation::Return(_)) | None => out.put_tag(tags::NODE_C_RETURN),
            Some(&Computation::Bind(..)) => out.put_tag(tags::NODE_C_BIND),
            Some(&Computation::ReturnAll(ref values)) => {
                out.put_tag(tags::NODE_C_RETURN_ALL);
                out.put_uvarint(WireU64::from(WireUsize::from(values.len())));
            },
            Some(&Computation::BindAll { arity, .. }) => {
                out.put_tag(tags::NODE_C_BIND_ALL);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(arity))));
            },
            Some(&Computation::Force(_)) => out.put_tag(tags::NODE_C_FORCE),
            Some(&Computation::Case { ref branches, .. }) => {
                out.put_tag(tags::NODE_C_CASE);
                out.put_uvarint(WireU64::from(WireUsize::from(branches.len())));
            },
            Some(&Computation::ListFold { .. }) => out.put_tag(tags::NODE_C_LIST_FOLD),
            Some(&Computation::ListCase { .. }) => out.put_tag(tags::NODE_C_LIST_CASE),
            Some(&Computation::With(ref components)) => {
                out.put_tag(tags::NODE_C_WITH);
                out.put_uvarint(WireU64::from(WireUsize::from(components.len())));
            },
            Some(&Computation::Project(component, _)) => {
                out.put_tag(tags::NODE_C_PROJECT);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(component))));
            },
        },
    }
    for &child in children {
        out.put_uvarint(child);
    }
    EncodedEntry(out)
}

/// Write a declaration's prenex level signature.
///
/// # Specification
/// - requires: `signature`'s constraints are in declaration order.
/// - ensures: appends the parameter count, the constraint count, and then each
///   constraint as its relation tag followed by its two levels.
/// - provides: the prenex interface's byte image, in the one order a decoder
///   reads it back in.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares complete appended bytes, including a nonempty
///   prefix, with literal wire fixtures. Text covers NUL, multibyte UTF-8 and
///   the 127/128 and 16383/16384 length boundaries; literals cover every kind
///   and sign plus canonical zero. Levels cover empty, constant, ordered
///   multi-atom and u64-ceiling forms, and signatures distinguish both
///   relations and parameter widths. These separate byte-versus-character
///   lengths, field permutation, prefix damage and lost high bits. Arbitrary
///   payload sizes and allocation failure are outside the fixture domain.
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        let params = u64::from(u32::from(signature.params()));
        ({ let scalar = params;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
            && ({ let scalar = u64::try_from(signature.constraints().len()).unwrap_or(u64::MAX);
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start.saturating_add(usize::try_from(64_u32.saturating_sub((params).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) .. (start.saturating_add(usize::try_from(64_u32.saturating_sub((params).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }) },
)]
fn encode_level_signature(
    out: &mut EncodedArtifact,
    signature: &LevelSignature,
)
{
    out.put_uvarint(WireU64::from(u64::from(u32::from(signature.params()))));
    let constraints = signature.constraints();
    out.put_uvarint(WireU64::from(WireUsize::from(constraints.len())));
    for constraint in constraints {
        out.put_tag(match constraint.relation() {
            ConstraintRelation::Leq => tags::RELATION_LEQ,
            ConstraintRelation::Eq => tags::RELATION_EQ,
        });
        encode_level(out, constraint.left());
        encode_level(out, constraint.right());
    }
}

/// Write a canonical level: its constant part, then its variable atoms in
/// ascending variable order, which is the order the level's own canonical form
/// keeps them in.
///
/// # Specification
/// - requires: `level` is canonical, which is what puts its atoms in ascending
///   variable order.
/// - ensures: appends the constant part, the atom count, and then each atom as
///   its variable index followed by its successor offset.
/// - provides: the level's byte image. The atom order is the level's own
///   canonical order rather than one chosen here, so two canonical levels agree
///   on bytes exactly when they are equal.
/// - panics: none.
///
/// # Cost
/// - allocation: the level's collected atoms and the appended bytes of its
///   image, growth within the level's atoms
///
/// # Adequacy
/// - hypothesis: L3 compares complete appended bytes, including a nonempty
///   prefix, with literal wire fixtures. Text covers NUL, multibyte UTF-8 and
///   the 127/128 and 16383/16384 length boundaries; literals cover every kind
///   and sign plus canonical zero. Levels cover empty, constant, ordered
///   multi-atom and u64-ceiling forms, and signatures distinguish both
///   relations and parameter widths. These separate byte-versus-character
///   lengths, field permutation, prefix damage and lost high bits. Arbitrary
///   payload sizes and allocation failure are outside the fixture domain.
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        let constant = u64::from(level.constant_part());
        let (count, fields) = level.atoms().fold((0_usize, 0_usize),
        |(count, fields), (variable, offset)| (count.saturating_add(1), fields.saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(u32::from(variable.index()))).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(offset)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))));
        let count = u64::try_from(count).unwrap_or(u64::MAX);
        bytes.len() == start.saturating_add(usize::try_from(64_u32.saturating_sub((constant).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(fields)
            && { let scalar = constant;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }
            && { let scalar = count;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start.saturating_add(usize::try_from(64_u32.saturating_sub((constant).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) .. (start.saturating_add(usize::try_from(64_u32.saturating_sub((constant).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) } },
)]
fn encode_level(
    out: &mut EncodedArtifact,
    level: &Level,
)
{
    out.put_uvarint(WireU64::from(u64::from(level.constant_part())));
    let atoms: SmallVec<_, 0, Global> = level.atoms().collect();
    out.put_uvarint(WireU64::from(WireUsize::from(atoms.len())));
    for (variable, offset) in atoms {
        out.put_uvarint(WireU64::from(u64::from(u32::from(variable.index()))));
        out.put_uvarint(WireU64::from(u64::from(offset)));
    }
}

/// Write a cover derivation: its step count, then each step in mint order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: writes the step count, then per step its tag and payload as
///   [`tags::KIND_DEF_COVERED`] states them.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a covered definition's derivations round-trip through the
///   wire unchanged.
/// - witness: `encode::tests::a_covered_definition_closes_its_segment_with_its_derivations`
#[spec(captures: entry = out.as_image().as_ref().len(), ensures: out.as_image().as_ref().len() > entry)]
fn encode_cover(
    out: &mut EncodedArtifact,
    cover: &crate::cover::Cover,
    positions: &mut Positions,
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(cover.steps().count())));
    for (_id, step) in cover.steps() {
        match *step {
            crate::cover::Step::Var(arm) => {
                out.put_tag(tags::COVER_VAR);
                out.put_uvarint(WireU64::from(WireUsize::from(arm)));
            },
            crate::cover::Step::Compose(inner) => {
                out.put_tag(tags::COVER_COMPOSE);
                out.put_uvarint(WireU64::from(u64::from(u32::from(inner))));
            },
            crate::cover::Step::Split {
                ref cases,
                ref branches,
            } => {
                out.put_tag(tags::COVER_SPLIT);
                encode_cases(out, cases, positions);
                out.put_uvarint(WireU64::from(WireUsize::from(branches.len())));
                for &branch in branches {
                    out.put_uvarint(WireU64::from(u64::from(u32::from(branch))));
                }
            },
        }
    }
}

/// Write one split's cases: their tag, then their payload.
///
/// # Specification
/// - requires: nothing.
/// - ensures: writes the cases' tag and payload as [`tags::KIND_DEF_COVERED`]
///   states them.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`encode_cover`].
/// - witness: `encode::tests::a_covered_definition_closes_its_segment_with_its_derivations`
#[spec(captures: entry = out.as_image().as_ref().len(), ensures: out.as_image().as_ref().len() > entry)]
fn encode_cases(
    out: &mut EncodedArtifact,
    cases: &crate::cover::Cases,
    positions: &mut Positions,
)
{
    use crate::cover::Cases;
    match *cases {
        Cases::Data {
            family,
            ref constructors,
            ref loops,
        } => {
            out.put_tag(tags::COVER_DATA);
            let written = positions.rename(family);
            out.put_uvarint(WireU64::from(WireUsize::from(usize::from(written))));
            out.put_uvarint(WireU64::from(WireUsize::from(constructors.len())));
            for &(tag, fields) in constructors {
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(tag))));
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(fields))));
            }
            out.put_uvarint(WireU64::from(WireUsize::from(loops.len())));
            for owed in loops {
                let words = positions.rename(owed.words());
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(words))));
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(owed.cell()))));
            }
        },
        Cases::Boolean => out.put_tag(tags::COVER_BOOLEAN),
        Cases::Integer(ref literal) => {
            out.put_tag(tags::COVER_INTEGER);
            encode_literal(out, literal);
        },
        Cases::Tuple(width) => {
            out.put_tag(tags::COVER_TUPLE);
            out.put_uvarint(WireU64::from(WireUsize::from(width)));
        },
        Cases::Record(width) => {
            out.put_tag(tags::COVER_RECORD);
            out.put_uvarint(WireU64::from(WireUsize::from(width)));
        },
        Cases::Sum(width) => {
            out.put_tag(tags::COVER_SUM);
            out.put_uvarint(WireU64::from(WireUsize::from(width)));
        },
        Cases::List => out.put_tag(tags::COVER_LIST),
        Cases::Guard => out.put_tag(tags::COVER_GUARD),
        Cases::Absurd => out.put_tag(tags::COVER_ABSURD),
    }
}

/// Write a literal: its kind, then its canonical payload.
///
/// # Specification
/// - requires: `literal` is canonical, which its constructors are the only way
///   to obtain.
/// - ensures: appends the kind tag, then the payload each kind owes — a sign
///   tag and digits for an integer, text for a string, a sign tag with integral
///   and fractional digits for a numeric, the scalar's UTF-8 text for a
///   character, and the bit pattern as an unsigned varint for a floating-point
///   or a width literal.
/// - provides: the literal's byte image; since the payload is canonical, two
///   literals agree on bytes exactly when they denote the same value.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares complete appended bytes, including a nonempty
///   prefix, with literal wire fixtures. Text covers NUL, multibyte UTF-8 and
///   the 127/128 and 16383/16384 length boundaries; literals cover every kind
///   and sign plus canonical zero. Levels cover empty, constant, ordered
///   multi-atom and u64-ceiling forms, and signatures distinguish both
///   relations and parameter widths. These separate byte-versus-character
///   lengths, field permutation, prefix damage and lost high bits. Arbitrary
///   payload sizes and allocation failure are outside the fixture domain.
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        match *literal { Literal::Integer(ref integer) => bytes.get(start).copied() == Some(u8::from(tags::LITERAL_INTEGER))
            && bytes.get(start.saturating_add(1)).copied() == Some(u8::from(sign_tag(integer.sign())))
            && bytes.len() == start.saturating_add(2).saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from((integer.magnitude().as_ref()).len()).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX).saturating_add((integer.magnitude().as_ref()).len()))
            && bytes.ends_with(integer.magnitude().as_ref().as_bytes()), Literal::Text(ref text) => bytes.get(start).copied() == Some(u8::from(tags::LITERAL_TEXT))
            && bytes.len() == start.saturating_add(1).saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from((text.as_ref()).len()).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX).saturating_add((text.as_ref()).len()))
            && bytes.ends_with(text.as_ref().as_bytes()), Literal::Numeric(ref numeric) => bytes.get(start).copied() == Some(u8::from(tags::LITERAL_NUMERIC))
            && bytes.get(start.saturating_add(1)).copied() == Some(u8::from(sign_tag(numeric.sign())))
            && bytes.len() == start.saturating_add(2).saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from((numeric.integer_part().as_ref()).len()).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX).saturating_add((numeric.integer_part().as_ref()).len())).saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from((numeric.fraction().as_ref()).len()).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX).saturating_add((numeric.fraction().as_ref()).len()))
            && bytes.ends_with(numeric.fraction().as_ref().as_bytes()), Literal::Character(ref character) => { let text = character.to_text();
        bytes.get(start).copied() == Some(u8::from(tags::LITERAL_CHARACTER))
            && bytes.get(start.saturating_add(1)).copied().map(usize::from) == Some(text.len())
            && bytes.len() == start.saturating_add(2).saturating_add(text.len())
            && bytes.ends_with(text.as_bytes()) }, Literal::Float64(float) => bytes.get(start).copied() == Some(u8::from(tags::LITERAL_FLOAT64))
            && bytes.len() == start.saturating_add(1).saturating_add(usize::try_from(64_u32.saturating_sub(u64::from(float).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)), Literal::Fixed(fixed) => { let bits = u64::from(fixed);
        bytes.get(start).copied() == Some(u8::from(fixed_literal_tag(fixed.width())))
            && bytes.len() == start.saturating_add(1).saturating_add(usize::try_from(64_u32.saturating_sub(bits.leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)) } } },
)]
fn encode_literal(
    out: &mut EncodedArtifact,
    literal: &Literal,
)
{
    match *literal {
        Literal::Integer(ref integer) => {
            out.put_tag(tags::LITERAL_INTEGER);
            out.put_tag(sign_tag(integer.sign()));
            let digits = integer.magnitude().to_digits();
            encode_text(out, ArtifactText::from(digits.as_str()));
        },
        Literal::Text(ref text) => {
            out.put_tag(tags::LITERAL_TEXT);
            let content = text.to_content();
            encode_text(out, ArtifactText::from(content.as_str()));
        },
        Literal::Numeric(ref numeric) => {
            out.put_tag(tags::LITERAL_NUMERIC);
            out.put_tag(sign_tag(numeric.sign()));
            let integer = numeric.integer_part().to_digits();
            encode_text(out, ArtifactText::from(integer.as_str()));
            let fraction = numeric.fraction().to_digits();
            encode_text(out, ArtifactText::from(fraction.as_str()));
        },
        Literal::Character(ref character) => {
            out.put_tag(tags::LITERAL_CHARACTER);
            let content = character.to_text();
            encode_text(out, ArtifactText::from(content.as_str()));
        },
        Literal::Float64(float) => {
            out.put_tag(tags::LITERAL_FLOAT64);
            out.put_uvarint(WireU64::from(u64::from(float)));
        },
        Literal::Fixed(fixed) => {
            out.put_tag(fixed_literal_tag(fixed.width()));
            out.put_uvarint(WireU64::from(u64::from(fixed)));
        },
    }
}

/// Write length-prefixed UTF-8 text.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends the byte length of the UTF-8 encoding and then those
///   bytes verbatim.
/// - provides: the framing every text field shares, so a payload carrying no
///   normalization of its own is still unambiguously delimited.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares complete appended bytes, including a nonempty
///   prefix, with literal wire fixtures. Text covers NUL, multibyte UTF-8 and
///   the 127/128 and 16383/16384 length boundaries; literals cover every kind
///   and sign plus canonical zero. Levels cover empty, constant, ordered
///   multi-atom and u64-ceiling forms, and signatures distinguish both
///   relations and parameter widths. These separate byte-versus-character
///   lengths, field permutation, prefix damage and lost high bits. Arbitrary
///   payload sizes and allocation failure are outside the fixture domain.
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        let length = u64::try_from(text.0.len()).unwrap_or(u64::MAX);
        bytes.len() == start.saturating_add(usize::try_from(64_u32.saturating_sub((length).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(text.0.len())
            && bytes.ends_with(text.0.as_bytes())
            && { let scalar = length;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) } },
)]
fn encode_text(
    out: &mut EncodedArtifact,
    text: ArtifactText<'_>,
)
{
    let bytes = text.0.as_bytes();
    out.put_uvarint(WireU64::from(WireUsize::from(bytes.len())));
    out.put_image(ArtifactImage::from(bytes));
}

/// The wire tag of a base-type atom.
///
/// # Specification
/// - requires: nothing.
/// - ensures: maps each base-type atom to its frozen tag, a width atom to its
///   width's.
/// - provides: the total atom-to-tag map, so a base type's byte is decided in
///   one place rather than at each write site.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 observes literal entry bytes for every frozen former, every
///   base atom, both injection sides, nonzero inline levels and distinguishable
///   one-, two- and three-child index sequences crossing varint boundaries.
///   This separates tag reassignment, child permutation, missing payloads and
///   lost high bits. It covers live nodes and supplied global assignments, not
///   formation or inputs outside the live, acyclic graph domain. L3 compares
///   complete appended bytes, including a nonempty prefix, with literal wire
///   fixtures. Text covers NUL, multibyte UTF-8 and the 127/128 and 16383/16384
///   length boundaries; literals cover every kind and sign plus canonical zero.
///   Levels cover empty, constant, ordered multi-atom and u64-ceiling forms,
///   and signatures distinguish both relations and parameter widths. These
///   separate byte-versus-character lengths, field permutation, prefix damage
///   and lost high bits. Arbitrary payload sizes and allocation failure are
///   outside the fixture domain.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    ensures: |ret| ret == match base { BaseType::Integer => tags::BASE_INTEGER, BaseType::String => tags::BASE_STRING, BaseType::Numeric => tags::BASE_NUMERIC, BaseType::Character => tags::BASE_CHARACTER, BaseType::Float64 => tags::BASE_FLOAT64, BaseType::Fixed(IntegerWidth::U32) => tags::BASE_U32, BaseType::Fixed(IntegerWidth::U64) => tags::BASE_U64, BaseType::Fixed(IntegerWidth::I32) => tags::BASE_I32, BaseType::Fixed(IntegerWidth::I64) => tags::BASE_I64, BaseType::Fixed(IntegerWidth::U8) => tags::BASE_U8, BaseType::Fixed(IntegerWidth::U16) => tags::BASE_U16, BaseType::Fixed(IntegerWidth::I8) => tags::BASE_I8, BaseType::Fixed(IntegerWidth::I16) => tags::BASE_I16, BaseType::Fixed(IntegerWidth::Usize) => tags::BASE_USIZE, BaseType::Fixed(IntegerWidth::Isize) => tags::BASE_ISIZE },
)]
#[inline]
fn base_type_tag(base: BaseType) -> WireTag
{
    match base {
        BaseType::Integer => tags::BASE_INTEGER,
        BaseType::String => tags::BASE_STRING,
        BaseType::Numeric => tags::BASE_NUMERIC,
        BaseType::Character => tags::BASE_CHARACTER,
        BaseType::Float64 => tags::BASE_FLOAT64,
        BaseType::Fixed(IntegerWidth::U32) => tags::BASE_U32,
        BaseType::Fixed(IntegerWidth::U64) => tags::BASE_U64,
        BaseType::Fixed(IntegerWidth::I32) => tags::BASE_I32,
        BaseType::Fixed(IntegerWidth::I64) => tags::BASE_I64,
        BaseType::Fixed(IntegerWidth::U8) => tags::BASE_U8,
        BaseType::Fixed(IntegerWidth::U16) => tags::BASE_U16,
        BaseType::Fixed(IntegerWidth::I8) => tags::BASE_I8,
        BaseType::Fixed(IntegerWidth::I16) => tags::BASE_I16,
        BaseType::Fixed(IntegerWidth::Usize) => tags::BASE_USIZE,
        BaseType::Fixed(IntegerWidth::Isize) => tags::BASE_ISIZE,
    }
}

/// The literal-kind tag of a width literal.
///
/// # Specification
/// - requires: nothing.
/// - ensures: maps each width to its frozen literal kind.
/// - provides: the one width-to-kind map the literal writer reads.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a literal of each width encodes to its fixture bytes, so
///   a swapped kind changes a fixture.
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
#[spec(
    ensures: |ret| ret == match width { IntegerWidth::U32 => tags::LITERAL_U32, IntegerWidth::U64 => tags::LITERAL_U64, IntegerWidth::I32 => tags::LITERAL_I32, IntegerWidth::I64 => tags::LITERAL_I64, IntegerWidth::U8 => tags::LITERAL_U8, IntegerWidth::U16 => tags::LITERAL_U16, IntegerWidth::I8 => tags::LITERAL_I8, IntegerWidth::I16 => tags::LITERAL_I16, IntegerWidth::Usize => tags::LITERAL_USIZE, IntegerWidth::Isize => tags::LITERAL_ISIZE },
)]
#[inline]
fn fixed_literal_tag(width: IntegerWidth) -> WireTag
{
    match width {
        IntegerWidth::U32 => tags::LITERAL_U32,
        IntegerWidth::U64 => tags::LITERAL_U64,
        IntegerWidth::I32 => tags::LITERAL_I32,
        IntegerWidth::I64 => tags::LITERAL_I64,
        IntegerWidth::U8 => tags::LITERAL_U8,
        IntegerWidth::U16 => tags::LITERAL_U16,
        IntegerWidth::I8 => tags::LITERAL_I8,
        IntegerWidth::I16 => tags::LITERAL_I16,
        IntegerWidth::Usize => tags::LITERAL_USIZE,
        IntegerWidth::Isize => tags::LITERAL_ISIZE,
    }
}

/// The wire tag of a literal sign.
///
/// # Specification
/// - requires: nothing.
/// - ensures: maps each sign to its frozen tag.
/// - provides: the total sign-to-tag map, so a sign's byte is decided in one
///   place rather than at each write site.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 observes literal entry bytes for every frozen former, every
///   base atom, both injection sides, nonzero inline levels and distinguishable
///   one-, two- and three-child index sequences crossing varint boundaries.
///   This separates tag reassignment, child permutation, missing payloads and
///   lost high bits. It covers live nodes and supplied global assignments, not
///   formation or inputs outside the live, acyclic graph domain. L3 compares
///   complete appended bytes, including a nonempty prefix, with literal wire
///   fixtures. Text covers NUL, multibyte UTF-8 and the 127/128 and 16383/16384
///   length boundaries; literals cover every kind and sign plus canonical zero.
///   Levels cover empty, constant, ordered multi-atom and u64-ceiling forms,
///   and signatures distinguish both relations and parameter widths. These
///   separate byte-versus-character lengths, field permutation, prefix damage
///   and lost high bits. Arbitrary payload sizes and allocation failure are
///   outside the fixture domain.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    ensures: |ret| ret == match sign { Sign::NonNegative => tags::SIGN_NON_NEGATIVE, Sign::Negative => tags::SIGN_NEGATIVE },
)]
#[inline]
fn sign_tag(sign: Sign) -> WireTag
{
    match sign {
        Sign::NonNegative => tags::SIGN_NON_NEGATIVE,
        Sign::Negative => tags::SIGN_NEGATIVE,
    }
}

/// The wire tag of a fixpoint's termination claim.
///
/// # Specification
/// - requires: nothing.
/// - ensures: maps each claim to its frozen tag; a staged claim's position
///   follows the tag at the write site.
/// - provides: the total claim-to-tag map, so a claim's byte is decided in one
///   place rather than at each write site.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 observes the literal entry bytes of a fixpoint under each
///   claim; a swapped or dropped claim byte changes the golden.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
#[spec(
    ensures: |ret| ret == match evidence {
        crate::FixpointEvidence::Partial => tags::FIXPOINT_PARTIAL,
        crate::FixpointEvidence::StructuralDescent => tags::FIXPOINT_STRUCTURAL_DESCENT,
        crate::FixpointEvidence::Staged { .. } => tags::FIXPOINT_STAGED,
        crate::FixpointEvidence::Joint { .. } => tags::FIXPOINT_JOINT,
        crate::FixpointEvidence::Guarded => tags::FIXPOINT_GUARDED,
    },
)]
#[inline]
fn evidence_tag(evidence: crate::FixpointEvidence) -> WireTag
{
    match evidence {
        crate::FixpointEvidence::Partial => tags::FIXPOINT_PARTIAL,
        crate::FixpointEvidence::StructuralDescent => tags::FIXPOINT_STRUCTURAL_DESCENT,
        crate::FixpointEvidence::Staged { .. } => tags::FIXPOINT_STAGED,
        crate::FixpointEvidence::Joint { .. } => tags::FIXPOINT_JOINT,
        crate::FixpointEvidence::Guarded => tags::FIXPOINT_GUARDED,
    }
}

/// The wire tag of a composition's seam.
///
/// # Specification
/// - requires: nothing.
/// - ensures: maps each seam to its frozen tag.
/// - provides: the total seam-to-tag map, so a seam's byte is decided in one
///   place rather than at each write site.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 observes the literal entry bytes of a composition under
///   each seam; a swapped or dropped seam byte changes the golden.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
#[spec(
    ensures: |ret| ret == match seam {
        crate::Seam::Sequence => tags::SEAM_SEQUENCE,
        crate::Seam::Feedback => tags::SEAM_FEEDBACK,
    },
)]
#[inline]
fn seam_tag(seam: crate::Seam) -> WireTag
{
    match seam {
        crate::Seam::Sequence => tags::SEAM_SEQUENCE,
        crate::Seam::Feedback => tags::SEAM_FEEDBACK,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::alloc::Global;
    use alloc::string::String;

    use gandr_kernel_data::SmallVec;
    use gandr_kernel_data::ThinShared;
    use quenchant_shape::shape::Maybe;

    use super::AnyNode;
    use super::ArtifactImage;
    use super::ArtifactText;
    use super::EncodedArtifact;
    use super::GlobalIndex;
    use super::Level;
    use super::TermArena;
    use crate::base::BaseType;
    use crate::base::FractionDigits;
    use crate::base::IntegerLiteral;
    use crate::base::Literal;
    use crate::base::Magnitude;
    use crate::base::NumericLiteral;
    use crate::base::Sign;
    use crate::base::StringLiteral;
    use crate::decl::AdmissionMark;
    use crate::decl::Declaration;
    use crate::decl::DeclarationBuilder;
    use crate::decl::LevelParamCount;
    use crate::decl::LevelSignature;
    use crate::decl::MarkedDeclaration;
    use crate::decl::NameSegment;
    use crate::decl::StructuredName;
    use crate::term::ConstantIndex;
    use crate::term::DeBruijnIndex;
    use crate::term::Summand;
    use crate::types::GroundSort;

    #[cfg(anodized_panic)]
    #[test]
    fn stale_roots_violate_the_encoding_domain()
    {
        extern crate std;

        let mut arena = TermArena::new();
        let empty = arena.watermark();
        let declared = arena.value_type_unit();
        let value = arena.value_unit();
        let negative_type = arena.comp_type_returner(declared);
        let computation = arena.computation_return(value);
        let declaration =
            DeclarationBuilder::new(&mut arena).def(LevelSignature::monomorphic(), declared, value);
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, declaration)];
        arena.truncate_to(empty);
        for node in [
            AnyNode::ValueType(declared),
            AnyNode::Value(value),
            AnyNode::CompType(negative_type),
            AnyNode::Computation(computation),
        ] {
            assert!(
                std::panic::catch_unwind(|| super::encode_entry(
                    &arena,
                    node,
                    &[],
                    &mut super::Positions::default()
                ))
                .is_err()
            );
        }
        assert!(std::panic::catch_unwind(|| super::encode(&arena, &declarations)).is_err());
    }

    #[test]
    fn text_and_literals_match_literal_wire_fixtures()
    {
        let cases: &[(String, &[u8])] = &[
            (String::new(), &[0]),
            (String::from("A\0é"), &[4]),
            ("x".repeat(127), &[0x7f]),
            ("x".repeat(128), &[0x80, 1]),
            ("x".repeat(0x3fff), &[0xff, 0x7f]),
            ("x".repeat(0x4000), &[0x80, 0x80, 1]),
        ];
        let mut expected: SmallVec<u8, 0, Global> = SmallVec::<_, 0, Global>::new();
        for &(ref text, length) in cases {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_text(&mut out, ArtifactText::from(text.as_str()));
            expected.clear();
            expected.extend_from_slice(&[0xde, 0xad]);
            expected.extend_from_slice(length);
            expected.extend_from_slice(text.as_bytes());
            assert_eq!(out.as_image().as_ref(), expected.as_slice());
        }
        let cases: &[(Literal, &[u8])] = &[
            (
                Literal::Integer(IntegerLiteral::new(Sign::Negative, Magnitude::zero())),
                &[0, 0, 1, b'0'],
            ),
            (
                Literal::Integer(IntegerLiteral::new(
                    Sign::NonNegative,
                    Magnitude::from_decimal_text(String::from("00123")).expect("digits"),
                )),
                &[0, 0, 3, b'1', b'2', b'3'],
            ),
            (
                Literal::Integer(IntegerLiteral::new(
                    Sign::Negative,
                    Magnitude::from_decimal_text(String::from("00123")).expect("digits"),
                )),
                &[0, 1, 3, b'1', b'2', b'3'],
            ),
            (Literal::Text(StringLiteral::new(String::from("A\0é"))), &[
                1, 4, b'A', 0, 0xc3, 0xa9,
            ]),
            (
                Literal::Numeric(NumericLiteral::new(
                    Sign::Negative,
                    Magnitude::from_decimal_text(String::from("0012")).expect("digits"),
                    FractionDigits::from_decimal_text(String::from("0300")).expect("fraction"),
                )),
                &[2, 1, 2, b'1', b'2', 2, b'0', b'3'],
            ),
            (
                Literal::Numeric(NumericLiteral::new(
                    Sign::Negative,
                    Magnitude::zero(),
                    FractionDigits::none(),
                )),
                &[2, 0, 1, b'0', 0],
            ),
            (
                Literal::Character(crate::base::CharacterLiteral::from('a')),
                &[3, 1, b'a'],
            ),
            (
                Literal::Character(crate::base::CharacterLiteral::from('𐐀')),
                &[3, 4, 0xf0, 0x90, 0x90, 0x80],
            ),
            (Literal::Fixed(crate::base::FixedInteger::U32(300)), &[
                4, 0xac, 0x02,
            ]),
            (Literal::Fixed(crate::base::FixedInteger::U64(0)), &[5, 0]),
            (Literal::Fixed(crate::base::FixedInteger::I32(-1)), &[
                6, 0xff, 0xff, 0xff, 0xff, 0x0f,
            ]),
            (Literal::Fixed(crate::base::FixedInteger::I64(-1)), &[
                7, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01,
            ]),
        ];
        let mut expected: SmallVec<u8, 0, Global> = SmallVec::<_, 0, Global>::new();
        for &(ref literal, bytes) in cases {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_literal(&mut out, literal);
            expected.clear();
            expected.extend_from_slice(&[0xde, 0xad]);
            expected.extend_from_slice(bytes);
            assert_eq!(out.as_image().as_ref(), expected.as_slice());
        }
    }

    #[test]
    fn levels_and_interfaces_match_literal_wire_fixtures()
    {
        let x = Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(0_u32),
        ));
        let y = Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(1_u32),
        ));
        let second = Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(2_u32),
        ))
        .succ()
        .expect("small offset");
        let later = Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(129_u32),
        ));
        let mixed = Level::constant(gandr_kernel_strata::LevelConstant::from(7_u64))
            .max(&later)
            .max(&second);
        let levels: &[(Level, &[u8])] = &[
            (Level::zero(), &[0, 0]),
            (
                Level::constant(gandr_kernel_strata::LevelConstant::from(128_u64)),
                &[0x80, 1, 0],
            ),
            (
                Level::constant(gandr_kernel_strata::LevelConstant::from(u64::MAX)),
                &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 1, 0],
            ),
            (x.clone(), &[0, 1, 0, 0]),
            (mixed, &[7, 2, 2, 1, 0x81, 1, 0]),
        ];
        let mut expected: SmallVec<u8, 0, Global> = SmallVec::<_, 0, Global>::new();
        for &(ref level, bytes) in levels {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_level(&mut out, level);
            expected.clear();
            expected.extend_from_slice(&[0xde, 0xad]);
            expected.extend_from_slice(bytes);
            assert_eq!(out.as_image().as_ref(), expected.as_slice());
        }
        let signature = LevelSignature::new(
            LevelParamCount::from(2_u32),
            SmallVec::<_, 0, Global>::from_iter([
                gandr_kernel_strata::LandmarkConstraint::leq(x.clone(), y.clone())
                    .expect("variable-only sides"),
                gandr_kernel_strata::LandmarkConstraint::equal(y, x).expect("variable-only sides"),
            ]),
        );
        let signatures: &[(LevelSignature, &[u8])] = &[
            (LevelSignature::monomorphic(), &[0, 0]),
            (
                LevelSignature::new(
                    LevelParamCount::from(u32::MAX),
                    SmallVec::<_, 0, Global>::new(),
                ),
                &[0xff, 0xff, 0xff, 0xff, 0x0f, 0],
            ),
            (signature, &[
                2, 2, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0,
            ]),
        ];
        let mut expected: SmallVec<u8, 0, Global> = SmallVec::<_, 0, Global>::new();
        for &(ref signature, bytes) in signatures {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_level_signature(&mut out, signature);
            expected.clear();
            expected.extend_from_slice(&[0xde, 0xad]);
            expected.extend_from_slice(bytes);
            assert_eq!(out.as_image().as_ref(), expected.as_slice());
        }
    }

    #[test]
    fn entry_goldens_pin_every_former_and_child_position()
    {
        let mut arena = TermArena::new();
        let t0 = arena.value_type_unit();
        let t1 = arena.value_type_base(BaseType::Integer);
        let v0 = arena.value_variable(DeBruijnIndex::from(0_u32));
        let v1 = arena.value_variable(DeBruijnIndex::from(1_u32));
        let c0 = arena.computation_return(v0);
        let c1 = arena.computation_return(v1);
        let k0 = arena.comp_type_returner(t0);
        let k1 = arena.comp_type_returner(t1);
        let level = Level::constant(gandr_kernel_strata::LevelConstant::from(7_u64));
        let first = GlobalIndex::from(3_u32);
        let second = GlobalIndex::from(129_u32);
        let third = GlobalIndex::from(0x4000_u32);
        let cases: &[(AnyNode, &[GlobalIndex], &[u8])] = &[
            (
                AnyNode::ValueType(arena.value_type_base(BaseType::Integer)),
                &[],
                &[0x00, 0],
            ),
            (
                AnyNode::ValueType(arena.value_type_base(BaseType::String)),
                &[],
                &[0x00, 1],
            ),
            (
                AnyNode::ValueType(arena.value_type_base(BaseType::Numeric)),
                &[],
                &[0x00, 2],
            ),
            (AnyNode::ValueType(arena.value_type_unit()), &[], &[0x03, 0]),
            (AnyNode::ValueType(arena.value_type_empty()), &[], &[
                0x04, 0,
            ]),
            (
                AnyNode::ValueType(arena.value_type_universe(GroundSort::Value, level.clone())),
                &[],
                &[0x02, 7, 0],
            ),
            (
                AnyNode::ValueType(arena.value_type_product(&[t0, t1])),
                &[first, second],
                &[0x03, 2, 3, 0x81, 1],
            ),
            (
                AnyNode::ValueType(arena.value_type_sum(&[t0, t1, t0])),
                &[first, second, third],
                &[0x04, 3, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (AnyNode::ValueType(arena.value_type_thunk(k0)), &[first], &[
                0x05, 3,
            ]),
            (
                AnyNode::ValueType(arena.value_type_lift(t0, level.clone())),
                &[first],
                &[0x06, 7, 0, 3],
            ),
            (
                AnyNode::CompType(arena.comp_type_returner(t0)),
                &[first],
                &[0x07, 3],
            ),
            (
                AnyNode::CompType(arena.comp_type_arrow(t0, k1)),
                &[first, second],
                &[0x08, 3, 0x81, 1],
            ),
            (
                AnyNode::Value(arena.value_variable(DeBruijnIndex::from(0x4000_u32))),
                &[],
                &[0x09, 0x80, 0x80, 1],
            ),
            // A position is written bare, as one more than twice itself.
            (
                AnyNode::Value(arena.value_constant(ConstantIndex::from(129_usize))),
                &[],
                &[0x0a, 0x83, 2],
            ),
            (AnyNode::Value(arena.value_unit()), &[], &[0x0d, 0]),
            (
                AnyNode::Value(
                    arena.value_literal(Literal::Text(StringLiteral::new(String::from("é")))),
                ),
                &[],
                &[0x0c, 1, 2, 0xc3, 0xa9],
            ),
            (
                AnyNode::Value(arena.value_tuple(&[v0, v1])),
                &[first, second],
                &[0x0d, 2, 3, 0x81, 1],
            ),
            (
                AnyNode::Value(arena.value_injection(Summand::from(0_usize), v0)),
                &[first],
                &[0x0e, 0, 3],
            ),
            (
                AnyNode::Value(arena.value_injection(Summand::from(129_usize), v0)),
                &[first],
                &[0x0e, 0x81, 1, 3],
            ),
            (AnyNode::Value(arena.value_thunk(c0)), &[first], &[0x0f, 3]),
            (
                AnyNode::Value(arena.value_lift(level.clone(), v0)),
                &[first],
                &[0x10, 7, 0, 3],
            ),
            (
                AnyNode::Computation(arena.computation_lambda(c0)),
                &[first],
                &[0x11, 3],
            ),
            (
                AnyNode::Computation(
                    arena.computation_fixpoint(c0, crate::FixpointEvidence::Partial),
                ),
                &[first],
                &[0x63, 0, 3],
            ),
            (
                AnyNode::Computation(
                    arena.computation_fixpoint(c0, crate::FixpointEvidence::StructuralDescent),
                ),
                &[first],
                &[0x63, 1, 3],
            ),
            (
                AnyNode::Computation(arena.computation_fixpoint(
                    c0,
                    crate::FixpointEvidence::Staged {
                        position: crate::StagedPosition::from(129_usize),
                    },
                )),
                &[first],
                &[0x63, 2, 0x81, 1, 3],
            ),
            (
                AnyNode::Computation(
                    arena.computation_fixpoint(c0, crate::FixpointEvidence::Guarded),
                ),
                &[first],
                &[0x63, 4, 3],
            ),
            (
                AnyNode::Computation(arena.computation_application(c0, v0)),
                &[first, second],
                &[0x12, 3, 0x81, 1],
            ),
            (
                AnyNode::Computation(arena.computation_return(v0)),
                &[first],
                &[0x13, 3],
            ),
            (
                AnyNode::Computation(arena.computation_bind(c0, c1)),
                &[first, second],
                &[0x14, 3, 0x81, 1],
            ),
            (
                AnyNode::Computation(arena.computation_force(v0)),
                &[first],
                &[0x15, 3],
            ),
            (
                AnyNode::Computation(arena.computation_case(v0, &[c0, c1])),
                &[first, second, third],
                &[0x16, 2, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (
                AnyNode::Computation(arena.computation_case(v0, &[])),
                &[first],
                &[0x16, 0, 3],
            ),
            (
                AnyNode::ValueType(arena.value_type_abstract(ConstantIndex::from(129_usize))),
                &[],
                &[0x17, 0x83, 2],
            ),
            (
                AnyNode::CompType(arena.comp_type_pi(t0, k1)),
                &[first, second],
                &[0x18, 3, 0x81, 1],
            ),
            (
                AnyNode::ValueType(arena.value_type_element(v0, level.clone())),
                &[first],
                &[0x19, 7, 0, 3],
            ),
            (
                AnyNode::ValueType(
                    arena.value_type_universe(GroundSort::Computation, level.clone()),
                ),
                &[],
                &[0x1a, 7, 0],
            ),
            (
                AnyNode::CompType(arena.comp_type_element(v0, level)),
                &[first],
                &[0x1b, 7, 0, 3],
            ),
            (AnyNode::Value(arena.value_quote(t0)), &[first], &[0x1c, 3]),
            (
                AnyNode::Value(arena.value_quote_computation(k0)),
                &[first],
                &[0x1d, 3],
            ),
            (
                AnyNode::ValueType(arena.value_type_static_pi(t0, t1)),
                &[first, second],
                &[0x1e, 3, 0x81, 1],
            ),
            (
                AnyNode::Value(arena.value_static_application(v0, v1)),
                &[first, second],
                &[0x1f, 3, 0x81, 1],
            ),
            (
                AnyNode::CompType(arena.comp_type_with(&[k0, k1])),
                &[first, second],
                &[0x65, 2, 3, 0x81, 1],
            ),
            (
                AnyNode::Computation(arena.computation_with(&[c0, c1])),
                &[first, second],
                &[0x66, 2, 3, 0x81, 1],
            ),
            (
                AnyNode::Computation(
                    arena.computation_project(crate::Component::from(0_usize), c0),
                ),
                &[second],
                &[0x67, 0, 0x81, 1],
            ),
            (
                AnyNode::Computation(
                    arena.computation_project(crate::Component::from(1_usize), c0),
                ),
                &[second],
                &[0x67, 1, 0x81, 1],
            ),
            (
                AnyNode::ValueType(arena.value_type_flow(t0, v0, v1)),
                &[first, second, third],
                &[0x4A, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (AnyNode::Value(arena.value_stay(v0)), &[first], &[
                0x4B, 0, 0, 3,
            ]),
            (
                AnyNode::Value(arena.value_forward_flow(
                    t0,
                    v0,
                    [v1].into(),
                    ThinShared::from_header_and_iter((), [SmallVec::<_, 0, Global>::new()]),
                )),
                &[first, second, third],
                &[0x4C, 1, 0, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (
                AnyNode::Value(arena.value_function_flow(t0, v0, v1)),
                &[first, second, third],
                &[0x4D, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (
                AnyNode::Value(arena.value_then(v0, v1, crate::Seam::Sequence)),
                &[first, second],
                &[0x4E, 0, 3, 0x81, 1],
            ),
            (
                AnyNode::Value(arena.value_then(v0, v1, crate::Seam::Feedback)),
                &[first, second],
                &[0x4E, 1, 3, 0x81, 1],
            ),
            (
                AnyNode::Computation(arena.computation_ride(t0, v0, v1)),
                &[first, second, third],
                &[0x4F, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (
                AnyNode::Computation(arena.computation_telescope_ride(k0, v0, v1, v0, v1)),
                &[first, second, third, first, second],
                &[0x68, 3, 0x81, 1, 0x80, 0x80, 1, 3, 0x81, 1],
            ),
        ];
        let mut words: SmallVec<super::WireU64, 0, Global> = SmallVec::<_, 0, Global>::new();
        for &(node, children, expected) in cases {
            words.clear();
            words.extend(
                children
                    .iter()
                    .map(|&child| super::WireU64::from(u64::from(u32::from(child)))),
            );
            assert_eq!(
                super::encode_entry(&arena, node, &words, &mut super::Positions::default())
                    .0
                    .as_image()
                    .as_ref(),
                expected,
                "{node:?}"
            );
        }
    }

    #[test]
    fn interning_reuses_content_across_segments_without_losing_order()
    {
        let mut arena = TermArena::new();
        let first_unit = arena.value_unit();
        let second_unit = arena.value_unit();
        let variable = arena.value_variable(DeBruijnIndex::from(0x4000_u32));
        let first_pair = arena.value_tuple(&[first_unit, variable]);
        let equal_pair = arena.value_tuple(&[second_unit, variable]);
        let reversed = arena.value_tuple(&[variable, first_unit]);
        let mut interner = super::Interner::new();
        interner.open_segment();
        let mut first_segment = SmallVec::<_, 0, Global>::new();
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut first_segment,
                AnyNode::Value(first_unit)
            ),
            GlobalIndex::from(0_u32)
        );
        let prefix = first_segment.clone();
        let first_memo = interner.by_node.clone();
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut first_segment,
                AnyNode::Value(first_unit)
            ),
            GlobalIndex::from(0_u32)
        );
        assert_eq!(interner.by_node, first_memo);
        assert_eq!(first_segment, prefix);
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut first_segment,
                AnyNode::Value(second_unit)
            ),
            GlobalIndex::from(0_u32)
        );
        assert_eq!(first_segment, prefix);
        assert_eq!(
            interner.by_node.get(&AnyNode::Value(second_unit)),
            Some(&GlobalIndex::from(0_u32))
        );
        // The second segment starts at global one. Its own entries take even
        // references from there, and the unit of the first segment is its
        // import zero, written as 2 * 0 + 1.
        interner.open_segment();
        let mut second_segment = SmallVec::<_, 0, Global>::new();
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut second_segment,
                AnyNode::Value(first_pair)
            ),
            GlobalIndex::from(2_u32)
        );
        let expected: &[&[u8]] = &[&[0x09, 0x80, 0x80, 1], &[0x0d, 2, 1, 0]];
        assert_eq!(second_segment.len(), expected.len());
        for (entry, &bytes) in second_segment.iter().zip(expected) {
            assert_eq!(entry.0.as_image().as_ref(), bytes);
        }
        let before_alias = second_segment.clone();
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut second_segment,
                AnyNode::Value(equal_pair)
            ),
            GlobalIndex::from(2_u32)
        );
        assert_eq!(second_segment, before_alias);
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut second_segment,
                AnyNode::Value(reversed)
            ),
            GlobalIndex::from(3_u32)
        );
        assert_eq!(
            second_segment
                .last()
                .expect("reversed entry")
                .0
                .as_image()
                .as_ref(),
            [0x0d, 2, 0, 1]
        );
        assert_eq!(interner.next, GlobalIndex::from(4_u32));
        assert_eq!(
            interner.frame.imports,
            [(0, 0)],
            "the segment imports the earlier unit once, from offset zero of place zero"
        );
        assert_eq!(interner.by_content.len(), 4);
        assert_eq!(interner.by_node.len(), 6);
        assert_eq!(first_segment, prefix);
    }

    #[test]
    fn a_staged_type_is_written_as_its_base()
    {
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(crate::BaseType::Integer);
        let staged =
            arena.value_type_staged(integer, crate::Stage::At(crate::StageId::from(0_usize)));
        let plain_list = arena.value_type_list(integer);
        let staged_list = arena.value_type_list(staged);
        let mut interner = super::Interner::new();
        let mut segment = SmallVec::<_, 0, Global>::new();
        let plain = super::intern(
            &arena,
            &mut interner,
            &mut segment,
            AnyNode::ValueType(plain_list),
        );
        let written = segment.clone();
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut segment,
                AnyNode::ValueType(staged_list)
            ),
            plain,
            "a list of a staged type is the list of its base on the wire"
        );
        assert_eq!(segment, written, "a stage writes no entry");
        assert_eq!(
            interner.by_node.get(&AnyNode::ValueType(staged)),
            interner.by_node.get(&AnyNode::ValueType(integer))
        );
    }

    #[test]
    fn declaration_sequences_match_literal_segment_fixtures()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let universe = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let atom = builder.abstract_type(
            LevelSignature::monomorphic(),
            universe,
            integer,
            super::SealScope::Open,
        );
        let mut builder = DeclarationBuilder::new(&mut arena);
        let abstract_type = builder
            .arena()
            .value_type_abstract(ConstantIndex::from(0_usize));
        let quote = builder.arena().value_quote(abstract_type);
        let definition = builder
            .def(LevelSignature::monomorphic(), universe, quote)
            .named(StructuredName::from(SmallVec::<_, 0, Global>::from_iter([
                NameSegment::from_text(String::from("a")).expect("segment"),
                NameSegment::from_text(String::from("é")).expect("segment"),
            ])));
        let axiom =
            DeclarationBuilder::new(&mut arena).axiom(LevelSignature::monomorphic(), abstract_type);
        let declarations = [
            MarkedDeclaration::new(AdmissionMark::Checked, atom),
            MarkedDeclaration::new(AdmissionMark::UncheckedBypass, definition),
            MarkedDeclaration::new(AdmissionMark::Checked, axiom),
        ];
        // The atom is open, so it is written closed after the two declarations
        // that follow it; its segment carries the universe and the integer
        // representation as entries, then its kind root, its representation
        // root and that extent. Each segment opens with an empty table of
        // names and its imports, and the definition reads the atom bare, as
        // 2 * 0 + 1. The definition imports the universe from offset zero of
        // place zero, and the axiom imports the abstract type from offset zero
        // of place one, each place written bare.
        let expected = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 1, 0, 1, 3, 0, 0, 0, 2, 0, 0, 0, 2, 0x02, 0, 0, 0x00,
            0x00, 0, 2, 2, 0, 1, 1, 0, 1, 0, 2, 1, b'a', 2, 0xc3, 0xa9, 0, 0, 2, 0x17, 1, 0x1c, 0,
            1, 2, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1, 0, 0, 0, 0, 1,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        assert_eq!(decoded.declarations().len(), 3);
        assert_eq!(
            decoded.declarations().get(1).expect("definition").mark(),
            AdmissionMark::UncheckedBypass
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected
        );
    }

    #[test]
    fn a_relating_definition_closes_its_segment_with_its_pairs()
    {
        use gandr_kernel_conversion_trace::ConversionDecision;
        use gandr_kernel_conversion_trace::ConversionSide;

        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let unit = builder.arena().value_unit();
        let wrapped = builder.arena().value_tuple(&[unit]);
        let related = SmallVec::<_, 0, Global>::from_iter([crate::decl::RelatedEndpoints {
            left: unit,
            right: wrapped,
            dialogue: SmallVec::<_, 0, Global>::from_iter([
                ConversionDecision::Decompose,
                ConversionDecision::ReturnEta {
                    side: ConversionSide::Right,
                },
            ]),
        }]);
        let definition = builder
            .def(LevelSignature::monomorphic(), unit_type, unit)
            .relating(related.clone());
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, definition)];
        // The relating kind, then the plain definition's fields: the unit type,
        // the unit and the wrapped unit as entries, the declared and body roots
        // and the four empty slots; then one pair, its two roots and its two
        // decision words.
        let expected = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 0, 1, 0, 0, 0, 7, 0, 0, 0, 3, 0x03, 0, 0x0D, 0, 0x0D,
            1, 2, 0, 2, 0, 0, 0, 0, 1, 2, 4, 2, 0x0B, 0x0E,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded.declarations().first().expect("one definition");
        assert_eq!(declaration.declaration().related().len(), 1);
        assert_eq!(
            declaration
                .declaration()
                .related()
                .first()
                .map(|pair| pair.dialogue.clone()),
            related.first().map(|pair| pair.dialogue.clone())
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected
        );
        // A relating kind closing with no pair decodes to a plain definition,
        // whose canonical bytes carry the plain kind.
        let empty = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 0, 1, 0, 0, 0, 7, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0, 2,
            0, 0, 0, 0, 0,
        ];
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(empty.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::NonCanonical,
            })
        );
        // A word outside the decision alphabet is refused as path evidence.
        let mut unknown = expected;
        if let Some(word) = unknown.last_mut() {
            *word = 0x7F;
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(unknown.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::PathEvidence,
            })
        );
        // The plain kind over the same bytes leaves the pair unread.
        let mut plain = expected;
        if let Some(kind) = plain.get_mut(12) {
            *kind = 0;
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(plain.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    #[test]
    fn a_lawful_definition_closes_its_segment_with_its_laws()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let unit = builder.arena().value_unit();
        let laws = SmallVec::<_, 0, Global>::from_iter([
            ConstantIndex::from(5_usize),
            ConstantIndex::from(2_usize),
        ]);
        let definition = builder
            .def(LevelSignature::monomorphic(), unit_type, unit)
            .lawful(laws.clone());
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, definition)];
        // The lawful kind, then the plain definition's fields: the unit type
        // and the unit as entries, the declared and body roots and the four
        // empty slots; then no related pair, and the two laws in written order,
        // each bare: 2 * 5 + 1 and 2 * 2 + 1.
        let expected = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 0, 1, 0, 0, 0, 9, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0, 2,
            0, 0, 0, 0, 0, 2, 11, 5,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded.declarations().first().expect("one definition");
        assert_eq!(declaration.declaration().laws(), laws.as_slice());
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected
        );
        // A lawful kind closing with no law decodes to a plain definition,
        // whose canonical bytes carry the plain kind.
        let empty = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 0, 1, 0, 0, 0, 9, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0, 2,
            0, 0, 0, 0, 0, 0,
        ];
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(empty.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::NonCanonical,
            })
        );
        // The relating kind over the same bytes reads the pair count and leaves
        // the laws unread.
        let mut relating = expected;
        if let Some(kind) = relating.get_mut(12) {
            *kind = 7;
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(relating.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    #[test]
    fn a_stage_signature_fills_the_erasure_slot()
    {
        use crate::stage_signature::PlacedChild;
        use crate::stage_signature::StageBinder;
        use crate::stage_signature::StageBound;
        use crate::stage_signature::StageMark;
        use crate::stage_signature::StageReach;
        use crate::stage_signature::StageSignature;
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let unit = builder.arena().value_unit();
        let stages = StageSignature::new(
            SmallVec::<_, 0, Global>::from_iter([
                StageBound::Unbounded,
                StageBound::Below(StageBinder::from(0_usize)),
            ]),
            SmallVec::<_, 0, Global>::from_iter([
                StageMark::new(
                    SmallVec::<_, 0, Global>::from_iter([
                        PlacedChild::from(0_usize),
                        PlacedChild::from(1_usize),
                    ]),
                    StageBinder::from(0_usize),
                    StageReach::Below(crate::term::StageDepth::ONE),
                ),
                StageMark::new(
                    SmallVec::<_, 0, Global>::from_iter([PlacedChild::from(1_usize)]),
                    StageBinder::from(1_usize),
                    StageReach::At,
                ),
            ]),
        );
        let definition = builder
            .def(LevelSignature::monomorphic(), unit_type, unit)
            .staged(stages.clone());
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, definition)];
        // The plain definition's fields up to its body root; then the erasure
        // slot: two binders, the second below the first, and two marks, each
        // its binder, its depth and its path; then the three other slots.
        let expected = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0, 2,
            2, 0, 1, 2, 0, 1, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded.declarations().first().expect("one definition");
        assert_eq!(declaration.declaration().stages(), &stages);
        // A signature binding nothing writes the empty slot.
        let plain =
            DeclarationBuilder::new(&mut arena).def(LevelSignature::monomorphic(), unit_type, unit);
        let plain = super::encode(&arena, &[MarkedDeclaration::new(
            AdmissionMark::Checked,
            plain,
        )]);
        assert_eq!(
            plain.as_image().as_ref().get(23 ..),
            Some(&[0_u8, 0, 0, 0][..])
        );
        // A bound naming no earlier binder, and a mark naming a binder the
        // signature does not bind, are refused at the slot.
        let malformed = Err(crate::error::DecodeError::Malformed {
            site: crate::error::MalformedSite::StageSignature,
        });
        for slot in [&[1_u8, 1][..], &[1_u8, 0, 1, 1, 0, 0][..]] {
            let mut forged = SmallVec::<_, 0, Global>::from_iter(
                expected.get(.. 23).unwrap_or_default().iter().copied(),
            );
            forged.extend_from_slice(slot);
            forged.extend_from_slice(&[0, 0, 0]);
            assert_eq!(
                crate::decode::decode(ArtifactImage::from(forged.as_slice())).map(|_| ()),
                malformed
            );
        }
    }

    #[test]
    fn a_ruled_definition_closes_its_segment_with_its_rules()
    {
        use crate::operation_rules::OperationNode;
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let unit = builder.arena().value_unit();
        // `f(x) ==> S(x)`, f at position 0 and S constructor 1 of the data
        // declaration at position 3.
        let rules =
            crate::operation_rules::OperationRules::new(SmallVec::<_, 0, Global>::from_iter([
                crate::operation_rules::OperationRule::new(
                    alloc::boxed::Box::from([
                        OperationNode::Operation {
                            constant: ConstantIndex::from(0_usize),
                            arity: crate::presented::FieldCount::from(1_usize),
                        },
                        OperationNode::Variable(crate::presented::RuleVariable::from(0_u32)),
                    ]),
                    alloc::boxed::Box::from([
                        OperationNode::Constructor {
                            family: ConstantIndex::from(3_usize),
                            tag: crate::term::ConstructorTag::from(1_usize),
                        },
                        OperationNode::Results(crate::presented::FieldCount::from(4_usize)),
                    ]),
                ),
            ]));
        let definition = builder
            .def(LevelSignature::monomorphic(), unit_type, unit)
            .ruled(rules.clone());
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, definition)];
        // The ruled kind, then the plain definition's fields; then no related
        // pair, no law, and the one rule: its left side, an operation at 0 of
        // arity 1 and variable 0, and its right side, constructor 1 of the
        // declaration at 3 and a results tuple of 4. Each position is bare:
        // 2 * 0 + 1 and 2 * 3 + 1.
        let expected = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 0, 1, 0, 0, 0, 0x0E, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0,
            2, 0, 0, 0, 0, 0, 0, 1, 2, 2, 1, 1, 1, 0, 2, 0, 7, 1, 3, 4,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(
            bytes.as_image().as_ref(),
            expected,
            "the ruled segment's literal bytes"
        );
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded.declarations().first().expect("one definition");
        assert_eq!(
            declaration.declaration().operation_rules(),
            &rules,
            "the rules decode in written order"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected,
            "and re-encode to the same bytes"
        );
        // A ruled kind closing with no rule decodes to a plain definition,
        // whose canonical bytes carry the plain kind.
        let empty = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 0, 1, 0, 0, 0, 0x0E, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0,
            2, 0, 0, 0, 0, 0, 0, 0,
        ];
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(empty.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::NonCanonical,
            }),
            "an empty rule block is not canonical"
        );
        // A node tag outside the alphabet refuses at its own site.
        let mut unknown = expected;
        if let Some(tag) = unknown.get_mut(31) {
            *tag = 9;
        }
        assert!(
            matches!(
                crate::decode::decode(ArtifactImage::from(unknown.as_slice())),
                Err(crate::error::DecodeError::UnknownTag {
                    site: crate::error::TagSite::RuleNode,
                    ..
                })
            ),
            "an unknown rule node tag is refused"
        );
    }

    #[test]
    fn a_covered_definition_closes_its_segment_with_its_derivations()
    {
        use crate::cover::Cases;
        use crate::cover::Cover;
        use crate::cover::Covered;
        use crate::cover::Loop;
        use crate::cover::Step;
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let unit = builder.arena().value_unit();
        let returned = builder.arena().computation_return(unit);
        let body = builder.arena().value_thunk(returned);
        // One derivation of every step and every cases' form: a data split
        // over a point and a loop, a composition under it, an integer test,
        // and the widths of a tuple, a record and a sum.
        let mut cover = Cover::new();
        let point = cover.mint(Step::Var(0));
        let looped = cover.mint(Step::Var(1));
        let below = cover.mint(Step::Split {
            cases: Cases::Integer(crate::Literal::Integer(crate::IntegerLiteral::new(
                crate::Sign::NonNegative,
                crate::Magnitude::from_decimal_text(alloc::string::String::from("7"))
                    .expect("digits"),
            ))),
            branches: SmallVec::<_, 0, Global>::from_iter([point, looped]),
        });
        let composed = cover.mint(Step::Compose(below));
        for cases in [
            Cases::Boolean,
            Cases::Tuple(2),
            Cases::Record(3),
            Cases::Sum(4),
            Cases::List,
            Cases::Guard,
            Cases::Absurd,
        ] {
            let _other = cover.mint(Step::Split {
                cases,
                branches: SmallVec::<_, 0, Global>::from_iter([point]),
            });
        }
        let _root = cover.mint(Step::Split {
            cases: Cases::Data {
                family: ConstantIndex::from(3_usize),
                constructors: SmallVec::<_, 0, Global>::from_iter([(
                    crate::term::ConstructorTag::from(0_usize),
                    crate::presented::FieldCount::from(2_usize),
                )]),
                loops: SmallVec::<_, 0, Global>::from_iter([Loop::new(
                    ConstantIndex::from(4_usize),
                    crate::CellIndex::from(0_usize),
                )]),
            },
            branches: SmallVec::<_, 0, Global>::from_iter([composed, looped]),
        });
        let covers = SmallVec::<_, 0, Global>::from_iter([Covered {
            root: returned,
            cover: cover.clone(),
        }]);
        let definition = builder
            .def(LevelSignature::monomorphic(), unit_type, body)
            .covered(covers);
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, definition)];
        let bytes = super::encode(&arena, &declarations);
        let image = bytes.as_image();
        assert_eq!(
            image.as_ref().get(12).copied(),
            Some(u8::from(crate::KIND_DEF_COVERED)),
            "the covered kind follows the header, the table, the imports and the mark"
        );
        let decoded = crate::decode::decode(image).expect("the covered artifact decodes");
        let declaration = decoded.declarations().first().expect("one definition");
        assert_eq!(
            declaration.declaration().covers().len(),
            1,
            "the one match's derivation"
        );
        assert_eq!(
            declaration
                .declaration()
                .covers()
                .first()
                .map(|covered| &covered.cover),
            Some(&cover),
            "the derivation decodes step for step"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            image.as_ref(),
            "and re-encodes to the same bytes"
        );
        // The cover block ends the segment, so the first step's tag stands
        // where the derivation's own bytes begin.
        let mut alone = super::EncodedArtifact::new();
        super::encode_cover(&mut alone, &cover, &mut super::Positions::default());
        let first_step = image
            .as_ref()
            .len()
            .saturating_sub(alone.as_image().as_ref().len())
            .saturating_add(1);
        let mut unknown = SmallVec::<_, 0, Global>::from_iter(image.as_ref().iter().copied());
        if let Some(tag) = unknown.get_mut(first_step) {
            *tag = 9;
        }
        assert!(
            matches!(
                crate::decode::decode(ArtifactImage::from(unknown.as_slice())),
                Err(crate::error::DecodeError::UnknownTag {
                    site: crate::error::TagSite::CoverStep,
                    ..
                })
            ),
            "an unknown step tag is refused at its own site"
        );
    }

    #[test]
    fn a_codata_declaration_closes_its_segment_with_its_observations()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Computation, Level::zero());
        let parameter = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        // `Stream(a)`: `head : F Integer` and `tail : Stream(a)`.
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let head = builder.arena().comp_type_returner(integer);
        let own = builder.arena().value_variable(DeBruijnIndex::from(0_u32));
        let tail = builder.arena().comp_type_codata(
            ConstantIndex::from(0_usize),
            SmallVec::<_, 0, Global>::from_iter([own]),
        );
        let codata = builder.codata(
            LevelSignature::monomorphic(),
            SmallVec::<_, 0, Global>::from_iter([parameter]),
            SmallVec::<_, 0, Global>::from_iter([head, tail]),
            kind,
        );
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, codata)];
        let bytes = super::encode(&arena, &declarations);
        let image = bytes.as_image();
        // The kind follows the header, the empty atom table, the segment's
        // empty table of names, its empty imports and the admission mark.
        let kind_at = 12;
        assert_eq!(
            image.as_ref().get(kind_at).copied(),
            Some(u8::from(crate::tags::KIND_CODATA))
        );
        let decoded = crate::decode::decode(ArtifactImage::from(image.as_ref()))
            .expect("a codata declaration decodes");
        let declaration = decoded.declarations().first().expect("one codata");
        let crate::decl::DeclarationContent::Codata {
            ref parameters,
            ref observations,
            ..
        } = *declaration.declaration().content()
        else {
            panic!("the declaration decodes as codata");
        };
        assert_eq!(parameters.len(), 1);
        let read = |at: usize| {
            let id = observations.get(at)?;
            decoded.arena().comp_type(*id)
        };
        assert!(
            matches!(read(0), Some(&crate::types::CompType::Returner(_)))
                && matches!(
                    read(1),
                    Some(&crate::types::CompType::Codata { declaration, ref arguments })
                        if usize::from(declaration) == 0 && arguments.len() == 1
                ),
            "the observations are read back in order, the second naming the declaration"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            image.as_ref()
        );
        // The data kind over the same bytes reads the observation roots as a
        // constructor's fields, and refuses them as computation types.
        let mut plain = SmallVec::<_, 0, Global>::from_iter(image.as_ref().iter().copied());
        if let Some(kind) = plain.get_mut(kind_at) {
            *kind = u8::from(crate::tags::KIND_DATA);
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(plain.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::Polarity,
            })
        );
    }

    #[test]
    fn a_literal_identity_test_closes_its_segment_with_its_base_and_polarity()
    {
        use crate::IdentityBase;
        use crate::LiteralIdentity;
        use crate::Polarity;
        for (base, atom) in [
            (IdentityBase::Integer, BaseType::Integer),
            (IdentityBase::Text, BaseType::String),
        ] {
            for polarity in [Polarity::Same, Polarity::Different] {
                let test = LiteralIdentity::new(base, polarity);
                let mut arena = TermArena::new();
                let mut builder = DeclarationBuilder::new(&mut arena);
                let compared = builder.arena().value_type_base(atom);
                let unit = builder.arena().value_type_unit();
                let boolean = builder.arena().value_type_sum(&[unit, unit]);
                let answer = builder.arena().comp_type_returner(boolean);
                let inner = builder.arena().comp_type_arrow(compared, answer);
                let outer = builder.arena().comp_type_arrow(compared, inner);
                let declared = builder.arena().value_type_thunk(outer);
                let identity =
                    builder.literal_identity(LevelSignature::monomorphic(), declared, test);
                let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, identity)];
                let bytes = super::encode(&arena, &declarations);
                let image =
                    SmallVec::<_, 0, Global>::from_iter(bytes.as_image().as_ref().iter().copied());
                assert_eq!(
                    image.get(12).copied(),
                    Some(u8::from(crate::tags::KIND_LITERAL_IDENTITY))
                );
                let (base_at, polarity_at) = (image.len() - 2, image.len() - 1);
                assert_eq!(
                    (image.get(base_at).copied(), image.get(polarity_at).copied()),
                    (
                        Some(u8::from(super::identity_base_tag(base))),
                        Some(u8::from(match polarity {
                            Polarity::Same => crate::tags::IDENTITY_SAME,
                            Polarity::Different => crate::tags::IDENTITY_DIFFERENT,
                        }))
                    ),
                    "the segment closes with the base's atom and the polarity"
                );
                let decoded = crate::decode::decode(ArtifactImage::from(image.as_slice()))
                    .expect("a literal identity test decodes");
                let content = decoded
                    .declarations()
                    .first()
                    .map(|marked| marked.declaration().content().clone());
                assert!(
                    matches!(
                        content,
                        Some(crate::decl::DeclarationContent::LiteralIdentity { test: read, .. })
                            if read == test
                    ),
                    "the test reads back whole: {content:?}"
                );
                assert_eq!(
                    super::encode(decoded.arena(), decoded.declarations())
                        .as_image()
                        .as_ref(),
                    image.as_slice()
                );
                let mut numeric = image.clone();
                if let Some(byte) = numeric.get_mut(base_at) {
                    *byte = u8::from(crate::tags::BASE_NUMERIC);
                }
                assert_eq!(
                    crate::decode::decode(ArtifactImage::from(numeric.as_slice())).err(),
                    Some(crate::error::DecodeError::UnknownTag {
                        site: crate::error::TagSite::IdentityBase,
                        tag: crate::tags::BASE_NUMERIC,
                    }),
                    "a numeric base is no identity of literals"
                );
                let mut third = image;
                if let Some(byte) = third.get_mut(polarity_at) {
                    *byte = 2;
                }
                assert_eq!(
                    crate::decode::decode(ArtifactImage::from(third.as_slice())).err(),
                    Some(crate::error::DecodeError::UnknownTag {
                        site: crate::error::TagSite::IdentityPolarity,
                        tag: crate::WireTag::from(2_u8),
                    })
                );
            }
        }
    }

    #[test]
    fn a_presented_data_declaration_closes_its_segment_with_its_rules()
    {
        use crate::presented::Presentation;
        use crate::presented::PresentedRule;
        use crate::presented::RuleNode;
        use crate::presented::RuleVariable;

        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = builder.arena().value_type_data(
            crate::ConstantIndex::from(0_usize),
            SmallVec::<_, 0, Global>::new(),
        );
        let tag = |ordinal: usize| RuleNode::Constructor(crate::ConstructorTag::from(ordinal));
        let variable = RuleNode::Variable(RuleVariable::from(0_u32));
        // The circle: `base`, `loop(x)`, `unloop(x)`, with
        // `loop(unloop(x)) ==> x` and `unloop(loop(x)) ==> x`.
        let rules = SmallVec::<_, 0, Global>::from_iter([
            PresentedRule::new(
                SmallVec::<_, 0, Global>::from_iter([tag(1), tag(2), variable]).into(),
                SmallVec::<_, 0, Global>::from_iter([variable]).into(),
            ),
            PresentedRule::new(
                SmallVec::<_, 0, Global>::from_iter([tag(2), tag(1), variable]).into(),
                SmallVec::<_, 0, Global>::from_iter([variable]).into(),
            ),
        ]);
        let data = builder
            .data(
                LevelSignature::monomorphic(),
                SmallVec::<_, 0, Global>::new(),
                SmallVec::<_, 0, Global>::from_iter([
                    SmallVec::<_, 0, Global>::new(),
                    SmallVec::<_, 0, Global>::from_iter([own]),
                    SmallVec::<_, 0, Global>::from_iter([own]),
                ]),
                kind,
            )
            .presented(Presentation::new(rules.clone()));
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, data)];
        // The presented kind, then the plain data declaration's fields: the
        // universe and the circle's own type as entries, the declared root, no
        // parameter, three constructors of arity zero, one and one; then two
        // rules, each two sides of a node count and tagged nodes.
        let expected = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 0, 1, 0, 0, 0, 8, 0, 0, 0, 2, 0x02, 0, 0, 0x5D, 1, 0,
            0, 0, 3, 0, 1, 2, 1, 2, 2, 3, 0, 1, 0, 2, 1, 0, 1, 1, 0, 3, 0, 2, 0, 1, 1, 0, 1, 1, 0,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded
            .declarations()
            .first()
            .expect("one data declaration");
        assert_eq!(declaration.declaration().presentation().rules(), rules);
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected
        );
        // A presented kind closing with no rule decodes to a free type, whose
        // canonical bytes carry the plain kind.
        let empty = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 0, 1, 0, 0, 0, 8, 0, 0, 0, 2, 0x02, 0, 0, 0x5D, 1, 0,
            0, 0, 3, 0, 1, 2, 1, 2, 0,
        ];
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(empty.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::NonCanonical,
            })
        );
        // A node tag outside the constructor and variable alphabet is refused
        // at the rule-node site.
        let mut unknown = expected;
        if let Some(node) = unknown.get_mut(35) {
            *node = 2;
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(unknown.as_slice())),
            Err(crate::error::DecodeError::UnknownTag {
                site: crate::error::TagSite::RuleNode,
                tag: crate::WireTag::from(2_u8),
            })
        );
        // The plain kind over the same bytes leaves the rules unread.
        let mut plain = expected;
        if let Some(kind) = plain.get_mut(12) {
            *kind = 6;
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(plain.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    #[test]
    fn a_type_of_words_closes_its_segment_with_its_cells()
    {
        use crate::presented::FreeCell;
        use crate::presented::FreeCells;
        use crate::presented::Presentation;
        use crate::presented::RuleNode;

        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = builder.arena().value_type_data(
            crate::ConstantIndex::from(0_usize),
            SmallVec::<_, 0, Global>::new(),
        );
        let base =
            || ThinShared::from_iter([RuleNode::Constructor(crate::ConstructorTag::from(0_usize))]);
        let cells = FreeCells::new(
            crate::ConstantIndex::from(0_usize),
            SmallVec::<_, 0, Global>::from_iter([FreeCell::new(base(), base())]),
        );
        let data = builder
            .data(
                LevelSignature::monomorphic(),
                SmallVec::<_, 0, Global>::new(),
                SmallVec::<_, 0, Global>::from_iter([
                    SmallVec::<_, 0, Global>::new(),
                    SmallVec::<_, 0, Global>::from_iter([own]),
                    SmallVec::<_, 0, Global>::from_iter([own]),
                ]),
                kind,
            )
            .presented(Presentation::words(cells.clone()));
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, data)];
        // The words kind, then the presented declaration's fields as the
        // circle writes them; then the sort's position, one cell, and its two
        // endpoints, each the one constructor `base`.
        let expected = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 0, 1, 0, 0, 0, 10, 0, 0, 0, 2, 0x02, 0, 0, 0x5D, 1,
            0, 0, 0, 3, 0, 1, 2, 1, 2, 2, 3, 0, 1, 0, 2, 1, 0, 1, 1, 0, 3, 0, 2, 0, 1, 1, 0, 1, 1,
            0, 1, 1, 1, 0, 0, 1, 0, 0,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded
            .declarations()
            .first()
            .expect("one data declaration");
        assert_eq!(
            declaration.declaration().presentation(),
            &Presentation::words(cells.clone())
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected
        );
        // Words whose rules were dropped still decode, to be refused by the
        // kernel against the mint, and keep their canonical bytes.
        let dropped = [
            b'G', b'K', b'X', b'1', 12, 0, 8, 0, 1, 0, 0, 0, 10, 0, 0, 0, 2, 0x02, 0, 0, 0x5D, 1,
            0, 0, 0, 3, 0, 1, 2, 1, 2, 0, 1, 1, 1, 0, 0, 1, 0, 0,
        ];
        let decoded = crate::decode::decode(ArtifactImage::from(dropped.as_slice()))
            .expect("a rule count of none decodes under the words kind");
        let declaration = decoded
            .declarations()
            .first()
            .expect("one data declaration");
        assert_eq!(declaration.declaration().presentation().rules(), []);
        assert_eq!(
            declaration.declaration().presentation().cells(),
            Some(&cells)
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            dropped
        );
        // The same cells at the reflexivity of their point write the higher
        // kind and decode to the same wrapping.
        let wrapped = cells.wrapped(crate::presented::Reflexivities::from(1_usize));
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = builder.arena().value_type_data(
            crate::ConstantIndex::from(0_usize),
            SmallVec::<_, 0, Global>::new(),
        );
        let data = builder
            .data(
                LevelSignature::monomorphic(),
                SmallVec::<_, 0, Global>::new(),
                SmallVec::<_, 0, Global>::from_iter([
                    SmallVec::<_, 0, Global>::new(),
                    SmallVec::<_, 0, Global>::from_iter([own]),
                    SmallVec::<_, 0, Global>::from_iter([own]),
                ]),
                kind,
            )
            .presented(Presentation::words(wrapped.clone()));
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, data)];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(
            bytes.as_image().as_ref().get(12),
            Some(&u8::from(super::tags::KIND_DATA_WORDS_HIGHER))
        );
        let decoded = crate::decode::decode(bytes.as_image())
            .expect("words over a wrapped point decode under their kind");
        let declaration = decoded
            .declarations()
            .first()
            .expect("one data declaration");
        assert_eq!(
            declaration.declaration().presentation().cells(),
            Some(&wrapped)
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations()).as_image(),
            bytes.as_image()
        );
    }

    #[test]
    fn an_interfaced_atom_closes_its_segment_with_its_interface()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let relation = builder.arena().value_unit();
        let reflexivity = builder.arena().value_tuple(&[relation]);
        let interface = crate::decl::AtomInterface::new(relation, reflexivity);
        let atom = builder
            .abstract_type(
                LevelSignature::monomorphic(),
                kind,
                integer,
                super::SealScope::Open,
            )
            .interfaced(interface);
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, atom)];
        let bytes = super::encode(&arena, &declarations);
        let image = bytes.as_image();
        // The kind follows the header, the one-entry atom table with its empty
        // table of names, the segment's empty table of names, its empty
        // imports and the admission mark.
        let kind_at = 14;
        assert_eq!(
            image.as_ref().get(kind_at).copied(),
            Some(u8::from(crate::tags::KIND_ABSTRACT_INTERFACED))
        );
        let decoded = crate::decode::decode(ArtifactImage::from(image.as_ref()))
            .expect("an interfaced atom decodes");
        let declaration = decoded.declarations().first().expect("one atom");
        let crate::decl::DeclarationContent::AbstractType {
            interface: super::Maybe::Present(read),
            ..
        } = *declaration.declaration().content()
        else {
            panic!("the atom decodes with its interface");
        };
        let arity = |value| {
            decoded
                .arena()
                .value(value)
                .and_then(crate::term::Value::components)
                .map(<[_]>::len)
        };
        assert_eq!(
            (arity(read.relation()), arity(read.reflexivity())),
            (Some(0), Some(1)),
            "the relation and the reflexivity are read back in order"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            image.as_ref()
        );
        // The plain kind over the same bytes leaves the interface unread.
        let mut plain = SmallVec::<_, 0, Global>::from_iter(image.as_ref().iter().copied());
        if let Some(kind) = plain.get_mut(kind_at) {
            *kind = u8::from(crate::tags::KIND_ABSTRACT_TYPE);
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(plain.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    #[test]
    fn a_lawful_atom_closes_its_segment_with_its_law()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let relation = builder.arena().value_unit();
        let reflexivity = builder.arena().value_tuple(&[relation]);
        let law = builder.arena().value_tuple(&[relation, reflexivity]);
        let interface = crate::decl::AtomInterface::new(relation, reflexivity).lawful(law);
        let atom = builder
            .abstract_type(
                LevelSignature::monomorphic(),
                kind,
                integer,
                super::SealScope::Open,
            )
            .interfaced(interface);
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, atom)];
        let bytes = super::encode(&arena, &declarations);
        let image = bytes.as_image();
        let kind_at = 14;
        assert_eq!(
            image.as_ref().get(kind_at).copied(),
            Some(u8::from(crate::tags::KIND_ABSTRACT_LAWFUL))
        );
        let decoded = crate::decode::decode(ArtifactImage::from(image.as_ref()))
            .expect("a lawful atom decodes");
        let declaration = decoded.declarations().first().expect("one atom");
        let crate::decl::DeclarationContent::AbstractType {
            interface: super::Maybe::Present(read),
            ..
        } = *declaration.declaration().content()
        else {
            panic!("the atom decodes with its interface");
        };
        let arity = |value| {
            decoded
                .arena()
                .value(value)
                .and_then(crate::term::Value::components)
                .map(<[_]>::len)
        };
        let super::Maybe::Present(read_law) = read.law()
        else {
            panic!("the atom decodes with its law");
        };
        assert_eq!(
            (
                arity(read.relation()),
                arity(read.reflexivity()),
                arity(read_law)
            ),
            (Some(0), Some(1), Some(2)),
            "the relation, the reflexivity and the law are read back in order"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            image.as_ref()
        );
        // The interfaced kind over the same bytes leaves the law unread.
        let mut lawless = SmallVec::<_, 0, Global>::from_iter(image.as_ref().iter().copied());
        if let Some(kind) = lawless.get_mut(kind_at) {
            *kind = u8::from(crate::tags::KIND_ABSTRACT_INTERFACED);
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(lawless.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    #[test]
    fn a_role_closes_a_holder_s_segment_5304()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let unit = builder.arena().value_unit();
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let plain_def = builder.def(LevelSignature::monomorphic(), unit_type, unit);
        let lawful_def = plain_def
            .clone()
            .lawful(SmallVec::<_, 0, Global>::from_iter([
                crate::ConstantIndex::from(0_usize),
            ]));
        let builder = DeclarationBuilder::new(&mut arena);
        let plain_data = builder.indexed(
            LevelSignature::monomorphic(),
            SmallVec::<_, 0, Global>::new(),
            (
                SmallVec::<_, 0, Global>::new(),
                SmallVec::<_, 0, Global>::from_iter([SmallVec::<_, 0, Global>::new()]),
                SmallVec::<_, 0, Global>::new(),
            ),
            kind,
        );
        let encoded = |declaration: &Declaration| {
            let marked = [MarkedDeclaration::new(
                AdmissionMark::Checked,
                declaration.clone(),
            )];
            SmallVec::<_, 0, Global>::from_iter(
                super::encode(&arena, &marked)
                    .as_image()
                    .as_ref()
                    .iter()
                    .copied(),
            )
        };
        // Each row: the plain declaration, its role, the role kind, the
        // counts the holder writes after the plain segment, and the role tag.
        for (plain, role, kind, counts, tag) in [
            (
                &plain_def,
                crate::Builtin::IrArgs,
                crate::tags::KIND_DEF_ROLED,
                &[0_u8, 0_u8, 0_u8, 0_u8][..],
                crate::tags::ROLE_IR_ARGS,
            ),
            (
                &lawful_def,
                crate::Builtin::IrDecode,
                crate::tags::KIND_DEF_ROLED,
                &[0_u8, 0_u8][..],
                crate::tags::ROLE_IR_DECODE,
            ),
            (
                &plain_data,
                crate::Builtin::IrPair,
                crate::tags::KIND_DATA_ROLED,
                &[][..],
                crate::tags::ROLE_IR_PAIR,
            ),
        ] {
            let held = plain.clone().held(role);
            let (unmarked, marked) = (encoded(plain), encoded(&held));
            // The holder writes the role kind where the plain declaration
            // writes its kind. A held definition writes each block the plain
            // one leaves out as a count of none, and the segment closes with
            // the role's tag.
            let mut expected = unmarked;
            if let Some(byte) = expected.get_mut(12) {
                *byte = u8::from(kind);
            }
            expected.extend_from_slice(counts);
            expected.push(u8::from(tag));
            assert_eq!(marked, expected, "{role:?} closes its holder's segment");
            let decoded = crate::decode::decode(ArtifactImage::from(marked.as_slice()))
                .expect("a holder decodes");
            let declaration = decoded.declarations().first().expect("one holder");
            assert_eq!(
                declaration.declaration().role(),
                Maybe::Present(role),
                "the role decodes"
            );
            assert_eq!(
                super::encode(decoded.arena(), decoded.declarations())
                    .as_image()
                    .as_ref(),
                marked.as_slice(),
                "and re-encodes to the same bytes"
            );
            // A role tag outside the alphabet refuses at its own site.
            let mut unknown = marked;
            if let Some(byte) = unknown.last_mut() {
                *byte = 9;
            }
            assert_eq!(
                crate::decode::decode(ArtifactImage::from(unknown.as_slice())).map(|_| ()),
                Err(crate::error::DecodeError::UnknownTag {
                    site: crate::error::TagSite::Role,
                    tag: crate::WireTag::from(9_u8),
                }),
                "an unknown role is refused"
            );
        }
    }

    #[test]
    fn a_coinductive_datatype_writes_its_own_kind_6647()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let unit = builder.arena().value_unit();
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let definition = builder.def(LevelSignature::monomorphic(), unit_type, unit);
        let builder = DeclarationBuilder::new(&mut arena);
        let inductive = builder.indexed(
            LevelSignature::monomorphic(),
            SmallVec::<_, 0, Global>::new(),
            (
                SmallVec::<_, 0, Global>::new(),
                SmallVec::<_, 0, Global>::from_iter([SmallVec::<_, 0, Global>::new()]),
                SmallVec::<_, 0, Global>::new(),
            ),
            kind,
        );
        let encoded = |declaration: &Declaration| {
            let marked = [MarkedDeclaration::new(
                AdmissionMark::Checked,
                declaration.clone(),
            )];
            SmallVec::<_, 0, Global>::from_iter(
                super::encode(&arena, &marked)
                    .as_image()
                    .as_ref()
                    .iter()
                    .copied(),
            )
        };
        let coinductive = inductive.clone().coinductive();
        let (least, greatest) = (encoded(&inductive), encoded(&coinductive));
        // The coinductive datatype writes its own kind where the inductive one
        // writes its kind, and every other byte is the same.
        let mut expected = least.clone();
        if let Some(byte) = expected.get_mut(12) {
            *byte = u8::from(crate::tags::KIND_DATA_COINDUCTIVE);
        }
        assert_eq!(greatest, expected, "the mark is the kind byte alone");
        assert_ne!(greatest, least, "the two fixpoints have two identities");
        let decoded = crate::decode::decode(ArtifactImage::from(greatest.as_slice()))
            .expect("a coinductive datatype decodes");
        let declaration = decoded.declarations().first().expect("one datatype");
        assert_eq!(
            declaration.declaration().fixpoint(),
            crate::DataFixpoint::Greatest,
            "the mark decodes"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            greatest.as_slice(),
            "and re-encodes to the same bytes"
        );
        // A definition takes no mark, so its bytes stay.
        assert_eq!(
            encoded(&definition.clone().coinductive()),
            encoded(&definition),
            "a definition is no datatype"
        );
    }

    #[test]
    fn an_indexed_data_declaration_closes_its_segment_with_its_indices()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let index = builder.arena().value_type_unit();
        let at = builder.arena().value_unit();
        let data = builder.indexed(
            LevelSignature::monomorphic(),
            SmallVec::<_, 0, Global>::new(),
            (
                SmallVec::<_, 0, Global>::from_iter([index]),
                SmallVec::<_, 0, Global>::from_iter([SmallVec::<_, 0, Global>::new()]),
                SmallVec::<_, 0, Global>::from_iter([SmallVec::<_, 0, Global>::from_iter([at])]),
            ),
            kind,
        );
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, data)];
        let bytes = super::encode(&arena, &declarations);
        let image = bytes.as_image();
        assert_eq!(
            image.as_ref().get(12).copied(),
            Some(u8::from(crate::tags::KIND_DATA_INDEXED))
        );
        let decoded = crate::decode::decode(ArtifactImage::from(image.as_ref()))
            .expect("an indexed declaration decodes");
        let declaration = decoded
            .declarations()
            .first()
            .expect("one data declaration");
        let crate::decl::DeclarationContent::Data {
            ref indices,
            ref results,
            ..
        } = *declaration.declaration().content()
        else {
            panic!("a data declaration decodes as data");
        };
        assert_eq!(indices.len(), 1, "the index classifier is read back");
        assert_eq!(
            results
                .iter()
                .map(|result| result.len())
                .collect::<SmallVec<_, 0, Global>>(),
            [1],
            "the constructor's result index is read back"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            image.as_ref()
        );
        // The plain kind over the same bytes leaves the indices unread.
        let mut plain = SmallVec::<_, 0, Global>::from_iter(image.as_ref().iter().copied());
        if let Some(kind) = plain.get_mut(12) {
            *kind = u8::from(crate::tags::KIND_DATA);
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(plain.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    /// - see: #8338
    #[test]
    fn an_indexed_data_declaration_closes_its_segment_with_its_rules_8338()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let index = builder.arena().value_type_unit();
        let at = builder.arena().value_unit();
        let own = builder.arena().value_type_data(
            crate::term::ConstantIndex::from(0_usize),
            SmallVec::<_, 0, Global>::from_iter([at]),
        );
        // `Stop` and `Skip(k)` at one index, and `Skip(Skip(k)) ==> Skip(k)`.
        let skip = crate::RuleNode::Constructor(crate::ConstructorTag::from(1_usize));
        let k = crate::RuleNode::Variable(crate::RuleVariable::from(0_u32));
        let rules = crate::Presentation::new(SmallVec::<_, 0, Global>::from_iter([
            crate::PresentedRule::new([skip, skip, k].into(), [skip, k].into()),
        ]));
        let free = builder.indexed(
            LevelSignature::monomorphic(),
            SmallVec::<_, 0, Global>::new(),
            (
                SmallVec::<_, 0, Global>::from_iter([index]),
                SmallVec::<_, 0, Global>::from_iter([
                    SmallVec::<_, 0, Global>::new(),
                    SmallVec::<_, 0, Global>::from_iter([own]),
                ]),
                SmallVec::<_, 0, Global>::from_iter([
                    SmallVec::<_, 0, Global>::from_iter([at]),
                    SmallVec::<_, 0, Global>::from_iter([at]),
                ]),
            ),
            kind,
        );
        let presented = free.clone().presented(rules.clone());
        let encoded = |declaration: &Declaration| {
            let marked = [MarkedDeclaration::new(
                AdmissionMark::Checked,
                declaration.clone(),
            )];
            SmallVec::<_, 0, Global>::from_iter(
                super::encode(&arena, &marked)
                    .as_image()
                    .as_ref()
                    .iter()
                    .copied(),
            )
        };
        let (plain, ruled) = (encoded(&free), encoded(&presented));
        assert_eq!(
            (plain.get(12).copied(), ruled.get(12).copied()),
            (
                Some(u8::from(crate::tags::KIND_DATA_INDEXED)),
                Some(u8::from(crate::tags::KIND_DATA_INDEXED_PRESENTED))
            ),
            "a family with a rule writes its own kind"
        );
        assert!(
            ruled.len() > plain.len(),
            "and the rule block after the results"
        );
        let decoded = crate::decode::decode(ArtifactImage::from(ruled.as_slice()))
            .expect("an indexed declaration with a rule decodes");
        let declaration = decoded
            .declarations()
            .first()
            .expect("one data declaration");
        let crate::decl::DeclarationContent::Data {
            ref indices,
            ref results,
            ..
        } = *declaration.declaration().content()
        else {
            panic!("a data declaration decodes as data");
        };
        assert_eq!(
            (indices.len(), results.len()),
            (1, 2),
            "the index and each result are read back"
        );
        assert_eq!(
            declaration.declaration().presentation(),
            &rules,
            "the rule is read back"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            ruled.as_slice(),
            "and re-encodes to the same bytes"
        );
        // The kind with no rule over the same bytes leaves the rules unread.
        let mut unruled = ruled.clone();
        if let Some(kind) = unruled.get_mut(12) {
            *kind = u8::from(crate::tags::KIND_DATA_INDEXED);
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(unruled.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    #[test]
    fn atom_positions_and_provenance_preserve_sequence_identity()
    {
        let mut positions = super::Positions::default();
        for mask in 0_u8 .. 64 {
            let mut arena = TermArena::new();
            let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
            let declared = arena.value_type_unit();
            let body = arena.value_unit();
            let mut declarations = SmallVec::<_, 0, Global>::new();
            let mut expected = SmallVec::<_, 0, Global>::new();
            for position in 0_u8 .. 6 {
                let builder = DeclarationBuilder::new(&mut arena);
                let is_atom = mask.checked_shr(u32::from(position)).unwrap_or(0) & 1 != 0;
                let declaration = if is_atom {
                    expected.push(usize::from(position));
                    builder.abstract_type(
                        LevelSignature::monomorphic(),
                        kind,
                        declared,
                        super::SealScope::Open,
                    )
                }
                else if position.rem_euclid(2) == 0 {
                    builder.axiom(LevelSignature::monomorphic(), declared)
                }
                else {
                    builder.def(LevelSignature::monomorphic(), declared, body)
                };
                let mark = if position.rem_euclid(2) == 0 {
                    AdmissionMark::Checked
                }
                else {
                    AdmissionMark::UncheckedBypass
                };
                declarations.push(MarkedDeclaration::new(mark, declaration));
            }
            assert_eq!(
                super::minted_atoms(&declarations)
                    .into_iter()
                    .map(usize::from)
                    .collect::<SmallVec<_, 0, Global>>(),
                expected
            );
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_minted_atom_table(
                &mut out,
                &mut positions,
                super::minted_places(&declarations, ConstantIndex::from(0_usize)),
                super::ByteCount::from(super::KEY_WIDTH_FLOOR),
            );
            // With no names the table is empty, and each atom at the place p
            // is written as 2p + 1.
            let mut bytes = SmallVec::<_, 0, Global>::from_iter([
                0xde_u8,
                0xad,
                u8::try_from(expected.len()).expect("at most six atoms"),
            ]);
            if !expected.is_empty() {
                bytes.push(0);
                bytes.extend(expected.into_iter().map(|position| {
                    u8::try_from(position.saturating_mul(2).saturating_add(1))
                        .expect("six positions")
                }));
            }
            assert_eq!(out.as_image().as_ref(), bytes.as_slice());
        }
        for (provenance, expected) in [
            (
                SmallVec::<_, 0, Global>::new(),
                SmallVec::<_, 0, Global>::from_iter([0]),
            ),
            (
                SmallVec::<_, 0, Global>::from_iter([
                    ConstantIndex::from(129_usize),
                    ConstantIndex::from(0_usize),
                    ConstantIndex::from(128_usize),
                ]),
                SmallVec::<_, 0, Global>::from_iter([3, 0x81, 1, 0, 0x80, 1]),
            ),
        ] {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_sealing_provenance(&mut out, &provenance);
            let mut bytes = SmallVec::<_, 0, Global>::from_iter([0xde_u8, 0xad]);
            bytes.extend(expected);
            assert_eq!(out.as_image().as_ref(), bytes.as_slice());
        }
    }

    #[test]
    fn an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let universe = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let atom = builder.abstract_type(
            LevelSignature::monomorphic(),
            universe,
            integer,
            super::SealScope::Closed(super::SealExtent::from(2_usize)),
        );
        let mut builder = DeclarationBuilder::new(&mut arena);
        let abstract_type = builder
            .arena()
            .value_type_abstract(ConstantIndex::from(0_usize));
        let quote = builder.arena().value_quote(abstract_type);
        let definition = builder
            .def(LevelSignature::monomorphic(), universe, quote)
            .named(StructuredName::from(SmallVec::<_, 0, Global>::from_iter([
                NameSegment::from_text(String::from("a")).expect("segment"),
            ])));
        let axiom =
            DeclarationBuilder::new(&mut arena).axiom(LevelSignature::monomorphic(), abstract_type);
        let leading = [
            MarkedDeclaration::new(AdmissionMark::Checked, atom),
            MarkedDeclaration::new(AdmissionMark::UncheckedBypass, definition),
            MarkedDeclaration::new(AdmissionMark::Checked, axiom),
        ];
        let named = super::Names::new(
            (1_u8 ..= 6)
                .map(|byte| Some(super::ConstantKey::from([byte; super::CONSTANT_KEY_LEN]))),
        );
        let namings = [super::Names::default(), named];
        let prefixes: SmallVec<SmallVec<_, 0, Global>, 0, Global> = namings
            .iter()
            .map(|names| {
                (0 ..= leading.len())
                    .map(|split| {
                        match super::encode_prefix(
                            &arena,
                            leading.get(.. split).expect("a split"),
                            names,
                        ) {
                            super::Maybe::Present(prefix) => prefix,
                            super::Maybe::Absent(absent) => panic!("no seal is open: {absent:?}"),
                        }
                    })
                    .collect()
            })
            .collect();
        // Built after the prefixes were encoded, as an editor's admission
        // builds a document's declarations after its closure's: one body is
        // the leading definition's own node, one is built anew to the same
        // content, and the last atom's seal is open to the end.
        let shared =
            DeclarationBuilder::new(&mut arena).def(LevelSignature::monomorphic(), universe, quote);
        let mut builder = DeclarationBuilder::new(&mut arena);
        let rebuilt_type = builder
            .arena()
            .value_type_abstract(ConstantIndex::from(0_usize));
        let rebuilt = builder.arena().value_quote(rebuilt_type);
        let anew = builder.def(LevelSignature::monomorphic(), universe, rebuilt);
        let open = DeclarationBuilder::new(&mut arena).abstract_type(
            LevelSignature::monomorphic(),
            universe,
            integer,
            super::SealScope::Open,
        );
        let whole: SmallVec<_, 0, Global> = leading
            .iter()
            .cloned()
            .chain([
                MarkedDeclaration::new(AdmissionMark::Checked, shared),
                MarkedDeclaration::new(AdmissionMark::Checked, anew),
                MarkedDeclaration::new(AdmissionMark::Checked, open),
            ])
            .collect();
        for (names, prefixes) in namings.iter().zip(&prefixes) {
            let expected = super::encode_named(&arena, &whole, None, names);
            for prefix in prefixes {
                let end = usize::from(prefix.end());
                assert_eq!(
                    super::encode_after(prefix, &arena, whole.get(end ..).expect("a split"), names),
                    expected,
                    "resumed after {end} declarations"
                );
            }
        }
    }

    #[test]
    fn a_prefix_with_an_open_seal_is_not_encoded_776()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let universe = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let open = builder.abstract_type(
            LevelSignature::monomorphic(),
            universe,
            integer,
            super::SealScope::Open,
        );
        let leading = [MarkedDeclaration::new(AdmissionMark::Checked, open)];
        assert!(matches!(
            super::encode_prefix(&arena, &leading, &super::Names::default()),
            super::Maybe::Absent(super::encoded_prefix::Absent::OpenSeal)
        ));
    }

    /// #6568: a keyed segment writes each position by where the segment
    /// first names it, so one declaration over two constants at two pairs of
    /// positions writes one image, and a member of its block by its place in
    /// the block.
    #[test]
    fn a_keyed_segment_writes_no_admission_order_6568()
    {
        let pair = |arena: &mut TermArena, first: usize, second: usize| {
            let mut builder = DeclarationBuilder::new(arena);
            let unit = builder.arena().value_type_unit();
            let declared = builder.arena().value_type_product(&[unit, unit]);
            let left = builder.arena().value_constant(ConstantIndex::from(first));
            let right = builder.arena().value_constant(ConstantIndex::from(second));
            let body = builder.arena().value_tuple(&[left, right]);
            MarkedDeclaration::new(
                AdmissionMark::Checked,
                builder.def(LevelSignature::monomorphic(), declared, body),
            )
        };
        let mut arena = TermArena::new();
        let early = pair(&mut arena, 7, 3);
        let late = pair(&mut arena, 2, 9);
        let repeated = pair(&mut arena, 7, 7);
        let keyed = |declaration: &MarkedDeclaration, block: core::ops::Range<ConstantIndex>| {
            let super::Maybe::Present(keyed) = super::keyed_segment(&arena, declaration, block)
            else {
                panic!("no seal is open");
            };
            keyed
        };
        let none = ConstantIndex::from(20_usize) .. ConstantIndex::from(20_usize);
        let (early_keyed, late_keyed) = (keyed(&early, none.clone()), keyed(&late, none.clone()));
        assert_eq!(
            early_keyed.image(),
            late_keyed.image(),
            "two pairs of positions in one shape write one image"
        );
        assert_eq!(early_keyed.named(), &[
            ConstantIndex::from(7_usize),
            ConstantIndex::from(3_usize)
        ]);
        assert_eq!(late_keyed.named(), &[
            ConstantIndex::from(2_usize),
            ConstantIndex::from(9_usize)
        ]);
        let repeated_keyed = keyed(&repeated, none);
        assert_ne!(
            repeated_keyed.image(),
            early_keyed.image(),
            "one position named twice is not two positions"
        );
        assert_eq!(repeated_keyed.named(), &[ConstantIndex::from(7_usize)]);
        let member = keyed(
            &early,
            ConstantIndex::from(7_usize) .. ConstantIndex::from(9_usize),
        );
        assert_eq!(
            member.named(),
            &[ConstantIndex::from(3_usize)],
            "a member of the block is not named outside it"
        );
        assert_ne!(member.image(), early_keyed.image());
    }

    /// #6845: a placed encoding writes each position as its place in rank
    /// order. A kept sequence with a retired position, and two declarations
    /// whose ranks swap, writes the bytes of the fresh sequence. Its raw
    /// encoding differs, so the test can fail.
    #[test]
    fn a_placed_encoding_writes_each_position_as_its_place_6845()
    {
        let named = |declaration: Declaration, name: &str| {
            let segment = NameSegment::from_text(name.into()).expect("a name segment");
            MarkedDeclaration::new(
                AdmissionMark::Checked,
                declaration.named(StructuredName::from(SmallVec::<_, 0, Global>::from_iter([
                    segment,
                ]))),
            )
        };
        let unit = |arena: &mut TermArena, name: &str| {
            let mut builder = DeclarationBuilder::new(arena);
            let declared = builder.arena().value_type_unit();
            let body = builder.arena().value_unit();
            named(
                builder.def(LevelSignature::monomorphic(), declared, body),
                name,
            )
        };
        let pair = |arena: &mut TermArena, first: usize, second: usize| {
            let mut builder = DeclarationBuilder::new(arena);
            let unit = builder.arena().value_type_unit();
            let declared = builder.arena().value_type_product(&[unit, unit]);
            let left = builder.arena().value_constant(ConstantIndex::from(first));
            let right = builder.arena().value_constant(ConstantIndex::from(second));
            let body = builder.arena().value_tuple(&[left, right]);
            named(
                builder.def(LevelSignature::monomorphic(), declared, body),
                "c",
            )
        };
        // The kept sequence: `a` at 0, a retired position 1, `b` at 2 and `c`
        // at 3 over both, with `b` ranked first.
        let mut kept = TermArena::new();
        let (a, b, c) = (
            unit(&mut kept, "a"),
            unit(&mut kept, "b"),
            pair(&mut kept, 0, 2),
        );
        let order = [2_usize, 0, 3].map(ConstantIndex::from);
        let places = super::Places::new(order, ConstantIndex::from(4_usize));
        assert_eq!(places.place(ConstantIndex::from(1_usize)), None);
        assert_eq!(
            places.place(ConstantIndex::from(3_usize)),
            Some(ConstantIndex::from(2_usize))
        );
        let ranked = [b, a, c];
        // The fresh sequence: `b` at 0, `a` at 1, and `c` at 2 over both.
        let mut fresh = TermArena::new();
        let fresh_sequence = [
            unit(&mut fresh, "b"),
            unit(&mut fresh, "a"),
            pair(&mut fresh, 1, 0),
        ];
        let expected = super::encode(&fresh, &fresh_sequence);
        assert_eq!(
            super::encode_placed(&kept, &ranked, &places)
                .as_image()
                .as_ref(),
            expected.as_image().as_ref(),
            "the kept sequence writes the bytes of the fresh one"
        );
        assert_ne!(
            super::encode(&kept, &ranked).as_image().as_ref(),
            expected.as_image().as_ref(),
            "the kept sequence written by position is not the fresh one"
        );
    }

    /// #7340: a named encoding writes each named place by its key in its
    /// segment's table. `c` reads `a` and `b`; a second sequence admits `z`
    /// before them. Named, the two write `c`'s segment byte for byte, and each
    /// decodes under its names to the sequence it encoded. Bare, `c`'s
    /// segments differ, so the test can fail. Names that miss a key refuse the
    /// bytes, and a key two places hold names the first of them alone. Names
    /// built whole name every place when each has a key, and none otherwise.
    #[test]
    fn a_named_encoding_writes_each_named_place_by_its_key_7340()
    {
        let named = |declaration: Declaration, name: &str| {
            let segment = NameSegment::from_text(name.into()).expect("a name segment");
            MarkedDeclaration::new(
                AdmissionMark::Checked,
                declaration.named(StructuredName::from(SmallVec::from_iter([segment]))),
            )
        };
        let unit = |arena: &mut TermArena, name: &str| {
            let mut builder = DeclarationBuilder::new(arena);
            let declared = builder.arena().value_type_unit();
            let body = builder.arena().value_unit();
            named(
                builder.def(LevelSignature::monomorphic(), declared, body),
                name,
            )
        };
        let fresh = |arena: &mut TermArena, name: &str| {
            let mut builder = DeclarationBuilder::new(arena);
            let declared = builder.arena().value_type_base(crate::BaseType::Integer);
            named(builder.axiom(LevelSignature::monomorphic(), declared), name)
        };
        let pair = |arena: &mut TermArena, first: usize, second: usize| {
            let mut builder = DeclarationBuilder::new(arena);
            let unit = builder.arena().value_type_unit();
            let declared = builder.arena().value_type_product(&[unit, unit]);
            let left = builder.arena().value_constant(ConstantIndex::from(first));
            let right = builder.arena().value_constant(ConstantIndex::from(second));
            let body = builder.arena().value_tuple(&[left, right]);
            named(
                builder.def(LevelSignature::monomorphic(), declared, body),
                "c",
            )
        };
        let key = |byte: u8| super::ConstantKey::from([byte; super::CONSTANT_KEY_LEN]);
        let mut arena = TermArena::new();
        let short = [
            unit(&mut arena, "a"),
            unit(&mut arena, "b"),
            pair(&mut arena, 0, 1),
        ];
        // The inserted axiom writes an entry of its own, so every later entry
        // takes a new global index. The pair's segment writes its own entries
        // from its base, and it reads the unit type through an import that
        // names the first unit's place by its key.
        let long = [
            fresh(&mut arena, "z"),
            unit(&mut arena, "a"),
            unit(&mut arena, "b"),
            pair(&mut arena, 1, 2),
        ];
        let short_names = super::Names::new([Some(key(1)), Some(key(2)), Some(key(3))]);
        let long_names =
            super::Names::new([Some(key(9)), Some(key(1)), Some(key(2)), Some(key(3))]);
        let last = |image: &super::EncodedArtifact, names: &super::Names| {
            let decoded = crate::decode_named(image.as_image(), names).expect("the bytes decode");
            let span = decoded
                .segments()
                .declaration_segments()
                .last()
                .expect("a last segment");
            let bytes = SmallVec::<_, 0, Global>::from_iter(
                image
                    .as_image()
                    .as_ref()
                    .get(usize::from(span.start) .. usize::from(span.end))
                    .expect("the segment's bytes")
                    .iter()
                    .copied(),
            );
            (decoded, bytes)
        };
        let short_named = super::encode_named(&arena, &short, None, &short_names);
        let long_named = super::encode_named(&arena, &long, None, &long_names);
        let (short_decoded, short_last) = last(&short_named, &short_names);
        let (long_decoded, long_last) = last(&long_named, &long_names);
        assert_eq!(
            short_last, long_last,
            "a declaration before the two it reads leaves its segment as it was"
        );
        assert_eq!(
            super::encode_named(
                short_decoded.arena(),
                short_decoded.declarations(),
                None,
                &short_names
            ),
            short_named,
            "the decoded sequence re-encodes to its bytes"
        );
        assert_eq!(
            long_decoded.declarations().len(),
            4,
            "the longer sequence decodes whole"
        );
        let short_bare = super::encode(&arena, &short);
        let long_bare = super::encode(&arena, &long);
        let (_, short_bare_last) = last(&short_bare, &super::Names::default());
        let (_, long_bare_last) = last(&long_bare, &super::Names::default());
        assert_ne!(
            short_bare_last, long_bare_last,
            "by position, the insertion moves the segment's bytes"
        );
        assert_eq!(
            crate::decode_named(
                short_named.as_image(),
                &super::Names::new([Some(key(1)), Some(key(4)), Some(key(3))])
            )
            .err(),
            Some(crate::DecodeError::Malformed {
                site: crate::MalformedSite::UnplacedName,
            }),
            "names that miss a key the segment holds refuse the bytes"
        );
        let shared = super::Names::new([Some(key(1)), Some(key(1)), Some(key(3))]);
        assert_eq!(
            (
                shared.key(ConstantIndex::from(0_usize)),
                shared.key(ConstantIndex::from(1_usize)),
                shared.place(&key(1))
            ),
            (Some(key(1)), None, Some(ConstantIndex::from(0_usize))),
            "a key two places hold names the first of them alone"
        );
        assert_eq!(
            super::encode_named(&arena, &short, None, &shared),
            super::encode_named(
                &arena,
                &short,
                None,
                &super::Names::new([Some(key(1)), None, Some(key(3))])
            ),
            "a later place whose key an earlier place holds is written bare"
        );
        assert_eq!(
            (
                super::Names::whole([Some(key(1)), Some(key(2)), Some(key(3))]),
                super::Names::whole([Some(key(1)), None, Some(key(3))])
            ),
            (short_names, super::Names::default()),
            "whole names name each place, or none when one place has no key"
        );
    }

    #[test]
    fn keys_that_share_a_word_widen_every_table_7340()
    {
        let mut arena = TermArena::new();
        let definition = |arena: &mut TermArena, body| {
            let mut builder = DeclarationBuilder::new(arena);
            let declared = builder.arena().value_type_unit();
            MarkedDeclaration::new(
                AdmissionMark::Checked,
                builder.def(LevelSignature::monomorphic(), declared, body),
            )
        };
        let unit = arena.value_unit();
        let first = definition(&mut arena, unit);
        let named_first = arena.value_constant(ConstantIndex::from(0_usize));
        let second = definition(&mut arena, named_first);
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let declared = builder.arena().value_type_product(&[unit_type, unit_type]);
        let left = builder.arena().value_constant(ConstantIndex::from(0_usize));
        let right = builder.arena().value_constant(ConstantIndex::from(1_usize));
        let body = builder.arena().value_tuple(&[left, right]);
        let pair = MarkedDeclaration::new(
            AdmissionMark::Checked,
            builder.def(LevelSignature::monomorphic(), declared, body),
        );
        let declarations = [first, second, pair];
        // A key whose first word is `head` and whose other bytes are `tail`.
        let key = |head: u8, tail: u8| {
            Some(super::ConstantKey::from(core::array::from_fn(|at| {
                if at < 8 { head } else { tail }
            })))
        };
        let apart = super::Names::new([key(1, 1), key(2, 2), key(3, 3)]);
        let close = super::Names::new([key(1, 1), key(2, 2), key(1, 3)]);
        assert_eq!(
            (usize::from(apart.width()), usize::from(close.width())),
            (8, 9),
            "keys apart in their first word take one word, and two that share it take a byte more"
        );
        let narrow = super::encode_named(&arena, &declarations, None, &apart);
        let wide = super::encode_named(&arena, &declarations, None, &close);
        // The second definition's segment: its table of the first one's key.
        let second_table = |image: &super::EncodedArtifact, names: &super::Names| {
            let decoded =
                crate::decode_named(image.as_image(), names).expect("the artifact decodes");
            let span = decoded
                .segments()
                .declaration_segments()
                .nth(1)
                .expect("a second segment");
            assert_eq!(
                super::encode_named(decoded.arena(), decoded.declarations(), None, names),
                *image,
                "the decoded sequence re-encodes to its bytes"
            );
            image
                .as_image()
                .as_ref()
                .get(usize::from(span.start) ..)
                .and_then(|segment| segment.get(.. usize::from(names.width()).saturating_add(1)))
                .map(|table| SmallVec::<_, 0, Global>::from_iter(table.iter().copied()))
        };
        assert_eq!(
            (
                narrow.as_image().as_ref().get(6).copied(),
                second_table(&narrow, &apart)
            ),
            (Some(8), Some(SmallVec::<u8, 0, Global>::from_iter([1; 9]))),
            "the header gives one word, and the table writes the first word of the key"
        );
        assert_eq!(
            (
                wide.as_image().as_ref().get(6).copied(),
                second_table(&wide, &close)
            ),
            (Some(9), Some(SmallVec::<u8, 0, Global>::from_iter([1; 10]))),
            "a later key that shares the first word widens the earlier segment's table too"
        );
        let leading = declarations.get(.. 2).expect("two leading declarations");
        let super::Maybe::Present(prefix) =
            super::encode_prefix(&arena, leading, &super::Names::new([key(1, 1), key(2, 2)]))
        else {
            panic!("the leading declarations encode");
        };
        assert_eq!(
            super::encode_after(
                &prefix,
                &arena,
                declarations.get(2 ..).expect("a declaration after"),
                &close
            ),
            wide,
            "an encoding resumed under wider names writes the prefix's tables at their width"
        );
        assert_eq!(
            crate::decode_named(narrow.as_image(), &close).err(),
            Some(crate::DecodeError::Malformed {
                site: crate::MalformedSite::SharedPrefix,
            }),
            "an entry that begins two names is refused"
        );
        assert_eq!(
            crate::decode_named(
                narrow.as_image(),
                &super::Names::new([key(1, 1), key(4, 4), key(3, 3)])
            )
            .err(),
            Some(crate::DecodeError::Malformed {
                site: crate::MalformedSite::UnplacedName,
            }),
            "an entry that begins no name is refused"
        );
    }

    /// A named atom stands in the header's atom table by its key. An axiom
    /// inserted before it leaves that table and the atom's segment byte for
    /// byte, its seal included. Bare, the atom's place moves with the
    /// insertion, so the test can fail. Each artifact decodes to its atoms.
    #[test]
    fn a_named_atom_keeps_its_table_past_an_insertion_7340()
    {
        let atom = |arena: &mut TermArena| {
            let mut builder = DeclarationBuilder::new(arena);
            let kind = builder
                .arena()
                .value_type_universe(GroundSort::Value, Level::zero());
            let integer = builder.arena().value_type_base(BaseType::Integer);
            MarkedDeclaration::new(
                AdmissionMark::Checked,
                builder.abstract_type(
                    LevelSignature::monomorphic(),
                    kind,
                    integer,
                    super::SealScope::Closed(super::SealExtent::from(1_usize)),
                ),
            )
        };
        let member = |arena: &mut TermArena| {
            let mut builder = DeclarationBuilder::new(arena);
            let declared = builder.arena().value_type_unit();
            let body = builder.arena().value_unit();
            MarkedDeclaration::new(
                AdmissionMark::Checked,
                builder.def(LevelSignature::monomorphic(), declared, body),
            )
        };
        // The inserted axiom shares no node with the atom or its member, so
        // neither of them imports from it.
        let inserted = |arena: &mut TermArena| {
            let mut builder = DeclarationBuilder::new(arena);
            let declared = builder.arena().value_type_base(BaseType::String);
            MarkedDeclaration::new(
                AdmissionMark::Checked,
                builder.axiom(LevelSignature::monomorphic(), declared),
            )
        };
        let key = |byte: u8| super::ConstantKey::from([byte; super::CONSTANT_KEY_LEN]);
        let mut arena = TermArena::new();
        let short = [atom(&mut arena), member(&mut arena)];
        let long = [inserted(&mut arena), atom(&mut arena), member(&mut arena)];
        let short_names = super::Names::new([Some(key(1)), Some(key(2))]);
        let long_names = super::Names::new([Some(key(9)), Some(key(1)), Some(key(2))]);
        // The atom table follows the magic, the version and the width.
        let table_at = crate::tags::MAGIC.len().saturating_add(3);
        let header = |image: &super::EncodedArtifact, length: usize| {
            image
                .as_image()
                .as_ref()
                .get(table_at .. table_at.saturating_add(length))
                .expect("the atom table")
                .iter()
                .copied()
                .collect::<SmallVec<_, 0, Global>>()
        };
        // One atom, a table of its key cut to one word, then the atom as twice
        // its entry in that table.
        let mut keyed = SmallVec::<_, 0, Global>::from_iter([1_u8, 1]);
        keyed.extend_from_slice(&[1_u8; 8]);
        keyed.push(0);
        let short_named = super::encode_named(&arena, &short, None, &short_names);
        let long_named = super::encode_named(&arena, &long, None, &long_names);
        assert_eq!(
            (header(&short_named, 11), header(&long_named, 11)),
            (keyed.clone(), keyed),
            "an insertion before a named atom leaves its entry in the atom table"
        );
        let segment = |image: &super::EncodedArtifact, names: &super::Names, at: usize| {
            let decoded = crate::decode_named(image.as_image(), names).expect("the bytes decode");
            let span = decoded
                .segments()
                .declaration_segments()
                .nth(at)
                .expect("the atom's segment");
            let bytes = image
                .as_image()
                .as_ref()
                .get(usize::from(span.start) .. usize::from(span.end))
                .expect("the segment's bytes")
                .iter()
                .copied()
                .collect::<SmallVec<_, 0, Global>>();
            (super::minted_atoms(decoded.declarations()), bytes)
        };
        let (short_atoms, short_segment) = segment(&short_named, &short_names, 0);
        let (long_atoms, long_segment) = segment(&long_named, &long_names, 1);
        assert_eq!(
            short_segment, long_segment,
            "the atom's segment, its seal's extent included, keeps its bytes"
        );
        assert_eq!(
            (short_atoms, long_atoms),
            (super::minted_atoms(&short), super::minted_atoms(&long)),
            "each artifact decodes to its atoms"
        );
        // Bare, the table is empty and the atom is its place p as 2p + 1.
        assert_eq!(
            (
                header(&super::encode(&arena, &short), 3),
                header(&super::encode(&arena, &long), 3)
            ),
            (
                SmallVec::<_, 0, Global>::from_iter([1_u8, 0, 1]),
                SmallVec::<_, 0, Global>::from_iter([1_u8, 0, 3])
            ),
            "bare, the atom's place moves with the insertion"
        );
    }

    #[test]
    fn a_segment_reads_an_earlier_entry_by_its_import_7340()
    {
        // Two axioms declare the pair of units, each over its own nodes. The
        // second's pair has the content of the first's, so its segment
        // imports that entry and writes no entry of its own.
        let mut arena = TermArena::new();
        let pair_axiom = |arena: &mut TermArena| {
            let unit = arena.value_type_unit();
            let declared = arena.value_type_product(&[unit, unit]);
            MarkedDeclaration::new(
                AdmissionMark::Checked,
                DeclarationBuilder::new(arena).axiom(LevelSignature::monomorphic(), declared),
            )
        };
        let declarations = [pair_axiom(&mut arena), pair_axiom(&mut arena)];
        let bytes = SmallVec::<u8, 0, Global>::from(super::encode(&arena, &declarations));
        let decoded = crate::decode::decode(ArtifactImage::from(bytes.as_slice()))
            .expect("the two axioms decode");
        let declared: SmallVec<_, 0, Global> = decoded
            .declarations()
            .iter()
            .map(|marked| marked.declaration().declared_id())
            .collect();
        assert_eq!(
            declared.first(),
            declared.get(1),
            "the second segment reads the first one's pair, so both declare one node"
        );
        let second = decoded
            .segments()
            .declaration_segments()
            .nth(1)
            .map(|span| usize::from(span.start))
            .expect("a second segment");
        // An empty table, one import, the first segment's place 0 written
        // bare as 2 * 0 + 1, and the pair's offset 1 after the unit.
        assert_eq!(
            bytes.get(second .. second.saturating_add(4)),
            Some([0_u8, 1, 1, 1].as_slice()),
            "the second segment imports the pair at its offset in the first"
        );
        let refused = |at: usize, byte: u8| {
            let mut forged = bytes.clone();
            if let Some(slot) = forged.get_mut(second.saturating_add(at)) {
                *slot = byte;
            }
            crate::decode::decode(ArtifactImage::from(forged.as_slice())).err()
        };
        let import = Some(crate::DecodeError::Malformed {
            site: crate::MalformedSite::Import,
        });
        assert_eq!(
            refused(3, 2),
            import,
            "an offset past the first segment's two entries is refused"
        );
        assert_eq!(
            refused(2, 3),
            import,
            "the place of the segment itself names no earlier segment"
        );
    }
}
