//! A plane's index on disk: a persistent hash-array trie from an identity to
//! the place of its record, whose root alone the open reads.
//!
//! Each level reads the next four bits of the identity, so an inner page has
//! at most sixteen children. A node is a leaf while it holds at most [`LEAF`]
//! entries, and a node over more is an inner page. So the shape is a function
//! of the set the trie holds, and two equal sets give equal pages. A page's
//! name is the digest of its bytes with each child's place left out, so the
//! name is a function of the set too. A child reference holds the child's
//! place beside its name, so a load reads each page by one positioned read
//! and needs no other index.
//!
//! A fold writes the pages on the path of each changed entry, and shares
//! every other page with the root before it. No page is ever rewritten in
//! place.
//!
//! # References
//!
//! - `vault:01a1d8c5-08cb-7e12-a5d5-9a2ad3279160` — anchor: the IO layer (§
//!   io-layer-extents): the index is a value of the root, from a digest to its
//!   place, in a few columns of fixed width.

use quenchant_shape::shape::Maybe;

use super::Image;
use super::Length;
use super::Offset;
use super::SegmentId;
use super::unheld;
use crate::store::StoreError;

/// The most entries a leaf holds: with the page's head, 78 entries of
/// [`SLOT`] bytes fill one page of 4 KiB.
const LEAF: usize = 78_usize;

/// The bytes of a page's head: its kind, a zero byte, then two little-endian
/// bytes of a leaf's count or of an inner page's map of children.
const HEAD: usize = 4_usize;

/// The bytes of one leaf entry or one inner child: 32 bytes of an identity or
/// of a page's name, then the place: the segment and the offset as eight
/// little-endian bytes each, and the length as four.
const SLOT: usize = 52_usize;

/// The children of an inner page: one for each value of four bits.
const FAN: usize = 16_usize;

/// The deepest level: 64 levels of four bits read the whole identity.
const DEEPEST: Depth = Depth(64_usize);

/// The kind byte of a leaf.
const LEAF_KIND: u8 = 1_u8;

/// The kind byte of an inner page.
const INNER_KIND: u8 = 2_u8;

/// The domain a page's name is taken in, so it meets no other digest of the
/// store.
const PAGE_DOMAIN: &[u8] = b"gandr storage-store index page\0";

/// An identity the trie maps, as its 32 bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Key(pub [u8; 32]);

/// Where a record or a page stands: its segment, its offset there and the
/// length of its bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Placed
{
    /// The segment.
    pub segment: SegmentId,
    /// The offset of the header.
    pub offset: Offset,
    /// The length of the bytes after the header.
    pub length: Length,
}

/// A page's name: the digest of its bytes with each child's place left out.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct PageName(pub [u8; 32]);

/// A reference to a page: its name and its place.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PageRef
{
    /// The page's name.
    pub name: PageName,
    /// The page's place.
    pub at: Placed,
}

/// How many levels of four bits lie above a node.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Depth(usize);

impl Depth
{
    /// The level below this one.
    ///
    /// # Specification
    /// trivial.
    const fn below(self) -> Self
    {
        Self(self.0.saturating_add(1_usize))
    }
}

/// Which child of an inner page a key falls under: four bits of the key.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Nibble(usize);

/// The map of an inner page's children: bit `n` stands for child `n`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Children(u16);

/// A child's place among the slots of its inner page.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Rank(usize);

impl Children
{
    /// The rank of the child `nibble` among the page's slots: how many
    /// children stand before it; none when the child does not stand.
    ///
    /// # Specification
    /// trivial.
    fn rank(
        self,
        nibble: Nibble,
    ) -> Option<Rank>
    {
        let bit = u32::try_from(nibble.0)
            .ok()
            .and_then(|shift| 1_u16.checked_shl(shift))?;
        if self.0 & bit == 0 {
            return None;
        }
        usize::try_from((self.0 & bit.saturating_sub(1_u16)).count_ones())
            .ok()
            .map(Rank)
    }
}

/// A page as its bytes read: a leaf's entries in the order of their keys, or
/// an inner page's map of children and their references in that order.
#[derive(Clone, Copy, Debug)]
pub(super) enum Node<'page>
{
    /// A leaf.
    Leaf(&'page [[u8; SLOT]]),
    /// An inner page.
    Inner(Children, &'page [[u8; SLOT]]),
}

/// The pages a trie reads: each by its reference, its name checked.
pub(super) trait Pages
{
    /// The page `at` refers to, read once and checked by its name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the node the page's bytes spell, when the bytes hash to the
    ///   name `at` gives.
    /// - provides: each read of a page by the trie.
    /// - fails: [`StoreError::Io`] when the page cannot be read, or its bytes
    ///   do not check against its name or spell no page.
    /// - panics: none.
    /// - executable: none — the page's bytes are the implementor's store.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a plane opened from its index loads each record
    ///   through the pages on its path.
    /// - witness: `plane::tests::a_plane_opens_from_its_index_and_reads_no_trailer`
    fn node(
        &self,
        at: PageRef,
    ) -> Result<Node<'_>, StoreError>;
}

/// Where a fold writes its pages: each page placed after the one before.
pub(super) trait Sink
{
    /// Place `page` under `name`, and give its reference.
    ///
    /// # Specification
    /// - requires: `name` is the name of `page`.
    /// - ensures: the reference of the page at its place, after each page
    ///   placed before it.
    /// - provides: each write of a page by a fold.
    /// - fails: [`StoreError::Oversized`] for a page of 4 GiB or more, which no
    ///   page is.
    /// - panics: none.
    /// - executable: none — the place is the implementor's store.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a trie folded in batches names the root of one fold,
    ///   and finds each entry at the place its page holds.
    /// - witness: `plane::index::tests::a_trie_folded_in_batches_names_the_root_of_one_fold`
    fn put(
        &mut self,
        page: Image<'_>,
        name: PageName,
    ) -> Result<PageRef, StoreError>;
}

/// The name of `page`: the digest of its head and of each slot's first 32
/// bytes for an inner page, and of all its bytes for a leaf.
///
/// # Specification
/// trivial.
pub(super) fn named(page: Image<'_>) -> PageName
{
    let mut hasher = blake3::Hasher::new();
    let _domain = hasher.update(PAGE_DOMAIN);
    match page.0.split_first_chunk::<HEAD>() {
        Some((head @ &[INNER_KIND, ..], slots)) => {
            let _head = hasher.update(head);
            for slot in slots.as_chunks::<SLOT>().0 {
                let _name = hasher.update(slot.first_chunk::<32>().map_or(&[][..], |name| name));
            }
        },
        Some(_) | None => {
            let _page = hasher.update(page.0);
        },
    }
    PageName(*hasher.finalize().as_bytes())
}

/// The node `page` spells, or `Unreadable` for bytes that spell none.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a leaf whose head counts its whole slots and at most [`LEAF`] of
///   them, or an inner page whose map counts its whole slots; `Unreadable` for
///   any other bytes.
/// - provides: the one decode every read of a page makes.
/// - fails: never; bytes that spell no page are the typed absence.
/// - panics: none.
/// - executable: none — a pure function of the bytes, which the trie's tests
///   read.
///
/// # Adequacy
/// - hypothesis: L3 — a trie folded in batches finds each entry.
/// - witness: `plane::index::tests::a_trie_folded_in_batches_names_the_root_of_one_fold`
pub(super) fn node(page: Image<'_>) -> Maybe<Node<'_>, unheld::Absent>
{
    let unreadable = Maybe::Absent(unheld::Absent::Unreadable);
    let Some((&[kind, 0_u8, low, high], rest)) = page.0.split_first_chunk::<HEAD>()
    else {
        return unreadable;
    };
    let (slots, torn) = rest.as_chunks::<SLOT>();
    let count = u16::from_le_bytes([low, high]);
    if !torn.is_empty() {
        return unreadable;
    }
    match kind {
        LEAF_KIND if usize::from(count) == slots.len() && slots.len() <= LEAF => {
            Maybe::Present(Node::Leaf(slots))
        },
        INNER_KIND if usize::try_from(count.count_ones()).is_ok_and(|held| held == slots.len()) => {
            Maybe::Present(Node::Inner(Children(count), slots))
        },
        _ => unreadable,
    }
}

/// The four bits of `key` that the level `depth` reads, the high half of a
/// byte first.
///
/// # Specification
/// trivial.
fn nibble(
    key: &Key,
    depth: Depth,
) -> Nibble
{
    let byte = key.0.get(depth.0 >> 1_u32).copied().unwrap_or(0_u8);
    Nibble(usize::from(if depth.0 & 1_usize == 0_usize {
        byte >> 4_u32
    }
    else {
        byte & 0x0f_u8
    }))
}

/// The bytes of one slot of a page.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct SlotBytes<'page>(&'page [u8; SLOT]);

/// The bytes of a page as a fold builds it.
#[repr(transparent)]
#[derive(Debug, Default)]
struct PageBytes(Vec<u8>);

/// The first 32 bytes of a slot and the place after them.
///
/// # Specification
/// trivial.
fn slot(bytes: SlotBytes<'_>) -> (Key, Placed)
{
    let (name, rest) = bytes
        .0
        .split_first_chunk::<32>()
        .map_or(([0_u8; 32], &[][..]), |(name, rest)| (*name, rest));
    let (segment, rest) = rest
        .split_first_chunk::<8>()
        .map_or(([0_u8; 8], &[][..]), |(segment, rest)| (*segment, rest));
    let (offset, rest) = rest
        .split_first_chunk::<8>()
        .map_or(([0_u8; 8], &[][..]), |(offset, rest)| (*offset, rest));
    let length = rest.first_chunk::<4>().copied().unwrap_or([0_u8; 4]);
    (Key(name), Placed {
        segment: SegmentId(u64::from_le_bytes(segment)),
        offset: Offset(u64::from_le_bytes(offset)),
        length: Length(u32::from_le_bytes(length)),
    })
}

/// Append a slot of `name` at `placed` to `page`.
///
/// # Specification
/// trivial.
fn push_slot(
    page: &mut PageBytes,
    name: Key,
    placed: Placed,
)
{
    page.0.extend_from_slice(&name.0);
    page.0.extend_from_slice(&placed.segment.0.to_le_bytes());
    page.0.extend_from_slice(&placed.offset.0.to_le_bytes());
    page.0.extend_from_slice(&placed.length.0.to_le_bytes());
}

/// The place `key` maps to in the trie whose root is `root`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the place of `key` when the trie holds it; `Unlisted` when it
///   does not.
/// - provides: the load of an identity that the plane's memory does not hold.
/// - fails: the fault of [`Pages::node`] for a page on the path.
/// - panics: none.
/// - executable: none — the pages are the plane's.
/// - intension: one read of each page on the path that no load read before, at
///   most one for each level.
///
/// # Errors
/// As [`Pages::node`].
///
/// # Adequacy
/// - hypothesis: L3 — a trie folded in batches finds each entry, and a store
///   reopened from its index loads each object.
/// - witness: `plane::index::tests::a_trie_folded_in_batches_names_the_root_of_one_fold`
/// - witness: `tests::store::a_store_opens_from_its_index_and_reads_no_trailer_7531`
pub(super) fn find<P>(
    pages: &P,
    root: PageRef,
    key: Key,
) -> Result<Maybe<Placed, unheld::Absent>, StoreError>
where
    P: Pages,
{
    let unlisted = Ok(Maybe::Absent(unheld::Absent::Unlisted));
    let mut at = root;
    let mut depth = Depth(0_usize);
    loop {
        match pages.node(at)? {
            Node::Leaf(slots) => {
                return Ok(slots
                    .binary_search_by(|each| slot(SlotBytes(each)).0.cmp(&key))
                    .ok()
                    .and_then(|found| slots.get(found))
                    .map_or(Maybe::Absent(unheld::Absent::Unlisted), |each| {
                        Maybe::Present(slot(SlotBytes(each)).1)
                    }));
            },
            Node::Inner(children, slots) => {
                let below = nibble(&key, depth);
                let Some(child) = children.rank(below).and_then(|rank| slots.get(rank.0))
                else {
                    return unlisted;
                };
                let (name, placed) = slot(SlotBytes(child));
                at = PageRef {
                    name: PageName(name.0),
                    at: placed,
                };
                depth = depth.below();
            },
        }
    }
}

/// Fold `entries` into the trie whose root is `root`, writing each new page
/// to `sink`, and give the new root.
///
/// # Specification
/// - requires: `root`, when given, is a trie of `pages`.
/// - ensures: on success the root of the trie that maps each key of `root` and
///   of `entries`, an entry's place taking over the root's for one key, and the
///   latest of two entries of one key taking over; `root` itself when `entries`
///   is empty. The new root's name is the name a fold of the whole set into no
///   root gives.
/// - provides: the step of each fold that names the plane's index.
/// - fails: the fault of [`Pages::node`] or of [`Sink::put`].
/// - panics: none.
/// - executable: none — the pages are the plane's.
/// - intension: one page written for each node on the path of a changed entry;
///   every other page shared with `root`.
///
/// # Errors
/// As [`Pages::node`] and [`Sink::put`].
///
/// # Adequacy
/// - hypothesis: L3 — a trie folded in batches names the root of one fold, and
///   a store reopened from its index loads each object.
/// - witness: `plane::index::tests::a_trie_folded_in_batches_names_the_root_of_one_fold`
/// - witness: `tests::store::a_store_opens_from_its_index_and_reads_no_trailer_7531`
pub(super) fn fold<P, S>(
    pages: &P,
    sink: &mut S,
    root: Option<PageRef>,
    entries: &mut Vec<(Key, Placed)>,
) -> Result<Option<PageRef>, StoreError>
where
    P: Pages,
    S: Sink,
{
    // A stable sort of the reversed list puts the latest entry of each key
    // first, and the dedup keeps it.
    entries.reverse();
    entries.sort_by_key(|&(key, _placed)| key);
    entries.dedup_by_key(|&mut (key, _placed)| key);
    if entries.is_empty() {
        return Ok(root);
    }
    let whole = Span {
        start: 0_usize,
        end: entries.len(),
    };
    // The walk keeps one frame for each node on the path it writes. A frame
    // writes its page once each run below it has written its own, so the
    // pages go out children first, as a parent's slots need their places.
    let mut path = vec![Frame::at(root, Depth(0_usize), whole)];
    loop {
        let Some(frame) = path.last_mut()
        else {
            return Ok(root);
        };
        let written = if frame.opened {
            match frame.runs.get(frame.next).copied() {
                Some(run) => {
                    let below = frame.children.get(run.nibble.0).copied().flatten();
                    let depth = frame.depth.below();
                    path.push(Frame::at(below, depth, run.span));
                    continue;
                },
                None => inner(sink, &frame.children)?,
            }
        }
        else {
            frame.opened = true;
            match opened(pages, sink, frame, entries)? {
                Some(written) => written,
                None => continue,
            }
        };
        let _done = path.pop();
        let Some(parent) = path.last_mut()
        else {
            return Ok(Some(written));
        };
        if let Some(child) = parent
            .runs
            .get(parent.next)
            .and_then(|run| parent.children.get_mut(run.nibble.0))
        {
            *child = Some(written);
        }
        parent.next = parent.next.saturating_add(1_usize);
    }
}

/// A run of the fold's entries: the entries from `start` up to `end`.
#[derive(Clone, Copy, Debug)]
struct Span
{
    /// The first entry.
    start: usize,
    /// The entry past the last.
    end: usize,
}

/// The entries of one child of a node: the four bits they share at the
/// node's level, and where they stand.
#[derive(Clone, Copy, Debug)]
struct Run
{
    /// The child.
    nibble: Nibble,
    /// The entries.
    span: Span,
}

/// One node on the path that a fold writes.
#[derive(Debug)]
struct Frame
{
    /// The node's page before the fold, or none for a new node.
    at: Option<PageRef>,
    /// The node's level.
    depth: Depth,
    /// The entries the fold puts under the node.
    span: Span,
    /// Whether the fold has read the node's page and split its entries.
    opened: bool,
    /// The node's children, as the fold leaves them so far.
    children: [Option<PageRef>; FAN],
    /// The runs of entries, one for each child that changes.
    runs: Vec<Run>,
    /// The run the fold writes next.
    next: usize,
}

impl Frame
{
    /// The frame of the node `at` at `depth`, with the entries of `span`.
    ///
    /// # Specification
    /// trivial.
    const fn at(
        at: Option<PageRef>,
        depth: Depth,
        span: Span,
    ) -> Self
    {
        Self {
            at,
            depth,
            span,
            opened: false,
            children: [None; FAN],
            runs: Vec::new(),
            next: 0_usize,
        }
    }
}

/// Open `frame`: read its page, and write it at once as a leaf when its
/// entries fit one, else split its entries into runs, one for each child.
///
/// # Specification
/// - requires: the entries of `frame.span` stand in `entries` in the order of
///   their keys, one for each key, and share the bits above `frame.depth`.
/// - ensures: on success the leaf's reference when the node is a leaf after the
///   fold, its page written; none otherwise, with the frame's children read
///   from its page and its runs split. A leaf before the fold merges its
///   entries with the frame's, the frame's taking over each key, and the merged
///   entries go to the end of `entries`.
/// - provides: the step of [`fold`] that reads a node.
/// - fails: the fault of [`Pages::node`] or of [`Sink::put`].
/// - panics: none.
/// - executable: none — the pages are the plane's.
///
/// # Errors
/// As [`Pages::node`] and [`Sink::put`].
///
/// # Adequacy
/// - hypothesis: L3 — a trie folded in batches names the root of one fold.
/// - witness: `plane::index::tests::a_trie_folded_in_batches_names_the_root_of_one_fold`
fn opened<P, S>(
    pages: &P,
    sink: &mut S,
    frame: &mut Frame,
    entries: &mut Vec<(Key, Placed)>,
) -> Result<Option<PageRef>, StoreError>
where
    P: Pages,
    S: Sink,
{
    let span = frame.span;
    match frame.at.map(|at| pages.node(at)).transpose()? {
        Some(Node::Inner(held, slots)) => {
            let mut standing = slots.iter();
            for (at, child) in frame.children.iter_mut().enumerate() {
                if held.rank(Nibble(at)).is_some() {
                    *child = standing.next().map(|each| {
                        let (name, placed) = slot(SlotBytes(each));
                        PageRef {
                            name: PageName(name.0),
                            at: placed,
                        }
                    });
                }
            }
            frame.runs = runs(entries, span, frame.depth);
            return Ok(None);
        },
        Some(Node::Leaf(slots)) => {
            let new = entries.get(span.start .. span.end).unwrap_or_default();
            let mut all: Vec<(Key, Placed)> =
                Vec::with_capacity(slots.len().saturating_add(new.len()));
            let mut fresh = new.iter().copied().peekable();
            for each in slots {
                let (key, placed) = slot(SlotBytes(each));
                while let Some(&(next, _placed)) = fresh.peek()
                    && next < key
                {
                    all.extend(fresh.next());
                }
                if fresh.peek().is_some_and(|&(next, _placed)| next == key) {
                    continue;
                }
                all.push((key, placed));
            }
            all.extend(fresh);
            frame.span = Span {
                start: entries.len(),
                end: entries.len().saturating_add(all.len()),
            };
            entries.extend(all);
        },
        None => {},
    }
    let own = entries
        .get(frame.span.start .. frame.span.end)
        .unwrap_or_default();
    if own.len() <= LEAF || frame.depth >= DEEPEST {
        return leaf(sink, own).map(Some);
    }
    frame.runs = runs(entries, frame.span, frame.depth);
    Ok(None)
}

/// The runs of the entries of `span` in `entries`, by the four bits that
/// `depth` reads.
///
/// # Specification
/// trivial.
fn runs(
    entries: &[(Key, Placed)],
    span: Span,
    depth: Depth,
) -> Vec<Run>
{
    let mut runs = Vec::new();
    let mut at = span.start;
    let own = entries.get(span.start .. span.end).unwrap_or_default();
    for run in own.chunk_by(|left, right| nibble(&left.0, depth) == nibble(&right.0, depth)) {
        let end = at.saturating_add(run.len());
        if let Some(&(key, _placed)) = run.first() {
            runs.push(Run {
                nibble: nibble(&key, depth),
                span: Span { start: at, end },
            });
        }
        at = end;
    }
    runs
}

/// The leaf that maps `entries`, written to `sink`.
///
/// # Specification
/// trivial.
fn leaf<S>(
    sink: &mut S,
    entries: &[(Key, Placed)],
) -> Result<PageRef, StoreError>
where
    S: Sink,
{
    let count = u16::try_from(entries.len()).unwrap_or(u16::MAX);
    let mut page = PageBytes(Vec::with_capacity(
        HEAD.saturating_add(entries.len().saturating_mul(SLOT)),
    ));
    page.0.extend_from_slice(&[LEAF_KIND, 0_u8]);
    page.0.extend_from_slice(&count.to_le_bytes());
    for &(key, placed) in entries {
        push_slot(&mut page, key, placed);
    }
    let name = named(Image(&page.0));
    sink.put(Image(&page.0), name)
}

/// The inner page over `children`, written to `sink`.
///
/// # Specification
/// trivial.
fn inner<S>(
    sink: &mut S,
    children: &[Option<PageRef>; FAN],
) -> Result<PageRef, StoreError>
where
    S: Sink,
{
    let mut map = 0_u16;
    let mut page = PageBytes(Vec::with_capacity(
        HEAD.saturating_add(FAN.saturating_mul(SLOT)),
    ));
    page.0.extend_from_slice(&[INNER_KIND, 0_u8, 0_u8, 0_u8]);
    for (at, child) in children.iter().copied().enumerate() {
        if let Some(child) = child {
            map |= u32::try_from(at)
                .ok()
                .and_then(|shift| 1_u16.checked_shl(shift))
                .unwrap_or(0_u16);
            push_slot(&mut page, Key(child.name.0), child.at);
        }
    }
    if let Some(head) = page.0.get_mut(2_usize .. HEAD) {
        head.copy_from_slice(&map.to_le_bytes());
    }
    let name = named(Image(&page.0));
    sink.put(Image(&page.0), name)
}

#[cfg(test)]
mod tests
{
    use core::sync::atomic::AtomicUsize;
    use core::sync::atomic::Ordering;

    use quenchant_shape::shape::Maybe;

    use super::Image;
    use super::Key;
    use super::Length;
    use super::Node;
    use super::Offset;
    use super::PageName;
    use super::PageRef;
    use super::Pages;
    use super::Placed;
    use super::SegmentId;
    use super::Sink;
    use super::find;
    use super::fold;
    use super::named;
    use super::node;
    use crate::store::StoreError;

    /// Pages held in memory, each at the offset of its slot.
    #[derive(Default)]
    struct Held
    {
        /// Each page's bytes, at a fixed slot.
        pages: boxcar::Vec<Box<[u8]>>,
        /// How many pages a fold wrote.
        written: AtomicUsize,
    }

    impl Held
    {
        /// How many pages the folds wrote so far.
        ///
        /// # Specification
        /// trivial.
        fn written(&self) -> Count
        {
            Count(self.written.load(Ordering::Relaxed))
        }
    }

    /// A count of pages.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    struct Count(usize);

    impl Pages for Held
    {
        /// The page in the slot that `at` names, checked by its name.
        ///
        /// # Specification
        /// trivial.
        fn node(
            &self,
            at: PageRef,
        ) -> Result<Node<'_>, StoreError>
        {
            let page = usize::try_from(at.at.offset.0)
                .ok()
                .and_then(|slot| self.pages.get(slot))
                .map_or(&[][..], |page| page);
            assert_eq!(named(Image(page)), at.name, "a page checks by its name");
            match node(Image(page)) {
                Maybe::Present(read) => Ok(read),
                Maybe::Absent(_) => Err(StoreError::Unowned),
            }
        }
    }

    impl Sink for &Held
    {
        /// Push `page` into the next slot.
        ///
        /// # Specification
        /// trivial.
        fn put(
            &mut self,
            page: Image<'_>,
            name: PageName,
        ) -> Result<PageRef, StoreError>
        {
            let slot = self.pages.push(Box::from(page.0));
            let _written = self.written.fetch_add(1_usize, Ordering::Relaxed);
            Ok(PageRef {
                name,
                at: Placed {
                    segment: SegmentId(0_u64),
                    offset: Offset(u64::try_from(slot).unwrap_or(u64::MAX)),
                    length: Length(u32::try_from(page.0.len()).unwrap_or(u32::MAX)),
                },
            })
        }
    }

    /// The `count` entries from `first` on, each a digest of its index.
    ///
    /// # Specification
    /// trivial.
    fn entries(
        first: Number,
        count: Number,
    ) -> Vec<(Key, Placed)>
    {
        (first.0 .. first.0.saturating_add(count.0))
            .map(|at| {
                (Key(*blake3::hash(&at.to_le_bytes()).as_bytes()), Placed {
                    segment: SegmentId(1_u64),
                    offset: Offset(at),
                    length: Length(64_u32),
                })
            })
            .collect()
    }

    /// A number of entries, or the first of them.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Number(u64);

    /// Three folds of 4,000, 64 and 64 entries name the root that one fold of
    /// all 4,128 names, find every entry, and write fewer pages than the
    /// whole for each small fold.
    #[test]
    fn a_trie_folded_in_batches_names_the_root_of_one_fold()
    {
        let batches = Held::default();
        let mut root = None;
        let mut writes = Vec::new();
        for (first, count) in [(0_u64, 4_000_u64), (4_000, 64), (4_064, 64)] {
            let before = batches.written();
            let mut batch = entries(Number(first), Number(count));
            root =
                fold(&batches, &mut &batches, root, &mut batch).expect("a fold in memory writes");
            writes.push(batches.written().0.saturating_sub(before.0));
        }
        let whole = Held::default();
        let all = entries(Number(0), Number(4_128));
        let once =
            fold(&whole, &mut &whole, None, &mut all.clone()).expect("a fold in memory writes");
        let (Some(root), Some(once)) = (root, once)
        else {
            panic!("a fold of entries names a root");
        };
        assert_eq!(root.name, once.name, "one set has one shape and one name");
        let pages = whole.written().0;
        assert!(
            writes.iter().skip(1).all(|&small| small < pages),
            "a small fold writes {writes:?} pages, the whole trie has {pages}"
        );
        for (key, placed) in all {
            assert_eq!(
                find(&batches, root, key).expect("a page in memory reads"),
                Maybe::Present(placed),
                "the trie finds each entry"
            );
        }
        let absent = Key(*blake3::hash(b"absent").as_bytes());
        assert_eq!(
            find(&batches, root, absent).expect("a page in memory reads"),
            Maybe::Absent(super::unheld::Absent::Unlisted),
            "the trie finds no entry it was not given"
        );
    }
}
