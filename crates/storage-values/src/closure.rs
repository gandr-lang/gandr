//! The closure walk: every chunk a reader of a pointer loads, and the records
//! it delivers.
//!
//! # The closure
//!
//! A pointer's closure is the chunk it names and, for every child record
//! inside the subtree it addresses, the closure of that child. Records of the
//! same chunk outside the addressed subtree are never followed, because a
//! reader never reaches them. For a root pointer [`crate::cam_commit`]
//! returned, the subtree is the root chunk's whole body, so the closure is
//! every chunk the commit cut.
//!
//! # The spliced token total
//!
//! A reader replaces each child record with the subtree it names. The records
//! it delivers are therefore the subtree's own records other than child
//! records, plus each child's delivered records, once per reference. A
//! manifest's token count states that total.
//!
//! # Each subtree once
//!
//! A chunk DAG can reference one subtree from many places, and a reader pays
//! for every reference. The walk counts each distinct subtree — a digest and
//! an offset — once and adds its total at each reference, so its work follows
//! the distinct subtrees rather than the paths through them. That work is
//! charged to the decode budget: a unit per record scanned and a unit per
//! image byte loaded.
//!
//! # No recursion
//!
//! Suspended subtrees live in a vector, so the depth of a DAG is bounded by
//! the decode budget rather than by the host stack. A cycle would need a chunk
//! holding its own digest; the budget would end even that walk.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::mem;

use anodized::spec;
use gandr_storage_chunker::TokenCount;

use crate::chunk::ChunkStore;
use crate::error::ValueError;
use crate::error::ValueQuantity;
use crate::ptr::ChunkDigest;
use crate::ptr::ContentPtr;
use crate::ptr::TokenOffset;
use crate::reader::charge;
use crate::tokens::BodyFront;
use crate::tokens::Record;
use crate::tokens::RecordFault;
use crate::tokens::TokenKind;
use crate::tokens::split_record;
use crate::units::ChunkCount;
use crate::units::DecodeWork;
use crate::units::MAX_DECODE_WORK;
use crate::units::TokenBody;

/// The chunks a reader of a value loads.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValueClosure(BTreeSet<ChunkDigest>);

impl ValueClosure
{
    /// Returns the digest of every chunk in the closure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn digests(&self) -> &BTreeSet<ChunkDigest>
    {
        &self.0
    }

    /// Returns the number of distinct chunks in the closure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn chunk_count(&self) -> ChunkCount
    {
        ChunkCount::from(self.0.len())
    }
}

impl From<ValueClosure> for BTreeSet<ChunkDigest>
{
    /// Takes the closure's digests.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(closure: ValueClosure) -> Self
    {
        closure.0
    }
}

/// What a walk from one pointer found: its closure, and the records a reader
/// of the pointer delivers.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Walked
{
    /// The chunks loaded.
    closure: ValueClosure,
    /// The records a reader of the pointer delivers, child chunks spliced.
    token_count: TokenCount,
}

impl Walked
{
    /// Returns the records a reader of the pointer delivers.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn token_count(&self) -> TokenCount
    {
        self.token_count
    }

    /// Borrows the chunks loaded.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn closure(&self) -> &ValueClosure
    {
        &self.closure
    }

    /// Takes the chunks loaded.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn into_closure(self) -> ValueClosure
    {
        self.closure
    }
}

/// How many constructors a scan has opened inside its subtree and not closed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct SubtreeDepth(u64);

impl SubtreeDepth
{
    /// Outside every constructor of the subtree.
    const OUTSIDE: Self = Self(0_u64);
}

/// Whether a scan's subtree has closed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ScanState
{
    /// Records of the subtree remain.
    Reading,
    /// The subtree has closed; nothing after it is read.
    Complete,
}

/// What one step of a scan met.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Scanned
{
    /// A record of the subtree's own, now counted.
    Delivered,
    /// A child record, whose subtree the walk counts in its place.
    Child(ContentPtr),
    /// The subtree has closed.
    Complete,
}

/// One subtree being counted.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Scan<'store>
{
    /// The pointer the subtree is addressed by.
    at: ContentPtr,
    /// The unread records of the chunk's body.
    remaining: TokenBody<'store>,
    /// The record position of the first unread record within the body.
    position: TokenOffset,
    /// Constructors opened inside the subtree and not yet closed.
    depth: SubtreeDepth,
    /// The records the subtree has delivered so far, child subtrees spliced.
    delivered: TokenCount,
    /// Whether the subtree has closed.
    state: ScanState,
}

impl<'store> Scan<'store>
{
    /// Opens a scan at the start of a chunk's body.
    ///
    /// # Specification
    /// trivial.
    const fn at_start(
        at: ContentPtr,
        body: TokenBody<'store>,
    ) -> Self
    {
        Self {
            at,
            remaining: body,
            position: TokenOffset::ZERO,
            depth: SubtreeDepth::OUTSIDE,
            delivered: TokenCount::ZERO,
            state: ScanState::Reading,
        }
    }

    /// Splits the record under the cursor off the unread body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the record under the cursor and the body after it;
    ///   the cursor does not move.
    /// - provides: the one grammar read the scan makes.
    /// - fails: [`ValueError::TruncatedStream`] at the end of the body or
    ///   inside a record, and [`ValueError::UnknownTokenKind`] for an
    ///   unassigned kind, each at the cursor's position.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    fn front(&self) -> Result<(Record<'store>, TokenBody<'store>), ValueError>
    {
        let position = self.position;
        let front = split_record(self.remaining).map_err(|fault| match fault {
            | RecordFault::Truncated => ValueError::TruncatedStream { position },
            | RecordFault::UnknownKind => ValueError::UnknownTokenKind { position },
        });
        let BodyFront::Record(record, rest) = front?
        else {
            return Err(ValueError::TruncatedStream { position });
        };

        Ok((record, rest))
    }

    /// Moves past the record under the cursor, charging one unit of work.
    ///
    /// # Specification
    /// - requires: `rest` is the body after the record under the cursor.
    /// - ensures: on success the cursor is at `rest`, one record further, and
    ///   one more unit is spent.
    /// - provides: the one place a scan moves and charges a record.
    /// - fails: [`ValueError::DecodeBudgetExceeded`] past the decode budget,
    ///   and an overflow refusal at the position's width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[spec(captures: [entry = u64::from(*spent)],
        ensures: |ret| ret.is_err()
            || (u64::from(*spent) == entry.saturating_add(1_u64) && self.remaining == rest))]
    fn advance(
        &mut self,
        rest: TokenBody<'store>,
        spent: &mut DecodeWork,
    ) -> Result<(), ValueError>
    {
        *spent = charge(*spent, DecodeWork::ONE, MAX_DECODE_WORK)?;
        self.position = self.position.next()?;
        self.remaining = rest;

        Ok(())
    }

    /// Skips the records before a pointer's offset without interpreting them.
    ///
    /// # Specification
    /// - requires: the scan is at the start of its body.
    /// - ensures: on success the cursor is `count` records into the body.
    /// - provides: the entry step for a pointer into the interior of a chunk,
    ///   as the reader takes it.
    /// - fails: [`ValueError::TruncatedStream`] when the body holds fewer
    ///   records, and [`Scan::advance`]'s refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[spec(ensures: |ret| ret.is_err() || self.position == count)]
    fn skip(
        &mut self,
        count: TokenOffset,
        spent: &mut DecodeWork,
    ) -> Result<(), ValueError>
    {
        for _record in 0_u32 .. u32::from(count) {
            let (_skipped, rest) = self.front()?;
            self.advance(rest, spent)?;
        }

        Ok(())
    }

    /// Reads one record of the subtree.
    ///
    /// # Specification
    /// - requires: the cursor is at or inside the subtree the scan counts.
    /// - ensures: on success, [`Scanned::Complete`] once the subtree has
    ///   closed, reading nothing; otherwise the record under the cursor is
    ///   consumed — a child record is returned for the walk to count, and any
    ///   other record is counted and tracked, the scan completing at the close
    ///   that ends the subtree.
    /// - provides: the scan's one step.
    /// - fails: [`ValueError::UnexpectedToken`] naming an open as required for
    ///   a payload or a close standing outside every constructor of the
    ///   subtree; [`Scan::front`]'s and [`Scan::advance`]'s refusals; an
    ///   overflow refusal at the depth's or the count's width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    fn step(
        &mut self,
        spent: &mut DecodeWork,
    ) -> Result<Scanned, ValueError>
    {
        if self.state == ScanState::Complete {
            return Ok(Scanned::Complete);
        }

        let position = self.position;
        let (record, rest) = self.front()?;
        self.advance(rest, spent)?;
        let outside = |found: TokenKind| ValueError::UnexpectedToken {
            expected: TokenKind::Open,
            found,
            position,
        };

        match record {
            | Record::Child(pointer) => return Ok(Scanned::Child(pointer)),
            | Record::Open(_tag) => {
                let Some(deeper) = self.depth.0.checked_add(1_u64)
                else {
                    return Err(ValueError::ArithmeticOverflow {
                        quantity: ValueQuantity::TokenCount,
                    });
                };
                self.depth = SubtreeDepth(deeper);
            },
            | Record::Word(_) | Record::Bytes(_) => {
                if self.depth == SubtreeDepth::OUTSIDE {
                    return Err(outside(record.kind()));
                }
            },
            | Record::Close => {
                let Some(shallower) = self.depth.0.checked_sub(1_u64)
                else {
                    return Err(outside(TokenKind::Close));
                };
                self.depth = SubtreeDepth(shallower);
            },
        }
        self.absorb(TokenCount::from(1_u64))?;

        Ok(Scanned::Delivered)
    }

    /// Counts delivered records: one of the subtree's own, or a child
    /// subtree's total in place of its child record.
    ///
    /// # Specification
    /// - requires: the records counted are the subtree's, at the scan's current
    ///   depth.
    /// - ensures: on success `count` more records are delivered, and the scan
    ///   is complete exactly when it stands outside every constructor — after
    ///   the close that ends the subtree, or after a child that stands for the
    ///   whole subtree.
    /// - provides: the accounting both a record and a counted child share.
    /// - fails: [`ValueError::ArithmeticOverflow`] naming the token count.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::ArithmeticOverflow`] — the count passes its width.
    #[spec(ensures: |ret| ret.is_err()
        || ((self.state == ScanState::Complete) == (self.depth == SubtreeDepth::OUTSIDE)))]
    fn absorb(
        &mut self,
        count: TokenCount,
    ) -> Result<(), ValueError>
    {
        self.delivered = add_tokens(self.delivered, count)?;
        if self.depth == SubtreeDepth::OUTSIDE {
            self.state = ScanState::Complete;
        }

        Ok(())
    }
}

/// The walk's state: the store, the chunks loaded, the subtrees counted, and
/// the work spent.
struct Walk<'store, Store>
where
    Store: ChunkStore + ?Sized,
{
    /// Where chunks are loaded from, verified.
    store: &'store Store,
    /// Every chunk loaded.
    digests: BTreeSet<ChunkDigest>,
    /// Every subtree counted, by the pointer that addresses it.
    counted: BTreeMap<ContentPtr, TokenCount>,
    /// The work spent.
    spent: DecodeWork,
}

impl<'store, Store> Walk<'store, Store>
where
    Store: ChunkStore + ?Sized,
{
    /// Loads the chunk a pointer names and opens a scan at its offset.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the chunk is verified and listed, its image length
    ///   charged, and the scan stands at the pointer's offset.
    /// - provides: the one place the walk loads a chunk.
    /// - fails: the store's refusals — [`ValueError::UnknownChunk`] naming the
    ///   digest it does not hold among them — the budget's refusal, and
    ///   [`Scan::skip`]'s.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    #[spec(ensures: |ret| ret.is_err() || self.digests.contains(&pointer.digest()))]
    fn enter(
        &mut self,
        pointer: ContentPtr,
    ) -> Result<Scan<'store>, ValueError>
    {
        let chunk = self.store.load(pointer.digest())?;
        let image_length = u64::try_from(chunk.image().as_ref().len()).unwrap_or(u64::MAX);
        self.spent = charge(self.spent, DecodeWork::from(image_length), MAX_DECODE_WORK)?;
        let _loaded = self.digests.insert(pointer.digest());

        let mut scan = Scan::at_start(pointer, chunk.body());
        scan.skip(pointer.offset(), &mut self.spent)?;

        Ok(scan)
    }
}

/// Walks the closure of the value a pointer addresses.
///
/// # Specification
/// - requires: nothing; every malformed or missing chunk is refused by name.
/// - ensures: on success the closure is every chunk a dereference of `root`
///   loads — the chunk `root` names and, for every child record inside the
///   subtree at its offset, that child's closure — and the token count is the
///   number of records a reader of `root` delivers, each child subtree counted
///   once per reference. Each distinct subtree is scanned once.
/// - provides: the walk a manifest's closure checks, a commit counts an
///   embedded pointer with, and [`crate::measure_edit`] counts over.
/// - fails: [`ValueError::UnknownChunk`] naming the first absent digest in
///   stream order, and the store's other refusals for a chunk it answers
///   wrongly; [`ValueError::TruncatedStream`] when a body ends before its
///   offset or before its subtree closes; [`ValueError::UnexpectedToken`] when
///   a subtree opens with a payload or a close;
///   [`ValueError::DecodeBudgetExceeded`] past [`MAX_DECODE_WORK`]; an overflow
///   refusal at a count's width.
/// - panics: none.
/// - intension: preorder in stream order, each distinct subtree scanned once;
///   observable through which absent digest a refusal names.
///
/// # Errors
/// [`ValueError`] — as listed above.
///
/// # Adequacy
/// - hypothesis: L2 agreement — the closure of every generated value under
///   every generated profile, committed into an empty store, is the set of
///   digests the store holds, and its token count the manifest's — plus L3 for
///   a missing chunk two seams below the root, named exactly, for an interior
///   offset counting only its own subtree, and for each malformed subtree,
///   refused by variant and position.
/// - witness: `tests::closure::the_closure_is_every_chunk_the_commit_wrote`
/// - witness: `tests::closure::a_missing_descendant_fails_the_closure_by_name`
/// - witness: `closure::tests::the_walk_counts_the_addressed_subtree_and_refuses_a_malformed_one`
#[spec(ensures: |ret| ret
    .as_ref()
    .ok()
    .is_none_or(|walked| walked.closure.0.contains(&root.digest())))]
pub(crate) fn walk_closure<Store>(
    store: &Store,
    root: ContentPtr,
) -> Result<Walked, ValueError>
where
    Store: ChunkStore + ?Sized,
{
    let mut walk = Walk {
        store,
        digests: BTreeSet::new(),
        counted: BTreeMap::new(),
        spent: DecodeWork::ZERO,
    };
    let mut current = walk.enter(root)?;
    let mut suspended = Vec::new();

    loop {
        let scanned = current.step(&mut walk.spent)?;
        match scanned {
            | Scanned::Delivered => {},
            | Scanned::Child(pointer) => {
                if let Some(&count) = walk.counted.get(&pointer) {
                    current.absorb(count)?;
                }
                else {
                    let child = walk.enter(pointer)?;
                    suspended.push(mem::replace(&mut current, child));
                }
            },
            | Scanned::Complete => {
                let total = current.delivered;
                let _counted = walk.counted.insert(current.at, total);
                let Some(parent) = suspended.pop()
                else {
                    return Ok(Walked {
                        closure: ValueClosure(walk.digests),
                        token_count: total,
                    });
                };
                current = parent;
                current.absorb(total)?;
            },
        }
    }
}

/// Adds two token counts, refusing a total past the width.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `|ret| ret.is_ok() ==
///   u64::from(count).checked_add(u64::from(more)).is_some()` — the sum exactly
///   when it fits.
/// - provides: the token arithmetic the walk and a commit's count share.
/// - fails: [`ValueError::ArithmeticOverflow`] naming the token count.
/// - panics: none.
///
/// # Errors
/// [`ValueError::ArithmeticOverflow`] — the sum passes sixty-four bits.
#[spec(ensures: |ret| ret.is_ok() == u64::from(count).checked_add(u64::from(more)).is_some())]
pub(crate) fn add_tokens(
    count: TokenCount,
    more: TokenCount,
) -> Result<TokenCount, ValueError>
{
    u64::from(count)
        .checked_add(u64::from(more))
        .map(TokenCount::from)
        .ok_or(ValueError::ArithmeticOverflow {
            quantity: ValueQuantity::TokenCount,
        })
}

#[cfg(test)]
mod tests
{
    use gandr_storage_chunker::TokenCount;

    use super::walk_closure;
    use crate::chunk::ChunkStore as _;
    use crate::chunk::InMemoryChunkStore;
    use crate::chunk::frame_chunk;
    use crate::error::ValueError;
    use crate::ptr::ContentPtr;
    use crate::ptr::TokenOffset;
    use crate::tokens::TokenKind;
    use crate::units::TokenBody;

    #[test]
    fn the_walk_counts_the_addressed_subtree_and_refuses_a_malformed_one()
    {
        let mut store = InMemoryChunkStore::new();
        let mut stored = |body: &[u8]| {
            let chunk = frame_chunk(TokenBody::from(body)).expect("the body frames");
            store.insert(chunk.as_verified()).expect("the chunk stores");
            chunk.digest()
        };

        // Open, open, word, close, close: the whole body is one subtree of
        // five records, and the inner subtree at offset one is three.
        let nested = stored(&[
            0x01_u8, 0x2A, 0x01, 0x2B, 0x02, 7, 0, 0, 0, 0, 0, 0, 0, 0x05, 0x05,
        ]);
        let word = stored(&[0x02_u8, 7, 0, 0, 0, 0, 0, 0, 0]);
        let close = stored(&[0x05_u8]);
        let unclosed = stored(&[0x01_u8, 0x2A]);
        let at = |digest, offset: u32| ContentPtr::new(digest, TokenOffset::from(offset));

        let whole = walk_closure(&store, at(nested, 0)).expect("the body is one subtree");
        assert_eq!(whole.token_count(), TokenCount::from(5_u64));
        let inner = walk_closure(&store, at(nested, 1)).expect("offset one is a subtree");
        assert_eq!(
            inner.token_count(),
            TokenCount::from(3_u64),
            "an interior offset counts its own subtree and stops at its close"
        );

        let refusals = [
            (at(word, 0), ValueError::UnexpectedToken {
                expected: TokenKind::Open,
                found: TokenKind::Word,
                position: TokenOffset::ZERO,
            }),
            (at(close, 0), ValueError::UnexpectedToken {
                expected: TokenKind::Open,
                found: TokenKind::Close,
                position: TokenOffset::ZERO,
            }),
            (at(unclosed, 0), ValueError::TruncatedStream {
                position: TokenOffset::from(1_u32),
            }),
            (at(nested, 5), ValueError::TruncatedStream {
                position: TokenOffset::from(5_u32),
            }),
        ];
        for (pointer, refusal) in refusals {
            assert_eq!(
                walk_closure(&store, pointer),
                Err(refusal),
                "the walk from {pointer:?} is refused by name"
            );
        }
    }
}
