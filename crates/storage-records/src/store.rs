//! Verified node storage through [`BlockStore`] and its in-memory
//! implementation.
//!
//! # Node admission
//!
//! Both store methods verify canonical node encodings. Value-plane chunks
//! use a separate store trait and byte language; see
//! [storage planes](https://github.com/gandr-lang/gandr/blob/main/crates/storage-records/README.md#storage-planes).
//!
//! # Store requirements
//!
//! Implementations verify bytes on insertion and load. Corrupted backing
//! bytes must produce an error rather than propagate to the caller.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;

use anodized::spec;

use crate::bytes::NodeHash;
use crate::error::RecordTreeError;
use crate::node::StoredNode;
use crate::node::verify_stored_node;

/// A content-addressed store of canonical node encodings.
///
/// # Specification
/// - requires: an implementor upholds the verified-load rule below.
/// - ensures: [`BlockStore::load`] yields bytes whose recomputed identity
///   equals the requested one and which decode as canonical node material; a
///   store that cannot establish that refuses rather than returning.
/// - provides: the boundary a tree writes through and a store-backed reader
///   reads through, with no traversal policy of its own.
/// - fails: both methods surface typed [`RecordTreeError`] values; neither
///   panics and neither silently drops a write.
/// - panics: none.
/// - executable: none — the universal obligation concerns every trait
///   implementation. Required-method instrumentation introduces implementation
///   hooks and associated constants, changing this trait's implementor and
///   trait-object interface; concrete method bodies carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 observations of the in-memory implementation cover valid
///   leaf admission, absence, identity mismatch, malformed material and
///   corruption after admission. This is evidence for that implementation, not
///   a proof about every implementation of the public trait.
/// - witness: `store::tests::a_written_node_loads_back`
/// - witness: `store::tests::an_absent_identity_is_refused`
/// - witness: `store::tests::insertion_refuses_a_mismatched_identity`
/// - witness: `store::tests::insertion_refuses_material_of_another_domain`
/// - witness: `store::tests::load_rechecks_corrupted_backing_bytes`
pub trait BlockStore
{
    /// Admits encoded node bytes under their claimed identity.
    ///
    /// # Specification
    /// - requires: `node` pairs encoded bytes with the identity the caller
    ///   claims for them; the implementor establishes the pairing rather than
    ///   assuming it.
    /// - ensures: on success the store holds those bytes under that identity,
    ///   and a later load of it yields them.
    /// - provides: the one admission path into a store, so material that cannot
    ///   be authenticated has no side door in.
    /// - fails: refuses with a typed [`RecordTreeError`] rather than admitting
    ///   unauthenticated or non-canonical material, and never drops a write
    ///   silently; the section below enumerates the variants.
    /// - panics: none.
    /// - executable: none — this required method has no body; trait-level
    ///   instrumentation changes its required implementation hooks and object
    ///   compatibility. The concrete insertion method checks admission and
    ///   state.
    ///
    /// # Errors
    /// [`RecordTreeError::HashMismatch`] — the bytes do not hash to the claimed
    /// identity.
    /// [`RecordTreeError::MalformedNode`] — the bytes are not node material.
    /// [`RecordTreeError::UnsupportedVersion`] — the bytes name an unknown
    /// encoding version.
    /// [`RecordTreeError::DuplicateKeys`] — a carried leaf repeats a key.
    /// [`RecordTreeError::BudgetExceeded`] — a declared count exceeds its
    /// ceiling.
    /// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
    ///
    /// # Adequacy
    /// - hypothesis: L3 valid and refused admissions through the concrete store
    ///   observe exact bytes, distinct-node counts and preservation of two
    ///   existing nodes after rejection. Other implementors must supply their
    ///   own evidence for the same obligation.
    /// - witness: `store::tests::a_written_node_loads_back`
    /// - witness: `store::tests::rejected_insertion_preserves_existing_nodes`
    /// - witness: `store::tests::rewriting_one_identity_keeps_one_entry`
    fn insert(
        &mut self,
        node: StoredNode<'_>,
    ) -> Result<(), RecordTreeError>;

    /// Returns the verified bytes stored under an identity.
    ///
    /// # Specification
    /// - requires: nothing — an identity the store never held is admissible
    ///   input and is refused by name.
    /// - ensures: on success bytes whose recomputed identity equals `hash` and
    ///   which decode as canonical node material.
    /// - provides: the verified-load rule the trait's own specification states,
    ///   so a reader never has to re-establish it.
    /// - fails: refuses with a typed [`RecordTreeError`] rather than returning
    ///   bytes it could not authenticate; the section below enumerates the
    ///   variants.
    /// - panics: none.
    /// - executable: none — this required method has no body; trait-level
    ///   instrumentation changes its required implementation hooks and object
    ///   compatibility. The concrete load method checks identity and decoding.
    ///
    /// # Errors
    /// [`RecordTreeError::UnknownNode`] — nothing is stored under the identity.
    /// [`RecordTreeError::HashMismatch`] — the stored bytes no longer hash to
    /// the identity.
    /// [`RecordTreeError::MalformedNode`] — the stored bytes no longer decode
    /// as node material.
    /// [`RecordTreeError::UnsupportedVersion`] — the stored bytes name an
    /// unknown encoding version.
    /// [`RecordTreeError::DuplicateKeys`] — a stored leaf repeats a key.
    /// [`RecordTreeError::BudgetExceeded`] — a declared count exceeds its
    /// ceiling.
    /// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
    ///
    /// # Adequacy
    /// - hypothesis: L3 loads through the concrete store compare complete
    ///   bytes, report the requested absent identity, and refuse backing bytes
    ///   altered after insertion or stored under a matching but noncanonical
    ///   identity. These fixtures do not certify third-party implementations.
    /// - witness: `store::tests::a_written_node_loads_back`
    /// - witness: `store::tests::an_absent_identity_is_refused`
    /// - witness: `store::tests::load_rechecks_corrupted_backing_bytes`
    fn load(
        &self,
        hash: NodeHash,
    ) -> Result<StoredNode<'_>, RecordTreeError>;
}

/// A store held in an ordered map.
///
/// The map is ordered rather than hashed so that iteration and replacement are
/// deterministic across processes, which a hashed map with a per-process seed
/// would not be.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the [`BlockStore`] guarantee, established by recomputing on both
///   paths rather than by trusting the map.
/// - provides: a synchronous resident implementation of verified storage.
/// - fails: as [`BlockStore`] states.
/// - panics: none.
/// - executable: none — backing bytes are untrusted, so validity cannot be a
///   state precondition. Fresh verification and failed-write preservation
///   relate operations to their inputs and prior state, as the methods check.
///
/// # Adequacy
/// - hypothesis: L3 leaf fixtures distinguish admission, unknown identities,
///   rejected replacement and corruption between insertion and load. Exact
///   bytes and error variants expose trusting the map without rechecking it.
/// - witness: `store::tests::a_written_node_loads_back`
/// - witness: `store::tests::an_absent_identity_is_refused`
/// - witness: `store::tests::insertion_refuses_a_mismatched_identity`
/// - witness: `store::tests::insertion_refuses_material_of_another_domain`
/// - witness: `store::tests::rejected_insertion_preserves_existing_nodes`
/// - witness: `store::tests::load_rechecks_corrupted_backing_bytes`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct InMemoryBlockStore
{
    /// Node encodings by identity.
    nodes: BTreeMap<NodeHash, Box<[u8]>>,
}

impl InMemoryBlockStore
{
    /// Builds an empty store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            nodes: BTreeMap::new(),
        }
    }

    /// Reports how many distinct nodes the store holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> StoredNodeCount
    {
        StoredNodeCount::from(self.nodes.len())
    }

    /// Reports whether the store holds nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`StoreOccupancy::Empty`] exactly when the store holds no
    ///   node, and [`StoreOccupancy::Occupied`] otherwise.
    /// - provides: a nominal occupancy decision rather than a bare Boolean.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observations before and after a valid insertion
    ///   distinguish empty and occupied states; an invalid insertion into an
    ///   empty store must not change occupancy.
    /// - witness: `store::tests::a_written_node_loads_back`
    /// - witness: `store::tests::insertion_refuses_a_mismatched_identity`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| (ret == StoreOccupancy::Empty) == self.nodes.is_empty())]
    pub fn is_empty(&self) -> StoreOccupancy
    {
        if self.nodes.is_empty() {
            StoreOccupancy::Empty
        }
        else {
            StoreOccupancy::Occupied
        }
    }
}

impl BlockStore for InMemoryBlockStore
{
    /// Admit encoded node bytes under their claimed identity.
    ///
    /// # Specification
    /// - requires: nothing beyond the trait's own precondition.
    /// - ensures: on success the map holds the bytes under the node's identity,
    ///   replacing any bytes stored under it before, and the identity was
    ///   recomputed from the bytes rather than trusted.
    /// - provides: the trait's admission guarantee, discharged by verifying
    ///   before the map is touched, so a refused write leaves the store as it
    ///   was.
    /// - fails: propagates the verification refusal unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 empty, single-entry and two-entry stores observe exact
    ///   retained bytes and counts after insertion, repeat insertion and
    ///   refused replacement. The predicate checks admission, target bytes and
    ///   cardinality; the two-entry witness also observes preservation of
    ///   unrelated bytes.
    /// - witness: `store::tests::a_written_node_loads_back`
    /// - witness: `store::tests::rewriting_one_identity_keeps_one_entry`
    /// - witness: `store::tests::rejected_insertion_preserves_existing_nodes`
    #[inline]
    #[spec(
        captures: entry = (self.nodes.len(), self.nodes.contains_key(&node.identity())),
        ensures: |ret| match verify_stored_node(node) {
            Ok(()) => ret.is_ok()
                && self.nodes.get(&node.identity()).is_some_and(|bytes| bytes.as_ref() == node.bytes().as_ref())
                && entry.0.checked_add(usize::from(!entry.1)) == Some(self.nodes.len()),
            Err(error) => ret == Err(error) && self.nodes.len() == entry.0,
        },
    )]
    fn insert(
        &mut self,
        node: StoredNode<'_>,
    ) -> Result<(), RecordTreeError>
    {
        verify_stored_node(node)?;
        let _replaced = self
            .nodes
            .insert(node.identity(), Box::<[u8]>::from(node.bytes()));

        Ok(())
    }

    /// Return the verified bytes stored under an identity.
    ///
    /// # Specification
    /// - requires: nothing — an identity the store never held is admissible
    ///   input.
    /// - ensures: on success bytes whose identity was recomputed and whose node
    ///   material was decoded on this path, not merely on the write.
    /// - provides: the trait's verified-load guarantee, discharged by
    ///   recomputing rather than by trusting the map's key.
    /// - fails: [`RecordTreeError::UnknownNode`] when the map holds nothing
    ///   under `hash`, and the verification refusal unchanged when the stored
    ///   bytes no longer authenticate.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 valid and absent leaf identities compare exact bytes
    ///   and error payloads. Mutating backing bytes after admission and
    ///   installing correctly hashed malformed bytes distinguish authentication
    ///   from map lookup and canonical decoding from hashing alone.
    /// - witness: `store::tests::a_written_node_loads_back`
    /// - witness: `store::tests::an_absent_identity_is_refused`
    /// - witness: `store::tests::load_rechecks_corrupted_backing_bytes`
    #[inline]
    #[spec(ensures: |ret| self.nodes.get(&hash).map_or_else(
        || ret == Err(RecordTreeError::UnknownNode { hash }),
        |bytes| match verify_stored_node(StoredNode::new(hash, bytes.as_ref().into())) {
            Ok(()) => ret.as_ref().is_ok_and(|loaded| loaded.identity() == hash
                && core::ptr::eq(core::ptr::from_ref(loaded.bytes().as_ref()), core::ptr::from_ref(bytes.as_ref()))),
            Err(error) => ret == Err(error),
        },
    ))]
    fn load(
        &self,
        hash: NodeHash,
    ) -> Result<StoredNode<'_>, RecordTreeError>
    {
        let bytes = self
            .nodes
            .get(&hash)
            .ok_or(RecordTreeError::UnknownNode { hash })?;
        let node = StoredNode::new(hash, bytes.as_ref().into());
        verify_stored_node(node)?;

        Ok(node)
    }
}

/// How many distinct nodes a store holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StoredNodeCount(usize);

impl From<usize> for StoredNodeCount
{
    /// Read a `usize` as a stored-node count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<StoredNodeCount> for usize
{
    /// Read the count back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: StoredNodeCount) -> Self
    {
        count.0
    }
}

/// Whether a store holds anything.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StoreOccupancy
{
    /// The store holds nothing.
    Empty,
    /// The store holds at least one node.
    Occupied,
}

#[cfg(test)]
mod tests
{
    use anodized::spec;

    use super::BlockStore;
    use super::InMemoryBlockStore;
    use super::StoreOccupancy;
    use super::StoredNodeCount;
    use crate::bytes::EncodedNode;
    use crate::bytes::NodeHash;
    use crate::error::RecordTreeError;
    use crate::node::StoredNode;
    use crate::node::encode_leaf;
    use crate::node::hash_node;
    use crate::record::RecordRef;

    /// A seed byte for a synthetic node identity.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct HashSeed(u8);

    /// A node identity built from one seed byte.
    ///
    /// # Specification
    /// - requires: nothing; every seed is admissible.
    /// - ensures: an identity whose first byte is the seed and whose remaining
    ///   bytes are zero, so distinct seeds give distinct identities.
    /// - provides: reproducible identities for absence and mismatch fixtures;
    ///   no claim of cryptographic impossibility is made about their preimages.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 absence and mismatch fixtures use seed bytes 7 and 9
    ///   and compare the resulting requested identities with independent
    ///   fixed-byte expectations in the returned errors. Zeroing or shifting
    ///   the seed fails.
    /// - witness: `store::tests::an_absent_identity_is_refused`
    /// - witness: `store::tests::insertion_refuses_a_mismatched_identity`
    #[spec(ensures: |ret| ret.as_ref().first() == Some(&seed.0)
        && ret.as_ref().iter().skip(1_usize).all(|byte| *byte == 0_u8))]
    fn node_hash(seed: HashSeed) -> NodeHash
    {
        let mut bytes = [0_u8; 32_usize];
        bytes[0] = seed.0;

        NodeHash::from(bytes)
    }

    #[test]
    fn a_written_node_loads_back()
    {
        let encoded = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
        let hash = hash_node(encoded.as_borrowed());
        let mut store = InMemoryBlockStore::new();

        assert_eq!(store.is_empty(), StoreOccupancy::Empty);
        assert_eq!(
            BlockStore::insert(&mut store, StoredNode::new(hash, encoded.as_borrowed())),
            Ok(())
        );
        assert_eq!(store.len(), StoredNodeCount::from(1_usize));
        assert_eq!(store.is_empty(), StoreOccupancy::Occupied);

        let loaded = BlockStore::load(&store, hash).expect("the node was written");
        assert_eq!(loaded.identity(), hash);
        assert_eq!(loaded.bytes().as_ref(), encoded.as_ref());
    }

    #[test]
    fn an_absent_identity_is_refused()
    {
        let store = InMemoryBlockStore::new();

        assert_eq!(
            BlockStore::load(&store, node_hash(HashSeed(7_u8))),
            Err(RecordTreeError::UnknownNode {
                hash: NodeHash::from([
                    7_u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0
                ]),
            })
        );
    }

    #[test]
    fn insertion_refuses_a_mismatched_identity()
    {
        let encoded = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
        let actual = hash_node(encoded.as_borrowed());
        let mut store = InMemoryBlockStore::new();

        assert_eq!(
            BlockStore::insert(
                &mut store,
                StoredNode::new(node_hash(HashSeed(9_u8)), encoded.as_borrowed())
            ),
            Err(RecordTreeError::HashMismatch {
                expected: NodeHash::from([
                    9_u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0
                ]),
                actual,
            })
        );
        assert_eq!(store.is_empty(), StoreOccupancy::Empty);
    }

    #[test]
    fn insertion_refuses_material_of_another_domain()
    {
        let body = b"a value-plane chunk, not a node";
        let hash = hash_node(EncodedNode::from(body));
        let mut store = InMemoryBlockStore::new();

        assert!(matches!(
            BlockStore::insert(&mut store, StoredNode::new(hash, EncodedNode::from(body))),
            Err(RecordTreeError::MalformedNode { .. })
        ));
    }

    #[test]
    fn rewriting_one_identity_keeps_one_entry()
    {
        let encoded = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
        let hash = hash_node(encoded.as_borrowed());
        let mut store = InMemoryBlockStore::new();

        assert_eq!(
            BlockStore::insert(&mut store, StoredNode::new(hash, encoded.as_borrowed())),
            Ok(())
        );
        assert_eq!(
            BlockStore::insert(&mut store, StoredNode::new(hash, encoded.as_borrowed())),
            Ok(())
        );
        assert_eq!(
            BlockStore::load(&store, hash)
                .expect("the identity remains stored")
                .bytes()
                .as_ref(),
            encoded.as_ref()
        );
        assert_eq!(store.len(), StoredNodeCount::from(1_usize));
    }

    #[test]
    fn rejected_insertion_preserves_existing_nodes()
    {
        let first = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the first leaf encodes");
        let second = encode_leaf(&[RecordRef::new(b"b", b"2")]).expect("the second leaf encodes");
        let first_hash = hash_node(first.as_borrowed());
        let second_hash = hash_node(second.as_borrowed());
        let mut store = InMemoryBlockStore::new();
        BlockStore::insert(&mut store, StoredNode::new(first_hash, first.as_borrowed()))
            .expect("the first leaf is valid");
        BlockStore::insert(
            &mut store,
            StoredNode::new(second_hash, second.as_borrowed()),
        )
        .expect("the second leaf is valid");
        assert_eq!(
            BlockStore::insert(
                &mut store,
                StoredNode::new(first_hash, second.as_borrowed())
            ),
            Err(RecordTreeError::HashMismatch {
                expected: first_hash,
                actual: second_hash
            })
        );
        let malformed = EncodedNode::from(b"not a canonical node");
        let malformed_hash = hash_node(malformed);
        assert!(matches!(
            BlockStore::insert(&mut store, StoredNode::new(malformed_hash, malformed)),
            Err(RecordTreeError::MalformedNode { .. })
        ));
        assert_eq!(store.len(), StoredNodeCount::from(2_usize));
        assert_eq!(
            BlockStore::load(&store, first_hash)
                .expect("the first leaf remains")
                .bytes()
                .as_ref(),
            first.as_ref()
        );
        assert_eq!(
            BlockStore::load(&store, second_hash)
                .expect("the second leaf remains")
                .bytes()
                .as_ref(),
            second.as_ref()
        );
        assert_eq!(
            BlockStore::load(&store, malformed_hash),
            Err(RecordTreeError::UnknownNode {
                hash: malformed_hash
            })
        );
    }

    #[test]
    fn load_rechecks_corrupted_backing_bytes()
    {
        let encoded = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
        let hash = hash_node(encoded.as_borrowed());
        let mut store = InMemoryBlockStore::new();
        BlockStore::insert(&mut store, StoredNode::new(hash, encoded.as_borrowed()))
            .expect("the leaf is valid");
        let bytes = store.nodes.get_mut(&hash).expect("the node was admitted");
        *bytes.last_mut().expect("the encoded node is not empty") ^= 1_u8;
        let actual = hash_node(EncodedNode::from(bytes.as_ref()));
        assert_eq!(
            BlockStore::load(&store, hash),
            Err(RecordTreeError::HashMismatch {
                expected: hash,
                actual
            })
        );

        let malformed = EncodedNode::from(b"not a canonical node");
        let malformed_hash = hash_node(malformed);
        let _previous = store
            .nodes
            .insert(malformed_hash, alloc::boxed::Box::from(malformed.as_ref()));
        assert!(matches!(
            BlockStore::load(&store, malformed_hash),
            Err(RecordTreeError::MalformedNode { .. })
        ));
    }
}
