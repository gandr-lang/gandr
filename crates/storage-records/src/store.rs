//! The node store boundary: [`BlockStore`], the contract an implementor owes,
//! and the in-memory implementation.
//!
//! # This store holds node material and nothing else
//!
//! Both [`BlockStore`] methods run the node admission check, so this trait is
//! the **keyed-record plane's** store: it admits canonical node encodings and
//! refuses everything else. That is deliberate and it is a boundary, not a
//! limitation to work around. A value-plane chunk is not node material, and
//! wrapping a chunk as a one-record leaf to fit it through this trait would
//! make the chunk's identity depend on this crate's leaf framing instead of on
//! the value's own canonical bytes — destroying exactly the identity a value
//! plane exists to provide.
//!
//! The value plane's store is therefore a **sibling trait** with the chunk
//! domain inside its own hashed preimage, not this one with a relaxed
//! verifier. One backing object implementing both traits gives the shared
//! backing store the storage design wants, while each plane keeps a verifier
//! that answers for its own byte language.
//!
//! # What an implementor owes
//!
//! An implementor must not hand out bytes it has not verified. Both bundled
//! paths recompute on insertion and on load, so a store whose backing bytes rot
//! reports a mismatch rather than propagating them.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;

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
///   reads through, with no traversal policy of its own. The postcondition
///   stays prose: it is an obligation on every implementor of this trait, and a
///   clause here would bind only the bodies declared in it, of which there are
///   none.
/// - fails: both methods surface typed [`RecordTreeError`] values; neither
///   panics and neither silently drops a write.
/// - panics: none.
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
    ///
    /// # Errors
    /// [`RecordTreeError::HashMismatch`] — the bytes do not hash to the claimed
    /// identity.
    /// [`RecordTreeError::MalformedNode`] — the bytes are not node material.
    /// [`RecordTreeError::UnsupportedVersion`] — the bytes name an unknown
    /// encoding version.
    /// [`RecordTreeError::BudgetExceeded`] — a declared count exceeds its
    /// ceiling.
    /// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
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
    ///
    /// # Errors
    /// [`RecordTreeError::UnknownNode`] — nothing is stored under the identity.
    /// [`RecordTreeError::HashMismatch`] — the stored bytes no longer hash to
    /// the identity.
    /// [`RecordTreeError::MalformedNode`] — the stored bytes no longer decode
    /// as node material.
    /// [`RecordTreeError::UnsupportedVersion`] — the stored bytes name an
    /// unknown encoding version.
    /// [`RecordTreeError::BudgetExceeded`] — a declared count exceeds its
    /// ceiling.
    /// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
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
/// - provides: the store every test and every in-process caller uses. The
///   postcondition stays prose: it restates the trait's obligation, which the
///   two method bodies discharge and a data specification cannot state.
/// - fails: as [`BlockStore`] states.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 only — the decision surfaces are the admission check on
///   insertion, the absence check on load, and the recomputation on load, each
///   separated by one triggering input with the exact variant asserted.
/// - witness: `store::tests::a_written_node_loads_back`
/// - witness: `store::tests::an_absent_identity_is_refused`
/// - witness: `store::tests::insertion_refuses_a_mismatched_identity`
/// - witness: `store::tests::insertion_refuses_material_of_another_domain`
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
    /// - provides: the occupancy question as a named pair of states rather than
    ///   a bare `bool`, so a caller cannot read the answer backwards.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
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
    #[inline]
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
    #[inline]
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

    /// A seed byte for a node identity no tree produces.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct HashSeed(u8);

    /// A node identity built from one seed byte.
    ///
    /// # Specification
    /// - requires: nothing; every seed is admissible.
    /// - ensures: an identity whose first byte is the seed and whose remaining
    ///   bytes are zero, so distinct seeds give distinct identities.
    /// - provides: an identity no encoding of a real node produces, which is
    ///   what the absence and mismatch fixtures below need.
    /// - panics: none.
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
                hash: node_hash(HashSeed(7_u8)),
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
                expected: node_hash(HashSeed(9_u8)),
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

        assert_eq!(
            BlockStore::insert(&mut store, StoredNode::new(hash, EncodedNode::from(body))),
            Err(RecordTreeError::MalformedNode {
                context: "node domain".into(),
            })
        );
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
        assert_eq!(store.len(), StoredNodeCount::from(1_usize));
    }
}
