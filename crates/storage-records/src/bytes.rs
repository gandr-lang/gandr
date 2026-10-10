//! The byte carriers the crate's signatures are written in: record keys,
//! record values, encoded node bytes, and the node identity [`NodeHash`].
//!
//! Each carrier is a `#[repr(transparent)]` newtype over a byte slice or a
//! boxed byte slice, in a borrowed and an owned flavour. The point is not
//! safety inside the crate but at its boundary: a key, a value, and a node
//! encoding are all `[u8]` and are all semantically different, so a signature
//! written in `&[u8]` lets a caller swap them silently.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

/// Byte width of a node identity, fixed by the hash family.
pub(crate) const NODE_HASH_LEN: usize = 32_usize;

/// Defines a borrowed byte carrier with its ordinary conversions.
macro_rules! borrowed_bytes {
    (
        $(#[$attribute:meta])*
        $name:ident
    ) => {
        $(#[$attribute])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name<'bytes>(&'bytes [u8]);

        impl<'bytes> From<&'bytes [u8]> for $name<'bytes> {
            /// Reads a byte slice as this carrier.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(bytes: &'bytes [u8]) -> Self {
                Self(bytes)
            }
        }

        impl<'bytes, const LEN: usize> From<&'bytes [u8; LEN]> for $name<'bytes> {
            /// Reads a fixed-width byte array as this carrier.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(bytes: &'bytes [u8; LEN]) -> Self {
                Self(bytes.as_slice())
            }
        }

        impl<'bytes> From<$name<'bytes>> for &'bytes [u8] {
            /// Reads the carried bytes back out as a slice.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(carrier: $name<'bytes>) -> Self {
                carrier.0
            }
        }

        impl AsRef<[u8]> for $name<'_> {
            /// Borrows the carried bytes.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn as_ref(&self) -> &[u8] {
                self.0
            }
        }
    };
}

/// Defines an owned byte carrier beside its borrowed sibling.
macro_rules! owned_bytes {
    (
        $(#[$attribute:meta])*
        $name:ident borrows $borrowed:ident
    ) => {
        $(#[$attribute])*
        #[repr(transparent)]
        #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(Box<[u8]>);

        impl $name {
            /// Borrows this value as its borrowed sibling.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            #[must_use]
            pub fn as_borrowed(&self) -> $borrowed<'_> {
                $borrowed::from(self.0.as_ref())
            }
        }

        impl From<Box<[u8]>> for $name {
            /// Takes over an owned boxed slice as this carrier.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(bytes: Box<[u8]>) -> Self {
                Self(bytes)
            }
        }

        impl From<$name> for Box<[u8]> {
            /// Reads the carried bytes back out as an owned boxed slice.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(carrier: $name) -> Self {
                carrier.0
            }
        }

        impl AsRef<[u8]> for $name {
            /// Borrows the carried bytes.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn as_ref(&self) -> &[u8] {
                self.0.as_ref()
            }
        }
    };
}

borrowed_bytes! {
    /// Borrowed canonical key bytes of one record.
    ///
    /// Keys are compared as byte strings and that comparison is the tree's
    /// order; the crate never interprets a key's contents.
    RecordKey
}

owned_bytes! {
    /// Owned canonical key bytes of one record.
    OwnedRecordKey borrows RecordKey
}

impl From<RecordKey<'_>> for Box<[u8]>
{
    /// Copies the carried bytes into an owned boxed slice.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the carried bytes, independent of the
    ///   borrow, including an empty input.
    /// - provides: the crossing from a borrowed carrier to owned bytes, which
    ///   copies.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 over the forty-record leaf corpus; decoded keys and
    ///   values distinguish dropped, reordered or substituted bytes at the
    ///   borrowed-to-owned boundary. Allocation counts are outside this
    ///   observer.
    /// - witness: `node::tests::leaves_round_trip`
    #[anodized::spec(ensures: |ret| ret.as_ref() == carrier.as_ref())]
    #[inline]
    fn from(carrier: RecordKey<'_>) -> Self
    {
        Self::from(carrier.0)
    }
}

impl From<Vec<u8>> for OwnedRecordKey
{
    /// Takes over a byte vector as this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: the carrier holds exactly the vector's bytes, with its excess
    ///   capacity released, which may reallocate.
    /// - provides: the crossing from a growable buffer an encoder built to the
    ///   fixed-width carrier a signature is written in.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on the forty-record leaf corpus; enforcing calls
    ///   distinguish changed widths and endpoints before the leaf consumes the
    ///   records. Interior replacement before encoding and allocation counts
    ///   are outside this observer.
    /// - witness: `node::tests::leaves_round_trip`
    #[anodized::spec(
        captures: before = (bytes.len(), bytes.first().copied(), bytes.last().copied()),
        ensures: |ret| ret.as_ref().len() == before.0
            && ret.as_ref().first().copied() == before.1
            && ret.as_ref().last().copied() == before.2,
    )]
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes.into_boxed_slice())
    }
}

impl From<&[u8]> for OwnedRecordKey
{
    /// Copies a byte slice into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the offered slice.
    /// - provides: the owning copy a caller takes when the borrow it has is
    ///   shorter-lived than the carrier it needs.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on decoded keys and values in the forty-record leaf
    ///   corpus; comparison with the offered record references distinguishes
    ///   lost or substituted payload bytes. Allocation counts are not observed.
    /// - witness: `node::tests::leaves_round_trip`
    #[anodized::spec(ensures: |ret| ret.as_ref() == bytes)]
    #[inline]
    fn from(bytes: &[u8]) -> Self
    {
        Self(Box::from(bytes))
    }
}

impl<const LEN: usize> From<&[u8; LEN]> for OwnedRecordKey
{
    /// Copies a fixed-width byte array into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the offered array.
    /// - provides: the literal-fixture path, so a test writes an array where
    ///   the signature asks for a carrier.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on three single-byte separator literals; decoded child
    ///   references distinguish omitted or collapsed separators without
    ///   claiming allocation-cost evidence.
    /// - witness: `node::tests::internal_nodes_round_trip`
    #[anodized::spec(ensures: |ret| ret.as_ref() == bytes.as_slice())]
    #[inline]
    fn from(bytes: &[u8; LEN]) -> Self
    {
        Self(Box::from(bytes.as_slice()))
    }
}

impl From<RecordKey<'_>> for OwnedRecordKey
{
    /// Copies the borrowed sibling's bytes into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the borrowed sibling's bytes.
    /// - provides: the owning half of the borrowed and owned pair, so the two
    ///   flavours convert without going through `[u8]` and losing which carrier
    ///   they were.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on reconstituted keys and values in the forty-record
    ///   leaf corpus; equality with decoded records distinguishes dropped,
    ///   reordered or substituted bytes. Allocation counts are outside this
    ///   observer.
    /// - witness: `node::tests::leaves_round_trip`
    #[anodized::spec(ensures: |ret| ret.as_ref() == carrier.as_ref())]
    #[inline]
    fn from(carrier: RecordKey<'_>) -> Self
    {
        Self(Box::from(carrier))
    }
}

borrowed_bytes! {
    /// Borrowed canonical value bytes of one record.
    ///
    /// Values are opaque to the tree: they contribute to node identity and to
    /// leaf boundaries, and are never parsed.
    RecordValue
}

owned_bytes! {
    /// Owned canonical value bytes of one record.
    OwnedRecordValue borrows RecordValue
}

impl From<RecordValue<'_>> for Box<[u8]>
{
    /// Copies the carried bytes into an owned boxed slice.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the carried bytes, independent of the
    ///   borrow, including an empty input.
    /// - provides: the crossing from a borrowed carrier to owned bytes, which
    ///   copies.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 over the forty-record leaf corpus; decoded keys and
    ///   values distinguish dropped, reordered or substituted bytes at the
    ///   borrowed-to-owned boundary. Allocation counts are outside this
    ///   observer.
    /// - witness: `node::tests::leaves_round_trip`
    #[anodized::spec(ensures: |ret| ret.as_ref() == carrier.as_ref())]
    #[inline]
    fn from(carrier: RecordValue<'_>) -> Self
    {
        Self::from(carrier.0)
    }
}

impl From<Vec<u8>> for OwnedRecordValue
{
    /// Takes over a byte vector as this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: the carrier holds exactly the vector's bytes, with its excess
    ///   capacity released, which may reallocate.
    /// - provides: the crossing from a growable buffer an encoder built to the
    ///   fixed-width carrier a signature is written in.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on the forty-record leaf corpus; enforcing calls
    ///   distinguish changed widths and endpoints before the leaf consumes the
    ///   records. Interior replacement before encoding and allocation counts
    ///   are outside this observer.
    /// - witness: `node::tests::leaves_round_trip`
    #[anodized::spec(
        captures: before = (bytes.len(), bytes.first().copied(), bytes.last().copied()),
        ensures: |ret| ret.as_ref().len() == before.0
            && ret.as_ref().first().copied() == before.1
            && ret.as_ref().last().copied() == before.2,
    )]
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes.into_boxed_slice())
    }
}

impl From<&[u8]> for OwnedRecordValue
{
    /// Copies a byte slice into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the offered slice.
    /// - provides: the owning copy a caller takes when the borrow it has is
    ///   shorter-lived than the carrier it needs.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on decoded keys and values in the forty-record leaf
    ///   corpus; comparison with the offered record references distinguishes
    ///   lost or substituted payload bytes. Allocation counts are not observed.
    /// - witness: `node::tests::leaves_round_trip`
    #[anodized::spec(ensures: |ret| ret.as_ref() == bytes)]
    #[inline]
    fn from(bytes: &[u8]) -> Self
    {
        Self(Box::from(bytes))
    }
}

impl<const LEN: usize> From<&[u8; LEN]> for OwnedRecordValue
{
    /// Copies a fixed-width byte array into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the offered array.
    /// - provides: the literal-fixture path, so a test writes an array where
    ///   the signature asks for a carrier.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the single-byte value of a one-record leaf; its
    ///   complete wire image and pinned identity distinguish a dropped or
    ///   changed value. Allocation counts are not observed.
    /// - witness: `node::tests::the_node_identity_is_pinned`
    #[anodized::spec(ensures: |ret| ret.as_ref() == bytes.as_slice())]
    #[inline]
    fn from(bytes: &[u8; LEN]) -> Self
    {
        Self(Box::from(bytes.as_slice()))
    }
}

impl From<RecordValue<'_>> for OwnedRecordValue
{
    /// Copies the borrowed sibling's bytes into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the borrowed sibling's bytes.
    /// - provides: the owning half of the borrowed and owned pair, so the two
    ///   flavours convert without going through `[u8]` and losing which carrier
    ///   they were.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on reconstituted keys and values in the forty-record
    ///   leaf corpus; equality with decoded records distinguishes dropped,
    ///   reordered or substituted bytes. Allocation counts are outside this
    ///   observer.
    /// - witness: `node::tests::leaves_round_trip`
    #[anodized::spec(ensures: |ret| ret.as_ref() == carrier.as_ref())]
    #[inline]
    fn from(carrier: RecordValue<'_>) -> Self
    {
        Self(Box::from(carrier))
    }
}

borrowed_bytes! {
    /// Borrowed canonical encoding of one record, as the boundary rule reads it.
    ///
    /// This is not node material: it is one record framed on its own, which is
    /// what makes a record's boundary decision a function of that record alone.
    RecordEncoding
}

owned_bytes! {
    /// Owned canonical encoding of one record.
    OwnedRecordEncoding borrows RecordEncoding
}

impl From<RecordEncoding<'_>> for Box<[u8]>
{
    /// Copies the carried bytes into an owned boxed slice.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the carried bytes, independent of the
    ///   borrow, including an empty input.
    /// - provides: the crossing from a borrowed carrier to owned bytes, which
    ///   copies.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the canonical (ab, c) record image; complete wire
    ///   bytes and an independent boundary residue distinguish changed widths,
    ///   framing and payload bytes. Allocation counts are not observed.
    /// - witness: `boundary::tests::record_encoding_pins_field_framing`
    #[anodized::spec(ensures: |ret| ret.as_ref() == carrier.as_ref())]
    #[inline]
    fn from(carrier: RecordEncoding<'_>) -> Self
    {
        Self::from(carrier.0)
    }
}

impl From<Vec<u8>> for OwnedRecordEncoding
{
    /// Takes over a byte vector as this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: the carrier holds exactly the vector's bytes, with its excess
    ///   capacity released, which may reallocate.
    /// - provides: the crossing from a growable buffer an encoder built to the
    ///   fixed-width carrier a signature is written in.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on empty, binary and (ab, c) records; complete wire
    ///   images and independent boundary residues distinguish changed widths,
    ///   framing and payload bytes. Allocation counts are not observed.
    /// - witness: `boundary::tests::record_encoding_pins_field_framing`
    #[anodized::spec(
        captures: before = (bytes.len(), bytes.first().copied(), bytes.last().copied()),
        ensures: |ret| ret.as_ref().len() == before.0
            && ret.as_ref().first().copied() == before.1
            && ret.as_ref().last().copied() == before.2,
    )]
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes.into_boxed_slice())
    }
}

impl From<&[u8]> for OwnedRecordEncoding
{
    /// Copies a byte slice into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the offered slice.
    /// - provides: the owning copy a caller takes when the borrow it has is
    ///   shorter-lived than the carrier it needs.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the canonical mixed-binary record; complete wire
    ///   bytes and an independent boundary residue distinguish changed widths,
    ///   lost zero bytes and changed high bytes. Allocation counts are not
    ///   observed.
    /// - witness: `boundary::tests::record_encoding_pins_field_framing`
    #[anodized::spec(ensures: |ret| ret.as_ref() == bytes)]
    #[inline]
    fn from(bytes: &[u8]) -> Self
    {
        Self(Box::from(bytes))
    }
}

impl<const LEN: usize> From<&[u8; LEN]> for OwnedRecordEncoding
{
    /// Copies a fixed-width byte array into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the offered array.
    /// - provides: the literal-fixture path, so a test writes an array where
    ///   the signature asks for a carrier.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the canonical empty record; its complete wire image
    ///   and independent boundary residue distinguish changed widths, domains
    ///   and length fields. Allocation counts are not observed.
    /// - witness: `boundary::tests::record_encoding_pins_field_framing`
    #[anodized::spec(ensures: |ret| ret.as_ref() == bytes.as_slice())]
    #[inline]
    fn from(bytes: &[u8; LEN]) -> Self
    {
        Self(Box::from(bytes.as_slice()))
    }
}

impl From<RecordEncoding<'_>> for OwnedRecordEncoding
{
    /// Copies the borrowed sibling's bytes into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the borrowed sibling's bytes.
    /// - provides: the owning half of the borrowed and owned pair, so the two
    ///   flavours convert without going through `[u8]` and losing which carrier
    ///   they were.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the canonical (ab, c) record image; complete wire
    ///   bytes and an independent boundary residue distinguish changed widths,
    ///   framing and payload bytes. Allocation counts are not observed.
    /// - witness: `boundary::tests::record_encoding_pins_field_framing`
    #[anodized::spec(ensures: |ret| ret.as_ref() == carrier.as_ref())]
    #[inline]
    fn from(carrier: RecordEncoding<'_>) -> Self
    {
        Self(Box::from(carrier))
    }
}

borrowed_bytes! {
    /// Borrowed canonical encoding of one tree node.
    ///
    /// These are the bytes the node identity is a digest of, so a value of
    /// this type is exactly what a store holds and a proof carries.
    EncodedNode
}

owned_bytes! {
    /// Owned canonical encoding of one tree node.
    OwnedEncodedNode borrows EncodedNode
}

impl From<EncodedNode<'_>> for Box<[u8]>
{
    /// Copies the carried bytes into an owned boxed slice.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the carried bytes, independent of the
    ///   borrow, including an empty input.
    /// - provides: the crossing from a borrowed carrier to owned bytes, which
    ///   copies.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on the encoded three-child internal node; decoded
    ///   separators, identities and record counts distinguish dropped,
    ///   reordered or substituted bytes. Allocation counts are not observed.
    /// - witness: `node::tests::internal_nodes_round_trip`
    #[anodized::spec(ensures: |ret| ret.as_ref() == carrier.as_ref())]
    #[inline]
    fn from(carrier: EncodedNode<'_>) -> Self
    {
        Self::from(carrier.0)
    }
}

impl From<Vec<u8>> for OwnedEncodedNode
{
    /// Takes over a byte vector as this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: the carrier holds exactly the vector's bytes, with its excess
    ///   capacity released, which may reallocate.
    /// - provides: the crossing from a growable buffer an encoder built to the
    ///   fixed-width carrier a signature is written in.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on a one-record leaf's complete wire image and L1 on
    ///   forty decoded records; these observers distinguish truncation,
    ///   reordered bytes and changed endpoints. Allocation counts are not
    ///   observed.
    /// - witness: `node::tests::leaves_round_trip`
    /// - witness: `node::tests::the_node_identity_is_pinned`
    #[anodized::spec(
        captures: before = (bytes.len(), bytes.first().copied(), bytes.last().copied()),
        ensures: |ret| ret.as_ref().len() == before.0
            && ret.as_ref().first().copied() == before.1
            && ret.as_ref().last().copied() == before.2,
    )]
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes.into_boxed_slice())
    }
}

impl From<&[u8]> for OwnedEncodedNode
{
    /// Copies a byte slice into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the offered slice.
    /// - provides: the owning copy a caller takes when the borrow it has is
    ///   shorter-lived than the carrier it needs.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on decoded keys and values in the forty-record leaf
    ///   corpus; comparison with the offered record references distinguishes
    ///   lost or substituted payload bytes. Allocation counts are not observed.
    /// - witness: `node::tests::leaves_round_trip`
    #[anodized::spec(ensures: |ret| ret.as_ref() == bytes)]
    #[inline]
    fn from(bytes: &[u8]) -> Self
    {
        Self(Box::from(bytes))
    }
}

impl<const LEN: usize> From<&[u8; LEN]> for OwnedEncodedNode
{
    /// Copies a fixed-width byte array into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the offered array.
    /// - provides: the literal-fixture path, so a test writes an array where
    ///   the signature asks for a carrier.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the literal one-record leaf image; equality with its
    ///   canonical encoding and its pinned identity distinguish changed widths,
    ///   framing and payload bytes. Allocation counts are not observed.
    /// - witness: `node::tests::the_node_identity_is_pinned`
    #[anodized::spec(ensures: |ret| ret.as_ref() == bytes.as_slice())]
    #[inline]
    fn from(bytes: &[u8; LEN]) -> Self
    {
        Self(Box::from(bytes.as_slice()))
    }
}

impl From<EncodedNode<'_>> for OwnedEncodedNode
{
    /// Copies the borrowed sibling's bytes into this carrier.
    ///
    /// # Specification
    /// - requires: nothing; any width is admissible.
    /// - ensures: owned bytes equal to the borrowed sibling's bytes.
    /// - provides: the owning half of the borrowed and owned pair, so the two
    ///   flavours convert without going through `[u8]` and losing which carrier
    ///   they were.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on the encoded three-child internal node; decoded
    ///   separators, identities and record counts distinguish dropped,
    ///   reordered or substituted bytes. Allocation counts are not observed.
    /// - witness: `node::tests::internal_nodes_round_trip`
    #[anodized::spec(ensures: |ret| ret.as_ref() == carrier.as_ref())]
    #[inline]
    fn from(carrier: EncodedNode<'_>) -> Self
    {
        Self(Box::from(carrier))
    }
}

/// The identity of an encoded node: a digest of its canonical bytes under the
/// node domain.
///
/// # Specification
/// - requires: nothing; the type is a carrier and admits any byte array.
/// - ensures: `Display` renders the lowercase hexadecimal of the bytes in
///   order, and `Debug` renders identically, because a node identity read in
///   two notations in one log is harder to match by eye than it is worth.
/// - provides: an opaque, fixed-width name for a node encoding.
/// - fails: never.
/// - panics: none.
/// - executable: none — rendering is observed through the formatter methods,
///   whose sinks expose no readable output buffer.
///
/// # Adequacy
/// - hypothesis: L2 on a fixed-width digest spanning zero, the nibble boundary
///   and 255, with a distinct byte at each position; exact hexadecimal output
///   distinguishes padding, case and byte-order faults. L3 observes the first
///   sink refusal and detects further writes after it.
/// - witness: `bytes::tests::node_hash_renders_lowercase_hexadecimal`
/// - witness: `bytes::tests::node_hash_formatting_stops_at_the_first_refusal`
#[repr(transparent)]
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeHash([u8; NODE_HASH_LEN]);

/// A borrowed fixed-width identity representation for const observations.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct NodeHashBytes<'hash>(pub &'hash [u8; NODE_HASH_LEN]);

impl NodeHash
{
    /// Borrows the fixed-width identity without a non-const trait call.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn byte_view(&self) -> NodeHashBytes<'_>
    {
        NodeHashBytes(&self.0)
    }
}

impl From<[u8; NODE_HASH_LEN]> for NodeHash
{
    /// Reads a fixed-width byte array as a node identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; NODE_HASH_LEN]) -> Self
    {
        Self(bytes)
    }
}

impl From<NodeHash> for [u8; NODE_HASH_LEN]
{
    /// Reads the identity back out as its bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(hash: NodeHash) -> Self
    {
        hash.0
    }
}

impl AsRef<[u8]> for NodeHash
{
    /// Borrows the identity's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

impl fmt::Display for NodeHash
{
    /// Writes the identity as lowercase hexadecimal.
    ///
    /// # Specification
    /// - requires: nothing; every byte array is an admissible identity.
    /// - ensures: writes each byte in order as exactly two lowercase
    ///   hexadecimal digits, so the rendering is fixed-width and a byte below
    ///   sixteen keeps its leading zero.
    /// - provides: the opaque name for a node encoding that a log line and a
    ///   refusal message both carry.
    /// - fails: propagates the formatter's own write failure unchanged,
    ///   stopping at the byte that failed.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on all positions of a distinct-byte digest spanning
    ///   zero, the nibble boundary and 255; the exact hexadecimal image
    ///   distinguishes padding, case and ordering. L3 observes a refusing
    ///   sink's error and write count to detect swallowed or delayed failure.
    /// - witness: `bytes::tests::node_hash_renders_lowercase_hexadecimal`
    /// - witness: `bytes::tests::node_hash_formatting_stops_at_the_first_refusal`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }

        Ok(())
    }
}

impl fmt::Debug for NodeHash
{
    /// Writes the identity as its `Display` rendering does.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes exactly what [`fmt::Display`] writes for the same
    ///   identity, so one identity never appears in two notations in one log.
    /// - provides: the single rendering the type's own specification claims.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on all positions of a distinct-byte digest spanning
    ///   zero, the nibble boundary and 255; the exact hexadecimal image
    ///   distinguishes padding, case and ordering. L3 observes a refusing
    ///   sink's error and write count to detect swallowed or delayed failure.
    /// - witness: `bytes::tests::node_hash_renders_lowercase_hexadecimal`
    /// - witness: `bytes::tests::node_hash_formatting_stops_at_the_first_refusal`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;

    use super::NodeHash;
    use super::RecordKey;

    #[test]
    fn node_hash_renders_lowercase_hexadecimal()
    {
        let mut bytes: [u8; super::NODE_HASH_LEN] =
            core::array::from_fn(|index| u8::try_from(index).expect("digest index fits"));
        bytes[31] = 0xff_u8;
        let hash = NodeHash::from(bytes);
        let expected = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1eff";
        assert_eq!(format!("{hash}"), expected);
        assert_eq!(format!("{hash:?}"), expected);
    }

    #[test]
    fn key_order_is_byte_order()
    {
        let short = RecordKey::from(b"a");
        let long = RecordKey::from(b"ab");

        assert!(short < long);
        assert!(RecordKey::from(b"b") > long);
    }

    /// The number of writes attempted against a refusing sink.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct WriteAttempts(u32);

    /// A sink that counts attempts and refuses every write.
    #[repr(transparent)]
    #[derive(Debug)]
    struct RefusingSink
    {
        attempts: WriteAttempts,
    }

    impl core::fmt::Write for RefusingSink
    {
        /// Records and refuses one attempted write.
        ///
        /// # Specification
        /// - requires: nothing; the text is arbitrary.
        /// - ensures: increments the attempt count, saturating at its width.
        /// - provides: an observer for writes after a formatter refusal.
        /// - fails: always returns the formatting error.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 on the first attempted digest write; its error and
        ///   count distinguish accepted writes and missing accounting. Counter
        ///   saturation is not exercised by these single-write fixtures.
        /// - witness: `bytes::tests::node_hash_formatting_stops_at_the_first_refusal`
        #[anodized::spec(
            captures: before = self.attempts.0,
            ensures: |ret| ret == Err(core::fmt::Error) && self.attempts.0 == before.saturating_add(1),
        )]
        fn write_str(
            &mut self,
            _text: &str,
        ) -> core::fmt::Result
        {
            self.attempts.0 = self.attempts.0.saturating_add(1);
            Err(core::fmt::Error)
        }
    }

    #[test]
    fn node_hash_formatting_stops_at_the_first_refusal()
    {
        let hash = NodeHash::from([0xab_u8; super::NODE_HASH_LEN]);
        for args in [format_args!("{hash}"), format_args!("{hash:?}")] {
            let mut sink = RefusingSink {
                attempts: WriteAttempts(0),
            };
            assert_eq!(core::fmt::write(&mut sink, args), Err(core::fmt::Error));
            assert_eq!(sink.attempts, WriteAttempts(1));
        }
    }
}
