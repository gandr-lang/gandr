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

        impl From<$name<'_>> for Box<[u8]> {
            /// Copies the carried bytes into an owned boxed slice.
            ///
            /// # Specification
            /// - requires: nothing; any width is admissible.
            /// - ensures: a fresh allocation holding exactly the carried
            ///   bytes, so the result outlives the borrow rather than
            ///   aliasing it.
            /// - provides: the crossing from a borrowed carrier to owned
            ///   bytes, which copies.
            /// - fails: never.
            /// - panics: none.
            #[inline]
            fn from(carrier: $name<'_>) -> Self {
                Self::from(carrier.0)
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

        impl From<Vec<u8>> for $name {
            /// Takes over a byte vector as this carrier.
            ///
            /// # Specification
            /// - requires: nothing; any width is admissible.
            /// - ensures: the carrier holds exactly the vector's bytes, with
            ///   its excess capacity released, which may reallocate.
            /// - provides: the crossing from a growable buffer an encoder
            ///   built to the fixed-width carrier a signature is written in.
            /// - fails: never.
            /// - panics: none.
            #[inline]
            fn from(bytes: Vec<u8>) -> Self {
                Self(bytes.into_boxed_slice())
            }
        }

        impl From<&[u8]> for $name {
            /// Copies a byte slice into this carrier.
            ///
            /// # Specification
            /// - requires: nothing; any width is admissible.
            /// - ensures: a fresh allocation holding exactly those bytes.
            /// - provides: the owning copy a caller takes when the borrow it
            ///   has is shorter-lived than the carrier it needs.
            /// - fails: never.
            /// - panics: none.
            #[inline]
            fn from(bytes: &[u8]) -> Self {
                Self(Box::from(bytes))
            }
        }

        impl<const LEN: usize> From<&[u8; LEN]> for $name {
            /// Copies a fixed-width byte array into this carrier.
            ///
            /// # Specification
            /// - requires: nothing; any width is admissible.
            /// - ensures: a fresh allocation holding exactly those bytes.
            /// - provides: the literal-fixture path, so a test writes an
            ///   array where the signature asks for a carrier.
            /// - fails: never.
            /// - panics: none.
            #[inline]
            fn from(bytes: &[u8; LEN]) -> Self {
                Self(Box::from(bytes.as_slice()))
            }
        }

        impl From<$borrowed<'_>> for $name {
            /// Copies the borrowed sibling's bytes into this carrier.
            ///
            /// # Specification
            /// - requires: nothing; any width is admissible.
            /// - ensures: a fresh allocation holding exactly the borrowed
            ///   bytes.
            /// - provides: the owning half of the borrowed and owned pair, so
            ///   the two flavours convert without going through `[u8]` and
            ///   losing which carrier they were.
            /// - fails: never.
            /// - panics: none.
            #[inline]
            fn from(carrier: $borrowed<'_>) -> Self {
                Self(Box::from(carrier))
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

/// The identity of an encoded node: a digest of its canonical bytes under the
/// node domain.
///
/// # Specification
/// - requires: nothing; the type is a carrier and admits any byte array.
/// - ensures: `Display` renders the lowercase hexadecimal of the bytes in
///   order, and `Debug` renders identically, because a node identity read in
///   two notations in one log is harder to match by eye than it is worth.
/// - provides: an opaque, fixed-width name for a node encoding. The
///   postcondition stays prose: it is a property of the [`fmt::Display`] and
///   [`fmt::Debug`] implementations below, not of a value this type constructs.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 only — the rendering is separated from any other rendering
///   by one pinned digest whose hexadecimal is asserted exactly.
/// - witness: `bytes::tests::node_hash_renders_lowercase_hexadecimal`
#[repr(transparent)]
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeHash([u8; NODE_HASH_LEN]);

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
    use super::OwnedRecordKey;
    use super::RecordKey;

    #[test]
    fn node_hash_renders_lowercase_hexadecimal()
    {
        let mut bytes = [0_u8; super::NODE_HASH_LEN];
        bytes[0] = 0x0a_u8;
        bytes[1] = 0xff_u8;
        let hash = NodeHash::from(bytes);

        assert_eq!(
            format!("{hash}"),
            "0aff000000000000000000000000000000000000000000000000000000000000"
        );
        assert_eq!(format!("{hash:?}"), format!("{hash}"));
    }

    #[test]
    fn owned_and_borrowed_keys_round_trip()
    {
        let owned = OwnedRecordKey::from(b"alpha");
        let borrowed: RecordKey<'_> = owned.as_borrowed();

        assert_eq!(borrowed.as_ref(), b"alpha".as_slice());
        assert_eq!(OwnedRecordKey::from(borrowed), owned);
    }

    #[test]
    fn key_order_is_byte_order()
    {
        let short = RecordKey::from(b"a");
        let long = RecordKey::from(b"ab");

        assert!(short < long);
        assert!(RecordKey::from(b"b") > long);
    }
}
