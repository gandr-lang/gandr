//! The semantic wrappers every value-plane signature is stated in.
//!
//! A chunk count, a seam depth, a payload word and a codec version are all
//! integers, and a token body, a chunk image and a payload are all bytes. Each
//! gets its own type so the compiler refuses a swap that would otherwise read
//! as success.

use alloc::boxed::Box;
use core::fmt;

/// Declares a transparent wrapper over one primitive, with the exact
/// conversions in both directions and the primitive's rendering.
macro_rules! semantic_integer {
    (
        $(#[$attribute:meta])*
        $visibility:vis struct $name:ident($primitive:ty);
    ) => {
        $(#[$attribute])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        $visibility struct $name($primitive);

        impl From<$primitive> for $name
        {
            /// Reads the primitive as this quantity.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $primitive) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $primitive
        {
            /// Reads the quantity back out as its primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }

        impl fmt::Display for $name
        {
            /// Writes the quantity through its primitive's rendering.
            ///
            /// # Specification
            /// - requires: nothing.
            /// - ensures: writes the carried number through the primitive's
            ///   rendering, so the width and fill options the caller set
            ///   apply to it.
            /// - provides: the number a refusal or a measurement names.
            /// - fails: propagates the formatter's own write failure
            ///   unchanged.
            /// - panics: none.
            /// - executable: none — the formatter exposes no readable output
            ///   buffer for a postcondition.
            ///
            /// # Errors
            /// Returns `fmt::Error` when the sink refuses a write.
            ///
            /// # Adequacy
            /// - hypothesis: L2 on zero, 37 and the primitive ceiling for the
            ///   integer carriers listed in the witness compares signed,
            ///   zero-padded rendering with the primitive. L3 sink refusal
            ///   distinguishes swallowed errors. These fixed inputs distinguish
            ///   substituted values and lost flags, not every formatting mode.
            /// - witness: `units::tests::quantities_preserve_values_flags_and_refusal`
            #[inline]
            fn fmt(
                &self,
                f: &mut fmt::Formatter<'_>,
            ) -> fmt::Result
            {
                fmt::Display::fmt(&self.0, f)
            }
        }
    };
}

/// Declares a transparent wrapper over one borrowed byte slice.
macro_rules! borrowed_bytes {
    (
        $(#[$attribute:meta])*
        $visibility:vis struct $name:ident<$lifetime:lifetime>;
    ) => {
        $(#[$attribute])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        $visibility struct $name<$lifetime>(&$lifetime [u8]);

        impl<$lifetime> From<&$lifetime [u8]> for $name<$lifetime>
        {
            /// Reads a byte slice as this kind of bytes.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(bytes: &$lifetime [u8]) -> Self
            {
                Self(bytes)
            }
        }

        impl<$lifetime> From<$name<$lifetime>> for &$lifetime [u8]
        {
            /// Reads the bytes back out with their full lifetime.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(bytes: $name<$lifetime>) -> Self
            {
                bytes.0
            }
        }

        impl AsRef<[u8]> for $name<'_>
        {
            /// Borrows the bytes.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn as_ref(&self) -> &[u8]
            {
                self.0
            }
        }
    };
}

semantic_integer! {
    /// A number of distinct chunks a store holds or an edit added.
    pub struct ChunkCount(usize);
}

semantic_integer! {
    /// How many chunk seams a reader is inside at once.
    pub struct SeamDepth(usize);
}

semantic_integer! {
    /// One canonical sixty-four-bit payload word, the only integer width the
    /// token framing admits.
    pub struct CanonicalWord(u64);
}

semantic_integer! {
    /// The stable identifier of a value's token codec.
    pub struct CodecId(u16);
}

semantic_integer! {
    /// The layout version of a value's token codec.
    pub struct CodecVersion(u16);
}

semantic_integer! {
    /// The layout version of a chunk image's frame.
    pub struct ChunkFormatVersion(u16);
}

semantic_integer! {
    /// The layout version of a value manifest.
    pub struct ValueManifestVersion(u16);
}

impl ChunkFormatVersion
{
    /// The frame layout this build writes and reads.
    pub const V1: Self = Self(1_u16);
}

impl ValueManifestVersion
{
    /// The manifest layout this build describes values under.
    pub const V1: Self = Self(1_u16);
}

semantic_integer! {
    /// The constructor depth of an edited node: zero at the value's root.
    pub struct EditDepth(u64);
}

semantic_integer! {
    /// An expected number of affected chunks, as the locality bound states it.
    pub struct ChunkBound(u64);
}

semantic_integer! {
    /// Units of work a decode has spent: one per record, one per payload byte,
    /// and one per chunk-image byte verified on a seam.
    pub struct DecodeWork(u64);
}

impl DecodeWork
{
    /// No work.
    pub const ZERO: Self = Self(0_u64);

    /// One unit of work: the charge for reading one record.
    pub const ONE: Self = Self(1_u64);
}

/// The most work one decode may spend: two to the thirty-fourth units.
pub const MAX_DECODE_WORK: DecodeWork = DecodeWork(0x0004_0000_0000_u64);

borrowed_bytes! {
    /// A token body: a sequence of token records, as a chunk frames it and as
    /// the flat form carries it.
    pub struct TokenBody<'body>;
}

borrowed_bytes! {
    /// A framed chunk image: the domain, the frame header, then the body.
    pub struct ChunkImage<'image>;
}

borrowed_bytes! {
    /// A value manifest image: the domain, then the manifest's fields.
    pub struct ManifestImage<'image>;
}

borrowed_bytes! {
    /// An inline canonical byte payload.
    pub struct TokenBytes<'bytes>;
}

/// An owned framed chunk image.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ChunkImageBuf(Box<[u8]>);

impl ChunkImageBuf
{
    /// Borrows the image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn as_image(&self) -> ChunkImage<'_>
    {
        ChunkImage(self.0.as_ref())
    }
}

impl From<Box<[u8]>> for ChunkImageBuf
{
    /// Takes over framed image bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Box<[u8]>) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for ChunkImageBuf
{
    /// Borrows the image bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_ref()
    }
}

/// The owned flat form of one value: its canonical token body, with no store
/// and no seam.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FlatBytes(Box<[u8]>);

impl FlatBytes
{
    /// Borrows the flat form as a token body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn as_body(&self) -> TokenBody<'_>
    {
        TokenBody(self.0.as_ref())
    }
}

impl From<Box<[u8]>> for FlatBytes
{
    /// Takes over token body bytes as a flat form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Box<[u8]>) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for FlatBytes
{
    /// Borrows the flat bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_ref()
    }
}

/// An owned value manifest image.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ManifestImageBuf(Box<[u8]>);

impl ManifestImageBuf
{
    /// Borrows the image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn as_image(&self) -> ManifestImage<'_>
    {
        ManifestImage(self.0.as_ref())
    }
}

impl From<Box<[u8]>> for ManifestImageBuf
{
    /// Takes over manifest image bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Box<[u8]>) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for ManifestImageBuf
{
    /// Borrows the image bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_ref()
    }
}

#[cfg(test)]
mod tests
{
    /// A formatting sink that refuses every write.
    #[derive(Debug)]
    struct RefusingSink;

    impl core::fmt::Write for RefusingSink
    {
        /// Refuses the offered text.
        ///
        /// # Specification
        /// - requires: nothing; any text is admitted.
        /// - ensures: returns the formatting error for every write.
        /// - provides: the refusal observer for quantity rendering.
        /// - fails: always returns the formatting error.
        /// - panics: none.
        ///
        /// # Errors
        /// Always returns the formatting error.
        ///
        /// # Adequacy
        /// - hypothesis: L3 on text from the quantity boundary matrix observes
        ///   the exact error, distinguishing a sink that accepts a write.
        /// - witness: `units::tests::quantities_preserve_values_flags_and_refusal`
        #[anodized::spec(ensures: |ret| ret == Err(core::fmt::Error))]
        fn write_str(
            &mut self,
            _text: &str,
        ) -> core::fmt::Result
        {
            Err(core::fmt::Error)
        }
    }

    #[test]
    fn quantities_preserve_values_flags_and_refusal()
    {
        macro_rules! check {
            ($quantity:ty, $primitive:ty) => {
                for value in [0, 37, <$primitive>::MAX] {
                    let quantity = <$quantity>::from(value);
                    assert_eq!(
                        alloc::format!("{quantity:+022}"),
                        alloc::format!("{value:+022}"),
                    );
                    assert_eq!(
                        core::fmt::write(&mut RefusingSink, format_args!("{quantity}")),
                        Err(core::fmt::Error),
                    );
                }
            };
        }

        check!(super::ChunkCount, usize);
        check!(super::SeamDepth, usize);
        check!(super::CanonicalWord, u64);
        check!(super::CodecId, u16);
        check!(super::CodecVersion, u16);
        check!(super::ChunkFormatVersion, u16);
        check!(super::ValueManifestVersion, u16);
        check!(super::EditDepth, u64);
        check!(super::ChunkBound, u64);
        check!(super::DecodeWork, u64);
    }
}
