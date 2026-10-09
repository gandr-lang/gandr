//! The crate's single typed failure vocabulary, [`ValueError`].

use core::error::Error;
use core::fmt;

use gandr_storage_chunker::TokenCount;

use crate::index_base::ChildIndexBase;
use crate::ptr::ChunkDigest;
use crate::ptr::TokenOffset;
use crate::tokens::ConstructorTag;
use crate::tokens::TokenKind;
use crate::units::DecodeWork;

/// The part of a chunk frame a refusal names.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ChunkFrameField
{
    /// The image does not open with the chunk domain.
    Domain,
    /// The frame names a layout version this build does not read.
    Version,
    /// The image ends inside the frame header.
    Header,
    /// The declared body length is not the number of bytes that follow.
    BodyLength,
    /// The body is not a sequence of well-formed token records.
    Records,
    /// The declared token count is not the number of records in the body.
    TokenCount,
}

impl fmt::Display for ChunkFrameField
{
    /// Writes the refused part of the frame.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - provides: the field a malformed-chunk refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Domain => "the image does not open with the value-chunk domain",
            | Self::Version => "the frame names an unsupported layout version",
            | Self::Header => "the image ends inside the frame header",
            | Self::BodyLength => "the declared body length does not match the image",
            | Self::Records => "the body is not a sequence of well-formed token records",
            | Self::TokenCount => "the declared token count does not match the body",
        })
    }
}

/// The field of a manifest image a refusal names, in image order.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ManifestField
{
    /// The domain the image opens with.
    Domain,
    /// The manifest layout version.
    ManifestVersion,
    /// The length prefix of the chunker commitment.
    CommitmentLength,
    /// The chunker commitment the length prefix counts.
    ChunkerCommitment,
    /// The digest family's tag.
    DigestFamily,
    /// The codec's identifier.
    CodecId,
    /// The codec's layout version.
    CodecVersion,
    /// The child index base's tag.
    ChildIndexBase,
    /// The boundary classification's tag.
    BoundaryClassification,
    /// The chunk frame layout version.
    ChunkFrameVersion,
    /// The root pointer's chunk digest.
    RootDigest,
    /// The root pointer's token offset.
    RootOffset,
    /// The value's token count.
    TokenCount,
}

impl fmt::Display for ManifestField
{
    /// Writes the refused field.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - provides: the field a manifest refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Domain => "the domain",
            | Self::ManifestVersion => "the manifest version",
            | Self::CommitmentLength => "the chunker commitment's length",
            | Self::ChunkerCommitment => "the chunker commitment",
            | Self::DigestFamily => "the digest family",
            | Self::CodecId => "the codec identifier",
            | Self::CodecVersion => "the codec version",
            | Self::ChildIndexBase => "the child index base",
            | Self::BoundaryClassification => "the boundary classification",
            | Self::ChunkFrameVersion => "the chunk frame version",
            | Self::RootDigest => "the root digest",
            | Self::RootOffset => "the root offset",
            | Self::TokenCount => "the token count",
        })
    }
}

/// The field of a value profile a reader's expectation can differ in, in
/// manifest image order.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ProfileField
{
    /// The typed chunker parameters, compared as their commitment.
    ChunkerCommitment,
    /// The digest family.
    DigestFamily,
    /// The codec's identifier.
    CodecId,
    /// The codec's layout version.
    CodecVersion,
    /// The child index base.
    ChildIndexBase,
    /// The boundary classification.
    BoundaryClassification,
    /// The chunk frame layout version.
    ChunkFrameVersion,
}

impl fmt::Display for ProfileField
{
    /// Writes the differing field.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - provides: the field an incompatible-profile refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::ChunkerCommitment => "the chunker commitment",
            | Self::DigestFamily => "the digest family",
            | Self::CodecId => "the codec identifier",
            | Self::CodecVersion => "the codec version",
            | Self::ChildIndexBase => "the child index base",
            | Self::BoundaryClassification => "the boundary classification",
            | Self::ChunkFrameVersion => "the chunk frame version",
        })
    }
}

/// The way a value's emission broke the one-balanced-value shape a sink
/// requires.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EmissionFault
{
    /// A close arrived with no constructor open.
    CloseWithoutOpen,
    /// A payload or a child arrived with no constructor open.
    PayloadOutsideConstructor,
    /// A second value opened after the first one closed.
    SecondRoot,
    /// The emission ended with a constructor still open.
    UnclosedConstructor,
    /// The emission produced no token at all.
    EmptyValue,
}

impl fmt::Display for EmissionFault
{
    /// Writes the broken shape.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - provides: the fault a malformed-emission refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::CloseWithoutOpen => "a close arrived with no constructor open",
            | Self::PayloadOutsideConstructor => "a payload arrived with no constructor open",
            | Self::SecondRoot => "a second value opened after the first closed",
            | Self::UnclosedConstructor => "the emission ended inside a constructor",
            | Self::EmptyValue => "the emission produced no token",
        })
    }
}

/// The quantity whose checked arithmetic overflowed.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ValueQuantity
{
    /// A token offset inside one body.
    TokenOffset,
    /// A token count.
    TokenCount,
    /// A payload or body byte length.
    ByteLength,
    /// A count of chunks.
    ChunkCount,
    /// The locality bound.
    LocalityBound,
}

impl fmt::Display for ValueQuantity
{
    /// Writes the quantity that overflowed.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - provides: the quantity an overflow refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::TokenOffset => "token offset",
            | Self::TokenCount => "token count",
            | Self::ByteLength => "byte length",
            | Self::ChunkCount => "chunk count",
            | Self::LocalityBound => "locality bound",
        })
    }
}

/// Every way the value plane refuses an input.
///
/// Refusal is the crate's only failure mode: no operation panics, and no
/// operation repairs a chunk, a stream or an emission it was handed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueError
{
    /// The store holds no chunk under the digest.
    UnknownChunk
    {
        /// The digest asked for.
        digest: ChunkDigest,
    },

    /// A chunk image does not hash to the digest it was offered under.
    DigestMismatch
    {
        /// The digest claimed.
        expected: ChunkDigest,
        /// The digest the image hashes to.
        actual: ChunkDigest,
    },

    /// A chunk image's frame is not the frame this crate writes.
    MalformedChunk
    {
        /// The part of the frame refused.
        field: ChunkFrameField,
    },

    /// A token stream ended inside a record or before the value did.
    TruncatedStream
    {
        /// The record position where the stream ran out.
        position: TokenOffset,
    },

    /// A record opened with a byte that names no token kind.
    UnknownTokenKind
    {
        /// The record position of the unknown kind.
        position: TokenOffset,
    },

    /// A record of one kind stood where another kind was required.
    UnexpectedToken
    {
        /// The kind required.
        expected: TokenKind,
        /// The kind found.
        found: TokenKind,
        /// The record position.
        position: TokenOffset,
    },

    /// A value's decoder met a constructor tag it does not admit.
    UnexpectedConstructor
    {
        /// The tag found.
        found: ConstructorTag,
        /// The record position the decoder reports.
        position: TokenOffset,
    },

    /// A child record appeared in a flat form, which has no store to resolve
    /// it against.
    SeamInFlatForm
    {
        /// The record position of the child record.
        position: TokenOffset,
    },

    /// A flat form continued past the end of its value.
    TrailingTokens
    {
        /// The record position where the value ended.
        position: TokenOffset,
    },

    /// A value's emission was not one balanced value.
    MalformedEmission
    {
        /// The broken shape.
        fault: EmissionFault,
    },

    /// A child-reference representation this traversal cannot produce.
    UnsupportedIndexBase
    {
        /// The representation asked for.
        base: ChildIndexBase,
    },

    /// Checked arithmetic overflowed.
    ArithmeticOverflow
    {
        /// The quantity that overflowed.
        quantity: ValueQuantity,
    },

    /// A decode spent more work than the total budget admits.
    DecodeBudgetExceeded
    {
        /// The work the decode would have spent.
        spent: DecodeWork,
        /// The budget's ceiling.
        ceiling: DecodeWork,
    },

    /// A manifest image's field holds a value this build does not read: a
    /// foreign domain, an unknown version or tag, or a chunker commitment that
    /// is not a typed one.
    MalformedManifest
    {
        /// The field refused.
        field: ManifestField,
    },

    /// A manifest image ended inside a field.
    TruncatedManifest
    {
        /// The field the image ended inside.
        field: ManifestField,
    },

    /// A manifest image continued past its last field.
    TrailingManifestBytes,

    /// A manifest's profile differs from the profile its reader expects.
    IncompatibleProfile
    {
        /// The first field, in manifest image order, that differs.
        field: ProfileField,
    },

    /// A manifest's token count is not the number of records its closure
    /// delivers.
    TokenCountMismatch
    {
        /// The count the manifest declares.
        declared: TokenCount,
        /// The records a reader of the root delivers, child chunks spliced.
        spliced: TokenCount,
    },
}

impl fmt::Display for ValueError
{
    /// Writes the refusal and the values it names.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one message per variant, each naming the digest,
    ///   field, kind, position, fault, quantity or counts its payload carries,
    ///   so no two variants render alike.
    /// - provides: the operator-facing sentence a caller prints, and the
    ///   [`Error`] rendering the implementation below inherits.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::UnknownChunk { digest } => write!(f, "no chunk is stored under {digest}"),
            | Self::DigestMismatch { expected, actual } => {
                write!(f, "a chunk offered as {expected} hashes to {actual}")
            },
            | Self::MalformedChunk { field } => write!(f, "malformed chunk: {field}"),
            | Self::TruncatedStream { position } => {
                write!(f, "the token stream ends inside record {position}")
            },
            | Self::UnknownTokenKind { position } => {
                write!(f, "record {position} opens with an unknown token kind")
            },
            | Self::UnexpectedToken {
                expected,
                found,
                position,
            } => {
                write!(
                    f,
                    "record {position} is {found} where {expected} was required"
                )
            },
            | Self::UnexpectedConstructor { found, position } => {
                write!(
                    f,
                    "record {position} opens constructor {found}, which the decoder does not admit"
                )
            },
            | Self::SeamInFlatForm { position } => {
                write!(
                    f,
                    "record {position} is a child record, which a flat form cannot carry"
                )
            },
            | Self::TrailingTokens { position } => {
                write!(
                    f,
                    "the flat form continues past its value at record {position}"
                )
            },
            | Self::MalformedEmission { fault } => write!(f, "malformed emission: {fault}"),
            | Self::UnsupportedIndexBase { base } => {
                write!(
                    f,
                    "the {base} child index base is not representable in this encoding"
                )
            },
            | Self::ArithmeticOverflow { quantity } => {
                write!(f, "arithmetic overflowed computing a {quantity}")
            },
            | Self::DecodeBudgetExceeded { spent, ceiling } => {
                write!(
                    f,
                    "a decode would spend {spent} units of work, past the budget of {ceiling}"
                )
            },
            | Self::MalformedManifest { field } => {
                write!(f, "a manifest image holds {field} this build does not read")
            },
            | Self::TruncatedManifest { field } => {
                write!(f, "a manifest image ends inside {field}")
            },
            | Self::TrailingManifestBytes => {
                f.write_str("a manifest image continues past its token count")
            },
            | Self::IncompatibleProfile { field } => {
                write!(
                    f,
                    "the manifest's profile differs from the expected one in {field}"
                )
            },
            | Self::TokenCountMismatch { declared, spliced } => {
                write!(
                    f,
                    "a manifest declares {declared} tokens where its closure delivers {spliced}"
                )
            },
        }
    }
}

impl Error for ValueError
{
}
