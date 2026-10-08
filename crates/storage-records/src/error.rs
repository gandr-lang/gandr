//! The crate's single typed failure vocabulary, [`RecordTreeError`].

use core::error::Error;
use core::fmt;

use crate::bytes::NodeHash;
use crate::record::RecordIndex;

/// A static phrase naming which part of a structure was rejected.
///
/// The phrase is a compile-time constant chosen at the rejection site, so an
/// error carries the site's own words without allocating and without a format
/// argument that could vary per run.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FailureContext(&'static str);

impl From<&'static str> for FailureContext
{
    /// Read a static phrase as a rejection site's context.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(context: &'static str) -> Self
    {
        Self(context)
    }
}

impl From<FailureContext> for &'static str
{
    /// Read the context phrase back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(context: FailureContext) -> Self
    {
        context.0
    }
}

impl fmt::Display for FailureContext
{
    /// Write the context phrase.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes exactly the phrase the rejection site chose, neither
    ///   quoted nor reworded.
    /// - provides: the site's own words inside a refusal's message, with no
    ///   allocation and no per-run format argument.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

/// A wire-format version number read out of encoded bytes.
///
/// The value is whatever the bytes said, so it is reported rather than
/// interpreted: an unsupported version is a refusal, never a fallback.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireVersion(pub u16);

impl From<u16> for WireVersion
{
    /// Read a `u16` as the version the bytes declared.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: u16) -> Self
    {
        Self(version)
    }
}

impl From<WireVersion> for u16
{
    /// Read the declared version back out as a `u16`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: WireVersion) -> Self
    {
        version.0
    }
}

impl fmt::Display for WireVersion
{
    /// Write the declared version.
    ///
    /// # Specification
    /// - requires: nothing; every value the bytes could have declared renders,
    ///   supported or not.
    /// - ensures: writes the number through the `u16` rendering, so the width
    ///   and fill options the caller set apply to it.
    /// - provides: the number a version refusal reports, uninterpreted.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        u16::from(*self).fmt(f)
    }
}

/// Every way this crate refuses an input.
///
/// Refusal is the crate's only failure mode: no operation panics, no operation
/// silently repairs a malformed structure, and no operation admits material it
/// could not authenticate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RecordTreeError
{
    /// Input records were not in strictly increasing key order.
    UnsortedInput
    {
        /// Position of the record preceding the violation.
        previous: RecordIndex,
        /// Position of the first record observed out of order.
        current: RecordIndex,
    },

    /// Two records carried the same key.
    DuplicateKeys
    {
        /// Position of the first record carrying the key.
        first: RecordIndex,
        /// Position of the later record carrying the key.
        second: RecordIndex,
    },

    /// Encoded node bytes were truncated, mis-framed, or not canonical.
    MalformedNode
    {
        /// The rejected part of the encoding.
        context: FailureContext,
    },

    /// A node hash was not present in the store it was requested from.
    UnknownNode
    {
        /// The absent identity.
        hash: NodeHash,
    },

    /// Bytes did not hash to the identity claimed for them.
    HashMismatch
    {
        /// The identity the bytes were offered under.
        expected: NodeHash,
        /// The identity recomputed from the bytes.
        actual: NodeHash,
    },

    /// Tree parameters were incompatible with a root, node, store, or proof.
    IncompatibleParameters
    {
        /// The disagreeing parameter.
        context: FailureContext,
    },

    /// Encoded material named an encoding version this build does not accept.
    UnsupportedVersion
    {
        /// The version the bytes named.
        version: WireVersion,
    },

    /// Proof material had a shape the requested verification cannot accept.
    InvalidProofShape
    {
        /// The rejected part of the proof.
        context: FailureContext,
    },

    /// A key range was reversed or otherwise uninhabitable.
    InvalidRange
    {
        /// The rejected relation between the bounds.
        context: FailureContext,
    },

    /// A decode budget was exhausted before the structure was consumed.
    ///
    /// The budgets bound the work a small input can force, so exhaustion is a
    /// refusal of the input rather than a resource condition of the process.
    BudgetExceeded
    {
        /// The budget that was exhausted.
        context: FailureContext,
    },

    /// A count, length, or offset did not fit the width it had to occupy.
    ///
    /// Every arithmetic step in the crate is checked, so an overflow surfaces
    /// here instead of wrapping into a wrong answer.
    ArithmeticOverflow
    {
        /// The quantity that did not fit.
        context: FailureContext,
    },
}

impl fmt::Display for RecordTreeError
{
    /// Write the refusal and the values it names.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one message per variant, each naming the context
    ///   phrase, count, index, or version its payload carries, so no two
    ///   variants render alike and no refusal renders as a repair.
    /// - provides: the operator-facing sentence a caller prints, and the
    ///   [`Error`] rendering the trait implementation below inherits.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::UnsortedInput { previous, current } => {
                write!(
                    f,
                    "input records are unsorted between positions {previous} and {current}"
                )
            },
            | Self::DuplicateKeys { first, second } => {
                write!(f, "duplicate key at positions {first} and {second}")
            },
            | Self::MalformedNode { context } => {
                write!(f, "node bytes are malformed: {context}")
            },
            | Self::UnknownNode { hash } => {
                write!(f, "node is unknown to the store: {hash}")
            },
            | Self::HashMismatch { expected, actual } => {
                write!(f, "hash mismatch: expected {expected}, recomputed {actual}")
            },
            | Self::IncompatibleParameters { context } => {
                write!(f, "tree parameters are incompatible: {context}")
            },
            | Self::UnsupportedVersion { version } => {
                write!(f, "encoding version is unsupported: {version}")
            },
            | Self::InvalidProofShape { context } => {
                write!(f, "proof shape is invalid: {context}")
            },
            | Self::InvalidRange { context } => {
                write!(f, "key range is invalid: {context}")
            },
            | Self::BudgetExceeded { context } => {
                write!(f, "decode budget is exhausted: {context}")
            },
            | Self::ArithmeticOverflow { context } => {
                write!(f, "value does not fit its width: {context}")
            },
        }
    }
}

impl Error for RecordTreeError
{
}
