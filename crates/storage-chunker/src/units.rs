//! The semantic wrappers every chunker signature is stated in.
//!
//! A byte count, a byte position, a record count and a token count are all
//! integers, and on a content-defined plane swapping two of them moves a cut
//! rather than crashing. Each gets its own type so the compiler refuses the
//! swap.

use core::fmt;

use crate::error::ArithmeticOperation;
use crate::error::ChunkerError;

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
            /// - provides: the number a refusal names.
            /// - fails: propagates the formatter's own write failure
            ///   unchanged.
            /// - panics: none.
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

semantic_integer! {
    /// A number of canonical bytes: a chunk limit or a measured length.
    pub struct ByteCount(u64);
}

semantic_integer! {
    /// A position in a canonical byte stream.
    pub struct BytePosition(u64);
}

semantic_integer! {
    /// A number of records inside one chunk.
    pub struct RecordCount(u32);
}

semantic_integer! {
    /// A position in canonical record order.
    pub struct RecordPosition(u64);
}

semantic_integer! {
    /// A number of canonical tokens.
    pub struct TokenCount(u64);
}

semantic_integer! {
    /// The rolling hash a caller reports for the subtree a boundary event
    /// closes.
    ///
    /// The chunker never computes one: the residue is the caller's, taken
    /// under whatever hash the caller's own commitment names, and the chunker
    /// only asks whether it is divisible by kappa.
    pub struct BoundaryResidue(u64);
}

impl ByteCount
{
    /// The empty byte count.
    pub const ZERO: Self = Self(0_u64);

    /// Adds two byte counts, refusing a sum past the width.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the exact sum.
    /// - provides: the checked addition a chunk's running size advances by.
    /// - fails: [`ChunkerError::ArithmeticOverflow`] naming `operation` when
    ///   the sum exceeds `u64`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::ArithmeticOverflow`] — the sum exceeds `u64`.
    pub(crate) fn checked_plus(
        self,
        other: Self,
        operation: ArithmeticOperation,
    ) -> Result<Self, ChunkerError>
    {
        self.0
            .checked_add(other.0)
            .map(Self)
            .ok_or(ChunkerError::ArithmeticOverflow { operation })
    }
}

impl BytePosition
{
    /// The start of a byte stream.
    pub const ZERO: Self = Self(0_u64);

    /// Advances a position by a byte count, refusing a position past the
    /// width.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the position `count` bytes later.
    /// - provides: the checked step from a record's start to its end.
    /// - fails: [`ChunkerError::ArithmeticOverflow`] naming `operation` when
    ///   the position exceeds `u64`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::ArithmeticOverflow`] — the position exceeds `u64`.
    pub(crate) fn checked_advance(
        self,
        count: ByteCount,
        operation: ArithmeticOperation,
    ) -> Result<Self, ChunkerError>
    {
        self.0
            .checked_add(count.0)
            .map(Self)
            .ok_or(ChunkerError::ArithmeticOverflow { operation })
    }

    /// Measures the bytes from an earlier position to this one.
    ///
    /// # Specification
    /// - requires: nothing; a `start` past `self` is the refused case.
    /// - ensures: on success the exact distance `self - start`.
    /// - provides: a record's length from its two edges.
    /// - fails: [`ChunkerError::ArithmeticOverflow`] naming `operation` when
    ///   `start` lies after `self`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::ArithmeticOverflow`] — `start` lies after `self`.
    pub(crate) fn checked_distance_from(
        self,
        start: Self,
        operation: ArithmeticOperation,
    ) -> Result<ByteCount, ChunkerError>
    {
        self.0
            .checked_sub(start.0)
            .map(ByteCount)
            .ok_or(ChunkerError::ArithmeticOverflow { operation })
    }
}

impl RecordCount
{
    /// The empty record count.
    pub const ZERO: Self = Self(0_u32);

    /// Counts one more record, refusing a count past the width.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the count plus one.
    /// - provides: the checked step a chunk's record count advances by.
    /// - fails: [`ChunkerError::ArithmeticOverflow`] naming `operation` when
    ///   the count exceeds `u32`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::ArithmeticOverflow`] — the count exceeds `u32`.
    pub(crate) fn checked_increment(
        self,
        operation: ArithmeticOperation,
    ) -> Result<Self, ChunkerError>
    {
        self.0
            .checked_add(1_u32)
            .map(Self)
            .ok_or(ChunkerError::ArithmeticOverflow { operation })
    }
}

impl RecordPosition
{
    /// The first position in record order.
    pub const ZERO: Self = Self(0_u64);

    /// Advances a position past `count` records, refusing a position past the
    /// width.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the position `count` records later.
    /// - provides: the end of a chunk's record span from its start and size.
    /// - fails: [`ChunkerError::ArithmeticOverflow`] for a record index when
    ///   the position exceeds `u64`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::ArithmeticOverflow`] — the position exceeds `u64`.
    pub(crate) fn checked_advance(
        self,
        count: RecordCount,
    ) -> Result<Self, ChunkerError>
    {
        self.0
            .checked_add(u64::from(count.0))
            .map(Self)
            .ok_or(ChunkerError::ArithmeticOverflow {
                operation: ArithmeticOperation::RecordIndex,
            })
    }

    /// Advances to the next record position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the position plus one.
    /// - provides: the step a scan takes per consumed record.
    /// - fails: [`ChunkerError::ArithmeticOverflow`] for a record index when
    ///   the position exceeds `u64`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::ArithmeticOverflow`] — the position exceeds `u64`.
    pub(crate) fn checked_next(self) -> Result<Self, ChunkerError>
    {
        self.checked_advance(RecordCount(1_u32))
    }
}

impl TokenCount
{
    /// No tokens.
    pub const ZERO: Self = Self(0_u64);

    /// One token.
    pub const ONE: Self = Self(1_u64);

    /// Adds two token counts, saturating at the width.
    ///
    /// Saturation is the safe direction for the one use this has: a pending
    /// count compared against a cap, where a saturated count reaches the cap
    /// and cuts, and never wraps below it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the sum when it fits `u64`, and `u64::MAX` otherwise.
    /// - provides: the pending-token accumulation the typed cap fires on.
    /// - fails: never.
    /// - panics: none.
    #[must_use]
    pub(crate) const fn saturating_plus(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(other.0))
    }
}
