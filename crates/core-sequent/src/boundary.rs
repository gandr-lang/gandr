//! The crate's own boundary wrappers: every index, count and verdict a
//! signature of this crate crosses, so no signature passes a bare primitive.
//!
//! Each wrapper is transparent and converts with the standard `From` traits,
//! so a primitive is unpacked only where a comparison or a count needs it.
//! Identifiers are `u32` addresses, matching the core arena's ids; counts are
//! `usize`.

use core::fmt;

/// Defines a transparent copyable newtype over one `usize`, with `From`
/// conversions both ways and `Display` passthrough.
macro_rules! count_wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        $vis struct $name(usize);

        impl From<usize> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: usize) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for usize
        {
            /// Unwraps the primitive.
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
            /// Writes the wrapped number.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn fmt(
                &self,
                f: &mut fmt::Formatter<'_>,
            ) -> fmt::Result
            {
                self.0.fmt(f)
            }
        }
    };
}

/// Defines a transparent copyable newtype over one `u32` index, with `From`
/// conversions both ways and `Display` passthrough.
macro_rules! index_wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        $vis struct $name(u32);

        impl From<u32> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: u32) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for u32
        {
            /// Unwraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }

        impl core::fmt::Display for $name
        {
            /// Writes the wrapped number.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn fmt(
                &self,
                f: &mut core::fmt::Formatter<'_>,
            ) -> core::fmt::Result
            {
                self.0.fmt(f)
            }
        }
    };
}

/// Defines a transparent copyable newtype over one `u32` address into a
/// family vector, with `From` conversions both ways, `Display` passthrough,
/// and the two crate-private family operations every arena and region shares:
/// the next address an append takes, and the checked read of an address.
macro_rules! address_wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $crate::boundary::index_wrapper! {
            $(#[$meta])*
            $vis struct $name;
        }

        impl $name
        {
            /// The address the next node appended to `family` takes, or `None`
            /// once the family holds `u32::MAX` nodes.
            ///
            /// # Specification
            /// - requires: nothing.
            /// - ensures: `Some(address)` naming offset `family.len()` below
            ///   the ceiling, so an append never reuses an address.
            /// - provides: the refusal point every append goes through.
            /// - fails: `None` at the ceiling.
            /// - panics: none.
            #[inline]
            pub(crate) fn next_in<Node>(family: &[Node]) -> Option<Self>
            {
                u32::try_from(family.len())
                    .ok()
                    .filter(|&address| address < u32::MAX)
                    .map(Self)
            }

            /// The node this address names in `family`, or `None` when it
            /// dangles.
            ///
            /// # Specification
            /// - requires: nothing; a dangling address is admissible.
            /// - ensures: `Some(node)` exactly when the address is an offset
            ///   `family` still holds.
            /// - provides: the one checked read of a family.
            /// - fails: `None` past the end, including an address a truncation
            ///   dropped.
            /// - panics: none.
            #[inline]
            pub(crate) fn read_in<Node>(
                self,
                family: &[Node],
            ) -> Option<&Node>
            {
                usize::try_from(self.0)
                    .ok()
                    .and_then(|offset| family.get(offset))
            }
        }
    };
}

pub(crate) use address_wrapper;
pub(crate) use index_wrapper;

count_wrapper! {
    /// How many producer children a constructor or destructor head declares.
    pub struct ProducerArity;
}

count_wrapper! {
    /// How many consumer children a constructor or destructor head declares.
    pub struct ConsumerArity;
}

count_wrapper! {
    /// The population of one node family: of an arena, a heap region or the
    /// frame region.
    pub struct NodeCount;
}

count_wrapper! {
    /// The height of the frame region: how many frames it holds.
    pub struct FrameHeight;
}

count_wrapper! {
    /// The serial a frame is pushed under. Serials strictly increase, so a
    /// frame popped and replaced at the same height carries a new serial.
    pub struct FrameSerial;
}

count_wrapper! {
    /// A number of machine transitions: the budget a run may spend.
    pub struct StepCount;
}

impl ProducerArity
{
    /// No producer children.
    pub const ZERO: Self = Self(0);
    /// One producer child.
    pub const ONE: Self = Self(1);
    /// Two producer children.
    pub const TWO: Self = Self(2);
}

impl ConsumerArity
{
    /// No consumer children.
    pub const ZERO: Self = Self(0);
    /// One consumer child.
    pub const ONE: Self = Self(1);
}

impl FrameHeight
{
    /// The empty region's height.
    pub const ZERO: Self = Self(0);
}

impl FrameSerial
{
    /// The serial below every frame: the base of the region.
    pub const BASE: Self = Self(0);
}
