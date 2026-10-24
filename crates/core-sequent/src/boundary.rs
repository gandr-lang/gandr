//! The crate's own boundary wrappers: every index, count and verdict a
//! signature of this crate crosses, so no signature passes a bare primitive.
//!
//! Each wrapper is transparent and converts with the standard `From` traits,
//! so a primitive is unpacked only where a comparison or a count needs it.
//! Identifiers are `u32` addresses, matching the core arena's ids; counts are
//! `usize`.

use core::fmt;

use anodized::spec;
use gandr_kernel_term::ArenaLength;
use gandr_kernel_term::Family;

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

/// Defines a transparent address and implements its checked family operations.
macro_rules! address_wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $crate::boundary::index_wrapper! {
            $(#[$meta])*
            $vis struct $name;
        }

        impl $crate::boundary::FamilyAddress for $name {}
    };
}

/// Checked family operations for the crate's transparent `u32` addresses.
pub trait FamilyAddress: Copy + From<u32> + Into<u32>
{
    /// The address the next node appended to `family` takes, or `None`
    /// once the family holds `u32::MAX` nodes.
    ///
    /// # Specification
    /// - requires: the address's conversions preserve its `u32` offset.
    /// - ensures: `Some(address)` naming offset `family.len()` below the
    ///   ceiling, so an append never reuses an address.
    /// - provides: the refusal point every append goes through.
    /// - fails: `None` at or above the ceiling.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and ordinary families expose reused or shifted
    ///   addresses; families of zero-sized nodes immediately below and at
    ///   `u32::MAX` expose an inclusive ceiling without allocating node
    ///   storage. The observer is the exact optional address; arbitrary
    ///   implementations with lossy conversions are excluded.
    /// - witness: `boundary::tests::addresses_refuse_exactly_at_the_u32_ceiling`
    #[inline]
    #[spec(ensures: |ret| match ret {
        | Some(address) => {
            let offset: u32 = address.into();
            usize::try_from(offset) == Ok(usize::from(family.len())) && offset < u32::MAX
        },
        | None => u32::try_from(usize::from(family.len())).is_err()
            || u32::try_from(usize::from(family.len())) == Ok(u32::MAX),
    })]
    fn next_in<Node>(family: &Family<Node>) -> Option<Self>
    {
        u32::try_from(usize::from(family.len()))
            .ok()
            .filter(|&address| address < u32::MAX)
            .map(Self::from)
    }

    /// The node this address names in `family`, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: the address's conversion preserves its `u32` offset; a
    ///   dangling address is admissible.
    /// - ensures: `Some(node)` exactly when the address is an offset `family`
    ///   still holds.
    /// - provides: the one checked read of a family.
    /// - fails: `None` past the end, including an address a truncation dropped.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct first and last nodes, the exact end and a
    ///   truncated address distinguish shifted reads, an inclusive endpoint and
    ///   retained stale nodes, in a family with nothing frozen and in one
    ///   frozen part way. The observer is the exact borrowed node or absence;
    ///   arbitrary implementations with lossy conversions are excluded.
    /// - witness: `boundary::tests::address_reads_distinguish_end_and_truncation`
    #[inline]
    #[spec(
        captures: [offset = Into::<u32>::into(self)],
        ensures: |ret| match ret {
            | Some(node) => usize::try_from(offset).ok()
                .and_then(|index| family.get(ArenaLength::from(index)))
                .is_some_and(|held| core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(node))),
            | None => usize::try_from(offset).map_or(true, |index| index >= usize::from(family.len())),
        },
    )]
    fn read_in<Node>(
        self,
        family: &Family<Node>,
    ) -> Option<&Node>
    {
        family.get(ArenaLength::from(
            usize::try_from(Into::<u32>::into(self)).ok()?,
        ))
    }
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
    /// The population of one node family: of an arena or of the store's
    /// values.
    pub struct NodeCount;
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

#[cfg(test)]
mod tests;
