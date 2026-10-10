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
    /// - hypothesis: L3 — empty and ordinary slices expose reused or shifted
    ///   addresses; zero-sized slices immediately below and at `u32::MAX`
    ///   expose an inclusive ceiling without allocating node storage. The
    ///   observer is the exact optional address; arbitrary implementations with
    ///   lossy conversions are excluded.
    /// - witness: `boundary::tests::addresses_refuse_exactly_at_the_u32_ceiling`
    #[inline]
    #[anodized::spec(ensures: |ret| match ret {
        | Some(address) => {
            let offset: u32 = address.into();
            usize::try_from(offset) == Ok(family.len()) && offset < u32::MAX
        },
        | None => u32::try_from(family.len()).is_err()
            || u32::try_from(family.len()) == Ok(u32::MAX),
    })]
    fn next_in<Node>(family: &[Node]) -> Option<Self>
    {
        u32::try_from(family.len())
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
    ///   retained stale nodes. The observer is the exact borrowed node or
    ///   absence; arbitrary implementations with lossy conversions are
    ///   excluded.
    /// - witness: `boundary::tests::address_reads_distinguish_end_and_truncation`
    #[inline]
    #[anodized::spec(
        captures: [offset = Into::<u32>::into(self)],
        ensures: |ret| match ret {
            | Some(node) => usize::try_from(offset).ok()
                .and_then(|index| family.get(index))
                .is_some_and(|held| core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(node))),
            | None => usize::try_from(offset).map_or(true, |index| index >= family.len()),
        },
    )]
    fn read_in<Node>(
        self,
        family: &[Node],
    ) -> Option<&Node>
    {
        family.get(usize::try_from(Into::<u32>::into(self)).ok()?)
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

#[cfg(test)]
mod tests
{
    use super::FamilyAddress as _;
    use crate::il::ProducerId;

    /// The excluded address ceiling is reached without allocating node bytes.
    #[test]
    fn addresses_refuse_exactly_at_the_u32_ceiling()
    {
        assert_eq!(
            Some(ProducerId::from(0_u32)),
            ProducerId::next_in::<()>(&[])
        );
        assert_eq!(
            Some(ProducerId::from(2_u32)),
            ProducerId::next_in(&[(), ()])
        );
        let ceiling = usize::try_from(u32::MAX).expect("the address ceiling fits usize");
        let mut family = alloc::vec![(); ceiling];
        assert_eq!(None, ProducerId::next_in(&family));
        family.pop().expect("the ceiling is positive");
        assert_eq!(
            Some(ProducerId::from(u32::MAX.saturating_sub(1))),
            ProducerId::next_in(&family),
        );
    }

    /// Reads distinguish the last live slot from the exact end and a dropped
    /// slot.
    #[test]
    fn address_reads_distinguish_end_and_truncation()
    {
        let mut family = alloc::vec![11_u32, 29_u32];
        let first = ProducerId::from(0_u32);
        let last = ProducerId::from(1_u32);
        assert_eq!(Some(&11_u32), first.read_in(&family));
        assert_eq!(Some(&29_u32), last.read_in(&family));
        assert_eq!(None, ProducerId::from(2_u32).read_in(&family));
        family.truncate(1);
        assert_eq!(Some(&11_u32), first.read_in(&family));
        assert_eq!(None, last.read_in(&family));
        family.clear();
        assert_eq!(None, first.read_in(&family));
    }
}
