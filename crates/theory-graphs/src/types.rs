//! The graph-domain names primitive quantities cross a boundary under: dense
//! node identities and counts, edge and component identities, walk heights
//! and chain lengths, and the fingerprint words.
//!
//! Every wrapper is transparent and converts with the standard `From` traits,
//! so a primitive is unpacked only where arithmetic or indexing needs it.

use core::fmt::Display;
use core::fmt::Formatter;
use core::fmt::Result as FmtResult;
use core::num::TryFromIntError;

use anodized::spec;

/// Defines a transparent newtype over one primitive with `From` conversions
/// both ways; the `display` arm adds a `Display` that writes the primitive.
macro_rules! primitive_newtype {
    ($(#[$meta:meta])* $vis:vis struct $name:ident($raw:ty);) => {
        $(#[$meta])*
        #[repr(transparent)]
        $vis struct $name($raw);

        impl From<$raw> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $raw) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $raw
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
    };
    (display $(#[$meta:meta])* $vis:vis struct $name:ident($raw:ty);) => {
        $crate::types::primitive_newtype! { $(#[$meta])* $vis struct $name($raw); }

        impl core::fmt::Display for $name
        {
            /// Writes the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn fmt(
                &self,
                f: &mut core::fmt::Formatter<'_>,
            ) -> core::fmt::Result
            {
                core::fmt::Display::fmt(&self.0, f)
            }
        }
    };
}

pub(crate) use primitive_newtype;

primitive_newtype! {
    display
    /// A dense graph node identity: a graph of `n` nodes names them `0..n`.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct NodeId(u32);
}

primitive_newtype! {
    display
    /// The dense node bound of a graph: its nodes are exactly `0..count`.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct NodeCount(u32);
}

impl NodeCount
{
    /// Returns every dense node id in ascending order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ids(self) -> NodeIdRange
    {
        NodeIdRange {
            next: 0,
            end: self.0,
        }
    }
}

/// The ascending dense node ids of one [`NodeCount`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeIdRange
{
    /// Next raw id to yield.
    next: u32,
    /// Exclusive raw id bound.
    end: u32,
}

impl Iterator for NodeIdRange
{
    type Item = NodeId;

    /// Yields the next id below the bound.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields `next` and advances it while `next < end`; once `next`
    ///   reaches `end` every call yields nothing.
    /// - provides: the ascending enumeration every algorithm visits sources in.
    /// - panics: none; the advance saturates at `end`.
    ///
    /// # Adequacy
    /// - hypothesis: For dense ranges, L3 observations distinguish skipping or
    ///   repeating an id, crossing the exclusive bound, and resuming after
    ///   exhaustion. Zero and the last representable bound are covered; the
    ///   contract concerns enumeration, not an exact-size iterator guarantee.
    /// - witness: `types::tests::node_ids_advance_and_remain_exhausted`
    #[spec(
        captures: [prior = self.next, end = self.end],
        ensures: |result| self.end == end && match result {
            Some(node) => prior < end && node.0 == prior && self.next == prior.saturating_add(1),
            None => prior >= end && self.next == prior,
        },
    )]
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        (self.next < self.end).then(|| {
            let node = NodeId(self.next);
            self.next = self.next.checked_add(1).unwrap_or(self.end);
            node
        })
    }
}

/// The host-addressable length of a vector holding one slot per node.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeCapacity(usize);

impl TryFrom<NodeCount> for NodeCapacity
{
    type Error = TryFromIntError;

    /// Widens a node bound to a host length.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the capacity equals the bound.
    /// - fails: the bound exceeds the host's `usize`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`TryFromIntError`] when the bound does not fit `usize`.
    ///
    /// # Adequacy
    /// - hypothesis: For every node bound, the result observer distinguishes
    ///   numerical preservation from truncation and refusal from successful
    ///   widening. L3 endpoint witnesses cover zero and the largest bound; a
    ///   refusal on a narrower host is conditional on its address width, not
    ///   simulated allocation failure.
    /// - witness: `types::tests::host_positions_preserve_bounds`
    #[spec(ensures: |result| result.map_or_else(
        |_| usize::try_from(value.0).is_err(),
        |capacity| u64::try_from(capacity.0).is_ok_and(|raw| raw == u64::from(value.0)),
    ))]
    #[inline]
    fn try_from(value: NodeCount) -> Result<Self, Self::Error>
    {
        usize::try_from(value.0).map(Self)
    }
}

impl From<NodeCapacity> for usize
{
    /// Unwraps the host length.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: NodeCapacity) -> Self
    {
        value.0
    }
}

/// The host-addressable position of one node's slot.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodePosition(usize);

impl TryFrom<NodeId> for NodePosition
{
    type Error = TryFromIntError;

    /// Widens a node id to a host position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the position equals the id.
    /// - fails: the id exceeds the host's `usize`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`TryFromIntError`] when the id does not fit `usize`.
    ///
    /// # Adequacy
    /// - hypothesis: For every dense node id, L3 endpoint observations
    ///   distinguish widening without a changed value from truncation or an
    ///   incorrect refusal. Host-width refusal is exercised only where the host
    ///   is narrower than the node representation; graph membership is
    ///   deliberately not checked here.
    /// - witness: `types::tests::host_positions_preserve_bounds`
    #[spec(ensures: |result| result.map_or_else(
        |_| usize::try_from(value.0).is_err(),
        |position| u64::try_from(position.0).is_ok_and(|raw| raw == u64::from(value.0)),
    ))]
    #[inline]
    fn try_from(value: NodeId) -> Result<Self, Self::Error>
    {
        usize::try_from(value.0).map(Self)
    }
}

impl TryFrom<NodePosition> for NodeId
{
    type Error = TryFromIntError;

    /// Narrows a host position back to a node id.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the id equals the position.
    /// - fails: the position exceeds `u32`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`TryFromIntError`] when the position does not fit `u32`.
    ///
    /// # Adequacy
    /// - hypothesis: For host positions, L3 endpoint and first-overflow
    ///   observations distinguish exact narrowing from truncation, off-by-one
    ///   refusal and accepting an unrepresentable id. The overflow witness runs
    ///   only when the host can represent that position; validity within any
    ///   particular graph is outside this conversion.
    /// - witness: `types::tests::host_positions_preserve_bounds`
    #[spec(ensures: |result| result.map_or_else(
        |_| u32::try_from(value.0).is_err(),
        |node| usize::try_from(node.0).is_ok_and(|raw| raw == value.0),
    ))]
    #[inline]
    fn try_from(value: NodePosition) -> Result<Self, Self::Error>
    {
        u32::try_from(value.0).map(Self)
    }
}

impl From<usize> for NodePosition
{
    /// Wraps a host position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<NodePosition> for usize
{
    /// Unwraps the host position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: NodePosition) -> Self
    {
        value.0
    }
}

/// A directed edge between two dense nodes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EdgeId
{
    /// The edge's source.
    pub source: NodeId,
    /// The edge's target.
    pub target: NodeId,
}

impl EdgeId
{
    /// Names the edge from `source` to `target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        source: NodeId,
        target: NodeId,
    ) -> Self
    {
        Self { source, target }
    }
}

impl Display for EdgeId
{
    /// Writes the edge as `source>target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        write!(f, "{}>{}", self.source, self.target)
    }
}

primitive_newtype! {
    display
    /// The canonical index of one strongly connected component in a
    /// [`Condensation`](crate::Condensation): components are numbered in
    /// ascending order of their smallest member.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ComponentIndex(u32);
}

/// A directed edge between two condensation components.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ComponentEdge
{
    /// The edge's source component.
    pub source: ComponentIndex,
    /// The edge's target component.
    pub target: ComponentIndex,
}

impl ComponentEdge
{
    /// Names the edge from `source` to `target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        source: ComponentIndex,
        target: ComponentIndex,
    ) -> Self
    {
        Self { source, target }
    }
}

impl Display for ComponentEdge
{
    /// Writes the edge as `source>target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        write!(f, "{}>{}", self.source, self.target)
    }
}

primitive_newtype! {
    display
    /// The height of one swing: its nonterminal count less one.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct SwingHeight(u32);
}

primitive_newtype! {
    display
    /// The height of one walk: how many of its swings have nonzero height.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct WalkHeight(u32);
}

primitive_newtype! {
    display
    /// The alternating length of one walk: twice its swing count, less one.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct WalkChainLength(u32);
}

primitive_newtype! {
    display
    /// A stable 64-bit FNV-1a fingerprint.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Fingerprint(u64);
}

primitive_newtype! {
    /// One byte of a fingerprint stream.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FingerprintByte(u8);
}

primitive_newtype! {
    /// One 16-bit word of a fingerprint stream, absorbed little-endian.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FingerprintWord16(u16);
}

primitive_newtype! {
    /// One 32-bit word of a fingerprint stream, absorbed little-endian.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FingerprintWord32(u32);
}

primitive_newtype! {
    /// One 64-bit word of a fingerprint stream, absorbed little-endian.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FingerprintWord64(u64);
}

/// A borrowed run of bytes absorbed into a fingerprint stream in order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FingerprintBytes<'bytes>(&'bytes [u8]);

impl<'bytes> From<&'bytes [u8]> for FingerprintBytes<'bytes>
{
    /// Borrows the slice.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'bytes [u8]) -> Self
    {
        Self(value)
    }
}

impl<'bytes, const LEN: usize> From<&'bytes [u8; LEN]> for FingerprintBytes<'bytes>
{
    /// Borrows the array as a slice.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'bytes [u8; LEN]) -> Self
    {
        Self(value)
    }
}

impl AsRef<[u8]> for FingerprintBytes<'_>
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

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use super::*;

    #[test]
    fn node_ids_advance_and_remain_exhausted()
    {
        let mut empty = NodeCount::from(0).ids();
        assert_eq!(empty.next(), None);
        assert_eq!(empty.next(), None);
        assert_eq!(
            NodeCount::from(3).ids().collect::<alloc::vec::Vec<_>>(),
            vec![NodeId::from(0), NodeId::from(1), NodeId::from(2)]
        );
        let mut last = NodeIdRange {
            next: u32::MAX.saturating_sub(1),
            end: u32::MAX,
        };
        assert_eq!(last.next(), Some(NodeId::from(u32::MAX.saturating_sub(1))));
        assert_eq!(last.next(), None);
        assert_eq!(last.next(), None);
    }

    #[test]
    fn host_positions_preserve_bounds()
    {
        for raw in [0_u32, u32::MAX] {
            if let Ok(expected) = usize::try_from(raw) {
                let capacity =
                    NodeCapacity::try_from(NodeCount::from(raw)).expect("representable bound");
                assert_eq!(usize::from(capacity), expected);
                let position = NodePosition::try_from(NodeId::from(raw)).expect("representable id");
                assert_eq!(usize::from(position), expected);
                assert_eq!(
                    NodeId::try_from(position).expect("round-trip id"),
                    NodeId::from(raw)
                );
            }
            else {
                assert!(NodeCapacity::try_from(NodeCount::from(raw)).is_err());
                assert!(NodePosition::try_from(NodeId::from(raw)).is_err());
            }
        }
        if let Some(overflow) = usize::try_from(u32::MAX)
            .ok()
            .and_then(|raw| raw.checked_add(1))
        {
            assert!(NodeId::try_from(NodePosition::from(overflow)).is_err());
        }
    }
}
