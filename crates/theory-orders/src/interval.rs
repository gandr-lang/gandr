//! Pre/post-order intervals over an [`OrderMaintenance`].
//!
//! A tree node maps to the pair of order points `[lo, hi]` straddling its
//! subtree — `lo` minted in pre-order (on entry) and `hi` in post-order (on
//! exit). One node's subtree contains another's exactly when its interval
//! contains the other's, which the order makes an O(1) test ([containment]).
//! This module is only the interval datum; the order structure does the
//! comparing.
//!
//! [`OrderMaintenance`]: crate::order::OrderMaintenance
//! [containment]: crate::order::OrderMaintenance::interval_contains

use crate::order::Pos;

/// A closed interval of order points: the `[lo, hi]` straddling a subtree.
///
/// `lo` and `hi` are handles into the *same* [`OrderMaintenance`] with `lo` no
/// later than `hi` in the order; containment is tested via [containment].
///
/// [`OrderMaintenance`]: crate::order::OrderMaintenance
/// [containment]: crate::order::OrderMaintenance::interval_contains
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Interval
{
    /// The interval's lower (pre-order) endpoint.
    pub lo: Pos,
    /// The interval's upper (post-order) endpoint.
    pub hi: Pos,
}

impl Interval
{
    /// Builds the interval `[lo, hi]`.
    ///
    /// # Specification
    /// - requires: `lo` and `hi` are handles into the same structure with `lo`
    ///   no later than `hi` in the order (the caller establishes this when it
    ///   mints the endpoints in pre/post-order).
    /// - ensures: returns the interval carrying the two endpoints unchanged.
    /// - provides: the datum the containment test consumes. Its owning order
    ///   establishes endpoint liveness and relative position.
    /// - panics: none.
    /// - executable: none — the owning order is absent, and opaque `Pos`
    ///   exposes neither its fields here nor a const value-equality observer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested, disjoint and equal-endpoint intervals
    ///   distinguish endpoint placement through the owning order; a stale
    ///   endpoint produces absence. These observations do not claim to validate
    ///   liveness when constructing the datum.
    /// - witness: `order::tests::interval_containment`
    /// - witness: `order::tests::interval_with_stale_endpoint_is_none`
    #[inline]
    #[must_use]
    pub const fn new(
        lo: Pos,
        hi: Pos,
    ) -> Self
    {
        Self { lo, hi }
    }
}
