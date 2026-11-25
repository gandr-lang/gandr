//! A self-contained **order-maintenance** structure: a total order over
//! payload-carrying elements, supporting insertion beside an existing element,
//! deletion, and **comparison of any two elements in O(1)**.
//!
//! [`OrderMaintenance`] is the structure and [`Interval`] the pre/post-order
//! containment query built on it. Everything a consumer layers on top — binder
//! lookup, per-node mark and dirty-bit layout, syntax-tree resync — has its own
//! invariants and lives in the consumer.
//!
//! Comparison is O(1) because every element carries a key strictly increasing
//! in list order, in two levels: its group's label on a circle of `2^64`
//! labels, then its own label within the group. Insertion is O(1) amortized
//! and the structure is total up to the `u32` slot ceiling; [`order`] states
//! the procedure.
//!
//! Handles are generation- and structure-checked: a stale handle to a removed
//! element, or a foreign handle from another structure, is detected rather than
//! silently aliasing an unrelated element.
//!
//! Every failure is a typed [`OrderError`]; no operation panics and no
//! operation silently no-ops on an inconsistent structure. Construction is
//! itself fallible rather than wrapping the process-wide structure-id counter.
//!
//! The crate is `no_std` and depends only on `core` and `alloc`.
//!
//! # Boundaries
//!
//! Structures carry a process-unique identity drawn from a shared atomic
//! counter, so that a handle from one structure is rejected by another instead
//! of silently resolving against an unrelated element. That counter needs an
//! atomic compare-exchange, which is the crate's only target requirement:
//! `target_has_atomic = "ptr"`. Every hosted target and every embedded target
//! with a compare-exchange instruction qualifies; the excluded set is
//! load/store-only cores such as `thumbv6m-none-eabi`, where a sound
//! process-wide counter would need a critical section this crate has no way to
//! obtain. The requirement is checked below rather than surfacing as a missing
//! atomic type.
//!
//! # References
//!
//! The papers the crate draws on are in its `README.md`, § References.

#![no_std]

#[cfg(not(target_has_atomic = "ptr"))]
compile_error!(
    "gandr-theory-order-maintenance requires a target with atomic \
     compare-exchange (target_has_atomic = \"ptr\"): structure identities \
     are minted from a shared atomic counter"
);

extern crate alloc;

pub mod interval;
pub mod order;

pub use crate::interval::Interval;
pub use crate::order::GroupWidth;
pub use crate::order::HandleMembership;
pub use crate::order::IntervalContainment;
pub use crate::order::Iter;
pub use crate::order::LiveLen;
pub use crate::order::OrderError;
pub use crate::order::OrderIsEmpty;
pub use crate::order::OrderMaintenance;
pub use crate::order::Pos;
