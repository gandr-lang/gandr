//! The kernel's own data types: a region whose ids carry its brand, and the
//! containers of the kernel's chain. The crate is `no_std` over `core` and
//! `alloc`, and depends on no other workspace crate, so both chains reach it
//! as a leaf.
//!
//! A [`Region`] holds values under a budget. A scope brands it, so no
//! [`Id`] leaves the scope, and three crossings move an id between regions:
//! [`Adopt`] at a fork, the fold's [`Translation`] at a join, and a durable
//! [`Key`] with its checked import, [`Region::seat`]. An id names its family
//! by a phantom kind. A fork of [`Width`] children shares one frozen prefix,
//! and each child keeps its suffix or drops it with a reason, its answer
//! among the [`Siblings`].
//! A region draws from the allocator below it, and a borrow of a region is
//! itself an allocator.
//!
//! A [`SmallVec`] holds up to `N` items in place, and past `N` all of them in
//! one block of the allocator below. A tag in its length names where the
//! items live, and a grow that the allocator refuses is a [`Refused`].
//!
//! A [`Shared`] shares one value by a count of holders, with no weak count,
//! so a mutable borrow reads the count with one load and a branch. A
//! [`Unique`] builds the value before the share. A [`ThinShared`] is one word
//! that points at one block of a header and a slice.
//!
//! A [`SmallString`] holds a text of up to 23 bytes inline, a static text, or
//! a block of its allocator, in 24 bytes for the global allocator, and reads
//! its text with one branch on its tag.

#![no_std]

extern crate alloc;

mod region;
mod shared;
mod small_string;
mod small_vec;
mod thin_shared;

pub use crate::region::Adopt;
pub use crate::region::Branded;
pub use crate::region::Budget;
pub use crate::region::Child;
pub use crate::region::Exhausted;
pub use crate::region::Id;
pub use crate::region::Key;
pub use crate::region::Mint;
pub use crate::region::Rebase;
pub use crate::region::Region;
pub use crate::region::Shift;
pub use crate::region::Sibling;
pub use crate::region::Siblings;
pub use crate::region::Translation;
pub use crate::region::Width;
pub use crate::region::scoped;
pub use crate::region::scoped_in;
pub use crate::shared::Held;
pub use crate::shared::Holders;
pub use crate::shared::Identity;
pub use crate::shared::Shared;
pub use crate::shared::Unique;
pub use crate::small_string::ByteLength;
pub use crate::small_string::Emptiness;
pub use crate::small_string::Fits;
pub use crate::small_string::SmallString;
pub use crate::small_string::Text;
pub use crate::small_vec::Count;
pub use crate::small_vec::Drain;
pub use crate::small_vec::IntoIter;
pub use crate::small_vec::Refused;
pub use crate::small_vec::SmallVec;
pub use crate::thin_shared::ThinShared;
