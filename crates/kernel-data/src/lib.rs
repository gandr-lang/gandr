//! The kernel's own data types: a region whose ids carry its brand, and the
//! containers of the kernel's chain. The crate is `no_std` over `core` and
//! `alloc`, and depends on no other workspace crate, so both chains reach it
//! as a leaf.
//!
//! A [`Region`] holds values under a budget. A scope brands it, so no
//! [`Id`] leaves the scope, and three crossings move an id between regions:
//! [`Adopt`] at a fork, the fold's translation at a join, and a durable
//! [`Key`] with its checked import, [`Region::seat`]. A region draws from the
//! allocator below it, and a borrow of a region is itself an allocator.
//!
//! A [`SmallVec`] holds up to `N` items in place, and past `N` all of them in
//! one block of the allocator below. A tag in its length names where the
//! items live, and a grow that the allocator refuses is a [`Refused`].

#![no_std]

extern crate alloc;

mod region;
mod small_vec;

pub use crate::region::Adopt;
pub use crate::region::Branded;
pub use crate::region::Budget;
pub use crate::region::Exhausted;
pub use crate::region::Id;
pub use crate::region::Key;
pub use crate::region::Mint;
pub use crate::region::Region;
pub use crate::region::scoped;
pub use crate::region::scoped_in;
pub use crate::small_vec::Count;
pub use crate::small_vec::Drain;
pub use crate::small_vec::IntoIter;
pub use crate::small_vec::Refused;
pub use crate::small_vec::SmallVec;
