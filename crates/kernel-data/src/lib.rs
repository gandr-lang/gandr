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

#![no_std]

extern crate alloc;

mod region;

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
