//! The data of the bootstrap that allocates: a vector of bytes and a string
//! buffer over the heap of `boot-alloc`. The crate is of the layer `boot`,
//! outside the integrity and the validity walls: it checks no term and keeps
//! no value of the store.
//!
//! The data core needs an owner of bytes that grows before gandr states one
//! itself. Rust's vector is generic over its element and its allocator, so
//! the direct call of Rust cannot name it. A [`Vector`] holds bytes alone,
//! in a block of one [`Heap`](gandr_boot_alloc::Heap). It gives its bytes as
//! a [`Range`](gandr_boot_core::Range) of `boot-core`, so each operation of
//! that crate reads them. A growth that the heap or the size of a layout
//! refuses gives a [`Refusal`], and the vector keeps its bytes.
//!
//! A [`StringBuffer`] is a vector whose bytes are valid UTF-8, with one zero
//! byte after the last byte. The check of UTF-8 of `boot-core` stands at each
//! way in: an append that is not UTF-8, and a vector whose bytes are not, get
//! a [`Rejected`], and the bytes stay as they were. The buffer gives its bytes
//! back as a vector with no copy.
//!
//! The line between this crate and `boot-core` is the allocation: this crate
//! allocates, and `boot-core` does not.
//!
//! A crate of the layer `boot` is a stage of the bootstrap. A twin in gandr
//! replaces it, so each public function has no type parameter and states the
//! clauses that the twin meets.
//!
//! # References
//!
//! - `vault:01a1ebc5-2ff2-7833-b871-85901e734925` — newest: the data core of
//!   the bootstrap (§ boot-data-crates, § boot-data-sequences and §
//!   boot-data-strings): the rules of a crate of the layer `boot`, the line of
//!   the allocation between this crate and `boot-core`, a vector as a capacity,
//!   a length and one linear owner, and an owner of a string as the same vector
//!   with a proof of UTF-8 and one zero byte after its last byte.

#![no_std]

mod string;
mod vector;

pub use crate::string::Rejected;
pub use crate::string::StringBuffer;
pub use crate::string::Unchecked;
pub use crate::vector::Refusal;
pub use crate::vector::Vector;
