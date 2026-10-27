//! One store for the CAM, the content-addressable memory of
//! `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory`:
//! the value plane, the record plane and the named roots under one directory,
//! opened once by a consumer and shared by everything it stores. A pointer
//! into it proves integrity, the bytes committed, and never validity.
//!
//! [`Store::open`] roots a store at a directory, the user's data directory's
//! `gandr/store` for the driver. The value plane, the content-addressable
//! memory of `storage-values`, holds its chunks in `chunks/`, each a file
//! named by its digest; the record plane of `storage-records` holds its nodes
//! in `nodes/`, each named by its identity; the two never share a name space.
//! [`Store::commit`] and [`Store::deref`] move a [`Stored`] value in and out
//! by [`ContentPtr`], [`Store::write_tree`] and [`Store::records`] a record
//! tree, and [`Store::set_root`] and [`Store::roots`] name a pointer for a
//! consumer to find again. The planes' own traits verify every load, so a
//! file changed on disk is refused by the plane's own fault, carried as
//! [`StoreError`].
//!
//! # Boundaries
//!
//! The store is integrity only: a pointer, a digest, a tree root and a root
//! name each say which bytes, and none of them says the bytes are valid. No
//! type of this crate is a verdict or makes one; a consumer that reuses one
//! takes it from the kernel's attested cache, never from a pointer.
//!
//! A store is one host's. Pointers cross hosts; roots, which a host's
//! consumers name, do not. The store is the persistent backend the planes
//! keep out of themselves, so neither plane crate touches the file system.
//!
//! # References
//!
//! - `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — background: the storage
//!   tier is the build layer's store, and its persistence is a backend beside
//!   the planes, not in them.
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — background: integrity never
//!   stands for validity, the wall this crate keeps.
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: the CAM
//!   the value plane is, which this store keeps on disk.

extern crate alloc;

mod plane;
mod roots;
mod store;

pub use gandr_storage_values::ContentPtr;

pub use crate::plane::ChunkDirectory;
pub use crate::plane::NodeDirectory;
pub use crate::roots::RootName;
pub use crate::roots::Roots;
pub use crate::roots::unrooted;
pub use crate::store::RootsFault;
pub use crate::store::Store;
pub use crate::store::StoreError;
pub use crate::store::Stored;
