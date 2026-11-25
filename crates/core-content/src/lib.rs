//! The content form of a core node: the name of a type or a term outside the
//! arena that holds it.
//!
//! An arena id names a node by the order that one session mints it in, and a
//! constant names its declaration by an admission position of one revision.
//! Neither survives a second session or an edit. The content form names a
//! node by its canonical table instead: every node that it reaches, numbered
//! by discovery, free of arena ids and of admission positions. Two arenas
//! that hold equal terms give equal tables, and a table mints back into an
//! arena as a node with that content.
//!
//! The crate sits under the checker. It reads the core vocabulary and the
//! leaves that the core shares with the kernel, and nothing above them. So
//! the incremental store and the image of a command read one content form,
//! and a crate built from gandr source keeps the checker out of its tree.
//!
//! # References
//!
//! - `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — lineage: the IO direction
//!   (§ io-direction-first-crate), which keeps the checker out of the embedded
//!   crate's tree.
//! - `vault:01a178aa-74f1-7b03-a3a9-d145795bf4fd` — lineage: the design of the
//!   content form and its node keys.

extern crate alloc;

mod boundary;
pub mod codec;
mod content;
mod reference;
mod support;
pub use crate::boundary::ChildPosition;
pub use crate::boundary::Discovery;
pub use crate::boundary::NodeIndex;
pub use crate::boundary::Occurrence;
pub use crate::content::ArenaNode;
pub use crate::content::CellsRoots;
pub use crate::content::ChildSlot;
pub use crate::content::Children;
pub use crate::content::ContentNode;
pub use crate::content::DataRoots;
pub use crate::content::Encoder;
pub use crate::content::MintEntry;
pub use crate::content::Minted;
pub use crate::content::Opacity;
pub use crate::content::Placer;
pub use crate::content::PresentationRoots;
pub use crate::content::Sort;
pub use crate::content::TablePlace;
pub use crate::content::Tabled;
pub use crate::content::TypeContent;
pub use crate::content::TypeMemo;
pub use crate::content::WorldContent;
pub use crate::content::map_children;
pub use crate::content::mint_table;
pub use crate::content::named_holes;
pub use crate::content::occurring;
pub use crate::content::referencing;
pub use crate::content::seating;
pub use crate::content::tabled;
pub use crate::content::tabled_roots;
pub use crate::content::words;
pub use crate::reference::ItemKey;
pub use crate::reference::KeyName;
pub use crate::reference::Reference;
pub use crate::reference::Resolver;
pub use crate::reference::SourceTag;
pub use crate::support::Expanded;
pub use crate::support::Factored;
pub use crate::support::NodeParts;
pub use crate::support::Numbered;
pub use crate::support::Placement;
pub use crate::support::SupportedNode;
pub use crate::support::TableFault;
pub use crate::support::assemble;
pub use crate::support::expand;
pub use crate::support::expand_from;
pub use crate::support::factor;
pub use crate::support::number;
