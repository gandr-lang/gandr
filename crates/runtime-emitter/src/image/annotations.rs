//! The annotations of a command's image: one content table of the core
//! types and codes that its nodes name, and the place of each root in it.
//!
//! A code, a fold, an operation, a handler and a session action name core
//! nodes of the arena's annotations. An arena id holds inside one process
//! alone, so the image writes each such node as its content. One table holds
//! every root of the command, so a type that two nodes name is written once.
//! The table is the byte form of the node codec of `gandr-core-content`, so a
//! content table has one byte form in the tree.
//!
//! # Boundaries
//!
//! - **A constant crosses as its position.** A table names a constant through
//!   [`Positions`], as four bytes of its admission position. The reader puts it
//!   back at the same position. The definitions of the image hold its body.
//!
//! # References
//!
//! - `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — lineage: the IO direction,
//!   § io-direction-first-crate: one byte form of a content table, for the
//!   store and for the image.

use alloc::vec::Vec;

use gandr_core_content::ArenaNode;
use gandr_core_content::ItemKey;
use gandr_core_content::Minted;
use gandr_core_content::Occurrence;
use gandr_core_content::Reference;
use gandr_core_content::Resolver;
use gandr_core_content::SupportedNode;
use gandr_core_content::TablePlace;
use gandr_core_content::codec::Bytes;
use gandr_core_content::codec::CodecError;
use gandr_core_content::codec::Reader;
use gandr_core_content::codec::Sink;
use gandr_core_content::codec::Writer;
use gandr_core_content::codec::check_discovery;
use gandr_core_content::codec::read_nodes;
use gandr_core_content::codec::read_table_place;
use gandr_core_content::codec::write_index;
use gandr_core_content::codec::write_nodes;
use gandr_core_content::codec::write_selection;
use gandr_core_content::seating;
use gandr_core_content::tabled_roots;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

/// The bytes that the node codec writes for an image.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
pub(super) struct Buffer(Vec<u8>);

impl Buffer
{
    /// The bytes written.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) fn into_bytes(self) -> Vec<u8>
    {
        self.0
    }
}

impl Sink for Buffer
{
    /// Append `bytes`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the appended bytes, growth within the image
    #[inline]
    fn put(
        &mut self,
        bytes: Bytes<'_>,
    )
    {
        self.0.extend_from_slice(bytes.0);
    }
}

/// The resolver of an image: a constant is its admission position.
///
/// # Specification
/// - ensures: [`Resolver::place`] gives back each position that
///   [`Resolver::resolve`] gives a reference for.
#[derive(Clone, Copy, Debug)]
pub(super) struct Positions;

impl Resolver for Positions
{
    /// The reference of the constant at `position`: four little-endian bytes
    /// of the position, at its first occurrence.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the four bytes of the key, growth within the table
    #[inline]
    fn resolve(
        &self,
        position: ConstantIndex,
    ) -> Reference
    {
        let at = u32::try_from(usize::from(position)).unwrap_or(u32::MAX);
        Reference::Item {
            key: ItemKey::from(at.to_le_bytes().as_slice()),
            occurrence: Occurrence::from(0_usize),
        }
    }

    /// The position that `reference` names, when it is four bytes at its
    /// first occurrence.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`seating::Absent::Unplaced`] for any other reference.
    #[inline]
    fn place(
        &self,
        reference: &Reference,
    ) -> Maybe<ConstantIndex, seating::Absent>
    {
        let Reference::Item {
            ref key,
            occurrence,
        } = *reference
        else {
            return Maybe::Absent(seating::Absent::Unplaced);
        };
        if occurrence != Occurrence::from(0_usize) {
            return Maybe::Absent(seating::Absent::Unplaced);
        }
        match <[u8; 4]>::try_from(key.as_ref()) {
            Ok(bytes) => usize::try_from(u32::from_le_bytes(bytes))
                .map_or(Maybe::Absent(seating::Absent::Unplaced), |at| {
                    Maybe::Present(ConstantIndex::from(at))
                }),
            Err(_other) => Maybe::Absent(seating::Absent::Unplaced),
        }
    }
}

/// One content table of a command's annotations, with the place of each
/// root.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default)]
pub(super) struct Table
{
    /// The nodes, numbered by discovery from the roots.
    nodes: Vec<SupportedNode>,
    /// The place of each root, in the order of the roots.
    places: Vec<TablePlace>,
}

impl Table
{
    /// The table of `roots` in `arena`, and the ordinal of each root in it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one place for each distinct content of the roots, at its
    ///   first occurrence, over one table that writes each node once; the
    ///   ordinal of each root is the place of its content. So two arenas that
    ///   share nodes differently give the same table.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the table, the places and the ordinals, growth within the
    ///   annotations
    #[inline]
    pub(super) fn of(
        arena: &CoreArena,
        roots: &[ArenaNode],
    ) -> (Self, Vec<u32>)
    {
        let (nodes, every) = tabled_roots(arena, &Positions, roots);
        let mut places: Vec<TablePlace> = Vec::new();
        let mut ordinals = Vec::with_capacity(every.len());
        for place in every {
            let at = places
                .iter()
                .position(|held| *held == place)
                .unwrap_or_else(|| {
                    places.push(place);
                    places.len().saturating_sub(1)
                });
            ordinals.push(u32::try_from(at).unwrap_or(u32::MAX));
        }
        (Self { nodes, places }, ordinals)
    }

    /// The number of roots.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) const fn roots(&self) -> usize
    {
        self.places.len()
    }

    /// The bytes of the table: its nodes, then the place of each root.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The [`CodecError`] of a node that has no byte form.
    ///
    /// # Cost
    /// - allocation: the bytes, growth within the table
    #[inline]
    pub(super) fn bytes(&self) -> Result<Vec<u8>, CodecError>
    {
        let mut buffer = Buffer::default();
        let mut writer = Writer { sink: &mut buffer };
        write_nodes(&mut writer, &self.nodes)?;
        for place in &self.places {
            write_index(&mut writer, place.node)?;
            write_selection(&mut writer, &place.support);
        }
        Ok(buffer.0)
    }

    /// Read a table of `roots` roots from `bytes`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the table that [`Self::bytes`] wrote.
    /// - fails: bytes that the node codec refuses, a child that names a node
    ///   after it, a table not numbered by discovery from its roots, and bytes
    ///   past the last place.
    /// - panics: none.
    ///
    /// # Errors
    /// The [`CodecError`] of the first fault.
    ///
    /// # Cost
    /// - allocation: the nodes and the places, growth within the bytes
    #[inline]
    pub(super) fn read(
        bytes: &[u8],
        roots: usize,
    ) -> Result<Self, CodecError>
    {
        let mut reader = Reader { bytes, cursor: 0 };
        let nodes = read_nodes(&mut reader)?;
        let mut places = Vec::new();
        for _root in 0 .. roots {
            places.push(read_table_place(&mut reader, &nodes)?);
        }
        reader.finish()?;
        check_discovery(&nodes, places.iter().map(|place| place.node))?;
        Ok(Self { nodes, places })
    }

    /// Mint each root into `arena`, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success one node of `arena` for each root, in order.
    /// - panics: none.
    ///
    /// # Errors
    /// The reason that a root does not mint.
    ///
    /// # Cost
    /// - allocation: each minted node and the list of roots, growth within the
    ///   table
    #[inline]
    pub(super) fn mint(
        &self,
        arena: &mut CoreArena,
    ) -> Maybe<Vec<ArenaNode>, seating::Absent>
    {
        let minted = match Minted::of(
            &self.nodes,
            self.places.iter().cloned(),
            (arena, &Positions),
        ) {
            Maybe::Present(minted) => minted,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let mut roots = Vec::with_capacity(self.places.len());
        for place in &self.places {
            match minted.node(place) {
                Some(node) => roots.push(node),
                None => return Maybe::Absent(seating::Absent::IllSorted),
            }
        }
        Maybe::Present(roots)
    }
}
