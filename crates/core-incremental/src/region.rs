//! The item seam: what a front end hands the incremental checker, and the
//! position-free names its constants resolve to.
//!
//! # Items, not positions
//!
//! A front end lowers each top-level declaration it offers into one [`Item`]:
//! a stable [`ItemKey`] it chooses — a digest of the declaration's name, say —
//! beside the checker's own [`Declaration`]. Admission positions are the
//! checker's coordinates and shift when an item is inserted before them, so
//! nothing that must survive an edit is stated in them: a constant is read as
//! the [`Reference`] its position resolves to in its own program, the key of
//! the item there and that item's occurrence among the items of its key.
//! Positions may skip: a declaration the front end refused is not offered,
//! and a constant naming its position resolves to [`Reference::Unoccupied`].

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_checker::Declaration;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::boundary::ItemOrdinal;
use crate::boundary::Occurrence;

quenchant_shape::reason_enum! {
    /// Why a reference names no item of a program.
    pub mod naming {
        /// The reason no item is named.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The program holds no item under that reference.
            Unnamed,
        }
    }
}

/// A front end's stable identity for one item, opaque to this crate.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ItemKey(Box<[u8]>);

impl From<&[u8]> for ItemKey
{
    /// The key of these bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &[u8]) -> Self
    {
        Self(Box::from(bytes))
    }
}

impl From<&str> for ItemKey
{
    /// The key of this text's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &str) -> Self
    {
        Self(Box::from(text.as_bytes()))
    }
}

impl AsRef<[u8]> for ItemKey
{
    /// The key's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// What a constant names, stated without admission positions.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Reference
{
    /// The item of `key` that `occurrence` items of the same key precede.
    Item
    {
        /// The item's key.
        key: ItemKey,
        /// How many items of the same key precede it.
        occurrence: Occurrence,
    },
    /// A position no item of the program occupies.
    Unoccupied,
}

/// One offered declaration under the key its front end gave it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Item
{
    /// The front end's stable identity for the item.
    key: ItemKey,
    /// The declaration the checker judges.
    declaration: Declaration,
}

impl Item
{
    /// The item `declaration` under `key`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        key: ItemKey,
        declaration: Declaration,
    ) -> Self
    {
        Self { key, declaration }
    }

    /// The front end's stable identity for the item.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn key(&self) -> &ItemKey
    {
        &self.key
    }

    /// The declaration the checker judges.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declaration(&self) -> &Declaration
    {
        &self.declaration
    }
}

/// Why a sequence of items is not a program.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ProgramError
{
    /// An item's admission position does not follow its predecessor's, so the
    /// checker would refuse it out of order.
    PositionOrder
    {
        /// The item out of order.
        ordinal: ItemOrdinal,
        /// Its admission position.
        position: ConstantIndex,
        /// Its predecessor's admission position.
        previous: ConstantIndex,
    },
}

impl fmt::Display for ProgramError
{
    /// Writes the failure's message.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::PositionOrder {
                ordinal,
                position,
                previous,
            } => {
                write!(
                    f,
                    "item {} takes admission position {} at or below its predecessor's {}",
                    usize::from(ordinal),
                    usize::from(position),
                    usize::from(previous)
                )
            },
        }
    }
}

impl core::error::Error for ProgramError
{
}

/// The items of a program and the two maps between positions, references and
/// source ordinals, apart from the arena so both can be borrowed at once.
#[derive(Clone, Debug)]
pub struct Layout
{
    /// The items, in source order, admission positions strictly ascending.
    pub items: Vec<Item>,
    /// Each item's own reference, in source order.
    pub references: Vec<Reference>,
    /// The item at each occupied admission position.
    occupied: BTreeMap<ConstantIndex, ItemOrdinal>,
    /// The item each reference names.
    named: BTreeMap<Reference, ItemOrdinal>,
}

impl Layout
{
    /// The reference the admission position `position` resolves to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the reference of the item at `position`, or
    ///   [`Reference::Unoccupied`] when no item takes it.
    /// - panics: none.
    pub(crate) fn resolve(
        &self,
        position: ConstantIndex,
    ) -> Reference
    {
        self.occupied
            .get(&position)
            .and_then(|&ordinal| self.references.get(usize::from(ordinal)))
            .cloned()
            .unwrap_or(Reference::Unoccupied)
    }

    /// The source ordinal of the item `reference` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the ordinal of the item whose own reference is `reference`.
    /// - provides: `naming::Absent::Unnamed` for [`Reference::Unoccupied`] and
    ///   for a reference no item of this program carries.
    /// - panics: none.
    pub(crate) fn ordinal_of(
        &self,
        reference: &Reference,
    ) -> Maybe<ItemOrdinal, naming::Absent>
    {
        match self.named.get(reference) {
            | Some(&ordinal) => Maybe::Present(ordinal),
            | None => Maybe::Absent(naming::Absent::Unnamed),
        }
    }
}

/// The items a front end offers for one revision, in source order, over the
/// arena their declarations were minted in.
#[derive(Clone, Debug)]
pub struct Program
{
    /// The arena every declaration's ids resolve in.
    arena: CoreArena,
    /// The items and their references.
    layout: Layout,
}

impl Program
{
    /// The program of `items` over `arena`.
    ///
    /// # Specification
    /// - requires: nothing — positions out of order are admissible input and
    ///   refused.
    /// - ensures: on success the items keep their order, and each item's
    ///   reference is its key with the number of items of that key before it.
    /// - provides: the one place positions are checked, so the checker never
    ///   refuses an item of a program for admission order.
    /// - fails: [`ProgramError::PositionOrder`] naming the first item whose
    ///   position does not exceed its predecessor's.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ProgramError::PositionOrder`] — admission positions do not strictly
    /// ascend in source order.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the strict comparison and the
    ///   occurrence count, separated by a repeated position, a descending one,
    ///   a gap, and two items sharing a key.
    /// - witness: `region::tests::positions_must_ascend_and_may_skip`
    /// - witness: `region::tests::a_repeated_key_counts_its_occurrences`
    #[inline]
    pub fn new(
        arena: CoreArena,
        items: Vec<Item>,
    ) -> Result<Self, ProgramError>
    {
        let mut references = Vec::with_capacity(items.len());
        let mut occupied = BTreeMap::new();
        let mut named = BTreeMap::new();
        let mut seen: BTreeMap<&ItemKey, Occurrence> = BTreeMap::new();
        let mut previous: Maybe<ConstantIndex, naming::Absent> =
            Maybe::Absent(naming::Absent::Unnamed);
        for (index, item) in items.iter().enumerate() {
            let ordinal = ItemOrdinal::from(index);
            let position = item.declaration.constant();
            if let Maybe::Present(previous) = previous
                && position <= previous
            {
                return Err(ProgramError::PositionOrder {
                    ordinal,
                    position,
                    previous,
                });
            }
            previous = Maybe::Present(position);
            let counter = seen.entry(&item.key).or_default();
            let occurrence = *counter;
            *counter = Occurrence::from(usize::from(occurrence).saturating_add(1));
            let reference = Reference::Item {
                key: item.key.clone(),
                occurrence,
            };
            let _vacant = occupied.insert(position, ordinal);
            let _vacant = named.insert(reference.clone(), ordinal);
            references.push(reference);
        }
        Ok(Self {
            arena,
            layout: Layout {
                items,
                references,
                occupied,
                named,
            },
        })
    }

    /// The arena every declaration's ids resolve in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn arena(&self) -> &CoreArena
    {
        &self.arena
    }

    /// The items and their references.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn layout(&self) -> &Layout
    {
        &self.layout
    }

    /// The arena, mutably, beside the layout: a pass grows the one while it
    /// reads the other.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn parts_mut(&mut self) -> (&mut CoreArena, &Layout)
    {
        (&mut self.arena, &self.layout)
    }

    /// The items, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn items(&self) -> &[Item]
    {
        &self.layout.items
    }

    /// The declarations, in source order, as the batch checker takes them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn declarations(&self) -> Vec<Declaration>
    {
        self.layout
            .items
            .iter()
            .map(|item| item.declaration)
            .collect()
    }

    /// Each item's own reference, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn references(&self) -> &[Reference]
    {
        &self.layout.references
    }

    /// The reference the admission position `position` resolves to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the reference of the item at `position`, or
    ///   [`Reference::Unoccupied`] when no item takes it.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn resolve(
        &self,
        position: ConstantIndex,
    ) -> Reference
    {
        self.layout.resolve(position)
    }
}

/// A front end's view of its own revisions: it lowers one into a [`Program`].
///
/// The engine never reads a revision, only the program lowered from it, so a
/// front end may keep any representation it likes behind this seam.
pub trait ItemSource
{
    /// The revision representation the front end reads.
    type Revision;
    /// Why a revision could not be lowered at all; a declaration the front end
    /// refuses is left out of the program rather than failing the revision.
    type Error;

    /// The program `revision` lowers to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the items the revision offers, in source order, with
    ///   admission positions ascending.
    /// - fails: when the revision cannot be lowered at all.
    /// - panics: none.
    ///
    /// # Errors
    /// The front end's own failure to lower the revision.
    fn items(
        &self,
        revision: &Self::Revision,
    ) -> Result<Program, Self::Error>;
}

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use gandr_core_checker::Declaration;
    use gandr_core_checker::OriginToken;
    use gandr_core_checker::body;
    use gandr_core_checker::signature;
    use gandr_core_term::CoreArena;
    use gandr_kernel_term::ConstantIndex;
    use quenchant_shape::shape::Maybe;

    use super::Item;
    use super::ItemKey;
    use super::Program;
    use super::ProgramError;
    use super::Reference;
    use crate::boundary::ItemOrdinal;
    use crate::boundary::Occurrence;

    /// A fixture item's key text.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Name(&'static str);

    /// A fixture item's admission position.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct At(usize);

    /// A bodiless, unsigned item named `key` at `position`.
    ///
    /// # Specification
    /// trivial.
    fn item(
        key: Name,
        position: At,
    ) -> Item
    {
        Item::new(
            ItemKey::from(key.0),
            Declaration::new(
                ConstantIndex::from(position.0),
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Absent(body::Absent::Hole),
                OriginToken::from(position.0),
            ),
        )
    }

    #[test]
    fn positions_must_ascend_and_may_skip()
    {
        let skipping = Program::new(CoreArena::new(), vec![
            item(Name("a"), At(0)),
            item(Name("b"), At(3)),
        ])
        .expect("a gap is admissible");
        assert_eq!(
            skipping.resolve(ConstantIndex::from(1_usize)),
            Reference::Unoccupied,
            "a skipped position resolves to no item"
        );
        assert_eq!(
            skipping.resolve(ConstantIndex::from(3_usize)),
            Reference::Item {
                key: ItemKey::from("b"),
                occurrence: Occurrence::from(0_usize),
            },
            "an occupied position resolves to its item"
        );
        for (later, label) in [(1_usize, "repeated"), (0_usize, "descending")] {
            assert_eq!(
                Program::new(CoreArena::new(), vec![
                    item(Name("a"), At(1)),
                    item(Name("b"), At(later))
                ])
                .map(|_| ()),
                Err(ProgramError::PositionOrder {
                    ordinal: ItemOrdinal::from(1_usize),
                    position: ConstantIndex::from(later),
                    previous: ConstantIndex::from(1_usize),
                }),
                "a {label} position is refused with both positions"
            );
        }
    }

    #[test]
    fn a_repeated_key_counts_its_occurrences()
    {
        let program = Program::new(CoreArena::new(), vec![
            item(Name("d"), At(0)),
            item(Name("e"), At(1)),
            item(Name("d"), At(2)),
        ])
        .expect("ascending");
        assert_eq!(
            program.references(),
            [
                Reference::Item {
                    key: ItemKey::from("d"),
                    occurrence: Occurrence::from(0_usize),
                },
                Reference::Item {
                    key: ItemKey::from("e"),
                    occurrence: Occurrence::from(0_usize),
                },
                Reference::Item {
                    key: ItemKey::from("d"),
                    occurrence: Occurrence::from(1_usize),
                },
            ],
            "the second item of a key is its first repeat"
        );
    }
}
