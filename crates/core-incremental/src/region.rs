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
//!
//! # References, not positions
//!
//! An admission position is an artefact of one revision. Every position an item
//! mentions is read as the `Reference` it resolves to — the key of the item at
//! that position and how many items of that key precede it — or `Unoccupied`.
//! Two revisions agree on what an item reads exactly when they agree on
//! references.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
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
///
/// # Specification
/// - requires: item keys and occurrence counts are interpreted in one program.
/// - ensures: an item reference names the occurrence of its key; an unoccupied
///   position names no item.
/// - panics: none.
/// - executable: none — the program assigning keys and occurrence counts is
///   external to a reference value.
///
/// # Adequacy
/// - hypothesis: L3 — empty, skipped and maximum positions, interleaved
///   repeated keys and unknown references distinguish missing names, wrong
///   occurrence counts and accidental naming by exact references and ordinals.
/// - witness: `region::tests::positions_must_ascend_and_may_skip`
/// - witness: `region::tests::a_repeated_key_counts_its_occurrences`
/// - witness: `region::tests::empty_and_extreme_programs_resolve_exactly`
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
///
/// # Specification
/// - requires: interpreted against the rejected sequence of offered items.
/// - ensures: the ordinal and two positions identify its first nonascending
///   pair, including equality.
/// - panics: none.
/// - executable: none — the rejected sequence is absent from the error value;
///   the constructor checks the payload against that sequence.
///
/// # Adequacy
/// - hypothesis: L3 — repeated and descending positions, including two
///   violations after a valid prefix, distinguish a relaxed comparison, wrong
///   positions and last-error selection through exact error payloads.
/// - witness: `region::tests::positions_must_ascend_and_may_skip`
/// - witness: `region::tests::the_first_position_violation_wins`
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
            Self::PositionOrder {
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
///
/// # Specification
/// - requires: constructed with the items of one program.
/// - ensures: items and references share source ordinals; occupied positions
///   and named references resolve back to those ordinals.
/// - panics: none.
/// - executable: none — the data declaration has no call boundary; program
///   construction and lookup predicates check the addressing relations.
///
/// # Adequacy
/// - hypothesis: L3 — constructor-produced empty and singleton layouts, gaps
///   and repeated keys distinguish missing entries, crossed ordinals and false
///   hits through exact reference and ordinal lookup results.
/// - witness: `region::tests::empty_and_extreme_programs_resolve_exactly`
/// - witness: `region::tests::positions_must_ascend_and_may_skip`
/// - witness: `region::tests::a_repeated_key_counts_its_occurrences`
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
    /// Whether the program declares a world or an item states an entry.
    locus: crate::content::Locus,
}

impl Layout
{
    /// Whether the program declares a world or an item states an entry: every
    /// item of a located program is opaque.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn locus(&self) -> crate::content::Locus
    {
        self.locus
    }

    /// The reference the admission position `position` resolves to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the reference of the item at `position`, or
    ///   [`Reference::Unoccupied`] when no item takes it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — occupied, skipped, empty and maximum positions
    ///   distinguish a false hit or a missing mapping by exact returned
    ///   references.
    /// - witness: `region::tests::positions_must_ascend_and_may_skip`
    /// - witness: `region::tests::empty_and_extreme_programs_resolve_exactly`
    #[spec(ensures: |ret| self.occupied.get(&position)
        .and_then(|&ordinal| self.references.get(usize::from(ordinal)))
        .map_or_else(|| ret == Reference::Unoccupied, |reference| ret == *reference))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the three distinct references of interleaved keys
    ///   round-trip to exact ordinals; unoccupied, unknown-key and out-of-range
    ///   occurrence references distinguish accidental naming by exact absence.
    /// - witness: `region::tests::a_repeated_key_counts_its_occurrences`
    /// - witness: `region::tests::empty_and_extreme_programs_resolve_exactly`
    #[spec(ensures: |ret| match self.named.get(reference) {
        Some(&ordinal) => ret == Maybe::Present(ordinal),
        None => ret == Maybe::Absent(naming::Absent::Unnamed),
    })]
    pub(crate) fn ordinal_of(
        &self,
        reference: &Reference,
    ) -> Maybe<ItemOrdinal, naming::Absent>
    {
        match self.named.get(reference) {
            Some(&ordinal) => Maybe::Present(ordinal),
            None => Maybe::Absent(naming::Absent::Unnamed),
        }
    }
}

/// The items a front end offers for one revision, in source order, over the
/// arena their declarations were minted in.
///
/// # Specification
/// - requires: nothing; unresolved arena identifiers remain admitted input.
/// - ensures: admitted positions strictly ascend, item order is retained and
///   references distinguish successive occurrences of each key.
/// - panics: none.
/// - executable: none — the data declaration has no entry or return boundary;
///   the constructor checks admission order and the assembled layout.
///
/// # Adequacy
/// - hypothesis: L3 — empty and maximum-position programs, gaps, repeated keys
///   and nonascending pairs distinguish lost items, wrong naming and incorrect
///   admission through exact references and refusal payloads. These witnesses
///   concern addressing, not validity of arena node ids.
/// - witness: `region::tests::empty_and_extreme_programs_resolve_exactly`
/// - witness: `region::tests::positions_must_ascend_and_may_skip`
/// - witness: `region::tests::a_repeated_key_counts_its_occurrences`
/// - witness: `region::tests::the_first_position_violation_wins`
#[derive(Clone, Debug)]
pub struct Program
{
    /// The arena every declaration's ids resolve in.
    arena: CoreArena,
    /// The items and their references.
    layout: Layout,
    /// What makes the tier each pass's context decides endpoint pairs on,
    /// with the policy a closed pair it meets crosses under, when the front
    /// end supplies one.
    tier: Option<(
        gandr_core_checker::tier::MakeTier,
        gandr_kernel_core::AdmissionPolicy,
    )>,
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
    /// - hypothesis: L3 — empty and singleton input, maximum and skipped
    ///   positions, interleaved repeated keys and two violations after a valid
    ///   prefix distinguish lost items, wrong occurrence counts, relaxed order
    ///   and last-error selection by exact references, ordinals and errors.
    /// - witness: `region::tests::positions_must_ascend_and_may_skip`
    /// - witness: `region::tests::a_repeated_key_counts_its_occurrences`
    /// - witness: `region::tests::empty_and_extreme_programs_resolve_exactly`
    /// - witness: `region::tests::the_first_position_violation_wins`
    #[spec(
        captures: [item_count = items.len(),
        first_bad = items.windows(2).enumerate().find_map(|(index, pair)| {
            let (previous, next) = pair.first().zip(pair.last())?;
            let position = next.declaration.constant();
            let previous = previous.declaration.constant();
            (position <= previous).then_some(ProgramError::PositionOrder {
                ordinal: ItemOrdinal::from(index.saturating_add(1)),
                position,
                previous,
            })
        })],
        ensures: |ret| match ret {
            Ok(ref program) => first_bad.is_none()
                && program.layout.items.len() == item_count
                && program.layout.references.len() == item_count
                && program.layout.occupied.len() == item_count
                && program.layout.named.len() == item_count
                && program.layout.items.iter().zip(&program.layout.references)
                    .enumerate().all(|(index, (item, reference))| {
                        matches!(reference, Reference::Item { key, .. } if key == &item.key)
                            && program.layout.occupied.get(&item.declaration.constant())
                                == Some(&ItemOrdinal::from(index))
                            && program.layout.named.get(reference)
                                == Some(&ItemOrdinal::from(index))
                    }),
            Err(error) => first_bad == Some(error),
        },
    )]
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
        let located = items.iter().any(|item| {
            matches!(
                *item.declaration.content(),
                gandr_core_checker::DeclarationContent::World
            ) || matches!(item.declaration.entry(), Maybe::Present(_))
        });
        Ok(Self {
            arena,
            layout: Layout {
                items,
                references,
                occupied,
                named,
                locus: if located {
                    crate::content::Locus::Located
                }
                else {
                    crate::content::Locus::Unlocated
                },
            },
            tier: None,
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

    /// Decide each endpoint pair every later pass meets on a tier `make`
    /// makes, one per pass, a closed pair it meets crossing as `policy`
    /// states.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every later pass's context is handed a tier `make` made and
    ///   `policy` ([`gandr_core_checker::CheckingContext::decide_endpoints_on`]);
    ///   the last maker and policy handed are the ones kept.
    /// - provides: the front end's hand-in of its tier to the incremental
    ///   checker, whose passes make their own contexts.
    /// - panics: none.
    /// - executable: none — a function pointer no predicate compares.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tier meeting every pair checks a claim the machine
    ///   refutes on a fresh pass and on one resumed after leading items, and a
    ///   program handed none refuses it on both.
    /// - witness: `tests::incremental::a_pass_hands_its_context_the_program_s_tier_2282`
    #[inline]
    pub fn decide_endpoints_on(
        &mut self,
        make: gandr_core_checker::tier::MakeTier,
        policy: gandr_kernel_core::AdmissionPolicy,
    )
    {
        self.tier = Some((make, policy));
    }

    /// What makes each pass's tier, and the policy beside it, when one was
    /// handed.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn tier(
        &self
    ) -> Option<(
        gandr_core_checker::tier::MakeTier,
        gandr_kernel_core::AdmissionPolicy,
    )>
    {
        self.tier
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
            .map(|item| item.declaration.clone())
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact results at occupied, skipped, empty and maximum
    ///   positions distinguish wrong position lookup and false absence.
    /// - witness: `region::tests::positions_must_ascend_and_may_skip`
    /// - witness: `region::tests::a_repeated_key_counts_its_occurrences`
    /// - witness: `region::tests::empty_and_extreme_programs_resolve_exactly`
    #[spec(ensures: |ret| self.layout.occupied.get(&position)
        .and_then(|&ordinal| self.layout.references.get(usize::from(ordinal)))
        .map_or_else(|| ret == Reference::Unoccupied, |reference| ret == *reference))]
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
///
/// # Specification
/// - requires: revision interpretation belongs to the implementing front end.
/// - ensures: successful lowering supplies a program in source order with
///   strictly ascending admission positions.
/// - fails: through the front end's associated error when lowering fails.
/// - panics: none.
/// - executable: none — revision meaning and failures are implementor-owned;
///   instrumenting this declaration changes required implementor methods.
///
/// # Adequacy
/// - hypothesis: L3 — empty, skipped and rejected position sequences witness
///   the local program-construction boundary of successful results. Revision
///   correspondence and frontend-specific failures remain obligations of the
///   implementing front end, not claims of these constructor witnesses.
/// - witness: `region::tests::empty_and_extreme_programs_resolve_exactly`
/// - witness: `region::tests::positions_must_ascend_and_may_skip`
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
    /// - executable: none — the revision has no shared semantic observer; a
    ///   declaration attribute also changes the required trait interface.
    ///
    /// # Errors
    /// The front end's own failure to lower the revision.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, skipped and rejected position sequences
    ///   distinguish incorrect admission at the local result-construction
    ///   boundary. The front end owns evidence for revision correspondence and
    ///   its errors.
    /// - witness: `region::tests::empty_and_extreme_programs_resolve_exactly`
    /// - witness: `region::tests::positions_must_ascend_and_may_skip`
    fn items(
        &self,
        revision: &Self::Revision,
    ) -> Result<Program, Self::Error>;
}

#[cfg(test)]
mod tests;
