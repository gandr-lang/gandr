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
//!
//! # References
//!
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — the
//!   strata persist in the store, which the [`Opener`] of a [`Program`] hands
//!   every context its pass makes.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_checker::Declaration;
use gandr_core_content::ItemKey;
use gandr_core_content::Occurrence;
use gandr_core_content::Reference;
use gandr_core_content::Resolver as _;
use gandr_core_term::CoreArena;
use gandr_core_term::hole::HoleId;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::boundary::ItemOrdinal;

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
}

impl Layout
{
    /// The layout of `items`: each item's reference, and the maps from
    /// positions and references to items.
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
    /// # Cost
    /// - allocation: the references, the occupied positions and the named
    ///   items, durable by the program's layout
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Program::new`], which lays its items out here.
    /// - witness: `region::tests::positions_must_ascend_and_may_skip`
    /// - witness: `region::tests::a_repeated_key_counts_its_occurrences`
    /// - witness: `region::tests::empty_and_extreme_programs_resolve_exactly`
    /// - witness: `region::tests::the_first_position_violation_wins`
    #[spec(
        captures: item_count = items.len(),
        ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|layout| {
            layout.items.len() == item_count
                && layout.references.len() == item_count
                && layout.occupied.len() == item_count
                && layout.named.len() == item_count
        }),
    )]
    #[inline]
    pub fn new(items: Vec<Item>) -> Result<Self, ProgramError>
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
            items,
            references,
            occupied,
            named,
        })
    }

    /// The ordinal of the item at the admission position `position`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn ordinal(
        &self,
        position: ConstantIndex,
    ) -> Option<ItemOrdinal>
    {
        self.occupied.get(&position).copied()
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

impl gandr_core_content::Resolver for Layout
{
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
    ///
    /// # Cost
    /// - allocation: a copy of the reference, growth within the layout
    #[spec(ensures: |ret| self.occupied.get(&position)
        .and_then(|&ordinal| self.references.get(usize::from(ordinal)))
        .map_or_else(|| ret == Reference::Unoccupied, |reference| ret == *reference))]
    #[inline]
    fn resolve(
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

    /// The position of the item that `reference` names, as
    /// [`crate::content::place`] reads it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn place(
        &self,
        reference: &Reference,
    ) -> Maybe<ConstantIndex, gandr_core_content::seating::Absent>
    {
        crate::content::place(self, reference)
    }
}

/// How a pass opens its checking context.
#[derive(Clone, Copy, Debug)]
pub enum Opened<'leading>
{
    /// At the first item, under the allowance.
    Fresh(gandr_core_checker::CheckBudget),
    /// After the leading items, from the checkpoint of their context.
    Resumed(&'leading gandr_core_checker::Checkpoint),
}

impl Opened<'_>
{
    /// A context with no setting of a front end: a fresh one under the
    /// allowance, or one resumed from a copy of the checkpoint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn bare(
        self,
        arena: &mut CoreArena,
    ) -> gandr_core_checker::CheckingContext<'_>
    {
        match self {
            Self::Fresh(budget) => gandr_core_checker::CheckingContext::new(arena, budget),
            Self::Resumed(checkpoint) => {
                gandr_core_checker::CheckingContext::resume(arena, checkpoint.clone())
            },
        }
    }
}

/// An endpoint tier as its own constructor builds it, beside the policy a
/// closed pair crosses under. A tier keeps state, so each context that an
/// [`Opener`] opens gets a new one.
///
/// # Specification
/// - executable: none — a constructor, which no predicate inspects;
///   [`Opener::settle`] states what a context gets.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Opener`].
/// - witness: `tests::incremental::a_pass_hands_its_context_the_program_s_tier_2282`
#[derive(Clone, Copy, Debug)]
pub struct Tier
{
    /// The tier's own constructor, which builds one tier for each context.
    new: fn() -> Box<dyn gandr_core_checker::tier::EndpointTier>,
    /// The policy a closed pair crosses under.
    admitting: gandr_kernel_core::AdmissionPolicy,
}

impl Tier
{
    /// The tier that `new` builds, under `admitting`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        new: fn() -> Box<dyn gandr_core_checker::tier::EndpointTier>,
        admitting: gandr_kernel_core::AdmissionPolicy,
    ) -> Self
    {
        Self { new, admitting }
    }
}

impl PartialEq for Tier
{
    /// Two tiers are equal when one constructor builds both under one policy.
    /// A constructor that has two addresses compares unequal, which costs a
    /// memo miss and never a wrong hit.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        core::ptr::fn_addr_eq(self.new, other.new) && self.admitting == other.admitting
    }
}

impl Eq for Tier
{
}

/// The settings each checking context of a program opens under: the tier it
/// decides closed pairs on, the store it keeps strata in, and the module's
/// pattern holes, reducts and literal readers.
///
/// A front end hands the settings it opens its own judgement's context under,
/// so a pass decides each item as the judgement does. The settings are data:
/// a pass reads them and calls no closure.
///
/// # Specification
/// - executable: none — [`Opener::settle`] states what a context gets.
///
/// # Adequacy
/// - hypothesis: L3 — a tier and a stratum store that the opener hands are read
///   by a fresh pass and by one resumed after leading items, and a program with
///   a bare opener reads neither.
/// - witness: `tests::incremental::a_pass_hands_its_context_the_program_s_tier_2282`
/// - witness: `tests::incremental::a_pass_hands_its_context_the_program_s_stratum_store_4034`
#[derive(Clone, Debug, Default)]
pub struct Opener
{
    /// The tier each context decides closed pairs on, new for each context.
    tier: Option<Tier>,
    /// The store each context keeps its strata in.
    strata: Option<Arc<dyn gandr_core_checker::ua::StratumStore>>,
    /// The holes the module's matches were written with in place of a
    /// pattern.
    holes: Vec<HoleId>,
    /// The reducts and the forgetting maps the module mints.
    reducts: Vec<ConstantIndex>,
    /// The literal readers the module lends.
    readers: Vec<gandr_core_term::LiteralReader>,
}

impl Opener
{
    /// The opener of a program that no front end prepares: each context is
    /// [`Opened::bare`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn bare() -> Self
    {
        Self {
            tier: None,
            strata: None,
            holes: Vec::new(),
            reducts: Vec::new(),
            readers: Vec::new(),
        }
    }

    /// This opener, whose contexts also decide each closed pair on a new
    /// tier that `tier` builds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn deciding_on(
        mut self,
        tier: Tier,
    ) -> Self
    {
        self.tier = Some(tier);
        self
    }

    /// This opener, whose contexts also keep their strata in `store`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn keeping_strata_in(
        mut self,
        store: Arc<dyn gandr_core_checker::ua::StratumStore>,
    ) -> Self
    {
        self.strata = Some(store);
        self
    }

    /// This opener, whose contexts also keep `holes`, `reducts` and
    /// `readers`: the module's pattern holes, its reducts with its forgetting
    /// maps, and its literal readers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn keeping(
        mut self,
        holes: Vec<HoleId>,
        reducts: Vec<ConstantIndex>,
        readers: Vec<gandr_core_term::LiteralReader>,
    ) -> Self
    {
        self.holes = holes;
        self.reducts = reducts;
        self.readers = readers;
        self
    }

    /// Hand `context` these settings: a new tier, the stratum store, the
    /// pattern holes, the reducts and the literal readers.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `context` offers each closed pair to a new tier of
    ///   [`Opener::deciding_on`] first, keeps its strata in the store of
    ///   [`Opener::keeping_strata_in`], and holds each hole, reduct and reader
    ///   of [`Opener::keeping`]; a setting the opener does not hold leaves the
    ///   context as it was.
    /// - panics: none.
    /// - executable: none — the tier is a trait object no predicate compares,
    ///   and the holes and reducts are the context's own to read.
    ///
    /// # Cost
    /// - allocation: the context's tier and its copies of the settings, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Opener`].
    /// - witness: `tests::incremental::a_pass_hands_its_context_the_program_s_tier_2282`
    /// - witness: `tests::incremental::a_pass_hands_its_context_the_program_s_stratum_store_4034`
    #[inline]
    pub fn settle(
        &self,
        context: &mut gandr_core_checker::CheckingContext<'_>,
    )
    {
        if let Some(tier) = self.tier {
            context.decide_endpoints_on((tier.new)(), tier.admitting);
        }
        if let Some(store) = self.strata.as_ref() {
            context.keep_strata_in(Arc::clone(store));
        }
        context.keep_pattern_holes(&self.holes);
        context.keep_reducts(&self.reducts);
        context.keep_readers(&self.readers);
    }

    /// The context the opener opens over `arena`, as `opened` says.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the context and its settings, setup
    fn open<'arena>(
        &self,
        arena: &'arena mut CoreArena,
        opened: Opened<'_>,
    ) -> gandr_core_checker::CheckingContext<'arena>
    {
        let mut context = opened.bare(arena);
        self.settle(&mut context);
        context
    }
}

impl PartialEq for Opener
{
    /// Two openers are equal when they hold equal tiers, one stratum store,
    /// and equal holes, reducts and readers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        let strata = match (self.strata.as_ref(), other.strata.as_ref()) {
            (Some(store), Some(theirs)) => Arc::ptr_eq(store, theirs),
            (None, None) => true,
            (Some(_), None) | (None, Some(_)) => false,
        };
        self.tier == other.tier
            && strata
            && self.holes == other.holes
            && self.reducts == other.reducts
            && self.readers == other.readers
    }
}

impl Eq for Opener
{
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
    /// What opens each context a pass over the program makes.
    opener: Opener,
    /// The entry the host bounds every declaration of each pass by.
    host: gandr_core_checker::worlds::HostEntry,
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
        Ok(Self::over(arena, Layout::new(items)?))
    }

    /// The program of the items that `layout` lays out, over `arena`.
    ///
    /// # Specification
    /// - requires: `layout`'s items declare over `arena`.
    /// - ensures: [`Self::arena`] is `arena`, and the items are `layout`'s.
    /// - panics: none.
    /// - executable: none — a construction from its parts.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Program::new`], which builds each program here.
    /// - witness: `region::tests::positions_must_ascend_and_may_skip`
    #[inline]
    #[must_use]
    pub fn over(
        arena: CoreArena,
        layout: Layout,
    ) -> Self
    {
        Self {
            arena,
            layout,
            opener: Opener::bare(),
            host: gandr_core_checker::worlds::HostEntry::Unbounded,
        }
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

    /// Open each later pass's context with `opener`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every later pass opens its context with `opener`; the last
    ///   opener handed is the one kept.
    /// - provides: the front end's hand-in of its context's settings to the
    ///   incremental checker, whose passes make their own contexts.
    /// - panics: none.
    /// - executable: none — the opener holds a tier's constructor, which no
    ///   predicate inspects.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Opener`].
    /// - witness: `tests::incremental::a_pass_hands_its_context_the_program_s_tier_2282`
    /// - witness: `tests::incremental::a_pass_hands_its_context_the_program_s_stratum_store_4034`
    #[inline]
    pub fn open_contexts_with(
        &mut self,
        opener: Opener,
    )
    {
        self.opener = opener;
    }

    /// The context of a pass over the program, opened as `opened` says under
    /// the program's opener and entered at its host, beside the layout the
    /// pass reads.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the context, its settings and its entry, setup
    pub(crate) fn open(
        &mut self,
        opened: Opened<'_>,
    ) -> (gandr_core_checker::CheckingContext<'_>, &Layout)
    {
        let mut context = self.opener.open(&mut self.arena, opened);
        context.enter_at(self.host.clone());
        (context, &self.layout)
    }

    /// Bound the entry of every declaration each later pass judges by
    /// `host`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every later pass's context is handed `host`
    ///   ([`gandr_core_checker::CheckingContext::enter_at`]); the last entry
    ///   handed is the one kept.
    /// - provides: the front end's hand-in of the host's grant to the
    ///   incremental checker, whose passes make their own contexts.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two passes over one located program under two grants
    ///   judge again each declaration whose resolved entry moves, and adopt
    ///   every other.
    /// - witness: `tests::worlds::a_changed_grant_judges_again_each_entry_it_moves_3381`
    #[spec(captures: host_before = host.clone(), ensures: self.host == host_before)]
    #[inline]
    pub fn enter_at(
        &mut self,
        host: gandr_core_checker::worlds::HostEntry,
    )
    {
        self.host = host;
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
