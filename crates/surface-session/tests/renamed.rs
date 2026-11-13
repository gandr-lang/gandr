//! A composition read up to a renaming of its arena's nodes (#6620).
//!
//! A judgement that takes a standing declaration from the last pass mints
//! none of the nodes that a decision of it mints. So each node that the rest
//! of the judgement mints stands at another id than in a judgement that
//! decides each declaration. The ids stay inside the session: a diagnostic
//! reads each one against its own arena. The reading here replaces each id
//! with the hash of its node's content, its children by their own hashes, so
//! two compositions read alike exactly when they name nodes of equal content
//! at each place.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write as _;
use core::hash::Hash;
use core::hash::Hasher as _;
use std::hash::DefaultHasher;

use anodized::spec;
use gandr_core_term::ArenaWatermark;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_surface_dispatcher::Composed;

/// The four families of an arena's nodes, each with the name its id prints
/// under.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Family
{
    /// A [`ValueId`].
    Value,
    /// A [`ComputationId`].
    Computation,
    /// A [`ValueTypeId`].
    ValueType,
    /// A [`CompTypeId`].
    CompType,
}

impl Family
{
    /// Each family with the name its id prints under, `ValueTypeId` before
    /// `ValueId` so neither reads as the other.
    const PRINTED: [(Self, &'static str); 4] = [
        (Self::ValueType, "ValueTypeId("),
        (Self::Value, "ValueId("),
        (Self::Computation, "ComputationId("),
        (Self::CompType, "CompTypeId("),
    ];
}

/// One node of an arena: its family and its place in the family.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Node
{
    /// The family.
    family: Family,
    /// The place in the family.
    place: usize,
}

/// The hash of a node's content.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Digest(u64);

/// A composition's printed form, each id replaced by its node's [`Digest`].
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reading(String);

/// The ids of one arena, by family and place, and the digest of each node read
/// so far.
struct Renaming<'arena>
{
    /// The arena.
    arena: &'arena CoreArena,
    /// The value ids, by place.
    values: Vec<ValueId>,
    /// The computation ids, by place.
    computations: Vec<ComputationId>,
    /// The value-type ids, by place.
    value_types: Vec<ValueTypeId>,
    /// The computation-type ids, by place.
    comp_types: Vec<CompTypeId>,
    /// The digest of each node read so far.
    digests: BTreeMap<Node, Digest>,
}

impl<'arena> Renaming<'arena>
{
    /// The renaming of `arena`, no node read yet.
    ///
    /// # Specification
    /// trivial.
    fn new(arena: &'arena CoreArena) -> Self
    {
        let empty = ArenaWatermark::default();
        Self {
            arena,
            values: arena.values_since(empty).collect(),
            computations: arena.computations_since(empty).collect(),
            value_types: arena.value_types_since(empty).collect(),
            comp_types: arena.comp_types_since(empty).collect(),
            digests: BTreeMap::new(),
        }
    }

    /// The printed form of `node`, or `dangling` for a place the arena does
    /// not hold.
    ///
    /// # Specification
    /// trivial.
    fn printed(
        &self,
        node: Node,
    ) -> Printed
    {
        let printed = match node.family {
            Family::Value => self
                .values
                .get(node.place)
                .and_then(|&id| self.arena.value(id))
                .map(|value| format!("{value:?}")),
            Family::Computation => self
                .computations
                .get(node.place)
                .and_then(|&id| self.arena.computation(id))
                .map(|computation| format!("{computation:?}")),
            Family::ValueType => self
                .value_types
                .get(node.place)
                .and_then(|&id| self.arena.value_type(id))
                .map(|value_type| format!("{value_type:?}")),
            Family::CompType => self
                .comp_types
                .get(node.place)
                .and_then(|&id| self.arena.comp_type(id))
                .map(|comp_type| format!("{comp_type:?}")),
        };
        Printed(printed.unwrap_or_else(|| String::from("dangling")))
    }

    /// The digest of `root`, read with each node below it that no digest
    /// holds yet. An arena mints each child before its parent, so the walk
    /// ends.
    ///
    /// # Specification
    /// trivial.
    fn digest(
        &mut self,
        root: Node,
    ) -> Digest
    {
        let mut pending = Vec::from([root]);
        while let Some(&node) = pending.last() {
            if self.digests.contains_key(&node) {
                let _done = pending.pop();
                continue;
            }
            let printed = self.printed(node);
            let unread: Vec<Node> = printed
                .named()
                .into_iter()
                .map(|named| named.node)
                .filter(|child| !self.digests.contains_key(child))
                .collect();
            if unread.is_empty() {
                let mut hasher = DefaultHasher::new();
                node.family.hash(&mut hasher);
                self.substituted(&printed).hash(&mut hasher);
                let _held = self.digests.insert(node, Digest(hasher.finish()));
                let _done = pending.pop();
            }
            else {
                pending.extend(unread);
            }
        }
        self.digests.get(&root).copied().unwrap_or(Digest(0))
    }

    /// `printed` with each id it names replaced by the digest of its node,
    /// each of which [`Self::digest`] read already.
    ///
    /// # Specification
    /// trivial.
    fn substituted(
        &self,
        printed: &Printed,
    ) -> String
    {
        let Printed(ref text) = *printed;
        let mut out = String::with_capacity(text.len());
        let mut from = 0;
        for named in printed.named() {
            out.push_str(text.get(from .. named.digits).unwrap_or_default());
            let Digest(digest) = self.digests.get(&named.node).copied().unwrap_or(Digest(0));
            let _written = write!(out, "#{digest:016x})");
            from = named.end;
        }
        out.push_str(text.get(from ..).unwrap_or_default());
        out
    }
}

/// A composition's printed form, as its `Debug` form writes it.
#[repr(transparent)]
struct Printed(String);

/// One id that a [`Printed`] form names: the node, and the byte spans of its
/// place and of its whole text.
struct Named
{
    /// The byte at which the id's place starts, past its name.
    digits: usize,
    /// The byte past the id's text.
    end: usize,
    /// The node the id names.
    node: Node,
}

impl Printed
{
    /// Each id that this form names, in order.
    ///
    /// # Specification
    /// trivial.
    fn named(&self) -> Vec<Named>
    {
        let Self(ref printed) = *self;
        let mut found = Vec::new();
        for (family, name) in Family::PRINTED {
            let mut from = 0;
            while let Some(at) = printed.get(from ..).and_then(|rest| rest.find(name)) {
                let start = from.saturating_add(at);
                let digits = start.saturating_add(name.len());
                from = digits;
                // A longer name that ends in this one, as `FormedValueTypeId`
                // would, is not this id.
                if printed
                    .get(.. start)
                    .and_then(|before| before.chars().next_back())
                    .is_some_and(char::is_alphanumeric)
                {
                    continue;
                }
                let rest = printed.get(digits ..).unwrap_or_default();
                let length = rest.chars().take_while(char::is_ascii_digit).count();
                let Some(place) = rest.get(.. length).and_then(|text| text.parse().ok())
                else {
                    continue;
                };
                if rest
                    .get(length ..)
                    .is_some_and(|tail| tail.starts_with(')'))
                {
                    found.push(Named {
                        digits,
                        end: digits.saturating_add(length).saturating_add(1),
                        node: Node { family, place },
                    });
                }
            }
        }
        found.sort_by_key(|named| named.digits);
        found
    }
}

/// `composed` read up to a renaming of the nodes of `arena`, the arena its ids
/// name.
///
/// # Specification
/// - ensures: two compositions whose arenas number equal nodes apart read
///   alike, and a node of other content at one place reads apart.
/// - panics: never.
///
/// # Adequacy
/// - hypothesis: L3 — a taken declaration's type at another id reads as the
///   decided declaration's type, and the reports of an edit that takes its
///   standing declarations read as a fresh session's.
/// - witness: `tests::incremental::deletion_matches_from_scratch`
/// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
#[spec(ensures: |ret| !ret.0.is_empty())]
pub fn renamed(
    composed: &Composed<'_>,
    arena: &CoreArena,
) -> Reading
{
    let printed = Printed(format!("{composed:?}"));
    let mut renaming = Renaming::new(arena);
    for named in printed.named() {
        let _digest = renaming.digest(named.node);
    }
    Reading(renaming.substituted(&printed))
}
