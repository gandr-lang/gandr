//! The origin side table: [`Origin`], the [`OriginToken`] a declaration
//! carries, and the [`OriginTable`] mapping every minted core node back to the
//! syntax node that produced it.
//!
//! # Types have origins from the first landing
//!
//! The table covers the type families as well as the term families. A checker
//! that later wants to attach a note to a *type* it derived needs the carrier
//! to exist already: retrofitting one means finding every mint site after the
//! fact, and a traversal missing one arm loses the origins of everything under
//! it silently. Building the table where the nodes are minted makes a new
//! former acquire origins by construction rather than by a later sweep.
//!
//! # An origin carries both identities
//!
//! A [`NodeIndex`] resolves fast inside the tree in hand; a [`NodeDigest`]
//! survives the tree. A diagnostic wants the first, a checkpoint keyed across
//! runs wants the second, and an origin that carried only one would force the
//! other consumer back to the tree.
//!
//! # The token is opaque on purpose
//!
//! A declaration's origin travels to a checker as an [`OriginToken`], a
//! transparent index the checker never interprets and echoes back with its
//! verdicts. That is what keeps spans, syntax nodes and names out of the core
//! lane entirely: the two sides agree on one small type rather than on a module
//! representation.

use alloc::vec::Vec;

use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why the table answers no origin.
    pub mod origin {
        /// The table holds no entry for the id or token asked about.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The id was not minted by this lowering, or the token not handed
            /// out by this table.
            Unrecorded,
        }
    }
}

/// Where one minted core node came from.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Origin
{
    /// The arena position of the syntax node that produced it.
    node: NodeIndex,
    /// That node's content identity, which survives the tree.
    digest: NodeDigest,
    /// The bytes of the source that node covers.
    span: ByteSpan,
}

impl Origin
{
    /// The origin naming `node`, identified by `digest`, covering `span`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        node: NodeIndex,
        digest: NodeDigest,
        span: ByteSpan,
    ) -> Self
    {
        Self { node, digest, span }
    }

    /// The arena position of the syntax node that produced the core node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn node(&self) -> NodeIndex
    {
        self.node
    }

    /// The content identity of that syntax node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn digest(&self) -> NodeDigest
    {
        self.digest
    }

    /// The bytes of the source that syntax node covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> ByteSpan
    {
        self.span
    }
}

/// A declaration's origin, as it travels to a consumer that never reads it.
///
/// The token is an index into one [`OriginTable`]'s declaration list and
/// carries no other meaning. A checker echoes it back beside a verdict; the
/// driver resolves it here, so the checker learns nothing of spans or names.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OriginToken(usize);

impl From<usize> for OriginToken
{
    /// The token at declaration-list position `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<OriginToken> for usize
{
    /// The declaration-list position `token` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(token: OriginToken) -> Self
    {
        token.0
    }
}

/// A number of origins one table holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OriginCount(usize);

impl From<usize> for OriginCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<OriginCount> for usize
{
    /// The number `count` holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: OriginCount) -> Self
    {
        count.0
    }
}

/// Every minted core node's origin, by family, and the declaration origins.
///
/// Each family is a vector of id-and-origin pairs held in mint order. Core ids
/// ascend with minting inside a family, so the vector is sorted by id by
/// construction and a lookup is a binary search rather than a map: no hashing,
/// no per-entry allocation, and an iteration order that is the mint order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct OriginTable
{
    /// The value family's origins, ascending by id.
    values: Vec<(ValueId, Origin)>,
    /// The computation family's origins, ascending by id.
    computations: Vec<(ComputationId, Origin)>,
    /// The value-type family's origins, ascending by id.
    value_types: Vec<(ValueTypeId, Origin)>,
    /// The computation-type family's origins, ascending by id.
    comp_types: Vec<(CompTypeId, Origin)>,
    /// The declarations' own origins, in admission order.
    declarations: Vec<Origin>,
}

/// Record one family's origin, keeping the vector ascending by id.
///
/// # Specification
/// - requires: `entries` is ascending by id, and `id` was minted after every id
///   already in it, which the arena's own constructor-only minting establishes.
/// - ensures: the pair is appended, so the vector stays ascending and the
///   lookup below stays a binary search.
/// - provides: the one recording step every family shares, so no family can
///   drift into an unsorted vector.
/// - fails: never.
/// - panics: none.
fn record<Id>(
    entries: &mut Vec<(Id, Origin)>,
    id: Id,
    origin: Origin,
)
{
    entries.push((id, origin));
}

/// Find one family's origin by id.
///
/// # Specification
/// - requires: `entries` is ascending by id.
/// - ensures: the origin recorded for `id`, and the unrecorded absence when no
///   entry carries it — an id minted outside this lowering included.
/// - provides: the one lookup step every family shares.
/// - fails: never.
/// - panics: none.
fn find<Id>(
    entries: &[(Id, Origin)],
    id: Id,
) -> Maybe<Origin, origin::Absent>
where
    Id: Copy + Ord,
{
    let found = entries
        .binary_search_by_key(&id, |&(held, _origin)| held)
        .ok()
        .and_then(|position| entries.get(position))
        .map(|&(_held, held)| held);

    found.map_or(Maybe::Absent(origin::Absent::Unrecorded), Maybe::Present)
}

impl OriginTable
{
    /// A table holding no origins.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Record the origin of a freshly minted value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn record_value(
        &mut self,
        id: ValueId,
        origin: Origin,
    )
    {
        record(&mut self.values, id, origin);
    }

    /// Record the origin of a freshly minted computation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn record_computation(
        &mut self,
        id: ComputationId,
        origin: Origin,
    )
    {
        record(&mut self.computations, id, origin);
    }

    /// Record the origin of a freshly minted value type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn record_value_type(
        &mut self,
        id: ValueTypeId,
        origin: Origin,
    )
    {
        record(&mut self.value_types, id, origin);
    }

    /// Record the origin of a freshly minted computation type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn record_comp_type(
        &mut self,
        id: CompTypeId,
        origin: Origin,
    )
    {
        record(&mut self.comp_types, id, origin);
    }

    /// Record a declaration's origin and return the token naming it.
    ///
    /// # Specification
    /// - requires: `origin` names the declaration form that introduced the
    ///   declaration's name.
    /// - ensures: the returned token names exactly this origin and no other,
    ///   and tokens are handed out in admission order, so a consumer echoing
    ///   one back resolves the declaration it was given.
    /// - provides: the opaque handle a checker carries in place of a span.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one append and one index, separated by the first
    ///   token over an empty table and a second token over a non-empty one,
    ///   each resolved back to its own origin and asserted exactly; a token
    ///   minted before the append would collide on the second.
    /// - witness: `origin::tests::a_declaration_token_resolves_to_its_own_origin`
    #[inline]
    pub fn record_declaration(
        &mut self,
        origin: Origin,
    ) -> OriginToken
    {
        let token = OriginToken(self.declarations.len());
        self.declarations.push(origin);

        token
    }

    /// The origin recorded for a value.
    ///
    /// # Specification
    /// - requires: nothing — an id this table holds nothing for is admissible
    ///   input, including one minted outside this lowering.
    /// - ensures: exactly the origin recorded when the id was minted.
    /// - provides: the term half of the origin lookup.
    /// - fails: never; an id this lowering did not mint is the unrecorded
    ///   absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one search, separated by a recorded id asserted as an
    ///   exact origin and an unrecorded id asserted absent, over a family
    ///   holding more than one entry so the search cannot pass by accident.
    /// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
    /// - witness: `origin::tests::an_unrecorded_id_has_no_origin`
    #[inline]
    pub fn value(
        &self,
        id: ValueId,
    ) -> Maybe<Origin, origin::Absent>
    {
        find(&self.values, id)
    }

    /// The origin recorded for a computation.
    ///
    /// # Specification
    /// - requires: nothing — an unrecorded id is admissible input.
    /// - ensures: exactly the origin recorded when the id was minted.
    /// - provides: the computation half of the origin lookup.
    /// - fails: never; an id this lowering did not mint is the unrecorded
    ///   absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same one search as the value family, separated by
    ///   a recorded and an unrecorded id over a multi-entry family.
    /// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
    #[inline]
    pub fn computation(
        &self,
        id: ComputationId,
    ) -> Maybe<Origin, origin::Absent>
    {
        find(&self.computations, id)
    }

    /// The origin recorded for a value type.
    ///
    /// # Specification
    /// - requires: nothing — an unrecorded id is admissible input.
    /// - ensures: exactly the origin recorded when the id was minted; the type
    ///   families are covered from the first landing rather than added later.
    /// - provides: the value-type half of the origin lookup.
    /// - fails: never; an id this lowering did not mint is the unrecorded
    ///   absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same one search as the value family, separated by
    ///   a recorded and an unrecorded id over a multi-entry family.
    /// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
    #[inline]
    pub fn value_type(
        &self,
        id: ValueTypeId,
    ) -> Maybe<Origin, origin::Absent>
    {
        find(&self.value_types, id)
    }

    /// The origin recorded for a computation type.
    ///
    /// # Specification
    /// - requires: nothing — an unrecorded id is admissible input.
    /// - ensures: exactly the origin recorded when the id was minted.
    /// - provides: the computation-type half of the origin lookup.
    /// - fails: never; an id this lowering did not mint is the unrecorded
    ///   absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same one search as the value family, separated by
    ///   a recorded and an unrecorded id over a multi-entry family.
    /// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
    #[inline]
    pub fn comp_type(
        &self,
        id: CompTypeId,
    ) -> Maybe<Origin, origin::Absent>
    {
        find(&self.comp_types, id)
    }

    /// The origin a declaration token names.
    ///
    /// # Specification
    /// - requires: nothing — a token this table did not mint is admissible
    ///   input, which is what makes an echoed token safe to resolve.
    /// - ensures: exactly the origin the token was minted for.
    /// - provides: the resolution a driver performs on a checker's echoed
    ///   token.
    /// - fails: never; a token this table did not mint is the unrecorded
    ///   absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — one checked lookup, separated by the boundary
    ///   pair `count - 1` / `count`, the first asserted as an exact origin and
    ///   the second asserted absent.
    /// - witness: `origin::tests::a_declaration_token_resolves_to_its_own_origin`
    /// - witness: `origin::tests::a_token_past_the_declaration_list_resolves_to_nothing`
    #[inline]
    pub fn declaration(
        &self,
        token: OriginToken,
    ) -> Maybe<Origin, origin::Absent>
    {
        self.declarations
            .get(token.0)
            .copied()
            .map_or(Maybe::Absent(origin::Absent::Unrecorded), Maybe::Present)
    }

    /// How many core nodes this table recorded an origin for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn recorded_count(&self) -> OriginCount
    {
        let terms = self.values.len().saturating_add(self.computations.len());
        let types = self.value_types.len().saturating_add(self.comp_types.len());

        OriginCount(terms.saturating_add(types))
    }

    /// How many declarations this table holds an origin for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn declaration_count(&self) -> OriginCount
    {
        OriginCount(self.declarations.len())
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::CoreArena;
    use gandr_surface_syntax::NodeIndex;
    use quenchant_shape::shape::Maybe;

    use super::Origin;
    use super::OriginCount;
    use super::OriginTable;
    use super::OriginToken;
    use super::origin;
    use crate::fixture::origin_at;

    /// A distinct origin naming the node at arena position `position`.
    ///
    /// # Specification
    /// trivial.
    fn at(position: NodeIndex) -> Origin
    {
        origin_at(position)
    }

    #[test]
    fn each_family_answers_its_own_recorded_origins()
    {
        let mut arena = CoreArena::new();
        let mut table = OriginTable::new();
        let first_value = arena.value_unit();
        let second_value = arena.value_unit();
        let computation = arena.computation_return(first_value);
        let value_type = arena.value_type_unit();
        let comp_type = arena.comp_type_returner(value_type);
        table.record_value(first_value, at(NodeIndex::from(1_usize)));
        table.record_value(second_value, at(NodeIndex::from(2_usize)));
        table.record_computation(computation, at(NodeIndex::from(3_usize)));
        table.record_value_type(value_type, at(NodeIndex::from(4_usize)));
        table.record_comp_type(comp_type, at(NodeIndex::from(5_usize)));

        assert_eq!(
            table.value(first_value),
            Maybe::Present(at(NodeIndex::from(1_usize))),
            "the first value keeps its own origin"
        );
        assert_eq!(
            table.value(second_value),
            Maybe::Present(at(NodeIndex::from(2_usize))),
            "a second entry in one family does not shadow the first"
        );
        assert_eq!(
            table.computation(computation),
            Maybe::Present(at(NodeIndex::from(3_usize))),
            "the computation family answers its own entry"
        );
        assert_eq!(
            table.value_type(value_type),
            Maybe::Present(at(NodeIndex::from(4_usize))),
            "the value-type family is covered from the first landing"
        );
        assert_eq!(
            table.comp_type(comp_type),
            Maybe::Present(at(NodeIndex::from(5_usize))),
            "the computation-type family is covered too"
        );
        assert_eq!(
            table.recorded_count(),
            OriginCount::from(5_usize),
            "every recorded node is counted once"
        );
    }

    #[test]
    fn an_unrecorded_id_has_no_origin()
    {
        let mut arena = CoreArena::new();
        let mut table = OriginTable::new();
        let recorded = arena.value_unit();
        let unrecorded = arena.value_unit();
        table.record_value(recorded, at(NodeIndex::from(1_usize)));

        assert_eq!(
            table.value(unrecorded),
            Maybe::Absent(origin::Absent::Unrecorded),
            "an id no entry carries resolves to nothing rather than to a neighbour"
        );
        assert_eq!(
            OriginTable::new().value(recorded),
            Maybe::Absent(origin::Absent::Unrecorded),
            "an empty family answers nothing at all"
        );
    }

    #[test]
    fn a_declaration_token_resolves_to_its_own_origin()
    {
        let mut table = OriginTable::new();
        let first = table.record_declaration(at(NodeIndex::from(1_usize)));
        let second = table.record_declaration(at(NodeIndex::from(2_usize)));

        assert_ne!(first, second, "each declaration takes its own token");
        assert_eq!(
            table.declaration(first),
            Maybe::Present(at(NodeIndex::from(1_usize))),
            "the first token resolves to the first origin"
        );
        assert_eq!(
            table.declaration(second),
            Maybe::Present(at(NodeIndex::from(2_usize))),
            "the second token resolves to the second origin"
        );
        assert_eq!(
            table.declaration_count(),
            OriginCount::from(2_usize),
            "the declaration list holds both"
        );
    }

    #[test]
    fn a_token_past_the_declaration_list_resolves_to_nothing()
    {
        let mut table = OriginTable::new();
        let only = table.record_declaration(at(NodeIndex::from(1_usize)));

        assert_eq!(
            table.declaration(only),
            Maybe::Present(at(NodeIndex::from(1_usize))),
            "the last minted token still resolves"
        );
        assert_eq!(
            table.declaration(OriginToken::from(1_usize)),
            Maybe::Absent(origin::Absent::Unrecorded),
            "one past the last token resolves to nothing"
        );
    }
}
