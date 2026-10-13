//! The origin side table: [`Origin`], the [`OriginToken`] a declaration
//! carries, and the [`OriginTable`] mapping every minted core node back to the
//! syntax node that produced it, written or inserted.
//!
//! # Origins for every node family
//!
//! The table covers type families as well as term families. A diagnostic can
//! resolve a derived type without recovering its origin from a second walk.
//! Each minting operation records its node in the corresponding family.
//!
//! # An origin carries a position
//!
//! A [`NodeIndex`] resolves fast inside the tree in hand, which is what a
//! diagnostic wants. A table keyed across runs reads the node's cross-tree key
//! from that tree ([`SyntaxTree::key`](gandr_surface_syntax::SyntaxTree::key)):
//! the key is a form's digest and a rank in it, so an origin carrying one
//! would be one more copy of what the tree already answers.
//!
//! # An inserted node says so
//!
//! The lowering writes five bridges the source did not spell — a force, a
//! thunk, a returner, a quote and a decode — at checked sites, by the sort of
//! the position, and two more: the nominal type of a constructor written
//! without an annotation, and the eliminations a match compiles to. Each
//! carries the origin of the syntax node whose position demanded it, marked
//! [`Provenance::Inserted`] with the [`Insertion`] it is, so a printer or a
//! diagnostic can show the cast a reader did not write, and every node the
//! source did write is [`Provenance::Written`].
//!
//! # A match keeps its arms
//!
//! A match lowers to a decision tree of native eliminations, so its patterns
//! do not survive into the core term. The table keeps them beside it: per
//! lowered match, a [`CaseOrigin`] holding the pattern table its arms are
//! written in, one [`ArmOrigin`] per arm alternative, and the syntax nodes of
//! the scrutinee and every pattern and body. A live match and a coverage
//! report read the arms from here and the tree from the arena.
//!
//! # A binder keeps its name
//!
//! The core is nameless: a lambda or a bind opens a binder by position. The
//! table keeps, per lambda a function parameter lowers to and per bind a named
//! `run` statement lowers to, the origin of the name the source wrote, so a
//! diagnostic can say which name a hypothesis of the checker is. A split, a
//! discarded statement and a lambda the lowering inserted record none.
//!
//! # The token is opaque on purpose
//!
//! A declaration's origin travels to a checker as an [`OriginToken`], a
//! transparent index the checker never interprets and echoes back with its
//! verdicts. That is what keeps spans, syntax nodes and names out of the core
//! lane entirely: the two sides agree on one small type rather than on a module
//! representation.
//!
//! # Origins for terms and types
//!
//! Every minted core node records the syntax node that produced it — its arena
//! position and its span — for values, computations, value types and
//! computation types alike, so a later note about a type has a carrier already,
//! and whether the author wrote it or the lowering inserted it. A grouping
//! mints nothing and its content keeps its own origin. A declaration's origin
//! travels as an opaque `OriginToken` that a checker echoes back, which keeps
//! spans and names out of the core. An origin carries no cross-tree identity: a
//! table keyed across runs reads the node's key from the tree it was lowered
//! from (`SyntaxTree::key`).
//!
//! Lookup uses arena-local IDs and table-local indices, not ownership
//! certificates. Equal IDs from separate arenas and equal tokens from separate
//! tables resolve in the table queried; only a missing key or out-of-range
//! token yields the unrecorded absence. Callers retain the associated arena and
//! table. Authenticating minting context would require a different identifier
//! model; revisit this choice if the side table becomes an ownership boundary.
//!
//! # A variable keeps its binder
//!
//! Every variable the lowering mints for a name the source wrote records the
//! span of the binder the name resolved to, so a face goes from a use to its
//! binder — a hover over the binder answers its uses' type; a definition
//! request, its binder — without resolving the name again. A variable the
//! lowering inserts, and one whose binder the source names nothing, records
//! none. Witness: `lower::tests::a_variable_keeps_its_binder`.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why the table answers no origin.
    pub mod origin {
        /// The table holds no entry for the id or token asked about.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No entry has the requested id, or the token is outside this
            /// table's declaration list.
            Unrecorded,
        }
    }
}

/// One of the insertions the lowering writes at a checked site.
///
/// The five bridges, the classifier of a constructor written without one,
/// the eliminations a match compiles to, a recursive function's fixpoint, a
/// compound endpoint, and the transport a derived identity operation unfolds
/// to.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the tag distinguishes force, thunk, returner, quote, decode,
///   classifier, match, fixpoint, endpoint and identity.
/// - provides: the kind of an insertion recorded in an origin.
/// - fails: not applicable to the tag itself.
/// - panics: not applicable to the tag itself.
/// - executable: none — the tag carries no core node against which to check
///   that the named bridge was inserted.
///
/// # Adequacy
/// - hypothesis: L3 — an inserted force and a written origin remain distinct
///   through recording and lookup; this does not prove that a bridge was
///   needed.
/// - witness: `origin::tests::lookups_separate_gaps_from_declaration_origins`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Insertion
{
    /// A force over a value standing in an elimination head.
    Force,
    /// A thunk over a function's body, a computation standing where the
    /// declaration takes a value.
    Thunk,
    /// A returner over a value type standing in a function's result position.
    Returner,
    /// A quote over a type standing where a value is read: the code of the
    /// type.
    Quote,
    /// A decode over a value name standing where a type is read: the type the
    /// code denotes.
    Decode,
    /// The nominal type of a constructor of a family without parameters,
    /// which the source wrote no annotation for.
    Classifier,
    /// A node of the decision tree a match compiles to: a scrutinee bind, a
    /// native or sum case, a field lambda, a literal test, or a binding an arm
    /// body is read under.
    Match,
    /// The fixpoint a recursive function closes over its last parameter's
    /// lambda, binding the function's own name.
    Fixpoint,
    /// The value a computation returns, standing where a path type's endpoint
    /// or reflexivity's point is read: a compound endpoint.
    Endpoint,
    /// The motive, the base and the shifted endpoints of the transport `back`,
    /// `then` or `cong` unfolds to.
    Identity,
}

/// Whether the source wrote a minted core node or the lowering inserted it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: written syntax and an insertion of a named kind stay distinct.
/// - provides: provenance without requiring the core to retain surface syntax.
/// - fails: not applicable to the tag itself.
/// - panics: not applicable to the tag itself.
/// - executable: none — a provenance tag has neither the source tree nor the
///   core node whose production it describes.
///
/// # Adequacy
/// - hypothesis: L3 — exact origin equality separates a written node from an
///   inserted force. The fixture checks preservation, not historical truth.
/// - witness: `origin::tests::lookups_separate_gaps_from_declaration_origins`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Provenance
{
    /// The source wrote the form the node lowers.
    Written,
    /// The lowering wrote the node at a checked site, by the sort of the
    /// position the syntax node stands in.
    Inserted(Insertion),
}

/// Where one minted core node came from.
///
/// # Specification
/// - requires: nothing; the fields are admitted as supplied metadata.
/// - ensures: the syntax position, span and provenance are carried together,
///   without certifying that they describe one real node.
/// - provides: the metadata a diagnostic resolves for a minted core node.
/// - fails: not applicable to the record itself.
/// - panics: not applicable to the record itself.
/// - executable: none — the record does not retain the tree needed to verify
///   the association between its position and span.
///
/// # Adequacy
/// - hypothesis: L3 — distinct complete origin values survive multi-entry
///   lookup, including inserted provenance. No tree-membership claim is tested.
/// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
/// - witness: `origin::tests::lookups_separate_gaps_from_declaration_origins`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Origin
{
    /// The arena position of the syntax node that produced it.
    node: NodeIndex,
    /// The bytes of the source that node covers.
    span: ByteSpan,
    /// Whether the source wrote the core node or the lowering inserted it.
    provenance: Provenance,
}

impl Origin
{
    /// The origin of a node the source wrote at `node`, covering `span`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        node: NodeIndex,
        span: ByteSpan,
    ) -> Self
    {
        Self {
            node,
            span,
            provenance: Provenance::Written,
        }
    }

    /// The same syntax node, as the origin of the bridge `insertion` the
    /// lowering wrote at it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn inserted(
        self,
        insertion: Insertion,
    ) -> Self
    {
        Self {
            provenance: Provenance::Inserted(insertion),
            ..self
        }
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

    /// Whether the source wrote the core node or the lowering inserted it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn provenance(&self) -> Provenance
    {
        self.provenance
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
///
/// Core ids are arena-local slots, and declaration tokens are table-local
/// indices. Lookup compares keys, not their minting histories: equal keys from
/// different contexts are indistinguishable. Consumers retain the associated
/// arena and table when interpreting an origin.
///
/// # Specification
/// - requires: each recording call supplies an id after the preceding ids in
///   its family; origin metadata itself is not validated here.
/// - ensures: family entries are strictly ascending by id; declaration origins
///   occupy a separate append-only token space and do not enter the node
///   census.
/// - provides: lookup of supplied metadata by key equality, without validating
///   the key's minting context or consulting the syntax tree.
/// - fails: not applicable to the stored representation itself.
/// - panics: not applicable to the stored representation itself.
/// - executable: none — the facade's type-refinement expansion requires its
///   disabled logic feature; recording and census predicates check the order
///   obligation at function boundaries instead.
///
/// # Adequacy
/// - hypothesis: L3 — recording checks its new suffix and the census checks
///   strict order in every family. Fixtures separate family lookups, gaps and
///   declaration tokens; enforcement rejects a reversed value family. These
///   observations do not establish the provenance of supplied metadata.
/// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
/// - witness: `origin::tests::lookups_separate_gaps_from_declaration_origins`
/// - witness: `origin::tests::census_rejects_a_disordered_family`
/// - witness: `origin::tests::keys_do_not_certify_their_minting_context`
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
    /// Each lowered match's arms, ascending by the root of its tree.
    cases: Vec<(ComputationId, CaseOrigin)>,
    /// The name each lambda or bind binds, by the computation that opens the
    /// binder, ascending by id: the syntax the binder's name was written at.
    binders: Vec<(ComputationId, Origin)>,
    /// Each variable written in the source, with its binder's span, ascending
    /// by id.
    bindings: Vec<(ValueId, ByteSpan)>,
}

/// Record one family's origin, keeping the vector ascending by id.
///
/// # Specification
/// - requires: entries are strictly ascending by id, and `id` follows every
///   existing id in that family.
/// - ensures: the pair is appended, so the vector stays ascending and the
///   lookup below stays a binary search.
/// - provides: the one recording step every family shares, so no family can
///   drift into an unsorted vector.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the predicate checks the new id against the old suffix,
///   the exact length change and the appended pair. Preservation of earlier
///   origins is separated by looking them up after another append.
/// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
#[spec(
    requires: entries.last().is_none_or(|&(held, _)| held < id),
    captures: before = entries.len(),
    ensures: before.checked_add(1_usize) == Some(entries.len())
        && entries
            .last()
            .is_some_and(|&(held, ref written)| held == id && *written == origin),
)]
fn record<Id>(
    entries: &mut Vec<(Id, Origin)>,
    id: Id,
    origin: Origin,
) where
    Id: Copy + Ord,
{
    entries.push((id, origin));
}

/// Find one family's origin by id.
///
/// # Specification
/// - requires: entries are strictly ascending by id.
/// - ensures: the origin whose key equals `id`, or the unrecorded absence when
///   no entry has that key. Minting context is not part of the comparison.
/// - provides: the one lookup step every family shares.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a linear lookup is an independent oracle for the binary
///   search on its stated sorted domain. Fixtures cover hits, empty input and
///   missing ids before, within and after a nonempty family.
/// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
/// - witness: `origin::tests::an_unrecorded_id_has_no_origin`
/// - witness: `origin::tests::lookups_separate_gaps_from_declaration_origins`
/// - witness: `origin::tests::keys_do_not_certify_their_minting_context`
#[spec(
    ensures: |ret| {
        ret == entries
            .iter()
            .find(|&&(held, _)| held == id)
            .map_or(Maybe::Absent(origin::Absent::Unrecorded), |&(_, origin)| {
                Maybe::Present(origin)
            })
    },
)]
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
    /// - ensures: the returned token indexes exactly this appended origin in
    ///   this table; tokens follow admission order. Another table may mint an
    ///   equal token for a different origin.
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
    #[spec(
        captures: before = self.declarations.len(),
        ensures: |ret| {
            ret.0 == before
                && before.checked_add(1_usize) == Some(self.declarations.len())
                && self.declarations.get(ret.0) == Some(&origin)
        },
    )]
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
    /// - requires: nothing; every value id is admissible as a lookup key.
    /// - ensures: exactly the origin stored under an equal id in this table's
    ///   value family. The id's minting arena is not authenticated.
    /// - provides: the term half of the origin lookup.
    /// - fails: never; a key with no entry yields the unrecorded absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one search, separated by a recorded id asserted as an
    ///   exact origin and an unrecorded id asserted absent, over a family
    ///   holding more than one entry so the search cannot pass by accident. The
    ///   predicate re-asks the logarithmic search over this family; the shared
    ///   lookup's own clause holds the linear oracle.
    /// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
    /// - witness: `origin::tests::an_unrecorded_id_has_no_origin`
    /// - witness: `origin::tests::keys_do_not_certify_their_minting_context`
    #[spec(
        ensures: |ret| {
            ret == self
                .values
                .binary_search_by_key(&id, |&(held, _)| held)
                .ok()
                .and_then(|at| self.values.get(at))
                .map_or(Maybe::Absent(origin::Absent::Unrecorded), |&(_, origin)| {
                    Maybe::Present(origin)
                })
        },
    )]
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
    /// - ensures: exactly the origin stored under an equal id in this table's
    ///   computation family, without authenticating its minting arena.
    /// - provides: the computation half of the origin lookup.
    /// - fails: never; a key with no entry yields the unrecorded absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the shared search checks a linear lookup oracle; this
    ///   family's recorded entry is separated from the other families. The
    ///   predicate re-asks the logarithmic search over this family.
    /// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
    #[spec(
        ensures: |ret| {
            ret == self
                .computations
                .binary_search_by_key(&id, |&(held, _)| held)
                .ok()
                .and_then(|at| self.computations.get(at))
                .map_or(Maybe::Absent(origin::Absent::Unrecorded), |&(_, origin)| {
                    Maybe::Present(origin)
                })
        },
    )]
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
    /// - ensures: exactly the origin stored under an equal id in this table's
    ///   value-type family, without authenticating its minting arena.
    /// - provides: the value-type half of the origin lookup.
    /// - fails: never; a key with no entry yields the unrecorded absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the shared search checks a linear lookup oracle; this
    ///   family's recorded entry is separated from the other families. The
    ///   predicate re-asks the logarithmic search over this family.
    /// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
    #[spec(
        ensures: |ret| {
            ret == self
                .value_types
                .binary_search_by_key(&id, |&(held, _)| held)
                .ok()
                .and_then(|at| self.value_types.get(at))
                .map_or(Maybe::Absent(origin::Absent::Unrecorded), |&(_, origin)| {
                    Maybe::Present(origin)
                })
        },
    )]
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
    /// - ensures: exactly the origin stored under an equal id in this table's
    ///   computation-type family, without authenticating its minting arena.
    /// - provides: the computation-type half of the origin lookup.
    /// - fails: never; a key with no entry yields the unrecorded absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the shared search checks a linear lookup oracle; this
    ///   family's recorded entry is separated from the other families. The
    ///   predicate re-asks the logarithmic search over this family.
    /// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
    #[spec(
        ensures: |ret| {
            ret == self
                .comp_types
                .binary_search_by_key(&id, |&(held, _)| held)
                .ok()
                .and_then(|at| self.comp_types.get(at))
                .map_or(Maybe::Absent(origin::Absent::Unrecorded), |&(_, origin)| {
                    Maybe::Present(origin)
                })
        },
    )]
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
    /// - requires: nothing; every token is admissible as an index.
    /// - ensures: the origin at the token's index in this table, regardless of
    ///   which table minted the token or whether it was constructed directly.
    /// - provides: the resolution a driver performs in the table associated
    ///   with a checker's echoed token.
    /// - fails: never; an out-of-bounds index yields the unrecorded absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — checked indexing separates the last occupied index
    ///   from the first out-of-bounds index. Equal tokens from distinct tables
    ///   resolve in the queried table, separating indexing from ownership.
    /// - witness: `origin::tests::a_declaration_token_resolves_to_its_own_origin`
    /// - witness: `origin::tests::a_token_past_the_declaration_list_resolves_to_nothing`
    /// - witness: `origin::tests::keys_do_not_certify_their_minting_context`
    #[spec(
        ensures: |ret| {
            ret == self
                .declarations
                .get(token.0)
                .copied()
                .map_or(Maybe::Absent(origin::Absent::Unrecorded), Maybe::Present)
        },
    )]
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

    /// Record that the freshly minted variable `id` is bound at `binder`.
    ///
    /// # Specification
    /// - requires: `id` follows every variable already recorded.
    /// - ensures: the pair is appended, so the list stays ascending by id and
    ///   [`Self::binding`] finds it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a use under two binders of one name is recorded at
    ///   the inner one.
    /// - witness: `lower::tests::a_variable_keeps_its_binder`
    #[spec(
        requires: self.bindings.last().is_none_or(|&(held, _)| held < id),
        captures: before = self.bindings.len(),
        ensures: before.checked_add(1_usize) == Some(self.bindings.len())
            && self.bindings.last() == Some(&(id, binder)),
    )]
    #[inline]
    pub fn record_binding(
        &mut self,
        id: ValueId,
        binder: ByteSpan,
    )
    {
        self.bindings.push((id, binder));
    }

    /// The span of the binder the variable `id` was written against.
    ///
    /// # Specification
    /// - requires: nothing — an unrecorded id is admissible input.
    /// - ensures: the binder span recorded under an equal id, or the unrecorded
    ///   absence.
    /// - provides: the use-to-binder lookup.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recorded variable and a node the lowering did not
    ///   mint as a written variable answer their exact binders.
    /// - witness: `lower::tests::a_variable_keeps_its_binder`
    #[spec(ensures: |ret| ret == self.bindings.iter().find(|&&(held, _)| held == id)
        .map_or(Maybe::Absent(origin::Absent::Unrecorded), |&(_, binder)| Maybe::Present(binder)))]
    #[inline]
    pub fn binding(
        &self,
        id: ValueId,
    ) -> Maybe<ByteSpan, origin::Absent>
    {
        self.bindings
            .binary_search_by_key(&id, |&(held, _)| held)
            .ok()
            .and_then(|position| self.bindings.get(position))
            .map_or(Maybe::Absent(origin::Absent::Unrecorded), |&(_, binder)| {
                Maybe::Present(binder)
            })
    }

    /// Every variable written in the source, with its binder's span, in mint
    /// order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn bindings(&self) -> &[(ValueId, ByteSpan)]
    {
        &self.bindings
    }

    /// Every value type's origin, in mint order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value_types(&self) -> &[(ValueTypeId, Origin)]
    {
        &self.value_types
    }

    /// Every computation type's origin, in mint order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn comp_types(&self) -> &[(CompTypeId, Origin)]
    {
        &self.comp_types
    }

    /// How many core nodes this table recorded an origin for.
    ///
    /// # Specification
    /// - requires: the table's family-order invariant holds.
    /// - ensures: the saturating sum of the four family lengths, excluding
    ///   declaration origins; the stored family-order predicate still holds.
    /// - provides: a census of the recorded core nodes, not syntax
    ///   declarations.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the predicate checks the four-family sum and the
    ///   order at each family's tail, where every record appends under a
    ///   requirement that keeps the family ascending. Multi-family and
    ///   declaration-bearing tables separate omitted families and accidentally
    ///   counting a declaration as a core node; a two-entry family disordered
    ///   after recording is refused. Saturation is expressed, not allocated up
    ///   to in these fixtures.
    /// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
    /// - witness: `origin::tests::lookups_separate_gaps_from_declaration_origins`
    /// - witness: `origin::tests::census_rejects_a_disordered_family`
    #[spec(
        ensures: |ret| {
            ret.0
                == self
                    .values
                    .len()
                    .saturating_add(self.computations.len())
                    .saturating_add(self.value_types.len())
                    .saturating_add(self.comp_types.len())
                && self.values.last_chunk::<2>().is_none_or(|pair| pair.first().map(|entry| entry.0) < pair.last().map(|entry| entry.0))
                && self.computations.last_chunk::<2>().is_none_or(|pair| pair.first().map(|entry| entry.0) < pair.last().map(|entry| entry.0))
                && self.value_types.last_chunk::<2>().is_none_or(|pair| pair.first().map(|entry| entry.0) < pair.last().map(|entry| entry.0))
                && self.comp_types.last_chunk::<2>().is_none_or(|pair| pair.first().map(|entry| entry.0) < pair.last().map(|entry| entry.0))
        },
    )]
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

    /// Record the arms of the match whose lowered tree is rooted at `root`.
    ///
    /// # Specification
    /// - requires: `root` follows every match root already recorded.
    /// - ensures: the record is appended, so the match list stays ascending by
    ///   root and [`Self::case`] finds it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two matches of one module answer their own arms by
    ///   root, and a computation that is no match root answers nothing.
    /// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
    #[spec(
        requires: self.cases.last().is_none_or(|&(held, _)| held < root),
        captures: before = self.cases.len(),
        ensures: self.cases.len() == before.saturating_add(1)
            && self.cases.last().is_some_and(|&(held, _)| held == root),
    )]
    #[inline]
    pub fn record_case(
        &mut self,
        root: ComputationId,
        case: CaseOrigin,
    )
    {
        self.cases.push((root, case));
    }

    /// The arms of the match whose lowered tree is rooted at `root`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the record kept for `root`, or the unrecorded absence for a
    ///   computation no match lowered to.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::record_case`]. The predicate re-asks the
    ///   logarithmic search over the ascending match roots.
    /// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(_))
        == self.cases.binary_search_by_key(&root, |&(held, _)| held).is_ok())]
    #[inline]
    pub fn case(
        &self,
        root: ComputationId,
    ) -> Maybe<&CaseOrigin, origin::Absent>
    {
        self.cases
            .binary_search_by_key(&root, |&(held, _)| held)
            .ok()
            .and_then(|position| self.cases.get(position))
            .map_or(Maybe::Absent(origin::Absent::Unrecorded), |entry| {
                Maybe::Present(&entry.1)
            })
    }

    /// Every lowered match's root and arms, in mint order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cases(&self) -> impl ExactSizeIterator<Item = (ComputationId, &CaseOrigin)>
    {
        self.cases.iter().map(|&(root, ref case)| (root, case))
    }

    /// Record the name the lambda or bind `opener` binds, written at `name`.
    ///
    /// # Specification
    /// - requires: `opener` follows every opener already recorded.
    /// - ensures: the pair is appended, so the binder list stays ascending and
    ///   [`Self::binder`] finds it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function's parameter and a `run` statement's name
    ///   are answered by their own openers; a split statement records none.
    /// - witness: `lower::tests::each_named_binder_records_where_its_name_is_written`
    #[spec(
        requires: self.binders.last().is_none_or(|&(held, _)| held < opener),
        captures: before = self.binders.len(),
        ensures: self.binders.len() == before.saturating_add(1)
            && self.binders.last() == Some(&(opener, name)),
    )]
    #[inline]
    pub fn record_binder(
        &mut self,
        opener: ComputationId,
        name: Origin,
    )
    {
        record(&mut self.binders, opener, name);
    }

    /// Where the name the lambda or bind `opener` binds is written.
    ///
    /// # Specification
    /// - requires: nothing — an unrecorded id is admissible input.
    /// - ensures: the origin recorded for `opener`'s binder, or the unrecorded
    ///   absence for a computation that opens no named binder: a split, an
    ///   inserted lambda, or a node that is no binder at all.
    /// - provides: the binder's name, which a diagnostic writes beside the type
    ///   the checker held for it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::record_binder`].
    /// - witness: `lower::tests::each_named_binder_records_where_its_name_is_written`
    #[spec(ensures: |ret| ret == find(&self.binders, opener))]
    #[inline]
    pub fn binder(
        &self,
        opener: ComputationId,
    ) -> Maybe<Origin, origin::Absent>
    {
        find(&self.binders, opener)
    }
}

/// One alternative of one arm of a lowered match.
///
/// # Specification
/// - requires: nothing; the fields are admitted as supplied metadata.
/// - ensures: the pattern names its match's table; an or-pattern's alternatives
///   are one record each, sharing their arm and body.
/// - executable: none — the record holds no table to resolve its pattern in.
///
/// # Adequacy
/// - hypothesis: L3 — a match with an or-pattern keeps one record per
///   alternative, in source order.
/// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArmOrigin
{
    /// The arm's position among the match's arms.
    pub arm: usize,
    /// The alternative's pattern, in the match's table.
    pub pattern: PatternId,
    /// The alternative's syntax node.
    pub written: NodeIndex,
    /// The arm body's syntax node.
    pub body: NodeIndex,
}

/// What a lowered match keeps of its arms.
///
/// # Specification
/// - requires: nothing; the fields are admitted as supplied metadata.
/// - ensures: the arms keep source order and name patterns of `patterns`; a
///   pattern hole's identity is its syntax node's position, the identity the
///   tree's stuck leaves and the term holes carry.
/// - executable: none — the record holds no tree to check its nodes against.
///
/// # Adequacy
/// - hypothesis: L3 — a match over nested constructors, a binder and a hole
///   keeps each pattern's shape and arm.
/// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CaseOrigin
{
    /// The match's syntax node.
    pub written: NodeIndex,
    /// The scrutinee's syntax node.
    pub scrutinee: NodeIndex,
    /// The patterns the arms are written in.
    pub patterns: Patterns,
    /// The arm alternatives, in source order.
    pub arms: Vec<ArmOrigin>,
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

    #[test]
    fn lookups_separate_gaps_from_declaration_origins()
    {
        let mut arena = CoreArena::new();
        let before = arena.value_unit();
        let first = arena.value_unit();
        let gap = arena.value_unit();
        let last = arena.value_unit();
        let after = arena.value_unit();
        let inserted = at(NodeIndex::from(1_usize)).inserted(super::Insertion::Force);
        let written = at(NodeIndex::from(4_usize));
        let mut table = OriginTable::new();
        table.record_value(first, inserted);
        table.record_value(last, written);
        let declaration = table.record_declaration(at(NodeIndex::from(9_usize)));

        assert_eq!(table.value(first), Maybe::Present(inserted));
        assert_eq!(table.value(last), Maybe::Present(written));
        for missing in [before, gap, after] {
            assert_eq!(
                table.value(missing),
                Maybe::Absent(origin::Absent::Unrecorded)
            );
        }
        assert_eq!(
            table.declaration(declaration),
            Maybe::Present(at(NodeIndex::from(9_usize)))
        );
        assert_eq!(table.recorded_count(), OriginCount::from(2_usize));
        assert_eq!(table.declaration_count(), OriginCount::from(1_usize));
    }

    #[test]
    fn keys_do_not_certify_their_minting_context()
    {
        let mut arena = CoreArena::new();
        let mut foreign_arena = CoreArena::new();
        let recorded = arena.value_unit();
        let foreign = foreign_arena.value_unit();
        assert_eq!(recorded, foreign);

        let first_origin = at(NodeIndex::from(1_usize));
        let second_origin = at(NodeIndex::from(8_usize));
        let mut first_table = OriginTable::new();
        first_table.record_value(recorded, first_origin);
        assert_eq!(first_table.value(foreign), Maybe::Present(first_origin));

        let first_token = first_table.record_declaration(first_origin);
        let mut second_table = OriginTable::new();
        let second_token = second_table.record_declaration(second_origin);
        assert_eq!(first_token, second_token);
        assert_eq!(
            first_table.declaration(second_token),
            Maybe::Present(first_origin)
        );
        assert_eq!(
            second_table.declaration(first_token),
            Maybe::Present(second_origin)
        );
    }

    #[cfg(anodized_panic)]
    #[test]
    #[should_panic(expected = "postcondition failed")]
    fn census_rejects_a_disordered_family()
    {
        let mut arena = CoreArena::new();
        let first = arena.value_unit();
        let second = arena.value_unit();
        let mut table = OriginTable::new();
        table.record_value(first, at(NodeIndex::from(1_usize)));
        table.record_value(second, at(NodeIndex::from(2_usize)));
        assert_eq!(table.recorded_count(), OriginCount::from(2_usize));
        table.values.swap(0_usize, 1_usize);
        let _count = table.recorded_count();
    }
}
