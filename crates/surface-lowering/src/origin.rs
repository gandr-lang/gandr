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
//! the position, and more: the `return` an exit inferred at a tail over a
//! value, the nominal type of a constructor written without an annotation,
//! and the eliminations a match compiles to. Each carries the origin of the
//! syntax node whose position demanded it, marked [`Provenance::Inserted`]
//! with the [`Insertion`] it is, so a printer or a diagnostic can show the
//! cast a reader did not write, and every node the source did write is
//! [`Provenance::Written`].
//!
//! # A match keeps its arms
//!
//! A match lowers to a decision tree of native eliminations, so its patterns
//! do not survive into the core term. The table keeps them beside it: per
//! lowered match, a [`CaseOrigin`] holding the pattern table its arms are
//! written in, one [`ArmOrigin`] per arm alternative, the syntax nodes of the
//! scrutinee and every pattern and body, the scrutinee's core value, and the
//! span every pattern and constructor name was written at ([`PatternSpan`]).
//! A live match and a coverage report read the arms from here and the tree
//! from the arena; a hover reads each pattern's span and types it from the
//! scrutinee's.
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
//!
//! # A rewritten node answers where its source is written
//!
//! A node a rewrite of the lowered terms mints after the lowering — the
//! checker's elaboration of a computation written where a value is read
//! among them — has no syntax of its own. [`OriginTable::carry`] records for
//! each the origin of the node it stands for, as the rewrite reports it: a
//! rebuilt node its source's, with the source's binder name and a variable's
//! binder, and a bind minted for a run the run's. A refusal over the rewritten
//! terms is then published at the written node that elaborated.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Carried;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::FieldLabel;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::identity::Relation;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;
use gandr_kernel_term::ConstantIndex;
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

quenchant_shape::reason_enum! {
    /// Why a match's record names no scrutinee value.
    pub mod scrutinised {
        /// The match's record holds no core value for its scrutinee.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The record was read before its match was minted: the table
            /// records a match only once its tree is minted, with the value.
            Unminted,
        }
    }
}

/// One of the insertions the lowering writes at a checked site.
///
/// The five bridges, the `return` of an inferred exit, the classifier of a
/// constructor written without one, the eliminations a match compiles to, a
/// recursive function's fixpoint, a compound endpoint, the transport a
/// derived identity operation unfolds to, a computation carried where a value
/// is read for the checker to run or suspend, and the type a model's member
/// derives from its signature.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the tag distinguishes force, thunk, returner, quote, decode,
///   return, classifier, match, fixpoint, endpoint, identity, nested, unwind,
///   model and relation.
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
    /// The `return` an exit inferred where a path through a body ends in a
    /// value: the returner over the value the source wrote there.
    Return,
    /// The nominal type of a constructor of a family without parameters,
    /// which the source wrote no annotation for.
    Classifier,
    /// A node of the decision tree a match compiles to: a scrutinee bind, a
    /// native or sum case, a field lambda, a literal test, or a binding an arm
    /// body is read under.
    Match,
    /// The fixpoint a recursive function closes over its staged parameter's
    /// lambda, binding the function's own name; and the joint fixpoint a
    /// mutual block's recursive functions share, with its sum case, its
    /// ascription and the injection each member and each call through a
    /// sibling passes.
    Fixpoint,
    /// A node a loop writes that the source does not: a `while`'s case on its
    /// condition with the unit its false branch leaves with, and the re-entry
    /// where a path through a loop's body ends without leaving it — the
    /// result discarded and the loop's fixpoint forced again.
    Loop,
    /// A node a block ending in a statement writes that the source does not:
    /// the statement's result discarded and the unit the block returns.
    Statement,
    /// The value a computation returns, standing where a path type's endpoint
    /// or reflexivity's point is read: a compound endpoint.
    Endpoint,
    /// The motive, the base and the shifted endpoints of the transport `back`,
    /// `then` or `cong` unfolds to.
    Identity,
    /// A computation standing where a value is read, carried to the checker,
    /// which runs it before the computation around it or suspends it as the
    /// type read there decides.
    Nested,
    /// The delimiter around a body a `return` in a handled subject leaves,
    /// and the capture that `return` is: the capture discards every handler
    /// frame up to the delimiter, which returns the value.
    Unwind,
    /// The type a model's member derives from the signature its module's
    /// header names, `S` in `Model(S)`, every node of it located at that
    /// name: the source writes the name, never the type or the binders the
    /// type opens.
    Model,
    /// A node of the record or the flow a relation between types abbreviates,
    /// below the type itself, every one located at the relation: the source
    /// writes `A ≃ B`, never the record's fields, the terms its round trips
    /// read or the binders it opens.
    Relation,
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

/// One component of a split, counted from the outermost: the place a
/// pattern's part binds among the binders the split opens.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SplitComponent(usize);

impl From<usize> for SplitComponent
{
    /// The component `component` places from the outermost.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(component: usize) -> Self
    {
        Self(component)
    }
}

impl From<SplitComponent> for usize
{
    /// How many places from the outermost `component` stands.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(component: SplitComponent) -> Self
    {
        component.0
    }
}

/// The name a split component binds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ComponentName
{
    /// The pattern variable written for the component, at its origin.
    Written(Origin),
    /// The label of the field a labelled pattern leaves unwritten: the one
    /// name the record declares for it.
    Labelled(FieldLabel),
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
    /// The data declaration each data case of a match's tree eliminates, by
    /// the case. The core matches by tag alone, so a printer naming a case's
    /// branches by their constructors reads the family here.
    eliminations: BTreeMap<ComputationId, ConstantIndex>,
    /// The name each lambda or bind binds, by the computation that opens the
    /// binder, ascending by id: the syntax the binder's name was written at.
    binders: Vec<(ComputationId, Origin)>,
    /// The name each component of a split binds, by the split and the
    /// component, ascending: the pattern variable written for it, or the
    /// label of the field a labelled pattern leaves unwritten. A split opens
    /// several binders, so the opener alone does not name one.
    components: Vec<((ComputationId, SplitComponent), ComponentName)>,
    /// The name each dependent arrow binds, by the arrow, ascending by id:
    /// the syntax its binder's name was written at, a parameter's or a
    /// telescope entry's. The core carries no name; the printer reads it
    /// here.
    arrows: Vec<(CompTypeId, Origin)>,
    /// The name each dependent pair a dependent record's field opens binds,
    /// by the pair, ascending by id: where the field's label is written. A
    /// later field reads the earlier one through that binder, and the
    /// context it is spelled in names it here (#728).
    pairs: Vec<(ValueTypeId, Origin)>,
    /// Each variable written in the source, with its binder's span, ascending
    /// by id.
    bindings: Vec<(ValueId, ByteSpan)>,
    /// Each `ua` statement with where it names its two descriptions, in the
    /// order lowered; the arena shares a statement written twice alike.
    sides: Vec<(ValueId, [Origin; 2])>,
    /// Each element transport with where its motive is written, in the order
    /// lowered; the arena shares a transport written twice alike.
    motives: Vec<(ComputationId, Origin)>,
    /// Each label written against an entry, with what it labels, in the
    /// order lowered.
    labels: Vec<Label>,
    /// Each index a data constructor's result states, by its bytes, with the
    /// names of the binders it is read under, outermost first, in the order
    /// lowered: a data declaration has no term whose binders name them.
    framed: Vec<(ByteSpan, Vec<String>)>,
    /// Each written type head standing for a type minted elsewhere, which it
    /// adopts, with the head's origin, in the order lowered.
    stand_ins: Vec<(ValueTypeId, Origin)>,
    /// Each relation written between two types, with the type it lowers to,
    /// in the order lowered.
    relations: Vec<(ValueTypeId, Relation)>,
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
/// - hypothesis: L3 — on the stated sorted domain the entry at `id`'s lower
///   bound is the only one that can hold `id`, so it decides a hit and a miss
///   alike at the lookup's own cost. Fixtures cover hits, empty input and
///   missing ids before, within and after a nonempty family.
/// - witness: `origin::tests::each_family_answers_its_own_recorded_origins`
/// - witness: `origin::tests::an_unrecorded_id_has_no_origin`
/// - witness: `origin::tests::lookups_separate_gaps_from_declaration_origins`
/// - witness: `origin::tests::keys_do_not_certify_their_minting_context`
#[spec(
    ensures: |ret| {
        let bound = entries.get(entries.partition_point(|&(held, _)| held < id));
        match ret {
            Maybe::Present(origin) => bound.is_some_and(|&(held, found)| held == id && found == origin),
            Maybe::Absent(_) => bound.is_none_or(|&(held, _)| held != id),
        }
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

/// What a computation a rewrite minted stands for.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Source
{
    /// A bind minted for the run it binds, which it answers at.
    Run(ValueId),
    /// A node rebuilt from the computation it stands in place of.
    Rebuilt(ComputationId),
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

    /// Record where the name a freshly minted dependent arrow binds is
    /// written.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn record_arrow(
        &mut self,
        id: CompTypeId,
        binder: Origin,
    )
    {
        record(&mut self.arrows, id, binder);
    }

    /// Record where the label a freshly minted dependent pair binds is
    /// written.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn record_pair(
        &mut self,
        id: ValueTypeId,
        label: Origin,
    )
    {
        record(&mut self.pairs, id, label);
    }

    /// Record that the data case `case` eliminates a value of the data
    /// declaration `family`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Self::elimination`] answers `family` for `case`, the first
    ///   record winning.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match over a unary family names each branch of its
    ///   case by the constructor it binds.
    /// - witness: `lower::native::tests::a_data_case_names_the_family_it_eliminates_809`
    #[spec(ensures: self.eliminations.contains_key(&case))]
    #[inline]
    pub fn record_elimination(
        &mut self,
        case: ComputationId,
        family: ConstantIndex,
    )
    {
        let _first = self.eliminations.entry(case).or_insert(family);
    }

    /// Record, for each node a rewrite of the lowered terms minted, the origin
    /// of the node it stands for: a rebuilt node takes the origin of the node
    /// it was rebuilt from, with that node's binder name and a variable's
    /// binder, and a bind minted for a run takes the run's origin and names no
    /// binder.
    ///
    /// # Specification
    /// - requires: every node `carried` and `binds` name as minted follows
    ///   every node this table records in its family, and every rebuilt node
    ///   follows the node it was rebuilt from, as a rewrite mints them.
    /// - ensures: each minted node whose source answers an origin records it,
    ///   the source being the node `carried` pairs it with, or for a bind the
    ///   run `binds` pairs it with, the run first and the first pair after it;
    ///   a rebuilt opener records its source's binder, a rebuilt data case the
    ///   family its source eliminates, a rebuilt dependent arrow the name its
    ///   source binds, and a rebuilt variable its source's binder span; a
    ///   minted bind records no binder; nothing recorded before changes, and
    ///   every family stays ascending.
    /// - provides: the nodes of a body the checker elaborated, located as the
    ///   written nodes they elaborate, so a refusal of the second run is
    ///   published where the first run's is.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a rebuilt case, lambda and variable, a node rebuilt
    ///   from a rebuilt node, and a bind reported both beside its run and as a
    ///   rebuilt region separate the source each answers at, the binder it
    ///   names and the run's precedence; a source with no origin leaves its
    ///   copy unrecorded.
    /// - witness: `origin::tests::an_elaborated_node_answers_where_its_source_is_written`
    #[spec(
        captures: before = (self.values.len(), self.computations.len(), self.declarations.len()),
        ensures: self.values.len() >= before.0
            && self.computations.len() >= before.1
            && self.declarations.len() == before.2,
    )]
    #[inline]
    pub fn carry(
        &mut self,
        carried: &[Carried],
        binds: &[(ValueId, ComputationId)],
    )
    {
        let mut values = BTreeMap::new();
        let mut computations = BTreeMap::new();
        let mut value_types = BTreeMap::new();
        let mut comp_types = BTreeMap::new();
        for &(run, bind) in binds {
            let _first = computations.entry(bind).or_insert(Source::Run(run));
        }
        for pair in carried {
            match *pair {
                Carried::Value(held, written) => {
                    let _first = values.entry(written).or_insert(held);
                },
                Carried::Computation(held, written) => {
                    let _first = computations.entry(written).or_insert(Source::Rebuilt(held));
                },
                Carried::ValueType(held, written) => {
                    let _first = value_types.entry(written).or_insert(held);
                },
                Carried::CompType(held, written) => {
                    let _first = comp_types.entry(written).or_insert(held);
                },
            }
        }
        for (written, held) in values {
            if let Maybe::Present(origin) = self.value(held) {
                self.record_value(written, origin);
            }
            if let Maybe::Present(binder) = self.binding(held) {
                self.record_binding(written, binder);
            }
        }
        for (written, source) in computations {
            let origin = match source {
                Source::Run(run) => self.value(run),
                Source::Rebuilt(held) => {
                    if let Maybe::Present(name) = self.binder(held) {
                        self.record_binder(written, name);
                    }
                    if let Some(&family) = self.eliminations.get(&held) {
                        self.record_elimination(written, family);
                    }
                    self.computation(held)
                },
            };
            if let Maybe::Present(origin) = origin {
                self.record_computation(written, origin);
            }
        }
        for (written, held) in value_types {
            if let Maybe::Present(origin) = self.value_type(held) {
                self.record_value_type(written, origin);
            }
            if let Maybe::Present(label) = find(&self.pairs, held) {
                self.record_pair(written, label);
            }
        }
        for (written, held) in comp_types {
            if let Maybe::Present(origin) = self.comp_type(held) {
                self.record_comp_type(written, origin);
            }
            if let Maybe::Present(binder) = find(&self.arrows, held) {
                self.record_arrow(written, binder);
            }
        }
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
    ///   absence; the check finds the id's place among the ascending ids
    ///   [`Self::record_binding`] keeps by one lower-bound search.
    /// - provides: the use-to-binder lookup.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recorded variable and a node the lowering did not
    ///   mint as a written variable answer their exact binders.
    /// - witness: `lower::tests::a_variable_keeps_its_binder`
    #[spec(ensures: |ret| ret == self.bindings.get(self.bindings.partition_point(|&(held, _)| held < id))
        .filter(|&&(held, _)| held == id)
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

    /// Every lambda and bind with the origin of the binder it opens, in mint
    /// order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn binders(&self) -> &[(ComputationId, Origin)]
    {
        &self.binders
    }

    /// Every split component with the name it binds, ascending by split and
    /// component.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn components(&self) -> &[((ComputationId, SplitComponent), ComponentName)]
    {
        &self.components
    }

    /// Every value's origin, in mint order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn values(&self) -> &[(ValueId, Origin)]
    {
        &self.values
    }

    /// Every computation's origin, ascending by id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn computations(&self) -> &[(ComputationId, Origin)]
    {
        &self.computations
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

    /// Each dependent arrow with where the name it binds is written,
    /// ascending by id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arrows(&self) -> &[(CompTypeId, Origin)]
    {
        &self.arrows
    }

    /// Each dependent pair a dependent record's field opens with where the
    /// field's label is written, ascending by id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pairs(&self) -> &[(ValueTypeId, Origin)]
    {
        &self.pairs
    }

    /// Each data case a match's tree holds, with the data declaration it
    /// eliminates, ascending by case.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn eliminations(&self) -> impl ExactSizeIterator<Item = (ComputationId, ConstantIndex)>
    {
        self.eliminations
            .iter()
            .map(|(&case, &family)| (case, family))
    }

    /// The data declaration the data case `case` eliminates.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn elimination(
        &self,
        case: ComputationId,
    ) -> Maybe<ConstantIndex, origin::Absent>
    {
        self.eliminations
            .get(&case)
            .copied()
            .map_or(Maybe::Absent(origin::Absent::Unrecorded), Maybe::Present)
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

    /// Record the name a field lambda `opener` binds, written at `name` as a
    /// pattern variable, where it falls among the openers already recorded.
    ///
    /// A switch's field lambdas are named after the whole match is minted:
    /// a branch's outermost field lambda is minted last, and an arm body's
    /// binders before the lambdas around it, so the openers arrive out of
    /// mint order and are placed rather than appended.
    ///
    /// # Specification
    /// - requires: nothing — an opener already recorded keeps its name.
    /// - ensures: the list holds `opener`, at `name` unless it held it before.
    /// - intension: the pair is inserted where the binary search over the
    ///   ascending list places it, so the list stays strictly ascending.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a record of three fields names its innermost lambda
    ///   after its outermost, below an arm body's binder recorded first.
    /// - witness: `lower::native::tests::a_record_names_every_field_binder_in_order`
    #[spec(
        captures: [before = find(&self.binders, opener)],
        ensures: find(&self.binders, opener) == match before {
                Maybe::Present(held) => Maybe::Present(held),
                Maybe::Absent(_) => Maybe::Present(name),
            },
    )]
    #[inline]
    pub fn place_binder(
        &mut self,
        opener: ComputationId,
        name: Origin,
    )
    {
        if let Err(at) = self
            .binders
            .binary_search_by_key(&opener, |&(held, _)| held)
        {
            self.binders.insert(at, (opener, name));
        }
    }

    /// Record the name component `component` of the split `split` binds,
    /// where it falls among the components already recorded: the pattern
    /// variable written for it, or the label of a field a labelled pattern
    /// leaves unwritten.
    ///
    /// A match's splits are named after the whole match is minted, as its
    /// field lambdas are, so they arrive out of mint order and are placed.
    ///
    /// # Specification
    /// - requires: nothing — a component already recorded keeps its name.
    /// - ensures: the list holds the component, at `name` unless it held it
    ///   before.
    /// - intension: the pair is inserted where the binary search over the
    ///   ascending list places it, so the list stays strictly ascending.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a relation's record split in one arm names each
    ///   component it writes a variable for, used or not, and each field a
    ///   label pattern leaves unwritten by its label.
    /// - witness: `lower::identity::tests::a_relation_split_names_each_written_component_665`
    /// - witness: `lower::identity::tests::an_unwritten_field_is_named_by_its_label_670`
    #[spec(
        captures: [
            before = self
                .components
                .binary_search_by_key(&(split, component), |&(held, _)| held)
                .ok()
                .and_then(|at| self.components.get(at))
                .map(|&(_, ref held)| held.clone()),
            named = name.clone(),
        ],
        ensures: self
            .components
            .binary_search_by_key(&(split, component), |&(held, _)| held)
            .ok()
            .and_then(|at| self.components.get(at))
            .map(|&(_, ref held)| held)
            == Some(before.as_ref().unwrap_or(&named)),
    )]
    #[inline]
    pub fn place_component(
        &mut self,
        split: ComputationId,
        component: SplitComponent,
        name: ComponentName,
    )
    {
        let key = (split, component);
        if let Err(at) = self
            .components
            .binary_search_by_key(&key, |&(held, _)| held)
        {
            self.components.insert(at, (key, name));
        }
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

    /// Record where the `ua` statement `statement` names its two
    /// descriptions, the source's first: a description is no core node, so a
    /// face answers it through the statement.
    ///
    /// # Specification
    /// - requires: nothing; a statement the arena shares with an earlier one is
    ///   recorded again, at its own names.
    /// - ensures: the pair is appended, so [`Self::sides`] holds it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a statement between two magmas records both names
    ///   where they are written.
    /// - witness: `lower::ua::tests::a_statement_lowers_to_univalence_at_its_stratum`
    #[spec(
        captures: before = self.sides.len(),
        ensures: self.sides.len() == before.saturating_add(1)
            && self.sides.last() == Some(&(statement, named)),
    )]
    #[inline]
    pub fn record_sides(
        &mut self,
        statement: ValueId,
        named: [Origin; 2],
    )
    {
        self.sides.push((statement, named));
    }

    /// Each `ua` statement with where it names its two descriptions, the
    /// source's first, in the order lowered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sides(&self) -> &[(ValueId, [Origin; 2])]
    {
        &self.sides
    }

    /// Record where the element transport or ride `transport` writes its
    /// motive: the family the motive denotes is shared by every motive that
    /// denotes it, so a face answers each written motive through its own
    /// transport.
    ///
    /// # Specification
    /// - requires: nothing; a transport the arena shares with an earlier one is
    ///   recorded again, at its own motive.
    /// - ensures: the pair is appended, so [`Self::motives`] holds it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list moved along a universe path records its motive
    ///   where it is written.
    /// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
    #[spec(
        captures: before = self.motives.len(),
        ensures: self.motives.len() == before.saturating_add(1)
            && self.motives.last() == Some(&(transport, motive)),
    )]
    #[inline]
    pub fn record_motive(
        &mut self,
        transport: ComputationId,
        motive: Origin,
    )
    {
        self.motives.push((transport, motive));
    }

    /// Each element transport and ride with where its motive is written, in
    /// the order lowered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn motives(&self) -> &[(ComputationId, Origin)]
    {
        &self.motives
    }

    /// Record that the label written at `label.span` names an entry.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the label is appended, so [`Self::labels`] holds it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a record type's, a record's and a dependent arrow's
    ///   labels are each recorded with what they label.
    /// - witness: `lower::arity::tests::each_label_names_what_it_labels`
    #[spec(
        captures: before = self.labels.len(),
        ensures: self.labels.len() == before.saturating_add(1),
    )]
    #[inline]
    pub fn record_label(
        &mut self,
        label: Label,
    )
    {
        self.labels.push(label);
    }

    /// Carry every label naming `from` over to `to`, which a rewrite put in
    /// its place.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no label names `from` unless `from == to`; every label that
    ///   named it names `to`; the count is unchanged.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a use instantiated at a binder a later instantiation
    ///   replaces answers at the value that replaced both; an endpoint written
    ///   in an offer the lowering rebuilds answers at the rebuilt offer.
    /// - witness: `lower::exits::tests::a_use_a_local_end_replaces_keeps_its_bytes`
    /// - witness: `lower::session::tests::each_endpoint_answers_at_its_action`
    #[spec(
        captures: before = self.labels.len(),
        ensures: self.labels.len() == before,
    )]
    pub(crate) fn relabel(
        &mut self,
        from: &Labelled,
        to: &Labelled,
    )
    {
        for label in &mut self.labels {
            if label.labelled == *from {
                label.labelled = to.clone();
            }
        }
    }

    /// Carry every label naming the session action `from` — its endpoint's
    /// and its offer arms' — over to `to`, which a rewrite put in its place.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no endpoint or branch label names `from` unless `from == to`;
    ///   every one that did names `to`, with its arm's label kept; the count is
    ///   unchanged.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an endpoint and an arm's label written in an offer
    ///   the lowering rebuilds answer at the rebuilt offer.
    /// - witness: `lower::session::tests::each_endpoint_answers_at_its_action`
    #[spec(
        captures: before = self.labels.len(),
        ensures: self.labels.len() == before,
    )]
    pub(crate) fn relabel_action(
        &mut self,
        from: ComputationId,
        to: ComputationId,
    )
    {
        for label in &mut self.labels {
            match label.labelled {
                Labelled::Endpoint(ref mut action) | Labelled::Branch { ref mut action, .. }
                    if *action == from =>
                {
                    *action = to;
                },
                Labelled::ValueType { .. }
                | Labelled::CompType { .. }
                | Labelled::Value(_)
                | Labelled::Endpoint(_)
                | Labelled::Bound(_)
                | Labelled::Branch { .. } => {},
            }
        }
    }

    /// Each label written against an entry, in the order lowered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn labels(&self) -> &[Label]
    {
        &self.labels
    }

    /// Record that the index written at `span` is read under binders named
    /// `names`, outermost first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the pair is appended, so [`Self::framed`] holds it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Cons`'s `S(n)` is framed under the family's
    ///   parameter and the constructor's fields.
    /// - witness: `lower::native::tests::each_stated_index_is_framed_under_its_family_s_telescope_931`
    #[spec(
        captures: before = self.framed.len(),
        ensures: self.framed.len() == before.saturating_add(1),
    )]
    #[inline]
    pub fn record_framed(
        &mut self,
        span: ByteSpan,
        names: Vec<String>,
    )
    {
        self.framed.push((span, names));
    }

    /// Each index a data constructor's result states, by its bytes, with the
    /// names of the binders it is read under, outermost first, in the order
    /// lowered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn framed(&self) -> &[(ByteSpan, Vec<String>)]
    {
        &self.framed
    }

    /// Record that the type head at `origin` stands for `ty`, a type minted
    /// elsewhere that the head adopts.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the pair is appended, so [`Self::stand_ins`] holds it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a manifest component named in a later component and
    ///   an instance's type named past its module each answer at their head.
    /// - witness: `lower::tests::a_type_head_answers_at_what_it_stands_for`
    #[spec(
        captures: before = self.stand_ins.len(),
        ensures: self.stand_ins.len() == before.saturating_add(1),
    )]
    #[inline]
    pub fn record_stand_in(
        &mut self,
        ty: ValueTypeId,
        origin: Origin,
    )
    {
        self.stand_ins.push((ty, origin));
    }

    /// Each written type head standing for a type minted elsewhere, with the
    /// head's origin, in the order lowered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn stand_ins(&self) -> &[(ValueTypeId, Origin)]
    {
        &self.stand_ins
    }

    /// Record that `ty` is the type the relation `relation` was written as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the pair is appended, so [`Self::relations`] holds it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each of the three relations, written infix and as
    ///   `Iso(A, B)`, answers at the type it lowers to.
    /// - witness: `lower::identity::tests::a_relation_lowers_to_the_type_it_abbreviates`
    #[spec(
        captures: before = self.relations.len(),
        ensures: self.relations.len() == before.saturating_add(1),
    )]
    #[inline]
    pub fn record_relation(
        &mut self,
        ty: ValueTypeId,
        relation: Relation,
    )
    {
        self.relations.push((ty, relation));
    }

    /// Each relation written between two types, with the type it lowers to,
    /// in the order lowered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn relations(&self) -> &[(ValueTypeId, Relation)]
    {
        &self.relations
    }
}

/// A label the source writes against an entry: a field of a record or sum
/// type, an observation of a lazy record, a binder of a telescope or of a
/// dependent arrow, a field of a record.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Label
{
    /// The label's bytes.
    pub span: ByteSpan,
    /// What the label names.
    pub labelled: Labelled,
}

/// What a label names: the type of its entry, or the term its entry holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Labelled
{
    /// A field's or a binder's value type, read in `context`: the names of
    /// the binders it stands under, outermost first.
    ValueType
    {
        /// The type.
        ty: ValueTypeId,
        /// The binders' names, outermost first.
        context: Vec<String>,
    },
    /// An observation's computation type, read in `context`.
    CompType
    {
        /// The type.
        ty: CompTypeId,
        /// The binders' names, outermost first.
        context: Vec<String>,
    },
    /// A record field's value, whose type the typed run judges.
    Value(ValueId),
    /// The endpoint a session action names, at the session type the typed
    /// run found it standing at there.
    Endpoint(ComputationId),
    /// A `run` binder, at the value type the computation written at the
    /// node returns, where the typed run judged that computation: the binder
    /// answers even where the block's rewrite leaves no bind or use naming
    /// it (#298).
    Bound(NodeIndex),
    /// An offer arm's label, at the session its endpoint continues as in that
    /// arm: the branch `label` names of the session type the typed run found
    /// the endpoint standing at the offer `action`.
    Branch
    {
        /// The offer.
        action: ComputationId,
        /// The arm's label.
        label: FieldLabel,
    },
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

/// What a span of a written pattern answers at.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PatternReading
{
    /// The pattern itself, at the type it matches: the pattern's own span, a
    /// word pattern's letter, which is a word of one letter, the key of a sum
    /// pattern, at the payload it names, or an or-pattern at its first
    /// alternative.
    Matched,
    /// The constructor a constructor pattern names, at the constructor's type:
    /// the name `S` of `S(x)`.
    Constructor,
}

/// One span a match's patterns were written at, with the pattern it belongs
/// to and what it answers at.
///
/// # Specification
/// - requires: nothing; the fields are admitted as supplied metadata.
/// - ensures: the pattern names its match's table.
/// - executable: none — the record holds no table to resolve its pattern in.
///
/// # Adequacy
/// - hypothesis: L3 — a match over a constructor pattern, a word pattern and a
///   binder keeps one span per written pattern and one per constructor name and
///   letter.
/// - witness: `lower::native::tests::a_match_keeps_its_patterns_beside_its_tree`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PatternSpan
{
    /// The pattern, in the match's table.
    pub pattern: PatternId,
    /// The bytes written.
    pub span: ByteSpan,
    /// What the bytes answer at.
    pub reading: PatternReading,
}

/// What a lowered match keeps of its arms.
///
/// # Specification
/// - requires: nothing; the fields are admitted as supplied metadata.
/// - ensures: the arms keep source order and name patterns of `patterns`; a
///   pattern hole's identity is its syntax node's position, the identity the
///   tree's stuck leaves and the term holes carry; every written pattern has a
///   span in `spans`, so a face answers a pattern as the node it is rather than
///   as the match around it.
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
    /// The scrutinee's core value, the one the tree eliminates, under the
    /// match's binders; every record the table holds names it.
    pub scrutinised: Maybe<ValueId, scrutinised::Absent>,
    /// The patterns the arms are written in.
    pub patterns: Patterns,
    /// The arm alternatives, in source order.
    pub arms: Vec<ArmOrigin>,
    /// Where each pattern, each constructor name and each letter was written,
    /// in the order the patterns were read.
    pub spans: Vec<PatternSpan>,
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::CoreArena;
    use gandr_surface_syntax::NodeIndex;
    use quenchant_shape::shape::Maybe;

    use super::Carried;
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
    fn an_elaborated_node_answers_where_its_source_is_written()
    {
        let mut arena = CoreArena::new();
        let mut table = OriginTable::new();
        let [variable, run, bare] = [(); 3].map(|()| arena.value_unit());
        let [lambda, region] = [(); 2].map(|()| arena.computation_return(variable));
        table.record_value(variable, at(NodeIndex::from(1_usize)));
        table.record_value(run, at(NodeIndex::from(2_usize)));
        table.record_computation(lambda, at(NodeIndex::from(3_usize)));
        table.record_computation(region, at(NodeIndex::from(4_usize)));
        table.record_binding(variable, at(NodeIndex::from(5_usize)).span());
        table.record_binder(lambda, at(NodeIndex::from(6_usize)));
        let [shifted, copied] = [(); 2].map(|()| arena.value_unit());
        let [rebuilt, closed, spliced, bind] = [(); 4].map(|()| arena.computation_return(variable));
        // A rewrite reports in memo order, not mint order; the region is
        // reported both as its closed body and as the bind wrapping it.
        table.carry(
            &[
                Carried::Computation(closed, spliced),
                Carried::Computation(region, bind),
                Carried::Value(bare, copied),
                Carried::Computation(region, closed),
                Carried::Value(variable, shifted),
                Carried::Computation(lambda, rebuilt),
            ],
            &[(run, bind)],
        );
        assert_eq!(
            (table.value(shifted), table.binding(shifted)),
            (
                Maybe::Present(at(NodeIndex::from(1_usize))),
                Maybe::Present(at(NodeIndex::from(5_usize)).span())
            ),
            "a rebuilt variable answers at its source and keeps its binder"
        );
        assert_eq!(
            (table.computation(rebuilt), table.binder(rebuilt)),
            (
                Maybe::Present(at(NodeIndex::from(3_usize))),
                Maybe::Present(at(NodeIndex::from(6_usize)))
            ),
            "a rebuilt opener answers at its source and names its binder"
        );
        assert_eq!(
            table.computation(spliced),
            Maybe::Present(at(NodeIndex::from(4_usize))),
            "a node rebuilt from a rebuilt node answers at the written one"
        );
        assert_eq!(
            (table.computation(bind), table.binder(bind)),
            (
                Maybe::Present(at(NodeIndex::from(2_usize))),
                Maybe::Absent(origin::Absent::Unrecorded)
            ),
            "a bind answers at the run it binds, before the region it wraps, and names no binder"
        );
        assert_eq!(
            table.value(copied),
            Maybe::Absent(origin::Absent::Unrecorded),
            "a copy of a node with no origin gains none"
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
