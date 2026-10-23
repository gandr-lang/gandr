//! Canonical content: an item's or a type's nodes as a co-de Bruijn table,
//! numbered by discovery, free of arena ids and admission positions.
//!
//! # One minimal-scope table per item
//!
//! The encoder lists every node reachable from an item's roots as a de
//! Bruijn table; `support::factor` then rebuilds it bottom-up as the
//! carrier of `gandr_core_term::support` lays it out. Each entry is a
//! [`SupportedNode`]: a compact former whose own variable, endpoint or slot,
//! if it has one, is a rank in its scope; the scope itself, as wide in each
//! zone as the variables free beneath the node; and a cover, one thinning
//! per child, saying where each of the child's free variables sits in the
//! node's scope or among the binders the child's slot crosses. Each root
//! keeps its own thinning into the item's empty scope. A child is named by
//! its number, a constant by the [`Reference`] its position resolves to.
//!
//! Equal compact nodes are one entry: the table is hash-consed by former,
//! cover and scope, so two equal subterms share whether the arena allocated
//! them once or twice, and a subterm under different unused binders is the
//! same entry because unused binders never reach its scope. Different
//! variable wiring stays distinct, because the cover records it. The arena's
//! own sharing is therefore no part of the content: two items built in two
//! arenas have equal tables exactly when their terms are equal.
//!
//! The table is numbered in the order a breadth-first walk from the roots
//! first discovers each entry, children left to right, so the numbering is a
//! function of the content. Factoring and numbering are iterative; the work
//! is linear in the de Bruijn table plus the sizes of the covers and the
//! reference sets.
//!
//! # References read off the roots
//!
//! Every entry carries the references beneath it, apart by position: those
//! in term positions and those beneath a signature or a type former, built
//! from its children's when it is factored and rebuilt by the reader of a
//! persisted table, which never trusts a stored set. An item's footprint is
//! the union over its roots (`footprint_of`); no walk of the table is needed.
//! The references are syntactic and over-approximate what the judgement
//! reads, as the footprint always has; they never decide a strengthening.
//!
//! # The de Bruijn projection
//!
//! [`TypeContent::debruijn`] and [`ItemContent::debruijn`] expand a root
//! back into a de Bruijn table under its root thinning: what minting a seat,
//! printing a type or any reader that counts binders consumes. A root
//! thinning whose index passes `u32` beneath a binder is reported as
//! `PlacementError::IndexOverflow`, never saturated.
//!
//! **Choice.** The compact former is [`ContentNode`] itself, its own
//! occurrence rewritten to its rank, rather than a former generic over its
//! index type: session actions and memory forms carry their endpoints and
//! slots as kernel indices inside shared syntax, and one former type keeps
//! the codec, the minting path and the printer on one vocabulary.
//! **Reversal.** A consumer that must tell a rank from an ambient index by
//! type, not by the table it came from, makes the generic former worth its
//! second spelling.
//!
//! # An id the arena does not hold
//!
//! An id that resolves to nothing is a fact about another arena. It is listed
//! as [`ContentNode::Unresolved`] with its sort, so encoding stays total, and
//! a table holding one beneath a root is opaque: its item is never adopted,
//! never persisted, and a reader of everything once anything changes. A
//! child of a de Bruijn table out of its range, or one closing a cycle, is
//! factored the same way.
//!
//! # Content, not ids
//!
//! An item's content is its reference, declaration category, the table of
//! every node reachable from its `DeclarationRoots` and each root's
//! thinning. Value roots retain the signature and body; Data roots retain
//! the kind, parameter telescope and constructor field types.
//!
//! # Native universe-path content
//!
//! The content table preserves universe sorts and levels, quotes, static
//! operators and native universe paths. Native path tags occupy `0x40–0x44` in
//! this cache codec, and element identity `0x45–0x4C`: the path type, `here`,
//! element transport, a compound endpoint, `funext` over its two functions,
//! `equiv` over its two translators, the telescope transport, and `ua` over
//! its stratum, its two descriptions and its translator records. None is a
//! kernel artifact tag.
//! Candidate evidence is exact content, including ordered direction and
//! dialogue boundaries, and never a cached admission receipt; a `funext` or an
//! `equiv` is content by its functions alone, and the evaluations it was
//! decided by are recomputed by the judgement that reads it. Type-only
//! signature content refuses term-bearing path
//! classifiers just as it refuses quotes and decodes.
//!
//! Checkpoint sets use `GCKPT\0\0\x10`; programs use `GPROG\0\0\x0a`. Their
//! identities bind the checker, native declaration categories, effect and
//! control content, support queries and refusal vocabulary. Identities of
//! another version are rejected rather than reusing answers from a different
//! fragment. Static family, universe and native-former round-trip witnesses
//! exercise their distinct tags and payloads.
//!
//! **Choice.** Preserve native classifiers, maps and candidate evidence as
//! content instead of caching a certificate verdict. Structural path conversion
//! may erase evidence, but checkpoint identity must not. **Reversal.**
//! Persisting the bridge mode, higher fields or guarded List inhabitants
//! requires its own versioned content vocabulary and validated dependency
//! support; none is inferred from a native path entry. The directed family
//! persists under its own tags, below.
//!
//! # Native declaration content and support
//!
//! A declaration's roots are `DeclarationRoots::Value`,
//! `DeclarationRoots::Data`, `DeclarationRoots::Abstract` or
//! `DeclarationRoots::World`; data retains the kind, every parameter and every
//! constructor field, and an abstract type its kind, its representation, the
//! extent of its seal, the site that mints its atom, the mobility its
//! signature marks and the relation, reflexivity and law of its interface,
//! each a value root, so an edit to the interface reaches every reader of the
//! atom. A mobile atom and an interfaced one take their own roots tags, so an
//! unmarked one without an interface encodes as before. Cache node tags
//! `0x50–0x55` represent the six native data/record forms independently of
//! kernel artifact tags, `0x5A` the positional tuple projection, its component
//! a count after its tuple child, and `0x5B` the split, its arity a count
//! between its scrutinee and body children. Field labels and arbitrary child
//! counts survive persistence.
//!
//! A value declaration's roots carry the laws its folds rest on as item
//! references, so adding, removing or reordering a `respects` law changes the
//! declaration's content even though its body is unchanged. A law's statement
//! reaches the fold the way any read signature does: the check reads it
//! through the signature table, and the support records the answer. Lawful
//! roots persist under their own roots tag, so content naming no law encodes
//! exactly as before.
//!
//! An abstract type answers no support query: a reader of its atom records
//! the atom in a type position, so an edit to the representation, the extent
//! or the site changes the abstract type's content and reaches every reader
//! through the value-changed closure. Adoption forms it again and mints its
//! atom in the new context.
//!
//! A located program — one declaring a world, or stating an entry — is
//! judged whole each time and never persisted: every item of it is opaque
//! (see [`Locus`]), and a world form or a world type in any item is listed
//! by its sort, as a stage is.
//!
//! Support keys distinguish a value-signature query from a data-signature query
//! at the same reference. A data answer contains the complete nominal schema or
//! its absence, not merely its universe. Adoption reforms a retained data
//! declaration in the new context. Term-bearing nominal type content remains
//! outside the type-only adoption reader and is conservatively rechecked; it is
//! never promoted to an authority-bearing cache hit.
//!
//! **Choice.** Extend ordinary declaration content and query-specific support
//! instead of treating data as a value signature. **Reversal.** A wider
//! adoption reader must validate term-valued indices and their dependencies
//! before reusing them.
//! `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
//! round-trips accepted and refused items, adopts an unchanged module,
//! invalidates a constructor after a schema-only change, and compares
//! incremental results with fresh checking.
//!
//! # Recursive data and fixpoints
//!
//! A fixpoint persists as cache node tag `0x19` with its evidence and its body;
//! it is a term, never a seatable type. A data declaration's fields may name
//! it: the self reference resolves to the item's own reference, and the checker
//! reads the forming block without a support query, so a recursive
//! declaration's footprint holds no query of itself. The occurrence refusals
//! keep their parameter or field site, a reference past the block keeps the
//! reference it names, and a descent refusal keeps its fixpoint's site and the
//! rule of the walk that failed.
//!
//! **Choice.** Persist the evidence as content, so a partial and a structurally
//! descending fixpoint never share an address. **Reversal.** A mutual block
//! would add a block reference to the support vocabulary; until then one block
//! is one item.
//! `tests::recursive_data::recursive_data_checkpoints_round_trip_and_resume`
//! round-trips a recursive family, a fixpoint and each new refusal and adopts
//! the unchanged program.
//!
//! # Effect and control content
//!
//! Pure returners retain tag `0x30`; row-qualified returners use `0x70`. Inline
//! interfaces store canonical operation names and ordered payload/reply type
//! edges. The List former and its control content use the following cache tags,
//! independent of kernel artifact tags.
//!
//! | Tag | Former |
//! | --- | ------ |
//! | `0x56` | List classifier |
//! | `0x57` | Empty list |
//! | `0x58` | Cons |
//! | `0x59` | List fold |
//! | `0x71` | Reify |
//! | `0x72` | Stack classifier |
//! | `0x73` | With classifier |
//! | `0x74` | Perform |
//! | `0x75` | Handle |
//! | `0x76` | Resume |
//! | `0x77` | Reset |
//! | `0x78` | Shift |
//! | `0x79` | With computation |
//! | `0x7A` | Project |
//! | `0x7B` | Exercise |
//! | `0x7C` | Capability scope |
//! | `0x7D` | Capability classifier |
//!
//! A handler retains source clause order; its branches' binders are
//! crossings of their slots, and the projection restores their de Bruijn
//! indices.
//! Stack frames retain execution order and projection side. Fixed children
//! precede interface type edges, which precede clause bodies; frames contribute
//! their Apply and Bind children in order. Unknown-operation, coverage,
//! undelimited-shift and dependent-stack refusals retain their sites and type
//! payloads. Closed Stack/With type tables can be reminted into another arena;
//! runtime term graphs are not invented by the type-only reminting path.
//!
//! A capability scope persists as a handler does, under its own tag, so a
//! scope and a handler over one interface never share an address. An exercise
//! keeps its capability and payload before its interface's type edges. A
//! capability classifier keeps its authority's restricted interfaces as a row,
//! then its grade and its region, a scoped region by its depth; it seats like
//! any closed type. The capability refusals keep their sites and type payloads.
//!
//! The session identities persist under their own tags, beside the session
//! classifier (`0x60`) and action (`0x61`):
//!
//! | Tag | Former |
//! | --- | ------ |
//! | `0x62` | Session statement, `bisim` or `sim` |
//! | `0x63` | Stay |
//! | `0x64` | Then |
//! | `0x65` | Recorded run |
//! | `0x66` | Ride |
//! | `0x67` | Flow classifier |
//! | `0x68` | Run classifier |
//! | `0x69` | Forward flow, `forward(f)` |
//! | `0x6A` | Function flow, `arrow(d, c)` |
//! | `0x6B` | Flow product, `flowProduct(p, q)` |
//!
//! A statement keeps its relation, so `bisim(a, b)` and `sim(a, b)` never
//! share an address; the decided simulation is checker output and is not
//! content. A recorded run keeps its moves in order, its payloads as value
//! edges and its labels inline. Flow and run classifiers hold terms and do
//! not seat, as an element path does not.
//!
//! **Choice.** Preserve typed interfaces and control syntax as content, not
//! runtime heap addresses or captured delimiter stacks. Omitting annotations
//! permits stale adoption; persisting a runtime continuation would require a
//! separate heap and capability protocol. Revisit only when that protocol and
//! its dependency validation are specified.
//!
//! Witnesses:
//! `content::tests::control_graphs_preserve_scopes_and_signature_edges`,
//! `content::tests::capability_graphs_keep_authority_region_and_scope`,
//! `codec::tests::control_nodes_persist_names_frames_and_branch_order` and
//! `edit::tests::control_edits_preserve_names_scopes_and_frame_order` in
//! `gandr-surface-session`.

use alloc::collections::BTreeMap;
use alloc::collections::VecDeque;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_term::BinderDepth;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::MarkIndex;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_core_term::session::SessionAction;
use gandr_core_term::support::Crossing;
use gandr_core_term::support::PlacementError;
use gandr_core_term::support::Thinning;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Summand;
use quenchant_shape::shape::Maybe;

use crate::boundary::NodeIndex;
use crate::region::Layout;
use crate::region::Program;
use crate::region::Reference;
use crate::support::SupportedNode;

quenchant_shape::reason_enum! {
    /// Why a type table could not be minted back into an arena.
    pub mod seating {
        /// The reason no node was minted.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The table holds an id another arena minted.
            Unresolved,
            /// The table holds a node that is its own descendant, which no
            /// arena can mint child before parent.
            Cyclic,
            /// The table names an item the program does not hold.
            Unplaced,
            /// The table is not a value type, or a child has the wrong sort.
            IllSorted,
            /// The type holds a term — the code of an element type — and a
            /// seat mints types alone.
            Unseatable,
            /// The type's de Bruijn projection places an index past the
            /// index space, or an edge past its node's support.
            Unplaceable,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an arena node has no site in an item's table.
    pub mod site {
        /// The reason no site is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The item's walk never reached the node.
            Unreached,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a content node names no reference.
    pub mod referencing {
        /// The reason no reference is named.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The node is neither a constant nor an abstract type.
            NotAReference,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a content node names no variable occurrence of its own.
    pub mod occurring {
        /// The reason no occurrence is named.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The node is no variable, endpoint use or memory slot use.
            Unnamed,
        }
    }
}

/// The four node sorts of the core vocabulary.
///
/// # Specification
/// - executable: none — a sort tag carries no arena or node whose
///   classification it could certify.
///
/// # Adequacy
/// - hypothesis: L2 — the finite content corpus exercises all four sorts; the
///   tag alone does not certify a table edge.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Sort
{
    /// A value.
    Value,
    /// A computation.
    Computation,
    /// A value type.
    ValueType,
    /// A computation type.
    CompType,
}

/// A node of a core arena, of any sort.
///
/// # Specification
/// - executable: none — the tagged identifier has no arena to establish whether
///   its node resolves.
///
/// # Adequacy
/// - hypothesis: L2 — arena-relative identity is separated by allocation noise
///   and an unresolved value identifier; other unresolved sorts are not claimed
///   here.
/// - witness: `content::tests::content_is_free_of_arena_ids`
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ArenaNode
{
    /// A value node.
    Value(ValueId),
    /// A computation node.
    Computation(ComputationId),
    /// A value-type node.
    ValueType(ValueTypeId),
    /// A computation-type node.
    CompType(CompTypeId),
}

/// One node of a content table: a core former over table indices.
///
/// # Specification
/// - executable: none — an entry alone has neither its table nor its arena;
///   edge validity belongs to the consuming walk.
///
/// # Adequacy
/// - hypothesis: L3 — shared and unresolved nodes, interleaved roots and the
///   finite persistence corpus bound the former and edge evidence; raw entries
///   need not form a closed or well-sorted table.
/// - witness: `content::tests::a_shared_node_is_listed_once`
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ContentNode
{
    /// A nominal datatype instance, preserving its declaration identity.
    Data
    {
        /// The declaration's stable item reference.
        declaration: Reference,
        /// Value arguments in telescope order.
        arguments: Vec<NodeIndex>,
    },
    /// A structural record classifier, ordered by field label.
    RecordType(BTreeMap<gandr_core_term::FieldLabel, NodeIndex>),
    /// A constructor at its complete nominal classifier.
    Constructor
    {
        /// The classifier of the constructed value.
        datatype: NodeIndex,
        /// The constructor's ordinal in its declaration.
        tag: gandr_core_term::ConstructorTag,
        /// Constructor fields in declaration order.
        fields: Vec<NodeIndex>,
    },
    /// A record value, ordered by field label.
    Record(BTreeMap<gandr_core_term::FieldLabel, NodeIndex>),
    /// Nominal elimination with a one-scrutinee-binder motive.
    DataCase
    {
        /// The eliminated value.
        scrutinee: NodeIndex,
        /// The result classifier under the scrutinee binder.
        motive: NodeIndex,
        /// Ambient-scope branch functions, in constructor order.
        branches: Vec<NodeIndex>,
        /// Each constructor's field count, in constructor order.
        arities: Vec<gandr_kernel_term::FieldCount>,
        /// The equations each branch takes past its fields, one per index.
        equations: gandr_kernel_term::EquationCount,
    },
    /// A projection returning the selected record field.
    RecordProjection(NodeIndex, gandr_core_term::FieldLabel),
    /// A projection returning the selected tuple component.
    TupleProjection(NodeIndex, gandr_core_term::Component),
    /// A flat literal continuation, in execution order.
    Reify(alloc::sync::Arc<[gandr_core_term::control::StackFrame<NodeIndex, NodeIndex>]>),
    /// A stack classifier with ordered input and output computation types.
    Stack
    {
        /// Computation fed to the stack.
        input: NodeIndex,
        /// Computation produced after all frames.
        output: NodeIndex,
    },
    /// A lazy product classifier over its components, in order.
    WithType(Vec<NodeIndex>),
    /// An operation request with its inline interface.
    Perform
    {
        /// Arena-independent interface type edges.
        signature: gandr_core_term::effect::EffectSig<NodeIndex>,
        /// Qualified operation's local name.
        operation: gandr_core_term::effect::OperationName,
        /// Request payload.
        payload: NodeIndex,
    },
    /// A deep handler retaining branch scopes and operation names.
    Handle
    {
        /// The discharged interface.
        signature: gandr_core_term::effect::EffectSig<NodeIndex>,
        /// Handled computation, no additional value binder.
        subject: NodeIndex,
        /// Return branch, beneath one value binder.
        on_return: NodeIndex,
        /// Each operation branch binds payload then resumption.
        clauses: alloc::sync::Arc<[gandr_core_term::control::EffectClause<NodeIndex>]>,
    },
    /// An operation exercised through a capability, with the interface the
    /// operation belongs to.
    Exercise
    {
        /// The capability.
        capability: NodeIndex,
        /// Arena-independent interface type edges.
        signature: gandr_core_term::effect::EffectSig<NodeIndex>,
        /// The operation's local name.
        operation: gandr_core_term::effect::OperationName,
        /// Request payload.
        payload: NodeIndex,
    },
    /// A capability scope: a deep handler whose subject binds the capability
    /// it introduces.
    Scope
    {
        /// The handled interface.
        signature: gandr_core_term::effect::EffectSig<NodeIndex>,
        /// Handled computation, beneath the capability's binder.
        subject: NodeIndex,
        /// Return branch, beneath one value binder.
        on_return: NodeIndex,
        /// Each operation branch binds payload then resumption.
        clauses: alloc::sync::Arc<[gandr_core_term::control::EffectClause<NodeIndex>]>,
    },
    /// A capability classifier: its authority's type edges, grade and
    /// region.
    Capability
    {
        /// The grant atoms, each interface restricted to its granted
        /// operations.
        authority: gandr_core_term::effect::EffectRow<NodeIndex>,
        /// How often it may be exercised.
        grade: gandr_core_term::effect::capability::CapabilityGrade,
        /// How long it lives.
        region: gandr_core_term::effect::capability::Region,
    },
    /// Feed a computation to a first-class stack.
    Resume(NodeIndex, NodeIndex),
    /// End a first-class stack without resuming it.
    Abandon(NodeIndex),
    /// Bind every component of a tuple in the body, component zero
    /// outermost.
    Split(NodeIndex, gandr_core_term::ComponentCount, NodeIndex),
    /// Bind every component of a tuple in the body, component zero
    /// outermost, under a motive over the scrutinee.
    DependentSplit
    {
        /// The tuple.
        scrutinee: NodeIndex,
        /// How many components the body binds.
        arity: gandr_core_term::ComponentCount,
        /// The motive, under one binder of the scrutinee.
        motive: NodeIndex,
        /// The body.
        body: NodeIndex,
    },
    /// A delimited answer boundary.
    Reset(NodeIndex),
    /// Capture a stack, bound in the body.
    Shift(NodeIndex),
    /// Suspended computations, in order.
    With(Vec<NodeIndex>),
    /// A computation ascribed a computation type.
    Ascribe
    {
        /// The computation ascribed.
        body: NodeIndex,
        /// The type it is checked against.
        ty: NodeIndex,
    },
    /// A value ascribed a value type.
    ValueAscribe
    {
        /// The value ascribed.
        value: NodeIndex,
        /// The type it is checked against.
        ty: NodeIndex,
    },
    /// Select a lazy-product component.
    Project(gandr_core_term::Component, NodeIndex),
    /// A closed table-typed native thunk.
    PrimitiveValue(gandr_core_term::primitive::Primitive),
    /// A saturated runtime-native operation.
    Primitive(
        gandr_core_term::primitive::Primitive,
        gandr_core_term::primitive::Arguments<NodeIndex>,
    ),
    /// A native universe-path classifier over quoted codes.
    PathUniverse(NodeIndex, NodeIndex),
    /// A reflexivity certificate.
    PathRefl(NodeIndex),
    /// A product certificate.
    PathProduct(NodeIndex, NodeIndex),
    /// A function extensionality over its two functions.
    Funext(NodeIndex, NodeIndex),
    /// A universe equivalence over its forward and backward translators.
    Equiv(NodeIndex, NodeIndex),
    /// Univalence `ua(e)` over its record and the forward map it carries.
    Univalence(NodeIndex, NodeIndex),
    /// Univalence at a stratum over its two translator records, retaining
    /// the stratum and the descriptions in the cache identity.
    Ua
    {
        /// The degree and the catalogue bound.
        stratum: gandr_core_term::ua::Stratum,
        /// The two descriptions.
        sides: alloc::sync::Arc<gandr_core_term::ua::Sides>,
        /// The forward translator record.
        forward: NodeIndex,
        /// The backward translator record.
        backward: NodeIndex,
    },
    /// An equivalence, retaining its evidence in the cache identity.
    PathEquiv
    {
        /// The classifier.
        path_type: NodeIndex,
        /// The forward map.
        forward: NodeIndex,
        /// The inverse map.
        backward: NodeIndex,
        /// The untrusted round-trip dialogues.
        evidence: alloc::sync::Arc<gandr_kernel_term::PathEvidence>,
    },
    /// Native transport.
    Transport(NodeIndex, NodeIndex),
    /// An element path type over its carrier and two endpoints.
    PathType
    {
        /// The carrier.
        carrier: NodeIndex,
        /// The left endpoint.
        left: NodeIndex,
        /// The right endpoint.
        right: NodeIndex,
    },
    /// Element reflexivity at its point.
    Here(NodeIndex),
    /// A compound endpoint: the computation whose returned value it stands
    /// for.
    Returned(NodeIndex),
    /// A computation written where a value is read, before elaboration.
    Nested(NodeIndex),
    /// A written run where a value is read, before elaboration.
    Run(NodeIndex),
    /// Transport along an element path in a motive under one binder.
    ElementTransport
    {
        /// The motive, under one binder.
        motive: NodeIndex,
        /// The path.
        path: NodeIndex,
        /// The transported value.
        value: NodeIndex,
    },
    /// Transport over a two-entry telescope, its motive a computation type
    /// whose arrows bind the telescope.
    TelescopeTransport
    {
        /// The motive.
        motive: NodeIndex,
        /// The path.
        path: NodeIndex,
        /// The family element at the path's source.
        start: NodeIndex,
        /// The identity over the path.
        over: NodeIndex,
        /// The transported value.
        value: NodeIndex,
    },
    /// A session statement over two session codes, retaining the relation it
    /// claims, and the paths covering its differing payload pairs.
    SessionRelated
    {
        /// Equivalence or subtyping.
        relation: gandr_core_term::session::SessionRelation,
        /// The source code.
        source: NodeIndex,
        /// The target code.
        target: NodeIndex,
        /// The payload paths, the empty tuple when none is written.
        payloads: NodeIndex,
    },
    /// The identity flow at its point.
    Stay(NodeIndex),
    /// Two flows composed, the first first.
    Then(NodeIndex, NodeIndex),
    /// The forward flow of a translator, `forward(f)`.
    Forward(NodeIndex),
    /// The arrow's action on a domain and a codomain flow, `arrow(d, c)`.
    FunctionFlow(NodeIndex, NodeIndex),
    /// The product of two universe flows, `flowProduct(p, q)`.
    FlowProduct(NodeIndex, NodeIndex),
    /// A recorded run, its moves in order, each payload an edge.
    Recorded(alloc::sync::Arc<[gandr_core_term::session::RecordedMove<NodeIndex>]>),
    /// Transport of a value along a flow in a motive under one binder.
    Ride
    {
        /// The motive, under one binder.
        motive: NodeIndex,
        /// The flow.
        flow: NodeIndex,
        /// The ridden value.
        value: NodeIndex,
    },
    /// A flow type over its carrier and two endpoints.
    FlowType
    {
        /// The carrier.
        carrier: NodeIndex,
        /// The source endpoint.
        source: NodeIndex,
        /// The target endpoint.
        target: NodeIndex,
    },
    /// The type of recorded runs of a session code.
    RunType(NodeIndex),
    /// The type of recorded prefixes of a session code.
    PrefixType(NodeIndex),
    /// A bound variable.
    Variable
    {
        /// The zone its index counts in.
        zone: Zone,
        /// The index.
        index: DeBruijnIndex,
    },
    /// A constant, by what its position names.
    Constant(Reference),
    /// A literal.
    Literal(Literal),
    /// A tuple of values, in order; the empty tuple is the unit value.
    Tuple(Vec<NodeIndex>),
    /// The empty native list.
    ListNil,
    /// A native list cell.
    ListCons(NodeIndex, NodeIndex),
    /// A sum injection into its summand.
    Injection(Summand, NodeIndex),
    /// A thunk of a computation.
    Thunk(NodeIndex),
    /// A universe lift of a value.
    ValueLift
    {
        /// The target level.
        target: Level,
        /// The value lifted.
        body: NodeIndex,
    },
    /// The code of a value type.
    Quote(NodeIndex),
    /// The code of a computation type.
    QuoteComputation(NodeIndex),
    /// A static lambda over its body, under one binder.
    StaticLambda(NodeIndex),
    /// A static application of an operator to an argument.
    StaticApplication(NodeIndex, NodeIndex),
    /// A term hole in value position, by its name.
    Hole(HoleId),
    /// A marked value: the mark's index over the value it marks.
    ValueMark
    {
        /// The mark's index in its elaboration's table.
        mark: MarkIndex,
        /// The value marked.
        body: NodeIndex,
    },
    /// A lambda over its body.
    Lambda(NodeIndex),
    /// An application of a computation to a value.
    Application(NodeIndex, NodeIndex),
    /// A return of a value.
    Return(NodeIndex),
    /// A bind of a computation into a continuation.
    Bind(NodeIndex, NodeIndex),
    /// A force of a value.
    Force(NodeIndex),
    /// A sum elimination.
    Case
    {
        /// The scrutinee.
        scrutinee: NodeIndex,
        /// The branches, one per summand in order.
        branches: Vec<NodeIndex>,
    },
    /// A term hole in computation position, by its name.
    ComputationHole(HoleId),
    /// A marked computation: the mark's index over the computation it marks.
    ComputationMark
    {
        /// The mark's index in its elaboration's table.
        mark: MarkIndex,
        /// The computation marked.
        body: NodeIndex,
    },
    /// A fixpoint over its body, under the self binder, with its evidence.
    Fixpoint
    {
        /// The body.
        body: NodeIndex,
        /// The termination evidence it carries.
        evidence: FixpointEvidence,
    },
    /// A pure native List fold, with annotations and ordered branches.
    ListFold
    {
        /// Ambient element type.
        element: NodeIndex,
        /// Ambient result type.
        result: NodeIndex,
        /// The list value.
        list: NodeIndex,
        /// The empty branch.
        on_nil: NodeIndex,
        /// The cell branch beneath two binders.
        on_cons: NodeIndex,
    },
    /// A native List case: the list and its two branches.
    ListCase
    {
        /// The list value.
        list: NodeIndex,
        /// The empty branch.
        on_nil: NodeIndex,
        /// The cell branch beneath two binders: the head, then the tail.
        on_cons: NodeIndex,
    },
    /// A session action: payload, arms, fork protocol and halves as edges,
    /// endpoints and labels as written.
    Session(gandr_core_term::session::SessionAction<NodeIndex, NodeIndex, NodeIndex>),
    /// A memory form: a held or written-back value and the bodies as edges,
    /// the linear slots as written.
    Memory(gandr_core_term::memory::MemoryForm<NodeIndex, NodeIndex>),
    /// A base-type atom.
    Base(BaseType),
    /// A product type over its components, in order; the empty product is
    /// the unit type.
    Product(Vec<NodeIndex>),
    /// A sum type over its summands, in order.
    Sum(Vec<NodeIndex>),
    /// A finite-list type.
    List(NodeIndex),
    /// A value type kept in a region: a capability scope's or a hold's by its
    /// depth, or a definition's region binder by its ordinal.
    KeptType
    {
        /// The kept value's type.
        value: NodeIndex,
        /// The region it lives in.
        region: gandr_core_term::effect::capability::Region,
    },
    /// A thunk type.
    ThunkType(NodeIndex),
    /// A universe of one sort.
    Universe
    {
        /// The family it classifies.
        sort: gandr_core_term::Sort,
        /// Its level within that family.
        level: Level,
    },
    /// A lift of a value type.
    TypeLift
    {
        /// The type lifted.
        inner: NodeIndex,
        /// The target level.
        target: Level,
    },
    /// The type a code denotes.
    Element
    {
        /// The code.
        code: NodeIndex,
        /// The level it is read at.
        target: Level,
    },
    /// A static Pi, whose codomain binds nothing.
    StaticPi
    {
        /// The domain.
        domain: NodeIndex,
        /// The codomain.
        codomain: NodeIndex,
    },
    /// A dependent pair, whose second factor binds the first.
    Sigma
    {
        /// The first factor.
        first: NodeIndex,
        /// The second factor, under the binder.
        second: NodeIndex,
    },
    /// A session type: its protocol and state, payload edges in slot order.
    SessionType(gandr_core_term::session::SessionType<NodeIndex>),
    /// A sealed abstract type, by what its position names.
    Abstract(Reference),
    /// The unknown value type.
    UnknownType,
    /// The opaque buffer type a receive places live.
    BufferType,
    /// A returner type.
    Returner
    {
        /// The returned value type.
        result: NodeIndex,
        /// Interfaces whose type edges use this content table's indices.
        effects: gandr_core_term::effect::EffectRow<NodeIndex>,
    },
    /// A non-dependent arrow.
    Arrow
    {
        /// The domain.
        domain: NodeIndex,
        /// The codomain.
        codomain: NodeIndex,
    },
    /// A dependent arrow.
    Pi
    {
        /// The domain.
        domain: NodeIndex,
        /// The codomain, under the domain's binder.
        codomain: NodeIndex,
    },
    /// The computation type a code denotes.
    ComputationElement
    {
        /// The code.
        code: NodeIndex,
        /// The level it is read at.
        target: Level,
    },
    /// The unknown computation type.
    UnknownComputationType,
    /// An id of this sort the arena resolves to nothing.
    Unresolved(Sort),
}

/// A fixed child slot of a former, counted from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ChildSlot(pub usize);

/// The children of one content node, each with the sort it must have and the
/// binders it stands under.
///
/// # Specification
/// - executable: none — the active-prefix representation is maintained by
///   `Children::of` and read by the graph walks, not a callable declaration.
///
/// # Adequacy
/// - hypothesis: L2 — sharing and interleaved roots exercise active child
///   slots; the persistence corpus covers selected multi-sort formers, not
///   every graph. Every binding former's crossings are checked by projecting
///   its cover back to de Bruijn indices.
/// - witness: `content::tests::a_shared_node_is_listed_once`
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
/// - witness: `content::tests::covers_preserve_every_binding_former`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Children<'node>
{
    /// The children in order; slots past `count` are unused.
    slots: [(NodeIndex, Sort); 5],
    /// The binders each fixed child stands under, slot for slot.
    crossings: [Crossing; 5],
    /// How many slots hold a child.
    count: usize,
    /// A variadic suffix, borrowed without per-node allocation.
    suffix: &'node [NodeIndex],
    /// Label-ordered fields, when this node is a record.
    fields: Option<&'node BTreeMap<gandr_core_term::FieldLabel, NodeIndex>>,
    /// The common sort of the suffix or fields.
    tail_sort: Sort,
    /// The binders every suffix child or field stands under.
    tail_crossing: Crossing,
    /// Additional operation-type edges borrowed from a returner's row.
    effects: Option<&'node gandr_core_term::effect::EffectRow<NodeIndex>>,
    /// Inline operation types, after fixed children.
    signature: Option<&'node gandr_core_term::effect::EffectSig<NodeIndex>>,
    /// Named branch bodies, after interface types, each under its payload
    /// and resumption binders.
    clauses: &'node [gandr_core_term::control::EffectClause<NodeIndex>],
    /// Literal stack edges, retaining frame order and omitting projections;
    /// a bind frame's body stands under its binder.
    frames: &'node [gandr_core_term::control::StackFrame<NodeIndex, NodeIndex>],
    /// Recorded moves, contributing their payload values in order.
    moves: &'node [gandr_core_term::session::RecordedMove<NodeIndex>],
}

impl Default for Sort
{
    /// The value sort, which only fills unused child slots.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::Value
    }
}

impl<'node> Children<'node>
{
    /// The children listed in `children`, in order.
    ///
    /// # Specification
    /// - requires: at most five fixed-prefix children; variadic children and a
    ///   row's extra edges are borrowed.
    /// - ensures: the first `children.len()` slots, in order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — shared nodes and the signature walk exercise active
    ///   child slots through graph consumers; the finite corpus adds selected
    ///   arities.
    /// - witness: `content::tests::a_shared_node_is_listed_once`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(
        requires: children.len() <= 5,
        ensures: |ret| ret.count == children.len()
            && ret.slots.get(..ret.count) == Some(children) && ret.effects.is_none(),
    )]
    fn of(children: &[(NodeIndex, Sort)]) -> Self
    {
        let mut slots = [(NodeIndex::default(), Sort::Value); 5];
        let mut count = 0_usize;
        for (slot, &child) in slots.iter_mut().zip(children) {
            *slot = child;
            count = count.saturating_add(1);
        }
        Self {
            slots,
            count,
            ..Self::default()
        }
    }

    /// The children, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the active prefix, in order, excluding unused slots.
    /// - executable: none — anodized 0.7 emits an invalid closure return type
    ///   for this opaque iterator, including for preconditions alone.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named graph consumer exercises the iterator; that
    ///   bounded evidence does not instrument the opaque return.
    /// - witness: `content::tests::a_shared_node_is_listed_once`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    pub(crate) fn iter(self) -> impl DoubleEndedIterator<Item = (NodeIndex, Sort)> + Clone + 'node
    {
        self.crossed().map(|(child, sort, _)| (child, sort))
    }

    /// The children, in order, each beside the binders of either zone the
    /// node opens over it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the children of [`Children::iter`], in its order; a fixed
    ///   slot carries the crossing its former set, a suffix child or field the
    ///   tail crossing, a clause body two intuitionistic binders, a bind
    ///   frame's body one, every other child none.
    /// - executable: none — anodized 0.7 emits an invalid closure return type
    ///   for this opaque iterator, including for preconditions alone.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every binding former, in both zones, projected back
    ///   from its cover recovers its original de Bruijn indices; a crossing on
    ///   the wrong slot or zone shifts an index. Interface types, clause bodies
    ///   and recorded payloads are walked whenever the former carries them,
    ///   checked against `map_children`'s independent enumeration.
    /// - witness: `content::tests::covers_preserve_every_binding_former`
    /// - witness: `content::tests::projection_keeps_every_variadic_child`
    pub(crate) fn crossed(
        self
    ) -> impl DoubleEndedIterator<Item = (NodeIndex, Sort, Crossing)> + Clone + 'node
    {
        let sort = self.tail_sort;
        let tail = self.tail_crossing;
        let none = Crossing::default();
        let clause = Crossing::of(Zone::Intuitionistic, BinderDepth::from(2_usize));
        let frame = Crossing::of(Zone::Intuitionistic, BinderDepth::from(1_usize));
        let fixed = self
            .slots
            .into_iter()
            .zip(self.crossings)
            .take(self.count)
            .map(|((child, sort), crossing)| (child, sort, crossing));
        // Most formers have only fixed slots: their walk skips the seven
        // empty variadic iterators a full chain would step through.
        let variadic = !self.suffix.is_empty()
            || self.fields.is_some()
            || self.effects.is_some()
            || self.signature.is_some()
            || !self.clauses.is_empty()
            || !self.frames.is_empty()
            || !self.moves.is_empty();
        let rest =
            variadic.then(move || {
                self.suffix
                    .iter()
                    .map(move |&child| (child, sort, tail))
                    .chain(
                        self.fields
                            .into_iter()
                            .flat_map(|fields| fields.values())
                            .map(move |&child| (child, sort, tail)),
                    )
                    .chain(self.effects.into_iter().flat_map(move |row| {
                        row.types().map(move |ty| (ty, Sort::ValueType, none))
                    }))
                    .chain(self.signature.into_iter().flat_map(move |signature| {
                        signature.types().map(move |ty| (ty, Sort::ValueType, none))
                    }))
                    .chain(
                        self.clauses
                            .iter()
                            .map(move |clause_body| (clause_body.body, Sort::Computation, clause)),
                    )
                    .chain(self.frames.iter().filter_map(move |step| match *step {
                        gandr_core_term::control::StackFrame::Apply(value) => {
                            Some((value, Sort::Value, none))
                        },
                        gandr_core_term::control::StackFrame::Bind(body) => {
                            Some((body, Sort::Computation, frame))
                        },
                        gandr_core_term::control::StackFrame::Project(_) => None,
                    }))
                    .chain(
                        self.moves
                            .iter()
                            .filter_map(move |step| match step.payload() {
                                Maybe::Present(payload) => Some((payload, Sort::Value, none)),
                                Maybe::Absent(_) => None,
                            }),
                    )
            });
        fixed.chain(rest.into_iter().flatten())
    }

    /// Stand the fixed child at `slot` under `crossing`.
    ///
    /// # Specification
    /// trivial.
    fn binding(
        mut self,
        slot: ChildSlot,
        crossing: Crossing,
    ) -> Self
    {
        if let Some(target) = self.crossings.get_mut(slot.0) {
            *target = crossing;
        }
        self
    }

    /// Stand every suffix child or field under `crossing`.
    ///
    /// # Specification
    /// trivial.
    const fn tail_binding(
        mut self,
        crossing: Crossing,
    ) -> Self
    {
        self.tail_crossing = crossing;
        self
    }

    /// Append a borrowed variadic child suffix.
    ///
    /// # Specification
    /// trivial.
    fn followed_by(
        mut self,
        suffix: &'node [NodeIndex],
        sort: Sort,
    ) -> Self
    {
        self.suffix = suffix;
        self.tail_sort = sort;
        self
    }

    /// Borrow the children of a label-ordered record.
    ///
    /// # Specification
    /// trivial.
    fn fields(
        fields: &'node BTreeMap<gandr_core_term::FieldLabel, NodeIndex>,
        sort: Sort,
    ) -> Self
    {
        Self {
            fields: Some(fields),
            tail_sort: sort,
            ..Self::default()
        }
    }
}

impl ContentNode
{
    /// Direct children in canonical former order, with each child's required
    /// sort.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn child_indices(&self) -> impl DoubleEndedIterator<Item = (NodeIndex, Sort)> + Clone + '_
    {
        self.children().iter()
    }

    /// The node's sort.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the core family of the former, or the stored unresolved sort.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite persistence corpus exercises all four
    ///   families; the unresolved witness bounds the foreign-identifier case to
    ///   values.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    /// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
    #[spec(ensures: |ret| match *self {
        | Self::Constructor { .. }
        | Self::Record(_)
        | Self::Reify(_)
        | Self::PathRefl(_)
        | Self::Here(_)
        | Self::Returned(_)
        | Self::Nested(_)
        | Self::Run(_)
        | Self::SessionRelated { .. }
        | Self::Stay(_)
        | Self::Then(..)
        | Self::Forward(_)
        | Self::FunctionFlow(..)
        | Self::FlowProduct(..)
        | Self::Recorded(_)
        | Self::PrimitiveValue(_)
        | Self::PathProduct(..)
        | Self::Funext(..)
        | Self::Equiv(..)
        | Self::Univalence(..)
        | Self::Ua { .. }
        | Self::PathEquiv { .. }
        | Self::Variable { .. }
        | Self::Constant(_)
        | Self::Tuple(_)
        | Self::ListNil
        | Self::ListCons(..)
        | Self::Literal(_)
        | Self::Injection(..)
        | Self::Thunk(_)
        | Self::ValueLift { .. }
        | Self::Quote(_)
        | Self::QuoteComputation(_)
        | Self::StaticLambda(_)
        | Self::StaticApplication(..)
        | Self::Hole(_)
        | Self::ValueAscribe { .. }
        | Self::ValueMark { .. } => matches!(ret, Sort::Value),
        | Self::DataCase { .. }
        | Self::RecordProjection(..)
        | Self::TupleProjection(..)
        | Self::Perform { .. }
        | Self::Handle { .. }
        | Self::Exercise { .. }
        | Self::Scope { .. }
        | Self::Resume(..)
        | Self::Abandon(_)
        | Self::Split(..)
        | Self::DependentSplit { .. }
        | Self::Reset(_)
        | Self::Shift(_)
        | Self::With(..)
        | Self::Ascribe { .. }
        | Self::Project(..)
        | Self::Transport(..)
        | Self::ElementTransport { .. }
        | Self::TelescopeTransport { .. }
        | Self::Ride { .. }
        | Self::Primitive(..)
        | Self::Lambda(_)
        | Self::Application(..)
        | Self::Return(_)
        | Self::Bind(..)
        | Self::Force(_)
        | Self::ListFold { .. }
        | Self::ListCase { .. }
        | Self::Case { .. }
        | Self::ComputationHole(_)
        | Self::ComputationMark { .. }
        | Self::Session(_)
        | Self::Memory(_)
        | Self::Fixpoint { .. } => matches!(ret, Sort::Computation),
        | Self::Data { .. }
        | Self::RecordType(_)
        | Self::Stack { .. }
        | Self::Capability { .. }
        | Self::PathUniverse(..)
        | Self::PathType { .. }
        | Self::FlowType { .. }
        | Self::RunType(_)
        | Self::PrefixType(_)
        | Self::Base(_)
        | Self::Product(_)
        | Self::Sum(_)
        | Self::List(_)
        | Self::KeptType { .. }
        | Self::ThunkType(_)
        | Self::Universe { .. }
        | Self::TypeLift { .. }
        | Self::Element { .. }
        | Self::Abstract(_)
        | Self::SessionType(_)
        | Self::StaticPi { .. }
        | Self::Sigma { .. }
        | Self::UnknownType
        | Self::BufferType => matches!(ret, Sort::ValueType),
        | Self::WithType(..)
        | Self::Returner { .. }
        | Self::Arrow { .. }
        | Self::Pi { .. }
        | Self::ComputationElement { .. }
        | Self::UnknownComputationType => matches!(ret, Sort::CompType),
        | Self::Unresolved(sort) => matches!(
            (sort, ret),
            (Sort::Value, Sort::Value)
                | (Sort::Computation, Sort::Computation)
                | (Sort::ValueType, Sort::ValueType)
                | (Sort::CompType, Sort::CompType)
        ),
    })]
    pub(crate) const fn sort(&self) -> Sort
    {
        match *self {
            Self::Constructor { .. }
            | Self::Record(_)
            | Self::Reify(_)
            | Self::PathRefl(_)
            | Self::Here(_)
            | Self::Returned(_)
            | Self::Nested(_)
            | Self::Run(_)
            | Self::SessionRelated { .. }
            | Self::Stay(_)
            | Self::Then(..)
            | Self::Forward(_)
            | Self::FunctionFlow(..)
            | Self::FlowProduct(..)
            | Self::Recorded(_)
            | Self::PrimitiveValue(_)
            | Self::PathProduct(..)
            | Self::Funext(..)
            | Self::Equiv(..)
            | Self::Univalence(..)
            | Self::Ua { .. }
            | Self::PathEquiv { .. }
            | Self::Variable { .. }
            | Self::Constant(_)
            | Self::Tuple(_)
            | Self::ListNil
            | Self::ListCons(..)
            | Self::Literal(_)
            | Self::Injection(..)
            | Self::Thunk(_)
            | Self::ValueLift { .. }
            | Self::Quote(_)
            | Self::QuoteComputation(_)
            | Self::StaticLambda(_)
            | Self::StaticApplication(..)
            | Self::Hole(_)
            | Self::ValueAscribe { .. }
            | Self::ValueMark { .. } => Sort::Value,
            Self::DataCase { .. }
            | Self::RecordProjection(..)
            | Self::TupleProjection(..)
            | Self::Perform { .. }
            | Self::Handle { .. }
            | Self::Exercise { .. }
            | Self::Scope { .. }
            | Self::Resume(..)
            | Self::Abandon(_)
            | Self::Split(..)
            | Self::DependentSplit { .. }
            | Self::Reset(_)
            | Self::Shift(_)
            | Self::With(..)
            | Self::Ascribe { .. }
            | Self::Project(..)
            | Self::Transport(..)
            | Self::ElementTransport { .. }
            | Self::TelescopeTransport { .. }
            | Self::Ride { .. }
            | Self::Primitive(..)
            | Self::Lambda(_)
            | Self::Application(..)
            | Self::Return(_)
            | Self::Bind(..)
            | Self::Force(_)
            | Self::ListFold { .. }
            | Self::ListCase { .. }
            | Self::Case { .. }
            | Self::ComputationHole(_)
            | Self::ComputationMark { .. }
            | Self::Session(_)
            | Self::Memory(_)
            | Self::Fixpoint { .. } => Sort::Computation,
            Self::Data { .. }
            | Self::RecordType(_)
            | Self::Stack { .. }
            | Self::Capability { .. }
            | Self::PathUniverse(..)
            | Self::PathType { .. }
            | Self::FlowType { .. }
            | Self::RunType(_)
            | Self::PrefixType(_)
            | Self::Base(_)
            | Self::Product(_)
            | Self::Sum(_)
            | Self::List(_)
            | Self::KeptType { .. }
            | Self::ThunkType(_)
            | Self::Universe { .. }
            | Self::TypeLift { .. }
            | Self::Element { .. }
            | Self::Abstract(_)
            | Self::SessionType(_)
            | Self::StaticPi { .. }
            | Self::Sigma { .. }
            | Self::UnknownType
            | Self::BufferType => Sort::ValueType,
            Self::WithType(..)
            | Self::Returner { .. }
            | Self::Arrow { .. }
            | Self::Pi { .. }
            | Self::ComputationElement { .. }
            | Self::UnknownComputationType => Sort::CompType,
            Self::Unresolved(sort) => sort,
        }
    }

    /// The node's children, in order, each with the sort its former requires.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every child index the node holds, left to right, beside the
    ///   sort the core vocabulary gives that position.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — shared edges and interleaved signature roots test
    ///   graph discovery; the finite persistence corpus supplies selected edges
    ///   across the four sorts. This is not exhaustive evidence for all graphs.
    /// - witness: `content::tests::a_shared_node_is_listed_once`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(ensures: |ret| {
        use Sort::CompType as C;
        use Sort::Computation as M;
        use Sort::Value as V;
        use Sort::ValueType as A;
        let actual = ret.slots.get(.. ret.count);
        (matches!(*self, Self::Returner { .. } | Self::Capability { .. }) || ret.effects.is_none()) && match *self {
            Self::Data { ref arguments,.. } => ret.iter().eq(arguments.iter().map(|&argument| (argument,V))),
            Self::RecordType(ref fields) => ret.iter().eq(fields.values().map(|&field| (field,A))),
            Self::Constructor { datatype,ref fields,.. } => ret.iter().eq(core::iter::once((datatype,A)).chain(fields.iter().map(|&field| (field,V)))),
            Self::Record(ref fields) => ret.iter().eq(fields.values().map(|&field| (field,V))),
            Self::DataCase { scrutinee,motive,ref branches,.. } => ret.iter().eq([(scrutinee,V),(motive,C)].into_iter().chain(branches.iter().map(|&branch| (branch,M)))),
            Self::RecordProjection(record,_) | Self::TupleProjection(record,_) => ret.iter().eq([(record,V)]),
            | Self::Reify(ref frames) => ret.iter().eq(frames.iter().filter_map(|frame| match *frame {
                gandr_core_term::control::StackFrame::Apply(value) => Some((value, V)),
                gandr_core_term::control::StackFrame::Bind(body) => Some((body, M)),
                gandr_core_term::control::StackFrame::Project(_) => None,
            })),
            | Self::Stack { input, output } => actual == Some(&[(input, C), (output, C)][..]),
            | Self::WithType(ref components) => ret.iter().eq(components.iter().map(|&component| (component, C))),
            | Self::Perform { payload, ref signature, .. } => ret.iter().eq(core::iter::once((payload, V)).chain(signature.types().map(|ty| (ty, A)))),
            | Self::Handle { subject, on_return, ref signature, ref clauses } | Self::Scope { subject, on_return, ref signature, ref clauses } => ret.iter().eq([(subject, M), (on_return, M)].into_iter().chain(signature.types().map(|ty| (ty, A))).chain(clauses.iter().map(|clause| (clause.body, M)))),
            | Self::Exercise { capability, payload, ref signature, .. } => ret.iter().eq([(capability, V), (payload, V)].into_iter().chain(signature.types().map(|ty| (ty, A)))),
            | Self::Capability { ref authority, .. } => ret.iter().eq(authority.types().map(|ty| (ty, A))),
            | Self::Resume(stack, body) | Self::Split(stack, _, body) => actual == Some(&[(stack, V), (body, M)][..]),
            | Self::Abandon(stack) => actual == Some(&[(stack, V)][..]),
            | Self::DependentSplit { scrutinee, motive, body, .. } => actual == Some(&[(scrutinee, V), (motive, C), (body, M)][..]),
            | Self::Reset(body) | Self::Shift(body) | Self::Project(_, body) => actual == Some(&[(body, M)][..]),
            | Self::With(ref components) => ret.iter().eq(components.iter().map(|&component| (component, M))),
            | Self::Ascribe { body, ty } => actual == Some(&[(body, M), (ty, C)][..]),
            | Self::ValueAscribe { value, ty } => actual == Some(&[(value, V), (ty, A)][..]),
            | Self::Primitive(_, arguments) => actual.is_some_and(|children| children.iter().copied().eq(arguments.iter().copied().map(|argument| (argument, V)))),
            | Self::Session(ref action) => ret.iter().eq(action.value_types().map(|ty| (ty, A)).chain(action.values().map(|value| (value, V))).chain(action.computations().map(|body| (body, M)))),
            | Self::Memory(ref form) => ret.iter().eq(form.values().map(|value| (value, V)).chain(form.computations().map(|body| (body, M)))),
            | Self::SessionType(ref session) => ret.iter().eq(session.payloads().iter().map(|&payload| (payload, A))),
            | Self::PrimitiveValue(_) | Self::Variable { .. }
            | Self::Constant(_)
            | Self::ListNil
            | Self::Literal(_)
            | Self::Base(_)
            | Self::Universe { .. }
            | Self::Abstract(_)
            | Self::Unresolved(_)
            | Self::Hole(_)
            | Self::ComputationHole(_)
            | Self::UnknownType
            | Self::BufferType
            | Self::UnknownComputationType => ret.count == 0,
            | Self::Tuple(ref components) => ret.iter().eq(components.iter().map(|&component| (component, V))),
            | Self::ListFold { element, result, list, on_nil, on_cons } => actual == Some(&[(element, A), (result, A), (list, V), (on_nil, M), (on_cons, M)][..]),
            | Self::ListCase { list, on_nil, on_cons } => actual == Some(&[(list, V), (on_nil, M), (on_cons, M)][..]),
            | Self::Univalence(a, b)
            | Self::ListCons(a, b) | Self::StaticApplication(a, b) | Self::PathUniverse(a, b) | Self::PathProduct(a, b) | Self::Funext(a, b) | Self::Equiv(a, b) | Self::Ua { forward: a, backward: b, .. } | Self::Transport(a, b) | Self::Then(a, b) | Self::FlowProduct(a, b) | Self::FunctionFlow(a, b) => {
                actual == Some(&[(a, V), (b, V)][..])
            },
            | Self::SessionRelated { source, target, payloads, .. } => actual == Some(&[(source, V), (target, V), (payloads, V)][..]),
            | Self::PathEquiv { path_type, forward, backward, .. } => actual == Some(&[(path_type, A), (forward, V), (backward, V)][..]),
            | Self::PathType { carrier, left, right } | Self::FlowType { carrier, source: left, target: right } => actual == Some(&[(carrier, A), (left, V), (right, V)][..]),
            | Self::ElementTransport { motive, path, value } | Self::Ride { motive, flow: path, value } => actual == Some(&[(motive, A), (path, V), (value, V)][..]),
            | Self::Recorded(ref moves) => ret.iter().eq(moves.iter().filter_map(|step| match step.payload() { Maybe::Present(payload) => Some((payload, V)), Maybe::Absent(_) => None })),
            | Self::TelescopeTransport { motive, path, start, over, value } => actual == Some(&[(motive, C), (path, V), (start, V), (over, V), (value, V)][..]),
            | Self::Returned(a) | Self::Nested(a) | Self::Run(a) => actual == Some(&[(a, M)][..]),
            | Self::PathRefl(a)
            | Self::Here(a)
            | Self::Stay(a)
            | Self::Forward(a)
            | Self::RunType(a)
            | Self::PrefixType(a)
            | Self::StaticLambda(a)
            | Self::Injection(_, a)
            | Self::ValueLift { body: a, .. }
            | Self::Return(a)
            | Self::Force(a)
            | Self::Element { code: a, .. }
            | Self::ComputationElement { code: a, .. }
            | Self::ValueMark { body: a, .. } => actual == Some(&[(a, V)][..]),
            | Self::ComputationMark { body: a, .. } | Self::Thunk(a) | Self::Lambda(a) | Self::Fixpoint { body: a, .. } => {
                actual == Some(&[(a, M)][..])
            },
            | Self::Application(a, b) => actual == Some(&[(a, M), (b, V)][..]),
            | Self::Bind(a, b) => actual == Some(&[(a, M), (b, M)][..]),
            | Self::Case {
                scrutinee: a,
                ref branches,
            } => ret.iter().eq(core::iter::once((a, V)).chain(branches.iter().map(|&branch| (branch, M)))),
            | Self::Product(ref parts) | Self::Sum(ref parts) => ret.iter().eq(parts.iter().map(|&part| (part, A))),
            | Self::StaticPi {
                domain: a,
                codomain: b,
            }
            | Self::Sigma {
                first: a,
                second: b,
            } => actual == Some(&[(a, A), (b, A)][..]),
            | Self::ThunkType(a) | Self::QuoteComputation(a) => actual == Some(&[(a, C)][..]),
            | Self::Returner { result, ref effects } => ret.iter().eq(core::iter::once((result, A)).chain(effects.types().map(|ty| (ty, A)))),
            | Self::List(a)
            | Self::KeptType { value: a, .. }
            | Self::TypeLift { inner: a, .. }
            | Self::Quote(a) => {
                actual == Some(&[(a, A)][..])
            },
            | Self::Arrow {
                domain: a,
                codomain: b,
            }
            | Self::Pi {
                domain: a,
                codomain: b,
            } => actual == Some(&[(a, A), (b, C)][..]),
        }
    })]
    pub(crate) fn children(&self) -> Children<'_>
    {
        use Sort::CompType as C;
        use Sort::Computation as M;
        use Sort::Value as V;
        use Sort::ValueType as A;
        let one = Crossing::of(Zone::Intuitionistic, BinderDepth::from(1_usize));
        let two = Crossing::of(Zone::Intuitionistic, BinderDepth::from(2_usize));
        let linear = Crossing::of(Zone::Linear, BinderDepth::from(1_usize));
        let split = |arity: gandr_core_term::ComponentCount| {
            Crossing::of(Zone::Intuitionistic, BinderDepth::from(usize::from(arity)))
        };
        match *self {
            Self::Data { ref arguments, .. } => Children::default().followed_by(arguments, V),
            Self::RecordType(ref fields) => Children::fields(fields, A),
            Self::Constructor {
                datatype,
                ref fields,
                ..
            } => Children::of(&[(datatype, A)]).followed_by(fields, V),
            Self::Record(ref fields) => Children::fields(fields, V),
            Self::DataCase {
                scrutinee,
                motive,
                ref branches,
                ..
            } => Children::of(&[(scrutinee, V), (motive, C)])
                .binding(ChildSlot(1), one)
                .followed_by(branches, M),
            Self::RecordProjection(record, _) | Self::TupleProjection(record, _) => {
                Children::of(&[(record, V)])
            },
            Self::Reify(ref frames) => Children {
                frames,
                ..Children::default()
            },
            Self::Stack { input, output } => Children::of(&[(input, C), (output, C)]),
            Self::WithType(ref components) => Children::default().followed_by(components, C),
            Self::Perform {
                payload,
                ref signature,
                ..
            } => Children {
                signature: Some(signature),
                ..Children::of(&[(payload, V)])
            },
            Self::Handle {
                subject,
                on_return,
                ref signature,
                ref clauses,
            } => Children {
                signature: Some(signature),
                clauses,
                ..Children::of(&[(subject, M), (on_return, M)]).binding(ChildSlot(1), one)
            },
            Self::Scope {
                subject,
                on_return,
                ref signature,
                ref clauses,
            } => Children {
                signature: Some(signature),
                clauses,
                ..Children::of(&[(subject, M), (on_return, M)])
                    .binding(ChildSlot(0), one)
                    .binding(ChildSlot(1), one)
            },
            Self::Exercise {
                capability,
                payload,
                ref signature,
                ..
            } => Children {
                signature: Some(signature),
                ..Children::of(&[(capability, V), (payload, V)])
            },
            Self::Capability { ref authority, .. } => Children {
                effects: Some(authority),
                ..Children::default()
            },
            Self::Resume(stack, body) => Children::of(&[(stack, V), (body, M)]),
            Self::Abandon(stack) => Children::of(&[(stack, V)]),
            Self::Split(stack, arity, body) => {
                Children::of(&[(stack, V), (body, M)]).binding(ChildSlot(1), split(arity))
            },
            Self::DependentSplit {
                scrutinee,
                motive,
                body,
                arity,
            } => Children::of(&[(scrutinee, V), (motive, C), (body, M)])
                .binding(ChildSlot(1), one)
                .binding(ChildSlot(2), split(arity)),
            Self::Shift(body) => Children::of(&[(body, M)]).binding(ChildSlot(0), one),
            Self::With(ref components) => Children::default().followed_by(components, M),
            Self::Ascribe { body, ty } => Children::of(&[(body, M), (ty, C)]),
            Self::ValueAscribe { value, ty } => Children::of(&[(value, V), (ty, A)]),
            Self::Session(ref action) => match *action {
                SessionAction::Send { payload, .. } => Children::of(&[(payload, V)]),
                SessionAction::Offer { ref arms, .. } => Children::fields(arms, M),
                SessionAction::Fork {
                    protocol,
                    child,
                    parent,
                } => Children::of(&[(protocol, A), (child, M), (parent, M)])
                    .binding(ChildSlot(1), linear)
                    .binding(ChildSlot(2), linear),
                SessionAction::Receive { body, .. } => {
                    Children::of(&[(body, M)]).binding(ChildSlot(0), linear)
                },
                SessionAction::Place { payload, body } => {
                    Children::of(&[(payload, V), (body, M)]).binding(ChildSlot(1), linear)
                },
                SessionAction::Select { .. } | SessionAction::Close { .. } => Children::default(),
            },
            Self::Memory(ref form) => match *form {
                MemoryForm::Hold { value, body, .. } => {
                    Children::of(&[(value, V), (body, M)]).binding(ChildSlot(1), linear)
                },
                MemoryForm::Access {
                    mode: AccessMode::Exclusive { unwind },
                    place: Place::Whole,
                    body,
                    ..
                } => Children::of(&[(body, M), (unwind, M)]).binding(ChildSlot(0), linear),
                MemoryForm::Access {
                    mode: AccessMode::Shared,
                    place: Place::Whole,
                    body,
                    ..
                } => Children::of(&[(body, M)]).binding(ChildSlot(0), linear),
                MemoryForm::Access {
                    mode: AccessMode::Exclusive { unwind },
                    place: Place::At { index },
                    body,
                    ..
                } => Children::of(&[(index, V), (body, M), (unwind, M)])
                    .binding(ChildSlot(1), linear),
                MemoryForm::Access {
                    mode: AccessMode::Shared,
                    place: Place::At { index },
                    body,
                    ..
                } => Children::of(&[(index, V), (body, M)]).binding(ChildSlot(1), linear),
                MemoryForm::Resume { value, .. } => Children::of(&[(value, V)]),
                MemoryForm::Abort { .. } | MemoryForm::Consume { .. } => Children::default(),
            },
            Self::SessionType(ref session) => {
                Children::default().followed_by(session.payloads(), A)
            },
            Self::Primitive(_, arguments) => match arguments {
                gandr_core_term::primitive::Arguments::Unary(argument) => {
                    Children::of(&[(argument, V)])
                },
                gandr_core_term::primitive::Arguments::Binary([first, second]) => {
                    Children::of(&[(first, V), (second, V)])
                },
            },
            Self::PathEquiv {
                path_type,
                forward,
                backward,
                ..
            } => Children::of(&[(path_type, A), (forward, V), (backward, V)]),
            Self::PathType {
                carrier,
                left,
                right,
            }
            | Self::FlowType {
                carrier,
                source: left,
                target: right,
            } => Children::of(&[(carrier, A), (left, V), (right, V)]),
            Self::ElementTransport {
                motive,
                path,
                value,
            }
            | Self::Ride {
                motive,
                flow: path,
                value,
            } => Children::of(&[(motive, A), (path, V), (value, V)]).binding(ChildSlot(0), one),
            Self::Recorded(ref moves) => Children {
                moves,
                ..Children::default()
            },
            Self::TelescopeTransport {
                motive,
                path,
                start,
                over,
                value,
            } => Children::of(&[(motive, C), (path, V), (start, V), (over, V), (value, V)]),
            Self::PrimitiveValue(_)
            | Self::Variable { .. }
            | Self::Constant(_)
            | Self::ListNil
            | Self::Literal(_)
            | Self::Base(_)
            | Self::Universe { .. }
            | Self::Abstract(_)
            | Self::Unresolved(_)
            | Self::Hole(_)
            | Self::ComputationHole(_)
            | Self::UnknownType
            | Self::BufferType
            | Self::UnknownComputationType => Children::default(),
            Self::Tuple(ref components) => Children::default().followed_by(components, V),
            Self::PathUniverse(first, second)
            | Self::PathProduct(first, second)
            | Self::Funext(first, second)
            | Self::Equiv(first, second)
            | Self::Univalence(first, second)
            | Self::Ua {
                forward: first,
                backward: second,
                ..
            }
            | Self::Transport(first, second)
            | Self::Then(first, second)
            | Self::FlowProduct(first, second)
            | Self::FunctionFlow(first, second)
            | Self::ListCons(first, second)
            | Self::StaticApplication(first, second) => Children::of(&[(first, V), (second, V)]),
            Self::SessionRelated {
                source,
                target,
                payloads,
                ..
            } => Children::of(&[(source, V), (target, V), (payloads, V)]),
            Self::StaticLambda(body) => Children::of(&[(body, V)]).binding(ChildSlot(0), one),
            Self::PathRefl(body)
            | Self::Here(body)
            | Self::Stay(body)
            | Self::Forward(body)
            | Self::RunType(body)
            | Self::PrefixType(body)
            | Self::Injection(_, body)
            | Self::ValueLift { body, .. }
            | Self::Return(body)
            | Self::Force(body)
            | Self::ValueMark { body, .. } => Children::of(&[(body, V)]),
            Self::ComputationMark { body, .. }
            | Self::Thunk(body)
            | Self::Returned(body)
            | Self::Nested(body)
            | Self::Run(body)
            | Self::Reset(body)
            | Self::Project(_, body) => Children::of(&[(body, M)]),
            Self::Lambda(body) | Self::Fixpoint { body, .. } => {
                Children::of(&[(body, M)]).binding(ChildSlot(0), one)
            },
            Self::Application(head, argument) => Children::of(&[(head, M), (argument, V)]),
            Self::Bind(bound, rest) => {
                Children::of(&[(bound, M), (rest, M)]).binding(ChildSlot(1), one)
            },
            Self::ListFold {
                element,
                result,
                list,
                on_nil,
                on_cons,
            } => Children::of(&[
                (element, A),
                (result, A),
                (list, V),
                (on_nil, M),
                (on_cons, M),
            ])
            .binding(ChildSlot(4), two),
            Self::ListCase {
                list,
                on_nil,
                on_cons,
            } => Children::of(&[(list, V), (on_nil, M), (on_cons, M)]).binding(ChildSlot(2), two),
            Self::Case {
                scrutinee,
                ref branches,
            } => Children::of(&[(scrutinee, V)])
                .followed_by(branches, M)
                .tail_binding(one),
            Self::Product(ref parts) | Self::Sum(ref parts) => {
                Children::default().followed_by(parts, A)
            },
            Self::StaticPi {
                domain: first,
                codomain: second,
            } => Children::of(&[(first, A), (second, A)]),
            Self::Sigma { first, second } => {
                Children::of(&[(first, A), (second, A)]).binding(ChildSlot(1), one)
            },
            Self::ThunkType(body) => Children::of(&[(body, C)]),
            Self::List(element) | Self::KeptType { value: element, .. } => {
                Children::of(&[(element, A)])
            },
            Self::Returner {
                result,
                ref effects,
            } => {
                let mut children = Children::of(&[(result, A)]);
                children.effects = Some(effects);
                children
            },
            Self::TypeLift { inner, .. } => Children::of(&[(inner, A)]),
            Self::Element { code, .. } | Self::ComputationElement { code, .. } => {
                Children::of(&[(code, V)])
            },
            Self::Quote(quoted) => Children::of(&[(quoted, A)]),
            Self::QuoteComputation(quoted) => Children::of(&[(quoted, C)]),
            Self::Arrow { domain, codomain } => Children::of(&[(domain, A), (codomain, C)]),
            Self::Pi { domain, codomain } => {
                Children::of(&[(domain, A), (codomain, C)]).binding(ChildSlot(1), one)
            },
        }
    }

    /// The reference a constant, abstract type or nominal datatype names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the borrowed reference for Constant, Abstract or Data,
    ///   otherwise `NotAReference`; the predicate checks the presence
    ///   classification.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the footprint corpus separates reachable references
    ///   from unreachable and unresolved entries; the attribute does not assert
    ///   borrowed payload identity in a const expression.
    /// - witness: `footprint::tests::bounded_tables_separate_reachability_opacity_and_holes`
    #[spec(ensures: |ret| match *self {
        Self::Constant(_) | Self::Abstract(_) | Self::Data { .. } => matches!(ret, Maybe::Present(_)),
        Self::Univalence(..) | Self::Abandon(_) |
        Self::RecordType(_) | Self::Constructor { .. } | Self::Record(_) | Self::DataCase { .. } | Self::RecordProjection(..) | Self::TupleProjection(..) | Self::Reify(_) | Self::Stack { .. } | Self::WithType(..) | Self::Perform { .. } | Self::Handle { .. } | Self::Exercise { .. } | Self::Scope { .. } | Self::Capability { .. } | Self::Resume(..) | Self::Split(..) | Self::DependentSplit { .. } | Self::Reset(_) | Self::Shift(_) | Self::With(..) | Self::Ascribe { .. } | Self::ValueAscribe { .. } | Self::Project(..) | Self::PrimitiveValue(_) | Self::Primitive(..) | Self::PathUniverse(..) | Self::PathRefl(_) | Self::PathProduct(..) | Self::Funext(..) | Self::Equiv(..) | Self::Ua { .. } | Self::PathEquiv { .. } | Self::Transport(..) | Self::PathType { .. } | Self::Here(_) | Self::Returned(_) | Self::Nested(_) | Self::Run(_) | Self::ElementTransport { .. } | Self::TelescopeTransport { .. } | Self::SessionRelated { .. } | Self::Stay(_) | Self::Then(..) | Self::Forward(_) | Self::FunctionFlow(..) | Self::FlowProduct(..) | Self::Recorded(_) | Self::Ride { .. } | Self::FlowType { .. } | Self::RunType(_) | Self::PrefixType(_) | Self::Variable { .. } | Self::Literal(_) | Self::Tuple(_) | Self::ListNil | Self::ListCons(..) | Self::Injection(..) | Self::Thunk(_) | Self::ValueLift { .. } | Self::Quote(_) | Self::QuoteComputation(_) | Self::StaticLambda(_) | Self::StaticApplication(..) | Self::Hole(_) | Self::ValueMark { .. } | Self::Lambda(_) | Self::Application(..) | Self::Return(_) | Self::Bind(..) | Self::Force(_) | Self::Case { .. } | Self::ComputationHole(_) | Self::ComputationMark { .. } | Self::Fixpoint { .. } | Self::ListFold { .. } | Self::ListCase { .. } | Self::Session(_) | Self::Memory(_) | Self::Base(_) | Self::Product(_) | Self::Sum(_) | Self::List(_) | Self::KeptType { .. } | Self::ThunkType(_) | Self::Universe { .. } | Self::TypeLift { .. } | Self::Element { .. } | Self::StaticPi { .. } | Self::Sigma { .. } | Self::SessionType(_) | Self::UnknownType | Self::BufferType | Self::Returner { .. } | Self::Arrow { .. } | Self::Pi { .. } | Self::ComputationElement { .. } | Self::UnknownComputationType | Self::Unresolved(_) => matches!(ret, Maybe::Absent(referencing::Absent::NotAReference)),
    })]
    pub(crate) const fn reference(&self) -> Maybe<&Reference, referencing::Absent>
    {
        match *self {
            Self::Constant(ref reference)
            | Self::Abstract(ref reference)
            | Self::Data {
                declaration: ref reference,
                ..
            } => Maybe::Present(reference),
            Self::PathUniverse(..)
            | Self::RecordType(_)
            | Self::Constructor { .. }
            | Self::Record(_)
            | Self::DataCase { .. }
            | Self::RecordProjection(..)
            | Self::TupleProjection(..)
            | Self::Reify(_)
            | Self::Stack { .. }
            | Self::WithType(..)
            | Self::Perform { .. }
            | Self::Handle { .. }
            | Self::Exercise { .. }
            | Self::Scope { .. }
            | Self::Capability { .. }
            | Self::Resume(..)
            | Self::Abandon(_)
            | Self::Split(..)
            | Self::DependentSplit { .. }
            | Self::Reset(_)
            | Self::Shift(_)
            | Self::With(..)
            | Self::Ascribe { .. }
            | Self::ValueAscribe { .. }
            | Self::Session(_)
            | Self::Memory(_)
            | Self::SessionType(_)
            | Self::Project(..)
            | Self::PrimitiveValue(_)
            | Self::Primitive(..)
            | Self::PathRefl(_)
            | Self::Here(_)
            | Self::Returned(_)
            | Self::Nested(_)
            | Self::Run(_)
            | Self::PathType { .. }
            | Self::FlowType { .. }
            | Self::RunType(_)
            | Self::PrefixType(_)
            | Self::SessionRelated { .. }
            | Self::Stay(_)
            | Self::Then(..)
            | Self::Forward(_)
            | Self::FunctionFlow(..)
            | Self::FlowProduct(..)
            | Self::Recorded(_)
            | Self::Ride { .. }
            | Self::ElementTransport { .. }
            | Self::TelescopeTransport { .. }
            | Self::PathProduct(..)
            | Self::Funext(..)
            | Self::Equiv(..)
            | Self::Univalence(..)
            | Self::Ua { .. }
            | Self::PathEquiv { .. }
            | Self::Transport(..)
            | Self::Variable { .. }
            | Self::Tuple(_)
            | Self::ListNil
            | Self::ListCons(..)
            | Self::ListFold { .. }
            | Self::ListCase { .. }
            | Self::Literal(_)
            | Self::Injection(..)
            | Self::Thunk(_)
            | Self::ValueLift { .. }
            | Self::Lambda(_)
            | Self::Application(..)
            | Self::Return(_)
            | Self::Bind(..)
            | Self::Force(_)
            | Self::Case { .. }
            | Self::Base(_)
            | Self::Product(_)
            | Self::Sum(_)
            | Self::List(_)
            | Self::KeptType { .. }
            | Self::ThunkType(_)
            | Self::Universe { .. }
            | Self::TypeLift { .. }
            | Self::Element { .. }
            | Self::Returner { .. }
            | Self::Arrow { .. }
            | Self::Pi { .. }
            | Self::Quote(_)
            | Self::QuoteComputation(_)
            | Self::StaticLambda(_)
            | Self::StaticApplication(..)
            | Self::StaticPi { .. }
            | Self::Sigma { .. }
            | Self::ComputationElement { .. }
            | Self::Unresolved(_)
            | Self::Hole(_)
            | Self::ValueMark { .. }
            | Self::ComputationHole(_)
            | Self::ComputationMark { .. }
            | Self::Fixpoint { .. }
            | Self::UnknownType
            | Self::BufferType
            | Self::UnknownComputationType => Maybe::Absent(referencing::Absent::NotAReference),
        }
    }

    /// The variable occurrence the node names itself, beside its zone: a
    /// variable's index, a session action's endpoint, an access's slot, a
    /// resume's or an abort's view.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the zone and index of a variable; the linear endpoint of a
    ///   send, receive, select, offer or close; the linear slot of an access
    ///   and the linear view of a resume or abort; `Unnamed` for every other
    ///   former, a fork and a hold included.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every occurrence-bearing former under binders of both
    ///   zones is projected back from its compact form to its original index; a
    ///   missed occurrence keeps a stale index.
    /// - witness: `content::tests::covers_preserve_every_binding_former`
    #[spec(ensures: |ret| match ret {
        Maybe::Present((zone, index)) => matches!(*self, Self::Variable { zone: own, index: named } if own == zone && named == index)
            || matches!(*self, Self::Session(ref action) if zone == Zone::Linear && action.endpoint() == Maybe::Present(index))
            || matches!(*self, Self::Memory(ref form) if zone == Zone::Linear && form.resident() == Maybe::Present(index)),
        Maybe::Absent(occurring::Absent::Unnamed) => !matches!(*self, Self::Variable { .. })
            && !matches!(*self, Self::Session(ref action) if matches!(action.endpoint(), Maybe::Present(_)))
            && !matches!(*self, Self::Memory(ref form) if matches!(form.resident(), Maybe::Present(_))),
    })]
    pub(crate) fn occurrence(&self) -> Maybe<(Zone, DeBruijnIndex), occurring::Absent>
    {
        if let Self::Variable { zone, index } = *self {
            return Maybe::Present((zone, index));
        }
        if let Self::Session(ref action) = *self
            && let Maybe::Present(endpoint) = action.endpoint()
        {
            return Maybe::Present((Zone::Linear, endpoint));
        }
        if let Self::Memory(ref form) = *self
            && let Maybe::Present(slot) = form.resident()
        {
            return Maybe::Present((Zone::Linear, slot));
        }
        Maybe::Absent(occurring::Absent::Unnamed)
    }

    /// The node with the occurrence it names itself replaced by `index`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the node, its former, children and every other payload
    ///   unchanged, its own occurrence — as [`ContentNode::occurrence`] reads
    ///   it — now `index`; a node naming none is returned unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ContentNode::occurrence`]: the compact form of
    ///   every occurrence-bearing former carries its rank, and its projection
    ///   its ambient index.
    /// - witness: `content::tests::covers_preserve_every_binding_former`
    #[spec(
        captures: [named = self.occurrence()],
        ensures: |ret| match named {
            Maybe::Present((zone, _)) => ret.occurrence() == Maybe::Present((zone, index)),
            Maybe::Absent(_) => ret.occurrence() == named,
        },
    )]
    pub(crate) fn relocated(
        mut self,
        index: DeBruijnIndex,
    ) -> Self
    {
        if let Self::Variable {
            index: ref mut held,
            ..
        } = self
        {
            *held = index;
        }
        else if let Self::Session(ref mut action) = self {
            match *action {
                SessionAction::Send {
                    ref mut endpoint, ..
                }
                | SessionAction::Receive {
                    ref mut endpoint, ..
                }
                | SessionAction::Select {
                    ref mut endpoint, ..
                }
                | SessionAction::Offer {
                    ref mut endpoint, ..
                }
                | SessionAction::Close { ref mut endpoint } => *endpoint = index,
                SessionAction::Fork { .. } | SessionAction::Place { .. } => {},
            }
        }
        else if let Self::Memory(ref mut form) = self {
            match *form {
                MemoryForm::Access { ref mut held, .. }
                | MemoryForm::Resume {
                    view: ref mut held, ..
                }
                | MemoryForm::Abort { view: ref mut held }
                | MemoryForm::Consume { ref mut held } => *held = index,
                MemoryForm::Hold { .. } => {},
            }
        }
        self
    }
}

/// Where an arena node sits in the table of the item that reached it.
///
/// # Specification
/// - executable: none — the map alone cannot establish which arena and walk
///   produced its entries.
///
/// # Adequacy
/// - hypothesis: L2 — the projection witness separates all four node families
///   and an unreached identifier in the same arena.
/// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Sites(BTreeMap<ArenaNode, NodeIndex>);

impl Sites
{
    /// The table index of `node`, when the item's walk reached it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the recorded index exactly, or Unreached if absent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — projection checks all four node families and an
    ///   unreached identifier in the same arena.
    /// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
    #[spec(ensures: |ret| match self.0.get(&node) {
        Some(&index) => ret == Maybe::Present(index),
        None => ret == Maybe::Absent(site::Absent::Unreached),
    })]
    pub(crate) fn of(
        &self,
        node: ArenaNode,
    ) -> Maybe<NodeIndex, site::Absent>
    {
        match self.0.get(&node) {
            Some(&index) => Maybe::Present(index),
            None => Maybe::Absent(site::Absent::Unreached),
        }
    }
}

/// Whether a table holds an id another arena minted.
///
/// # Specification
/// - executable: none — the tag contains no table; each [`SupportedNode`]
///   carries the tag of its subterm, and [`ItemContent::opacity`] reads it off
///   the roots.
///
/// # Adequacy
/// - hypothesis: L2 — a foreign unresolved value makes content opaque; the
///   supported persistence corpus supplies resolving tables.
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Opacity
{
    /// Every node resolved.
    Transparent,
    /// Some node did not resolve; the item is never adopted or persisted.
    Opaque,
}

/// Whether an item belongs to a located program: one that declares a world,
/// or an item that states an entry.
///
/// A located judgement reads the world register and the home of every
/// constant it names, and a home reaches a reader through a term position no
/// footprint keeps as type support. The cache has no vocabulary for that, so
/// every item of a located program is opaque: judged each time, never
/// persisted. **Reversal.** A home recorded in the support a reader consults,
/// once an editor session over located code measures the recheck.
///
/// # Specification
/// - executable: none — the tag holds no program; `Program::new` decides it.
///
/// # Adequacy
/// - hypothesis: L3 — an item of a program declaring a world is opaque and
///   refused persistence by name, while the same item alone is transparent.
/// - witness: `content::tests::an_item_of_a_located_program_is_opaque`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Locus
{
    /// No world is declared and no entry stated.
    #[default]
    Unlocated,
    /// The program declares a world, or the item states an entry.
    Located,
}

/// The roots of a nominal declaration in a discovery-numbered table, and the
/// rules presenting its terms, which name constructors by tag and no node.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DataRoots
{
    /// Parameter classifiers in telescope order.
    pub parameters: Vec<NodeIndex>,
    /// Index classifiers in telescope order; none for a parameterised type.
    pub indices: Vec<NodeIndex>,
    /// Constructor field classifiers in constructor and field order.
    pub constructors: Vec<Vec<NodeIndex>>,
    /// Each constructor's stated indices; none for a parameterised type.
    pub results: Vec<Vec<NodeIndex>>,
    /// The universe classifying the declared datatype.
    pub kind: NodeIndex,
    /// The rules rewriting the datatype's constructor terms; none for a free
    /// type.
    pub presentation: gandr_core_term::Presentation,
}

impl DataRoots
{
    /// All roots in their canonical discovery order.
    ///
    /// # Specification
    /// - ensures: parameters, then indices, then constructor fields, then
    ///   stated indices, then the kind.
    /// - executable: none — the return is an opaque iterator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — native checkpoint round trips preserve each signature
    ///   slot; a signature whose fields are open keeps one support per root.
    /// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
    /// - witness: `content::tests::open_roots_project_under_their_own_supports`
    pub(crate) fn iter(&self) -> impl Iterator<Item = NodeIndex> + Clone + '_
    {
        self.parameters
            .iter()
            .chain(&self.indices)
            .chain(self.constructors.iter().flatten())
            .chain(self.results.iter().flatten())
            .copied()
            .chain(core::iter::once(self.kind))
    }

    /// All roots in their canonical discovery order, each with the sort its
    /// node must have.
    ///
    /// # Specification
    /// - ensures: [`Self::iter`]'s roots in its order, a stated index a value
    ///   and every other root a value type.
    /// - executable: none — the return is an opaque iterator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a vector's stated lengths are values beside its
    ///   classifiers, and its checkpoint round-trips.
    /// - witness: `codec::tests::an_indexed_family_round_trips_its_indices`
    pub(crate) fn sorted(&self) -> impl Iterator<Item = (NodeIndex, Sort)> + Clone + '_
    {
        let classifiers = self
            .parameters
            .iter()
            .chain(&self.indices)
            .chain(self.constructors.iter().flatten())
            .map(|&root| (root, Sort::ValueType));
        let stated = self
            .results
            .iter()
            .flatten()
            .map(|&root| (root, Sort::Value));
        classifiers
            .chain(stated)
            .chain(core::iter::once((self.kind, Sort::ValueType)))
    }
}

/// One node of an operation rule's side as content: every position it names
/// resolved to the item that takes it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum RuleRoot
{
    /// An operation, by the item that defines it, at its arity.
    Operation
    {
        /// The item defining the operation; the ruled item's own reference
        /// for a recursive call.
        callee: Reference,
        /// How many arguments follow.
        arity: gandr_kernel_term::FieldCount,
    },
    /// A constructor, by its family's item and its tag.
    Constructor
    {
        /// The item declaring the family.
        family: Reference,
        /// The constructor's tag.
        tag: gandr_kernel_term::ConstructorTag,
    },
    /// A many-output operation's results, by their count.
    Results(gandr_kernel_term::FieldCount),
    /// A pattern variable.
    Variable(gandr_kernel_term::RuleVariable),
}

/// One operation rule as content: its two sides in pre-order.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct RuleRoots
{
    /// The left side.
    pub left: Vec<RuleRoot>,
    /// The right side.
    pub right: Vec<RuleRoot>,
}

/// An operation's rules as content, every position resolved through `layout`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one [`RuleRoots`] per rule in written order, each node as written
///   but its positions, each read as [`Layout::resolve`] reads it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a ruled item's rules are content, so two items differing
///   only in a rule differ in identity.
/// - witness: `content::tests::an_operation_rule_is_content`
#[spec(ensures: |ret| ret.len() == rules.rules().len())]
fn rule_roots(
    layout: &Layout,
    rules: &gandr_kernel_term::OperationRules,
) -> Vec<RuleRoots>
{
    use gandr_kernel_term::OperationNode;
    let side = |nodes: &[OperationNode]| {
        nodes
            .iter()
            .map(|&node| match node {
                OperationNode::Operation { constant, arity } => RuleRoot::Operation {
                    callee: layout.resolve(constant),
                    arity,
                },
                OperationNode::Constructor { family, tag } => RuleRoot::Constructor {
                    family: layout.resolve(family),
                    tag,
                },
                OperationNode::Results(count) => RuleRoot::Results(count),
                OperationNode::Variable(variable) => RuleRoot::Variable(variable),
            })
            .collect()
    };
    rules
        .rules()
        .iter()
        .map(|rule| RuleRoots {
            left: side(rule.left()),
            right: side(rule.right()),
        })
        .collect()
}

/// The declaration's roots; nominal declarations are not value axioms.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum DeclarationRoots
{
    /// A value declaration's optional signature and body, the laws a fold
    /// rests on, the rules of the operation it lowered from, the stage
    /// binders it is quantified over and the stages its calls supply.
    Value
    {
        /// The signature classifier, or why it is absent.
        signature: Maybe<NodeIndex, signature::Absent>,
        /// The body, or why it is absent.
        body: Maybe<NodeIndex, body::Absent>,
        /// The items whose laws the declaration's folds rest on, in its folded
        /// type's rule order; empty for a declaration that names none. A law
        /// is evidence, not content the body reaches, so it is no node.
        laws: Vec<Reference>,
        /// The rules of the operation the declaration lowered from, in
        /// written order; empty for every other declaration. The kernel
        /// decides them, so a changed rule is changed content.
        rules: Vec<RuleRoots>,
        /// The bound of each stage binder the declaration is quantified over,
        /// in binder order; empty for every other declaration. The signature
        /// names each binder by ordinal, so a changed bound is changed
        /// content.
        stages: Vec<gandr_kernel_term::StageBound>,
        /// Each stage a call of the body supplies its callee's binder at,
        /// `f[i = j]`, at the node of the value the call forces; empty for a
        /// declaration whose calls supply none. The checker holds a call to
        /// it, so a changed supply is changed content.
        supplies: Vec<(
            NodeIndex,
            gandr_kernel_term::StageBinder,
            gandr_kernel_term::Stage,
        )>,
    },
    /// A complete nominal signature.
    Data(DataRoots),
    /// A sealed abstract type.
    Abstract(AbstractRoots),
    /// A world declaration: no roots. Its program is located, so its item is
    /// opaque.
    World,
    /// A codata declaration: no roots. A codata signature has no content
    /// form, so its item is opaque.
    Codata,
}

/// The roots of a sealed abstract type, with the reach of its seal, the site
/// that mints its atom, the mobility its signature marks and the interface its
/// elements are related by.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct AbstractRoots
{
    /// The universe classifying the atom.
    pub kind: NodeIndex,
    /// The type the atom is sealed over.
    pub representation: NodeIndex,
    /// How many declarations after the abstract type its seal reaches.
    pub extent: gandr_kernel_term::SealExtent,
    /// The site that mints the atom.
    pub site: gandr_core_checker::SealSite,
    /// Whether its signature marks it mobile: sealing checks the mark against
    /// the representation.
    pub mobility: gandr_core_checker::worlds::Mobility,
    /// The roots of the interface its elements are related by, when stated.
    pub interface: Maybe<InterfaceRoots, gandr_core_checker::interface::Absent>,
}

/// The roots of a sealed atom's interface: its relation, the relation's
/// reflexivity and, when stated, its law.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct InterfaceRoots
{
    /// The relation between two elements.
    pub relation: NodeIndex,
    /// The relation's reflexivity.
    pub reflexivity: NodeIndex,
    /// The singleton's contraction onto its centre, when stated.
    pub law: Maybe<NodeIndex, gandr_core_checker::law::Absent>,
}

impl DeclarationRoots
{
    /// Each root and its required family, in discovery order.
    ///
    /// # Specification
    /// - ensures: value signature before body, all nominal roots in order as
    ///   [`DataRoots::sorted`] sorts them, an abstract type's kind before its
    ///   representation and both before its interface's relation, reflexivity
    ///   and law, or none for a world or a codata declaration.
    /// - executable: none — the return is an opaque iterator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — persistence rejects ill-sorted and reordered native
    ///   roots.
    /// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
    pub(crate) fn iter(&self) -> impl Iterator<Item = (NodeIndex, Sort)> + Clone + '_
    {
        let (values, data) = match *(self) {
            Self::Value {
                ref signature,
                ref body,
                ..
            } => (
                [
                    match *signature {
                        Maybe::Present(root) => Some((root, Sort::ValueType)),
                        Maybe::Absent(_) => None,
                    },
                    match *body {
                        Maybe::Present(root) => Some((root, Sort::Value)),
                        Maybe::Absent(_) => None,
                    },
                    None,
                    None,
                    None,
                ],
                None,
            ),
            Self::Data(ref roots) => ([None; 5], Some(roots)),
            Self::World | Self::Codata => ([None; 5], None),
            Self::Abstract(roots) => {
                let (relation, reflexivity, law) = match roots.interface {
                    Maybe::Present(interface) => (
                        Some((interface.relation, Sort::Value)),
                        Some((interface.reflexivity, Sort::Value)),
                        match interface.law {
                            Maybe::Present(law) => Some((law, Sort::Value)),
                            Maybe::Absent(_) => None,
                        },
                    ),
                    Maybe::Absent(_) => (None, None, None),
                };
                (
                    [
                        Some((roots.kind, Sort::ValueType)),
                        Some((roots.representation, Sort::ValueType)),
                        relation,
                        reflexivity,
                        law,
                    ],
                    None,
                )
            },
        };
        values
            .into_iter()
            .flatten()
            .chain(data.into_iter().flat_map(DataRoots::sorted))
    }

    /// The roots with every root index replaced by its image under `image`,
    /// every other field unchanged.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same category, laws and payloads; each root, in
    ///   [`DeclarationRoots::iter`] order, replaced by its image.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — native checkpoints round-trip every root slot of a
    ///   value, a data and an abstract declaration through renumbering, an
    ///   abstract one's interface roots among them; roots that move under
    ///   renumbering still name their own nodes.
    /// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
    /// - witness: `tests::native_formers::an_atom_interface_persists_and_an_edit_to_it_reaches_every_reader`
    /// - witness: `content::tests::open_roots_project_under_their_own_supports`
    /// - witness: `content::tests::an_abstract_type_s_interface_roots_are_renumbered_with_it`
    #[spec(ensures: |ret| ret.iter().map(|(_, sort)| sort).eq(self.iter().map(|(_, sort)| sort))
        && ret.iter().map(|(root, _)| root).eq(self.iter().map(|(root, _)| image(root))))]
    pub(crate) fn renumbered<Image>(
        &self,
        image: Image,
    ) -> Self
    where
        Image: Fn(NodeIndex) -> NodeIndex,
    {
        match *self {
            Self::Value {
                ref signature,
                ref body,
                ref laws,
                ref rules,
                ref stages,
                ref supplies,
            } => Self::Value {
                signature: signature.map(&image),
                body: body.map(&image),
                laws: laws.clone(),
                rules: rules.clone(),
                stages: stages.clone(),
                supplies: supplies
                    .iter()
                    .map(|&(head, binder, stage)| (image(head), binder, stage))
                    .collect(),
            },
            Self::Data(ref roots) => Self::Data(roots.renumbered(&image)),
            Self::Abstract(roots) => Self::Abstract(AbstractRoots {
                kind: image(roots.kind),
                representation: image(roots.representation),
                interface: roots.interface.map(|interface| InterfaceRoots {
                    relation: image(interface.relation),
                    reflexivity: image(interface.reflexivity),
                    law: interface.law.map(&image),
                }),
                ..roots
            }),
            Self::World => Self::World,
            Self::Codata => Self::Codata,
        }
    }
}

impl DataRoots
{
    /// The roots with every index replaced by its image under `image`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same shape and presentation, each root replaced by its
    ///   image in [`DataRoots::iter`] order; the predicate checks the kind's
    ///   image and the shape's widths, and the witness the per-root images,
    ///   since comparing them walks every root.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`DeclarationRoots::renumbered`].
    /// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
    #[spec(ensures: |ret| ret.kind == image(self.kind)
        && ret.parameters.len() == self.parameters.len()
        && ret.constructors.len() == self.constructors.len()
        && ret.presentation == self.presentation)]
    pub(crate) fn renumbered<Image>(
        &self,
        image: Image,
    ) -> Self
    where
        Image: Fn(NodeIndex) -> NodeIndex,
    {
        let rows = |rows: &[Vec<NodeIndex>]| {
            rows.iter()
                .map(|row| row.iter().map(|&root| image(root)).collect())
                .collect()
        };
        Self {
            parameters: self.parameters.iter().map(|&root| image(root)).collect(),
            indices: self.indices.iter().map(|&root| image(root)).collect(),
            constructors: rows(&self.constructors),
            results: rows(&self.results),
            kind: image(self.kind),
            presentation: self.presentation.clone(),
        }
    }
}

/// A de Bruijn table factored into supported nodes and numbered from its
/// roots.
///
/// # Specification
/// - executable: none — a data declaration; [`tabled`] establishes it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`tabled`].
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
pub struct Tabled
{
    /// The supported nodes, numbered by discovery from the roots.
    pub nodes: Vec<SupportedNode>,
    /// Where each de Bruijn entry landed in the factored table.
    placed: Vec<crate::support::Placement>,
    /// The number each factored node took.
    numbers: Vec<Option<NodeIndex>>,
}

impl Tabled
{
    /// The supported node the de Bruijn entry `raw` became.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn of(
        &self,
        raw: NodeIndex,
    ) -> NodeIndex
    {
        self.placed.get(usize::from(raw)).map_or(raw, |placed| {
            self.numbers
                .get(usize::from(placed.node))
                .copied()
                .flatten()
                .unwrap_or(placed.node)
        })
    }

    /// The support of the de Bruijn entry `raw` in its ambient scope.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn support(
        &self,
        raw: NodeIndex,
    ) -> Thinning
    {
        self.placed
            .get(usize::from(raw))
            .map_or_else(Thinning::empty, |placed| placed.support.clone())
    }

    /// The supports of the de Bruijn entries `roots`, in order.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn supports(
        &self,
        roots: &[NodeIndex],
    ) -> Vec<Thinning>
    {
        roots.iter().map(|&root| self.support(root)).collect()
    }
}

/// Factor the de Bruijn table `raw` and number it from `roots`.
///
/// # Specification
/// - requires: every root is an entry of `raw`, as the encoder hands them out.
/// - ensures: the supported table of every node reachable from the roots,
///   numbered breadth-first from them in order; the numbered image and the
///   support of every entry.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an item's signature renumbered from its table equals its
///   type encoded alone; a shared subterm is one node.
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
/// - witness: `content::tests::a_shared_node_is_listed_once`
#[spec(ensures: |ret| ret.placed.len() == raw.len())]
pub fn tabled(
    raw: &[ContentNode],
    roots: &[NodeIndex],
) -> Tabled
{
    let factored = crate::support::factor(raw);
    let placed = factored.placements;
    let mut owned: Vec<Option<SupportedNode>> = factored.nodes.into_iter().map(Some).collect();
    let numbered = crate::support::number(
        NodeIndex::from(owned.len()),
        roots.iter().map(|&root| {
            placed
                .get(usize::from(root))
                .map_or(root, |placement| placement.node)
        }),
        |old| owned.get_mut(usize::from(old)).and_then(Option::take),
    );
    Tabled {
        nodes: numbered.nodes,
        placed,
        numbers: numbered.numbers,
    }
}

/// A complete nominal signature in arena-independent coordinates.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DataContent
{
    /// The parameter, constructor and kind roots.
    roots: DataRoots,
    /// The complete shared table of reachable nodes.
    nodes: Vec<SupportedNode>,
    /// Each root's support in its ambient scope, in [`DataRoots::iter`]
    /// order.
    placements: Vec<Thinning>,
}

impl DataContent
{
    /// Signature roots in this table.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn roots(&self) -> &DataRoots
    {
        &self.roots
    }

    /// The discovery-numbered shared table.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn nodes(&self) -> &[SupportedNode]
    {
        &self.nodes
    }

    /// Each root's support in its ambient scope, in [`DataRoots::iter`]
    /// order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn placements(&self) -> &[Thinning]
    {
        &self.placements
    }

    /// Every reference beneath a root, ascending and once each.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the union of every root's value and type reads.
    /// - executable: none — the return is an opaque iterator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a data answer whose constructor names a changed
    ///   definition invalidates its reader.
    /// - witness: `checkpoint::tests::recorded_answer_references_participate_in_value_invalidation`
    pub(crate) fn reads(&self) -> alloc::collections::BTreeSet<&Reference>
    {
        self.roots
            .iter()
            .filter_map(|root| self.nodes.get(usize::from(root)))
            .flat_map(|node| node.value_reads().chain(node.type_reads()))
            .collect()
    }

    /// Reassemble decoded parts, which the reader validated.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn from_parts(
        roots: DataRoots,
        nodes: Vec<SupportedNode>,
        placements: Vec<Thinning>,
    ) -> Self
    {
        Self {
            roots,
            nodes,
            placements,
        }
    }

    /// Encode every constructor signature, not merely its universe kind.
    ///
    /// # Specification
    /// - requires: nothing; unresolved nodes retain their sort.
    /// - ensures: every signature root is represented in the canonical shared
    ///   table, with its support.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — changing a constructor while preserving its kind
    ///   invalidates reuse.
    /// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
    #[spec(ensures: |ret| ret.roots.parameters.len() == signature.parameters().len()
        && ret.roots.constructors.iter().map(Vec::len).eq(signature.constructors().iter().map(Vec::len))
        && ret.roots.iter().all(|root| usize::from(root) < ret.nodes.len())
        && ret.placements.len() == ret.roots.iter().count())]
    pub(crate) fn of(
        arena: &CoreArena,
        layout: &Layout,
        signature: &gandr_core_term::DataSignature,
    ) -> Self
    {
        let mut encoder = Encoder::new(arena, layout);
        let roots = encoder.data_roots(signature);
        encoder.drain();
        Self::tabulated(&roots, &encoder.nodes)
    }

    /// The signature whose roots `roots` index the de Bruijn table `raw`,
    /// factored and numbered from those roots.
    ///
    /// # Specification
    /// - requires: every root is an entry of `raw`.
    /// - ensures: the roots renumbered into the supported table of every node
    ///   reachable from them, with one support per root.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`DataContent::of`], which builds through it.
    /// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
    #[spec(ensures: |ret| ret.placements.len() == ret.roots.iter().count())]
    pub(crate) fn tabulated(
        roots: &DataRoots,
        raw: &[ContentNode],
    ) -> Self
    {
        let raw_roots: Vec<NodeIndex> = roots.iter().collect();
        let tabled = tabled(raw, &raw_roots);
        Self {
            roots: roots.renumbered(|raw| tabled.of(raw)),
            placements: tabled.supports(&raw_roots),
            nodes: tabled.nodes,
        }
    }
}

/// An item's canonical declaration roots and one shared node table.
///
/// # Specification
/// - executable: none — stored roots and entries do not retain an arena; raw
///   reconstruction is not validation.
///
/// # Adequacy
/// - hypothesis: L3 — noisy arenas, sharing, unresolved identifiers and
///   signature extraction bound the encoding evidence; arbitrary raw tables are
///   not certified by this representation.
/// - witness: `content::tests::content_is_free_of_arena_ids`
/// - witness: `content::tests::a_shared_node_is_listed_once`
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ItemContent
{
    /// The item's own reference: its key and occurrence.
    reference: Reference,
    /// The value or nominal declaration's roots.
    declaration: DeclarationRoots,
    /// Every node reachable from the roots, numbered by discovery.
    nodes: Vec<SupportedNode>,
    /// Each root's support in the item's empty scope, in
    /// [`DeclarationRoots::iter`] order: empty for a closed root.
    placements: Vec<Thinning>,
    /// Whether the item belongs to a located program.
    locus: Locus,
}

impl ItemContent
{
    /// The item's own reference.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reference(&self) -> &Reference
    {
        &self.reference
    }

    /// The declaration's roots, retaining its value or nominal category.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn declaration(&self) -> &DeclarationRoots
    {
        &self.declaration
    }

    /// Every node reachable from the roots, numbered by discovery.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[SupportedNode]
    {
        &self.nodes
    }

    /// Each root's support in the item's empty scope, in
    /// [`DeclarationRoots::iter`] order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn placements(&self) -> &[Thinning]
    {
        &self.placements
    }

    /// The de Bruijn table of the node `root`, the root first, placed by the
    /// support of the first declaration root naming it: the projection a
    /// printer reads a signature or a kind from.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as `support::expand` from `root` under its root support; a
    ///   node no root names is placed under the empty support.
    /// - fails: [`PlacementError::OutOfScope`] for a node with free indices
    ///   that no root names; [`PlacementError::IndexOverflow`] when a binder
    ///   raises an index past `u32`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlacementError`]: as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a signature projects to the table of its type encoded
    ///   alone; every binding former of both zones projects back to its
    ///   indices; each open root projects under its own support.
    /// - witness: `content::tests::covers_preserve_every_binding_former`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    /// - witness: `content::tests::open_roots_project_under_their_own_supports`
    #[spec(ensures: |ret| ret.as_ref().is_err() || self.nodes.get(usize::from(root)).is_none_or(|node|
        ret.as_ref().is_ok_and(|table| table.first().map(ContentNode::sort) == Some(node.sort()))))]
    #[inline]
    pub fn debruijn(
        &self,
        root: NodeIndex,
    ) -> Result<Vec<ContentNode>, PlacementError>
    {
        let empty = Thinning::empty();
        let placement = self
            .declaration
            .iter()
            .zip(&self.placements)
            .find_map(|((named, _), placement)| (named == root).then_some(placement))
            .unwrap_or(&empty);
        crate::support::expand(&self.nodes, root, placement)
    }

    /// Whether the item belongs to a located program.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn locus(&self) -> Locus
    {
        self.locus
    }

    /// The content of these parts, as the decoder reassembles it: content a
    /// decoder reads was persisted, so it is unlocated.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn from_parts(
        reference: Reference,
        declaration: DeclarationRoots,
        nodes: Vec<SupportedNode>,
        placements: Vec<Thinning>,
    ) -> Self
    {
        Self {
            reference,
            declaration,
            nodes,
            placements,
            locus: Locus::Unlocated,
        }
    }

    /// Whether the item may be adopted and persisted: every node resolved, in
    /// an unlocated program, and no codata declaration.
    ///
    /// # Specification
    /// - ensures: [`Opacity::Opaque`] for a located item and for a codata
    ///   declaration, else opaque exactly when a root carries an unresolved
    ///   node beneath it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Locus`], and an unresolved id beneath the body
    ///   makes its item opaque.
    /// - witness: `content::tests::an_item_of_a_located_program_is_opaque`
    /// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
    #[spec(ensures: |ret| (ret == Opacity::Opaque
            || (self.locus == Locus::Unlocated && !matches!(self.declaration, DeclarationRoots::Codata)))
        && (self.locus == Locus::Located || matches!(self.declaration, DeclarationRoots::Codata) || (ret == Opacity::Opaque) == self.declaration.iter().any(|(root, _)|
            self.nodes.get(usize::from(root)).is_some_and(|node| node.opacity() == Opacity::Opaque))))]
    #[inline]
    #[must_use]
    pub fn opacity(&self) -> Opacity
    {
        let opaque = match self.locus {
            Locus::Located => true,
            Locus::Unlocated if matches!(self.declaration, DeclarationRoots::Codata) => true,
            Locus::Unlocated => self.declaration.iter().any(|(root, _)| {
                self.nodes
                    .get(usize::from(root))
                    .is_some_and(|node| node.opacity() == Opacity::Opaque)
            }),
        };
        if opaque {
            Opacity::Opaque
        }
        else {
            Opacity::Transparent
        }
    }

    /// The signature's type, as a type table of its own.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the table of every node reachable from the signature root,
    ///   renumbered by discovery from that root alone, with the root's support,
    ///   so it equals the content [`TypeContent::of_value_type`] gives the
    ///   signature in its arena.
    /// - provides: None for an unsigned value or a nominal declaration.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an interleaved signature is compared with
    ///   independently encoding its root.
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[spec(ensures: |ret| match (&self.declaration, ret.as_ref()) {
        (&DeclarationRoots::Value { signature: Maybe::Present(root), .. }, Some(content)) =>
            content.nodes.first().map(SupportedNode::sort) == self.nodes.get(usize::from(root)).map(SupportedNode::sort),
        (&DeclarationRoots::Value { signature: Maybe::Present(_), .. }, None) => false,
        (&(DeclarationRoots::Value { signature: Maybe::Absent(_), .. } | DeclarationRoots::Data(_) | DeclarationRoots::Abstract(_) | DeclarationRoots::World | DeclarationRoots::Codata), found) => found.is_none(),
    })]
    pub(crate) fn signature_type(&self) -> Option<TypeContent>
    {
        match self.declaration {
            DeclarationRoots::Value {
                signature: Maybe::Present(root),
                ..
            } => {
                let numbered =
                    crate::support::number(NodeIndex::from(self.nodes.len()), [root], |old| {
                        self.nodes.get(usize::from(old)).cloned()
                    });
                Some(TypeContent {
                    nodes: numbered.nodes,
                    root: self.placements.first().cloned().unwrap_or_default(),
                })
            },
            DeclarationRoots::Value {
                signature: Maybe::Absent(_),
                ..
            }
            | DeclarationRoots::Data(_)
            | DeclarationRoots::Abstract(_)
            | DeclarationRoots::World
            | DeclarationRoots::Codata => None,
        }
    }
}

/// A type's canonical content: every node reachable from it, numbered by
/// discovery, the type itself first, and the type's support in the scope it
/// stands in.
///
/// # Specification
/// - executable: none — a data declaration; [`TypeContent::of`] and the reader
///   establish that the table is supported and the root support has the root's
///   widths.
///
/// # Adequacy
/// - hypothesis: L3 — independent type encoding and minting preserve a shared
///   arrow; a finite malformed corpus separates the named mint refusals.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TypeContent
{
    /// The nodes; the root is the first.
    nodes: Vec<SupportedNode>,
    /// The root's support in the scope the type stands in.
    root: Thinning,
}

impl TypeContent
{
    /// The nodes; the root is the first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[SupportedNode]
    {
        &self.nodes
    }

    /// The root's support in the scope the type stands in: the de Bruijn
    /// indices it reads there.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> &Thinning
    {
        &self.root
    }

    /// The type's de Bruijn table, the root first: the projection a reader
    /// that prints ambient binders reads.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as `support::expand` from the first node under the root's
    ///   support; an empty table projects to no node.
    /// - fails: [`PlacementError::IndexOverflow`] when an ambient index under a
    ///   binder passes `u32`; [`PlacementError::OutOfScope`] for a support
    ///   narrower than its node.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlacementError`]: as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every binding former of both zones projects back to
    ///   its indices, and a root support at the index ceiling under a binder
    ///   reports overflow.
    /// - witness: `content::tests::covers_preserve_every_binding_former`
    /// - witness: `content::tests::debruijn_projection_reports_index_overflow`
    #[spec(ensures: |ret| self.nodes.is_empty() || ret.as_ref().is_err() || ret.as_ref().is_ok_and(|table|
        table.first().map(ContentNode::sort) == self.nodes.first().map(SupportedNode::sort)))]
    #[inline]
    pub fn debruijn(&self) -> Result<Vec<ContentNode>, PlacementError>
    {
        if self.nodes.is_empty() {
            return Ok(Vec::new());
        }
        crate::support::expand(&self.nodes, NodeIndex::from(0_usize), &self.root)
    }

    /// Every reference beneath the type, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the root's value and type reads; nothing for an empty table.
    /// - executable: none — the return is an opaque iterator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recorded answer naming a changed definition in a
    ///   type position, an abstract type or a code invalidates its reader.
    /// - witness: `checkpoint::tests::recorded_answer_references_participate_in_value_invalidation`
    pub(crate) fn reads(&self) -> impl Iterator<Item = &Reference>
    {
        self.nodes
            .first()
            .into_iter()
            .flat_map(|root| root.value_reads().chain(root.type_reads()))
    }

    /// The content of these parts, as the decoder reassembles it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn from_parts(
        nodes: Vec<SupportedNode>,
        root: Thinning,
    ) -> Self
    {
        Self { nodes, root }
    }

    /// The content of the value type `ty` of `program`'s arena.
    ///
    /// # Specification
    /// - requires: nothing — an unresolved id is admissible and listed as
    ///   unresolved.
    /// - ensures: the table the item encoding gives the same node, renumbered
    ///   from it, so a type compares equal to itself across arenas.
    /// - provides: the comparison form of types: answers, verdicts and seats
    ///   are compared by it, never by arena id.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — allocation noise and a shared arrow separate arena
    ///   identity from content; the same signature is encoded through the item
    ///   path.
    /// - witness: `content::tests::a_type_minted_back_has_its_own_content`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[spec(ensures: |ret| match program.arena().value_type(ty) {
            | Some(_) => ret.nodes.first().is_some_and(|node| {
                node.sort() == Sort::ValueType && !matches!(*node.former(), ContentNode::Unresolved(_))
            }),
            | None => ret.nodes.first().map(SupportedNode::former) == Some(&ContentNode::Unresolved(Sort::ValueType)),
        })]
    #[inline]
    #[must_use]
    pub fn of_value_type(
        program: &Program,
        ty: ValueTypeId,
    ) -> Self
    {
        Self::of(program.arena(), program.layout(), ArenaNode::ValueType(ty))
    }

    /// The content of the node `root` of `arena`, constants resolved through
    /// `layout`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the discovery-numbered supported table of every node
    ///   reachable from `root`, `root` first, with its support.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent type extraction and shared-node minting
    ///   exercise a rooted value-type graph; other root families are not
    ///   claimed here.
    /// - witness: `content::tests::a_type_minted_back_has_its_own_content`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[spec(ensures: |ret| {
            ret.nodes.first().is_some_and(|node| {
                node.sort()
                    == match root {
                        | ArenaNode::Value(_) => Sort::Value,
                        | ArenaNode::Computation(_) => Sort::Computation,
                        | ArenaNode::ValueType(_) => Sort::ValueType,
                        | ArenaNode::CompType(_) => Sort::CompType,
                    }
            }) && ret.nodes.iter().all(|node| {
                node.former().children()
                    .iter()
                    .all(|(child, _)| usize::from(child) < ret.nodes.len())
            })
        })]
    pub(crate) fn of(
        arena: &CoreArena,
        layout: &Layout,
        root: ArenaNode,
    ) -> Self
    {
        let mut encoder = Encoder::new(arena, layout);
        let raw = encoder.discover(root);
        encoder.drain();
        Self::tabulated(&encoder.nodes, raw)
    }

    /// The type rooted at `root` of the de Bruijn table `raw`, factored and
    /// numbered from it.
    ///
    /// # Specification
    /// - requires: `root` is an entry of `raw`.
    /// - ensures: the supported table of every node reachable from `root`,
    ///   `root` first, with its support in `raw`'s ambient scope.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TypeContent::of`], which builds through it; a
    ///   table read back through [`TypeContent::debruijn`] is the table
    ///   factored.
    /// - witness: `content::tests::covers_preserve_every_binding_former`
    #[spec(ensures: |ret| ret.nodes.iter().all(|node| node.former().children()
        .iter()
        .all(|(child, _)| usize::from(child) < ret.nodes.len())))]
    pub(crate) fn tabulated(
        raw: &[ContentNode],
        root: NodeIndex,
    ) -> Self
    {
        let tabled = tabled(raw, &[root]);
        Self {
            root: tabled.support(root),
            nodes: tabled.nodes,
        }
    }

    /// Mint the type into `arena`, constants placed through `layout`.
    ///
    /// A table whose every node is closed is already its own de Bruijn
    /// table: each node is its former over the empty scope, and the
    /// projection would number and share it exactly as it stands. Only a
    /// table with an open node is projected first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success a value type of `arena` whose content is this
    ///   table, each distinct placed node minted once.
    /// - provides: the seat an adopted synthesised type is read from.
    /// - fails: `seating::Absent` naming why: an index the projection cannot
    ///   place, an unresolved node, a reference the program does not hold, a
    ///   table that is no value type, or a former holding a term. A
    ///   term-bearing inferred type is rechecked rather than adopted when it
    ///   cannot be seated.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shared arrow is minted back into a noisy arena; one
    ///   table for each refusal reason bounds error evidence, closed and open
    ///   alike. The predicate checks successful seat resolution, not a second
    ///   encoding.
    /// - witness: `content::tests::a_type_minted_back_has_its_own_content`
    /// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(id) => arena.value_type(id).is_some(),
        Maybe::Absent(_) => true,
    })]
    pub(crate) fn mint(
        &self,
        arena: &mut CoreArena,
        layout: &Layout,
    ) -> Maybe<ValueTypeId, seating::Absent>
    {
        let minted = if self
            .nodes
            .iter()
            .all(|node| node.scope() == gandr_core_term::support::Scope::default())
        {
            mint_table(&self.nodes, arena, layout)
        }
        else {
            let Ok(table) = self.debruijn()
            else {
                return Maybe::Absent(seating::Absent::Unplaceable);
            };
            mint_table(&table, arena, layout)
        };
        match minted {
            Maybe::Present(Minted::ValueType(id)) => Maybe::Present(id),
            Maybe::Present(Minted::CompType(_)) => Maybe::Absent(seating::Absent::IllSorted),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }
}

/// The type tables one judgement pass has encoded, by the arena type each
/// encodes. Within a pass the arena only grows and the program's layout is
/// fixed, so an arena type's table never changes: the pass encodes each type
/// it answers or projects once, however many items consult it.
///
/// # Specification
/// - executable: none — a cache; [`TypeMemo::content`] checks every answer
///   against a fresh encoding.
///
/// # Adequacy
/// - hypothesis: L2 — the incremental differential compares every judged item's
///   answers and typings with a from-scratch pass.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
#[repr(transparent)]
#[derive(Debug, Default)]
pub struct TypeMemo(core::cell::RefCell<BTreeMap<ArenaNode, TypeContent>>);

impl TypeMemo
{
    /// The table of the arena type `node`, encoded on its first request in
    /// the pass.
    ///
    /// # Specification
    /// - requires: since the memo's first entry, `arena` has only grown and
    ///   `layout` is the one every entry was encoded through.
    /// - ensures: the table [`TypeContent::of`] encodes for `node`.
    /// - panics: none; the memo is never borrowed across an encoding.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`TypeMemo`].
    /// - witness: `tests::incremental::incremental_equals_from_scratch`
    #[spec(ensures: |ret| ret == TypeContent::of(arena, layout, node))]
    pub(crate) fn content(
        &self,
        arena: &CoreArena,
        layout: &Layout,
        node: ArenaNode,
    ) -> TypeContent
    {
        if let Some(found) = self.0.borrow().get(&node) {
            return found.clone();
        }
        let content = TypeContent::of(arena, layout, node);
        let _replaced = self.0.borrow_mut().insert(node, content.clone());
        content
    }
}

/// An item's content beside where its arena nodes sit in it.
///
/// # Specification
/// - executable: none — the pair does not retain its source arena;
///   correspondence is established by `encode_item`.
///
/// # Adequacy
/// - hypothesis: L2 — item identity and the site projection are checked through
///   their actual consumers, not inferred from the pair alone.
/// - witness: `content::tests::content_is_free_of_arena_ids`
/// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
pub struct Encoded
{
    /// The content.
    pub content: ItemContent,
    /// The table index of every arena node the walk reached.
    pub sites: Sites,
}

/// The content of the item at `ordinal` of a program.
///
/// # Specification
/// - requires: nothing; an ordinal outside `layout` encodes an empty unsigned
///   hole under an unoccupied reference.
/// - ensures: the item's reference, complete declaration roots, the shared
///   supported table numbered by discovery from them and each root's support;
///   nominal roots follow parameter and constructor order; the program's locus.
///   Every arena node the walk reached has a site, the supported node it
///   became.
/// - provides: the item's identity, the sites its verdict is projected through,
///   and the roots its footprint is read from — one walk for all three.
/// - panics: none.
/// - intension: reads each reachable node once, factors each de Bruijn entry
///   once and allocates one table entry per distinct supported node.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the discovery order, the sharing and the
///   id-freedom, separated by two arenas building one item in different
///   allocation orders, a shared subterm listed once, a constant resolved to
///   its item's reference, and an unresolved id listed by sort.
/// - witness: `content::tests::content_is_free_of_arena_ids`
/// - witness: `content::tests::a_shared_node_is_listed_once`
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
#[spec(ensures: |ret| ret.sites.0.values().all(|index| usize::from(*index) < ret.content.nodes.len())
    && ret.content.placements.len() == ret.content.declaration.iter().count()
    && match layout.items.get(usize::from(ordinal)) {
        Some(item) => layout.references.get(usize::from(ordinal)) == Some(&ret.content.reference)
            && { let (matched_left_value, matched_right_value) = (item.declaration().content(),&ret.content.declaration);
if let gandr_core_checker::DeclarationContent::Value { ref signature,ref body } = *matched_left_value && let DeclarationRoots::Value { signature:ref actual_signature,body:ref actual_body,laws:ref actual_laws,rules:ref actual_rules,stages:ref actual_stages,supplies:ref actual_supplies } = *matched_right_value { signature.map(|ty| ret.sites.0.get(&ArenaNode::ValueType(ty)).copied()) == actual_signature.map(Some)
                    && body.map(|value| ret.sites.0.get(&ArenaNode::Value(value)).copied()) == actual_body.map(Some)
                    && item.declaration().laws().iter().map(|&law| layout.resolve(law)).eq(actual_laws.iter().cloned())
                    && *actual_rules == rule_roots(layout, item.declaration().operation_rules())
                    && actual_stages.as_slice() == item.declaration().stages()
                    && actual_supplies.iter().copied().eq(item.declaration().supplies().iter().filter_map(|supply| ret.sites.0.get(&ArenaNode::Value(supply.head)).map(|&head| (head, supply.binder, supply.stage)))) }
 else if let gandr_core_checker::DeclarationContent::Data(ref signature) = *matched_left_value && let DeclarationRoots::Data(ref roots) = *matched_right_value { ret.sites.0.get(&ArenaNode::ValueType(signature.kind())) == Some(&roots.kind)
                    && signature.parameters().iter().map(|&ty| ret.sites.0.get(&ArenaNode::ValueType(ty))).eq(roots.parameters.iter().map(Some))
                    && signature.constructors().len() == roots.constructors.len()
                    && signature.constructors().iter().zip(&roots.constructors).all(|(fields,roots)| fields.iter().map(|&ty| ret.sites.0.get(&ArenaNode::ValueType(ty))).eq(roots.iter().map(Some))) }
 else if let gandr_core_checker::DeclarationContent::Abstract(sealed) = *matched_left_value && let DeclarationRoots::Abstract(roots) = *matched_right_value { ret.sites.0.get(&ArenaNode::ValueType(sealed.kind())) == Some(&roots.kind)
                    && ret.sites.0.get(&ArenaNode::ValueType(sealed.representation())) == Some(&roots.representation)
                    && roots.extent == sealed.extent() && roots.site == sealed.site() && roots.mobility == sealed.mobility()
                    && match (sealed.interface(), roots.interface) {
                        (Maybe::Present(interface), Maybe::Present(actual)) => ret.sites.0.get(&ArenaNode::Value(interface.relation())) == Some(&actual.relation)
                            && ret.sites.0.get(&ArenaNode::Value(interface.reflexivity())) == Some(&actual.reflexivity)
                            && interface.law().map(|law| ret.sites.0.get(&ArenaNode::Value(law)).copied()) == actual.law.map(Some),
                        (Maybe::Absent(_), Maybe::Absent(_)) => true,
                        (Maybe::Present(_), Maybe::Absent(_)) | (Maybe::Absent(_), Maybe::Present(_)) => false,
                    } }
 else { matches!((matched_left_value, matched_right_value), (gandr_core_checker::DeclarationContent::World, DeclarationRoots::World) | (gandr_core_checker::DeclarationContent::Codata(_), DeclarationRoots::Codata)) }
} && ret.content.locus == layout.locus(),
        None => ret.content.reference == Reference::Unoccupied
            && matches!(ret.content.declaration,DeclarationRoots::Value {signature:Maybe::Absent(signature::Absent::Unsigned),body:Maybe::Absent(body::Absent::Hole),ref laws,ref rules,ref stages,ref supplies} if laws.is_empty() && rules.is_empty() && stages.is_empty() && supplies.is_empty())
            && ret.content.nodes.is_empty(),
    })]
pub fn encode_item(
    arena: &CoreArena,
    layout: &Layout,
    ordinal: crate::boundary::ItemOrdinal,
) -> Encoded
{
    let mut encoder = Encoder::new(arena, layout);
    let (reference, declaration) = layout.items.get(usize::from(ordinal)).map_or_else(
        || {
            (Reference::Unoccupied, DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Absent(body::Absent::Hole),
                laws: Vec::new(),
                rules: Vec::new(),
                stages: Vec::new(),
                supplies: Vec::new(),
            })
        },
        |item| {
            let declaration = match *(item.declaration().content()) {
                gandr_core_checker::DeclarationContent::Value {
                    ref signature,
                    ref body,
                } => DeclarationRoots::Value {
                    signature: signature.map(|ty| encoder.discover(ArenaNode::ValueType(ty))),
                    body: body.map(|term| encoder.discover(ArenaNode::Value(term))),
                    laws: item
                        .declaration()
                        .laws()
                        .iter()
                        .map(|&law| layout.resolve(law))
                        .collect(),
                    rules: rule_roots(layout, item.declaration().operation_rules()),
                    stages: item.declaration().stages().to_vec(),
                    supplies: Vec::new(),
                },
                gandr_core_checker::DeclarationContent::Data(ref signature) => {
                    DeclarationRoots::Data(encoder.data_roots(signature))
                },
                gandr_core_checker::DeclarationContent::Abstract(sealed) => {
                    DeclarationRoots::Abstract(AbstractRoots {
                        kind: encoder.discover(ArenaNode::ValueType(sealed.kind())),
                        representation: encoder
                            .discover(ArenaNode::ValueType(sealed.representation())),
                        extent: sealed.extent(),
                        site: sealed.site(),
                        mobility: sealed.mobility(),
                        interface: sealed.interface().map(|interface| InterfaceRoots {
                            relation: encoder.discover(ArenaNode::Value(interface.relation())),
                            reflexivity: encoder
                                .discover(ArenaNode::Value(interface.reflexivity())),
                            law: interface
                                .law()
                                .map(|law| encoder.discover(ArenaNode::Value(law))),
                        }),
                    })
                },
                gandr_core_checker::DeclarationContent::World => DeclarationRoots::World,
                gandr_core_checker::DeclarationContent::Codata(_) => DeclarationRoots::Codata,
            };
            let reference = layout
                .references
                .get(usize::from(ordinal))
                .cloned()
                .unwrap_or(Reference::Unoccupied);
            (reference, declaration)
        },
    );
    encoder.drain();
    // A supplied head is numbered by the body's walk, never as a root of its
    // own; a head the body no longer reaches supplies nothing.
    let mut declaration = declaration;
    if let DeclarationRoots::Value {
        ref mut supplies, ..
    } = declaration
        && let Some(item) = layout.items.get(usize::from(ordinal))
    {
        supplies.extend(item.declaration().supplies().iter().filter_map(|supply| {
            encoder
                .seen
                .get(&ArenaNode::Value(supply.head))
                .map(|&raw| (raw, supply.binder, supply.stage))
        }));
    }
    let raw_roots: Vec<NodeIndex> = declaration.iter().map(|(root, _)| root).collect();
    let tabled = tabled(&encoder.nodes, &raw_roots);
    let mut sites = encoder.seen;
    for raw in sites.values_mut() {
        *raw = tabled.of(*raw);
    }
    Encoded {
        content: ItemContent {
            reference,
            declaration: declaration.renumbered(|raw| tabled.of(raw)),
            placements: tabled.supports(&raw_roots),
            nodes: tabled.nodes,
            locus: layout.locus(),
        },
        sites: Sites(sites),
    }
}

/// The breadth-first walk that numbers an arena graph by discovery.
///
/// # Specification
/// - executable: none — queue order and first discovery relate mutable fields
///   over a walk, not a callable type declaration.
///
/// # Adequacy
/// - hypothesis: L3 — distinct arena allocations, shared nodes and interleaved
///   roots separate the breadth-first identity cases without a universal graph
///   claim.
/// - witness: `content::tests::content_is_free_of_arena_ids`
/// - witness: `content::tests::a_shared_node_is_listed_once`
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
struct Encoder<'arena, 'layout>
{
    /// The arena read.
    arena: &'arena CoreArena,
    /// The program positions resolve through.
    layout: &'layout Layout,
    /// The number each discovered node took.
    seen: BTreeMap<ArenaNode, NodeIndex>,
    /// The discovered nodes not yet written, in discovery order.
    queue: VecDeque<ArenaNode>,
    /// The written nodes, in discovery order.
    nodes: Vec<ContentNode>,
}

impl<'arena, 'layout> Encoder<'arena, 'layout>
{
    /// An empty walk over `arena`.
    ///
    /// # Specification
    /// trivial.
    const fn new(
        arena: &'arena CoreArena,
        layout: &'layout Layout,
    ) -> Self
    {
        Self {
            arena,
            layout,
            seen: BTreeMap::new(),
            queue: VecDeque::new(),
            nodes: Vec::new(),
        }
    }

    /// The number of `node`, numbering and queueing it on first discovery.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the number `node` took when first discovered; a node
    ///   discovered now takes the next number and joins the queue.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a shared node retains one number; separately
    ///   allocated equal nodes retain distinct numbers.
    /// - witness: `content::tests::a_shared_node_is_listed_once`
    #[spec(
        captures: [old = self.seen.get(&node).copied(), count = self.seen.len(), queued = self.queue.len()],
        ensures: |ret| self.seen.get(&node) == Some(&ret) && match old {
            Some(index) => ret == index && self.seen.len() == count && self.queue.len() == queued,
            None => usize::from(ret) == count && self.seen.len() == count.saturating_add(1)
                && self.queue.len() == queued.saturating_add(1) && self.queue.back() == Some(&node),
        },
    )]
    fn discover(
        &mut self,
        node: ArenaNode,
    ) -> NodeIndex
    {
        let next = NodeIndex::from(self.seen.len());
        let index = *self.seen.entry(node).or_insert(next);
        if index == next {
            self.queue.push_back(node);
        }
        index
    }

    /// Discover a whole nominal signature in its canonical root order.
    ///
    /// # Specification
    /// - requires: nothing; unresolved source nodes are admissible.
    /// - ensures: every parameter, index, constructor field and stated index is
    ///   discovered once by identity.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — shared fields and changed constructor signatures
    ///   remain distinct.
    /// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
    #[spec(ensures: |ret| ret.parameters.len() == signature.parameters().len()
        && ret.constructors.iter().map(Vec::len).eq(signature.constructors().iter().map(Vec::len))
        && ret.iter().all(|root| usize::from(root) < self.seen.len()))]
    fn data_roots(
        &mut self,
        signature: &gandr_core_term::DataSignature,
    ) -> DataRoots
    {
        let parameters = signature
            .parameters()
            .iter()
            .map(|&ty| self.discover(ArenaNode::ValueType(ty)))
            .collect();
        let indices = signature
            .indices()
            .iter()
            .map(|&ty| self.discover(ArenaNode::ValueType(ty)))
            .collect();
        let constructors = signature
            .constructors()
            .iter()
            .map(|fields| {
                fields
                    .iter()
                    .map(|&ty| self.discover(ArenaNode::ValueType(ty)))
                    .collect()
            })
            .collect();
        let results = signature
            .results()
            .iter()
            .map(|stated| {
                stated
                    .iter()
                    .map(|&value| self.discover(ArenaNode::Value(value)))
                    .collect()
            })
            .collect();
        let kind = self.discover(ArenaNode::ValueType(signature.kind()));
        DataRoots {
            parameters,
            indices,
            constructors,
            results,
            kind,
            presentation: signature.presentation().clone(),
        }
    }

    /// Write every queued node, discovering its children as it is written.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the queue is empty and the table holds one entry per number
    ///   handed out, in number order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — shared and interleaved roots are exhausted into one
    ///   discovery-numbered table.
    /// - witness: `content::tests::a_shared_node_is_listed_once`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: each encoder drains once, writing every node it discovered; the check reads each discovered number once"
        )
    )]
    #[spec(ensures: self.queue.is_empty() && self.nodes.len() == self.seen.len()
        && self.seen.values().all(|index| usize::from(*index) < self.nodes.len()))]
    fn drain(&mut self)
    {
        while let Some(node) = self.queue.pop_front() {
            let written = self.read(node);
            self.nodes.push(written);
        }
    }

    /// The content node of `node`, its children discovered left to right.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the former of `node` over its children's numbers, a constant
    ///   resolved to its reference, or the unresolved node of its sort.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite corpus exercises four resolving node
    ///   families; the foreign-id witness exercises the unresolved value
    ///   branch.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    /// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
    #[spec(ensures: |ret| ret.sort() == match node {
        ArenaNode::Value(_) => Sort::Value,
        ArenaNode::Computation(_) => Sort::Computation,
        ArenaNode::ValueType(_) => Sort::ValueType,
        ArenaNode::CompType(_) => Sort::CompType,
    })]
    fn read(
        &mut self,
        node: ArenaNode,
    ) -> ContentNode
    {
        let arena = self.arena;
        match node {
            ArenaNode::Value(id) => arena
                .value(id)
                .map_or(ContentNode::Unresolved(Sort::Value), |value| {
                    self.read_value(value)
                }),
            ArenaNode::Computation(id) => arena
                .computation(id)
                .map_or(ContentNode::Unresolved(Sort::Computation), |computation| {
                    self.read_computation(computation)
                }),
            ArenaNode::ValueType(id) => arena
                .value_type(id)
                .map_or(ContentNode::Unresolved(Sort::ValueType), |value_type| {
                    self.read_value_type(value_type)
                }),
            ArenaNode::CompType(id) => arena
                .comp_type(id)
                .map_or(ContentNode::Unresolved(Sort::CompType), |comp_type| {
                    self.read_comp_type(comp_type)
                }),
        }
    }

    /// The content node of a value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the corresponding former with child ids replaced by their
    ///   discovery indices; the predicate bounds the sort and child indices.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite persistence corpus exercises selected
    ///   formers and sharing. The attribute does not independently reconstruct
    ///   every payload.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(ensures: |ret| ret.sort() == Sort::Value
        && !matches!(ret, ContentNode::Unresolved(_))
        && ret.children().iter().all(|(child, _)| usize::from(child) < self.seen.len()))]
    fn read_value(
        &mut self,
        value: &Value,
    ) -> ContentNode
    {
        match *value {
            Value::Constructor {
                datatype,
                tag,
                ref fields,
            } => ContentNode::Constructor {
                datatype: self.discover(ArenaNode::ValueType(datatype)),
                tag,
                fields: fields
                    .iter()
                    .map(|&field| self.discover(ArenaNode::Value(field)))
                    .collect(),
            },
            Value::Record(ref fields) => ContentNode::Record(
                fields
                    .iter()
                    .map(|(label, &field)| (label.clone(), self.discover(ArenaNode::Value(field))))
                    .collect(),
            ),
            Value::Reify(ref frames) => ContentNode::Reify(
                frames
                    .iter()
                    .map(|frame| match *frame {
                        gandr_core_term::control::StackFrame::Apply(value) => {
                            gandr_core_term::control::StackFrame::Apply(
                                self.discover(ArenaNode::Value(value)),
                            )
                        },
                        gandr_core_term::control::StackFrame::Bind(body) => {
                            gandr_core_term::control::StackFrame::Bind(
                                self.discover(ArenaNode::Computation(body)),
                            )
                        },
                        gandr_core_term::control::StackFrame::Project(side) => {
                            gandr_core_term::control::StackFrame::Project(side)
                        },
                    })
                    .collect(),
            ),
            Value::Primitive { primitive, .. } => ContentNode::PrimitiveValue(primitive),
            Value::PathRefl(code) => ContentNode::PathRefl(self.discover(ArenaNode::Value(code))),
            Value::Here(point) => ContentNode::Here(self.discover(ArenaNode::Value(point))),
            Value::SessionRelated {
                relation,
                source,
                target,
                payloads,
            } => {
                let source = self.discover(ArenaNode::Value(source));
                let target = self.discover(ArenaNode::Value(target));
                ContentNode::SessionRelated {
                    relation,
                    source,
                    target,
                    payloads: self.discover(ArenaNode::Value(payloads)),
                }
            },
            Value::Stay(point) => ContentNode::Stay(self.discover(ArenaNode::Value(point))),
            Value::Then(first, second) => {
                let first = self.discover(ArenaNode::Value(first));
                ContentNode::Then(first, self.discover(ArenaNode::Value(second)))
            },
            Value::FlowProduct(first, second) => {
                let first = self.discover(ArenaNode::Value(first));
                ContentNode::FlowProduct(first, self.discover(ArenaNode::Value(second)))
            },
            Value::Forward(translator) => {
                ContentNode::Forward(self.discover(ArenaNode::Value(translator)))
            },
            Value::FunctionFlow(domain, codomain) => {
                let domain = self.discover(ArenaNode::Value(domain));
                ContentNode::FunctionFlow(domain, self.discover(ArenaNode::Value(codomain)))
            },
            Value::Recorded(ref moves) => ContentNode::Recorded(
                moves
                    .iter()
                    .map(|step| {
                        step.try_map(|payload| {
                            Ok::<_, core::convert::Infallible>(
                                self.discover(ArenaNode::Value(payload)),
                            )
                        })
                        .unwrap_or_else(|never| match never {})
                    })
                    .collect(),
            ),
            Value::Returned(computation) => {
                ContentNode::Returned(self.discover(ArenaNode::Computation(computation)))
            },
            Value::Nested(computation) => {
                ContentNode::Nested(self.discover(ArenaNode::Computation(computation)))
            },
            Value::Run(computation) => {
                ContentNode::Run(self.discover(ArenaNode::Computation(computation)))
            },
            Value::PathProduct(first, second) => {
                let first = self.discover(ArenaNode::Value(first));
                ContentNode::PathProduct(first, self.discover(ArenaNode::Value(second)))
            },
            Value::Funext(left, right) => {
                let left = self.discover(ArenaNode::Value(left));
                ContentNode::Funext(left, self.discover(ArenaNode::Value(right)))
            },
            Value::Equiv(forward, backward) => {
                let forward = self.discover(ArenaNode::Value(forward));
                ContentNode::Equiv(forward, self.discover(ArenaNode::Value(backward)))
            },
            Value::Univalence(record, forward) => {
                let record = self.discover(ArenaNode::Value(record));
                ContentNode::Univalence(record, self.discover(ArenaNode::Value(forward)))
            },
            Value::Ua {
                stratum,
                ref sides,
                forward,
                backward,
            } => ContentNode::Ua {
                stratum,
                sides: alloc::sync::Arc::clone(sides),
                forward: self.discover(ArenaNode::Value(forward)),
                backward: self.discover(ArenaNode::Value(backward)),
            },
            Value::PathEquiv {
                path_type,
                forward,
                backward,
                ref evidence,
            } => ContentNode::PathEquiv {
                path_type: self.discover(ArenaNode::ValueType(path_type)),
                forward: self.discover(ArenaNode::Value(forward)),
                backward: self.discover(ArenaNode::Value(backward)),
                evidence: alloc::sync::Arc::clone(evidence),
            },
            Value::Variable { zone, index } => ContentNode::Variable { zone, index },
            Value::Constant(position) => ContentNode::Constant(self.layout.resolve(position)),
            Value::ListNil => ContentNode::ListNil,
            Value::ListCons(head, tail) => {
                let head = self.discover(ArenaNode::Value(head));
                ContentNode::ListCons(head, self.discover(ArenaNode::Value(tail)))
            },
            Value::Literal(ref literal) => ContentNode::Literal(literal.clone()),
            Value::Tuple(ref components) => ContentNode::Tuple(
                components
                    .iter()
                    .map(|&component| self.discover(ArenaNode::Value(component)))
                    .collect(),
            ),
            Value::Injection(summand, body) => {
                ContentNode::Injection(summand, self.discover(ArenaNode::Value(body)))
            },
            Value::Ascribe { value, ty } => {
                let value = self.discover(ArenaNode::Value(value));
                ContentNode::ValueAscribe {
                    value,
                    ty: self.discover(ArenaNode::ValueType(ty)),
                }
            },
            Value::Thunk(body) => ContentNode::Thunk(self.discover(ArenaNode::Computation(body))),
            Value::Lift { ref target, body } => ContentNode::ValueLift {
                target: target.clone(),
                body: self.discover(ArenaNode::Value(body)),
            },
            Value::Quote(quoted) => ContentNode::Quote(self.discover(ArenaNode::ValueType(quoted))),
            Value::QuoteComputation(quoted) => {
                ContentNode::QuoteComputation(self.discover(ArenaNode::CompType(quoted)))
            },
            Value::StaticLambda(body) => {
                ContentNode::StaticLambda(self.discover(ArenaNode::Value(body)))
            },
            Value::StaticApplication(head, argument) => {
                let head = self.discover(ArenaNode::Value(head));
                ContentNode::StaticApplication(head, self.discover(ArenaNode::Value(argument)))
            },
            Value::Hole(hole) => ContentNode::Hole(hole),
            Value::Mark { mark, body } => ContentNode::ValueMark {
                mark,
                body: self.discover(ArenaNode::Value(body)),
            },
        }
    }

    /// The content node of a computation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the corresponding former with child ids replaced by their
    ///   discovery indices; a world form has no content vocabulary and is
    ///   listed by its sort, which makes the item opaque. The predicate bounds
    ///   the sort and child indices.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite persistence corpus exercises selected
    ///   formers and sharing. The attribute does not independently reconstruct
    ///   every payload.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(ensures: |ret| ret.sort() == Sort::Computation
        && (!matches!(ret, ContentNode::Unresolved(_)) || matches!(*computation, Computation::World(_)))
        && ret.children().iter().all(|(child, _)| usize::from(child) < self.seen.len()))]
    fn read_computation(
        &mut self,
        computation: &Computation,
    ) -> ContentNode
    {
        match *computation {
            Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
                ref arities,
                equations,
            } => ContentNode::DataCase {
                scrutinee: self.discover(ArenaNode::Value(scrutinee)),
                motive: self.discover(ArenaNode::CompType(motive)),
                branches: branches
                    .iter()
                    .map(|&branch| self.discover(ArenaNode::Computation(branch)))
                    .collect(),
                arities: arities.clone(),
                equations,
            },
            Computation::RecordProjection(record, ref label) => ContentNode::RecordProjection(
                self.discover(ArenaNode::Value(record)),
                label.clone(),
            ),
            Computation::TupleProjection(tuple, component) => {
                ContentNode::TupleProjection(self.discover(ArenaNode::Value(tuple)), component)
            },
            Computation::Ride {
                motive,
                flow,
                value,
            } => {
                let motive = self.discover(ArenaNode::ValueType(motive));
                let flow = self.discover(ArenaNode::Value(flow));
                ContentNode::Ride {
                    motive,
                    flow,
                    value: self.discover(ArenaNode::Value(value)),
                }
            },
            Computation::Session(ref action) => ContentNode::Session(
                action
                    .try_map(
                        gandr_core_term::session::ChildOrder::Forward,
                        self,
                        |reader, value| {
                            Ok::<_, core::convert::Infallible>(
                                reader.discover(ArenaNode::Value(value)),
                            )
                        },
                        |reader, body| Ok(reader.discover(ArenaNode::Computation(body))),
                        |reader, ty| Ok(reader.discover(ArenaNode::ValueType(ty))),
                    )
                    .unwrap_or_else(|never| match never {}),
            ),
            // A located judgement reads the world register and each constant's
            // home, which no footprint records: content holding a world form
            // has no identity to key on, and stays opaque.
            Computation::World(_) => ContentNode::Unresolved(Sort::Computation),
            Computation::Memory(ref form) => ContentNode::Memory(
                form.try_map(
                    gandr_core_term::session::ChildOrder::Forward,
                    self,
                    |reader, value| {
                        Ok::<_, core::convert::Infallible>(reader.discover(ArenaNode::Value(value)))
                    },
                    |reader, body| Ok(reader.discover(ArenaNode::Computation(body))),
                )
                .unwrap_or_else(|never| match never {}),
            ),
            Computation::Perform {
                ref signature,
                ref operation,
                payload,
            } => {
                let payload = self.discover(ArenaNode::Value(payload));
                let signature = signature
                    .try_relocate(|ty| {
                        Ok::<_, core::convert::Infallible>(self.discover(ArenaNode::ValueType(ty)))
                    })
                    .unwrap_or_else(|never| match never {});
                ContentNode::Perform {
                    signature,
                    operation: operation.clone(),
                    payload,
                }
            },
            Computation::Handle {
                ref signature,
                subject,
                on_return,
                ref clauses,
            }
            | Computation::Scope {
                ref signature,
                subject,
                on_return,
                ref clauses,
            } => {
                let subject = self.discover(ArenaNode::Computation(subject));
                let on_return = self.discover(ArenaNode::Computation(on_return));
                let signature = signature
                    .try_relocate(|ty| {
                        Ok::<_, core::convert::Infallible>(self.discover(ArenaNode::ValueType(ty)))
                    })
                    .unwrap_or_else(|never| match never {});
                let clauses = clauses
                    .iter()
                    .map(|clause| gandr_core_term::control::EffectClause {
                        operation: clause.operation.clone(),
                        body: self.discover(ArenaNode::Computation(clause.body)),
                    })
                    .collect();
                if matches!(*computation, Computation::Scope { .. }) {
                    ContentNode::Scope {
                        signature,
                        subject,
                        on_return,
                        clauses,
                    }
                }
                else {
                    ContentNode::Handle {
                        signature,
                        subject,
                        on_return,
                        clauses,
                    }
                }
            },
            Computation::Exercise {
                capability,
                ref signature,
                ref operation,
                payload,
            } => {
                let capability = self.discover(ArenaNode::Value(capability));
                let payload = self.discover(ArenaNode::Value(payload));
                let signature = signature
                    .try_relocate(|ty| {
                        Ok::<_, core::convert::Infallible>(self.discover(ArenaNode::ValueType(ty)))
                    })
                    .unwrap_or_else(|never| match never {});
                ContentNode::Exercise {
                    capability,
                    signature,
                    operation: operation.clone(),
                    payload,
                }
            },
            Computation::Resume(stack, body) => ContentNode::Resume(
                self.discover(ArenaNode::Value(stack)),
                self.discover(ArenaNode::Computation(body)),
            ),
            Computation::Abandon(stack) => {
                ContentNode::Abandon(self.discover(ArenaNode::Value(stack)))
            },
            Computation::Split {
                scrutinee,
                arity,
                motive: gandr_core_term::SplitMotive::Ambient,
                body,
            } => ContentNode::Split(
                self.discover(ArenaNode::Value(scrutinee)),
                arity,
                self.discover(ArenaNode::Computation(body)),
            ),
            Computation::Split {
                scrutinee,
                arity,
                motive: gandr_core_term::SplitMotive::Scrutinee(motive),
                body,
            } => {
                let scrutinee = self.discover(ArenaNode::Value(scrutinee));
                let motive = self.discover(ArenaNode::CompType(motive));
                ContentNode::DependentSplit {
                    scrutinee,
                    arity,
                    motive,
                    body: self.discover(ArenaNode::Computation(body)),
                }
            },
            Computation::Reset(body) => {
                ContentNode::Reset(self.discover(ArenaNode::Computation(body)))
            },
            Computation::Shift(body) => {
                ContentNode::Shift(self.discover(ArenaNode::Computation(body)))
            },
            Computation::With(ref components) => ContentNode::With(
                components
                    .iter()
                    .map(|&component| self.discover(ArenaNode::Computation(component)))
                    .collect(),
            ),
            Computation::Ascribe { body, ty } => {
                let body = self.discover(ArenaNode::Computation(body));
                ContentNode::Ascribe {
                    body,
                    ty: self.discover(ArenaNode::CompType(ty)),
                }
            },
            Computation::Project(component, body) => {
                ContentNode::Project(component, self.discover(ArenaNode::Computation(body)))
            },

            Computation::ListFold {
                element,
                result,
                list,
                on_nil,
                on_cons,
            } => ContentNode::ListFold {
                element: self.discover(ArenaNode::ValueType(element)),
                result: self.discover(ArenaNode::ValueType(result)),
                list: self.discover(ArenaNode::Value(list)),
                on_nil: self.discover(ArenaNode::Computation(on_nil)),
                on_cons: self.discover(ArenaNode::Computation(on_cons)),
            },
            Computation::ListCase {
                list,
                on_nil,
                on_cons,
            } => ContentNode::ListCase {
                list: self.discover(ArenaNode::Value(list)),
                on_nil: self.discover(ArenaNode::Computation(on_nil)),
                on_cons: self.discover(ArenaNode::Computation(on_cons)),
            },
            Computation::Primitive {
                primitive,
                arguments,
            } => {
                use gandr_core_term::primitive::Arguments;
                let arguments = match arguments {
                    Arguments::Unary(argument) => {
                        Arguments::Unary(self.discover(ArenaNode::Value(argument)))
                    },
                    Arguments::Binary([first, second]) => {
                        let first = self.discover(ArenaNode::Value(first));
                        Arguments::Binary([first, self.discover(ArenaNode::Value(second))])
                    },
                };
                ContentNode::Primitive(primitive, arguments)
            },
            Computation::Transport(path, value) => {
                let path = self.discover(ArenaNode::Value(path));
                ContentNode::Transport(path, self.discover(ArenaNode::Value(value)))
            },
            Computation::PathTransport {
                motive,
                path,
                value,
            } => ContentNode::ElementTransport {
                motive: self.discover(ArenaNode::ValueType(motive)),
                path: self.discover(ArenaNode::Value(path)),
                value: self.discover(ArenaNode::Value(value)),
            },
            Computation::TelescopeTransport {
                motive,
                path,
                start,
                over,
                value,
            } => ContentNode::TelescopeTransport {
                motive: self.discover(ArenaNode::CompType(motive)),
                path: self.discover(ArenaNode::Value(path)),
                start: self.discover(ArenaNode::Value(start)),
                over: self.discover(ArenaNode::Value(over)),
                value: self.discover(ArenaNode::Value(value)),
            },
            Computation::Lambda(body) => {
                ContentNode::Lambda(self.discover(ArenaNode::Computation(body)))
            },
            Computation::Application(head, argument) => {
                let head = self.discover(ArenaNode::Computation(head));
                ContentNode::Application(head, self.discover(ArenaNode::Value(argument)))
            },
            Computation::Return(value) => {
                ContentNode::Return(self.discover(ArenaNode::Value(value)))
            },
            Computation::Bind(bound, rest) => {
                let bound = self.discover(ArenaNode::Computation(bound));
                ContentNode::Bind(bound, self.discover(ArenaNode::Computation(rest)))
            },
            Computation::Force(value) => ContentNode::Force(self.discover(ArenaNode::Value(value))),
            Computation::Case {
                scrutinee,
                ref branches,
            } => {
                let scrutinee = self.discover(ArenaNode::Value(scrutinee));
                ContentNode::Case {
                    scrutinee,
                    branches: branches
                        .iter()
                        .map(|&branch| self.discover(ArenaNode::Computation(branch)))
                        .collect(),
                }
            },
            Computation::Hole(hole) => ContentNode::ComputationHole(hole),
            Computation::Mark { mark, body } => ContentNode::ComputationMark {
                mark,
                body: self.discover(ArenaNode::Computation(body)),
            },
            Computation::Fixpoint { body, evidence } => ContentNode::Fixpoint {
                body: self.discover(ArenaNode::Computation(body)),
                evidence,
            },
        }
    }

    /// The content node of a value type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the corresponding former with child ids replaced by their
    ///   discovery indices; the predicate bounds the sort and child indices. A
    ///   staged type, the judgement's own, is the unresolved node.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite persistence corpus exercises selected
    ///   formers and sharing. The attribute does not independently reconstruct
    ///   every payload.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(ensures: |ret| ret.sort() == Sort::ValueType
        && (!matches!(ret, ContentNode::Unresolved(_)) || matches!(*value_type, ValueType::Staged { .. } | ValueType::World(_)))
        && ret.children().iter().all(|(child, _)| usize::from(child) < self.seen.len()))]
    fn read_value_type(
        &mut self,
        value_type: &ValueType,
    ) -> ContentNode
    {
        match *value_type {
            ValueType::Session(ref session) => ContentNode::SessionType(
                session
                    .try_relocate(|ty| {
                        Ok::<_, core::convert::Infallible>(self.discover(ArenaNode::ValueType(ty)))
                    })
                    .unwrap_or_else(|never| match never {}),
            ),
            ValueType::Data {
                declaration,
                ref arguments,
            } => ContentNode::Data {
                declaration: self.layout.resolve(declaration),
                arguments: arguments
                    .iter()
                    .map(|&argument| self.discover(ArenaNode::Value(argument)))
                    .collect(),
            },
            ValueType::Record(ref fields) => ContentNode::RecordType(
                fields
                    .iter()
                    .map(|(label, &field)| {
                        (label.clone(), self.discover(ArenaNode::ValueType(field)))
                    })
                    .collect(),
            ),
            ValueType::Stack { input, output } => ContentNode::Stack {
                input: self.discover(ArenaNode::CompType(input)),
                output: self.discover(ArenaNode::CompType(output)),
            },
            ValueType::Capability {
                ref authority,
                grade,
                region,
            } => ContentNode::Capability {
                authority: authority
                    .try_relocate(|ty| {
                        Ok::<_, core::convert::Infallible>(self.discover(ArenaNode::ValueType(ty)))
                    })
                    .unwrap_or_else(|never| match never {}),
                grade,
                region,
            },
            ValueType::PathUniverse(source, target) => {
                let source = self.discover(ArenaNode::Value(source));
                ContentNode::PathUniverse(source, self.discover(ArenaNode::Value(target)))
            },
            ValueType::Path {
                carrier,
                left,
                right,
            } => ContentNode::PathType {
                carrier: self.discover(ArenaNode::ValueType(carrier)),
                left: self.discover(ArenaNode::Value(left)),
                right: self.discover(ArenaNode::Value(right)),
            },
            ValueType::Flow {
                carrier,
                source,
                target,
            } => ContentNode::FlowType {
                carrier: self.discover(ArenaNode::ValueType(carrier)),
                source: self.discover(ArenaNode::Value(source)),
                target: self.discover(ArenaNode::Value(target)),
            },
            ValueType::Run(code) => ContentNode::RunType(self.discover(ArenaNode::Value(code))),
            ValueType::Prefix(code) => {
                ContentNode::PrefixType(self.discover(ArenaNode::Value(code)))
            },
            ValueType::Base(base) => ContentNode::Base(base),
            ValueType::Kept { value, region } => ContentNode::KeptType {
                value: self.discover(ArenaNode::ValueType(value)),
                region,
            },
            ValueType::List(element) => {
                ContentNode::List(self.discover(ArenaNode::ValueType(element)))
            },
            ValueType::Product(ref parts) => ContentNode::Product(
                parts
                    .iter()
                    .map(|&part| self.discover(ArenaNode::ValueType(part)))
                    .collect(),
            ),
            ValueType::Sum(ref parts) => ContentNode::Sum(
                parts
                    .iter()
                    .map(|&part| self.discover(ArenaNode::ValueType(part)))
                    .collect(),
            ),
            ValueType::Thunk(body) => {
                ContentNode::ThunkType(self.discover(ArenaNode::CompType(body)))
            },
            ValueType::Universe { sort, ref level } => ContentNode::Universe {
                sort,
                level: level.clone(),
            },
            ValueType::Lift { inner, ref target } => ContentNode::TypeLift {
                inner: self.discover(ArenaNode::ValueType(inner)),
                target: target.clone(),
            },
            ValueType::Element { code, ref target } => ContentNode::Element {
                code: self.discover(ArenaNode::Value(code)),
                target: target.clone(),
            },
            ValueType::Abstract(position) => ContentNode::Abstract(self.layout.resolve(position)),
            ValueType::StaticPi { domain, codomain } => {
                let domain = self.discover(ArenaNode::ValueType(domain));
                ContentNode::StaticPi {
                    domain,
                    codomain: self.discover(ArenaNode::ValueType(codomain)),
                }
            },
            ValueType::Sigma { first, second } => {
                let first = self.discover(ArenaNode::ValueType(first));
                ContentNode::Sigma {
                    first,
                    second: self.discover(ArenaNode::ValueType(second)),
                }
            },
            ValueType::Unknown => ContentNode::UnknownType,
            ValueType::Buffer => ContentNode::BufferType,
            // A stage is minted by one judgement and names nothing past it,
            // and a handle or a capability names a world, whose crossing
            // decisions read what no footprint records: content naming
            // either has no identity to key on, and stays opaque.
            ValueType::Staged { .. } | ValueType::World(_) => {
                ContentNode::Unresolved(Sort::ValueType)
            },
        }
    }

    /// The content node of a computation type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the corresponding former with child ids replaced by their
    ///   discovery indices; the predicate bounds the sort and child indices.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite persistence corpus exercises selected
    ///   formers and sharing. The attribute does not independently reconstruct
    ///   every payload.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(ensures: |ret| ret.sort() == Sort::CompType
        && (!matches!(ret, ContentNode::Unresolved(_)) || matches!(*comp_type, CompType::Codata { .. }))
        && ret.children().iter().all(|(child, _)| usize::from(child) < self.seen.len()))]
    fn read_comp_type(
        &mut self,
        comp_type: &CompType,
    ) -> ContentNode
    {
        match *comp_type {
            CompType::With(ref components) => ContentNode::WithType(
                components
                    .iter()
                    .map(|&component| self.discover(ArenaNode::CompType(component)))
                    .collect(),
            ),
            CompType::Returner {
                result,
                ref effects,
            } => {
                let result = self.discover(ArenaNode::ValueType(result));
                let effects = effects
                    .try_relocate(|ty| {
                        Ok::<_, core::convert::Infallible>(self.discover(ArenaNode::ValueType(ty)))
                    })
                    .unwrap_or_else(|never| match never {});
                ContentNode::Returner { result, effects }
            },
            CompType::Arrow { domain, codomain } => {
                let domain = self.discover(ArenaNode::ValueType(domain));
                ContentNode::Arrow {
                    domain,
                    codomain: self.discover(ArenaNode::CompType(codomain)),
                }
            },
            CompType::Pi { domain, codomain } => {
                let domain = self.discover(ArenaNode::ValueType(domain));
                ContentNode::Pi {
                    domain,
                    codomain: self.discover(ArenaNode::CompType(codomain)),
                }
            },
            CompType::Element { code, ref target } => ContentNode::ComputationElement {
                code: self.discover(ArenaNode::Value(code)),
                target: target.clone(),
            },
            CompType::Unknown => ContentNode::UnknownComputationType,
            // A codata application has no content form, and stays opaque.
            CompType::Codata { .. } => ContentNode::Unresolved(Sort::CompType),
        }
    }
}

/// `node` with every child index replaced by its image under `image`, applied
/// left to right.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the former and non-child payloads are retained; each child is
///   replaced by one call to `image`, in left-to-right order. The predicate
///   checks the former, sort and child-slot sorts without recalling `image`.
/// - panics: propagates a panic from `image`.
///
/// # Adequacy
/// - hypothesis: L2 — an interleaved signature is renumbered independently. The
///   malformed-table witness checks cycles, dangling children and root
///   selection.
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
/// - witness: `content::tests::factoring_closes_dangling_and_cyclic_tables`
/// - witness: `content::tests::renumbering_carries_every_frame_and_clause_body_to_its_image`
#[spec(ensures: |ret| {
        core::mem::discriminant(&ret) == core::mem::discriminant(node)
            && ret.sort() == node.sort()
            && ret
                .children()
                .iter()
                .map(|(_, sort)| sort)
                .eq(node.children().iter().map(|(_, sort)| sort))
    })]
#[inline]
pub fn map_children<Image>(
    node: &ContentNode,
    image: &mut Image,
) -> ContentNode
where
    Image: FnMut(NodeIndex) -> NodeIndex,
{
    match *node {
        ContentNode::Data {
            ref declaration,
            ref arguments,
        } => ContentNode::Data {
            declaration: declaration.clone(),
            arguments: arguments.iter().map(|&argument| image(argument)).collect(),
        },
        ContentNode::RecordType(ref fields) => ContentNode::RecordType(
            fields
                .iter()
                .map(|(label, &field)| (label.clone(), image(field)))
                .collect(),
        ),
        ContentNode::Constructor {
            datatype,
            tag,
            ref fields,
        } => ContentNode::Constructor {
            datatype: image(datatype),
            tag,
            fields: fields.iter().map(|&field| image(field)).collect(),
        },
        ContentNode::Record(ref fields) => ContentNode::Record(
            fields
                .iter()
                .map(|(label, &field)| (label.clone(), image(field)))
                .collect(),
        ),
        ContentNode::DataCase {
            scrutinee,
            motive,
            ref branches,
            ref arities,
            equations,
        } => ContentNode::DataCase {
            scrutinee: image(scrutinee),
            motive: image(motive),
            branches: branches.iter().map(|&branch| image(branch)).collect(),
            arities: arities.clone(),
            equations,
        },
        ContentNode::RecordProjection(record, ref label) => {
            ContentNode::RecordProjection(image(record), label.clone())
        },
        ContentNode::TupleProjection(tuple, component) => {
            ContentNode::TupleProjection(image(tuple), component)
        },
        ContentNode::Reify(ref frames) => {
            let mut mapped = alloc::sync::Arc::clone(frames);
            for (index, frame) in frames.iter().enumerate() {
                let new = match *frame {
                    gandr_core_term::control::StackFrame::Apply(value) => {
                        gandr_core_term::control::StackFrame::Apply(image(value))
                    },
                    gandr_core_term::control::StackFrame::Bind(body) => {
                        gandr_core_term::control::StackFrame::Bind(image(body))
                    },
                    gandr_core_term::control::StackFrame::Project(side) => {
                        gandr_core_term::control::StackFrame::Project(side)
                    },
                };
                if new != *frame
                    && let Some(slot) = alloc::sync::Arc::make_mut(&mut mapped).get_mut(index)
                {
                    *slot = new;
                }
            }
            ContentNode::Reify(mapped)
        },
        ContentNode::Stack { input, output } => ContentNode::Stack {
            input: image(input),
            output: image(output),
        },
        ContentNode::WithType(ref components) => ContentNode::WithType(
            components
                .iter()
                .map(|&component| image(component))
                .collect(),
        ),
        ContentNode::Session(ref action) => ContentNode::Session(
            action
                .try_map(
                    gandr_core_term::session::ChildOrder::Forward,
                    image,
                    |image, value| Ok::<_, core::convert::Infallible>(image(value)),
                    |image, body| Ok(image(body)),
                    |image, ty| Ok(image(ty)),
                )
                .unwrap_or_else(|never| match never {}),
        ),
        ContentNode::Memory(ref form) => ContentNode::Memory(
            form.try_map(
                gandr_core_term::session::ChildOrder::Forward,
                image,
                |image, value| Ok::<_, core::convert::Infallible>(image(value)),
                |image, body| Ok(image(body)),
            )
            .unwrap_or_else(|never| match never {}),
        ),
        ContentNode::SessionType(ref session) => ContentNode::SessionType(
            session
                .try_relocate(|ty| Ok::<_, core::convert::Infallible>(image(ty)))
                .unwrap_or_else(|never| match never {}),
        ),
        ContentNode::Perform {
            ref signature,
            ref operation,
            payload,
        } => {
            let payload = image(payload);
            let signature = signature
                .try_map_types(gandr_core_term::effect::TypeOrder::Forward, |ty| {
                    Ok::<_, core::convert::Infallible>(image(ty))
                })
                .unwrap_or_else(|never| match never {});
            ContentNode::Perform {
                signature,
                operation: operation.clone(),
                payload,
            }
        },
        ContentNode::Handle {
            ref signature,
            subject,
            on_return,
            ref clauses,
        }
        | ContentNode::Scope {
            ref signature,
            subject,
            on_return,
            ref clauses,
        } => {
            let subject = image(subject);
            let on_return = image(on_return);
            let signature = signature
                .try_map_types(gandr_core_term::effect::TypeOrder::Forward, |ty| {
                    Ok::<_, core::convert::Infallible>(image(ty))
                })
                .unwrap_or_else(|never| match never {});
            let mut mapped = alloc::sync::Arc::clone(clauses);
            for (index, clause) in clauses.iter().enumerate() {
                let body = image(clause.body);
                if body != clause.body
                    && let Some(slot) = alloc::sync::Arc::make_mut(&mut mapped).get_mut(index)
                {
                    slot.body = body;
                }
            }
            if matches!(*node, ContentNode::Scope { .. }) {
                ContentNode::Scope {
                    signature,
                    subject,
                    on_return,
                    clauses: mapped,
                }
            }
            else {
                ContentNode::Handle {
                    signature,
                    subject,
                    on_return,
                    clauses: mapped,
                }
            }
        },
        ContentNode::Exercise {
            capability,
            ref signature,
            ref operation,
            payload,
        } => {
            let capability = image(capability);
            let payload = image(payload);
            let signature = signature
                .try_map_types(gandr_core_term::effect::TypeOrder::Forward, |ty| {
                    Ok::<_, core::convert::Infallible>(image(ty))
                })
                .unwrap_or_else(|never| match never {});
            ContentNode::Exercise {
                capability,
                signature,
                operation: operation.clone(),
                payload,
            }
        },
        ContentNode::Resume(stack, body) => ContentNode::Resume(image(stack), image(body)),
        ContentNode::Abandon(stack) => ContentNode::Abandon(image(stack)),
        ContentNode::Split(scrutinee, arity, body) => {
            ContentNode::Split(image(scrutinee), arity, image(body))
        },
        ContentNode::DependentSplit {
            scrutinee,
            arity,
            motive,
            body,
        } => ContentNode::DependentSplit {
            scrutinee: image(scrutinee),
            arity,
            motive: image(motive),
            body: image(body),
        },
        ContentNode::Reset(body) => ContentNode::Reset(image(body)),
        ContentNode::Shift(body) => ContentNode::Shift(image(body)),
        ContentNode::With(ref components) => ContentNode::With(
            components
                .iter()
                .map(|&component| image(component))
                .collect(),
        ),
        ContentNode::Ascribe { body, ty } => ContentNode::Ascribe {
            body: image(body),
            ty: image(ty),
        },
        ContentNode::ValueAscribe { value, ty } => ContentNode::ValueAscribe {
            value: image(value),
            ty: image(ty),
        },
        ContentNode::Project(component, body) => ContentNode::Project(component, image(body)),
        ContentNode::PrimitiveValue(primitive) => ContentNode::PrimitiveValue(primitive),
        ContentNode::Primitive(primitive, mut arguments) => {
            for argument in arguments.iter_mut() {
                *argument = image(*argument);
            }
            ContentNode::Primitive(primitive, arguments)
        },
        ContentNode::PathUniverse(source, target) => {
            let source = image(source);
            ContentNode::PathUniverse(source, image(target))
        },
        ContentNode::PathRefl(code) => ContentNode::PathRefl(image(code)),
        ContentNode::Here(point) => ContentNode::Here(image(point)),
        ContentNode::Returned(computation) => ContentNode::Returned(image(computation)),
        ContentNode::Nested(computation) => ContentNode::Nested(image(computation)),
        ContentNode::Run(computation) => ContentNode::Run(image(computation)),
        ContentNode::PathType {
            carrier,
            left,
            right,
        } => ContentNode::PathType {
            carrier: image(carrier),
            left: image(left),
            right: image(right),
        },
        ContentNode::FlowType {
            carrier,
            source,
            target,
        } => ContentNode::FlowType {
            carrier: image(carrier),
            source: image(source),
            target: image(target),
        },
        ContentNode::RunType(code) => ContentNode::RunType(image(code)),
        ContentNode::PrefixType(code) => ContentNode::PrefixType(image(code)),
        ContentNode::SessionRelated {
            relation,
            source,
            target,
            payloads,
        } => ContentNode::SessionRelated {
            relation,
            source: image(source),
            target: image(target),
            payloads: image(payloads),
        },
        ContentNode::Stay(point) => ContentNode::Stay(image(point)),
        ContentNode::Then(first, second) => {
            let first = image(first);
            ContentNode::Then(first, image(second))
        },
        ContentNode::FlowProduct(first, second) => {
            let first = image(first);
            ContentNode::FlowProduct(first, image(second))
        },
        ContentNode::Forward(translator) => ContentNode::Forward(image(translator)),
        ContentNode::FunctionFlow(domain, codomain) => {
            let domain = image(domain);
            ContentNode::FunctionFlow(domain, image(codomain))
        },
        ContentNode::Recorded(ref moves) => ContentNode::Recorded(
            moves
                .iter()
                .map(|step| {
                    step.try_map(|payload| Ok::<_, core::convert::Infallible>(image(payload)))
                        .unwrap_or_else(|never| match never {})
                })
                .collect(),
        ),
        ContentNode::Ride {
            motive,
            flow,
            value,
        } => ContentNode::Ride {
            motive: image(motive),
            flow: image(flow),
            value: image(value),
        },
        ContentNode::ElementTransport {
            motive,
            path,
            value,
        } => ContentNode::ElementTransport {
            motive: image(motive),
            path: image(path),
            value: image(value),
        },
        ContentNode::TelescopeTransport {
            motive,
            path,
            start,
            over,
            value,
        } => ContentNode::TelescopeTransport {
            motive: image(motive),
            path: image(path),
            start: image(start),
            over: image(over),
            value: image(value),
        },
        ContentNode::PathProduct(first, second) => {
            let first = image(first);
            ContentNode::PathProduct(first, image(second))
        },
        ContentNode::Funext(left, right) => {
            let left = image(left);
            ContentNode::Funext(left, image(right))
        },
        ContentNode::Equiv(forward, backward) => {
            let forward = image(forward);
            ContentNode::Equiv(forward, image(backward))
        },
        ContentNode::Univalence(record, forward) => {
            let record = image(record);
            ContentNode::Univalence(record, image(forward))
        },
        ContentNode::Ua {
            stratum,
            ref sides,
            forward,
            backward,
        } => {
            let forward = image(forward);
            ContentNode::Ua {
                stratum,
                sides: alloc::sync::Arc::clone(sides),
                forward,
                backward: image(backward),
            }
        },
        ContentNode::PathEquiv {
            path_type,
            forward,
            backward,
            ref evidence,
        } => ContentNode::PathEquiv {
            path_type: image(path_type),
            forward: image(forward),
            backward: image(backward),
            evidence: alloc::sync::Arc::clone(evidence),
        },
        ContentNode::Transport(path, value) => {
            let path = image(path);
            ContentNode::Transport(path, image(value))
        },
        ContentNode::Variable { .. }
        | ContentNode::Constant(_)
        | ContentNode::ListNil
        | ContentNode::Literal(_)
        | ContentNode::Base(_)
        | ContentNode::Universe { .. }
        | ContentNode::Abstract(_)
        | ContentNode::Unresolved(_)
        | ContentNode::Hole(_)
        | ContentNode::ComputationHole(_)
        | ContentNode::UnknownType
        | ContentNode::BufferType
        | ContentNode::UnknownComputationType => node.clone(),
        ContentNode::ListCons(head, tail) => ContentNode::ListCons(image(head), image(tail)),
        ContentNode::ListFold {
            element,
            result,
            list,
            on_nil,
            on_cons,
        } => ContentNode::ListFold {
            element: image(element),
            result: image(result),
            list: image(list),
            on_nil: image(on_nil),
            on_cons: image(on_cons),
        },
        ContentNode::ListCase {
            list,
            on_nil,
            on_cons,
        } => ContentNode::ListCase {
            list: image(list),
            on_nil: image(on_nil),
            on_cons: image(on_cons),
        },
        ContentNode::Tuple(ref components) => ContentNode::Tuple(
            components
                .iter()
                .map(|&component| image(component))
                .collect(),
        ),
        ContentNode::Injection(summand, body) => ContentNode::Injection(summand, image(body)),
        ContentNode::Thunk(body) => ContentNode::Thunk(image(body)),
        ContentNode::ValueLift { ref target, body } => ContentNode::ValueLift {
            target: target.clone(),
            body: image(body),
        },
        ContentNode::Lambda(body) => ContentNode::Lambda(image(body)),
        ContentNode::Application(head, argument) => {
            let head = image(head);
            ContentNode::Application(head, image(argument))
        },
        ContentNode::Return(value) => ContentNode::Return(image(value)),
        ContentNode::Bind(bound, rest) => {
            let bound = image(bound);
            ContentNode::Bind(bound, image(rest))
        },
        ContentNode::Force(value) => ContentNode::Force(image(value)),
        ContentNode::Case {
            scrutinee,
            ref branches,
        } => {
            let scrutinee = image(scrutinee);
            ContentNode::Case {
                scrutinee,
                branches: branches.iter().map(|&branch| image(branch)).collect(),
            }
        },
        ContentNode::Product(ref parts) => {
            ContentNode::Product(parts.iter().map(|&part| image(part)).collect())
        },
        ContentNode::Sum(ref parts) => {
            ContentNode::Sum(parts.iter().map(|&part| image(part)).collect())
        },
        ContentNode::List(element) => ContentNode::List(image(element)),
        ContentNode::KeptType { value, region } => ContentNode::KeptType {
            value: image(value),
            region,
        },
        ContentNode::ThunkType(body) => ContentNode::ThunkType(image(body)),
        ContentNode::TypeLift { inner, ref target } => ContentNode::TypeLift {
            inner: image(inner),
            target: target.clone(),
        },
        ContentNode::Element { code, ref target } => ContentNode::Element {
            code: image(code),
            target: target.clone(),
        },
        ContentNode::Returner {
            result,
            ref effects,
        } => {
            let result = image(result);
            let effects = effects
                .try_map_types(gandr_core_term::effect::TypeOrder::Forward, |ty| {
                    Ok::<_, core::convert::Infallible>(image(ty))
                })
                .unwrap_or_else(|never| match never {});
            ContentNode::Returner { result, effects }
        },
        ContentNode::Capability {
            ref authority,
            grade,
            region,
        } => ContentNode::Capability {
            authority: authority
                .try_map_types(gandr_core_term::effect::TypeOrder::Forward, |ty| {
                    Ok::<_, core::convert::Infallible>(image(ty))
                })
                .unwrap_or_else(|never| match never {}),
            grade,
            region,
        },
        ContentNode::Arrow { domain, codomain } => {
            let domain = image(domain);
            ContentNode::Arrow {
                domain,
                codomain: image(codomain),
            }
        },
        ContentNode::Pi { domain, codomain } => {
            let domain = image(domain);
            ContentNode::Pi {
                domain,
                codomain: image(codomain),
            }
        },
        ContentNode::Quote(quoted) => ContentNode::Quote(image(quoted)),
        ContentNode::QuoteComputation(quoted) => ContentNode::QuoteComputation(image(quoted)),
        ContentNode::StaticLambda(body) => ContentNode::StaticLambda(image(body)),
        ContentNode::StaticApplication(head, argument) => {
            let head = image(head);
            ContentNode::StaticApplication(head, image(argument))
        },
        ContentNode::ValueMark { mark, body } => ContentNode::ValueMark {
            mark,
            body: image(body),
        },
        ContentNode::ComputationMark { mark, body } => ContentNode::ComputationMark {
            mark,
            body: image(body),
        },
        ContentNode::Fixpoint { body, evidence } => ContentNode::Fixpoint {
            body: image(body),
            evidence,
        },
        ContentNode::StaticPi { domain, codomain } => {
            let domain = image(domain);
            ContentNode::StaticPi {
                domain,
                codomain: image(codomain),
            }
        },
        ContentNode::Sigma { first, second } => {
            let first = image(first);
            ContentNode::Sigma {
                first,
                second: image(second),
            }
        },
        ContentNode::ComputationElement { code, ref target } => ContentNode::ComputationElement {
            code: image(code),
            target: target.clone(),
        },
    }
}

/// A type node minted into an arena.
///
/// # Specification
/// - executable: none — the sort-tagged seat has no arena with which to certify
///   resolution.
///
/// # Adequacy
/// - hypothesis: L2 — A shared arrow is minted into a noisy arena and
///   reconstructed by content.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Minted
{
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// Where the post-order mint stands at one table entry.
///
/// # Specification
/// - executable: none — a traversal marker alone cannot establish the preceding
///   DFS transitions.
///
/// # Adequacy
/// - hypothesis: L2 — Shared-node reuse and a cycle distinguish completed from
///   open entries.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MintState
{
    /// Not reached.
    Fresh,
    /// Reached; its children are being minted.
    Open,
    /// Minted.
    Done(Minted),
}

/// One step of the post-order mint.
///
/// # Specification
/// - executable: none — an individual frame has neither the traversal stack nor
///   its state table.
///
/// # Adequacy
/// - hypothesis: L2 — The shared-arrow and refusal corpus bound post-order
///   traversal evidence.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MintFrame
{
    /// Reach the entry: open it and queue its children.
    Enter(NodeIndex),
    /// Mint the entry from its minted children.
    Exit(NodeIndex),
}

/// An entry of a table a mint reads: a de Bruijn former, or a closed node of
/// a supported table, which is its own former.
trait MintEntry
{
    /// The former the entry mints.
    ///
    /// # Specification
    /// trivial.
    fn minted_former(&self) -> &ContentNode;
}

impl MintEntry for ContentNode
{
    /// The former itself.
    ///
    /// # Specification
    /// trivial.
    fn minted_former(&self) -> &ContentNode
    {
        self
    }
}

impl MintEntry for SupportedNode
{
    /// The node's former.
    ///
    /// # Specification
    /// trivial.
    fn minted_former(&self) -> &ContentNode
    {
        self.former()
    }
}

/// Mint the type table `nodes`, rooted at its first entry, into `arena`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the root's minted node; each entry is minted once,
///   after its children.
/// - fails: as [`TypeContent::mint`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a shared arrow is reconstructed after minting; one finite
///   table for each named refusal bounds failures. Empty, dangling and
///   wrong-sort child tables add structural boundaries without claiming
///   arbitrary graphs.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
/// - witness: `content::tests::malformed_type_tables_fail_by_structure`
#[spec(ensures: |ret| match ret {
    Maybe::Present(Minted::ValueType(id)) => arena.value_type(id).is_some()
        && nodes.first().is_some_and(|node| node.minted_former().sort() == Sort::ValueType),
    Maybe::Present(Minted::CompType(id)) => arena.comp_type(id).is_some()
        && nodes.first().is_some_and(|node| node.minted_former().sort() == Sort::CompType),
    Maybe::Absent(reason) => !nodes.is_empty() || reason == seating::Absent::IllSorted,
})]
fn mint_table<Entry>(
    nodes: &[Entry],
    arena: &mut CoreArena,
    layout: &Layout,
) -> Maybe<Minted, seating::Absent>
where
    Entry: MintEntry,
{
    let mut states = alloc::vec![MintState::Fresh; nodes.len()];
    let mut frames = alloc::vec![MintFrame::Enter(NodeIndex::from(0_usize))];
    while let Some(frame) = frames.pop() {
        match frame {
            MintFrame::Enter(index) => {
                let (Some(state), Some(node)) = (
                    states.get_mut(usize::from(index)),
                    nodes.get(usize::from(index)),
                )
                else {
                    return Maybe::Absent(seating::Absent::IllSorted);
                };
                match *state {
                    MintState::Done(_) => {},
                    MintState::Open => return Maybe::Absent(seating::Absent::Cyclic),
                    MintState::Fresh => {
                        *state = MintState::Open;
                        frames.push(MintFrame::Exit(index));
                        let children = node.minted_former().children();
                        frames.extend(
                            children
                                .iter()
                                .rev()
                                .map(|(child, _)| MintFrame::Enter(child)),
                        );
                    },
                }
            },
            MintFrame::Exit(index) => {
                let Some(node) = nodes.get(usize::from(index))
                else {
                    return Maybe::Absent(seating::Absent::IllSorted);
                };
                let minted = match mint_node(node.minted_former(), &states, arena, layout) {
                    Maybe::Present(minted) => minted,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                };
                if let Some(state) = states.get_mut(usize::from(index)) {
                    *state = MintState::Done(minted);
                }
            },
        }
    }
    match states.first() {
        Some(&MintState::Done(minted)) => Maybe::Present(minted),
        Some(&(MintState::Fresh | MintState::Open)) | None => {
            Maybe::Absent(seating::Absent::IllSorted)
        },
    }
}

/// The value type minted for the entry `index`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the matching completed seat at `index`, otherwise `IllSorted`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the shared-arrow reconstruction exercises completed
///   seats; malformed child sorts are refused through the enclosing mint. Fresh
///   and open states are not claimed as direct witness coverage.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::malformed_type_tables_fail_by_structure`
#[spec(ensures: |ret| match states.get(usize::from(index)) {
    Some(&MintState::Done(Minted::ValueType(id))) => ret == Maybe::Present(id),
    _ => ret == Maybe::Absent(seating::Absent::IllSorted),
})]
fn minted_value_type(
    states: &[MintState],
    index: NodeIndex,
) -> Maybe<ValueTypeId, seating::Absent>
{
    match states.get(usize::from(index)) {
        Some(&MintState::Done(Minted::ValueType(id))) => Maybe::Present(id),
        Some(&(MintState::Done(Minted::CompType(_)) | MintState::Fresh | MintState::Open))
        | None => Maybe::Absent(seating::Absent::IllSorted),
    }
}

/// The computation type minted for the entry `index`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the matching completed seat at `index`, otherwise `IllSorted`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the shared-arrow reconstruction exercises completed
///   seats; malformed child sorts are refused through the enclosing mint. Fresh
///   and open states are not claimed as direct witness coverage.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::malformed_type_tables_fail_by_structure`
#[spec(ensures: |ret| match states.get(usize::from(index)) {
    Some(&MintState::Done(Minted::CompType(id))) => ret == Maybe::Present(id),
    _ => ret == Maybe::Absent(seating::Absent::IllSorted),
})]
fn minted_comp_type(
    states: &[MintState],
    index: NodeIndex,
) -> Maybe<CompTypeId, seating::Absent>
{
    match states.get(usize::from(index)) {
        Some(&MintState::Done(Minted::CompType(id))) => Maybe::Present(id),
        Some(&(MintState::Done(Minted::ValueType(_)) | MintState::Fresh | MintState::Open))
        | None => Maybe::Absent(seating::Absent::IllSorted),
    }
}

/// Mint one type entry whose children are all minted.
///
/// # Specification
/// - requires: every child of `node` is `Done` in `states`.
/// - ensures: the type node of `node`'s former over its children's minted
///   nodes.
/// - fails: `Unresolved` for an unresolved entry, `Unplaced` for a reference
///   the program does not hold, `IllSorted` for a child of the wrong sort, and
///   `Unseatable` for a former that holds a term.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the shared-arrow graph checks reconstruction; named
///   refusal tables and wrong-sort children bound failures. The predicate
///   checks seat resolution, result sort and refusal class, not a duplicate
///   arena encoding.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
/// - witness: `content::tests::malformed_type_tables_fail_by_structure`
/// - witness: `content::tests::every_dependent_former_mints_back_as_its_own_table`
/// - witness: `content::tests::a_data_type_mints_only_unapplied`
#[spec(
    requires: node.children().iter().all(|(child, _)| matches!(states.get(usize::from(child)), Some(&MintState::Done(_)))),
    ensures: |ret| match ret {
        Maybe::Present(Minted::ValueType(id)) => node.sort() == Sort::ValueType && arena.value_type(id).is_some(),
        Maybe::Present(Minted::CompType(id)) => node.sort() == Sort::CompType && arena.comp_type(id).is_some(),
        Maybe::Absent(reason) => if matches!(*node, ContentNode::Unresolved(_)) {
            reason == seating::Absent::Unresolved
        } else if matches!(node.sort(), Sort::Value | Sort::Computation)
            || matches!(*node, ContentNode::Element { .. } | ContentNode::ComputationElement { .. } | ContentNode::PathUniverse(..) | ContentNode::PathType { .. } | ContentNode::FlowType { .. } | ContentNode::RunType(_) | ContentNode::PrefixType(_))
            || matches!(node,ContentNode::Data { arguments,.. } if !arguments.is_empty()) {
            reason == seating::Absent::Unseatable
        } else {
            reason == seating::Absent::IllSorted || (matches!(*node, ContentNode::Abstract(_) | ContentNode::Data { .. }) && reason == seating::Absent::Unplaced)
        },
    },
)]
fn mint_node(
    node: &ContentNode,
    states: &[MintState],
    arena: &mut CoreArena,
    layout: &Layout,
) -> Maybe<Minted, seating::Absent>
{
    let ill_sorted = Maybe::Absent(seating::Absent::IllSorted);
    match *node {
        ContentNode::RecordType(ref fields) => {
            let mut minted = BTreeMap::new();
            for (label, &field) in fields {
                let Maybe::Present(field) = minted_value_type(states, field)
                else {
                    return ill_sorted;
                };
                let _previous = minted.insert(label.clone(), field);
            }
            Maybe::Present(Minted::ValueType(arena.value_type_record(minted)))
        },
        ContentNode::Data {
            ref declaration,
            ref arguments,
        } => {
            if !arguments.is_empty() {
                return Maybe::Absent(seating::Absent::Unseatable);
            }
            match place(layout, declaration) {
                Maybe::Present(position) => Maybe::Present(Minted::ValueType(
                    arena.value_type_data(position, Vec::new()),
                )),
                Maybe::Absent(reason) => Maybe::Absent(reason),
            }
        },
        ContentNode::Stack { input, output } => match (
            minted_comp_type(states, input),
            minted_comp_type(states, output),
        ) {
            (Maybe::Present(input), Maybe::Present(output)) => {
                Maybe::Present(Minted::ValueType(arena.value_type_stack(input, output)))
            },
            _ => ill_sorted,
        },
        ContentNode::WithType(ref components) => {
            let mut minted = Vec::with_capacity(components.len());
            for &component in components {
                let Maybe::Present(component) = minted_comp_type(states, component)
                else {
                    return ill_sorted;
                };
                minted.push(component);
            }
            Maybe::Present(Minted::CompType(arena.comp_type_with(&minted)))
        },
        ContentNode::Base(base) => Maybe::Present(Minted::ValueType(arena.value_type_base(base))),
        ContentNode::Universe { sort, ref level } => Maybe::Present(Minted::ValueType(
            arena.value_type_universe(sort, level.clone()),
        )),
        ContentNode::Abstract(ref reference) => match place(layout, reference) {
            Maybe::Present(position) => {
                Maybe::Present(Minted::ValueType(arena.value_type_abstract(position)))
            },
            Maybe::Absent(reason) => Maybe::Absent(reason),
        },
        ContentNode::Product(ref parts) | ContentNode::Sum(ref parts) => {
            let mut minted = Vec::with_capacity(parts.len());
            for &part in parts {
                let Maybe::Present(part) = minted_value_type(states, part)
                else {
                    return ill_sorted;
                };
                minted.push(part);
            }
            Maybe::Present(Minted::ValueType(
                if matches!(*node, ContentNode::Product(_)) {
                    arena.value_type_product(&minted)
                }
                else {
                    arena.value_type_sum(&minted)
                },
            ))
        },
        ContentNode::List(element) => match minted_value_type(states, element) {
            Maybe::Present(element) => {
                Maybe::Present(Minted::ValueType(arena.value_type_list(element)))
            },
            Maybe::Absent(_) => ill_sorted,
        },
        ContentNode::KeptType { value, region } => match minted_value_type(states, value) {
            Maybe::Present(value) => {
                Maybe::Present(Minted::ValueType(arena.value_type_kept(value, region)))
            },
            Maybe::Absent(_) => ill_sorted,
        },
        ContentNode::StaticPi { domain, codomain } => {
            match (
                minted_value_type(states, domain),
                minted_value_type(states, codomain),
            ) {
                (Maybe::Present(domain), Maybe::Present(codomain)) => Maybe::Present(
                    Minted::ValueType(arena.value_type_static_pi(domain, codomain)),
                ),
                _ => ill_sorted,
            }
        },
        ContentNode::Sigma { first, second } => {
            match (
                minted_value_type(states, first),
                minted_value_type(states, second),
            ) {
                (Maybe::Present(first), Maybe::Present(second)) => {
                    Maybe::Present(Minted::ValueType(arena.value_type_sigma(first, second)))
                },
                _ => ill_sorted,
            }
        },
        ContentNode::ThunkType(body) => match minted_comp_type(states, body) {
            Maybe::Present(body) => Maybe::Present(Minted::ValueType(arena.value_type_thunk(body))),
            Maybe::Absent(_) => ill_sorted,
        },
        ContentNode::TypeLift { inner, ref target } => match minted_value_type(states, inner) {
            Maybe::Present(inner) => Maybe::Present(Minted::ValueType(
                arena.value_type_lift(inner, target.clone()),
            )),
            Maybe::Absent(_) => ill_sorted,
        },
        ContentNode::Returner {
            result,
            ref effects,
        } => {
            let Maybe::Present(result) = minted_value_type(states, result)
            else {
                return ill_sorted;
            };
            let effects = effects.try_relocate(|ty| match minted_value_type(states, ty) {
                Maybe::Present(ty) => Ok(ty),
                Maybe::Absent(reason) => Err(reason),
            });
            match effects {
                Ok(effects) => Maybe::Present(Minted::CompType(
                    arena.comp_type_returner_with_effects(result, effects),
                )),
                Err(reason) => Maybe::Absent(reason),
            }
        },
        ContentNode::SessionType(ref session) => {
            match session.try_relocate(|ty| match minted_value_type(states, ty) {
                Maybe::Present(ty) => Ok(ty),
                Maybe::Absent(reason) => Err(reason),
            }) {
                Ok(session) => Maybe::Present(Minted::ValueType(arena.value_type_session(session))),
                Err(reason) => Maybe::Absent(reason),
            }
        },
        ContentNode::Capability {
            ref authority,
            grade,
            region,
        } => {
            let authority = authority.try_relocate(|ty| match minted_value_type(states, ty) {
                Maybe::Present(ty) => Ok(ty),
                Maybe::Absent(reason) => Err(reason),
            });
            match authority {
                Ok(authority) => Maybe::Present(Minted::ValueType(
                    arena.value_type_capability(authority, grade, region),
                )),
                Err(reason) => Maybe::Absent(reason),
            }
        },
        ContentNode::Arrow { domain, codomain } => {
            match (
                minted_value_type(states, domain),
                minted_comp_type(states, codomain),
            ) {
                (Maybe::Present(domain), Maybe::Present(codomain)) => {
                    Maybe::Present(Minted::CompType(arena.comp_type_arrow(domain, codomain)))
                },
                _ => ill_sorted,
            }
        },
        ContentNode::Pi { domain, codomain } => {
            match (
                minted_value_type(states, domain),
                minted_comp_type(states, codomain),
            ) {
                (Maybe::Present(domain), Maybe::Present(codomain)) => {
                    Maybe::Present(Minted::CompType(arena.comp_type_pi(domain, codomain)))
                },
                _ => ill_sorted,
            }
        },
        ContentNode::UnknownType => Maybe::Present(Minted::ValueType(arena.value_type_unknown())),
        ContentNode::BufferType => Maybe::Present(Minted::ValueType(arena.value_type_buffer())),
        ContentNode::UnknownComputationType => {
            Maybe::Present(Minted::CompType(arena.comp_type_unknown()))
        },
        ContentNode::Unresolved(_) => Maybe::Absent(seating::Absent::Unresolved),
        ContentNode::PathUniverse(..)
        | ContentNode::PathType { .. }
        | ContentNode::FlowType { .. }
        | ContentNode::RunType(_)
        | ContentNode::PrefixType(_)
        | ContentNode::SessionRelated { .. }
        | ContentNode::Stay(_)
        | ContentNode::Then(..)
        | ContentNode::FlowProduct(..)
        | ContentNode::Forward(_)
        | ContentNode::FunctionFlow(..)
        | ContentNode::Recorded(_)
        | ContentNode::Ride { .. }
        | ContentNode::Here(_)
        | ContentNode::Returned(_)
        | ContentNode::Nested(_)
        | ContentNode::Run(_)
        | ContentNode::ElementTransport { .. }
        | ContentNode::TelescopeTransport { .. }
        | ContentNode::Constructor { .. }
        | ContentNode::Record(_)
        | ContentNode::DataCase { .. }
        | ContentNode::RecordProjection(..)
        | ContentNode::TupleProjection(..)
        | ContentNode::Reify(_)
        | ContentNode::Perform { .. }
        | ContentNode::Session(_)
        | ContentNode::Memory(_)
        | ContentNode::Handle { .. }
        | ContentNode::Exercise { .. }
        | ContentNode::Scope { .. }
        | ContentNode::Resume(..)
        | ContentNode::Abandon(_)
        | ContentNode::Split(..)
        | ContentNode::DependentSplit { .. }
        | ContentNode::Reset(_)
        | ContentNode::Shift(_)
        | ContentNode::With(..)
        | ContentNode::Ascribe { .. }
        | ContentNode::ValueAscribe { .. }
        | ContentNode::Project(..)
        | ContentNode::PrimitiveValue(_)
        | ContentNode::Primitive(..)
        | ContentNode::PathRefl(_)
        | ContentNode::PathProduct(..)
        | ContentNode::Funext(..)
        | ContentNode::Equiv(..)
        | ContentNode::Univalence(..)
        | ContentNode::Ua { .. }
        | ContentNode::PathEquiv { .. }
        | ContentNode::Transport(..)
        | ContentNode::Element { .. }
        | ContentNode::ComputationElement { .. }
        | ContentNode::Variable { .. }
        | ContentNode::Constant(_)
        | ContentNode::ListNil
        | ContentNode::ListCons(..)
        | ContentNode::ListFold { .. }
        | ContentNode::ListCase { .. }
        | ContentNode::Literal(_)
        | ContentNode::Tuple(_)
        | ContentNode::Injection(..)
        | ContentNode::Thunk(_)
        | ContentNode::ValueLift { .. }
        | ContentNode::Quote(_)
        | ContentNode::QuoteComputation(_)
        | ContentNode::StaticLambda(_)
        | ContentNode::StaticApplication(..)
        | ContentNode::Lambda(_)
        | ContentNode::Application(..)
        | ContentNode::Return(_)
        | ContentNode::Bind(..)
        | ContentNode::Force(_)
        | ContentNode::Case { .. }
        | ContentNode::Hole(_)
        | ContentNode::ValueMark { .. }
        | ContentNode::ComputationHole(_)
        | ContentNode::ComputationMark { .. }
        | ContentNode::Fixpoint { .. } => Maybe::Absent(seating::Absent::Unseatable),
    }
}

/// The admission position the item `reference` names takes in `layout`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the position of the item whose own reference is `reference`.
/// - provides: `Unplaced` when no item of the program carries it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — a missing abstract reference is refused; repeated keys
///   and skipped positions distinguish successful relocation by occurrence.
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
/// - witness: `content::tests::abstract_types_relocate_by_key_and_occurrence`
#[spec(ensures: |ret| match ret {
        | Maybe::Present(position) => layout
            .items
            .iter()
            .zip(&layout.references)
            .any(|(item, named)| item.declaration().constant() == position && named == reference),
        | Maybe::Absent(reason) => {
            reason == seating::Absent::Unplaced
                && !layout.references.iter().any(|named| named == reference)
        },
    })]
fn place(
    layout: &Layout,
    reference: &Reference,
) -> Maybe<gandr_kernel_term::ConstantIndex, seating::Absent>
{
    match layout.ordinal_of(reference) {
        Maybe::Present(ordinal) => layout
            .items
            .get(usize::from(ordinal))
            .map_or(Maybe::Absent(seating::Absent::Unplaced), |item| {
                Maybe::Present(item.declaration().constant())
            }),
        Maybe::Absent(_) => Maybe::Absent(seating::Absent::Unplaced),
    }
}

#[cfg(test)]
mod tests;
