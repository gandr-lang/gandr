//! The content of an item: its roots over the node form of
//! `gandr-core-content`.
//!
//! The node form, its tables, its projection and its mint live in that crate.
//! This module adds the roots of each declaration and the encoding of an
//! item. The cache codec writes both with the tags below.
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
//! Checkpoint sets use `GCKPT\0\0\x19`; programs use `GPROG\0\0\x0d`. Their
//! identities bind the checker, native declaration categories, effect and
//! control content, support queries and refusal vocabulary. Identities of
//! another version are rejected rather than reusing answers from a different
//! fragment. Static family, universe and native-former round-trip witnesses
//! exercise their distinct tags and payloads.
//!
//! **Choice.** Preserve native classifiers, maps and candidate evidence as
//! content instead of caching a certificate verdict. Structural path conversion
//! may erase evidence, but checkpoint identity must not. **Reversal.**
//! Persisting higher fields or guarded List inhabitants requires its own
//! versioned content vocabulary and validated dependency support; none is
//! inferred from a native path entry. The directed family and the bridge type
//! persist under their own tags, below.
//!
//! # Native declaration content and support
//!
//! A declaration's roots are `DeclarationRoots::Value`,
//! `DeclarationRoots::Data`, `DeclarationRoots::Abstract` or
//! `DeclarationRoots::World`; data retains the kind, every parameter and every
//! constructor field, and an abstract type its kind, its representation, the
//! extent of its seal, the component its seal names, the mobility its
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
//! A located item is content like any other. A world form and a world type
//! name their world by the reference of its declaration ([`WorldContent`]),
//! a world declaration's roots are the row it requires, and a value
//! declaration's roots carry the entry it states. What the world register
//! answers a judgement beyond that is support: the home and the spending of
//! each constant it reads, and the entry it resolves to under the host's
//! grant.
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
//! edges. Decoding refuses duplicate or out-of-order names and an empty row
//! under `0x70`;
//! `content::tests::effect_rows_round_trip_without_losing_operation_types`
//! round-trips a row's operation types, and `codec`'s readers name the
//! refusals' witnesses. The List former and its control content use the
//! following cache tags, independent of kernel artifact tags.
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
//! payloads. A control table of any sort can be minted into another arena;
//! the mint copies the content and invents no runtime term graph.
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
//! edges and its labels inline. Flow and run classifiers hold terms, and
//! they seat as any other former does.
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
use gandr_core_content::ArenaNode;
use gandr_core_content::ChildPosition;
use gandr_core_content::ContentNode;
use gandr_core_content::DataRoots;
use gandr_core_content::Discovery;
use gandr_core_content::Encoder;
use gandr_core_content::NodeIndex;
use gandr_core_content::Opacity;
use gandr_core_content::Reference;
use gandr_core_content::Resolver as _;
use gandr_core_content::Sort;
use gandr_core_content::SupportedNode;
use gandr_core_content::TypeContent;
use gandr_core_content::WorldContent;
use gandr_core_content::seating;
use gandr_core_content::tabled;
use gandr_core_term::CoreArena;
use gandr_core_term::support::PlacementError;
use gandr_core_term::support::Thinning;
use quenchant_shape::shape::Maybe;

use crate::region::Layout;
use crate::region::Program;

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

/// Where an arena node sits in the table of the item that reached it, beside
/// the place the item's walk discovered it at.
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
pub struct Sites(BTreeMap<ArenaNode, (NodeIndex, Discovery)>);

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
        Some(&(index, _)) => ret == Maybe::Present(index),
        None => ret == Maybe::Absent(site::Absent::Unreached),
    })]
    pub(crate) fn of(
        &self,
        node: ArenaNode,
    ) -> Maybe<NodeIndex, site::Absent>
    {
        match self.0.get(&node) {
            Some(&(index, _)) => Maybe::Present(index),
            None => Maybe::Absent(site::Absent::Unreached),
        }
    }

    /// The place the item's walk discovered `node` at, when it reached it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn discovery(
        &self,
        node: ArenaNode,
    ) -> Maybe<Discovery, site::Absent>
    {
        match self.0.get(&node) {
            Some(&(_, discovery)) => Maybe::Present(discovery),
            None => Maybe::Absent(site::Absent::Unreached),
        }
    }

    /// The reached arena nodes, in the order the item's walk discovered them:
    /// the node at each [`Discovery`].
    ///
    /// # Specification
    /// - ensures: each reached node once, ascending by its discovery.
    /// - panics: none.
    /// - executable: none — the clause is the sort this body runs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a failure seated from its checkpoint places each node
    ///   it names through this walk.
    /// - witness: `failure::tests::a_failure_seats_at_the_nodes_it_names`
    ///
    /// # Cost
    /// - allocation: the list of reached arena nodes, growth within the item
    pub(crate) fn walk(&self) -> Vec<ArenaNode>
    {
        let mut walk: Vec<(Discovery, ArenaNode)> = self
            .0
            .iter()
            .map(|(&node, &(_, discovery))| (discovery, node))
            .collect();
        walk.sort_unstable();
        walk.into_iter().map(|(_, node)| node).collect()
    }

    /// How many of the reached nodes the arena minted at or after `mark`.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    pub(crate) fn minted_since(
        &self,
        mark: gandr_core_term::ArenaWatermark,
    ) -> gandr_kernel_term::ArenaLength
    {
        self.0
            .keys()
            .filter(|&&node| {
                let minted = match node {
                    ArenaNode::Value(id) => mark.of_value(id),
                    ArenaNode::Computation(id) => mark.of_computation(id),
                    ArenaNode::ValueType(id) => mark.of_value_type(id),
                    ArenaNode::CompType(id) => mark.of_comp_type(id),
                };
                matches!(minted, gandr_core_term::Minted::Since)
            })
            .count()
            .into()
    }
}

/// A stated entry as content: its home, then the world of each capability in
/// the order the entry names them.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct EntryRoots
{
    /// The world the body is judged at.
    pub home: WorldContent,
    /// The world each capability migrates to.
    pub capabilities: Vec<WorldContent>,
}

impl EntryRoots
{
    /// The content of `entry`, each position resolved through `layout`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the roots of the entry, growth within the entry
    pub(crate) fn of(
        layout: &Layout,
        entry: &gandr_core_checker::worlds::Entry,
    ) -> Self
    {
        Self {
            home: WorldContent::of(layout, entry.home()),
            capabilities: entry
                .capabilities()
                .iter()
                .map(|&world| WorldContent::of(layout, world))
                .collect(),
        }
    }
}

/// A world declaration's roots: the row that code at the world performs in,
/// its operation types in the table's indices.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct WorldRoots
{
    /// The row the world requires.
    pub row: gandr_core_term::effect::EffectRow<NodeIndex>,
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
///
/// # Cost
/// - allocation: the rules as content, growth within the operation
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
    /// binders it is quantified over, the stages its calls supply, the
    /// model slots they omit and the entry it states.
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
        /// `f[.i = j]`, at the node of the value the call forces; empty for a
        /// declaration whose calls supply none. The checker holds a call to
        /// it, so a changed supply is changed content.
        supplies: Vec<(
            NodeIndex,
            gandr_kernel_term::StageBinder,
            gandr_kernel_term::Stage,
        )>,
        /// Each model slot a call of the body omits whose every hole the body
        /// reaches, with the candidates the checker resolves it among; empty
        /// for a declaration whose calls omit none. A candidate in scope
        /// decides the verdict without the body naming it, so a changed
        /// candidate is changed content.
        models: Vec<ModelRoots>,
        /// The entry the declaration states, or why it states none. Its home
        /// is the world its body is judged at, and its capabilities are the
        /// migrations the body may make, so a changed entry is changed
        /// content.
        entry: Maybe<EntryRoots, gandr_core_checker::entry::Absent>,
    },
    /// A complete nominal signature.
    Data(DataRoots),
    /// A sealed abstract type.
    Abstract(AbstractRoots),
    /// A world declaration: the row that code at the world performs in.
    World(WorldRoots),
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
    /// The site that mints the atom, as the item's table names it: the
    /// component of the ascription the site seals, and the ascription the
    /// first of the table ([`local_site`]).
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

/// The roots of a model slot a call omits: the node of each hole the call
/// nominated, numbered by the body's walk, the code of each type the slot fixes
/// a sort to, and each candidate's components and codes of those sorts, each a
/// value root of its own.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ModelRoots
{
    /// The hole nominated for each component, in signature order.
    pub holes: Vec<NodeIndex>,
    /// The code of the type the slot fixes each fixed sort to, in the order
    /// of the sorts' names.
    pub fixed: Vec<NodeIndex>,
    /// Each candidate's components, in the order the lowering met the
    /// candidates; each holds one component per hole, then its own code of
    /// each fixed sort.
    pub candidates: Vec<Vec<NodeIndex>>,
}

impl DeclarationRoots
{
    /// Each root and its required family, in discovery order.
    ///
    /// # Specification
    /// - ensures: value signature before body, then each model slot's fixed
    ///   codes and each of its candidates' components and codes, in slot and
    ///   candidate order, all nominal roots in order as [`DataRoots::sorted`]
    ///   sorts them, an abstract type's kind before its representation and both
    ///   before its interface's relation, reflexivity and law, each type of a
    ///   world's row in the row's order, or none for a codata declaration.
    /// - executable: none — the return is an opaque iterator.
    ///
    /// # Clause cost
    /// - bound: one step per root the declaration holds: its value roots, each
    ///   model slot's fixed codes and its candidates' roots and its nominal
    ///   roots; nothing outside the roots is read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — persistence rejects ill-sorted and reordered native
    ///   roots.
    /// - witness: `tests::native_formers::native_checkpoint_round_trip_and_signature_invalidation`
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = (NodeIndex, Sort)> + Clone + '_
    {
        let (values, data, models) = match *(self) {
            Self::Value {
                ref signature,
                ref body,
                ref models,
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
                models.as_slice(),
            ),
            Self::Data(ref roots) => ([None; 5], Some(roots), [].as_slice()),
            Self::World(_) | Self::Codata => ([None; 5], None, [].as_slice()),
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
                    [].as_slice(),
                )
            },
        };
        let row = if let Self::World(ref roots) = *self {
            Some(&roots.row)
        }
        else {
            None
        };
        values
            .into_iter()
            .flatten()
            .chain(
                models
                    .iter()
                    .flat_map(|slot| slot.fixed.iter().chain(slot.candidates.iter().flatten()))
                    .map(|&root| (root, Sort::Value)),
            )
            .chain(data.into_iter().flat_map(DataRoots::sorted))
            .chain(
                row.into_iter()
                    .flat_map(|row| row.types().map(|root| (root, Sort::ValueType))),
            )
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
    ///
    /// # Cost
    /// - allocation: the renumbered roots, growth within the roots
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
                ref models,
                ref entry,
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
                models: models
                    .iter()
                    .map(|slot| ModelRoots {
                        holes: slot.holes.iter().map(|&hole| image(hole)).collect(),
                        fixed: slot.fixed.iter().map(|&code| image(code)).collect(),
                        candidates: slot
                            .candidates
                            .iter()
                            .map(|components| components.iter().map(|&root| image(root)).collect())
                            .collect(),
                    })
                    .collect(),
                entry: entry.clone(),
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
            Self::World(ref roots) => Self::World(WorldRoots {
                row: roots
                    .row
                    .try_map_types(gandr_core_term::effect::TypeOrder::Forward, |ty| {
                        Ok::<_, core::convert::Infallible>(image(ty))
                    })
                    .unwrap_or_else(|never| match never {}),
            }),
            Self::Codata => Self::Codata,
        }
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
    ///
    /// # Cost
    /// - allocation: the set of references beneath the roots, growth within the
    ///   table
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
    ///
    /// # Cost
    /// - allocation: the roots of every constructor signature, growth within
    ///   the signature
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
    ///
    /// # Cost
    /// - allocation: the factored table and its roots, growth within the table
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
    ///
    /// # Cost
    /// - allocation: the de Bruijn table, growth within the table
    #[spec(ensures: |ret| ret.as_ref().is_err() || self.nodes.get(usize::from(root)).is_none_or(|node|
        ret.as_ref().is_ok_and(|table| table.first().map(ContentNode::sort) == Some(node.sort()))))]
    #[inline]
    pub fn debruijn(
        &self,
        root: NodeIndex,
    ) -> Result<Vec<ContentNode>, PlacementError>
    {
        let empty = Thinning::empty();
        gandr_core_content::expand(&self.nodes, root, self.placement_of(root).unwrap_or(&empty))
    }

    /// The support of the first declaration root naming the entry `root`.
    ///
    /// # Specification
    /// - ensures: the placement beside the first root equal to `root`, in
    ///   [`DeclarationRoots::iter`] order; none when no root names it.
    /// - panics: none.
    /// - executable: none — the clause is the search this body runs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each open root projects under its own support, and a
    ///   signature renumbers under the support of the first root.
    /// - witness: `content::tests::open_roots_project_under_their_own_supports`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    fn placement_of(
        &self,
        root: NodeIndex,
    ) -> Option<&Thinning>
    {
        self.declaration
            .iter()
            .zip(&self.placements)
            .find_map(|((named, _), placement)| (named == root).then_some(placement))
    }

    /// The content under the entry `root`, as a table of its own: the name of
    /// the term or the type at `root`, whatever item holds it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the table of every node reachable from `root`, renumbered by
    ///   discovery from `root` alone, each hole named by its place under
    ///   `root`, with the support of the first declaration root naming it, else
    ///   the empty support; so it equals the content [`of_node`] gives the node
    ///   in its arena.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an interleaved signature is compared with encoding
    ///   its root alone, and a term with a lambda and a bind with the content
    ///   of its mint.
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    /// - witness: `content::tests::alpha_equal_terms_mint_to_one_name`
    /// - witness: `content::tests::a_root_names_its_holes_by_their_place_under_it`
    ///
    /// # Cost
    /// - allocation: the table under the root, growth within the table
    #[spec(ensures: |ret| self.nodes.get(usize::from(root)).is_none_or(|node|
        ret.nodes().first().map(SupportedNode::sort) == Some(node.sort())))]
    #[inline]
    #[must_use]
    pub fn rooted(
        &self,
        root: NodeIndex,
    ) -> TypeContent
    {
        let numbered =
            gandr_core_content::number(NodeIndex::from(self.nodes.len()), [root], |old| {
                self.nodes.get(usize::from(old)).cloned()
            });
        TypeContent::from_parts(
            gandr_core_content::named_holes(numbered.nodes),
            self.placement_of(root).cloned().unwrap_or_default(),
        )
    }

    /// The content of these parts, as the decoder reassembles it.
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
        }
    }

    /// Whether the item may be adopted and persisted: every node resolved,
    /// and no codata declaration.
    ///
    /// # Specification
    /// - ensures: [`Opacity::Opaque`] for a codata declaration, else opaque
    ///   exactly when a root carries an unresolved node beneath it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unresolved id beneath the body makes its item
    ///   opaque, and an item of a located program is transparent.
    /// - witness: `content::tests::an_item_of_a_located_program_is_transparent_3381`
    /// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
    #[spec(ensures: |ret| (ret == Opacity::Opaque)
        == (matches!(self.declaration, DeclarationRoots::Codata) || self.declaration.iter().any(|(root, _)|
            self.nodes.get(usize::from(root)).is_some_and(|node| node.opacity() == Opacity::Opaque))))]
    #[inline]
    #[must_use]
    pub fn opacity(&self) -> Opacity
    {
        let opaque = matches!(self.declaration, DeclarationRoots::Codata)
            || self.declaration.iter().any(|(root, _)| {
                self.nodes
                    .get(usize::from(root))
                    .is_some_and(|node| node.opacity() == Opacity::Opaque)
            });
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
    /// - ensures: the content [`ItemContent::rooted`] gives the signature root,
    ///   so it equals the content [`of_node`] gives the signature in its arena.
    /// - provides: None for an unsigned value or a nominal declaration.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an interleaved signature is compared with
    ///   independently encoding its root.
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[spec(ensures: |ret| match (&self.declaration, ret.as_ref()) {
        (&DeclarationRoots::Value { signature: Maybe::Present(root), .. }, Some(content)) =>
            content.nodes().first().map(SupportedNode::sort) == self.nodes.get(usize::from(root)).map(SupportedNode::sort),
        (&DeclarationRoots::Value { signature: Maybe::Present(_), .. }, None) => false,
        (&(DeclarationRoots::Value { signature: Maybe::Absent(_), .. } | DeclarationRoots::Data(_) | DeclarationRoots::Abstract(_) | DeclarationRoots::World(_) | DeclarationRoots::Codata), found) => found.is_none(),
    })]
    pub(crate) fn signature_type(&self) -> Option<TypeContent>
    {
        match self.declaration {
            DeclarationRoots::Value {
                signature: Maybe::Present(root),
                ..
            } => Some(self.rooted(root)),
            DeclarationRoots::Value {
                signature: Maybe::Absent(_),
                ..
            }
            | DeclarationRoots::Data(_)
            | DeclarationRoots::Abstract(_)
            | DeclarationRoots::World(_)
            | DeclarationRoots::Codata => None,
        }
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
///   nominal roots follow parameter and constructor order; a value
///   declaration's stated entry and a world's row are content. Every arena node
///   the walk reached has a site, the supported node it became.
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
///
/// # Cost
/// - allocation: the table and the roots of the item, growth within the item
#[spec(ensures: |ret| ret.sites.0.values().all(|&(index, _)| usize::from(index) < ret.content.nodes.len())
    && ret.content.placements.len() == ret.content.declaration.iter().count()
    && match layout.items.get(usize::from(ordinal)) {
        Some(item) => layout.references.get(usize::from(ordinal)) == Some(&ret.content.reference)
            && { let (matched_left_value, matched_right_value) = (item.declaration().content(),&ret.content.declaration);
if let gandr_core_checker::DeclarationContent::Value { ref signature,ref body } = *matched_left_value && let DeclarationRoots::Value { signature:ref actual_signature,body:ref actual_body,laws:ref actual_laws,rules:ref actual_rules,stages:ref actual_stages,supplies:ref actual_supplies,models:ref actual_models,entry:ref actual_entry } = *matched_right_value { signature.map(|ty| ret.sites.0.get(&ArenaNode::ValueType(ty)).map(|&(index, _)| index)) == actual_signature.map(Some)
                    && item.declaration().entry().map(|entry| EntryRoots::of(layout, entry)) == *actual_entry
                    && body.map(|value| ret.sites.0.get(&ArenaNode::Value(value)).map(|&(index, _)| index)) == actual_body.map(Some)
                    && item.declaration().laws().iter().map(|&law| layout.resolve(law)).eq(actual_laws.iter().cloned())
                    && *actual_rules == rule_roots(layout, item.declaration().operation_rules())
                    && actual_stages.as_slice() == item.declaration().stages()
                    && actual_supplies.iter().copied().eq(item.declaration().supplies().iter().filter_map(|supply| ret.sites.0.get(&ArenaNode::Value(supply.head)).map(|&(head, _)| (head, supply.binder, supply.stage))))
                    && actual_models.len() <= item.declaration().models().len() }
 else if let gandr_core_checker::DeclarationContent::Data(ref signature) = *matched_left_value && let DeclarationRoots::Data(ref roots) = *matched_right_value { ret.sites.0.get(&ArenaNode::ValueType(signature.kind())).map(|&(index, _)| index) == Some(roots.kind)
                    && signature.parameters().iter().map(|&ty| ret.sites.0.get(&ArenaNode::ValueType(ty)).map(|&(index, _)| index)).eq(roots.parameters.iter().copied().map(Some))
                    && signature.constructors().len() == roots.constructors.len()
                    && signature.constructors().iter().zip(&roots.constructors).all(|(fields,roots)| fields.iter().map(|&ty| ret.sites.0.get(&ArenaNode::ValueType(ty)).map(|&(index, _)| index)).eq(roots.iter().copied().map(Some))) }
 else if let gandr_core_checker::DeclarationContent::Abstract(sealed) = *matched_left_value && let DeclarationRoots::Abstract(roots) = *matched_right_value { ret.sites.0.get(&ArenaNode::ValueType(sealed.kind())).map(|&(index, _)| index) == Some(roots.kind)
                    && ret.sites.0.get(&ArenaNode::ValueType(sealed.representation())).map(|&(index, _)| index) == Some(roots.representation)
                    && roots.extent == sealed.extent() && roots.site == local_site(sealed.site()) && roots.mobility == sealed.mobility()
                    && match (sealed.interface(), roots.interface) {
                        (Maybe::Present(interface), Maybe::Present(actual)) => ret.sites.0.get(&ArenaNode::Value(interface.relation())).map(|&(index, _)| index) == Some(actual.relation)
                            && ret.sites.0.get(&ArenaNode::Value(interface.reflexivity())).map(|&(index, _)| index) == Some(actual.reflexivity)
                            && interface.law().map(|law| ret.sites.0.get(&ArenaNode::Value(law)).map(|&(index, _)| index)) == actual.law.map(Some),
                        (Maybe::Absent(_), Maybe::Absent(_)) => true,
                        (Maybe::Present(_), Maybe::Absent(_)) | (Maybe::Absent(_), Maybe::Present(_)) => false,
                    } }
 else { matches!((matched_left_value, matched_right_value), (gandr_core_checker::DeclarationContent::World(_), DeclarationRoots::World(_)) | (gandr_core_checker::DeclarationContent::Codata(_), DeclarationRoots::Codata)) }
},
        None => ret.content.reference == Reference::Unoccupied
            && matches!(ret.content.declaration,DeclarationRoots::Value {signature:Maybe::Absent(signature::Absent::Unsigned),body:Maybe::Absent(body::Absent::Hole),ref laws,ref rules,ref stages,ref supplies,ref models,entry:Maybe::Absent(_)} if laws.is_empty() && rules.is_empty() && stages.is_empty() && supplies.is_empty() && models.is_empty())
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
                models: Vec::new(),
                entry: Maybe::Absent(gandr_core_checker::entry::Absent::Unstated),
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
                    models: Vec::new(),
                    entry: item
                        .declaration()
                        .entry()
                        .map(|entry| EntryRoots::of(layout, entry)),
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
                        site: local_site(sealed.site()),
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
                gandr_core_checker::DeclarationContent::World(ref requirement) => {
                    DeclarationRoots::World(WorldRoots {
                        row: requirement
                            .try_relocate(|ty| {
                                Ok::<_, core::convert::Infallible>(
                                    encoder.discover(ArenaNode::ValueType(ty)),
                                )
                            })
                            .unwrap_or_else(|never| match never {}),
                    })
                },
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
    // own; a head the body no longer reaches supplies nothing. A model slot's
    // holes are numbered the same way, and a slot the body no longer reaches
    // whole is left out; each candidate's components are roots of their own.
    let mut declaration = declaration;
    if let DeclarationRoots::Value {
        ref mut supplies,
        ref mut models,
        ..
    } = declaration
        && let Some(item) = layout.items.get(usize::from(ordinal))
    {
        supplies.extend(item.declaration().supplies().iter().filter_map(|supply| {
            encoder
                .seen
                .get(&ArenaNode::Value(supply.head))
                .map(|&raw| (raw, supply.binder, supply.stage))
        }));
        let met: BTreeMap<gandr_core_term::hole::HoleId, NodeIndex> = encoder
            .seen
            .iter()
            .filter_map(|(&node, &raw)| match node {
                ArenaNode::Value(at) => match arena.value(at) {
                    Some(&gandr_core_term::Value::Hole(hole)) => Some((hole, raw)),
                    _ => None,
                },
                ArenaNode::Computation(_) | ArenaNode::ValueType(_) | ArenaNode::CompType(_) => {
                    None
                },
            })
            .collect();
        for slot in item.declaration().models() {
            let Some(holes) = slot
                .holes
                .iter()
                .map(|hole| met.get(hole).copied())
                .collect::<Option<Vec<NodeIndex>>>()
            else {
                continue;
            };
            let fixed = slot
                .fixed
                .iter()
                .map(|&code| encoder.discover(ArenaNode::Value(code)))
                .collect();
            let candidates = slot
                .candidates
                .iter()
                .map(|candidate| {
                    candidate
                        .components
                        .iter()
                        .chain(&candidate.fixed)
                        .map(|&component| encoder.discover(ArenaNode::Value(component)))
                        .collect()
                })
                .collect();
            models.push(ModelRoots {
                holes,
                fixed,
                candidates,
            });
        }
        encoder.drain();
    }
    let raw_roots: Vec<NodeIndex> = declaration.iter().map(|(root, _)| root).collect();
    let tabled = tabled(&encoder.nodes, &raw_roots);
    let sites = encoder
        .seen
        .into_iter()
        .map(|(node, raw)| (node, (tabled.of(raw), Discovery::from(usize::from(raw)))))
        .collect();
    Encoded {
        content: ItemContent {
            reference,
            declaration: declaration.renumbered(|raw| tabled.of(raw)),
            placements: tabled.supports(&raw_roots),
            nodes: tabled.nodes,
        },
        sites: Sites(sites),
    }
}

/// The arena nodes that root `item`'s declaration, in a fixed order: a
/// value's signature then its body; a datatype's parameters, indices,
/// constructor fields, stated results and kind; a codata type's parameters,
/// observations and kind; an abstract type's kind, representation and
/// interface; none for a world.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each root once for each place the declaration names it, in the
///   order above; the order depends on the declaration alone.
/// - provides: the roots a failure's node outside its item is placed under.
/// - panics: none.
/// - executable: none — the clause restates the body.
///
/// # Adequacy
/// - hypothesis: L3 — a node of another item's signature, and a codata item's
///   own kind, are placed under their roots and seat at them again.
/// - witness: `failure::tests::a_node_of_another_item_seats_at_its_root`
///
/// # Cost
/// - allocation: the list of root nodes, growth within the declaration
pub fn item_roots(item: &crate::region::Item) -> Vec<ArenaNode>
{
    let mut roots = Vec::new();
    match *item.declaration().content() {
        gandr_core_checker::DeclarationContent::Value { signature, body } => {
            if let Maybe::Present(ty) = signature {
                roots.push(ArenaNode::ValueType(ty));
            }
            if let Maybe::Present(value) = body {
                roots.push(ArenaNode::Value(value));
            }
        },
        gandr_core_checker::DeclarationContent::Data(ref signature) => {
            roots.extend(
                signature
                    .parameters()
                    .iter()
                    .chain(signature.indices())
                    .chain(signature.constructors().iter().flatten())
                    .map(|&ty| ArenaNode::ValueType(ty)),
            );
            roots.extend(
                signature
                    .results()
                    .iter()
                    .flatten()
                    .map(|&value| ArenaNode::Value(value)),
            );
            roots.push(ArenaNode::ValueType(signature.kind()));
        },
        gandr_core_checker::DeclarationContent::Codata(ref signature) => {
            roots.extend(
                signature
                    .parameters()
                    .iter()
                    .map(|&ty| ArenaNode::ValueType(ty)),
            );
            roots.extend(
                signature
                    .observations()
                    .iter()
                    .map(|&ty| ArenaNode::CompType(ty)),
            );
            roots.push(ArenaNode::ValueType(signature.kind()));
        },
        gandr_core_checker::DeclarationContent::Abstract(sealed) => {
            roots.push(ArenaNode::ValueType(sealed.kind()));
            roots.push(ArenaNode::ValueType(sealed.representation()));
            if let Maybe::Present(interface) = sealed.interface() {
                roots.push(ArenaNode::Value(interface.relation()));
                roots.push(ArenaNode::Value(interface.reflexivity()));
                if let Maybe::Present(law) = interface.law() {
                    roots.push(ArenaNode::Value(law));
                }
            }
        },
        gandr_core_checker::DeclarationContent::World(_) => {},
    }
    roots
}

/// The walk of `root` alone: each arena node it reaches, in the order a walk
/// from `root` discovers them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `root` first, then each node the breadth-first walk of
///   [`encode_item`] reaches from `root` alone, once each; the order depends on
///   the graph under `root` alone, so an edit outside it moves no place.
/// - panics: none.
/// - executable: none — a predicate would walk the graph again.
///
/// # Adequacy
/// - hypothesis: L3 — as [`item_roots`].
/// - witness: `failure::tests::a_node_of_another_item_seats_at_its_root`
///
/// # Cost
/// - allocation: the list of reached arena nodes, growth within the root
pub fn root_walk(
    arena: &CoreArena,
    layout: &Layout,
    root: ArenaNode,
) -> Vec<ArenaNode>
{
    let mut encoder = Encoder::new(arena, layout);
    let _root = encoder.discover(root);
    encoder.drain();
    let mut walk: Vec<(NodeIndex, ArenaNode)> = encoder
        .seen
        .into_iter()
        .map(|(node, raw)| (raw, node))
        .collect();
    walk.sort_unstable();
    walk.into_iter().map(|(_, node)| node).collect()
}

/// A node of an item that a node outside the item holds: the path of child
/// positions to it from the outside node, and its place in the item's walk.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Anchor
{
    /// The child positions from the outside node down to the item's node.
    pub path: Vec<ChildPosition>,
    /// The item node's place in the item's walk.
    pub at: Discovery,
}

/// The seal site an item's table names for `site`: the same component, of
/// the first ascription. A producer numbers the ascriptions of the whole
/// laid unit, so one ascription takes another number in another closure; an
/// item's table holds one site, so the first ascription names it in each.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `site`'s component, at ascription zero.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — one ascription numbered apart in two closures.
/// - witness: `content::tests::a_seal_site_is_named_by_its_component_6522`
#[spec(ensures: |ret| ret.component() == site.component()
    && usize::from(ret.sealing()) == 0_usize)]
fn local_site(site: gandr_core_checker::SealSite) -> gandr_core_checker::SealSite
{
    gandr_core_checker::SealSite::new(
        gandr_core_checker::SealingSite::from(0_usize),
        site.component(),
    )
}

/// The nodes of an item that the node `root` outside the item holds, each by
/// its path from `root` and its place in the item's walk.
///
/// # Specification
/// - requires: `sites` are the sites of the item that `root` stands outside.
/// - ensures: one anchor for each node of the walk from `root` that `sites`
///   places, by the first path that a breadth-first walk from `root` takes to
///   it; the walk goes below no node that it anchors, and never anchors `root`.
/// - panics: none.
/// - executable: none — a predicate would walk the graph again.
///
/// # Adequacy
/// - hypothesis: L3 — a content outside an item that holds the item's body
///   anchors the body once, and none of the nodes below it.
/// - witness: `failure::tests::a_content_outside_the_item_mints_over_the_item_nodes_it_holds`
///
/// # Cost
/// - allocation: the list of anchors and the walk of the root, growth within
///   the item
pub fn anchors(
    arena: &CoreArena,
    layout: &Layout,
    root: ArenaNode,
    sites: &Sites,
) -> Vec<Anchor>
{
    let mut encoder = Encoder::new(arena, layout);
    let top = encoder.discover(root);
    encoder.drain();
    let mut numbered: Vec<Option<ArenaNode>> = alloc::vec![None; encoder.nodes.len()];
    for (&node, &number) in &encoder.seen {
        if let Some(slot) = numbered.get_mut(usize::from(number)) {
            *slot = Some(node);
        }
    }
    let mut reached: Vec<Option<()>> = alloc::vec![None; encoder.nodes.len()];
    if let Some(slot) = reached.get_mut(usize::from(top)) {
        *slot = Some(());
    }
    let mut anchors = Vec::new();
    let mut queue = VecDeque::from([(top, Vec::new())]);
    while let Some((number, path)) = queue.pop_front() {
        if number != top
            && let Some(&Some(node)) = numbered.get(usize::from(number))
            && let Maybe::Present(at) = sites.discovery(node)
        {
            anchors.push(Anchor { path, at });
            continue;
        }
        let Some(entry) = encoder.nodes.get(usize::from(number))
        else {
            continue;
        };
        for (position, (child, _)) in entry.children().iter().enumerate() {
            if let Some(slot) = reached.get_mut(usize::from(child))
                && slot.is_none()
            {
                *slot = Some(());
                let mut below = path.clone();
                below.push(ChildPosition::from(position));
                queue.push_back((child, below));
            }
        }
    }
    anchors
}

/// The content of the node `root` of `program`'s arena.
///
/// # Specification
/// - requires: nothing — an unresolved id is admissible and listed as
///   unresolved.
/// - ensures: the table the item encoding gives the same node, renumbered from
///   it, so a node compares equal to itself across arenas.
/// - provides: the comparison form of types and terms: answers, verdicts and
///   seats are compared by it, never by arena id.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — allocation noise and a shared arrow separate arena
///   identity from content; the same signature is encoded through the item
///   path; a term with a lambda and a bind reads back from its mint.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
/// - witness: `content::tests::alpha_equal_terms_mint_to_one_name`
///
/// # Cost
/// - allocation: the table of the node, growth within the table
#[spec(ensures: |ret| ret.nodes().first().is_some_and(|node| node.sort() == root.sort()
        && (root.held(program.arena()).is_some() || *node.former() == ContentNode::Unresolved(root.sort()))))]
#[inline]
#[must_use]
pub fn of_node(
    program: &Program,
    root: ArenaNode,
) -> TypeContent
{
    TypeContent::of(program.arena(), program.layout(), root)
}

/// Mint the content into `program`'s arena under its layout.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`TypeContent::mint`] into the program's arena.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — terms with a lambda and a bind mint into a fresh program
///   and read back as their own content.
/// - witness: `content::tests::alpha_equal_terms_mint_to_one_name`
///
/// # Cost
/// - allocation: each minted node, growth within the arena of the program
#[spec(ensures: |ret| match ret {
        Maybe::Present(node) => node.held(program.arena()).is_some(),
        Maybe::Absent(_) => true,
    })]
#[inline]
pub fn mint_in(
    content: &TypeContent,
    program: &mut Program,
) -> Maybe<ArenaNode, seating::Absent>
{
    let (arena, layout) = program.parts_mut();
    content.mint(arena, layout)
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
pub fn place(
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
