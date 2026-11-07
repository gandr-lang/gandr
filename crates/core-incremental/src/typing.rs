//! An item's typing: the checker's verdict, projected to a form free of arena
//! ids and admission positions.
//!
//! # A coordinate change, nothing more
//!
//! A [`Verdict`] names arena ids and positions, which differ between two runs
//! over two arenas even when the runs agree. The projection replaces each id
//! with the content it names — a term node with its index in the item's
//! table, a type with its type table — and each position with the reference
//! it resolves to. Two runs agree exactly when their projections are equal,
//! which is what "incremental equals batch" compares. The origin token is not
//! projected: it is the producer's coordinate for the item, echoed from the
//! edited declaration, never reused from a checkpoint.
//!
//! # References
//!
//! - `vault:01a178aa-6a53-7ec2-b60c-2de66202cf07` — lineage: a stored
//!   `FootprintsOverlap` keeps both halves' footprints and what they share, the
//!   three try-first 1 names.

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingForm;
use gandr_core_checker::ConversionCount;
use gandr_core_checker::CoreNode;
use gandr_core_checker::Mismatch;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::Verdict;
use gandr_core_checker::session::Capture;
use gandr_core_checker::session::Endpoint;
use gandr_core_checker::session::ForkSide;
use gandr_core_checker::session::LinearityDefect;
use gandr_core_term::CoreArena;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::boundary::ItemOrdinal;
use crate::boundary::NodeIndex;
use crate::content::ArenaNode;
use crate::content::Sites;
use crate::content::TypeContent;
use crate::content::TypeMemo;
use crate::content::encode_item;
use crate::region::Layout;
use crate::region::Program;
use crate::region::Reference;

/// Where in its item a refusal stood.
///
/// # Specification
/// - requires: a node site is interpreted against its associated item's table.
/// - ensures: a reached node names its table index; an unreached node invents
///   no index. The variant alone does not certify an arbitrary index.
/// - executable: none — this declaration has no call boundary; the owning table
///   and arena-node correspondence are external to a stored site.
///
/// # Adequacy
/// - hypothesis: L3 — the projection witnesses use fixed breadth-first table
///   coordinates for all four arena-node sorts and a node outside the walk.
///   They certify projected sites, not arbitrary constructed indices.
/// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Site
{
    /// The node at this index of the item's table.
    Node(NodeIndex),
    /// A node the item's walk did not reach; the judgement names none, and the
    /// projection stays total without inventing an index.
    Unreached,
}

/// A checking-only form met where a type had to be synthesised.
///
/// # Specification
/// - requires: a projected checking form is interpreted in its item's table.
/// - ensures: projection retains the checking-only former and its site, or the
///   hole marker without the producer's origin coordinate.
/// - executable: none — this declaration has no call boundary; the source
///   checking form and its arena are not part of a stored value.
///
/// # Adequacy
/// - hypothesis: L3 — real hole and thunk refusals and structural lambda,
///   return and static-lambda payloads separate the five tags and their node
///   sorts. The structural corpus does not establish checker reachability.
/// - witness: `typing::tests::each_verdict_projects_to_its_typing`
/// - witness: `typing::tests::each_refusal_projects_its_payload`
/// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Form
{
    /// A literal stack.
    Reify(Site),
    /// A deep handler.
    Handle(Site),
    /// An answer delimiter.
    Reset(Site),
    /// A continuation capture.
    Shift(Site),
    /// A lazy product.
    With(Site),
    /// A native List introduction.
    List(Site),
    /// A sum injection.
    Injection(Site),
    /// A sum case.
    Case(Site),
    /// A thunk.
    Thunk(Site),
    /// A lambda.
    Lambda(Site),
    /// A static lambda.
    StaticLambda(Site),
    /// The item's own hole.
    Hole,
    /// A fixpoint.
    Fixpoint(Site),
    /// A computation written where a value is read.
    Nested(Site),
    /// An offer.
    Offer(Site),
    /// A capability scope.
    Scope(Site),
    /// A recorded run.
    Run(Site),
    /// A decimal literal.
    Decimal(Site),
}

/// A synthesised type that does not convert to the type it was checked
/// against, projected: the term's site and both types' contents, of a value or
/// a computation alike.
///
/// # Specification
/// - requires: the site is interpreted in its item's table, and each type in
///   its own type table.
/// - ensures: projection keeps the term's site and both types, and drops which
///   sort the term is of, which the site's node already states.
/// - executable: none — this declaration has no call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — a value and a computation mismatch each project their
///   site and both types.
/// - witness: `typing::tests::each_refusal_projects_its_payload`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Mismatched
{
    /// The term.
    pub at: Site,
    /// The type it synthesised.
    pub synthesised: TypeContent,
    /// The type it was checked against.
    pub expected: TypeContent,
}

/// An endpoint, by the site of the fork that bound it and its side.
///
/// # Specification
/// - requires: the fork's site is interpreted in its item's table.
/// - ensures: projection keeps the side and maps the fork to its item site.
/// - executable: none — this declaration has no call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — a residue at a fork's child end projects the fork's item
///   site and the side.
/// - witness: `typing::tests::session_refusals_project_their_endpoints_and_states`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EndpointSite
{
    /// The fork.
    pub fork: Site,
    /// Which of its ends.
    pub side: ForkSide,
}

/// How an endpoint escaped its one linear use, projected: endpoints and arms
/// as item sites, a residue's session type as its own type table.
///
/// # Specification
/// - requires: sites are interpreted in their item's table.
/// - ensures: projection preserves the defect kind and its scalar payloads.
/// - executable: none — this declaration has no call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — a residue and an arm disagreement project their endpoint,
///   state and arm sites.
/// - witness: `typing::tests::session_refusals_project_their_endpoints_and_states`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Linearity
{
    /// A half of a fork finished with the endpoint unconsumed.
    Residue
    {
        /// The endpoint.
        endpoint: EndpointSite,
        /// Its session type when the half finished.
        state: TypeContent,
    },
    /// The endpoint was acted on after it was closed.
    Closed
    {
        /// The endpoint.
        endpoint: EndpointSite,
    },
    /// The endpoint was used twice in one action.
    UsedTwice
    {
        /// The endpoint.
        endpoint: EndpointSite,
    },
    /// The endpoint was named where its use may run other than once.
    Captured
    {
        /// The endpoint.
        endpoint: EndpointSite,
        /// What may run it.
        by: Capture,
    },
    /// The endpoint was read as a value outside an action.
    AsValue
    {
        /// The endpoint.
        endpoint: EndpointSite,
    },
    /// Two arms of an offer or a case left the endpoint in different states.
    ArmsDisagree
    {
        /// The endpoint.
        endpoint: EndpointSite,
        /// The first arm.
        first: Site,
        /// The arm that disagrees with it.
        other: Site,
    },
    /// A declaration's type is a session type.
    Unrestricted,
    /// An action names a linear index no fork or receive bound.
    Unbound
    {
        /// The index.
        index: DeBruijnIndex,
    },
    /// A buffer placed live reached the end of its scope never returned.
    BufferUnreturned
    {
        /// The computation that placed it live.
        site: Site,
    },
    /// A buffer was returned a second time.
    BufferReturnedTwice
    {
        /// The computation that placed it live.
        site: Site,
    },
    /// A buffer was read other than by what returns it, or a buffer never
    /// placed live was returned.
    BufferRead
    {
        /// The computation that placed it live, or the action returning a
        /// buffer no slot holds.
        site: Site,
    },
    /// An operation clause whose continuation holds an obligation finished
    /// without resuming or abandoning it.
    ContinuationUnspent
    {
        /// The clause's body.
        clause: Site,
    },
    /// A continuation holding an obligation was ended a second time.
    ContinuationUsedTwice
    {
        /// The clause's body.
        clause: Site,
    },
    /// A continuation holding an obligation was named where its end may run
    /// other than once.
    ContinuationCaptured
    {
        /// The clause's body.
        clause: Site,
        /// What may run it.
        by: Capture,
    },
    /// A continuation holding an obligation was read as a value, other than as
    /// what a resumption or an abandonment ends.
    ContinuationAsValue
    {
        /// The clause's body.
        clause: Site,
    },
    /// A linear function's body read its parameter after its copy was spent.
    LinearSlotConsumed
    {
        /// The linear lambda.
        lambda: Site,
    },
    /// A linear function's body ended with its parameter's copy unread, or
    /// one arm of a case read the copy and another did not.
    LinearSlotUnconsumed
    {
        /// The linear lambda.
        lambda: Site,
    },
    /// A linear function's parameter was read as a value where its read may
    /// run other than once.
    ShadowCaptured
    {
        /// The linear lambda.
        lambda: Site,
        /// What may run the read.
        by: Capture,
    },
}

/// The world a located refusal names, projected: the host's, or the
/// reference of the world declaration.
///
/// # Specification
/// - executable: none — this declaration has no call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — a missing capability projects its declared world.
/// - witness: `typing::tests::a_located_refusal_projects_its_worlds_and_types`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Place
{
    /// The host's world.
    Host,
    /// The world the declaration at this reference declares.
    Declared(Reference),
}

/// How a located judgement broke, projected: types as their own tables,
/// worlds and positions as references.
///
/// # Specification
/// - requires: tables are interpreted in their own coordinates.
/// - ensures: projection preserves the defect kind and its scalar payloads.
/// - executable: none — this declaration has no call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — a missing capability and an unfounded mark project their
///   world, atom and former.
/// - witness: `typing::tests::a_located_refusal_projects_its_worlds_and_types`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Located
{
    /// A value crosses to a world where its type does not.
    Immobile
    {
        /// What crosses.
        crossed: gandr_core_checker::worlds::Crossed,
        /// Its type.
        ty: TypeContent,
        /// The former that fails.
        former: TypeContent,
        /// The predicate it fails.
        predicate: gandr_core_checker::worlds::Predicate,
    },
    /// A migration found no capability for its world.
    CapabilityMissing
    {
        /// The world migrated to.
        world: Place,
    },
    /// A migration under a former that may run it other than once.
    CapabilityCaptured
    {
        /// The world migrated to.
        world: Place,
        /// What may run it again.
        by: Capture,
    },
    /// A hypothesis or a resident used at a world other than its own.
    Elsewhere
    {
        /// The world it was bound at.
        bound: Place,
    },
    /// A hold checked against a handle at another world.
    HoldElsewhere
    {
        /// The world the handle was wanted at.
        wanted: Place,
    },
    /// A `leta` writing another world than the one its handle stands at.
    OpenedElsewhere
    {
        /// The world the `leta` writes.
        written: Place,
        /// The world the handle stands at.
        handle: Place,
    },
    /// A hold or a `leta` at the host's world.
    Unlocated,
    /// A world position no world declaration holds.
    UndeclaredWorld
    {
        /// The position named.
        world: Reference,
    },
    /// The host's entry names a world the source declares nowhere.
    HostWorldUndeclared,
    /// A `mobile` mark over a representation that does not cross.
    MarkUnfounded
    {
        /// The abstract type.
        atom: Reference,
        /// The former that fails.
        former: TypeContent,
        /// The predicate it fails.
        predicate: gandr_core_checker::worlds::Predicate,
    },
    /// An entry named from another declaration.
    EntryNamed
    {
        /// The entry.
        constant: Reference,
    },
    /// A stated entry the host's does not hold.
    EntryUngranted
    {
        /// The declaration stating it.
        constant: Reference,
    },
    /// A `leta` of a value whose type is no handle.
    NotAHandle
    {
        /// The type the value synthesised.
        found: TypeContent,
    },
}

refusal_enum! {
    /// A refusal, projected.
    ///
    /// The variants are the checker's refusals, one each, generated by the crate's
    /// build script from `CheckRefusal` and `refusals.toml`: each field at the
    /// type its role keeps, and without the fields the table elides.
    ///
    /// # Specification
    /// - requires: a projected refusal is interpreted in its item's table and
    ///   reference layout; type tables use their own discovery coordinates.
    /// - ensures: projection preserves the refusal kind, semantic payloads and
    ///   mapped sites, omitting only the fields `refusals.toml` elides.
    /// - executable: none — this declaration has no call boundary; a stored refusal
    ///   does not retain the source judgement or coordinate context.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real checking refusals and a finite structural payload
    ///   corpus distinguish item sites, independent type-table roots, named and
    ///   unoccupied references, classifier direction and arity direction. The
    ///   corpus does not certify arbitrary stored values or establish that the
    ///   checker emits each structural case. Internal admission-order and
    ///   machine-invariant refusals remain outside its witnessed domain.
    /// - witness: `typing::tests::each_refusal_projects_its_payload`
    /// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
    #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    pub enum Refusal
}

/// An item's typing: its verdict, projected.
///
/// # Specification
/// - requires: a projected typing is interpreted against its source judgement.
/// - ensures: projection preserves the four verdict classes, conversion counts
///   and semantic type or refusal content, not arena coordinates.
/// - executable: none — this declaration has no call boundary; the source
///   judgement needed to certify a constructed typing is external.
///
/// # Adequacy
/// - hypothesis: L3 — real checked, synthesised, owed and refused declarations
///   distinguish all four classes; independent integer content and exact
///   refusal payloads distinguish coordinate projection from arena-id copying.
///   The finite cases do not certify arbitrary values of this public enum.
/// - witness: `typing::tests::each_verdict_projects_to_its_typing`
/// - witness: `typing::tests::each_refusal_projects_its_payload`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Typing
{
    /// A nominal declaration whose whole signature formed.
    Data,
    /// The body checked against the signature.
    Checked
    {
        /// The conversions the check made.
        conversions: ConversionCount,
    },
    /// The unsigned body synthesised a type.
    Synthesised
    {
        /// The type produced.
        produced: TypeContent,
        /// The conversions the synthesis made.
        conversions: ConversionCount,
    },
    /// The body is a hole under the signature, owed.
    Owed,
    /// The body waits on owed holes: its type is supplied, nothing defined.
    Suspended,
    /// The item was refused.
    Refused(Refusal),
}

/// What a projection reads beside the verdict: the arena its ids resolve in,
/// the program its positions resolve through, the item's sites, and the
/// pass's encoded types.
///
/// # Specification
/// - requires: arena ids, layout positions and sites refer to the same
///   judgement context; the arena may include nodes minted by checking; the
///   memo belongs to the pass judging in that arena and layout.
/// - ensures: projection reads that context without retaining arena ids or
///   admission positions in its results; absent sites remain unreached.
/// - executable: none — this declaration has no call boundary, and ownership
///   correspondence between its borrowed inputs has no retained proof.
///
/// # Adequacy
/// - hypothesis: L3 — projection over a noisy arena and a fixed item graph
///   distinguishes arena indices, item indices and type-table indices. Actual
///   checking witnesses include types minted after item encoding. These
///   observations assume the inputs share their stated context.
/// - witness: `typing::tests::each_verdict_projects_to_its_typing`
/// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
pub struct Projection<'arena, 'layout, 'sites, 'types>
{
    /// The arena the verdict's ids resolve in.
    pub arena: &'arena CoreArena,
    /// The program positions resolve through.
    pub layout: &'layout Layout,
    /// The item's table indices of its arena nodes.
    pub sites: &'sites Sites,
    /// The pass's encoded types.
    pub types: &'types TypeMemo,
}

impl Projection<'_, '_, '_, '_>
{
    /// The projected typing of `verdict`.
    ///
    /// # Specification
    /// - requires: `verdict` judged the item whose sites these are, in this
    ///   arena.
    /// - ensures: each verdict maps to its typing, each id to the content or
    ///   site it names, each position to its reference, and nothing else is
    ///   dropped but the origin and the admission positions of an out-of-order
    ///   refusal.
    /// - provides: the coordinate change both runs of the differential pass
    ///   through.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real declarations separate all four verdict classes
    ///   and conversion counts. Six checker refusal classes distinguish named
    ///   coordinates and type content, without claiming all refusal variants or
    ///   all valid arenas have been exercised through this entry.
    /// - witness: `typing::tests::each_verdict_projects_to_its_typing`
    /// - witness: `typing::tests::each_refusal_projects_its_payload`
    #[spec(ensures: |ret| match *verdict {
        Verdict::Data => matches!(ret,Typing::Data),
        | Verdict::Checked { evidence, .. } => {
            matches!(ret, Typing::Checked { conversions } if conversions == evidence.conversions())
        },
        | Verdict::Synthesised { synthesised, .. } => {
            matches!(ret, Typing::Synthesised { conversions, .. } if conversions == synthesised.conversions())
        },
        | Verdict::Owed(_) => matches!(ret, Typing::Owed),
        | Verdict::Suspended(_) => matches!(ret, Typing::Suspended),
        | Verdict::Refused(_) => matches!(ret, Typing::Refused(_)),
    })]
    pub(crate) fn typing(
        &self,
        verdict: &Verdict,
    ) -> Typing
    {
        match *verdict {
            Verdict::Data => Typing::Data,
            Verdict::Checked { evidence, .. } => Typing::Checked {
                conversions: evidence.conversions(),
            },
            Verdict::Synthesised { synthesised, .. } => Typing::Synthesised {
                produced: self.value_type(synthesised.produced().id()),
                conversions: synthesised.conversions(),
            },
            Verdict::Owed(_) => Typing::Owed,
            Verdict::Suspended(_) => Typing::Suspended,
            Verdict::Refused(refusal) => Typing::Refused(self.refusal(refusal)),
        }
    }

    /// The content of a value type.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &self,
        ty: gandr_core_term::ValueTypeId,
    ) -> TypeContent
    {
        self.types
            .content(self.arena, self.layout, ArenaNode::ValueType(ty))
    }

    /// The content of a type node.
    ///
    /// # Specification
    /// trivial.
    fn type_node(
        &self,
        node: TypeNode,
    ) -> TypeContent
    {
        match node {
            TypeNode::Value(ty) => self.value_type(ty),
            TypeNode::Computation(ty) => {
                self.types
                    .content(self.arena, self.layout, ArenaNode::CompType(ty))
            },
        }
    }

    /// The site of an arena node.
    ///
    /// # Specification
    /// - requires: the node is interpreted in this projection's arena.
    /// - ensures: a listed node yields exactly its stored table index;
    ///   otherwise the site is unreached, even if the arena holds the node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fixed item-local sites of four node sorts and one
    ///   same-arena node outside the item walk distinguish absent membership
    ///   from arena validity. No arbitrary-table well-formedness is claimed.
    /// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
    #[spec(ensures: |ret| match self.sites.of(node) {
        Maybe::Present(index) => ret == Site::Node(index),
        Maybe::Absent(_) => ret == Site::Unreached,
    })]
    fn site(
        &self,
        node: ArenaNode,
    ) -> Site
    {
        match self.sites.of(node) {
            Maybe::Present(index) => Site::Node(index),
            Maybe::Absent(_) => Site::Unreached,
        }
    }

    /// The site of a term node.
    ///
    /// # Specification
    /// trivial.
    fn term_site(
        &self,
        node: TermNode,
    ) -> Site
    {
        match node {
            TermNode::Value(id) => self.site(ArenaNode::Value(id)),
            TermNode::Computation(id) => self.site(ArenaNode::Computation(id)),
        }
    }

    /// The site of any core node.
    ///
    /// # Specification
    /// trivial.
    fn core_site(
        &self,
        node: CoreNode,
    ) -> Site
    {
        match node {
            CoreNode::Term(term) => self.term_site(term),
            CoreNode::Type(TypeNode::Value(id)) => self.site(ArenaNode::ValueType(id)),
            CoreNode::Type(TypeNode::Computation(id)) => self.site(ArenaNode::CompType(id)),
        }
    }

    /// The site of an endpoint's fork, beside its side.
    ///
    /// # Specification
    /// trivial.
    fn endpoint(
        &self,
        endpoint: Endpoint,
    ) -> EndpointSite
    {
        EndpointSite {
            fork: self.site(ArenaNode::Computation(endpoint.fork)),
            side: endpoint.side,
        }
    }

    /// The projected linearity defect.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the defect kind and scalar payloads are kept; endpoints and
    ///   arms are item sites and a residue's state its own type table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a residue and an arm disagreement project their
    ///   endpoint, state and arm sites.
    /// - witness: `typing::tests::session_refusals_project_their_endpoints_and_states`
    #[spec(ensures: |ret| core::mem::discriminant(&ret) == match defect {
        | LinearityDefect::Unrestricted => core::mem::discriminant(&Linearity::Unrestricted),
        | _ => core::mem::discriminant(&ret),
    })]
    fn linearity(
        &self,
        defect: LinearityDefect,
    ) -> Linearity
    {
        match defect {
            LinearityDefect::Residue { endpoint, state } => Linearity::Residue {
                endpoint: self.endpoint(endpoint),
                state: self.value_type(state),
            },
            LinearityDefect::Closed { endpoint } => Linearity::Closed {
                endpoint: self.endpoint(endpoint),
            },
            LinearityDefect::UsedTwice { endpoint } => Linearity::UsedTwice {
                endpoint: self.endpoint(endpoint),
            },
            LinearityDefect::Captured { endpoint, by } => Linearity::Captured {
                endpoint: self.endpoint(endpoint),
                by,
            },
            LinearityDefect::AsValue { endpoint } => Linearity::AsValue {
                endpoint: self.endpoint(endpoint),
            },
            LinearityDefect::ArmsDisagree {
                endpoint,
                first,
                other,
            } => Linearity::ArmsDisagree {
                endpoint: self.endpoint(endpoint),
                first: self.site(ArenaNode::Computation(first)),
                other: self.site(ArenaNode::Computation(other)),
            },
            LinearityDefect::Unrestricted => Linearity::Unrestricted,
            LinearityDefect::Unbound { index } => Linearity::Unbound { index },
            LinearityDefect::BufferUnreturned { site } => Linearity::BufferUnreturned {
                site: self.site(ArenaNode::Computation(site)),
            },
            LinearityDefect::BufferReturnedTwice { site } => Linearity::BufferReturnedTwice {
                site: self.site(ArenaNode::Computation(site)),
            },
            LinearityDefect::BufferRead { site } => Linearity::BufferRead {
                site: self.site(ArenaNode::Computation(site)),
            },
            LinearityDefect::ContinuationUnspent { clause } => Linearity::ContinuationUnspent {
                clause: self.site(ArenaNode::Computation(clause)),
            },
            LinearityDefect::ContinuationUsedTwice { clause } => Linearity::ContinuationUsedTwice {
                clause: self.site(ArenaNode::Computation(clause)),
            },
            LinearityDefect::ContinuationCaptured { clause, by } => {
                Linearity::ContinuationCaptured {
                    clause: self.site(ArenaNode::Computation(clause)),
                    by,
                }
            },
            LinearityDefect::ContinuationAsValue { clause } => Linearity::ContinuationAsValue {
                clause: self.site(ArenaNode::Computation(clause)),
            },
            LinearityDefect::LinearSlotConsumed { lambda } => Linearity::LinearSlotConsumed {
                lambda: self.site(ArenaNode::Computation(lambda)),
            },
            LinearityDefect::LinearSlotUnconsumed { lambda } => Linearity::LinearSlotUnconsumed {
                lambda: self.site(ArenaNode::Computation(lambda)),
            },
            LinearityDefect::ShadowCaptured { lambda, by } => Linearity::ShadowCaptured {
                lambda: self.site(ArenaNode::Computation(lambda)),
                by,
            },
        }
    }

    /// The projected world.
    ///
    /// # Specification
    /// trivial.
    fn place(
        &self,
        world: gandr_core_term::world::World,
    ) -> Place
    {
        match world {
            gandr_core_term::world::World::Host => Place::Host,
            gandr_core_term::world::World::Declared(constant) => {
                Place::Declared(self.layout.resolve(constant))
            },
        }
    }

    /// The projected located defect.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the defect kind and scalar payloads are kept; types are their
    ///   own tables and worlds and positions references.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing capability and an unfounded mark project
    ///   their world, atom and former.
    /// - witness: `typing::tests::a_located_refusal_projects_its_worlds_and_types`
    #[spec(ensures: |ret| matches!(
        (defect, &ret),
        (gandr_core_checker::worlds::LocatedDefect::Unlocated, &Located::Unlocated)
            | (gandr_core_checker::worlds::LocatedDefect::HostWorldUndeclared, &Located::HostWorldUndeclared)
    ) || !matches!(ret, Located::Unlocated | Located::HostWorldUndeclared))]
    fn located(
        &self,
        defect: gandr_core_checker::worlds::LocatedDefect,
    ) -> Located
    {
        use gandr_core_checker::worlds::LocatedDefect;
        match defect {
            LocatedDefect::Immobile {
                crossed,
                ty,
                former,
                predicate,
            } => Located::Immobile {
                crossed,
                ty: self.value_type(ty),
                former: self.value_type(former),
                predicate,
            },
            LocatedDefect::CapabilityMissing { world } => Located::CapabilityMissing {
                world: self.place(world),
            },
            LocatedDefect::CapabilityCaptured { world, by } => Located::CapabilityCaptured {
                world: self.place(world),
                by,
            },
            LocatedDefect::Elsewhere { bound } => Located::Elsewhere {
                bound: self.place(bound),
            },
            LocatedDefect::HoldElsewhere { wanted } => Located::HoldElsewhere {
                wanted: self.place(wanted),
            },
            LocatedDefect::OpenedElsewhere { written, handle } => Located::OpenedElsewhere {
                written: self.place(gandr_core_term::world::World::Declared(written)),
                handle: self.place(gandr_core_term::world::World::Declared(handle)),
            },
            LocatedDefect::Unlocated => Located::Unlocated,
            LocatedDefect::UndeclaredWorld { world } => Located::UndeclaredWorld {
                world: self.layout.resolve(world),
            },
            LocatedDefect::HostWorldUndeclared => Located::HostWorldUndeclared,
            LocatedDefect::MarkUnfounded {
                atom,
                former,
                predicate,
            } => Located::MarkUnfounded {
                atom: self.layout.resolve(atom),
                former: self.value_type(former),
                predicate,
            },
            LocatedDefect::EntryNamed { constant } => Located::EntryNamed {
                constant: self.layout.resolve(constant),
            },
            LocatedDefect::EntryUngranted { constant } => Located::EntryUngranted {
                constant: self.layout.resolve(constant),
            },
            LocatedDefect::NotAHandle { found } => Located::NotAHandle {
                found: self.value_type(found),
            },
        }
    }

    /// The site of a value.
    ///
    /// # Specification
    /// trivial.
    fn value_site(
        &self,
        node: gandr_core_term::ValueId,
    ) -> Site
    {
        self.site(ArenaNode::Value(node))
    }

    /// The site of a computation.
    ///
    /// # Specification
    /// trivial.
    fn computation_site(
        &self,
        node: gandr_core_term::ComputationId,
    ) -> Site
    {
        self.site(ArenaNode::Computation(node))
    }

    /// The site of a value type, read as a node of the item rather than as a
    /// type's content.
    ///
    /// # Specification
    /// trivial.
    fn value_type_site(
        &self,
        node: gandr_core_term::ValueTypeId,
    ) -> Site
    {
        self.site(ArenaNode::ValueType(node))
    }

    /// The content of a computation type.
    ///
    /// # Specification
    /// trivial.
    fn comp_type(
        &self,
        ty: gandr_core_term::CompTypeId,
    ) -> TypeContent
    {
        self.type_node(TypeNode::Computation(ty))
    }

    /// The reference an admission position resolves to.
    ///
    /// # Specification
    /// trivial.
    fn reference(
        &self,
        constant: gandr_kernel_term::ConstantIndex,
    ) -> Reference
    {
        self.layout.resolve(constant)
    }

    /// A checking-only form, by its former and its node's site; the hole drops
    /// the producer's origin.
    ///
    /// # Specification
    /// trivial.
    fn form(
        &self,
        form: CheckingForm,
    ) -> Form
    {
        match form {
            CheckingForm::Reify(id) => Form::Reify(self.value_site(id)),
            CheckingForm::Handle(id) => Form::Handle(self.computation_site(id)),
            CheckingForm::Reset(id) => Form::Reset(self.computation_site(id)),
            CheckingForm::Shift(id) => Form::Shift(self.computation_site(id)),
            CheckingForm::With(id) => Form::With(self.computation_site(id)),
            CheckingForm::List(id) => Form::List(self.value_site(id)),
            CheckingForm::Injection(id) => Form::Injection(self.value_site(id)),
            CheckingForm::Case(id) => Form::Case(self.computation_site(id)),
            CheckingForm::Thunk(id) => Form::Thunk(self.value_site(id)),
            CheckingForm::Lambda(id) => Form::Lambda(self.computation_site(id)),
            CheckingForm::Hole(_) => Form::Hole,
            CheckingForm::StaticLambda(id) => Form::StaticLambda(self.value_site(id)),
            CheckingForm::Fixpoint(id) => Form::Fixpoint(self.computation_site(id)),
            CheckingForm::Nested(id) => Form::Nested(self.value_site(id)),
            CheckingForm::Run(id) => Form::Run(self.value_site(id)),
            CheckingForm::Decimal(id) => Form::Decimal(self.value_site(id)),
            CheckingForm::Offer(id) => Form::Offer(self.computation_site(id)),
            CheckingForm::Scope(id) => Form::Scope(self.computation_site(id)),
        }
    }

    /// A mismatch, by the term's site and both types' contents, of a value or
    /// a computation alike.
    ///
    /// # Specification
    /// trivial.
    fn mismatch(
        &self,
        mismatch: Mismatch,
    ) -> Mismatched
    {
        match mismatch {
            Mismatch::Value {
                at,
                synthesised,
                expected,
            } => Mismatched {
                at: self.value_site(at),
                synthesised: self.value_type(synthesised),
                expected: self.value_type(expected),
            },
            Mismatch::Computation {
                at,
                synthesised,
                expected,
            } => Mismatched {
                at: self.computation_site(at),
                synthesised: self.comp_type(synthesised),
                expected: self.comp_type(expected),
            },
        }
    }

    /// The projected refusal.
    ///
    /// # Specification
    /// - requires: the payload's coordinates are interpreted in this arena and
    ///   layout. The refusal need not be reachable from a checker run.
    /// - ensures: the refusal kind is preserved; node payloads use item sites,
    ///   type payloads use independent type tables, and positions use named
    ///   references. Scalar payloads remain exact; the fields `refusals.toml`
    ///   elides are omitted.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real checker errors and a finite structural corpus
    ///   separate all four site sorts, unreached nodes, type-content direction,
    ///   checking-form tags, arity direction and classifier positions. The
    ///   corpus does not prove checker reachability; internal admission-order
    ///   and machine-invariant cases are outside the witnessed domain.
    /// - witness: `typing::tests::each_refusal_projects_its_payload`
    /// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
    #[spec(ensures: |ret| refusal_kept!(refusal, &ret))]
    fn refusal(
        &self,
        refusal: CheckRefusal,
    ) -> Refusal
    {
        refusal_projection!(self, refusal)
    }
}

/// The typing `verdict` projects to, for the item at `ordinal` of `program`,
/// judged in `arena`.
///
/// # Specification
/// - requires: `arena` is `program`'s arena or grew from a copy of it, so every
///   id of the program names the same node in it; `verdict` judged the item at
///   `ordinal` in it.
/// - ensures: the typing an incremental or batch run of this crate records for
///   that verdict.
/// - provides: the coordinate change a caller needs to compare its own batch
///   run — the checker's module entry, say — against this crate's typings.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the generated differential suite compares this public
///   projection against incremental typings over bounded well-formed edits. It
///   does not establish all arena-growth histories or the truth of an arbitrary
///   verdict supplied without its judgement context.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
#[spec(
    requires: usize::from(ordinal) < program.items().len(),
    ensures: |ret| match *verdict {
        Verdict::Data => matches!(ret,Typing::Data),
        | Verdict::Checked { evidence, .. } => {
            matches!(ret, Typing::Checked { conversions } if conversions == evidence.conversions())
        },
        | Verdict::Synthesised { synthesised, .. } => {
            matches!(ret, Typing::Synthesised { conversions, .. } if conversions == synthesised.conversions())
        },
        | Verdict::Owed(_) => matches!(ret, Typing::Owed),
        | Verdict::Suspended(_) => matches!(ret, Typing::Suspended),
        | Verdict::Refused(_) => matches!(ret, Typing::Refused(_)),
    }
)]
#[inline]
#[must_use]
pub fn project(
    program: &Program,
    arena: &CoreArena,
    ordinal: ItemOrdinal,
    verdict: &Verdict,
) -> Typing
{
    let encoded = encode_item(arena, program.layout(), ordinal);
    Projection {
        arena,
        layout: program.layout(),
        sites: &encoded.sites,
        types: &TypeMemo::default(),
    }
    .typing(verdict)
}

#[cfg(test)]
mod tests;
