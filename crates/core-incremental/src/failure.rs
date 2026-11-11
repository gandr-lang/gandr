//! A refused item's failure, kept as content beside its refusal, and its seat
//! in an edited arena.
//!
//! # Places, not sites
//!
//! A checkpoint's [`Refusal`] is a key. It names each node by its site in the
//! item's table, and the table keeps one entry for each content. So two equal
//! subterms share one site, and each variable of one scope is one leaf. A
//! diagnostic reads the node itself, because the node's origin places the
//! message in the source. So the failure content names each node by its
//! [`Discovery`]: the place at which the item's walk discovered the node. A
//! place names one node.
//!
//! A node that the walk does not reach is kept as its content table, once for
//! each node. A root of the item, or of an item that its judgement consulted,
//! can reach that node: the type of another declaration, or a codata item's
//! own kind. Then the content keeps the node's place under that root too
//! ([`Rooted`]). The walk from one root alone discovers the same nodes in the
//! same order whatever the rest of its item holds.
//!
//! # The seat
//!
//! A seat places each node through the walk of the item in the edited
//! program. It places a rooted node through the walk of its root there, when
//! that node has the content kept. It mints each other content table once. It
//! builds the checker's refusal again from the stored one, through the seat
//! that the build script generates beside the projection. The projection
//! records each node it reads, in order, and the seat takes the nodes in the
//! same order. Then the seat builds the failure from its parts.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingForm;
use gandr_core_checker::Compared;
use gandr_core_checker::CoreNode;
use gandr_core_checker::Failure;
use gandr_core_checker::FrameRole;
use gandr_core_checker::Mismatch;
use gandr_core_checker::Obligation;
use gandr_core_checker::Pursuit;
use gandr_core_checker::Stage;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::compared;
use gandr_core_checker::judged;
use gandr_core_checker::kept;
use gandr_core_checker::session::Endpoint;
use gandr_core_checker::session::ForkSide;
use gandr_core_checker::session::LinearityDefect;
use gandr_core_checker::session::LiveEndpoint;
use gandr_core_checker::worlds::LocatedDefect;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::LinearUse;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::world::World;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::boundary::Discovery;
use crate::boundary::ItemOrdinal;
use crate::boundary::OutsideIndex;
use crate::boundary::RootOrdinal;
use crate::content::Anchor;
use crate::content::ArenaNode;
use crate::content::Sites;
use crate::content::TypeContent;
use crate::content::anchors;
use crate::content::item_roots;
use crate::content::place;
use crate::content::root_walk;
use crate::content::seating;
use crate::region::Layout;
use crate::region::Reference;
use crate::typing::EndpointSite;
use crate::typing::Forcing;
use crate::typing::Form;
use crate::typing::Former;
use crate::typing::Linearity;
use crate::typing::Located;
use crate::typing::Mismatched;
use crate::typing::Place;
use crate::typing::Projection;
use crate::typing::Refusal;
use crate::typing::Site;

quenchant_shape::reason_enum! {
    /// Why a checkpoint keeps no failure content.
    pub(crate) mod failed {
        /// The reason no failure content is kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(crate) enum Absent {
            /// The item was not refused, or the maker of the checkpoint kept
            /// no failure content for it.
            Unkept,
            /// The item is opaque: no pass adopts or takes its checkpoint, so
            /// no seat reads a failure that it would keep.
            Opaque,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a node outside the item keeps no place under a root.
    pub(crate) mod rooted {
        /// The reason no root place is kept.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(crate) enum Absent {
            /// No root of the item, or of an item its judgement consulted,
            /// reaches the node: the checker formed it.
            Unrooted,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a kept failure holds no solved comparison.
    pub(crate) mod solved {
        /// The reason no solved comparison is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(crate) enum Absent {
            /// No solution changed a type that the refusal compares.
            Unchanged,
        }
    }
}

/// Where a failure names a node: at its place in the item's walk, or as a
/// content outside the item.
///
/// # Specification
/// - executable: none — this declaration has no call boundary; a place is read
///   against the walk of its item.
///
/// # Adequacy
/// - hypothesis: L3 — a refused corpus item's failure, seated from its
///   checkpoint, renders the diagnostic of the whole judgement.
/// - witness: `failure::tests::a_failure_seats_at_the_nodes_it_names`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Placed
{
    /// The node at this place of the item's walk.
    At(Discovery),
    /// The node whose content the failure keeps at this index.
    Outside(OutsideIndex),
}

/// A pending obligation, its nodes placed.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ObligationContent
{
    /// The rule the frame stands for.
    pub role: FrameRole,
    /// The node the rule stands on.
    pub at: Placed,
    /// The type that node was checked against.
    pub expected: Maybe<Placed, judged::Absent>,
    /// The types of the binders the rule holds open, outermost first.
    pub binders: Vec<Placed>,
}

/// The goal a run pursued when it refused, its nodes placed.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct PursuitContent
{
    /// The node judged or formed.
    pub at: Placed,
    /// The type it was checked against.
    pub expected: Maybe<Placed, judged::Absent>,
    /// Where the machine stood.
    pub stage: Stage,
}

/// An endpoint the run held bound, its fork and its state placed.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct EndpointContent
{
    /// The fork that bound the endpoint.
    pub fork: Placed,
    /// Which of its ends.
    pub side: ForkSide,
    /// The endpoint's session type.
    pub state: Placed,
    /// Whether it was still unconsumed.
    pub use_state: LinearUse,
}

/// The types a refusal compares, read through the solutions, placed.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ComparedContent
{
    /// The type the rule required.
    pub expected: Maybe<Placed, compared::Absent>,
    /// The type found.
    pub found: Maybe<Placed, compared::Absent>,
    /// The found type in weak head.
    pub unfolded: Maybe<Placed, compared::Absent>,
}

/// The parts of a kept failure beside its refusal, their nodes placed.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FailureParts
{
    /// The pending obligations, outermost first.
    pub obligations: Vec<ObligationContent>,
    /// The goal under way.
    pub pursuit: PursuitContent,
    /// The types of the binders the run held open, outermost first.
    pub hypotheses: Vec<Placed>,
    /// The endpoints the run held bound, outermost first.
    pub endpoints: Vec<EndpointContent>,
    /// The compared types read through the solutions.
    pub solved: Maybe<ComparedContent, solved::Absent>,
}

/// A refused item's failure as content: the place of each node its refusal
/// reads, its failure's parts, and the content of each node outside the item.
///
/// # Specification
/// - executable: none — this declaration has no call boundary; its places are
///   read against the walk of the item whose checkpoint keeps it.
///
/// # Adequacy
/// - hypothesis: L3 — over the corpus's refusals, a refused item's diagnostic
///   rendered from its checkpoint is the diagnostic of the whole judgement.
/// - witness: `failure::tests::a_failure_seats_at_the_nodes_it_names`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FailureContent
{
    /// The place of each node the refusal's projection reads, in the order it
    /// reads them.
    pub refusal: Vec<Placed>,
    /// The kept failure's parts, or why the judgement kept none.
    pub parts: Maybe<FailureParts, kept::Absent>,
    /// Each node outside the item, by its index: its content and its place
    /// under a root.
    pub outside: Vec<OutsideContent>,
}

/// A node outside a refused item: its content, or why it cannot mint, its
/// place under a root of the item or of an item the judgement consulted, and
/// the nodes of the item that it holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct OutsideContent
{
    /// The node's content, or why it cannot mint: a content that holds an
    /// unresolved node.
    pub content: Maybe<TypeContent, seating::Absent>,
    /// The node's place under a root, or why no root reaches it.
    pub rooted: Maybe<Rooted, rooted::Absent>,
    /// Each node of the item that the node holds, by its path from the node:
    /// a content minted back holds that node of the item again, so a table
    /// that names the item's nodes still names it.
    pub anchors: Vec<Anchor>,
}

/// A node's place under one root of an item: the item, the root among the
/// roots [`item_roots`] lists, and the node's discovery in the walk of that
/// root alone.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Rooted
{
    /// The item whose root reaches the node.
    pub item: Reference,
    /// The root.
    pub root: RootOrdinal,
    /// The node's place in the walk of that root.
    pub at: Discovery,
}

/// The places of the nodes a projection reads, beside the content of each
/// node outside the item.
///
/// # Specification
/// trivial.
struct Placing<'projection, 'arena, 'layout, 'sites, 'types, 'candidates>
{
    /// The projection whose arena and sites the nodes are read in.
    projection: &'projection Projection<'arena, 'layout, 'sites, 'types>,
    /// The item, then each item its judgement consulted, whose roots place a
    /// node outside the item.
    candidates: &'candidates [&'candidates Reference],
    /// The place of each node the roots of the candidates reach, by the
    /// candidate: walked on the first node outside the item.
    roots: Option<BTreeMap<ArenaNode, (&'candidates Reference, RootOrdinal, Discovery)>>,
    /// The index of each node outside the item placed so far.
    indices: BTreeMap<ArenaNode, OutsideIndex>,
    /// Each node outside the item, by its index.
    outside: Vec<OutsideContent>,
}

impl Placing<'_, '_, '_, '_, '_, '_>
{
    /// The place of `node`.
    ///
    /// # Specification
    /// - ensures: the node's discovery when the item's walk reached it;
    ///   otherwise the index of its content, which one node takes once; a
    ///   content that holds an unresolved node is kept as its reason. The
    ///   content keeps the node's place under the first root of the first
    ///   candidate that reaches it, and each node of the item that it holds.
    /// - panics: none.
    /// - executable: none — the clause restates the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FailureContent`].
    /// - witness: `failure::tests::a_failure_seats_at_the_nodes_it_names`
    /// - witness: `failure::tests::a_node_of_another_item_seats_at_its_root`
    fn place(
        &mut self,
        node: ArenaNode,
    ) -> Placed
    {
        if let Maybe::Present(discovery) = self.projection.sites.discovery(node) {
            return Placed::At(discovery);
        }
        let next = OutsideIndex::from(self.outside.len());
        let index = *self.indices.entry(node).or_insert(next);
        if index == next {
            let content =
                self.projection
                    .types
                    .content(self.projection.arena, self.projection.layout, node);
            let rooted = self.rooted(node);
            let unresolved = content
                .nodes()
                .iter()
                .any(|node| matches!(*node.former(), crate::content::ContentNode::Unresolved(_)));
            let (content, anchors) = if unresolved {
                (Maybe::Absent(seating::Absent::Unresolved), Vec::new())
            }
            else {
                let anchors = anchors(
                    self.projection.arena,
                    self.projection.layout,
                    node,
                    self.projection.sites,
                );
                (Maybe::Present(content), anchors)
            };
            self.outside.push(OutsideContent {
                content,
                rooted,
                anchors,
            });
        }
        Placed::Outside(index)
    }

    /// The place of `node` under a root of a candidate: the candidate, the root
    /// and the node's discovery from it.
    ///
    /// # Specification
    /// - ensures: the first candidate, the first root of it and the node's
    ///   place in that root's walk, for the first candidate whose root reaches
    ///   the node; [`rooted::Absent::Unrooted`] when no root reaches it. The
    ///   first call walks each root of each candidate once.
    /// - panics: none.
    /// - executable: none — the clause restates the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Placing::place`].
    /// - witness: `failure::tests::a_node_of_another_item_seats_at_its_root`
    fn rooted(
        &mut self,
        node: ArenaNode,
    ) -> Maybe<Rooted, rooted::Absent>
    {
        let (arena, layout) = (self.projection.arena, self.projection.layout);
        let candidates = self.candidates;
        let roots = self.roots.get_or_insert_with(|| {
            let mut roots = BTreeMap::new();
            for &reference in candidates {
                let Maybe::Present(ordinal) = layout.ordinal_of(reference)
                else {
                    continue;
                };
                let Some(item) = layout.items.get(usize::from(ordinal))
                else {
                    continue;
                };
                for (root, &top) in item_roots(item).iter().enumerate() {
                    for (at, reached) in root_walk(arena, layout, top).into_iter().enumerate() {
                        let _first = roots.entry(reached).or_insert_with(|| {
                            (reference, RootOrdinal::from(root), Discovery::from(at))
                        });
                    }
                }
            }
            roots
        });
        roots.get(&node).map_or(
            Maybe::Absent(rooted::Absent::Unrooted),
            |&(item, root, at)| {
                Maybe::Present(Rooted {
                    item: item.clone(),
                    root,
                    at,
                })
            },
        )
    }

    /// The place of a type node.
    ///
    /// # Specification
    /// trivial.
    fn type_node(
        &mut self,
        node: TypeNode,
    ) -> Placed
    {
        self.place(type_arena_node(node))
    }

    /// The place of an expected type, or why there is none.
    ///
    /// # Specification
    /// trivial.
    fn expected<Reason>(
        &mut self,
        expected: Maybe<TypeNode, Reason>,
    ) -> Maybe<Placed, Reason>
    {
        match expected {
            Maybe::Present(node) => Maybe::Present(self.type_node(node)),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The parts of `failure`, their nodes placed.
    ///
    /// # Specification
    /// trivial.
    fn parts(
        &mut self,
        failure: &Failure,
    ) -> FailureParts
    {
        let mut obligations = Vec::with_capacity(failure.obligations().len());
        for obligation in failure.obligations() {
            let at = self.place(core_arena_node(obligation.at()));
            let expected = self.expected(obligation.expected());
            let binders = obligation
                .binders()
                .iter()
                .map(|&ty| self.place(ArenaNode::ValueType(ty)))
                .collect();
            obligations.push(ObligationContent {
                role: obligation.role(),
                at,
                expected,
                binders,
            });
        }
        let pursuit = failure.pursuit();
        let pursuit = PursuitContent {
            at: self.place(core_arena_node(pursuit.at())),
            expected: self.expected(pursuit.expected()),
            stage: pursuit.stage(),
        };
        let hypotheses = failure
            .hypotheses()
            .iter()
            .map(|&ty| self.place(ArenaNode::ValueType(ty)))
            .collect();
        let endpoints = failure
            .endpoints()
            .iter()
            .map(|live| EndpointContent {
                fork: self.place(ArenaNode::Computation(live.endpoint.fork)),
                side: live.endpoint.side,
                state: self.place(ArenaNode::ValueType(live.state)),
                use_state: live.use_state,
            })
            .collect();
        let solved =
            failure
                .solutions()
                .map_or(Maybe::Absent(solved::Absent::Unchanged), |compared| {
                    Maybe::Present(ComparedContent {
                        expected: self.expected(compared.expected),
                        found: self.expected(compared.found),
                        unfolded: self.expected(compared.unfolded),
                    })
                });
        FailureParts {
            obligations,
            pursuit,
            hypotheses,
            endpoints,
            solved,
        }
    }
}

impl Projection<'_, '_, '_, '_>
{
    /// The failure content of an item refused with `refusal`, beside its kept
    /// `failure`; `candidates` lists the item, then each item its judgement
    /// consulted.
    ///
    /// # Specification
    /// - requires: `refusal` and `failure` were judged over this projection's
    ///   arena, of the item whose sites these are.
    /// - ensures: the place of each node the refusal's projection reads, in the
    ///   order it reads them; the failure's parts, each node placed; and the
    ///   content of each node outside the item, once for each node, with its
    ///   place under the first root of `candidates` that reaches it.
    /// - panics: none.
    /// - executable: none — the places are read against the walk, which a
    ///   predicate would walk again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FailureContent`].
    /// - witness: `failure::tests::a_failure_seats_at_the_nodes_it_names`
    /// - witness: `failure::tests::a_node_of_another_item_seats_at_its_root`
    pub(crate) fn failed(
        &self,
        refusal: CheckRefusal,
        failure: Maybe<&Failure, kept::Absent>,
        candidates: &[&Reference],
    ) -> FailureContent
    {
        let earlier = self.read.replace(Some(Vec::new()));
        let _projected: Refusal = self.refusal(refusal);
        let read = self.read.replace(earlier).unwrap_or_default();
        let mut placing = Placing {
            projection: self,
            candidates,
            roots: None,
            indices: BTreeMap::new(),
            outside: Vec::new(),
        };
        let refusal = read.into_iter().map(|node| placing.place(node)).collect();
        let parts = match failure {
            Maybe::Present(failure) => Maybe::Present(placing.parts(failure)),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        FailureContent {
            refusal,
            parts,
            outside: placing.outside,
        }
    }
}

impl FailureContent
{
    /// The checker's refusal and failure of an item refused with `refusal`,
    /// seated in `arena`: each place through `sites`, the item's sites in the
    /// edited program, each rooted node through its root there, and each
    /// other content outside the item minted once, over the item's nodes that
    /// it holds.
    ///
    /// # Specification
    /// - requires: `refusal` is the stored refusal this content sits beside;
    ///   `sites` are the sites of the item in the edited program, whose content
    ///   equals the content this checkpoint keeps; `own` is the item's own
    ///   position there.
    /// - ensures: on success, the checker's refusal whose projection through
    ///   the edited item is `refusal`, and the failure with its parts seated. A
    ///   node outside the item is the node at its root place in the edited
    ///   program when that node has the content kept, or when no content is
    ///   kept; otherwise the content minted, each node of the item that it
    ///   holds being the edited walk's node at the same place.
    /// - fails: [`seating::Absent::Unwalked`] for a place the edited walk does
    ///   not hold, or for places the refusal does not read;
    ///   [`seating::Absent::IllSorted`] for a node of another sort than its
    ///   field; and the reason [`TypeContent::mint_holding`] gives for a
    ///   content it cannot mint.
    /// - panics: none.
    /// - executable: none — a predicate would project the seated refusal again,
    ///   through a walk that this call reads.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FailureContent`].
    /// - witness: `failure::tests::a_failure_seats_at_the_nodes_it_names`
    /// - witness: `failure::tests::a_node_of_another_item_seats_at_its_root`
    pub(crate) fn seat(
        &self,
        refusal: &Refusal,
        (arena, layout): (&mut CoreArena, &Layout),
        sites: &Sites,
        own: ConstantIndex,
    ) -> Result<(CheckRefusal, Maybe<Failure, kept::Absent>), seating::Absent>
    {
        let mut seat = Seat {
            arena,
            layout,
            walk: sites.walk(),
            outside: &self.outside,
            minted: BTreeMap::new(),
            walks: BTreeMap::new(),
            places: self.refusal.iter(),
            own,
        };
        let seated = seat.refusal(refusal)?;
        if seat.places.next().is_some() {
            return Err(seating::Absent::Unwalked);
        }
        let failure = match self.parts {
            Maybe::Present(ref parts) => Maybe::Present(seat.failure(seated, parts)?),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        Ok((seated, failure))
    }
}

/// A failure content's seat in an edited arena: the walk of the item there,
/// the nodes minted for the contents outside it, and the refusal's places not
/// yet seated.
///
/// # Specification
/// trivial.
struct Seat<'seat>
{
    /// The edited arena.
    arena: &'seat mut CoreArena,
    /// The edited program.
    layout: &'seat Layout,
    /// The edited item's arena nodes, by discovery.
    walk: Vec<ArenaNode>,
    /// Each node outside the item, by its index.
    outside: &'seat [OutsideContent],
    /// The node seated for each node outside the item so far.
    minted: BTreeMap<OutsideIndex, ArenaNode>,
    /// The walk of each root seated through so far, by its item and root.
    walks: BTreeMap<(ItemOrdinal, RootOrdinal), Vec<ArenaNode>>,
    /// The refusal's places not yet seated, in the order its projection read
    /// them.
    places: core::slice::Iter<'seat, Placed>,
    /// The item's own position, which its hole names.
    own: ConstantIndex,
}

impl Seat<'_>
{
    /// The node at `placed`.
    ///
    /// # Specification
    /// - ensures: the edited walk's node at a discovery. For a node outside the
    ///   item, on its first seat: the node at its root place in the edited
    ///   program, when that node has the content kept or no content is kept;
    ///   otherwise the content minted over the edited walk's node at each of
    ///   its anchors.
    /// - fails: [`seating::Absent::Unwalked`] past the walk or the contents, or
    ///   for an anchor past the walk; the reason the content gives when it
    ///   cannot mint and no root place holds the node.
    /// - panics: none.
    /// - executable: none — the clause restates the body.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FailureContent`].
    /// - witness: `failure::tests::a_failure_seats_at_the_nodes_it_names`
    /// - witness: `failure::tests::a_node_of_another_item_seats_at_its_root`
    /// - witness: `failure::tests::a_content_outside_the_item_mints_over_the_item_nodes_it_holds`
    fn node(
        &mut self,
        placed: Placed,
    ) -> Result<ArenaNode, seating::Absent>
    {
        match placed {
            Placed::At(discovery) => self
                .walk
                .get(usize::from(discovery))
                .copied()
                .ok_or(seating::Absent::Unwalked),
            Placed::Outside(index) => {
                if let Some(&node) = self.minted.get(&index) {
                    return Ok(node);
                }
                let outside = self
                    .outside
                    .get(usize::from(index))
                    .ok_or(seating::Absent::Unwalked)?;
                let rooted = match outside.rooted {
                    Maybe::Present(ref rooted) => self.rooted(rooted),
                    Maybe::Absent(_) => None,
                };
                let node = match (rooted, &outside.content) {
                    (Some(node), &Maybe::Present(ref content))
                        if TypeContent::of(self.arena, self.layout, node) == *content =>
                    {
                        node
                    },
                    (Some(node), &Maybe::Absent(_)) => node,
                    (_, &Maybe::Present(ref content)) => {
                        let mut held = Vec::with_capacity(outside.anchors.len());
                        for anchor in &outside.anchors {
                            let node = self
                                .walk
                                .get(usize::from(anchor.at))
                                .copied()
                                .ok_or(seating::Absent::Unwalked)?;
                            held.push((anchor.path.as_slice(), node));
                        }
                        match content.mint_holding(self.arena, self.layout, &held) {
                            Maybe::Present(node) => node,
                            Maybe::Absent(reason) => return Err(reason),
                        }
                    },
                    (None, &Maybe::Absent(reason)) => return Err(reason),
                };
                let _first = self.minted.insert(index, node);
                Ok(node)
            },
        }
    }

    /// The node at `rooted` in the edited program: its item placed by its
    /// reference, the root among the item's roots, and the node at its place
    /// in the walk of that root.
    ///
    /// # Specification
    /// - ensures: the node of the edited arena at that place; none when no item
    ///   of the edited program carries the reference, the item has no such
    ///   root, or the root's walk is shorter. Each root is walked once.
    /// - panics: none.
    /// - executable: none — the clause restates the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FailureContent`].
    /// - witness: `failure::tests::a_node_of_another_item_seats_at_its_root`
    fn rooted(
        &mut self,
        rooted: &Rooted,
    ) -> Option<ArenaNode>
    {
        let Maybe::Present(ordinal) = self.layout.ordinal_of(&rooted.item)
        else {
            return None;
        };
        let (arena, layout) = (&*self.arena, self.layout);
        let walk = match self.walks.entry((ordinal, rooted.root)) {
            alloc::collections::btree_map::Entry::Occupied(walked) => walked.into_mut(),
            alloc::collections::btree_map::Entry::Vacant(unwalked) => {
                let top = layout
                    .items
                    .get(usize::from(ordinal))
                    .and_then(|item| item_roots(item).get(usize::from(rooted.root)).copied())?;
                unwalked.insert(root_walk(arena, layout, top))
            },
        };
        walk.get(usize::from(rooted.at)).copied()
    }

    /// The node at the refusal's next place.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> Result<ArenaNode, seating::Absent>
    {
        let placed = *self.places.next().ok_or(seating::Absent::Unwalked)?;
        self.node(placed)
    }

    /// The refusal's next node, as a value.
    ///
    /// # Specification
    /// trivial.
    fn value_site(
        &mut self,
        _site: &Site,
    ) -> Result<ValueId, seating::Absent>
    {
        value_of(self.next()?)
    }

    /// The refusal's next node, as a computation.
    ///
    /// # Specification
    /// trivial.
    fn computation_site(
        &mut self,
        _site: &Site,
    ) -> Result<ComputationId, seating::Absent>
    {
        computation_of(self.next()?)
    }

    /// The refusal's next node, as a value type read at its site.
    ///
    /// # Specification
    /// trivial.
    fn value_type_site(
        &mut self,
        _site: &Site,
    ) -> Result<ValueTypeId, seating::Absent>
    {
        value_type_of(self.next()?)
    }

    /// The refusal's next node, as a value type.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &mut self,
        _content: &TypeContent,
    ) -> Result<ValueTypeId, seating::Absent>
    {
        value_type_of(self.next()?)
    }

    /// The refusal's next node, as a computation type.
    ///
    /// # Specification
    /// trivial.
    fn comp_type(
        &mut self,
        _content: &TypeContent,
    ) -> Result<CompTypeId, seating::Absent>
    {
        comp_type_of(self.next()?)
    }

    /// The refusal's next node, as a type node.
    ///
    /// # Specification
    /// trivial.
    fn type_node(
        &mut self,
        _content: &TypeContent,
    ) -> Result<TypeNode, seating::Absent>
    {
        type_node_of(self.next()?)
    }

    /// The refusal's next node, as a core node.
    ///
    /// # Specification
    /// trivial.
    fn core_site(
        &mut self,
        _site: &Site,
    ) -> Result<CoreNode, seating::Absent>
    {
        Ok(core_node_of(self.next()?))
    }

    /// The refusal's next node, as a term node.
    ///
    /// # Specification
    /// trivial.
    fn term_site(
        &mut self,
        _site: &Site,
    ) -> Result<TermNode, seating::Absent>
    {
        term_node_of(self.next()?)
    }

    /// The position `reference` names in the edited program.
    ///
    /// # Specification
    /// trivial.
    fn reference(
        &self,
        reference: &Reference,
    ) -> Result<ConstantIndex, seating::Absent>
    {
        match place(self.layout, reference) {
            Maybe::Present(position) => Ok(position),
            Maybe::Absent(reason) => Err(reason),
        }
    }

    /// The world `place` names in the edited program.
    ///
    /// # Specification
    /// trivial.
    fn world(
        &self,
        place: &Place,
    ) -> Result<World, seating::Absent>
    {
        match *place {
            Place::Host => Ok(World::Host),
            Place::Declared(ref reference) => Ok(World::Declared(self.reference(reference)?)),
        }
    }

    /// The declared world `place` names in the edited program.
    ///
    /// # Specification
    /// trivial.
    fn declared(
        &self,
        place: &Place,
    ) -> Result<ConstantIndex, seating::Absent>
    {
        match *place {
            Place::Host => Err(seating::Absent::IllSorted),
            Place::Declared(ref reference) => self.reference(reference),
        }
    }

    /// The checking-only form `form` names, its node the refusal's next.
    ///
    /// # Specification
    /// trivial.
    fn form(
        &mut self,
        form: &Form,
    ) -> Result<CheckingForm, seating::Absent>
    {
        Ok(match *form {
            Form::Reify(ref site) => CheckingForm::Reify(self.value_site(site)?),
            Form::Handle(ref site) => CheckingForm::Handle(self.computation_site(site)?),
            Form::Reset(ref site) => CheckingForm::Reset(self.computation_site(site)?),
            Form::Shift(ref site) => CheckingForm::Shift(self.computation_site(site)?),
            Form::With(ref site) => CheckingForm::With(self.computation_site(site)?),
            Form::List(ref site) => CheckingForm::List(self.value_site(site)?),
            Form::Injection(ref site) => CheckingForm::Injection(self.value_site(site)?),
            Form::Case(ref site) => CheckingForm::Case(self.computation_site(site)?),
            Form::Thunk(ref site) => CheckingForm::Thunk(self.value_site(site)?),
            Form::Lambda(ref site) => CheckingForm::Lambda(self.computation_site(site)?),
            Form::Hole => CheckingForm::Hole(self.own),
            Form::StaticLambda(ref site) => CheckingForm::StaticLambda(self.value_site(site)?),
            Form::Fixpoint(ref site) => CheckingForm::Fixpoint(self.computation_site(site)?),
            Form::Nested(ref site) => CheckingForm::Nested(self.value_site(site)?),
            Form::Run(ref site) => CheckingForm::Run(self.value_site(site)?),
            Form::Decimal(ref site) => CheckingForm::Decimal(self.value_site(site)?),
            Form::Offer(ref site) => CheckingForm::Offer(self.computation_site(site)?),
            Form::Scope(ref site) => CheckingForm::Scope(self.computation_site(site)?),
        })
    }

    /// The mismatch `mismatched` names, of a value or a computation as its
    /// seated node is.
    ///
    /// # Specification
    /// trivial.
    fn mismatch(
        &mut self,
        _mismatched: &Mismatched,
    ) -> Result<Mismatch, seating::Absent>
    {
        Ok(match self.next()? {
            ArenaNode::Value(at) => Mismatch::Value {
                at,
                synthesised: value_type_of(self.next()?)?,
                expected: value_type_of(self.next()?)?,
            },
            ArenaNode::Computation(at) => Mismatch::Computation {
                at,
                synthesised: comp_type_of(self.next()?)?,
                expected: comp_type_of(self.next()?)?,
            },
            ArenaNode::ValueType(_) | ArenaNode::CompType(_) => {
                return Err(seating::Absent::IllSorted);
            },
        })
    }

    /// The endpoint `endpoint` names, its fork the refusal's next node.
    ///
    /// # Specification
    /// trivial.
    fn endpoint(
        &mut self,
        endpoint: &EndpointSite,
    ) -> Result<Endpoint, seating::Absent>
    {
        Ok(Endpoint {
            fork: computation_of(self.next()?)?,
            side: endpoint.side,
        })
    }

    /// The former `former` names: an interleaving's two operations are the
    /// refusal's next two nodes, child first.
    ///
    /// # Specification
    /// trivial.
    fn former(
        &mut self,
        former: &Former,
    ) -> Result<gandr_core_checker::UnadmittedFormer, seating::Absent>
    {
        Ok(match *former {
            Former::Named(named) => named,
            Former::Interleaving {
                ref child,
                ref parent,
            } => gandr_core_checker::UnadmittedFormer::Interleaving {
                child: self.core_site(child)?,
                parent: self.core_site(parent)?,
            },
        })
    }

    /// The linearity defect `linearity` names.
    ///
    /// # Specification
    /// trivial.
    fn linearity(
        &mut self,
        linearity: &Linearity,
    ) -> Result<LinearityDefect, seating::Absent>
    {
        Ok(match *linearity {
            Linearity::Residue {
                ref endpoint,
                ref state,
            } => LinearityDefect::Residue {
                endpoint: self.endpoint(endpoint)?,
                state: self.value_type(state)?,
            },
            Linearity::Closed { ref endpoint } => LinearityDefect::Closed {
                endpoint: self.endpoint(endpoint)?,
            },
            Linearity::UsedTwice { ref endpoint } => LinearityDefect::UsedTwice {
                endpoint: self.endpoint(endpoint)?,
            },
            Linearity::Captured { ref endpoint, by } => LinearityDefect::Captured {
                endpoint: self.endpoint(endpoint)?,
                by,
            },
            Linearity::AsValue { ref endpoint } => LinearityDefect::AsValue {
                endpoint: self.endpoint(endpoint)?,
            },
            Linearity::ArmsDisagree {
                ref endpoint,
                ref first,
                ref other,
            } => LinearityDefect::ArmsDisagree {
                endpoint: self.endpoint(endpoint)?,
                first: self.computation_site(first)?,
                other: self.computation_site(other)?,
            },
            Linearity::Unrestricted => LinearityDefect::Unrestricted,
            Linearity::Unbound { index } => LinearityDefect::Unbound { index },
            Linearity::BufferUnreturned { ref site } => LinearityDefect::BufferUnreturned {
                site: self.computation_site(site)?,
            },
            Linearity::BufferReturnedTwice { ref site } => LinearityDefect::BufferReturnedTwice {
                site: self.computation_site(site)?,
            },
            Linearity::BufferRead { ref site } => LinearityDefect::BufferRead {
                site: self.computation_site(site)?,
            },
            Linearity::ContinuationUnspent { ref clause } => LinearityDefect::ContinuationUnspent {
                clause: self.computation_site(clause)?,
            },
            Linearity::ContinuationUsedTwice { ref clause } => {
                LinearityDefect::ContinuationUsedTwice {
                    clause: self.computation_site(clause)?,
                }
            },
            Linearity::ContinuationCaptured { ref clause, by } => {
                LinearityDefect::ContinuationCaptured {
                    clause: self.computation_site(clause)?,
                    by,
                }
            },
            Linearity::ContinuationAsValue { ref clause } => LinearityDefect::ContinuationAsValue {
                clause: self.computation_site(clause)?,
            },
            Linearity::LinearSlotConsumed { ref lambda } => LinearityDefect::LinearSlotConsumed {
                lambda: self.computation_site(lambda)?,
            },
            Linearity::LinearSlotUnconsumed { ref lambda } => {
                LinearityDefect::LinearSlotUnconsumed {
                    lambda: self.computation_site(lambda)?,
                }
            },
            Linearity::ShadowCaptured { ref lambda, by } => LinearityDefect::ShadowCaptured {
                lambda: self.computation_site(lambda)?,
                by,
            },
            Linearity::ComonoidAbsent { ref ty, grade } => LinearityDefect::ComonoidAbsent {
                ty: self.value_type(ty)?,
                grade,
            },
        })
    }

    /// The located defect `located` names.
    ///
    /// # Specification
    /// trivial.
    fn located(
        &mut self,
        located: &Located,
    ) -> Result<LocatedDefect, seating::Absent>
    {
        Ok(match *located {
            Located::Immobile {
                crossed,
                ref ty,
                ref former,
                predicate,
            } => LocatedDefect::Immobile {
                crossed,
                ty: self.value_type(ty)?,
                former: self.value_type(former)?,
                predicate,
            },
            Located::CapabilityMissing { ref world } => LocatedDefect::CapabilityMissing {
                world: self.world(world)?,
            },
            Located::CapabilityCaptured { ref world, by } => LocatedDefect::CapabilityCaptured {
                world: self.world(world)?,
                by,
            },
            Located::Elsewhere { ref bound } => LocatedDefect::Elsewhere {
                bound: self.world(bound)?,
            },
            Located::HoldElsewhere { ref wanted } => LocatedDefect::HoldElsewhere {
                wanted: self.world(wanted)?,
            },
            Located::OpenedElsewhere {
                ref written,
                ref handle,
            } => LocatedDefect::OpenedElsewhere {
                written: self.declared(written)?,
                handle: self.declared(handle)?,
            },
            Located::Unlocated => LocatedDefect::Unlocated,
            Located::UndeclaredWorld { ref world } => LocatedDefect::UndeclaredWorld {
                world: self.reference(world)?,
            },
            Located::HostWorldUndeclared => LocatedDefect::HostWorldUndeclared,
            Located::MarkUnfounded {
                ref atom,
                ref former,
                predicate,
            } => LocatedDefect::MarkUnfounded {
                atom: self.reference(atom)?,
                former: self.value_type(former)?,
                predicate,
            },
            Located::EntryNamed { ref constant } => LocatedDefect::EntryNamed {
                constant: self.reference(constant)?,
            },
            Located::EntryUngranted { ref constant } => LocatedDefect::EntryUngranted {
                constant: self.reference(constant)?,
            },
            Located::NotAHandle { ref found } => LocatedDefect::NotAHandle {
                found: self.value_type(found)?,
            },
        })
    }

    /// What `forcing` names an unanswered slot's call forces.
    ///
    /// # Specification
    /// trivial.
    fn forced(
        &mut self,
        forcing: &Forcing,
    ) -> Result<gandr_core_checker::Forced, seating::Absent>
    {
        Ok(match *forcing {
            Forcing::Type(ref ty) => gandr_core_checker::Forced::Type(self.value_type(ty)?),
            Forcing::Unforced => gandr_core_checker::Forced::Unforced,
        })
    }

    /// The checker's refusal `stored` names, each node the refusal's next.
    ///
    /// # Specification
    /// trivial.
    fn refusal(
        &mut self,
        stored: &Refusal,
    ) -> Result<CheckRefusal, seating::Absent>
    {
        Ok(refusal_seat!(self, stored))
    }

    /// The type node at `placed`, or why there is none.
    ///
    /// # Specification
    /// trivial.
    fn expected<Reason>(
        &mut self,
        placed: Maybe<Placed, Reason>,
    ) -> Result<Maybe<TypeNode, Reason>, seating::Absent>
    {
        Ok(match placed {
            Maybe::Present(placed) => Maybe::Present(type_node_of(self.node(placed)?)?),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        })
    }

    /// The value type at `placed`.
    ///
    /// # Specification
    /// trivial.
    fn value_type_at(
        &mut self,
        placed: Placed,
    ) -> Result<ValueTypeId, seating::Absent>
    {
        value_type_of(self.node(placed)?)
    }

    /// The failure of the run refused with `refusal`, its parts seated.
    ///
    /// # Specification
    /// trivial.
    fn failure(
        &mut self,
        refusal: CheckRefusal,
        parts: &FailureParts,
    ) -> Result<Failure, seating::Absent>
    {
        let mut obligations = Vec::with_capacity(parts.obligations.len());
        for obligation in &parts.obligations {
            let at = core_node_of(self.node(obligation.at)?);
            let expected = self.expected(obligation.expected)?;
            let mut binders = Vec::with_capacity(obligation.binders.len());
            for &binder in &obligation.binders {
                binders.push(self.value_type_at(binder)?);
            }
            obligations.push(Obligation::new(obligation.role, at, expected, binders));
        }
        let pursuit = Pursuit::new(
            core_node_of(self.node(parts.pursuit.at)?),
            self.expected(parts.pursuit.expected)?,
            parts.pursuit.stage,
        );
        let mut hypotheses = Vec::with_capacity(parts.hypotheses.len());
        for &hypothesis in &parts.hypotheses {
            hypotheses.push(self.value_type_at(hypothesis)?);
        }
        let mut endpoints = Vec::with_capacity(parts.endpoints.len());
        for endpoint in &parts.endpoints {
            endpoints.push(LiveEndpoint {
                endpoint: Endpoint {
                    fork: computation_of(self.node(endpoint.fork)?)?,
                    side: endpoint.side,
                },
                state: self.value_type_at(endpoint.state)?,
                use_state: endpoint.use_state,
            });
        }
        let solved = match parts.solved {
            Maybe::Present(compared) => Some(Compared {
                expected: self.expected(compared.expected)?,
                found: self.expected(compared.found)?,
                unfolded: self.expected(compared.unfolded)?,
            }),
            Maybe::Absent(solved::Absent::Unchanged) => None,
        };
        Ok(Failure::seated(
            refusal,
            obligations,
            pursuit,
            hypotheses,
            endpoints,
            solved,
        ))
    }
}

/// The arena node of a core node.
///
/// # Specification
/// trivial.
const fn core_arena_node(node: CoreNode) -> ArenaNode
{
    match node {
        CoreNode::Term(TermNode::Value(id)) => ArenaNode::Value(id),
        CoreNode::Term(TermNode::Computation(id)) => ArenaNode::Computation(id),
        CoreNode::Type(node) => type_arena_node(node),
    }
}

/// The arena node of a type node.
///
/// # Specification
/// trivial.
pub const fn type_arena_node(node: TypeNode) -> ArenaNode
{
    match node {
        TypeNode::Value(id) => ArenaNode::ValueType(id),
        TypeNode::Computation(id) => ArenaNode::CompType(id),
    }
}

/// The core node of an arena node.
///
/// # Specification
/// trivial.
const fn core_node_of(node: ArenaNode) -> CoreNode
{
    match node {
        ArenaNode::Value(id) => CoreNode::Term(TermNode::Value(id)),
        ArenaNode::Computation(id) => CoreNode::Term(TermNode::Computation(id)),
        ArenaNode::ValueType(id) => CoreNode::Type(TypeNode::Value(id)),
        ArenaNode::CompType(id) => CoreNode::Type(TypeNode::Computation(id)),
    }
}

/// The value an arena node is.
///
/// # Specification
/// trivial.
pub const fn value_of(node: ArenaNode) -> Result<ValueId, seating::Absent>
{
    match node {
        ArenaNode::Value(id) => Ok(id),
        ArenaNode::Computation(_) | ArenaNode::ValueType(_) | ArenaNode::CompType(_) => {
            Err(seating::Absent::IllSorted)
        },
    }
}

/// The computation an arena node is.
///
/// # Specification
/// trivial.
pub const fn computation_of(node: ArenaNode) -> Result<ComputationId, seating::Absent>
{
    match node {
        ArenaNode::Computation(id) => Ok(id),
        ArenaNode::Value(_) | ArenaNode::ValueType(_) | ArenaNode::CompType(_) => {
            Err(seating::Absent::IllSorted)
        },
    }
}

/// The value type an arena node is.
///
/// # Specification
/// trivial.
pub const fn value_type_of(node: ArenaNode) -> Result<ValueTypeId, seating::Absent>
{
    match node {
        ArenaNode::ValueType(id) => Ok(id),
        ArenaNode::Value(_) | ArenaNode::Computation(_) | ArenaNode::CompType(_) => {
            Err(seating::Absent::IllSorted)
        },
    }
}

/// The computation type an arena node is.
///
/// # Specification
/// trivial.
pub const fn comp_type_of(node: ArenaNode) -> Result<CompTypeId, seating::Absent>
{
    match node {
        ArenaNode::CompType(id) => Ok(id),
        ArenaNode::Value(_) | ArenaNode::Computation(_) | ArenaNode::ValueType(_) => {
            Err(seating::Absent::IllSorted)
        },
    }
}

/// The type node an arena node is.
///
/// # Specification
/// trivial.
pub const fn type_node_of(node: ArenaNode) -> Result<TypeNode, seating::Absent>
{
    match node {
        ArenaNode::ValueType(id) => Ok(TypeNode::Value(id)),
        ArenaNode::CompType(id) => Ok(TypeNode::Computation(id)),
        ArenaNode::Value(_) | ArenaNode::Computation(_) => Err(seating::Absent::IllSorted),
    }
}

/// The term node an arena node is.
///
/// # Specification
/// trivial.
const fn term_node_of(node: ArenaNode) -> Result<TermNode, seating::Absent>
{
    match node {
        ArenaNode::Value(id) => Ok(TermNode::Value(id)),
        ArenaNode::Computation(id) => Ok(TermNode::Computation(id)),
        ArenaNode::ValueType(_) | ArenaNode::CompType(_) => Err(seating::Absent::IllSorted),
    }
}

#[cfg(test)]
mod tests;
