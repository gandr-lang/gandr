//! Where a precisely counted runtime duplicates, drops and reuses a value,
//! read off the carried supports of the command IL one node at a time.
//!
//! Only intuitionistic producer variables (`Γ`) are counted. A binding owns
//! one reference. A node whose children name a variable `k` times past their
//! binders duplicates it `k − 1` times before it runs; a binder whose body does
//! not name its bound variable drops it on entry; the arms of a match share
//! their context, so an arm drops each name the match received that the arm
//! does not name. Linear residents (`Σ`) are never counted — a linear value
//! leaves by being consumed or by its unwind, and a shared view lends the held
//! cell without a count — and covariables (`Δ`) name frames, which return by
//! the frame discipline.
//!
//! # Items
//!
//! - [`Ownership::of`] reads every node reachable from its roots once and never
//!   walks below a node: each rule compares a node's support with its
//!   children's, which minting already carried.
//! - [`Entry`] is one node's reading: the duplications before it runs and, per
//!   child, the drops on entry and the captures a suspended body duplicates on
//!   entry.
//! - [`Runs`] says how often a suspension's body may run. A nominal match's
//!   branch, the curried objects that take the branch's fields, and a thunk or
//!   object cut straight against a frame run once and hand their captures to
//!   their bodies; any other may run its body more than once, so the suspension
//!   keeps one reference to each capture and the body duplicates each capture
//!   it names on entry. A fold's cell branch, a handler's clauses and a stack's
//!   bind frames are kept the same way by the node that holds them.
//! - [`Reuse`] pairs a match whose scrutinee dies in a branch with a
//!   constructor of the scrutinee's size that the branch builds, reached
//!   without crossing a body that may run more than once or a choice between
//!   arms.
//!
//! # Boundaries
//!
//! - The table rewrites nothing: the runtime reads it where it lowers each
//!   node, and dropping what a suspension keeps is the runtime's, when the
//!   suspension itself is dropped.
//! - Constants are separate roots: a [`ProducerNode::Constant`] is a leaf.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;

use crate::boundary::NodeCount;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::CommandNode;
use crate::il::ConsumerNode;
use crate::il::DestructorTag;
use crate::il::NodeAddress;
use crate::il::Opens;
use crate::il::ProducerId;
use crate::il::ProducerNode;
use crate::il::command_children;
use crate::il::consumer_children;
use crate::il::producer_children;

/// How often a suspension's body may run.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Runs
{
    /// At most once: the body owns the captures.
    Once,
    /// Any number of times: the suspension keeps its captures and the body
    /// duplicates each one it names on entry.
    Many,
}

/// One child's share of its parent's references.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Child
{
    /// The child.
    pub node: NodeAddress,
    /// The intuitionistic names dropped on entry to the child, ascending, as
    /// the child stands: bound names it ignores, and the names an arm's
    /// siblings received that the arm ignores.
    pub drops: Box<[DeBruijnIndex]>,
    /// The captures a kept body duplicates on entry, ascending, as the body
    /// stands; empty for a body that owns what it names.
    pub entry: Box<[DeBruijnIndex]>,
}

/// One node's reading.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry
{
    /// Each intuitionistic name the node duplicates before it runs,
    /// ascending, as the node stands: a name `k` children use appears
    /// `k − 1` times.
    pub dups: Box<[DeBruijnIndex]>,
    /// The node's children in edge order.
    pub children: Box<[Child]>,
}

/// A constructor that writes into the cell of a match's dying scrutinee.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Reuse
{
    /// The cut of the scrutinee variable against the match.
    pub matched: CommandId,
    /// The arm or branch, by position.
    pub branch: NodeCount,
    /// The constructor the branch builds.
    pub built: ProducerId,
}

/// Why a reading was refused.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OwnershipRefusal
{
    /// A root or a child the arena does not hold.
    Dangling(NodeAddress),
}

/// Where every node reachable from a set of roots duplicates, drops and
/// reuses.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Ownership
{
    /// Each reachable node's reading.
    entries: BTreeMap<NodeAddress, Entry>,
    /// The suspensions whose bodies run at most once.
    once: BTreeSet<ProducerId>,
    /// The reuse pairs, in node order.
    reuses: Vec<Reuse>,
}

/// How a child edge shares its parent's references.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Share
{
    /// The child consumes a reference to each name it uses.
    Alone,
    /// One of a group of arms of which exactly one runs: the group consumes
    /// one reference to each name any arm uses, and an arm drops what it
    /// ignores.
    Arm,
    /// One of a group of bodies the node keeps and may run many times: the
    /// node keeps one reference to each name any body uses, and each body
    /// duplicates what it names on entry.
    Kept,
}

/// A child edge as the reading sees it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
struct Edge
{
    /// The child.
    node: NodeAddress,
    /// How it shares.
    share: Share,
    /// The intuitionistic producer binders the parent opens over it.
    depth: u32,
    /// The intuitionistic names it selects, as it stands, ascending.
    names: Vec<u32>,
}

impl Ownership
{
    /// Read every node reachable from `roots`.
    ///
    /// # Specification
    /// - ensures: one [`Entry`] per reachable node; each name a node's children
    ///   consume `k ≥ 2` references to appears `k − 1` times in its
    ///   duplications; each bound name a child ignores, and each name an arm's
    ///   group consumes that the arm ignores, is dropped on entry to the child;
    ///   a kept body duplicates on entry each capture it names; a root
    ///   suspension runs many times.
    /// - panics: none.
    /// - intension: one visit per reachable node; each rule reads the node's
    ///   and its children's carried supports and nothing below them.
    ///
    /// # Errors
    /// [`OwnershipRefusal::Dangling`] for a root or child the arena does not
    /// hold.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — contraction, weakening, a match's arms, a kept and a
    ///   once-run body, a linear name, and the probe's `step` reuse each read
    ///   as stated.
    /// - witness: `ownership::tests::a_name_two_children_use_is_duplicated_once`
    /// - witness: `ownership::tests::an_ignored_binder_is_dropped_on_entry`
    /// - witness: `ownership::tests::an_arm_drops_what_its_sibling_uses`
    /// - witness: `ownership::tests::a_kept_body_duplicates_its_captures_on_entry`
    /// - witness: `ownership::tests::a_linear_name_is_never_counted`
    /// - witness: `ownership::tests::a_nullary_match_reuses_nothing`
    /// - witness: `ownership::tests::a_branch_rebuilding_its_scrutinee_reuses_the_cell`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |ownership| roots.iter().all(|&root| ownership.entry(root).is_some())))]
    #[inline]
    pub fn of(
        arena: &CommandArena,
        roots: &[NodeAddress],
    ) -> Result<Self, OwnershipRefusal>
    {
        let reachable = reachable(arena, roots)?;
        let once = once(arena, roots, &reachable)?;
        let mut ownership = Self {
            entries: BTreeMap::new(),
            once,
            reuses: Vec::new(),
        };
        for &node in &reachable {
            let entry = ownership.entry_of(arena, node)?;
            ownership.entries.insert(node, entry);
        }
        for &node in &reachable {
            if let NodeAddress::Command(cut) = node {
                ownership.pair(arena, cut)?;
            }
        }
        Ok(ownership)
    }

    /// The reading of `node`, when it was reached.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn entry(
        &self,
        node: NodeAddress,
    ) -> Option<&Entry>
    {
        self.entries.get(&node)
    }

    /// How often the body of `suspension` may run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn runs(
        &self,
        suspension: ProducerId,
    ) -> Runs
    {
        if self.once.contains(&suspension) {
            Runs::Once
        }
        else {
            Runs::Many
        }
    }

    /// The reuse pairs, in node order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn reuses(&self) -> &[Reuse]
    {
        &self.reuses
    }

    /// The child edges of `node`, each with its share and the names it
    /// selects.
    ///
    /// # Specification
    /// trivial.
    fn edges(
        &self,
        arena: &CommandArena,
        node: NodeAddress,
    ) -> Result<Vec<Edge>, OwnershipRefusal>
    {
        let mut edges = Vec::new();
        visit(arena, node, |child, opens| {
            let depth = u32::try_from(usize::from(opens.producers.depth(Zone::Intuitionistic)))
                .unwrap_or(u32::MAX);
            let names = arena
                .node_scope(child)
                .ok_or(OwnershipRefusal::Dangling(child))?
                .producers()
                .indices(Zone::Intuitionistic)
                .map(u32::from)
                .collect();
            edges.push(Edge {
                node: child,
                share: Share::Alone,
                depth,
                names,
            });
            Ok(())
        })?;
        self.share(arena, node, &mut edges)?;
        Ok(edges)
    }

    /// Mark the edges of `node` that are arms or kept bodies.
    ///
    /// # Specification
    /// trivial.
    fn share(
        &self,
        arena: &CommandArena,
        node: NodeAddress,
        edges: &mut [Edge],
    ) -> Result<(), OwnershipRefusal>
    {
        let dangling = OwnershipRefusal::Dangling(node);
        let mut mark = |from: usize, to: usize, share: Share| {
            for edge in edges.iter_mut().take(to).skip(from) {
                edge.share = share;
            }
        };
        match node {
            NodeAddress::Producer(id) => match *arena.producer(id).ok_or(dangling)? {
                ProducerNode::Thunk { .. } | ProducerNode::Cocase { .. } => {
                    let share = match self.runs(id) {
                        Runs::Once => Share::Arm,
                        Runs::Many => Share::Kept,
                    };
                    mark(0, usize::MAX, share);
                },
                ProducerNode::Fixpoint { .. } => mark(0, usize::MAX, Share::Kept),
                ProducerNode::Reify(ref frames) => {
                    let mut at = 0_usize;
                    for frame in frames.iter() {
                        match *frame {
                            gandr_core_term::control::StackFrame::Apply(_) => {
                                at = at.saturating_add(1);
                            },
                            gandr_core_term::control::StackFrame::Bind(_) => {
                                mark(at, at.saturating_add(1), Share::Kept);
                                at = at.saturating_add(1);
                            },
                            gandr_core_term::control::StackFrame::Project(_) => {},
                        }
                    }
                },
                ProducerNode::Primitive { .. }
                | ProducerNode::Variable { .. }
                | ProducerNode::Constant(_)
                | ProducerNode::Literal(_)
                | ProducerNode::Code(_)
                | ProducerNode::Constructor { .. }
                | ProducerNode::Mu { .. } => {},
            },
            NodeAddress::Consumer(id) => match *arena.consumer(id).ok_or(dangling)? {
                ConsumerNode::Case { .. } => mark(0, usize::MAX, Share::Arm),
                ConsumerNode::DataCase { ref branches, .. } => {
                    mark(0, branches.len(), Share::Arm);
                },
                // reason: the cell branch runs once per element.
                ConsumerNode::ListFold { .. } => mark(1, 2, Share::Kept),
                ConsumerNode::Covariable(_)
                | ConsumerNode::MuTilde { .. }
                | ConsumerNode::Destructor { .. }
                | ConsumerNode::Select { .. }
                | ConsumerNode::Top => {},
            },
            NodeAddress::Command(id) => match *arena.command(id).ok_or(dangling)? {
                // reason: the subject and the return clause precede the
                // clauses, which run once per perform the handler answers.
                CommandNode::Handle { ref clauses, .. } => {
                    mark(2, clauses.len().saturating_add(2), Share::Kept);
                },
                CommandNode::Perform { .. }
                | CommandNode::Resume { .. }
                | CommandNode::Abandon { .. }
                | CommandNode::Reset { .. }
                | CommandNode::Shift { .. }
                | CommandNode::Cut { .. }
                | CommandNode::Memory { .. } => {},
            },
        }
        Ok(())
    }

    /// The reading of one node.
    ///
    /// # Specification
    /// trivial.
    fn entry_of(
        &self,
        arena: &CommandArena,
        node: NodeAddress,
    ) -> Result<Entry, OwnershipRefusal>
    {
        let edges = self.edges(arena, node)?;
        let outer = |edge: &Edge| -> Vec<u32> {
            edge.names
                .iter()
                .filter_map(|&name| name.checked_sub(edge.depth))
                .collect()
        };
        // How many references each name the node's children consume: one per
        // edge sharing alone, one per group of arms or of kept bodies.
        let mut uses: BTreeMap<u32, u32> = BTreeMap::new();
        let mut arms: BTreeSet<u32> = BTreeSet::new();
        let mut kept: BTreeSet<u32> = BTreeSet::new();
        for edge in &edges {
            for name in outer(edge) {
                match edge.share {
                    Share::Alone => {
                        let count = uses.entry(name).or_default();
                        *count = count.saturating_add(1);
                    },
                    Share::Arm => {
                        arms.insert(name);
                    },
                    Share::Kept => {
                        kept.insert(name);
                    },
                }
            }
        }
        for name in arms.iter().chain(kept.iter()) {
            let count = uses.entry(*name).or_default();
            *count = count.saturating_add(1);
        }
        let dups = uses
            .iter()
            .flat_map(|(&name, &count)| {
                core::iter::repeat_n(DeBruijnIndex::from(name), {
                    let extra = count.saturating_sub(1);
                    usize::try_from(extra).unwrap_or(usize::MAX)
                })
            })
            .collect();
        let children = edges
            .iter()
            .map(|edge| {
                let selects = |name: u32| edge.names.binary_search(&name).is_ok();
                let mut drops: Vec<DeBruijnIndex> = (0 .. edge.depth)
                    .filter(|&bound| !selects(bound))
                    .map(DeBruijnIndex::from)
                    .collect();
                if edge.share == Share::Arm {
                    drops.extend(
                        arms.iter()
                            .filter_map(|&name| name.checked_add(edge.depth))
                            .filter(|&name| !selects(name))
                            .map(DeBruijnIndex::from),
                    );
                }
                let entry = match edge.share {
                    Share::Kept => edge
                        .names
                        .iter()
                        .copied()
                        .filter(|&name| name >= edge.depth)
                        .map(DeBruijnIndex::from)
                        .collect(),
                    Share::Alone | Share::Arm => Box::default(),
                };
                Child {
                    node: edge.node,
                    drops: drops.into_boxed_slice(),
                    entry,
                }
            })
            .collect();
        Ok(Entry { dups, children })
    }

    /// Record the reuse pairs of `cut` when it matches a variable.
    ///
    /// # Specification
    /// trivial.
    fn pair(
        &mut self,
        arena: &CommandArena,
        cut: CommandId,
    ) -> Result<(), OwnershipRefusal>
    {
        let dangling = OwnershipRefusal::Dangling(NodeAddress::Command(cut));
        let CommandNode::Cut {
            producer, consumer, ..
        } = *arena.command(cut).ok_or(dangling)?
        else {
            return Ok(());
        };
        let ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index,
        } = *arena.producer(producer).ok_or(dangling)?
        else {
            return Ok(());
        };
        let scrutinee = u32::from(index);
        // reason: a match that names its scrutinee again holds a second
        // reference, so the cell is never unique where the arm runs.
        if self
            .edges(arena, NodeAddress::Consumer(consumer))?
            .iter()
            .any(|edge| {
                edge.names
                    .iter()
                    .any(|&name| name.checked_sub(edge.depth) == Some(scrutinee))
            })
        {
            return Ok(());
        }
        let mut found = Vec::new();
        match *arena.consumer(consumer).ok_or(dangling)? {
            ConsumerNode::Case { ref arms } => {
                for (position, arm) in arms.iter().enumerate() {
                    let size = NodeCount::from(
                        usize::from(arm.constructor.producer_arity())
                            .saturating_add(usize::from(arm.constructor.consumer_arity())),
                    );
                    if let Some(built) = self.built(arena, NodeAddress::Command(arm.body), size)? {
                        found.push((position, built));
                    }
                }
            },
            ConsumerNode::DataCase { ref branches, .. } => {
                for (position, &branch) in branches.iter().enumerate() {
                    let (body, size) = curried(arena, branch)?;
                    if let Some(body) = body
                        && let Some(built) = self.built(arena, NodeAddress::Command(body), size)?
                    {
                        found.push((position, built));
                    }
                }
            },
            ConsumerNode::Covariable(_)
            | ConsumerNode::MuTilde { .. }
            | ConsumerNode::Destructor { .. }
            | ConsumerNode::Select { .. }
            | ConsumerNode::ListFold { .. }
            | ConsumerNode::Top => {},
        }
        self.reuses
            .extend(found.into_iter().map(|(position, built)| Reuse {
                matched: cut,
                branch: NodeCount::from(position),
                built,
            }));
        Ok(())
    }

    /// The first constructor of `size` fields reached from `from` through
    /// edges that run once and choose no arm, in edge order; none for a
    /// nullary head, which has no cell.
    ///
    /// # Specification
    /// trivial.
    fn built(
        &self,
        arena: &CommandArena,
        from: NodeAddress,
        size: NodeCount,
    ) -> Result<Option<ProducerId>, OwnershipRefusal>
    {
        let size = usize::from(size);
        if size == 0 {
            return Ok(None);
        }
        let mut pending = Vec::from([from]);
        while let Some(node) = pending.pop() {
            if let NodeAddress::Producer(id) = node
                && let ProducerNode::Constructor {
                    ref producers,
                    ref consumers,
                    ..
                } = *arena.producer(id).ok_or(OwnershipRefusal::Dangling(node))?
                && producers.len().saturating_add(consumers.len()) == size
            {
                return Ok(Some(id));
            }
            let edges = self.edges(arena, node)?;
            // reason: a node with one arm chooses nothing; a once-run
            // suspension's single body is that arm.
            let single = edges.len() == 1;
            for edge in edges.iter().rev() {
                match edge.share {
                    Share::Alone => pending.push(edge.node),
                    Share::Arm if single => pending.push(edge.node),
                    Share::Arm | Share::Kept => {},
                }
            }
        }
        Ok(None)
    }
}

/// Visit the children of `node` beside the binders it opens over each.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`OwnershipRefusal::Dangling`] when `node` is not held, or `each`'s first
/// refusal.
fn visit<Each>(
    arena: &CommandArena,
    node: NodeAddress,
    each: Each,
) -> Result<(), OwnershipRefusal>
where
    Each: FnMut(NodeAddress, Opens) -> Result<(), OwnershipRefusal>,
{
    let dangling = OwnershipRefusal::Dangling(node);
    match node {
        NodeAddress::Producer(id) => producer_children(arena.producer(id).ok_or(dangling)?, each),
        NodeAddress::Consumer(id) => consumer_children(arena.consumer(id).ok_or(dangling)?, each),
        NodeAddress::Command(id) => command_children(arena.command(id).ok_or(dangling)?, each),
    }
}

/// Every node reachable from `roots`, each once, in first-visit order.
///
/// # Specification
/// trivial.
fn reachable(
    arena: &CommandArena,
    roots: &[NodeAddress],
) -> Result<Vec<NodeAddress>, OwnershipRefusal>
{
    let mut seen = BTreeSet::new();
    let mut order = Vec::new();
    let mut pending: Vec<NodeAddress> = roots.iter().rev().copied().collect();
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        order.push(node);
        let mut children = Vec::new();
        visit(arena, node, |child, _| {
            children.push(child);
            Ok(())
        })?;
        pending.extend(children.into_iter().rev());
    }
    Ok(order)
}

/// The suspensions among `reachable` whose bodies run at most once: those no
/// root is and every occurrence of which runs them once.
///
/// # Specification
/// trivial.
fn once(
    arena: &CommandArena,
    roots: &[NodeAddress],
    reachable: &[NodeAddress],
) -> Result<BTreeSet<ProducerId>, OwnershipRefusal>
{
    let mut chained = BTreeSet::new();
    for &node in reachable {
        if let NodeAddress::Consumer(id) = node
            && let ConsumerNode::DataCase { ref branches, .. } =
                *arena.consumer(id).ok_or(OwnershipRefusal::Dangling(node))?
        {
            for &branch in branches {
                chain(arena, branch, &mut chained)?;
            }
        }
    }
    let mut once = BTreeSet::new();
    let mut many: BTreeSet<ProducerId> = roots
        .iter()
        .filter_map(|&root| match root {
            NodeAddress::Producer(id) => Some(id),
            NodeAddress::Consumer(_) | NodeAddress::Command(_) => None,
        })
        .collect();
    for &node in reachable {
        let mut occurrences = Vec::new();
        let runs_once = |child: ProducerId| -> Result<Runs, OwnershipRefusal> {
            if chained.contains(&child) {
                return Ok(Runs::Once);
            }
            let NodeAddress::Command(id) = node
            else {
                return Ok(Runs::Many);
            };
            let CommandNode::Cut {
                producer, consumer, ..
            } = *arena.command(id).ok_or(OwnershipRefusal::Dangling(node))?
            else {
                return Ok(Runs::Many);
            };
            let frame = arena
                .consumer(consumer)
                .ok_or(OwnershipRefusal::Dangling(NodeAddress::Consumer(consumer)))?;
            Ok(match *frame {
                ConsumerNode::Destructor {
                    tag: DestructorTag::Force | DestructorTag::Apply | DestructorTag::Project(_),
                    ..
                } if producer == child => Runs::Once,
                ConsumerNode::Covariable(_)
                | ConsumerNode::MuTilde { .. }
                | ConsumerNode::Destructor { .. }
                | ConsumerNode::Case { .. }
                | ConsumerNode::DataCase { .. }
                | ConsumerNode::Select { .. }
                | ConsumerNode::ListFold { .. }
                | ConsumerNode::Top => Runs::Many,
            })
        };
        visit(arena, node, |child, _| {
            if let NodeAddress::Producer(id) = child
                && let Some(
                    &(ProducerNode::Thunk { .. }
                    | ProducerNode::Fixpoint { .. }
                    | ProducerNode::Cocase { .. }),
                ) = arena.producer(id)
            {
                occurrences.push(id);
            }
            Ok(())
        })?;
        for id in occurrences {
            let fixpoint = matches!(arena.producer(id), Some(&ProducerNode::Fixpoint { .. }));
            match (runs_once(id)?, fixpoint) {
                (Runs::Once, false) => {
                    once.insert(id);
                },
                (Runs::Once | Runs::Many, _) => {
                    many.insert(id);
                },
            }
        }
    }
    Ok(once.difference(&many).copied().collect())
}

/// Add a nominal match's branch and the curried objects that take its fields
/// to `chained`: `{force(α) ⇒ ⟨cocase {apply(x; α) ⇒ …} |− α0⟩}`, each
/// level's body cutting the next object against its own continuation.
///
/// # Specification
/// trivial.
fn chain(
    arena: &CommandArena,
    branch: ProducerId,
    chained: &mut BTreeSet<ProducerId>,
) -> Result<(), OwnershipRefusal>
{
    let dangling = |id| OwnershipRefusal::Dangling(NodeAddress::Producer(id));
    let ProducerNode::Thunk { body } = *arena.producer(branch).ok_or_else(|| dangling(branch))?
    else {
        return Ok(());
    };
    chained.insert(branch);
    let mut at = body;
    while let Some(object) = applied(arena, at)? {
        chained.insert(object);
        let Some(&ProducerNode::Cocase { ref arms }) = arena.producer(object)
        else {
            break;
        };
        let Some(arm) = arms.first()
        else {
            break;
        };
        at = arm.body;
    }
    Ok(())
}

/// The object `body` cuts against its own continuation, when it is a
/// single-arm `apply` object.
///
/// # Specification
/// trivial.
fn applied(
    arena: &CommandArena,
    body: CommandId,
) -> Result<Option<ProducerId>, OwnershipRefusal>
{
    let CommandNode::Cut {
        producer, consumer, ..
    } = *arena
        .command(body)
        .ok_or(OwnershipRefusal::Dangling(NodeAddress::Command(body)))?
    else {
        return Ok(None);
    };
    let continuation = matches!(
        arena.consumer(consumer),
        Some(&ConsumerNode::Covariable(index)) if u32::from(index) == 0
    );
    let object = match arena.producer(producer) {
        Some(&ProducerNode::Cocase { ref arms }) => {
            matches!(&**arms, [arm] if arm.destructor == DestructorTag::Apply)
        },
        Some(_) | None => false,
    };
    Ok((continuation && object).then_some(producer))
}

/// The innermost body of a nominal match's branch and how many fields its
/// curried objects take.
///
/// # Specification
/// trivial.
fn curried(
    arena: &CommandArena,
    branch: ProducerId,
) -> Result<(Option<CommandId>, NodeCount), OwnershipRefusal>
{
    let ProducerNode::Thunk { body } = *arena
        .producer(branch)
        .ok_or(OwnershipRefusal::Dangling(NodeAddress::Producer(branch)))?
    else {
        return Ok((None, NodeCount::from(0_usize)));
    };
    let mut at = body;
    let mut fields = 0_usize;
    while let Some(object) = applied(arena, at)? {
        let Some(&ProducerNode::Cocase { ref arms }) = arena.producer(object)
        else {
            break;
        };
        let Some(arm) = arms.first()
        else {
            break;
        };
        at = arm.body;
        fields = fields.saturating_add(1);
    }
    Ok((Some(at), NodeCount::from(fields)))
}

#[cfg(test)]
mod tests;
