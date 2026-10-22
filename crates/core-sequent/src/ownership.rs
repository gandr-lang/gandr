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
//!   children's, which minting already carried. Every reading's names sit in
//!   one buffer, and the per-node work reuses one set of scratch buffers, so a
//!   reading allocates per table, not per node.
//! - [`Entry`] is one node's reading: the duplications before it runs, the
//!   drops on its entry, and the captures it duplicates on entry when a
//!   suspended body. The last two are its parent's to give; a node two parents
//!   give different ones has no reading.
//! - [`Runs`] says how often a suspension's body may run. A nominal match's
//!   branch, the curried objects that take its constructor's fields — as many
//!   as the match's arity for that constructor states, so a function the branch
//!   answers is not among them — and a thunk or object cut straight against a
//!   frame run once and hand their captures to their bodies; any other may run
//!   its body more than once, so the suspension keeps one reference to each
//!   capture and the body duplicates each capture it names on entry. A fold's
//!   cell branch and a handler's clauses are kept the same way by the node that
//!   holds them. A stack's bind frame owns its captures as any child does, one
//!   reference each: the stack that holds the frame is the keeper, and every
//!   resumption copies the frame's window out of it with a reference of its
//!   own.
//! - [`Reuse`] pairs a match whose scrutinee dies in a branch with a
//!   constructor of the scrutinee's size that the branch builds in the window
//!   it runs in: reached through no choice between arms and no suspension but a
//!   `μ` its cut runs where it stands, a nominal branch's curried objects being
//!   the match's to take apart where it stands.
//!
//! # Boundaries
//!
//! - The table rewrites nothing: the runtime reads it where it lowers each
//!   node, and dropping what a suspension keeps is the runtime's, when the
//!   suspension itself is dropped.
//! - Constants are separate roots: a [`ProducerNode::Constant`] is a leaf.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_theory_cell_complexes::Polarity;

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

/// One node's reading.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Entry<'reading>
{
    /// Each intuitionistic name the node duplicates before it runs,
    /// ascending, as the node stands: a name `k` children use appears
    /// `k − 1` times.
    pub dups: &'reading [DeBruijnIndex],
    /// The intuitionistic names dropped on entry to the node, ascending, as
    /// it stands: bound names it ignores, and the names an arm's siblings
    /// received that the arm ignores.
    pub drops: &'reading [DeBruijnIndex],
    /// The captures a kept body duplicates on entry, ascending, as the body
    /// stands; empty for a node that owns what it names.
    pub entered: &'reading [DeBruijnIndex],
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
    /// Each reachable node's reading, as spans of `names`, sorted by node.
    entries: Vec<(NodeAddress, Stored)>,
    /// Every reading's names, back to back.
    names: Vec<DeBruijnIndex>,
    /// The suspensions whose bodies run at most once.
    once: BTreeSet<ProducerId>,
    /// The reuse pairs, in node order.
    reuses: Vec<Reuse>,
}

/// A run of a buffer's elements.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Span
{
    /// The first element.
    start: usize,
    /// One past the last.
    end: usize,
}

/// The elements of `buffer` that `span` covers.
///
/// # Specification
/// trivial.
fn spanned<Element>(
    buffer: &[Element],
    span: Span,
) -> &[Element]
{
    buffer.get(span.start .. span.end).unwrap_or_default()
}

/// One node's reading as held: spans of the reading's names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Stored
{
    /// The duplications before the node runs.
    dups: Span,
    /// The drops on its entry.
    drops: Span,
    /// The captures it duplicates on entry.
    entered: Span,
    /// How its parents placed it.
    placed: Placement,
}

/// How a node's parents placed it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Placement
{
    /// No edge has reached it: a root.
    #[default]
    Root,
    /// Every edge reaching it gives the same drops and entry.
    Agreed,
    /// Two edges reaching it give different drops or entries.
    Ambiguous,
}

/// The buffers one reading reuses from node to node.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Scratch
{
    /// The current node's edges.
    edges: Vec<Edge>,
    /// The names the current node's edges select, back to back.
    selected: Vec<u32>,
    /// The names the current node's children consume, one per reference.
    uses: Vec<u32>,
    /// The names the current node's arms consume.
    arms: Vec<u32>,
    /// The names the current node's kept bodies consume.
    kept: Vec<u32>,
    /// The nodes a search for a rebuilt constructor has yet to visit.
    pending: Vec<NodeAddress>,
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
#[derive(Clone, Copy, Debug)]
struct Edge
{
    /// The child.
    node: NodeAddress,
    /// How it shares.
    share: Share,
    /// The intuitionistic producer binders the parent opens over it.
    depth: u32,
    /// The intuitionistic names it selects, as it stands, ascending: a span
    /// of the scratch's `selected`.
    names: Span,
}

impl Ownership
{
    /// Read every node reachable from `roots`, as `reached` lists them.
    ///
    /// # Specification
    /// - requires: `reached` is every node reachable from `roots`, each once,
    ///   in first-visit order, as [`reach`] appends them from an empty set.
    /// - ensures: one [`Entry`] per reachable node that no two edges give
    ///   different drops or entries; each name a node's children consume `k ≥
    ///   2` references to appears `k − 1` times in its duplications; each bound
    ///   name a child ignores, and each name an arm's group consumes that the
    ///   arm ignores, is dropped on entry to the child; a kept body duplicates
    ///   on entry each capture it names; a root suspension runs many times.
    /// - panics: none.
    /// - intension: one visit per reachable node; each rule reads the node's
    ///   and its children's carried supports and nothing below them, into one
    ///   name buffer, through scratch buffers reused from node to node.
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
    /// - witness: `ownership::tests::a_reified_bind_body_owns_its_captures`
    /// - witness: `ownership::tests::a_linear_name_is_never_counted`
    /// - witness: `ownership::tests::a_nullary_match_reuses_nothing`
    /// - witness: `ownership::tests::a_branch_rebuilding_its_scrutinee_reuses_the_cell`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |ownership| roots.iter().all(|&root| ownership.stored(root).is_some())))]
    #[inline]
    pub fn of(
        arena: &CommandArena,
        roots: &[NodeAddress],
        reached: &[NodeAddress],
    ) -> Result<Self, OwnershipRefusal>
    {
        let once = once(arena, roots, reached)?;
        let mut entries: Vec<(NodeAddress, Stored)> = reached
            .iter()
            .map(|&node| (node, Stored::default()))
            .collect();
        entries.sort_unstable_by_key(|&(node, _)| node);
        let mut ownership = Self {
            entries,
            names: Vec::new(),
            once,
            reuses: Vec::new(),
        };
        let mut scratch = Scratch::default();
        for &node in reached {
            ownership.read(arena, node, &mut scratch)?;
        }
        for &node in reached {
            if let NodeAddress::Command(cut) = node {
                ownership.pair(arena, cut, &mut scratch)?;
            }
        }
        Ok(ownership)
    }

    /// The reading of `node`: none when it was not reached, or when two
    /// edges reaching it give it different drops or entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn entry(
        &self,
        node: NodeAddress,
    ) -> Option<Entry<'_>>
    {
        let stored = self.stored(node)?;
        (stored.placed != Placement::Ambiguous).then(|| Entry {
            dups: spanned(&self.names, stored.dups),
            drops: spanned(&self.names, stored.drops),
            entered: spanned(&self.names, stored.entered),
        })
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

    /// Fill `scratch`'s edges with the child edges of `node`, each with its
    /// share and the names it selects.
    ///
    /// # Specification
    /// trivial.
    fn edges(
        &self,
        arena: &CommandArena,
        node: NodeAddress,
        scratch: &mut Scratch,
    ) -> Result<(), OwnershipRefusal>
    {
        scratch.edges.clear();
        scratch.selected.clear();
        let Scratch {
            ref mut edges,
            ref mut selected,
            ..
        } = *scratch;
        visit(arena, node, |child, opens| {
            let depth = u32::try_from(usize::from(opens.producers.depth(Zone::Intuitionistic)))
                .unwrap_or(u32::MAX);
            let start = selected.len();
            selected.extend(
                arena
                    .node_scope(child)
                    .ok_or(OwnershipRefusal::Dangling(child))?
                    .producers()
                    .indices(Zone::Intuitionistic)
                    .map(u32::from),
            );
            edges.push(Edge {
                node: child,
                share: Share::Alone,
                depth,
                names: Span {
                    start,
                    end: selected.len(),
                },
            });
            Ok(())
        })?;
        self.share(arena, node, &mut scratch.edges)
    }

    /// Mark the edges of `node` that are arms or kept bodies.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a case's arms each drop what a sibling uses, and a
    ///   body that may run many times duplicates its captures on entry; an edge
    ///   left unmarked does neither.
    /// - witness: `ownership::tests::an_arm_drops_what_its_sibling_uses`
    /// - witness: `ownership::tests::a_kept_body_duplicates_its_captures_on_entry`
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
                ProducerNode::Primitive { .. }
                | ProducerNode::Variable { .. }
                | ProducerNode::Constant(_)
                | ProducerNode::Literal(_)
                | ProducerNode::Code(_)
                | ProducerNode::Constructor { .. }
                | ProducerNode::Reify(_)
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

    /// Read `node`: its duplications, and the drops and entry it gives each
    /// child.
    ///
    /// # Specification
    /// trivial.
    fn read(
        &mut self,
        arena: &CommandArena,
        node: NodeAddress,
        scratch: &mut Scratch,
    ) -> Result<(), OwnershipRefusal>
    {
        self.edges(arena, node, scratch)?;
        let Scratch {
            ref edges,
            ref selected,
            ref mut uses,
            ref mut arms,
            ref mut kept,
            ..
        } = *scratch;
        // How many references each name the node's children consume: one per
        // edge sharing alone, one per group of arms or of kept bodies.
        uses.clear();
        arms.clear();
        kept.clear();
        for edge in edges {
            let outer = spanned(selected, edge.names)
                .iter()
                .filter_map(|&name| name.checked_sub(edge.depth));
            match edge.share {
                Share::Alone => uses.extend(outer),
                Share::Arm => arms.extend(outer),
                Share::Kept => kept.extend(outer),
            }
        }
        arms.sort_unstable();
        arms.dedup();
        kept.sort_unstable();
        kept.dedup();
        uses.extend_from_slice(arms);
        uses.extend_from_slice(kept);
        uses.sort_unstable();
        let start = self.names.len();
        let mut previous = None;
        for &name in uses.iter() {
            if previous == Some(name) {
                self.names.push(DeBruijnIndex::from(name));
            }
            previous = Some(name);
        }
        let dups = Span {
            start,
            end: self.names.len(),
        };
        if let Some(stored) = self.stored_mut(node) {
            stored.dups = dups;
        }
        for edge in edges {
            let chosen = spanned(selected, edge.names);
            let selects = |name: u32| chosen.binary_search(&name).is_ok();
            let start = self.names.len();
            self.names.extend(
                (0 .. edge.depth)
                    .filter(|&bound| !selects(bound))
                    .map(DeBruijnIndex::from),
            );
            if edge.share == Share::Arm {
                self.names.extend(
                    arms.iter()
                        .filter_map(|&name| name.checked_add(edge.depth))
                        .filter(|&name| !selects(name))
                        .map(DeBruijnIndex::from),
                );
            }
            let drops = Span {
                start,
                end: self.names.len(),
            };
            if edge.share == Share::Kept {
                self.names.extend(
                    chosen
                        .iter()
                        .copied()
                        .filter(|&name| name >= edge.depth)
                        .map(DeBruijnIndex::from),
                );
            }
            let entered = Span {
                start: drops.end,
                end: self.names.len(),
            };
            self.place(edge.node, drops, entered);
        }
        Ok(())
    }

    /// Give `node` the drops and entry an edge reaching it records, just
    /// pushed onto the names from `drops`' start: kept for the first edge,
    /// taken back for a later edge that agrees, and marking the node
    /// ambiguous for one that does not.
    ///
    /// # Specification
    /// trivial.
    fn place(
        &mut self,
        node: NodeAddress,
        drops: Span,
        entered: Span,
    )
    {
        let names = &self.names;
        let Some(stored) = self
            .entries
            .binary_search_by_key(&node, |&(held, _)| held)
            .ok()
            .and_then(|at| self.entries.get_mut(at))
            .map(|entry| &mut entry.1)
        else {
            self.names.truncate(drops.start);
            return;
        };
        match stored.placed {
            Placement::Root => {
                stored.drops = drops;
                stored.entered = entered;
                stored.placed = Placement::Agreed;
                return;
            },
            Placement::Agreed => {
                let agrees = spanned(names, stored.drops) == spanned(names, drops)
                    && spanned(names, stored.entered) == spanned(names, entered);
                if !agrees {
                    stored.placed = Placement::Ambiguous;
                }
            },
            Placement::Ambiguous => {},
        }
        self.names.truncate(drops.start);
    }

    /// The held reading of `node`.
    ///
    /// # Specification
    /// trivial.
    fn stored(
        &self,
        node: NodeAddress,
    ) -> Option<&Stored>
    {
        let at = self
            .entries
            .binary_search_by_key(&node, |&(held, _)| held)
            .ok()?;
        self.entries.get(at).map(|entry| &entry.1)
    }

    /// The held reading of `node`, to fill in.
    ///
    /// # Specification
    /// trivial.
    fn stored_mut(
        &mut self,
        node: NodeAddress,
    ) -> Option<&mut Stored>
    {
        let at = self
            .entries
            .binary_search_by_key(&node, |&(held, _)| held)
            .ok()?;
        self.entries.get_mut(at).map(|entry| &mut entry.1)
    }

    /// Record the reuse pairs of `cut` when it matches a variable.
    ///
    /// # Specification
    /// trivial.
    fn pair(
        &mut self,
        arena: &CommandArena,
        cut: CommandId,
        scratch: &mut Scratch,
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
        self.edges(arena, NodeAddress::Consumer(consumer), scratch)?;
        if scratch.edges.iter().any(|edge| {
            spanned(&scratch.selected, edge.names)
                .iter()
                .any(|&name| name.checked_sub(edge.depth) == Some(scrutinee))
        }) {
            return Ok(());
        }
        match *arena.consumer(consumer).ok_or(dangling)? {
            ConsumerNode::Case { ref arms } => {
                for (position, arm) in arms.iter().enumerate() {
                    let size = NodeCount::from(
                        usize::from(arm.constructor.producer_arity())
                            .saturating_add(usize::from(arm.constructor.consumer_arity())),
                    );
                    if let Some(built) =
                        self.built(arena, NodeAddress::Command(arm.body), size, scratch)?
                    {
                        self.reuses.push(Reuse {
                            matched: cut,
                            branch: NodeCount::from(position),
                            built,
                        });
                    }
                }
            },
            ConsumerNode::DataCase {
                ref branches,
                ref arities,
                ..
            } => {
                for (position, (&branch, &arity)) in branches.iter().zip(arities).enumerate() {
                    let size = NodeCount::from(usize::from(arity));
                    if let Some(body) = curried(arena, branch, arity)?
                        && let Some(built) =
                            self.built(arena, NodeAddress::Command(body), size, scratch)?
                    {
                        self.reuses.push(Reuse {
                            matched: cut,
                            branch: NodeCount::from(position),
                            built,
                        });
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
        Ok(())
    }

    /// The first constructor of `size` fields reached from `from` through
    /// edges that run once, choose no arm and stay in the window `from` runs
    /// in, in edge order; none for a nullary head, which has no cell. A
    /// suspension's body runs in a window of its own, out of the token's
    /// reach, so the walk stops at a thunk, a fixpoint, an object and a `μ`
    /// other than one a cut runs where it stands. It stops too at every
    /// command that may run code outside the window — a call, a nominal
    /// match's branch, a fold, a selection, an effect or a delimiter — since
    /// that code may capture the window and replay it more than once, and
    /// each replay would build into the one block the token names.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a branch pairs the constructor it rebuilds, through a
    ///   `μ` run where it stands, the binder after it, a single-arm match and a
    ///   constructor of another field count around it, and pairs nothing past a
    ///   thunk, a call, a suspended `μ` or a choice of arms.
    /// - witness: `ownership::tests::a_branch_rebuilding_its_scrutinee_reuses_the_cell`
    fn built(
        &self,
        arena: &CommandArena,
        from: NodeAddress,
        size: NodeCount,
        scratch: &mut Scratch,
    ) -> Result<Option<ProducerId>, OwnershipRefusal>
    {
        let size = usize::from(size);
        if size == 0 {
            return Ok(None);
        }
        let mut pending = core::mem::take(&mut scratch.pending);
        pending.clear();
        pending.push(from);
        let mut built = None;
        while let Some(node) = pending.pop() {
            let mut inline = None;
            match node {
                NodeAddress::Producer(id) => {
                    match *arena.producer(id).ok_or(OwnershipRefusal::Dangling(node))? {
                        ProducerNode::Constructor {
                            ref producers,
                            ref consumers,
                            ..
                        } if producers.len().saturating_add(consumers.len()) == size => {
                            built = Some(id);
                            break;
                        },
                        ProducerNode::Thunk { .. }
                        | ProducerNode::Fixpoint { .. }
                        | ProducerNode::Cocase { .. }
                        | ProducerNode::Mu { .. } => continue,
                        ProducerNode::Constructor { .. }
                        | ProducerNode::Variable { .. }
                        | ProducerNode::Constant(_)
                        | ProducerNode::Literal(_)
                        | ProducerNode::Code(_)
                        | ProducerNode::Primitive { .. }
                        | ProducerNode::Reify(_) => {},
                    }
                },
                NodeAddress::Command(id) => {
                    if extent(arena, id)? == Extent::Beyond {
                        continue;
                    }
                    inline = ran(arena, id)?;
                },
                NodeAddress::Consumer(_) => {},
            }
            self.edges(arena, node, scratch)?;
            // reason: a node with one arm chooses nothing; a once-run
            // suspension's single body is that arm.
            let single = scratch.edges.len() == 1;
            for edge in scratch.edges.iter().rev() {
                let next = match inline {
                    Some((mu, body)) if edge.node == NodeAddress::Producer(mu) => {
                        NodeAddress::Command(body)
                    },
                    Some(_) | None => edge.node,
                };
                match edge.share {
                    Share::Alone => pending.push(next),
                    Share::Arm if single => pending.push(next),
                    Share::Arm | Share::Kept => {},
                }
            }
        }
        scratch.pending = pending;
        Ok(built)
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

/// Walk from `roots` to every node `seen` does not hold yet.
///
/// Each node is appended to `order` and added to `seen` once, in first-visit
/// order: a node before its children, the children in order. Called again
/// with more roots and the same two, it extends the walk without revisiting a
/// node.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`OwnershipRefusal::Dangling`] for a root or child the arena does not
/// hold.
#[inline]
pub fn reach(
    arena: &CommandArena,
    roots: &[NodeAddress],
    seen: &mut BTreeSet<NodeAddress>,
    order: &mut Vec<NodeAddress>,
) -> Result<(), OwnershipRefusal>
{
    let mut pending: Vec<NodeAddress> = roots.iter().rev().copied().collect();
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        order.push(node);
        // The children land on the stack in order and are reversed in place,
        // so the first is popped first.
        let from = pending.len();
        visit(arena, node, |child, _| {
            pending.push(child);
            Ok(())
        })?;
        if let Some(children) = pending.get_mut(from ..) {
            children.reverse();
        }
    }
    Ok(())
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
            && let ConsumerNode::DataCase {
                ref branches,
                ref arities,
                ..
            } = *arena.consumer(id).ok_or(OwnershipRefusal::Dangling(node))?
        {
            for (&branch, &arity) in branches.iter().zip(arities) {
                chain(arena, branch, arity, &mut chained)?;
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
    let mut occurrences = Vec::new();
    for &node in reachable {
        occurrences.clear();
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
        for &id in &occurrences {
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

/// Add a nominal match's branch and the `arity` curried objects that take
/// its constructor's fields to `chained`: `{force(α) ⇒ ⟨cocase {apply(x; α)
/// ⇒ …} |− α0⟩}`, each level's body cutting the next object against its own
/// continuation. An object past the constructor's fields is the branch's
/// answer, a function its caller may apply any number of times, and is left
/// out.
///
/// # Specification
/// trivial.
fn chain(
    arena: &CommandArena,
    branch: ProducerId,
    arity: FieldCount,
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
    for _field in 0 .. usize::from(arity) {
        let Some(object) = applied(arena, at)?
        else {
            break;
        };
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

/// How far the code a command runs reaches.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Extent
{
    /// Only code of the command's own window.
    Window,
    /// Code that may run outside the window: a call, a nominal match's
    /// branch, a selection, a fold or a control command.
    Beyond,
}

/// How far the command `id` reaches: its own window for a cut against a
/// covariable, a binder, a structural match or the top; beyond it for a cut
/// against a destructor, a nominal match, a selection or a fold, and for
/// every control command.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as `Ownership::built`: a call stops the pairing, and the
///   branch's own cuts, the binder and the single-arm match do not.
/// - witness: `ownership::tests::a_branch_rebuilding_its_scrutinee_reuses_the_cell`
fn extent(
    arena: &CommandArena,
    id: CommandId,
) -> Result<Extent, OwnershipRefusal>
{
    let CommandNode::Cut { consumer, .. } = *arena
        .command(id)
        .ok_or(OwnershipRefusal::Dangling(NodeAddress::Command(id)))?
    else {
        return Ok(Extent::Beyond);
    };
    Ok(match arena.consumer(consumer) {
        Some(
            &(ConsumerNode::Covariable(_)
            | ConsumerNode::MuTilde { .. }
            | ConsumerNode::Case { .. }
            | ConsumerNode::Top),
        ) => Extent::Window,
        Some(
            &(ConsumerNode::Destructor { .. }
            | ConsumerNode::DataCase { .. }
            | ConsumerNode::Select { .. }
            | ConsumerNode::ListFold { .. }),
        )
        | None => Extent::Beyond,
    })
}

/// The `μ` that the cut `cut` runs where it stands, and its body: every
/// cut's but the by-name side of a negative cut against a binder, which
/// suspends it.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as `Ownership::built`: a `μ` cut against a covariable or,
///   positively, against a binder pairs its constructor; a negative cut against
///   a binder pairs none.
/// - witness: `ownership::tests::a_branch_rebuilding_its_scrutinee_reuses_the_cell`
fn ran(
    arena: &CommandArena,
    cut: CommandId,
) -> Result<Option<(ProducerId, CommandId)>, OwnershipRefusal>
{
    let dangling = OwnershipRefusal::Dangling(NodeAddress::Command(cut));
    let CommandNode::Cut {
        polarity,
        producer,
        consumer,
    } = *arena.command(cut).ok_or(dangling)?
    else {
        return Ok(None);
    };
    let ProducerNode::Mu { body } = *arena.producer(producer).ok_or(dangling)?
    else {
        return Ok(None);
    };
    let binds = matches!(arena.consumer(consumer), Some(ConsumerNode::MuTilde { .. }));
    Ok((!(binds && polarity == Polarity::Negative)).then_some((producer, body)))
}

/// The body of a nominal match's branch under the `arity` curried objects
/// that take its constructor's fields; none when the branch is no thunk of
/// that many.
///
/// # Specification
/// trivial.
fn curried(
    arena: &CommandArena,
    branch: ProducerId,
    arity: FieldCount,
) -> Result<Option<CommandId>, OwnershipRefusal>
{
    let ProducerNode::Thunk { body } = *arena
        .producer(branch)
        .ok_or(OwnershipRefusal::Dangling(NodeAddress::Producer(branch)))?
    else {
        return Ok(None);
    };
    let mut at = body;
    for _field in 0 .. usize::from(arity) {
        let Some(object) = applied(arena, at)?
        else {
            return Ok(None);
        };
        let Some(&ProducerNode::Cocase { ref arms }) = arena.producer(object)
        else {
            return Ok(None);
        };
        let Some(arm) = arms.first()
        else {
            return Ok(None);
        };
        at = arm.body;
    }
    Ok(Some(at))
}

#[cfg(test)]
mod tests;
