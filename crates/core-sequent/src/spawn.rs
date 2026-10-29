//! The concurrent schedule of a run's independent cuts: each cut whose binder
//! focus marked independent spawns its writer, and the binder reads the
//! writer's answer where its reader first needs it.
//!
//! [`spawn_independent`] rewrites a marked cut `⟨μα.s |+ μ̃x.t⟩` into
//! `⟨SPAWN {force(α) ⇒ s} |+ μ̃h.t′⟩`. The spawn is a perform of [`SPAWN`] of
//! [`CELL`]. Its payload is the writer suspended as a thunk over the same
//! command, which binds the same one covariable. Its continuation binds the
//! writer's handle `h` where the cut bound `x`. In `t′`, a perform of [`READ`]
//! of `h` binds `x` again. A host that answers both operations runs the writer
//! apart from its reader, and the reader waits for the writer's answer at the
//! read.
//!
//! # The read's place
//!
//! The read descends from the binder through each cut and each perform whose
//! continuation is a value binder and whose sent producer, payload and route
//! do not name `x`. It stands before the first command that is neither, or
//! that names `x`. So a reader runs all that does not need the writer's answer
//! before it waits for that answer. A path that never names `x` still reads it
//! before its end, so the run waits for every writer it starts, as the
//! sequential schedule runs every writer. The rewrite runs bottom-up, so the
//! read of an outer cut descends through the spawns and the reads of the cuts
//! inside it.
//!
//! # Boundaries
//!
//! - **Before the lowering, not inside it.** The lowering pushes a binder's
//!   frame inside the frames of its head, so a fused writer cannot run apart
//!   from its binder. A pass over the IL leaves the lowering, its fusion and
//!   its owner counts as they are, and a run selects the pass or leaves it out.
//! - **The mark is the caller's claim.** The pass trusts that a marked writer
//!   performs nothing. A writer that names an outer marked binder still reads
//!   it, because the outer read stands before a spawn whose payload names its
//!   binder.
//! - **A writer runs after the reader's effects that precede its read.** A
//!   writer performs nothing, so only a writer that never ends tells the two
//!   schedules apart: the reader's host may end the run first.
//! - **A cut whose read the renaming refuses stays sequential.** A command
//!   whose annotation names a variable that the read's binder moves keeps its
//!   cut as focus wrote it.
//!
//! # References
//!
//! - `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: the futures design
//!   (§ futures-in-gandr item 1): the concurrent schedule of a cut, its writer
//!   spawned and its cell written once.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_term::BinderDepth;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::OperationName;
use gandr_kernel_term::ConstantIndex;

use crate::closure::ClosureRefusal;
use crate::closure::Renaming;
use crate::closure::children;
use crate::closure::counted;
use crate::closure::rebuild;
use crate::closure::rename;
use crate::definitions::Definition;
use crate::definitions::Definitions;
use crate::il::CELL;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::CommandNode;
use crate::il::ConsumerNode;
use crate::il::Independence;
use crate::il::MintRefusal;
use crate::il::NodeAddress;
use crate::il::ProducerId;
use crate::il::ProducerNode;
use crate::il::READ;
use crate::il::Route;
use crate::il::SPAWN;

/// Why the schedule of a run's independent cuts was refused.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScheduleRefusal
{
    /// A rewrite refused a node: one the arena does not hold, an index past
    /// the largest a variable carries, or a mint the arena refused.
    Rewrite(ClosureRefusal),
    /// The cell's interface did not form.
    Interface,
}

impl From<ClosureRefusal> for ScheduleRefusal
{
    /// The refusal of the rewrite the schedule runs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: ClosureRefusal) -> Self
    {
        Self::Rewrite(refusal)
    }
}

impl From<MintRefusal> for ScheduleRefusal
{
    /// A mint the arena refused, as the rewrite's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: MintRefusal) -> Self
    {
        Self::Rewrite(ClosureRefusal::Mint(refusal))
    }
}

impl fmt::Display for ScheduleRefusal
{
    /// Name the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Rewrite(refusal) => write!(f, "the spawn schedule's rewrite: {refusal}"),
            Self::Interface => f.write_str("the cell's interface did not form"),
        }
    }
}

/// Rewrite each cut whose binder is marked independent, in `root` and in
/// every transparent definition, into a spawn of its writer and a read of its
/// handle where its binder is first needed.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on `Ok`, the root and the definitions, in which every marked cut
///   that `root` or a definition reaches is a perform of [`SPAWN`] of [`CELL`],
///   save a cut whose read the renaming refused. Each spawn's continuation
///   reads its handle once on each path, by a perform of [`READ`] of [`CELL`].
///   Every other node is as focus wrote it, so an arena with no marked binder
///   gives back `root` and `definitions` as they were. On `Err`, the arena is
///   as on entry.
/// - provides: the one rewrite from the sequential schedule of a marked cut to
///   its concurrent one.
/// - fails: as Errors.
/// - panics: none.
/// - executable: none — "every marked cut" quantifies over the reachable graph.
///
/// # Errors
/// [`ScheduleRefusal::Rewrite`] for a node the arena does not hold, an index
/// past the `u32` space, or a mint the arena refuses;
/// [`ScheduleRefusal::Interface`] when the cell's interface does not form.
///
/// # Adequacy
/// - hypothesis: L2 — a marked cut spawns its writer as a thunk over its own
///   command, and its read stands past an unrelated cut and before the command
///   that names its binder; a read placed at the spawn, after the naming
///   command, or under the wrong index changes the shape. A writer that names
///   an outer marked binder reads it before its spawn, a path that never names
///   its binder reads it before its end, a marked cut inside a definition
///   spawns there, and an unmarked arena is given back unchanged.
/// - witness: `spawn::tests::a_marked_cut_spawns_its_writer_and_reads_it_where_first_named`
/// - witness: `spawn::tests::an_inner_writer_reads_the_outer_binder_before_its_spawn`
/// - witness: `spawn::tests::a_binder_never_named_is_read_before_the_end`
/// - witness: `spawn::tests::a_marked_cut_in_a_definition_spawns_there`
/// - witness: `spawn::tests::an_unmarked_arena_is_given_back_unchanged`
#[inline]
pub fn spawn_independent(
    arena: &mut CommandArena,
    (root, definitions): (CommandId, &Definitions),
) -> Result<(CommandId, Definitions), ScheduleRefusal>
{
    let entry = arena.watermark();
    let scheduled = schedule(arena, root, definitions);
    if scheduled.is_err() {
        arena.truncate_to(entry);
    }
    scheduled
}

/// [`spawn_independent`] over `definitions` alone: the definitions every run
/// of a program shares, scheduled once for all of its roots.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on `Ok`, the definitions [`spawn_independent`] gives back beside
///   any root, so a root that holds no marked cut runs over them as written. On
///   `Err`, the arena is as on entry.
/// - provides: a program's concurrent definitions, rewritten once and not on
///   each run.
/// - fails: as Errors.
/// - panics: none.
/// - executable: none — as [`spawn_independent`].
///
/// # Errors
/// As [`spawn_independent`].
///
/// # Adequacy
/// - hypothesis: L2 — a marked cut inside a definition spawns there as it does
///   beside a root, and an unmarked arena is given back unchanged with nothing
///   minted.
/// - witness: `spawn::tests::a_marked_cut_in_a_definition_spawns_there`
/// - witness: `spawn::tests::an_unmarked_arena_is_given_back_unchanged`
#[inline]
pub fn spawn_independent_definitions(
    arena: &mut CommandArena,
    definitions: &Definitions,
) -> Result<Definitions, ScheduleRefusal>
{
    let entry = arena.watermark();
    let scheduled = Images::new().and_then(|mut images| images.definitions(arena, definitions));
    if scheduled.is_err() {
        arena.truncate_to(entry);
    }
    scheduled
}

/// The schedule, leaving a refusal's partial nodes for the caller to
/// truncate.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`spawn_independent`].
fn schedule(
    arena: &mut CommandArena,
    root: CommandId,
    definitions: &Definitions,
) -> Result<(CommandId, Definitions), ScheduleRefusal>
{
    let mut images = Images::new()?;
    let NodeAddress::Command(root) = images.image(arena, NodeAddress::Command(root))?
    else {
        return Err(ClosureRefusal::Dangling(NodeAddress::Command(root)).into());
    };
    Ok((root, images.definitions(arena, definitions)?))
}

/// One step of the post-order walk.
#[derive(Clone, Copy, Debug)]
enum Step
{
    /// Schedule the node's children.
    Enter(NodeAddress),
    /// Rebuild the node over its children's images.
    Exit(NodeAddress),
}

/// The images the schedule gives the nodes it reached.
#[derive(Debug)]
struct Images
{
    /// The cell's interface, which every spawn and read performs.
    cell: EffectSig,
    /// Each node reached, beside its image.
    done: BTreeMap<NodeAddress, NodeAddress>,
}

impl Images
{
    /// No node reached yet.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`ScheduleRefusal::Interface`] when the cell's interface does not form.
    fn new() -> Result<Self, ScheduleRefusal>
    {
        Ok(Self {
            cell: EffectSig::new(EffectName::from(CELL), core::iter::empty())
                .map_err(|_conflict| ScheduleRefusal::Interface)?,
            done: BTreeMap::new(),
        })
    }

    /// The image of each of `definitions`, by position: a transparent one's
    /// producer rewritten, an opaque one kept.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`spawn_independent`].
    fn definitions(
        &mut self,
        arena: &mut CommandArena,
        definitions: &Definitions,
    ) -> Result<Definitions, ScheduleRefusal>
    {
        let mut scheduled = Definitions::new();
        for position in 0 .. usize::from(definitions.len()) {
            let definition = match definitions.get(ConstantIndex::from(position)) {
                Some(Definition::Transparent(value)) => {
                    Definition::Transparent(self.producer(arena, value)?)
                },
                Some(Definition::Opaque) | None => Definition::Opaque,
            };
            scheduled.push(definition);
        }
        Ok(scheduled)
    }

    /// The image of the producer `value`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`spawn_independent`].
    fn producer(
        &mut self,
        arena: &mut CommandArena,
        value: ProducerId,
    ) -> Result<ProducerId, ScheduleRefusal>
    {
        match self.image(arena, NodeAddress::Producer(value))? {
            NodeAddress::Producer(image) => Ok(image),
            image @ (NodeAddress::Consumer(_) | NodeAddress::Command(_)) => {
                Err(ClosureRefusal::Dangling(image).into())
            },
        }
    }

    /// The image of `root`: each node below it rebuilt over its children's
    /// images, children first, and each marked cut spawned.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`spawn_independent`].
    fn image(
        &mut self,
        arena: &mut CommandArena,
        root: NodeAddress,
    ) -> Result<NodeAddress, ScheduleRefusal>
    {
        let mut stack = Vec::from([Step::Enter(root)]);
        while let Some(step) = stack.pop() {
            match step {
                Step::Enter(node) => {
                    if self.done.contains_key(&node) {
                        continue;
                    }
                    stack.push(Step::Exit(node));
                    let work = stack.len();
                    children(arena, node, |child, _opens| {
                        stack.push(Step::Enter(child));
                        Ok(())
                    })?;
                    if let Some(pushed) = stack.get_mut(work ..) {
                        pushed.reverse();
                    }
                },
                Step::Exit(node) => {
                    if self.done.contains_key(&node) {
                        continue;
                    }
                    let mut images = Vec::new();
                    children(arena, node, |child, _opens| {
                        images.push(
                            *self
                                .done
                                .get(&child)
                                .ok_or(ClosureRefusal::Dangling(child))?,
                        );
                        Ok(())
                    })?;
                    let rebuilt = rebuild(arena, node, images, |_space, index| Ok(index))?;
                    let image = self.spawned(arena, node, rebuilt)?;
                    self.done.insert(node, image);
                },
            }
        }
        Ok(self
            .done
            .get(&root)
            .copied()
            .ok_or(ClosureRefusal::Dangling(root))?)
    }

    /// `rebuilt`, the image of `node`, spawned when `node` is a marked cut of
    /// a `μ` against a value binder whose read the renaming takes.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`spawn_independent`].
    fn spawned(
        &self,
        arena: &mut CommandArena,
        node: NodeAddress,
        rebuilt: NodeAddress,
    ) -> Result<NodeAddress, ScheduleRefusal>
    {
        let (NodeAddress::Command(node), NodeAddress::Command(cut)) = (node, rebuilt)
        else {
            return Ok(rebuilt);
        };
        let Some(&CommandNode::Cut {
            consumer: binder, ..
        }) = arena.command(node)
        else {
            return Ok(rebuilt);
        };
        if arena.independence(binder) != Independence::Independent {
            return Ok(rebuilt);
        }
        let Some(&CommandNode::Cut {
            producer, consumer, ..
        }) = arena.command(cut)
        else {
            return Err(ClosureRefusal::Dangling(rebuilt).into());
        };
        let (
            Some(&ProducerNode::Mu { body: writer }),
            Some(&ConsumerNode::MuTilde { body: reader }),
        ) = (arena.producer(producer), arena.consumer(consumer))
        else {
            return Ok(rebuilt);
        };
        let mark = arena.watermark();
        match self.read(arena, reader) {
            Ok(reader) => {
                let thunk = arena.mint_producer(ProducerNode::Thunk { body: writer })?;
                let handle = arena.mint_consumer(ConsumerNode::MuTilde { body: reader })?;
                let spawn =
                    arena.mint_command(self.perform(OperationName::from(SPAWN), thunk, handle))?;
                Ok(NodeAddress::Command(spawn))
            },
            Err(ClosureRefusal::Annotation(_)) => {
                arena.truncate_to(mark);
                Ok(rebuilt)
            },
            Err(refusal) => Err(refusal.into()),
        }
    }

    /// `reader`, which binds the handle where the cut bound its value, with a
    /// read of the handle placed where the value is first needed.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`rename`], and a node the arena does not hold.
    fn read(
        &self,
        arena: &mut CommandArena,
        reader: CommandId,
    ) -> Result<CommandId, ClosureRefusal>
    {
        let mut spine = Vec::new();
        let mut at = reader;
        while let Some(next) = past(arena, at, BinderDepth::from(spine.len()))? {
            spine.push(at);
            at = next;
        }
        let depth = spine.len();
        let NodeAddress::Command(moved) =
            rename(arena, NodeAddress::Command(at), Renaming::Capture {
                bound: 0,
                captured: depth,
            })?
        else {
            return Err(ClosureRefusal::Dangling(NodeAddress::Command(at)));
        };
        let handle = arena.mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: counted(BinderDepth::from(depth))?,
        })?;
        let bound = arena.mint_consumer(ConsumerNode::MuTilde { body: moved })?;
        let mut image =
            arena.mint_command(self.perform(OperationName::from(READ), handle, bound))?;
        for &outer in spine.iter().rev() {
            image = rebound(arena, outer, image)?;
        }
        Ok(image)
    }

    /// A perform of `operation` of the cell, sending `payload` and continuing
    /// to `continuation`.
    ///
    /// # Specification
    /// trivial.
    fn perform(
        &self,
        operation: OperationName,
        payload: ProducerId,
        continuation: crate::il::ConsumerId,
    ) -> CommandNode
    {
        CommandNode::Perform {
            signature: self.cell.clone(),
            operation,
            route: Route::Nearest,
            payload,
            continuation,
        }
    }
}

/// The body of the value binder that `at` continues to, when the read may
/// stand past `at`: `at` is a cut or a perform into a value binder, and what
/// it sends and how it routes do not name the variable `depth` binders out.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ClosureRefusal::Dangling`] for a node the arena does not hold;
/// [`ClosureRefusal::Overflow`] past the `u32` index space.
fn past(
    arena: &CommandArena,
    at: CommandId,
    depth: BinderDepth,
) -> Result<Option<CommandId>, ClosureRefusal>
{
    let dangling = ClosureRefusal::Dangling(NodeAddress::Command(at));
    let (sent, routed, continuation) = match *arena.command(at).ok_or(dangling)? {
        CommandNode::Cut {
            producer, consumer, ..
        } => (producer, None, consumer),
        CommandNode::Perform {
            payload,
            route,
            continuation,
            ..
        } => {
            let routed = match route {
                Route::Capability(capability) => Some(capability),
                Route::Nearest => None,
            };
            (payload, routed, continuation)
        },
        CommandNode::Handle { .. }
        | CommandNode::Resume { .. }
        | CommandNode::Abandon { .. }
        | CommandNode::Reset { .. }
        | CommandNode::Shift { .. }
        | CommandNode::Memory { .. }
        | CommandNode::World { .. }
        | CommandNode::Session { .. } => return Ok(None),
    };
    let Some(&ConsumerNode::MuTilde { body }) = arena.consumer(continuation)
    else {
        return Ok(None);
    };
    let index = counted(depth)?;
    for producer in core::iter::once(sent).chain(routed) {
        let node = NodeAddress::Producer(producer);
        let scope = arena
            .node_scope(node)
            .ok_or(ClosureRefusal::Dangling(node))?;
        if scope
            .producers()
            .indices(Zone::Intuitionistic)
            .any(|named| named == index)
        {
            return Ok(None);
        }
    }
    Ok(Some(body))
}

/// `outer`, a cut or a perform into a value binder, rebuilt with `body` as
/// that binder's body.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`ClosureRefusal::Dangling`] for a node the arena does not hold or one of
/// another form; a refused mint.
fn rebound(
    arena: &mut CommandArena,
    outer: CommandId,
    body: CommandId,
) -> Result<CommandId, ClosureRefusal>
{
    let dangling = ClosureRefusal::Dangling(NodeAddress::Command(outer));
    let binder = arena.mint_consumer(ConsumerNode::MuTilde { body })?;
    let node = match *arena.command(outer).ok_or(dangling)? {
        CommandNode::Cut {
            polarity, producer, ..
        } => CommandNode::Cut {
            polarity,
            producer,
            consumer: binder,
        },
        CommandNode::Perform {
            ref signature,
            ref operation,
            route,
            payload,
            ..
        } => CommandNode::Perform {
            signature: signature.clone(),
            operation: operation.clone(),
            route,
            payload,
            continuation: binder,
        },
        CommandNode::Handle { .. }
        | CommandNode::Resume { .. }
        | CommandNode::Abandon { .. }
        | CommandNode::Reset { .. }
        | CommandNode::Shift { .. }
        | CommandNode::Memory { .. }
        | CommandNode::World { .. }
        | CommandNode::Session { .. } => return Err(dangling),
    };
    Ok(arena.mint_command(node)?)
}

#[cfg(test)]
mod tests;
