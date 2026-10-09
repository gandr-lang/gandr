//! The duplication walk: an overlay root rebuilt under a duplication policy.
//!
//! # Three treatments, one per share
//!
//! [`duplicate_value`] and [`duplicate_computation`] validate a root, then
//! rebuild everything it reaches into fresh nodes appended to the same overlay,
//! asking [`DuplicationPolicy::copies`], share by share, what to do with each
//! part of the leg:
//!
//! - A leg that is no abstraction is one rib. Copied, the share is **inlined**:
//!   its leg walked afresh at each occurrence, the share itself gone. Shared,
//!   the share is **kept**: its leg rebuilt once and every occurrence pointing
//!   at it.
//! - A leg that is an abstraction — a lambda, or a thunk over one — has a
//!   **spine**, the paths from its binder down to the binder's occurrences, and
//!   **ribs**, the maximal subterms of its body that do not read the binder.
//!   Both parts copied, the share is inlined; the spine shared, it is kept; the
//!   spine copied and the ribs shared, it is **distributed**: each rib becomes
//!   the leg of a new share standing where the abstraction's share stood, and
//!   each occurrence of the abstraction becomes a copy of its spine whose ribs
//!   are occurrences of those shares.
//!
//! The output validates and erases to the tree the input erases to; the input
//! is left untouched, and a refusal truncates the overlay back to its entry
//! watermark.
//!
//! # What makes a subterm a rib
//!
//! Erasure reads a leg's indices where each occurrence stands, so a subterm
//! moved into a share's leg and read back at its own position reads what it
//! read before. A subterm of the abstraction's body is therefore a rib when its
//! expansion does not read the binder — the binder's index, counted from where
//! the subterm stands, is not among the subterm's free indices, an occurrence
//! of an outer share reading its leg's and an opaque node its core term's — and
//! when no occurrence inside it names a share opened inside the abstraction's
//! leg, whose frame would not enclose the rib's new share. It is maximal when
//! its parent is not a rib.
//!
//! Ribs are sought through the body and the bodies of the shares nested in it.
//! A nested share's leg is read where its occurrences stand rather than where
//! it is written, so the binder's index there is no single number, and the leg
//! travels with the spine. New rib shares are not distributed again in the
//! same walk.
//!
//! # Frames, distributors and covers live on the walk's stack
//!
//! The walk is one loop over a heap task stack, with an output frame per share
//! it is rebuilding the body of, and the input scope a persistent list of
//! bindings in an arena of its own, so a leg is walked in the scope it stands
//! in however deep its occurrence lies. A distribution's cursor — the frame of
//! its first rib share, and the ribs found or met — is the distributor the
//! stance's calculus would mint as a node, and a share inside a leg the dry
//! pass reads is covered in scope rather than rebuilt; neither is ever minted.
//!
//! # The copying stance is priced before it runs
//!
//! When the policy copies every rib, the output is the root's whole expansion,
//! so the walk measures the root first and refuses an expansion past the ids an
//! overlay family holds before minting anything. A sharing stance mints at most
//! the expansion and two nodes per rib, and a family that runs out of ids
//! refuses at the mint.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;

use crate::free::CoreTerm;
use crate::free::FreeFault;
use crate::free::FreeIndices;
use crate::free::Lowering;
use crate::free::Membership;
use crate::free::Outward;
use crate::measure::ExpansionSize;
use crate::measure::MeasureFault;
use crate::measure::SharingMeasure;
use crate::overlay::Bound;
use crate::overlay::CompGraft;
use crate::overlay::CompNode;
use crate::overlay::CoreId;
use crate::overlay::Overlay;
use crate::overlay::OverlayCompId;
use crate::overlay::OverlayFault;
use crate::overlay::OverlayId;
use crate::overlay::OverlayRefusal;
use crate::overlay::OverlayValueId;
use crate::overlay::Shape;
use crate::overlay::ShareArity;
use crate::overlay::ShareDistance;
use crate::overlay::SharePosition;
use crate::overlay::Sharing;
use crate::overlay::ValueGraft;
use crate::overlay::ValueNode;
use crate::policy::Copied;
use crate::policy::DuplicationPolicy;
use crate::policy::SharedPart;

/// Why a root could not be duplicated. A refused duplication leaves the overlay
/// as it found it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DuplicationFault
{
    /// Validation refused the overlay, in its own vocabulary, before anything
    /// was minted.
    Refused(OverlayRefusal),
    /// The measure the copying stance is priced by refused, in its own
    /// vocabulary: the root's expansion passes a 64-bit counter.
    Measure(MeasureFault),
    /// The copying stance would mint the root's whole expansion, and it passes
    /// the ids an overlay family holds.
    ExpansionPastIds
    {
        /// The expansion the stance would mint.
        expansion: ExpansionSize,
    },
    /// A mint was refused, in the overlay's own vocabulary: a family ran out
    /// of ids.
    Mint(OverlayFault),
    /// An opaque node names no node of the core arena its free indices are
    /// read in.
    UnresolvedOpaque
    {
        /// The opaque node.
        node: OverlayId,
    },
    /// The root reaches a quote grafted with its type: a type inside a term,
    /// which the stance's calculus has no rule to distribute. A producer
    /// carries a quote as an opaque node instead, read whole wherever it
    /// stands.
    Quote
    {
        /// The quote's node.
        node: OverlayId,
    },
    /// The walk's own stacks disagreed with the validated overlay. Unreachable
    /// while every frame is opened beneath the body that reads it and every
    /// graft is rebuilt over the children its own tasks left; kept so the walk
    /// fails closed rather than answering.
    MachineInvariant,
}

/// Duplicate a value overlay root under `policy`.
///
/// # Specification
/// - requires: `core` is the arena the overlay's opaque nodes name.
/// - ensures: on success a fresh root, appended to `overlay` together with
///   every node it reaches, that validates and erases to a term equal as a tree
///   to the one `root` erases to; `root` and the nodes it reaches are
///   untouched. Each share is treated as its leg and the policy decide: a leg
///   that is no abstraction is inlined when the policy copies ribs and kept
///   otherwise; an abstraction is inlined when the policy copies both parts,
///   kept when it shares the spine, and distributed when it copies the spine
///   and shares the ribs. On refusal the overlay is at its entry watermark.
/// - provides: the duplication entry the policy parameter enters through, for
///   the value family. The clause states that the result validates; its
///   erasure's equality with the input's is a relation between two erasures,
///   and the witnesses below carry it.
/// - fails: [`DuplicationFault::Refused`] before anything is minted when the
///   root does not validate; [`DuplicationFault::Measure`] and
///   [`DuplicationFault::ExpansionPastIds`], before anything is minted, when
///   the policy copies every rib and the root's expansion passes the counter or
///   the ids a family holds; [`DuplicationFault::Mint`] when a family runs out
///   of ids; [`DuplicationFault::UnresolvedOpaque`] for an opaque node the core
///   arena does not hold; [`DuplicationFault::MachineInvariant`] when the
///   walk's own stacks break.
/// - panics: none.
/// - intension: validation, the measure when the policy copies every rib, a
///   post-order survey of free indices and outward distances when it
///   distributes, then one heap walk that enters each node once per copy the
///   treatment asks for.
///
/// # Errors
/// - [`DuplicationFault::Refused`] — the overlay does not validate.
/// - [`DuplicationFault::Measure`] — the expansion passes its counter.
/// - [`DuplicationFault::ExpansionPastIds`] — the expansion passes the ids.
/// - [`DuplicationFault::Mint`] — a family ran out of ids.
/// - [`DuplicationFault::UnresolvedOpaque`] — an opaque node does not resolve.
/// - [`DuplicationFault::MachineInvariant`] — the walk's own stacks broke.
///
/// # Adequacy
/// - hypothesis: L1 for the erasure — over generated overlays of both families
///   holding shared abstractions, nested shares, occurrences of outer shares
///   inside legs and opaque nodes reading indices, the output's erasure and the
///   input's are compared as trees by a test-local walk under both stances, the
///   oracle sharing nothing with the walk. L3 for the treatments and the gates
///   — the copying stance's output measured as the expansion, the sharing
///   stance keeping a leaf leg and distributing an abstraction into its ribs
///   with node counts asserted, a refusal by validation and by the id space
///   each leaving the overlay at its watermark, and the teardown chain
///   duplicated inside a small stack.
/// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
/// - witness: `duplication::duplication::a_copying_duplicate_is_the_expansion`
/// - witness:
///   `duplication::duplication::a_spinal_duplicate_keeps_a_leg_that_is_no_abstraction`
/// - witness:
///   `duplication::duplication::a_spinal_duplicate_distributes_an_abstraction_over_its_ribs`
/// - witness:
///   `duplication::duplication::a_refused_duplication_leaves_the_overlay_as_it_found_it`
/// - witness:
///   `teardown::teardown::a_spinal_deep_overlay_duplicates_and_tears_down_inside_a_small_stack`
#[inline]
#[spec(ensures: |ret| ret
    .as_ref()
    .map_or(true, |rebuilt| overlay.validate(OverlayId::Value(*rebuilt)).is_ok()))]
pub fn duplicate_value(
    overlay: &mut Overlay,
    core: &CoreArena,
    policy: DuplicationPolicy,
    root: OverlayValueId,
) -> Result<OverlayValueId, DuplicationFault>
{
    let rebuilt = duplicate(overlay, core, policy, OverlayId::Value(root))?;
    match rebuilt {
        | OverlayId::Value(id) => Ok(id),
        | OverlayId::Computation(_) | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
            Err(DuplicationFault::MachineInvariant)
        },
    }
}

/// Duplicate a computation overlay root under `policy`.
///
/// # Specification
/// - requires: `core` is the arena the overlay's opaque nodes name.
/// - ensures: as [`duplicate_value`], for a computation root.
/// - provides: the computation half of the duplication entry.
/// - fails: as [`duplicate_value`] fails.
/// - panics: none.
///
/// # Errors
/// As [`duplicate_value`].
///
/// # Adequacy
/// - hypothesis: L1 for the erasure, over the generated computation roots of
///   the property; L3 for the distribution of a shared abstraction applied
///   twice, read off the evaluator's step count.
/// - witness: `duplication::duplication::spinal_duplication_is_invisible_to_erasure`
/// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
#[inline]
#[spec(ensures: |ret| ret
    .as_ref()
    .map_or(true, |rebuilt| overlay.validate(OverlayId::Computation(*rebuilt)).is_ok()))]
pub fn duplicate_computation(
    overlay: &mut Overlay,
    core: &CoreArena,
    policy: DuplicationPolicy,
    root: OverlayCompId,
) -> Result<OverlayCompId, DuplicationFault>
{
    let rebuilt = duplicate(overlay, core, policy, OverlayId::Computation(root))?;
    match rebuilt {
        | OverlayId::Computation(id) => Ok(id),
        | OverlayId::Value(_) | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
            Err(DuplicationFault::MachineInvariant)
        },
    }
}

/// Validate, price, survey, then walk, restoring the overlay on refusal.
///
/// # Specification
/// - requires: `core` is the arena the overlay's opaque nodes name.
/// - ensures: as [`duplicate_value`], for a root of either evaluation family.
/// - provides: the one gate both typed entries share.
/// - fails: as [`duplicate_value`] fails.
/// - panics: none.
///
/// # Errors
/// As [`duplicate_value`].
pub fn duplicate(
    overlay: &mut Overlay,
    core: &CoreArena,
    policy: DuplicationPolicy,
    root: OverlayId,
) -> Result<OverlayId, DuplicationFault>
{
    overlay.validate(root).map_err(DuplicationFault::Refused)?;
    if policy.copies(SharedPart::Rib) == Copied::Copied {
        let measured = SharingMeasure::of(overlay, root).map_err(DuplicationFault::Measure)?;
        let expansion = measured.expansion();
        if u64::from(expansion) > u64::from(u32::MAX) {
            return Err(DuplicationFault::ExpansionPastIds { expansion });
        }
    }
    let reached = match (
        policy.copies(SharedPart::Spine),
        policy.copies(SharedPart::Rib),
    ) {
        | (Copied::Copied, Copied::Shared) => survey(overlay, core, root)?,
        | (Copied::Copied | Copied::Shared, Copied::Copied) | (Copied::Shared, Copied::Shared) => {
            BTreeMap::new()
        },
    };
    let mark = overlay.watermark();
    let mut walk = Walk {
        overlay,
        policy,
        reached,
        tasks: Vec::new(),
        results: Vec::new(),
        frames: Vec::new(),
        scopes: Vec::from([ScopeCell {
            binding: Binding::Empty,
            parent: ScopeId::EMPTY,
        }]),
        cursors: Vec::new(),
    };
    let outcome = walk.run(root);
    if outcome.is_err() {
        walk.overlay.truncate_to(mark);
    }
    outcome
}

/// What the survey knows of one input node: the intuitionistic indices its
/// expansion reads and the share distances its occurrences reach past it, each
/// counted from where the node stands.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Reach
{
    /// The free intuitionistic indices of the node's expansion.
    reads: Outward<DeBruijnIndex>,
    /// The distances, past the node, of the shares its occurrences name.
    escapes: Outward<ShareDistance>,
}

/// One child of a graft, with the binders it stands under.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Child
{
    /// The child.
    node: OverlayId,
    /// The intuitionistic binders between the graft and the child.
    binders: Lowering,
}

/// A graft's children, left to right, the absent ones last.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Under
{
    /// Up to three children.
    listed: [Option<Child>; 3],
}

impl Under
{
    /// The children of the graft `node`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each child the graft names, left to right as the core former
    ///   orders them: a lambda's body, a bind's continuation and a case's
    ///   branches under one binder, every other child under none.
    /// - provides: the one reading of the formers' binding the survey and the
    ///   walk share.
    /// - fails: [`DuplicationFault::MachineInvariant`] when `node` is no value
    ///   or computation graft, which no walk from a validated evaluation root
    ///   reaches.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — `node` is no evaluation
    ///   graft.
    fn of(
        overlay: &Overlay,
        node: OverlayId,
    ) -> Result<Self, DuplicationFault>
    {
        let child = |node: OverlayId, binders: Lowering| Some(Child { node, binders });
        let listed = match node {
            | OverlayId::Value(id) => {
                let Some(held) = overlay.value(id)
                else {
                    return Err(DuplicationFault::MachineInvariant);
                };
                let ValueNode::Grafted(ref graft) = *held
                else {
                    return Err(DuplicationFault::MachineInvariant);
                };
                match *graft {
                    | ValueGraft::Variable { .. }
                    | ValueGraft::Constant(_)
                    | ValueGraft::Unit
                    | ValueGraft::Literal(_) => [None; 3],
                    | ValueGraft::Pair(first, second) => [
                        child(OverlayId::Value(first), Lowering::NONE),
                        child(OverlayId::Value(second), Lowering::NONE),
                        None,
                    ],
                    | ValueGraft::Injection(_, body) | ValueGraft::Lift { body, .. } => {
                        [child(OverlayId::Value(body), Lowering::NONE), None, None]
                    },
                    | ValueGraft::Thunk(body) => [
                        child(OverlayId::Computation(body), Lowering::NONE),
                        None,
                        None,
                    ],
                    | ValueGraft::Quote(_) | ValueGraft::QuoteComputation(_) => {
                        return Err(DuplicationFault::Quote { node });
                    },
                }
            },
            | OverlayId::Computation(id) => {
                let Some(&CompNode::Grafted(graft)) = overlay.computation(id)
                else {
                    return Err(DuplicationFault::MachineInvariant);
                };
                match graft {
                    | CompGraft::Lambda(body) => [
                        child(OverlayId::Computation(body), Lowering::ONE),
                        None,
                        None,
                    ],
                    | CompGraft::Application(head, argument) => [
                        child(OverlayId::Computation(head), Lowering::NONE),
                        child(OverlayId::Value(argument), Lowering::NONE),
                        None,
                    ],
                    | CompGraft::Return(value) | CompGraft::Force(value) => {
                        [child(OverlayId::Value(value), Lowering::NONE), None, None]
                    },
                    | CompGraft::Bind(bound, body) => [
                        child(OverlayId::Computation(bound), Lowering::NONE),
                        child(OverlayId::Computation(body), Lowering::ONE),
                        None,
                    ],
                    | CompGraft::Case {
                        scrutinee,
                        on_left,
                        on_right,
                    } => [
                        child(OverlayId::Value(scrutinee), Lowering::NONE),
                        child(OverlayId::Computation(on_left), Lowering::ONE),
                        child(OverlayId::Computation(on_right), Lowering::ONE),
                    ],
                }
            },
            | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                return Err(DuplicationFault::MachineInvariant);
            },
        };
        Ok(Self { listed })
    }
}

/// One pending step of the survey.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Survey
{
    /// Survey one node, or queue what surveying it takes.
    Enter(OverlayId),
    /// Bring a share's leg into scope, before its body.
    Bind(OverlayId),
    /// Survey a share from its leg and its body, and take its leg out of
    /// scope.
    Unbind(OverlayId),
    /// Survey a graft from its children.
    Assemble(OverlayId),
}

/// The leg the innermost share named by `distance` binds.
///
/// # Specification
/// - requires: `legs` holds the legs of the shares whose bodies enclose the
///   occurrence, innermost last.
/// - ensures: the leg `distance` shares out.
/// - provides: the survey's occurrence lookup.
/// - fails: [`DuplicationFault::MachineInvariant`] when no leg in scope
///   answers, which validation excludes.
/// - panics: none.
///
/// # Errors
/// - [`DuplicationFault::MachineInvariant`] — no leg in scope answers.
fn innermost(
    legs: &[OverlayId],
    distance: ShareDistance,
) -> Result<OverlayId, DuplicationFault>
{
    let Ok(distance) = usize::try_from(u32::from(distance))
    else {
        return Err(DuplicationFault::MachineInvariant);
    };
    legs.len()
        .checked_sub(1)
        .and_then(|last| last.checked_sub(distance))
        .and_then(|named| legs.get(named))
        .copied()
        .ok_or(DuplicationFault::MachineInvariant)
}

/// Survey the overlay reachable from `root`: what each node reads and how far
/// its occurrences reach.
///
/// # Specification
/// - requires: the overlay validates from `root`, and `core` is the arena its
///   opaque nodes name.
/// - ensures: one reach per reachable node: an opaque node reads its core
///   term's free intuitionistic indices; an intuitionistic variable reads its
///   own index; an occurrence reads its leg's and reaches its own distance; a
///   graft reads its children's, each lowered by the binders it stands under,
///   and reaches theirs; a share reads its body's and reaches its leg's and its
///   body's one frame lower.
/// - provides: the facts the walk's rib test reads.
/// - fails: [`DuplicationFault::UnresolvedOpaque`] for an opaque node the core
///   arena does not hold, [`DuplicationFault::MachineInvariant`] when the
///   survey's own order breaks.
/// - panics: none.
/// - intension: one post-order walk on a heap stack, entering each node once.
///   `economy: one owned reach per node; keep only the reaches of nodes inside
///   abstraction legs when a workload's memory meets it`.
///
/// # Errors
/// - [`DuplicationFault::UnresolvedOpaque`] — an opaque node does not resolve.
/// - [`DuplicationFault::MachineInvariant`] — the survey's order broke.
fn survey(
    overlay: &Overlay,
    core: &CoreArena,
    root: OverlayId,
) -> Result<BTreeMap<OverlayId, Reach>, DuplicationFault>
{
    let mut free = FreeIndices::default();
    let mut reached: BTreeMap<OverlayId, Reach> = BTreeMap::new();
    let mut legs: Vec<OverlayId> = Vec::new();
    let mut tasks = Vec::from([Survey::Enter(root)]);
    while let Some(task) = tasks.pop() {
        match task {
            | Survey::Enter(node) => {
                let shape = overlay.shape(node).map_err(DuplicationFault::Refused)?;
                match shape {
                    | Shape::Opaque(held) => {
                        let term = match held {
                            | CoreId::Value(id) => CoreTerm::Value(id),
                            | CoreId::Computation(id) => CoreTerm::Computation(id),
                            | CoreId::ValueType(_) | CoreId::CompType(_) => {
                                return Err(DuplicationFault::MachineInvariant);
                            },
                        };
                        let answered = free.of(core, term).map_err(|fault| match fault {
                            | FreeFault::Dangling => DuplicationFault::UnresolvedOpaque { node },
                            | FreeFault::MachineInvariant => DuplicationFault::MachineInvariant,
                        })?;
                        let reads = answered.intuitionistic().clone();
                        reached.insert(node, Reach {
                            reads,
                            escapes: Outward::default(),
                        });
                    },
                    | Shape::Bound(bound) => {
                        let leg = innermost(&legs, bound.distance)?;
                        let Some(read) = reached.get(&leg)
                        else {
                            return Err(DuplicationFault::MachineInvariant);
                        };
                        let reads = read.reads.clone();
                        reached.insert(node, Reach {
                            reads,
                            escapes: Outward::single(bound.distance),
                        });
                    },
                    | Shape::Shared(sharing) => {
                        tasks.push(Survey::Unbind(node));
                        tasks.push(Survey::Enter(sharing.body));
                        tasks.push(Survey::Bind(sharing.leg));
                        tasks.push(Survey::Enter(sharing.leg));
                    },
                    | Shape::Grafted(_) => {
                        let under = Under::of(overlay, node)?;
                        tasks.push(Survey::Assemble(node));
                        for child in under.listed.into_iter().rev().flatten() {
                            tasks.push(Survey::Enter(child.node));
                        }
                    },
                }
            },
            | Survey::Bind(leg) => legs.push(leg),
            | Survey::Unbind(share) => {
                if legs.pop().is_none() {
                    return Err(DuplicationFault::MachineInvariant);
                }
                let shape = overlay.shape(share).map_err(DuplicationFault::Refused)?;
                let Shape::Shared(sharing) = shape
                else {
                    return Err(DuplicationFault::MachineInvariant);
                };
                let (Some(leg), Some(body)) =
                    (reached.get(&sharing.leg), reached.get(&sharing.body))
                else {
                    return Err(DuplicationFault::MachineInvariant);
                };
                let mut escapes = leg.escapes.clone();
                escapes.join_lowered(&body.escapes, Lowering::ONE);
                let reads = body.reads.clone();
                reached.insert(share, Reach { reads, escapes });
            },
            | Survey::Assemble(node) => {
                let under = Under::of(overlay, node)?;
                let mut reach = Reach::default();
                if let OverlayId::Value(id) = node
                    && let Some(&ValueNode::Grafted(ValueGraft::Variable {
                        zone: Zone::Intuitionistic,
                        index,
                    })) = overlay.value(id)
                {
                    reach.reads = Outward::single(index);
                }
                for child in under.listed.into_iter().flatten() {
                    let Some(below) = reached.get(&child.node)
                    else {
                        return Err(DuplicationFault::MachineInvariant);
                    };
                    reach.reads.join_lowered(&below.reads, child.binders);
                    reach.escapes.join_lowered(&below.escapes, Lowering::NONE);
                }
                reached.insert(node, reach);
            },
        }
    }
    Ok(reached)
}

/// What the walk does with one share.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Treatment
{
    /// Walk the leg afresh at each occurrence; the share is gone.
    Inline,
    /// Rebuild the leg once and point every occurrence at it.
    Keep,
    /// Share each rib of the abstraction and copy its spine at each
    /// occurrence.
    Distribute,
}

/// Whether a leg is an abstraction, whose parts the policy is asked about
/// apart.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LegShape
{
    /// No abstraction: the whole leg is one rib.
    Whole,
    /// A lambda, or a thunk over one.
    Abstraction,
}

/// The shape of the leg `leg`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`LegShape::Abstraction`] exactly when `leg` is a grafted lambda
///   or a grafted thunk over a grafted lambda.
/// - provides: the classification the treatment is read from.
/// - fails: never.
/// - panics: none.
fn leg_shape(
    overlay: &Overlay,
    leg: OverlayId,
) -> LegShape
{
    let lambda = match leg {
        | OverlayId::Value(id) => match overlay.value(id) {
            | Some(&ValueNode::Grafted(ValueGraft::Thunk(body))) => Some(body),
            | Some(_) | None => None,
        },
        | OverlayId::Computation(id) => Some(id),
        | OverlayId::ValueType(_) | OverlayId::CompType(_) => None,
    };
    match lambda.and_then(|id| overlay.computation(id)) {
        | Some(&CompNode::Grafted(CompGraft::Lambda(_))) => LegShape::Abstraction,
        | Some(_) | None => LegShape::Whole,
    }
}

/// What `policy` does with a share whose leg has `shape`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a whole leg is inlined when ribs are copied and kept when they
///   are shared; an abstraction is inlined when both parts are copied, kept
///   when the spine is shared, and distributed when the spine is copied and the
///   ribs shared.
/// - provides: the one place the policy's per-part answers become a treatment.
/// - fails: never.
/// - panics: none.
fn treatment(
    policy: DuplicationPolicy,
    shape: LegShape,
) -> Treatment
{
    match (
        shape,
        policy.copies(SharedPart::Spine),
        policy.copies(SharedPart::Rib),
    ) {
        | (LegShape::Whole, _, Copied::Copied)
        | (LegShape::Abstraction, Copied::Copied, Copied::Copied) => Treatment::Inline,
        | (LegShape::Whole, _, Copied::Shared) | (LegShape::Abstraction, Copied::Shared, _) => {
            Treatment::Keep
        },
        | (LegShape::Abstraction, Copied::Copied, Copied::Shared) => Treatment::Distribute,
    }
}

/// The index of one output frame: a share whose body the walk is rebuilding.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct FrameIndex(usize);

/// The index of one cell of the input scope arena.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ScopeId(usize);

impl ScopeId
{
    /// The empty scope, every scope's root.
    const EMPTY: Self = Self(0_usize);
}

/// The index of one distribution's cursor.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct CursorId(usize);

/// How many occurrences of one output share the walk has minted.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Taken(u32);

/// How many ribs a distribution has found, or a spine copy met.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct RibCount(u32);

/// How many intuitionistic binders stand between an abstraction's body and a
/// node inside it: the binder's index, counted from the node.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct BinderDepth(u32);

/// How many shares opened inside an abstraction's leg enclose a node inside
/// it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct InnerFrames(u32);

/// Where a node stands inside the abstraction whose ribs are sought.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct RibSite
{
    /// The binders between the abstraction's body and the node.
    depth: BinderDepth,
    /// The shares opened inside the leg whose bodies enclose the node.
    inner: InnerFrames,
}

impl RibSite
{
    /// The site `binders` binders further in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the depth raised by `binders`, the frames unchanged.
    /// - provides: the step from a graft to a child under its binders.
    /// - fails: [`DuplicationFault::MachineInvariant`] past the counter, which
    ///   needs more binders than an overlay holds nodes.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — the depth passed its counter.
    fn under(
        self,
        binders: Lowering,
    ) -> Result<Self, DuplicationFault>
    {
        let Some(depth) = self.depth.0.checked_add(u32::from(binders))
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        Ok(Self {
            depth: BinderDepth(depth),
            inner: self.inner,
        })
    }

    /// The site inside one more share's body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the frames raised by one, the depth unchanged.
    /// - provides: the step from a share to its body.
    /// - fails: [`DuplicationFault::MachineInvariant`] past the counter, which
    ///   needs more shares than an overlay holds nodes.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — the frames passed their
    ///   counter.
    fn within(self) -> Result<Self, DuplicationFault>
    {
        let Some(inner) = self.inner.0.checked_add(1_u32)
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        Ok(Self {
            depth: self.depth,
            inner: InnerFrames(inner),
        })
    }
}

/// How the walk reads the node it enters.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mode
{
    /// Rebuild the node and everything beneath it.
    Plain,
    /// Rebuild the thunk and the lambda above a distributed leg's body.
    Prefix
    {
        /// The spine copy under way.
        cursor: CursorId,
    },
    /// Rebuild a distributed leg's body, each rib an occurrence of its share.
    Spine
    {
        /// The spine copy under way.
        cursor: CursorId,
        /// Where the node stands inside the abstraction.
        at: RibSite,
    },
    /// Walk the thunk and the lambda above a distributed leg's body, rebuilding
    /// nothing.
    DryPrefix
    {
        /// The distribution under way.
        cursor: CursorId,
    },
    /// Find a distributed leg's ribs, rebuilding each as the leg of a new share
    /// and nothing else.
    Dry
    {
        /// The distribution under way.
        cursor: CursorId,
        /// Where the node stands inside the abstraction.
        at: RibSite,
    },
}

/// What an input share's occurrences resolve to, in the scope of its body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binding
{
    /// The root of every scope: no share.
    Empty,
    /// A kept share: its occurrences point at the output frame.
    Kept
    {
        /// The output frame of the rebuilt share.
        frame: FrameIndex,
    },
    /// An inlined share: each occurrence walks the leg afresh in the scope
    /// the leg stands in.
    Inlined
    {
        /// The leg.
        leg: OverlayId,
        /// The scope the leg stands in.
        scope: ScopeId,
    },
    /// A distributed share: each occurrence rebuilds the leg's spine, its
    /// ribs pointing at the output frames from `ribs` on.
    Distributed
    {
        /// The leg.
        leg: OverlayId,
        /// The scope the leg stands in.
        scope: ScopeId,
        /// The output frame of the first rib share.
        ribs: FrameIndex,
    },
    /// A share inside a leg the dry pass reads: covered, never resolved,
    /// because no rib names it.
    Covered,
}

/// One cell of the persistent input scope.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ScopeCell
{
    /// The innermost share's binding.
    binding: Binding,
    /// The scope around it.
    parent: ScopeId,
}

/// One distribution's place in the output: the frame of its first rib share,
/// and the ribs the dry pass has found or a spine copy has met.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Cursor
{
    /// The output frame of the first rib share.
    ribs: FrameIndex,
    /// The ribs found or met so far.
    met: RibCount,
}

/// One pending step of the walk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Task
{
    /// Rebuild, copy or survey one input node, as its mode says.
    Enter
    {
        /// The input node.
        node: OverlayId,
        /// The input scope it stands in.
        scope: ScopeId,
        /// How it is read.
        mode: Mode,
    },
    /// Rebuild a graft over the children its own tasks left.
    Assemble(OverlayId),
    /// Open a kept share's frame over its rebuilt leg, and walk its body.
    Open
    {
        /// The input share.
        share: OverlayId,
        /// The input scope the share stands in.
        scope: ScopeId,
        /// How its body is read.
        mode: Mode,
    },
    /// Mint a kept share over its rebuilt leg and body, and close its frame.
    Close,
    /// Open a rib share's frame over its rebuilt leg.
    OpenRib(CursorId),
    /// Bind a distributed share once its ribs are found, and walk its body.
    Distribute
    {
        /// The input share.
        share: OverlayId,
        /// The input scope the share stands in.
        scope: ScopeId,
        /// How its body is read.
        mode: Mode,
        /// The distribution's cursor.
        cursor: CursorId,
    },
    /// Mint a distribution's rib shares around its rebuilt body, innermost
    /// first, and close their frames.
    CloseRibs(CursorId),
}

/// The walk: the overlay it rebuilds in, the policy, the survey, its task and
/// result stacks, the output frames open, the input scope arena and the
/// distributions' cursors.
struct Walk<'run>
{
    /// The overlay read and appended to.
    overlay: &'run mut Overlay,
    /// The policy asked per share.
    policy: DuplicationPolicy,
    /// The survey's reach per input node; empty unless the policy distributes.
    reached: BTreeMap<OverlayId, Reach>,
    /// The pending steps.
    tasks: Vec<Task>,
    /// The rebuilt nodes awaiting their parent, and kept or rib legs awaiting
    /// their share.
    results: Vec<OverlayId>,
    /// The output shares whose bodies are being rebuilt, innermost last, each
    /// with the occurrences minted for it so far.
    frames: Vec<Taken>,
    /// The input scope arena; cell zero is the empty scope.
    scopes: Vec<ScopeCell>,
    /// One cursor per distribution and per spine copy.
    // economy: a cursor per spine copy is kept for the walk; pop it at the
    // copy's end when a workload's memory meets it.
    cursors: Vec<Cursor>,
}

impl Walk<'_>
{
    /// Drive the walk from `root` until its steps run out.
    ///
    /// # Specification
    /// - requires: the overlay validates from `root`, and the survey answers
    ///   every node a distribution reads.
    /// - ensures: the rebuilt root, with no frame open and no other result
    ///   left.
    /// - provides: the heap-only drive; depth costs steps, never host frames.
    /// - fails: every variant a step raises.
    /// - panics: none.
    ///
    /// # Errors
    /// Every variant a step raises.
    ///
    /// # Termination
    /// - reason: the `while let` below pops one task per iteration.
    /// - measure: the nodes of the expansion still to be visited, plus the
    ///   frame and assembly tasks pending.
    /// - boundedness: each task enters an input node in a copy the treatment
    ///   asks for, and the copies of a node are bounded by its occurrences in
    ///   the root's expansion.
    /// - input recursion: none.
    fn run(
        &mut self,
        root: OverlayId,
    ) -> Result<OverlayId, DuplicationFault>
    {
        self.tasks.push(Task::Enter {
            node: root,
            scope: ScopeId::EMPTY,
            mode: Mode::Plain,
        });
        while let Some(task) = self.tasks.pop() {
            self.step(task)?;
        }
        let Some(rebuilt) = self.results.pop()
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        if self.results.is_empty() && self.frames.is_empty() {
            Ok(rebuilt)
        }
        else {
            Err(DuplicationFault::MachineInvariant)
        }
    }

    /// Perform one task.
    ///
    /// # Specification
    /// - requires: `task` was popped from the walk's own stack.
    /// - ensures: the task's result is pushed, or the tasks producing it are.
    /// - provides: the walk's whole transition relation.
    /// - fails: every variant the arms raise.
    /// - panics: none.
    ///
    /// # Errors
    /// Every variant the arms raise.
    fn step(
        &mut self,
        task: Task,
    ) -> Result<(), DuplicationFault>
    {
        match task {
            | Task::Enter { node, scope, mode } => self.enter(node, scope, mode),
            | Task::Assemble(node) => {
                let rebuilt = self.assemble(node)?;
                self.results.push(rebuilt);
                Ok(())
            },
            | Task::Open { share, scope, mode } => self.open(share, scope, mode),
            | Task::Close => self.close(),
            | Task::OpenRib(cursor) => self.open_rib(cursor),
            | Task::Distribute {
                share,
                scope,
                mode,
                cursor,
            } => self.distribute(share, scope, mode, cursor),
            | Task::CloseRibs(cursor) => self.close_ribs(cursor),
        }
    }

    /// Enter one input node in `mode`.
    ///
    /// # Specification
    /// - requires: `scope` binds every share whose body encloses `node`.
    /// - ensures: inside a distributed leg's body, a rib becomes an occurrence
    ///   of its share in a spine copy and the leg of a new share in the dry
    ///   pass; every other node is rebuilt, copied or passed over by kind.
    /// - provides: the dispatch on the rib test and the node's kind.
    /// - fails: every variant the kind's arm raises.
    /// - panics: none.
    ///
    /// # Errors
    /// Every variant the kind's arm raises.
    fn enter(
        &mut self,
        node: OverlayId,
        scope: ScopeId,
        mode: Mode,
    ) -> Result<(), DuplicationFault>
    {
        match mode {
            | Mode::Spine { cursor, at } => {
                let part = self.part(node, at)?;
                if part == SharedPart::Rib {
                    return self.rib_occurrence(node, cursor);
                }
            },
            | Mode::Dry { cursor, at } => {
                let part = self.part(node, at)?;
                if part == SharedPart::Rib {
                    self.tasks.push(Task::OpenRib(cursor));
                    self.tasks.push(Task::Enter {
                        node,
                        scope,
                        mode: Mode::Plain,
                    });
                    return Ok(());
                }
            },
            | Mode::Plain | Mode::Prefix { .. } | Mode::DryPrefix { .. } => {},
        }
        let shape = self
            .overlay
            .shape(node)
            .map_err(DuplicationFault::Refused)?;
        match shape {
            | Shape::Opaque(_) => self.opaque(node, mode),
            | Shape::Bound(bound) => self.occurrence(node, bound, scope, mode),
            | Shape::Shared(sharing) => self.share(node, sharing, scope, mode),
            | Shape::Grafted(_) => self.graft(node, scope, mode),
        }
    }

    /// Whether `node`, standing at `at` inside an abstraction, is on the spine
    /// or a rib.
    ///
    /// # Specification
    /// - requires: the survey answered `node`.
    /// - ensures: [`SharedPart::Spine`] when the node's expansion reads the
    ///   abstraction's binder or one of its occurrences names a share opened
    ///   inside the leg, and [`SharedPart::Rib`] otherwise.
    /// - provides: the rib test, read off the survey.
    /// - fails: [`DuplicationFault::MachineInvariant`] when the survey did not
    ///   answer `node`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — no survey answer.
    fn part(
        &self,
        node: OverlayId,
        at: RibSite,
    ) -> Result<SharedPart, DuplicationFault>
    {
        let Some(reach) = self.reached.get(&node)
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        if reach.reads.holds(DeBruijnIndex::from(at.depth.0)) == Membership::Held {
            return Ok(SharedPart::Spine);
        }
        match reach.escapes.least() {
            | Some(least) if u32::from(least) < at.inner.0 => Ok(SharedPart::Spine),
            | Some(_) | None => Ok(SharedPart::Rib),
        }
    }

    /// Copy an opaque node, or pass over it.
    ///
    /// # Specification
    /// - requires: `node` is opaque.
    /// - ensures: a fresh opaque node over the same core term, unless the mode
    ///   rebuilds nothing.
    /// - provides: the opaque arm.
    /// - fails: [`DuplicationFault::Mint`] when the family is full, and
    ///   [`DuplicationFault::MachineInvariant`] in a prefix mode, which only
    ///   ever enters a thunk or a lambda.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::Mint`] — the family is full.
    /// - [`DuplicationFault::MachineInvariant`] — a prefix mode met it.
    fn opaque(
        &mut self,
        node: OverlayId,
        mode: Mode,
    ) -> Result<(), DuplicationFault>
    {
        match mode {
            | Mode::Dry { .. } => Ok(()),
            | Mode::Prefix { .. } | Mode::DryPrefix { .. } => {
                Err(DuplicationFault::MachineInvariant)
            },
            | Mode::Plain | Mode::Spine { .. } => {
                let copied = match node {
                    | OverlayId::Value(id) => match self.overlay.value(id) {
                        | Some(&ValueNode::Opaque(term)) => self
                            .overlay
                            .mint_value(ValueNode::Opaque(term))
                            .map(OverlayId::Value),
                        | Some(_) | None => return Err(DuplicationFault::MachineInvariant),
                    },
                    | OverlayId::Computation(id) => match self.overlay.computation(id) {
                        | Some(&CompNode::Opaque(term)) => self
                            .overlay
                            .mint_computation(CompNode::Opaque(term))
                            .map(OverlayId::Computation),
                        | Some(_) | None => return Err(DuplicationFault::MachineInvariant),
                    },
                    | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                        return Err(DuplicationFault::MachineInvariant);
                    },
                };
                let copied = copied.map_err(DuplicationFault::Mint)?;
                self.results.push(copied);
                Ok(())
            },
        }
    }

    /// Resolve an occurrence through the scope, or pass over it.
    ///
    /// # Specification
    /// - requires: `scope` binds the share `bound` names.
    /// - ensures: an occurrence of a kept share becomes an occurrence of its
    ///   output frame; of an inlined share, a fresh walk of the leg in the
    ///   leg's scope; of a distributed share, a spine copy of the leg in the
    ///   leg's scope. The dry pass rebuilds nothing.
    /// - provides: the occurrence arm.
    /// - fails: [`DuplicationFault::Mint`] when the family is full, and
    ///   [`DuplicationFault::MachineInvariant`] when the scope does not answer
    ///   or a prefix mode met it.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::Mint`] — the family is full.
    /// - [`DuplicationFault::MachineInvariant`] — the scope does not answer.
    fn occurrence(
        &mut self,
        node: OverlayId,
        bound: Bound,
        scope: ScopeId,
        mode: Mode,
    ) -> Result<(), DuplicationFault>
    {
        match mode {
            | Mode::Dry { .. } => return Ok(()),
            | Mode::Prefix { .. } | Mode::DryPrefix { .. } => {
                return Err(DuplicationFault::MachineInvariant);
            },
            | Mode::Plain | Mode::Spine { .. } => {},
        }
        let binding = self.binding(scope, bound.distance)?;
        match binding {
            | Binding::Kept { frame } => {
                let pointed = self.point(node, frame)?;
                self.results.push(pointed);
            },
            | Binding::Inlined { leg, scope } => self.tasks.push(Task::Enter {
                node: leg,
                scope,
                mode: Mode::Plain,
            }),
            | Binding::Distributed { leg, scope, ribs } => {
                let cursor = self.cursor(ribs);
                self.tasks.push(Task::Enter {
                    node: leg,
                    scope,
                    mode: Mode::Prefix { cursor },
                });
            },
            | Binding::Empty | Binding::Covered => return Err(DuplicationFault::MachineInvariant),
        }
        Ok(())
    }

    /// Treat one share as its leg and the policy decide.
    ///
    /// # Specification
    /// - requires: `scope` binds every share whose body encloses `node`.
    /// - ensures: a kept share queues its leg, its frame and its close; an
    ///   inlined share binds its leg and queues its body; a distributed share
    ///   queues the dry pass over its leg and then its body. Inside a spine
    ///   copy the share's leg is rebuilt whole and its body read one frame
    ///   further in; the dry pass covers the share and reads only its body.
    /// - provides: the share arm.
    /// - fails: [`DuplicationFault::MachineInvariant`] in a prefix mode, or
    ///   when a frame count passes its counter.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — a prefix mode met it.
    fn share(
        &mut self,
        node: OverlayId,
        sharing: Sharing<OverlayId>,
        scope: ScopeId,
        mode: Mode,
    ) -> Result<(), DuplicationFault>
    {
        let body_mode = match mode {
            | Mode::Plain => Mode::Plain,
            | Mode::Spine { cursor, at } => {
                let at = at.within()?;
                Mode::Spine { cursor, at }
            },
            | Mode::Dry { cursor, at } => {
                let at = at.within()?;
                let covered = self.bind(scope, Binding::Covered);
                self.tasks.push(Task::Enter {
                    node: sharing.body,
                    scope: covered,
                    mode: Mode::Dry { cursor, at },
                });
                return Ok(());
            },
            | Mode::Prefix { .. } | Mode::DryPrefix { .. } => {
                return Err(DuplicationFault::MachineInvariant);
            },
        };
        match treatment(self.policy, leg_shape(self.overlay, sharing.leg)) {
            | Treatment::Keep => {
                self.tasks.push(Task::Close);
                self.tasks.push(Task::Open {
                    share: node,
                    scope,
                    mode: body_mode,
                });
                self.tasks.push(Task::Enter {
                    node: sharing.leg,
                    scope,
                    mode: Mode::Plain,
                });
            },
            | Treatment::Inline => {
                let inner = self.bind(scope, Binding::Inlined {
                    leg: sharing.leg,
                    scope,
                });
                self.tasks.push(Task::Enter {
                    node: sharing.body,
                    scope: inner,
                    mode: body_mode,
                });
            },
            | Treatment::Distribute => {
                let cursor = self.cursor(FrameIndex(self.frames.len()));
                self.tasks.push(Task::Distribute {
                    share: node,
                    scope,
                    mode: body_mode,
                    cursor,
                });
                self.tasks.push(Task::Enter {
                    node: sharing.leg,
                    scope,
                    mode: Mode::DryPrefix { cursor },
                });
            },
        }
        Ok(())
    }

    /// Rebuild one graft, or walk it in a prefix or dry mode.
    ///
    /// # Specification
    /// - requires: `node` is a graft.
    /// - ensures: in a prefix mode a thunk keeps the mode for its lambda and a
    ///   lambda starts the body at the abstraction's own site, the spine copy
    ///   queueing the rebuild and the dry pass not; otherwise the children are
    ///   queued left to right, a binder's children one binder further in, and
    ///   the rebuild after them unless the pass is dry.
    /// - provides: the graft arm.
    /// - fails: [`DuplicationFault::MachineInvariant`] when a prefix mode meets
    ///   anything but a thunk or a lambda, or a depth passes its counter.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — the prefix or a counter
    ///   broke.
    fn graft(
        &mut self,
        node: OverlayId,
        scope: ScopeId,
        mode: Mode,
    ) -> Result<(), DuplicationFault>
    {
        let under = Under::of(self.overlay, node)?;
        let rebuilds = match mode {
            | Mode::Plain | Mode::Prefix { .. } | Mode::Spine { .. } => Rebuilds::Yes,
            | Mode::DryPrefix { .. } | Mode::Dry { .. } => Rebuilds::No,
        };
        if rebuilds == Rebuilds::Yes {
            self.tasks.push(Task::Assemble(node));
        }
        for child in under.listed.into_iter().rev().flatten() {
            let mode = match mode {
                | Mode::Plain => Mode::Plain,
                | Mode::Prefix { cursor } | Mode::DryPrefix { cursor } => {
                    let below = prefix_below(self.overlay, node)?;
                    match (below, rebuilds) {
                        | (Below::Lambda, _) => Mode::Prefix { cursor },
                        | (Below::Body, Rebuilds::Yes) => Mode::Spine {
                            cursor,
                            at: RibSite::default(),
                        },
                        | (Below::Body, Rebuilds::No) => Mode::Dry {
                            cursor,
                            at: RibSite::default(),
                        },
                    }
                },
                | Mode::Spine { cursor, at } => {
                    let at = at.under(child.binders)?;
                    Mode::Spine { cursor, at }
                },
                | Mode::Dry { cursor, at } => {
                    let at = at.under(child.binders)?;
                    Mode::Dry { cursor, at }
                },
            };
            let mode = match (mode, rebuilds) {
                | (Mode::Prefix { cursor }, Rebuilds::No) => Mode::DryPrefix { cursor },
                | (other, _) => other,
            };
            self.tasks.push(Task::Enter {
                node: child.node,
                scope,
                mode,
            });
        }
        Ok(())
    }

    /// Open a kept share's frame and walk its body.
    ///
    /// # Specification
    /// - requires: the share's rebuilt leg is the topmost result.
    /// - ensures: a frame is open for the share, and its body is queued in a
    ///   scope binding the share to that frame.
    /// - provides: the kept share's opening.
    /// - fails: [`DuplicationFault::MachineInvariant`] when `share` is no
    ///   share.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — `share` is no share.
    fn open(
        &mut self,
        share: OverlayId,
        scope: ScopeId,
        mode: Mode,
    ) -> Result<(), DuplicationFault>
    {
        let sharing = self.sharing(share)?;
        let frame = FrameIndex(self.frames.len());
        self.frames.push(Taken::default());
        let inner = self.bind(scope, Binding::Kept { frame });
        self.tasks.push(Task::Enter {
            node: sharing.body,
            scope: inner,
            mode,
        });
        Ok(())
    }

    /// Mint a kept share over its rebuilt leg and body, and close its frame.
    ///
    /// # Specification
    /// - requires: the rebuilt body is the topmost result, the rebuilt leg
    ///   beneath it, and the share's frame the innermost.
    /// - ensures: a share of the arity the frame counted, over the two results.
    /// - provides: the kept share's close.
    /// - fails: [`DuplicationFault::Mint`] when the family is full, and
    ///   [`DuplicationFault::MachineInvariant`] when a stack is short.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::Mint`] — the family is full.
    /// - [`DuplicationFault::MachineInvariant`] — a stack is short.
    fn close(&mut self) -> Result<(), DuplicationFault>
    {
        let (Some(body), Some(leg), Some(taken)) =
            (self.results.pop(), self.results.pop(), self.frames.pop())
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        let shared = self.mint_share(body, ShareArity::from(taken.0), leg)?;
        self.results.push(shared);
        Ok(())
    }

    /// Open one rib share's frame over its rebuilt leg.
    ///
    /// # Specification
    /// - requires: the rib's rebuilt leg is the topmost result.
    /// - ensures: a frame is open for the rib share, and the distribution
    ///   counts one more rib.
    /// - provides: the dry pass's step past each rib.
    /// - fails: [`DuplicationFault::MachineInvariant`] when the cursor does not
    ///   resolve or its count passes the counter.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — the cursor broke.
    fn open_rib(
        &mut self,
        cursor: CursorId,
    ) -> Result<(), DuplicationFault>
    {
        let Some(held) = self.cursors.get_mut(cursor.0)
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        let Some(met) = held.met.0.checked_add(1_u32)
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        held.met = RibCount(met);
        self.frames.push(Taken::default());
        Ok(())
    }

    /// Bind a distributed share once its ribs are found, and walk its body.
    ///
    /// # Specification
    /// - requires: the dry pass over the share's leg has opened one frame per
    ///   rib, from the cursor's first.
    /// - ensures: the body is queued in a scope binding the share to its leg
    ///   and its first rib frame, and the rib shares' close beneath it.
    /// - provides: the distribution's turn from its ribs to its body.
    /// - fails: [`DuplicationFault::MachineInvariant`] when `share` is no share
    ///   or the cursor does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — the share or cursor broke.
    fn distribute(
        &mut self,
        share: OverlayId,
        scope: ScopeId,
        mode: Mode,
        cursor: CursorId,
    ) -> Result<(), DuplicationFault>
    {
        let sharing = self.sharing(share)?;
        let Some(&Cursor { ribs, .. }) = self.cursors.get(cursor.0)
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        let inner = self.bind(scope, Binding::Distributed {
            leg: sharing.leg,
            scope,
            ribs,
        });
        self.tasks.push(Task::CloseRibs(cursor));
        self.tasks.push(Task::Enter {
            node: sharing.body,
            scope: inner,
            mode,
        });
        Ok(())
    }

    /// Mint a distribution's rib shares around its rebuilt body.
    ///
    /// # Specification
    /// - requires: the rebuilt body is the topmost result, each rib's rebuilt
    ///   leg beneath it in reverse, and each rib's frame open, the last
    ///   innermost.
    /// - ensures: one share per rib, innermost first, each of the arity its
    ///   frame counted over its leg and the share inside it.
    /// - provides: the distribution's close.
    /// - fails: [`DuplicationFault::Mint`] when the family is full, and
    ///   [`DuplicationFault::MachineInvariant`] when a stack is short.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::Mint`] — the family is full.
    /// - [`DuplicationFault::MachineInvariant`] — a stack is short.
    fn close_ribs(
        &mut self,
        cursor: CursorId,
    ) -> Result<(), DuplicationFault>
    {
        let (Some(&Cursor { met, .. }), Some(mut body)) =
            (self.cursors.get(cursor.0), self.results.pop())
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        for _rib in 0_u32 .. met.0 {
            let (Some(taken), Some(leg)) = (self.frames.pop(), self.results.pop())
            else {
                return Err(DuplicationFault::MachineInvariant);
            };
            body = self.mint_share(body, ShareArity::from(taken.0), leg)?;
        }
        self.results.push(body);
        Ok(())
    }

    /// Mint the next rib's occurrence in a spine copy.
    ///
    /// # Specification
    /// - requires: the copy's distribution opened a frame for each rib from the
    ///   cursor's first, and the copy meets its ribs in the order the dry pass
    ///   found them.
    /// - ensures: an occurrence of the next rib share's frame, and the copy has
    ///   met one more rib.
    /// - provides: the spine copy's rib arm.
    /// - fails: [`DuplicationFault::Mint`] when the family is full, and
    ///   [`DuplicationFault::MachineInvariant`] when the cursor does not
    ///   resolve or a count passes its counter.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::Mint`] — the family is full.
    /// - [`DuplicationFault::MachineInvariant`] — the cursor broke.
    fn rib_occurrence(
        &mut self,
        node: OverlayId,
        cursor: CursorId,
    ) -> Result<(), DuplicationFault>
    {
        let Some(held) = self.cursors.get_mut(cursor.0)
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        let (Ok(offset), Some(met)) = (usize::try_from(held.met.0), held.met.0.checked_add(1_u32))
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        let Some(frame) = held.ribs.0.checked_add(offset)
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        held.met = RibCount(met);
        let pointed = self.point(node, FrameIndex(frame))?;
        self.results.push(pointed);
        Ok(())
    }

    /// Mint an occurrence of the output frame `frame`, in `node`'s family.
    ///
    /// # Specification
    /// - requires: `frame` is open.
    /// - ensures: an occurrence at the distance from the innermost open frame
    ///   to `frame`, at the frame's next position, which advances by one.
    /// - provides: the one place an output occurrence is minted.
    /// - fails: [`DuplicationFault::Mint`] when the family is full, and
    ///   [`DuplicationFault::MachineInvariant`] when `frame` is not open or a
    ///   count passes its counter.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::Mint`] — the family is full.
    /// - [`DuplicationFault::MachineInvariant`] — the frame broke.
    fn point(
        &mut self,
        node: OverlayId,
        frame: FrameIndex,
    ) -> Result<OverlayId, DuplicationFault>
    {
        let distance = self
            .frames
            .len()
            .checked_sub(1)
            .and_then(|innermost| innermost.checked_sub(frame.0))
            .and_then(|distance| u32::try_from(distance).ok());
        let Some(distance) = distance
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        let Some(taken) = self.frames.get_mut(frame.0)
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        let position = SharePosition::from(taken.0);
        let Some(next) = taken.0.checked_add(1_u32)
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        *taken = Taken(next);
        let bound = Bound {
            distance: ShareDistance::from(distance),
            position,
        };
        let pointed = match node {
            | OverlayId::Value(_) => self
                .overlay
                .mint_value(ValueNode::Bound(bound))
                .map(OverlayId::Value),
            | OverlayId::Computation(_) => self
                .overlay
                .mint_computation(CompNode::Bound(bound))
                .map(OverlayId::Computation),
            | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                return Err(DuplicationFault::MachineInvariant);
            },
        };
        pointed.map_err(DuplicationFault::Mint)
    }

    /// Mint a share of `arity` over `leg` and `body`, in the body's family.
    ///
    /// # Specification
    /// - requires: `leg` and `body` are rebuilt nodes.
    /// - ensures: the share, in the body's family.
    /// - provides: the one place an output share is minted.
    /// - fails: [`DuplicationFault::Mint`] when the family is full, and
    ///   [`DuplicationFault::MachineInvariant`] for a body of a type family.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::Mint`] — the family is full.
    /// - [`DuplicationFault::MachineInvariant`] — the body is of a type family.
    fn mint_share(
        &mut self,
        body: OverlayId,
        arity: ShareArity,
        leg: OverlayId,
    ) -> Result<OverlayId, DuplicationFault>
    {
        let shared = match body {
            | OverlayId::Value(body) => self
                .overlay
                .mint_value(ValueNode::Shared(Sharing { arity, leg, body }))
                .map(OverlayId::Value),
            | OverlayId::Computation(body) => self
                .overlay
                .mint_computation(CompNode::Shared(Sharing { arity, leg, body }))
                .map(OverlayId::Computation),
            | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                return Err(DuplicationFault::MachineInvariant);
            },
        };
        shared.map_err(DuplicationFault::Mint)
    }

    /// Rebuild the graft `node` over the children its tasks left.
    ///
    /// # Specification
    /// - requires: the graft's rebuilt children are the topmost results,
    ///   rightmost on top.
    /// - ensures: a fresh graft of the same former and payload over them.
    /// - provides: the one place a graft is rebuilt.
    /// - fails: [`DuplicationFault::Mint`] when the family is full, and
    ///   [`DuplicationFault::MachineInvariant`] when a child is missing or of
    ///   another family.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::Mint`] — the family is full.
    /// - [`DuplicationFault::MachineInvariant`] — a child is missing.
    fn assemble(
        &mut self,
        node: OverlayId,
    ) -> Result<OverlayId, DuplicationFault>
    {
        match node {
            | OverlayId::Value(id) => {
                let Some(held) = self.overlay.value(id)
                else {
                    return Err(DuplicationFault::MachineInvariant);
                };
                let ValueNode::Grafted(ref graft) = *held
                else {
                    return Err(DuplicationFault::MachineInvariant);
                };
                let graft = graft.clone();
                let rebuilt = match graft {
                    | ValueGraft::Variable { .. }
                    | ValueGraft::Constant(_)
                    | ValueGraft::Unit
                    | ValueGraft::Literal(_) => graft,
                    | ValueGraft::Pair(..) => {
                        let second = self.value()?;
                        let first = self.value()?;
                        ValueGraft::Pair(first, second)
                    },
                    | ValueGraft::Injection(side, _) => {
                        let body = self.value()?;
                        ValueGraft::Injection(side, body)
                    },
                    | ValueGraft::Thunk(_) => {
                        let body = self.computation()?;
                        ValueGraft::Thunk(body)
                    },
                    | ValueGraft::Lift { target, .. } => {
                        let body = self.value()?;
                        ValueGraft::Lift { target, body }
                    },
                    // `Under::of` refuses a quote before its assembly is queued.
                    | ValueGraft::Quote(_) | ValueGraft::QuoteComputation(_) => {
                        return Err(DuplicationFault::MachineInvariant);
                    },
                };
                let minted = self
                    .overlay
                    .mint_value(ValueNode::Grafted(rebuilt))
                    .map_err(DuplicationFault::Mint)?;
                Ok(OverlayId::Value(minted))
            },
            | OverlayId::Computation(id) => {
                let Some(&CompNode::Grafted(graft)) = self.overlay.computation(id)
                else {
                    return Err(DuplicationFault::MachineInvariant);
                };
                let rebuilt = match graft {
                    | CompGraft::Lambda(_) => {
                        let body = self.computation()?;
                        CompGraft::Lambda(body)
                    },
                    | CompGraft::Application(..) => {
                        let argument = self.value()?;
                        let head = self.computation()?;
                        CompGraft::Application(head, argument)
                    },
                    | CompGraft::Return(_) => {
                        let value = self.value()?;
                        CompGraft::Return(value)
                    },
                    | CompGraft::Bind(..) => {
                        let body = self.computation()?;
                        let bound = self.computation()?;
                        CompGraft::Bind(bound, body)
                    },
                    | CompGraft::Force(_) => {
                        let value = self.value()?;
                        CompGraft::Force(value)
                    },
                    | CompGraft::Case { .. } => {
                        let on_right = self.computation()?;
                        let on_left = self.computation()?;
                        let scrutinee = self.value()?;
                        CompGraft::Case {
                            scrutinee,
                            on_left,
                            on_right,
                        }
                    },
                };
                let minted = self
                    .overlay
                    .mint_computation(CompNode::Grafted(rebuilt))
                    .map_err(DuplicationFault::Mint)?;
                Ok(OverlayId::Computation(minted))
            },
            | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                Err(DuplicationFault::MachineInvariant)
            },
        }
    }

    /// Pop a rebuilt value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the topmost result, when it is a value.
    /// - provides: the typed pop that catches a family the walk did not expect.
    /// - fails: [`DuplicationFault::MachineInvariant`] when the top is missing
    ///   or of another family.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — no value is on top.
    fn value(&mut self) -> Result<OverlayValueId, DuplicationFault>
    {
        let Some(OverlayId::Value(id)) = self.results.pop()
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        Ok(id)
    }

    /// Pop a rebuilt computation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the topmost result, when it is a computation.
    /// - provides: the typed pop that catches a family the walk did not expect.
    /// - fails: [`DuplicationFault::MachineInvariant`] when the top is missing
    ///   or of another family.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — no computation is on top.
    fn computation(&mut self) -> Result<OverlayCompId, DuplicationFault>
    {
        let Some(OverlayId::Computation(id)) = self.results.pop()
        else {
            return Err(DuplicationFault::MachineInvariant);
        };
        Ok(id)
    }

    /// The share `share` holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the share's arity, leg and body.
    /// - provides: the checked read of a share the frame tasks name.
    /// - fails: [`DuplicationFault::MachineInvariant`] when `share` is no
    ///   share.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — `share` is no share.
    fn sharing(
        &self,
        share: OverlayId,
    ) -> Result<Sharing<OverlayId>, DuplicationFault>
    {
        match self.overlay.shape(share) {
            | Ok(Shape::Shared(sharing)) => Ok(sharing),
            | Ok(Shape::Opaque(_) | Shape::Bound(_) | Shape::Grafted(_)) | Err(_) => {
                Err(DuplicationFault::MachineInvariant)
            },
        }
    }

    /// The binding of the share `distance` shares out from `scope`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the binding of the cell `distance` parents up from `scope`.
    /// - provides: the occurrence lookup, one cell per share passed.
    /// - fails: [`DuplicationFault::MachineInvariant`] when the walk reaches
    ///   the empty scope or a cell that does not resolve.
    /// - panics: none.
    /// - intension: `economy: a lookup walks one cell per share between the
    ///   occurrence and its share; index the cells by depth when a workload's
    ///   distances meet it`.
    ///
    /// # Errors
    /// - [`DuplicationFault::MachineInvariant`] — the scope does not answer.
    fn binding(
        &self,
        scope: ScopeId,
        distance: ShareDistance,
    ) -> Result<Binding, DuplicationFault>
    {
        let mut here = scope;
        let mut remaining = u32::from(distance);
        loop {
            let Some(cell) = self.scopes.get(here.0)
            else {
                return Err(DuplicationFault::MachineInvariant);
            };
            if cell.binding == Binding::Empty {
                return Err(DuplicationFault::MachineInvariant);
            }
            let Some(further) = remaining.checked_sub(1_u32)
            else {
                return Ok(cell.binding);
            };
            remaining = further;
            here = cell.parent;
        }
    }

    /// Open a scope cell binding one share inside `scope`.
    ///
    /// # Specification
    /// trivial.
    fn bind(
        &mut self,
        scope: ScopeId,
        binding: Binding,
    ) -> ScopeId
    {
        let cell = ScopeId(self.scopes.len());
        self.scopes.push(ScopeCell {
            binding,
            parent: scope,
        });
        cell
    }

    /// Start a cursor whose first rib frame is `ribs`.
    ///
    /// # Specification
    /// trivial.
    fn cursor(
        &mut self,
        ribs: FrameIndex,
    ) -> CursorId
    {
        let cursor = CursorId(self.cursors.len());
        self.cursors.push(Cursor {
            ribs,
            met: RibCount::default(),
        });
        cursor
    }
}

/// Whether a walk rebuilds what it enters.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rebuilds
{
    /// It does.
    Yes,
    /// It does not: the dry pass.
    No,
}

/// What lies below a node of an abstraction's prefix.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Below
{
    /// The lambda, below a thunk.
    Lambda,
    /// The abstraction's body, below the lambda.
    Body,
}

/// What lies below `node`, a node of an abstraction's prefix.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Below::Lambda`] for a grafted thunk and [`Below::Body`] for a
///   grafted lambda.
/// - provides: the prefix's one decision.
/// - fails: [`DuplicationFault::MachineInvariant`] for any other node, which
///   the treatment's classification excludes.
/// - panics: none.
///
/// # Errors
/// - [`DuplicationFault::MachineInvariant`] — `node` is no prefix node.
fn prefix_below(
    overlay: &Overlay,
    node: OverlayId,
) -> Result<Below, DuplicationFault>
{
    match node {
        | OverlayId::Value(id) => match overlay.value(id) {
            | Some(&ValueNode::Grafted(ValueGraft::Thunk(_))) => Ok(Below::Lambda),
            | Some(_) | None => Err(DuplicationFault::MachineInvariant),
        },
        | OverlayId::Computation(id) => match overlay.computation(id) {
            | Some(&CompNode::Grafted(CompGraft::Lambda(_))) => Ok(Below::Body),
            | Some(_) | None => Err(DuplicationFault::MachineInvariant),
        },
        | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
            Err(DuplicationFault::MachineInvariant)
        },
    }
}
