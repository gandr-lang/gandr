//! The check of the IL's annotations: each field type against the type of the
//! binder that binds the field's variable.
//!
//! Focusing writes a type on each `μ̃x` and on each field of a constructor. It
//! imports each type by its content, so two annotations of one content share
//! one id, and the check compares ids with no conversion. A node states once
//! the types that its constructor fields demand of its free producer
//! variables. A parent reads each child's demands past the binders that it
//! opens over the child. A `μ̃x : T` discharges the demand on `x` against `T`.
//! Every other binder discharges its variables with no type to compare.
//!
//! # Boundaries
//!
//! - **The unknown type compares with nothing.** A field or a binder at the
//!   unknown type is a position that the check cannot verify.
//! - **A field that is no variable demands nothing.** Its value carries no
//!   annotation to compare.
//! - **A binder with no annotation verifies nothing.** A pattern arm, a
//!   copattern arm, a closure's code, a fixpoint and a memory form's body bind
//!   variables with no type in the IL.
//! - **A shared node counts once for each parent.** A parent reads the demands
//!   of a shared child again, so the counts of fields follow the paths, and the
//!   work stays one visit of each node.
//!
//! # References
//!
//! - `vault:01a1ead7-6581-7f22-9479-5b0b363e80d3` — newest: the IL states the
//!   type of each binder `μ̃x` and of each field of a constructor. The checker's
//!   report gives the type, and this check verifies it where the IL gives it
//!   directly.

use alloc::collections::BTreeMap;

use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;

use super::CheckRefusal;
use super::dangling;
use crate::boundary::NodeCount;
use crate::il::CommandArena;
use crate::il::ConsumerNode;
use crate::il::NodeAddress;
use crate::il::Opens;
use crate::il::ProducerNode;
use crate::il::command_children;
use crate::il::consumer_children;
use crate::il::producer_children;

/// The type that the fields of a node demand of one free variable, and how
/// many fields demand it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Demand
{
    /// The demanded type.
    ty: ValueTypeId,
    /// The fields that demand it.
    fields: NodeCount,
}

/// The demands of one node, by the zone and the index of each free producer
/// variable, counted from the node.
type Demands = BTreeMap<(Zone, DeBruijnIndex), Demand>;

/// What the check of the annotations reads over one command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Annotated
{
    /// The field demands that a `μ̃` discharges at the same id.
    fields_verified: NodeCount,
    /// The field demands that no typed `μ̃` discharges, and the fields at the
    /// unknown type or with no variable.
    fields_unverified: NodeCount,
    /// The typed `μ̃` binders that discharge a demand at their own id.
    binders_verified: NodeCount,
    /// The `μ̃` binders that discharge no demand, or hold the unknown type.
    binders_unverified: NodeCount,
}

impl Annotated
{
    /// The field demands that a `μ̃` discharges at the same id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fields_verified(&self) -> NodeCount
    {
        self.fields_verified
    }

    /// The fields that the check cannot verify.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fields_unverified(&self) -> NodeCount
    {
        self.fields_unverified
    }

    /// The typed `μ̃` binders that discharge a demand at their own id.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn binders_verified(&self) -> NodeCount
    {
        self.binders_verified
    }

    /// The `μ̃` binders that the check cannot verify.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn binders_unverified(&self) -> NodeCount
    {
        self.binders_unverified
    }
}

/// A step of the walk: the first visit schedules the children, and the
/// second reads their demands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Visit
{
    /// Schedule the children.
    Enter,
    /// Read the children's demands.
    Leave,
}

/// Compare each field type below `root` with the type of the binder of its
/// variable, by id. A demand that reaches `root` free counts unverified.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each `μ̃x : T` that discharges a field's demand on `x` at the id
///   `T` counts the field and the binder verified; each other field and binder
///   counts unverified.
/// - fails: a demand that a `μ̃` discharges at another id, two demands of one
///   variable at two ids, and an address that the arena does not hold.
/// - panics: none.
/// - executable: none — the counts and the verdict are the walk's own result,
///   which only a second walk could restate.
///
/// # Errors
/// [`CheckRefusal::AnnotationMismatch`] at the `μ̃`, or at the node that joins
/// two demands, for two ids of one variable. [`CheckRefusal::DanglingCommand`],
/// [`CheckRefusal::DanglingProducer`] or [`CheckRefusal::DanglingConsumer`] for
/// an address that the arena does not hold.
///
/// # Cost
/// - allocation: the demands of each node, one map each, growth within the
///   nodes below `root`
///
/// # Adequacy
/// - hypothesis: L3 — a field whose variable a `μ̃` binds at the same type, at
///   another type and at the unknown type separates the three verdicts.
/// - witness: `check::tests::a_field_meets_its_binder_by_id_8161`
#[inline]
pub fn check_annotations(
    arena: &CommandArena,
    root: NodeAddress,
) -> Result<Annotated, CheckRefusal>
{
    let unknown = arena.unknown_type();
    let mut annotated = Annotated::default();
    let mut demands: BTreeMap<NodeAddress, Demands> = BTreeMap::new();
    let mut pending = alloc::vec![(root, Visit::Enter)];
    while let Some((node, visit)) = pending.pop() {
        if demands.contains_key(&node) {
            continue;
        }
        if visit == Visit::Enter {
            pending.push((node, Visit::Leave));
            children(arena, node, |child, _| {
                if !demands.contains_key(&child) {
                    pending.push((child, Visit::Enter));
                }
                Ok(())
            })?;
            continue;
        }
        let mut own = Demands::new();
        if let NodeAddress::Producer(id) = node
            && let Some(&ProducerNode::Constructor {
                ref producers,
                ref types,
                ..
            }) = arena.producer(id)
        {
            for (&field, &ty) in producers.iter().zip(types.iter()) {
                match arena.producer(field) {
                    Some(&ProducerNode::Variable { zone, index }) if ty != unknown => {
                        let demand = Demand {
                            ty,
                            fields: NodeCount::from(1_usize),
                        };
                        join(&mut own, (zone, index), demand, node)?;
                    },
                    Some(_) => add(&mut annotated.fields_unverified, NodeCount::from(1_usize)),
                    None => return Err(dangling(NodeAddress::Producer(field))),
                }
            }
        }
        let binder = match node {
            NodeAddress::Consumer(id) => match arena.consumer(id) {
                Some(&ConsumerNode::MuTilde { ty, .. }) => Some(ty),
                Some(_) | None => None,
            },
            NodeAddress::Command(_) | NodeAddress::Producer(_) => None,
        };
        let mut met = false;
        children(arena, node, |child, opens: Opens| {
            let held = demands.get(&child).ok_or_else(|| dangling(child))?;
            for (&(zone, index), &demand) in held {
                let crossed =
                    u32::try_from(usize::from(opens.producers.depth(zone))).unwrap_or(u32::MAX);
                if let Some(outer) = u32::from(index).checked_sub(crossed) {
                    join(&mut own, (zone, DeBruijnIndex::from(outer)), demand, node)?;
                    continue;
                }
                match binder {
                    Some(stated) if stated != unknown && stated == demand.ty => {
                        add(&mut annotated.fields_verified, demand.fields);
                        met = true;
                    },
                    Some(stated) if stated != unknown => {
                        return Err(CheckRefusal::AnnotationMismatch {
                            at: node,
                            stated,
                            demanded: demand.ty,
                        });
                    },
                    Some(_) | None => add(&mut annotated.fields_unverified, demand.fields),
                }
            }
            Ok(())
        })?;
        if binder.is_some() {
            let tally = if met {
                &mut annotated.binders_verified
            }
            else {
                &mut annotated.binders_unverified
            };
            add(tally, NodeCount::from(1_usize));
        }
        let _first = demands.insert(node, own);
    }
    for demand in demands.get(&root).into_iter().flat_map(BTreeMap::values) {
        add(&mut annotated.fields_unverified, demand.fields);
    }
    Ok(annotated)
}

/// Join `demand` into the demands of `node` on `variable`: one more field at
/// the same type, or a refusal at another type.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`CheckRefusal::AnnotationMismatch`] at `node` for a held demand at another
/// type.
fn join(
    own: &mut Demands,
    variable: (Zone, DeBruijnIndex),
    demand: Demand,
    node: NodeAddress,
) -> Result<(), CheckRefusal>
{
    match own.get_mut(&variable) {
        None => {
            let _first = own.insert(variable, demand);
        },
        Some(held) if held.ty == demand.ty => add(&mut held.fields, demand.fields),
        Some(held) => {
            return Err(CheckRefusal::AnnotationMismatch {
                at: node,
                stated: held.ty,
                demanded: demand.ty,
            });
        },
    }
    Ok(())
}

/// Add `more` to `count`.
///
/// # Specification
/// trivial.
fn add(
    count: &mut NodeCount,
    more: NodeCount,
)
{
    *count = NodeCount::from(usize::from(*count).saturating_add(usize::from(more)));
}

/// Visit the children of `node` beside the binders that it opens over each.
///
/// # Specification
/// trivial.
fn children<Each>(
    arena: &CommandArena,
    node: NodeAddress,
    each: Each,
) -> Result<(), CheckRefusal>
where
    Each: FnMut(NodeAddress, Opens) -> Result<(), CheckRefusal>,
{
    match node {
        NodeAddress::Command(id) => {
            command_children(arena.command(id).ok_or_else(|| dangling(node))?, each)
        },
        NodeAddress::Producer(id) => {
            producer_children(arena.producer(id).ok_or_else(|| dangling(node))?, each)
        },
        NodeAddress::Consumer(id) => {
            consumer_children(arena.consumer(id).ok_or_else(|| dangling(node))?, each)
        },
    }
}
