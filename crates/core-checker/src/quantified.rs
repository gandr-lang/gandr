//! A definition quantified over stages: `def applyAt @[i : Size] (f :
//! Nat[<i] => Nat, x : Nat[<i])`.
//!
//! - **The signature is read off the declared type.** The lowering writes each
//!   `Nat[i]` as `Nat` at the stage its binder's ordinal names; [`split`] reads
//!   every such occurrence the stage order places into a [`StageMark`] and
//!   erases it, so the signature table holds the plain type and the kernel
//!   receives the marks beside it.
//! - **The definition's own body checks at minted stages.** [`mint`] mints one
//!   stage per binder before the signature forms, a bounded binder's below its
//!   bound's, so each binder's ordinal is the stage it minted and the declared
//!   type is the type the body checks at.
//! - **A call reads its stages off its arguments**, as the kernel does
//!   ([`instantiation`]): each binder at the stage of the first marked
//!   occurrence a variable argument's type holds a stage at; a binder no
//!   argument shows leaves its occurrences plain. The arguments then check
//!   against the re-staged type ([`restaged`]) by the stage order.
//!
//! An occurrence the stage order does not place — inside a path type's
//! carrier, say — is not marked; it crosses as a stage the kernel never
//! reads from a term, and the crossing refuses it.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::staged::Part;
use gandr_core_term::staged::placed;
use gandr_core_term::staged::rebuild;
use gandr_kernel_core::stage_order::Fit;
use gandr_kernel_core::stage_order::StageOrder;
use gandr_kernel_core::stage_order::below;
use gandr_kernel_term::PlacedChild;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageBinder;
use gandr_kernel_term::StageBound;
use gandr_kernel_term::StageId;
use gandr_kernel_term::StageMark;
use gandr_kernel_term::StageReach;
use gandr_kernel_term::StageSignature;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;

/// Why a binder stands at no stage.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unread
{
    /// No argument shows it: its occurrences stay plain.
    Plain,
}

/// The refusal a stage naming no binder of the signature, or refining no
/// data type, earns at `at`.
///
/// # Specification
/// trivial.
const fn unbound(at: ValueTypeId) -> CheckRefusal
{
    CheckRefusal::OutOfFragment {
        at: CoreNode::Type(TypeNode::Value(at)),
        former: UnadmittedFormer::Stage,
    }
}

/// Refuse `bounds` when a bound names no earlier binder.
///
/// # Specification
/// - ensures: nothing changes.
/// - fails: [`CheckRefusal::OutOfFragment`] naming [`UnadmittedFormer::Stage`]
///   at `declared` for a bound naming the binder it bounds or a later one.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a bound is a binder stated before it.
/// - witness: `quantified::tests::a_bound_naming_a_later_binder_is_refused`
#[spec(ensures: |ret| ret.is_err() == bounds.iter().enumerate().any(|(ordinal, &bound)| {
    matches!(bound, StageBound::Below(binder) if usize::from(binder) >= ordinal)
}))]
pub fn bounded(
    bounds: &[StageBound],
    declared: ValueTypeId,
) -> Result<(), CheckRefusal>
{
    for (ordinal, &bound) in bounds.iter().enumerate() {
        match bound {
            StageBound::Below(binder) if usize::from(binder) >= ordinal => {
                return Err(unbound(declared));
            },
            StageBound::Below(_) | StageBound::Unbounded => {},
        }
    }
    Ok(())
}

/// Mint one stage per binder of `bounds` in `stages`, in binder order: a root
/// for an unbounded binder, a child of its bound's stage for a bounded one.
///
/// # Specification
/// - requires: `stages` is the fresh order of the judgement about to run, so
///   each binder's stage is its ordinal; [`bounded`] accepted `bounds`.
/// - ensures: one stage minted per binder, each bounded one below its bound's.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a helper typed at a stage checks its body there.
/// - witness: `quantified::tests::a_helper_at_a_stage_takes_a_recursion_s_claim`
#[spec(requires: bounds.iter().enumerate().all(|(ordinal, &bound)| {
    !matches!(bound, StageBound::Below(binder) if usize::from(binder) >= ordinal)
}))]
pub fn mint(
    stages: &mut StageOrder,
    bounds: &[StageBound],
)
{
    for &bound in bounds {
        let _minted = match bound {
            StageBound::Unbounded => stages.mint_root(),
            StageBound::Below(binder) => stages
                .mint_below(StageId::from(usize::from(binder)))
                .unwrap_or_else(|_unminted| stages.mint_root()),
        };
    }
}

/// `declared` with every staged occurrence the stage order places erased,
/// and a mark for each: its path, the binder its stage's ordinal names and
/// its reach.
///
/// # Specification
/// - requires: each stage in `declared` names a binder by its ordinal.
/// - ensures: the erased type and the marks in pre-order; `declared` itself and
///   no mark when it holds no placed stage.
/// - fails: [`CheckRefusal::OutOfFragment`] naming [`UnadmittedFormer::Stage`]
///   for a stage naming no binder of `bounds` or refining no data type, the
///   occurrence the kernel's mark could not place;
///   [`CheckRefusal::MachineInvariant`] for a malformed arena.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `while let` worklist, not recursion; each node is opened once
///   and closed once.
/// - measure: the unread nodes under `declared`, finite because the arena is
///   acyclic.
///
/// # Adequacy
/// - hypothesis: L3 — a helper's function parameter and its argument each yield
///   a mark and erase to the plain type.
/// - witness: `quantified::tests::a_helper_at_a_stage_takes_a_recursion_s_claim`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(erased, ref marks)| arena.value_type(erased).is_some() && marks.iter().all(|mark| usize::from(mark.binder()) < bounds.len())))]
pub fn split(
    arena: &mut CoreArena,
    declared: ValueTypeId,
    bounds: &[StageBound],
) -> Result<(ValueTypeId, Vec<StageMark>), CheckRefusal>
{
    /// One step of the walk.
    enum Walk
    {
        /// Read the node at the path, recording its stage and opening its
        /// placed children.
        Open(Part, Vec<PlacedChild>),
        /// Rebuild the node from its children's erasures.
        Close(Part, usize),
    }
    let mut marks = Vec::new();
    let mut erased: Vec<Part> = Vec::new();
    let mut work = alloc::vec![Walk::Open(Part::Value(declared), Vec::new())];
    while let Some(step) = work.pop() {
        match step {
            Walk::Open(part, path) => {
                let part = match part {
                    Part::Value(id) => match arena.value_type(id) {
                        Some(&ValueType::Staged { base, stage }) => {
                            let (anchor, reach) = match stage {
                                Stage::At(anchor) => (anchor, StageReach::At),
                                Stage::Below { anchor, depth } => {
                                    (anchor, StageReach::Below(depth))
                                },
                            };
                            if usize::from(anchor) >= bounds.len()
                                || !matches!(arena.value_type(base), Some(ValueType::Data { .. }))
                            {
                                return Err(unbound(id));
                            }
                            marks.push(StageMark::new(
                                path.clone(),
                                StageBinder::from(usize::from(anchor)),
                                reach,
                            ));
                            Part::Value(base)
                        },
                        Some(_) | None => part,
                    },
                    Part::Computation(_) => part,
                };
                let mut children = Vec::new();
                placed(arena, part, |child| children.push(child));
                work.push(Walk::Close(part, children.len()));
                for (ordinal, child) in children.into_iter().enumerate().rev() {
                    let mut inner = path.clone();
                    inner.push(PlacedChild::from(ordinal));
                    work.push(Walk::Open(child, inner));
                }
            },
            Walk::Close(part, count) => {
                let start = erased
                    .len()
                    .checked_sub(count)
                    .ok_or(CheckRefusal::MachineInvariant)?;
                let children = erased.split_off(start);
                erased.push(if children.is_empty() {
                    part
                }
                else {
                    rebuild(arena, part, &children).ok_or(CheckRefusal::MachineInvariant)?
                });
            },
        }
    }
    match (erased.pop(), erased.is_empty()) {
        (Some(Part::Value(erased)), true) => Ok((erased, marks)),
        (Some(_) | None, _) => Err(CheckRefusal::MachineInvariant),
    }
}

/// `declared` with each occurrence `signature` marks refined at its binder's
/// stage in `at`, read through the mark's reach; an occurrence whose binder
/// stands at no stage stays plain.
///
/// # Specification
/// - requires: `at` holds one entry per binder of `signature`; `declared` is
///   the type [`split`] erased the marks from.
/// - ensures: `declared` itself when every binder stands at no stage; otherwise
///   the same type with each marked occurrence staged, the deepest marks first.
/// - fails: [`CheckRefusal::MachineInvariant`] for a mark the type does not
///   place.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`instantiation`].
/// - witness: `quantified::tests::a_helper_at_a_stage_takes_a_recursion_s_claim`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&staged| arena.value_type(staged).is_some()))]
pub fn restaged(
    arena: &mut CoreArena,
    declared: ValueTypeId,
    signature: &StageSignature,
    at: &[Maybe<Stage, Unread>],
) -> Result<ValueTypeId, CheckRefusal>
{
    let mut order: Vec<&StageMark> = signature.marks().iter().collect();
    order.sort_by_key(|mark| core::cmp::Reverse(mark.path().len()));
    let mut root = Part::Value(declared);
    for mark in order {
        let stage = match at.get(usize::from(mark.binder())) {
            Some(&Maybe::Present(stage)) => reached_through(stage, mark.reach()),
            Some(&Maybe::Absent(Unread::Plain)) => continue,
            None => return Err(CheckRefusal::MachineInvariant),
        };
        root = wrapped(arena, root, mark.path(), stage)?;
    }
    match root {
        Part::Value(staged) => Ok(staged),
        Part::Computation(_) => Err(CheckRefusal::MachineInvariant),
    }
}

/// The stage of an occurrence `reach` places relative to a binder at `stage`.
///
/// # Specification
/// trivial.
fn reached_through(
    stage: Stage,
    reach: StageReach,
) -> Stage
{
    match reach {
        StageReach::At => stage,
        StageReach::Below(depth) => {
            let mut lowered = stage;
            for _step in 0 .. u32::from(depth) {
                lowered = below(lowered);
            }
            lowered
        },
    }
}

/// `root` with the data type `path` reaches refined at `stage`, every node on
/// the way rebuilt over its new child.
///
/// # Specification
/// - ensures: the rebuilt root, of `root`'s kind.
/// - fails: [`CheckRefusal::MachineInvariant`] for a step past a former's
///   placed children or an end at no data type.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`restaged`].
/// - witness: `quantified::tests::a_helper_at_a_stage_takes_a_recursion_s_claim`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |rebuilt| matches!((root, *rebuilt),
    (Part::Value(_), Part::Value(_)) | (Part::Computation(_), Part::Computation(_)))))]
fn wrapped(
    arena: &mut CoreArena,
    root: Part,
    path: &[PlacedChild],
    stage: Stage,
) -> Result<Part, CheckRefusal>
{
    let mut chain: Vec<(Part, Vec<Part>)> = Vec::with_capacity(path.len());
    let mut node = root;
    for &step in path {
        let mut children = Vec::new();
        placed(arena, node, |child| children.push(child));
        let Some(&next) = children.get(usize::from(step))
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        chain.push((node, children));
        node = next;
    }
    let Part::Value(occurrence) = node
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    if !matches!(arena.value_type(occurrence), Some(&ValueType::Data { .. })) {
        return Err(CheckRefusal::MachineInvariant);
    }
    let mut rebuilt = Part::Value(arena.value_type_staged(occurrence, stage));
    for (&step, (parent, mut children)) in path.iter().rev().zip(chain.into_iter().rev()) {
        if let Some(child) = children.get_mut(usize::from(step)) {
            *child = rebuilt;
        }
        rebuilt = rebuild(arena, parent, &children).ok_or(CheckRefusal::MachineInvariant)?;
    }
    Ok(rebuilt)
}

/// The stages a call of a definition declared `declared`, quantified over
/// `signature`, instantiates its binders at: each read where the first mark
/// of it lies in the domain of an argument of `spine` that is a variable
/// whose type, `found` reads it, holds a stage there.
///
/// # Specification
/// - requires: `spine` holds the call's arguments, first applied first;
///   `declared` is the thunk of the definition's arrows; `order` holds every
///   stage the arguments' types name.
/// - ensures: one entry per binder: a stage read off an argument, a bounded
///   binder no argument shows read one step below its bound's stage, and no
///   stage otherwise. A mark at `<i` reads `i` off an argument bound `<s` at
///   `s`, and off nothing at a stage itself.
/// - fails: `found`'s refusal; [`CheckRefusal::StageNotBelow`] at the argument
///   a bounded binder is read off when `order` does not place its stage below
///   its bound's, where the body was checked with it.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a recursion's claim handed to a helper typed at a stage
///   instantiates it at the recursion's own; a call on a value at no stage
///   instantiates nothing; a bounded binder read at its bound's own stage is
///   refused.
/// - witness: `quantified::tests::a_helper_at_a_stage_takes_a_recursion_s_claim`
/// - witness: `quantified::tests::a_call_at_no_stage_reads_its_result_plain`
/// - witness: `quantified::tests::a_bounded_binder_read_above_its_bound_is_refused_1241`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |read| read.len() == signature.bounds().len()))]
pub fn instantiation<Found>(
    (arena, order): (&CoreArena, &StageOrder),
    (declared, signature): (ValueTypeId, &StageSignature),
    spine: &[ValueId],
    mut found: Found,
) -> Result<Vec<Maybe<Stage, Unread>>, CheckRefusal>
where
    Found: FnMut(gandr_kernel_term::DeBruijnIndex) -> Result<ValueTypeId, CheckRefusal>,
{
    let mut read: Vec<Maybe<Stage, Unread>> = signature
        .bounds()
        .iter()
        .map(|_| Maybe::Absent(Unread::Plain))
        .collect();
    let mut shown: Vec<Option<ValueId>> = signature.bounds().iter().map(|_| None).collect();
    for mark in signature.marks() {
        let binder = usize::from(mark.binder());
        if !matches!(read.get(binder), Some(&Maybe::Absent(_))) {
            continue;
        }
        let Maybe::Present((argument, inside)) = argument_at(arena, (declared, spine), mark.path())
        else {
            continue;
        };
        let Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) = arena.value(argument)
        else {
            continue;
        };
        let Maybe::Present(stage) = stage_at(arena, found(index)?, inside)
        else {
            continue;
        };
        let instance = match (mark.reach(), stage) {
            (StageReach::At, stage) => Maybe::Present(stage),
            (
                StageReach::Below(depth),
                Stage::Below {
                    anchor,
                    depth: under,
                },
            ) => match u32::from(under).checked_sub(u32::from(depth)) {
                Some(0) => Maybe::Present(Stage::At(anchor)),
                Some(rest) => {
                    core::num::NonZeroU32::new(rest).map_or(Maybe::Absent(Unread::Plain), |rest| {
                        Maybe::Present(Stage::Below {
                            anchor,
                            depth: gandr_kernel_term::StageDepth::from(rest),
                        })
                    })
                },
                None => Maybe::Absent(Unread::Plain),
            },
            (StageReach::Below(_), Stage::At(_)) => Maybe::Absent(Unread::Plain),
        };
        if let Some(slot) = read.get_mut(binder) {
            *slot = instance;
        }
        if let Some(slot) = shown.get_mut(binder) {
            *slot = Some(argument);
        }
    }
    for (binder, &bound) in signature.bounds().iter().enumerate() {
        let StageBound::Below(over) = bound
        else {
            continue;
        };
        let Some(&Maybe::Present(above)) = read.get(usize::from(over))
        else {
            continue;
        };
        match (read.get(binder), shown.get(binder)) {
            (Some(&Maybe::Present(stage)), Some(&Some(argument))) => {
                if order.fit(stage, below(above)) == Fit::NotBelow {
                    return Err(CheckRefusal::StageNotBelow {
                        at: argument,
                        found: gandr_kernel_term::Standing::Staged(stage),
                        bound: below(above),
                    });
                }
            },
            (Some(&Maybe::Absent(_)), _) => {
                if let Some(slot) = read.get_mut(binder) {
                    *slot = Maybe::Present(below(above));
                }
            },
            (Some(&Maybe::Present(_)), Some(&None) | None) | (None, _) => {},
        }
    }
    Ok(read)
}

/// The argument of `spine` whose domain a mark's path enters, and the rest of
/// the path inside that domain.
///
/// # Specification
/// - ensures: for a path through `declared`'s thunk and `k` codomains into the
///   `k`-th arrow's domain, the `k`-th argument of `spine` and the steps after
///   it; absent for a path into the result or past the arguments.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`instantiation`].
/// - witness: `quantified::tests::a_helper_at_a_stage_takes_a_recursion_s_claim`
#[spec(ensures: |ret| match ret {
    Maybe::Present((argument, rest)) => spine.contains(&argument) && rest.len() < path.len(),
    Maybe::Absent(_) => true,
})]
fn argument_at<'path>(
    arena: &CoreArena,
    (declared, spine): (ValueTypeId, &[ValueId]),
    path: &'path [PlacedChild],
) -> Maybe<(ValueId, &'path [PlacedChild]), Unread>
{
    let Some((&first, mut rest)) = path.split_first()
    else {
        return Maybe::Absent(Unread::Plain);
    };
    let Some(&ValueType::Thunk(mut arrow)) = arena.value_type(declared)
    else {
        return Maybe::Absent(Unread::Plain);
    };
    if usize::from(first) != 0 {
        return Maybe::Absent(Unread::Plain);
    }
    let mut argument = 0_usize;
    loop {
        let Some(&(CompType::Arrow { codomain, .. } | CompType::Pi { codomain, .. })) =
            arena.comp_type(arrow)
        else {
            return Maybe::Absent(Unread::Plain);
        };
        let Some((&step, after)) = rest.split_first()
        else {
            return Maybe::Absent(Unread::Plain);
        };
        match usize::from(step) {
            0 => {
                return spine
                    .get(argument)
                    .map_or(Maybe::Absent(Unread::Plain), |&value| {
                        Maybe::Present((value, after))
                    });
            },
            1 => {
                argument = argument.saturating_add(1);
                arrow = codomain;
                rest = after;
            },
            _ => return Maybe::Absent(Unread::Plain),
        }
    }
}

/// The stage of the node `path` reaches in `found`, each staged node on the
/// way read through its base.
///
/// # Specification
/// - ensures: the stage of the reached node when it is staged; absent
///   otherwise, a path past a former's placed children included.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`instantiation`].
/// - witness: `quantified::tests::a_helper_at_a_stage_takes_a_recursion_s_claim`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_))
    || !path.is_empty()
    || matches!(arena.value_type(found), Some(ValueType::Staged { .. })))]
fn stage_at(
    arena: &CoreArena,
    found: ValueTypeId,
    path: &[PlacedChild],
) -> Maybe<Stage, Unread>
{
    let mut node = Part::Value(found);
    for &step in path {
        if let Part::Value(id) = node
            && let Some(&ValueType::Staged { base, .. }) = arena.value_type(id)
        {
            node = Part::Value(base);
        }
        let wanted = usize::from(step);
        let mut next = None;
        let mut position = 0_usize;
        placed(arena, node, |child| {
            if position == wanted {
                next = Some(child);
            }
            position = position.saturating_add(1);
        });
        let Some(next) = next
        else {
            return Maybe::Absent(Unread::Plain);
        };
        node = next;
    }
    match node {
        Part::Value(id) => match arena.value_type(id) {
            Some(&ValueType::Staged { stage, .. }) => Maybe::Present(stage),
            Some(_) | None => Maybe::Absent(Unread::Plain),
        },
        Part::Computation(_) => Maybe::Absent(Unread::Plain),
    }
}

#[cfg(test)]
mod tests;
