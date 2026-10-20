//! A definition quantified over stages: its declared type re-staged from its
//! [`StageSignature`].
//!
//! - **The definition's own body checks at minted stages.** [`minted`] mints
//!   one stage per binder, a bounded binder's below its bound's, and
//!   [`restaged`] refines each marked occurrence of the declared type there.
//! - **A call reads its stages off its arguments.** [`instantiation`] reads
//!   each binder's stage where a variable argument's type holds an occurrence
//!   the signature marks, the first such mark's; a binder no argument shows
//!   stands at no stage, so its occurrences stay plain. The arguments then
//!   check against the re-staged type by the stage order.
//! - **A mark reaches a data type.** Its path steps through the children the
//!   stage order places; a path that ends anywhere else is refused as
//!   [`KernelError::StageUnplaced`].

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::CompType;
use gandr_kernel_term::PlacedChild;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageBound;
use gandr_kernel_term::StageReach;
use gandr_kernel_term::StageSignature;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_shape::shape::Maybe;

use super::recursion::Part;
use super::recursion::placed;
use super::recursion::rebuild;
use crate::error::KernelError;
use crate::stage_order::StageOrder;
use crate::stage_order::below;

/// Why a binder stands at no stage.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Unread
{
    /// No argument shows it: its occurrences stay plain.
    Plain,
}

/// The constant a call's spine applies and its arguments, first applied
/// first, for the application of `head` to `last`.
///
/// # Specification
/// - ensures: for `head` a spine of applications over the force of a constant,
///   that constant and every argument of the spine, `last` the final one;
///   absent otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`instantiation`].
/// - witness: `tests::quantified::a_helper_at_a_stage_takes_a_recursion_s_claim`
#[spec(ensures: |ret| match ret { Maybe::Present((_, ref arguments)) => arguments.last() == Some(&last), Maybe::Absent(_) => true })]
pub(super) fn spine(
    arena: &TermArena,
    head: gandr_kernel_term::ComputationId,
    last: ValueId,
) -> Maybe<(gandr_kernel_term::ConstantIndex, Vec<ValueId>), Unread>
{
    let mut arguments = alloc::vec![last];
    let mut cursor = head;
    loop {
        match arena.computation(cursor) {
            Some(&gandr_kernel_term::Computation::Application(inner, argument)) => {
                arguments.push(argument);
                cursor = inner;
            },
            Some(&gandr_kernel_term::Computation::Force(forced)) => {
                return match arena.value(forced) {
                    Some(&Value::Constant(constant)) => {
                        arguments.reverse();
                        Maybe::Present((constant, arguments))
                    },
                    Some(_) | None => Maybe::Absent(Unread::Plain),
                };
            },
            Some(_) | None => return Maybe::Absent(Unread::Plain),
        }
    }
}

/// One stage per binder of `signature`, minted in `stages`: a root for an
/// unbounded binder, a child of its bound's stage for a bounded one.
///
/// # Specification
/// - requires: each bound names an earlier binder, as the format guarantees.
/// - ensures: one stage per binder, in binder order, each minted fresh.
/// - fails: [`KernelError::StageUnplaced`] for a bound naming no earlier
///   binder.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a helper typed at a stage checks its body there.
/// - witness: `tests::quantified::a_helper_at_a_stage_takes_a_recursion_s_claim`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |minted| minted.len() == signature.bounds().len()))]
pub(super) fn minted(
    stages: &mut StageOrder,
    signature: &StageSignature,
) -> Result<Vec<Maybe<Stage, Unread>>, KernelError>
{
    let mut minted: Vec<Maybe<Stage, Unread>> = Vec::with_capacity(signature.bounds().len());
    for &bound in signature.bounds() {
        let stage = match bound {
            StageBound::Unbounded => stages.mint_root(),
            StageBound::Below(binder) => match minted.get(usize::from(binder)) {
                Some(&Maybe::Present(Stage::At(parent))) => stages
                    .mint_below(parent)
                    .map_err(|_unminted| KernelError::StageUnplaced)?,
                Some(&Maybe::Present(Stage::Below { .. }) | &Maybe::Absent(_)) | None => {
                    return Err(KernelError::StageUnplaced);
                },
            },
        };
        minted.push(Maybe::Present(Stage::At(stage)));
    }
    Ok(minted)
}

/// `declared` with each occurrence `signature` marks refined at its binder's
/// stage in `at`, read through the mark's reach; an occurrence whose binder
/// stands at no stage stays plain.
///
/// # Specification
/// - requires: `at` holds one entry per binder of `signature`.
/// - ensures: `declared` itself when every binder stands at no stage; otherwise
///   the same type with each marked occurrence staged, the deepest marks first
///   so a shallower one wraps what a deeper one staged.
/// - fails: [`KernelError::StageUnplaced`] for a mark naming a binder past
///   `at`, a path stepping past a former's placed children, or one ending
///   anywhere but a data type.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a helper's function parameter and its argument move to
///   the stage, so a recursion's claim and its field check through it; a mark
///   on a unit type is refused.
/// - witness: `tests::quantified::a_helper_at_a_stage_takes_a_recursion_s_claim`
/// - witness: `tests::quantified::a_mark_reaching_no_data_type_is_refused`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&staged| arena.value_type(staged).is_some()))]
pub(super) fn restaged(
    arena: &mut TermArena,
    declared: ValueTypeId,
    signature: &StageSignature,
    at: &[Maybe<Stage, Unread>],
) -> Result<ValueTypeId, KernelError>
{
    let mut order: Vec<usize> = (0 .. signature.marks().len()).collect();
    order.sort_by_key(|&mark| {
        core::cmp::Reverse(
            signature
                .marks()
                .get(mark)
                .map_or(0, |mark| mark.path().len()),
        )
    });
    let mut root = Part::Value(declared);
    for mark in order
        .into_iter()
        .filter_map(|mark| signature.marks().get(mark))
    {
        let stage = match at.get(usize::from(mark.binder())) {
            Some(&Maybe::Present(stage)) => reached_through(stage, mark.reach()),
            Some(&Maybe::Absent(Unread::Plain)) => continue,
            None => return Err(KernelError::StageUnplaced),
        };
        root = wrapped(arena, root, mark.path(), stage)?;
    }
    match root {
        Part::Value(staged) => Ok(staged),
        Part::Computation(_) => Err(KernelError::ArenaFault),
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
/// - requires: nothing.
/// - ensures: the rebuilt root, of `root`'s kind.
/// - fails: [`KernelError::StageUnplaced`] for a step past a former's placed
///   children or an end anywhere but a data type.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`restaged`].
/// - witness: `tests::quantified::a_mark_reaching_no_data_type_is_refused`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |rebuilt| matches!((root, *rebuilt),
    (Part::Value(_), Part::Value(_)) | (Part::Computation(_), Part::Computation(_)))))]
fn wrapped(
    arena: &mut TermArena,
    root: Part,
    path: &[PlacedChild],
    stage: Stage,
) -> Result<Part, KernelError>
{
    let mut chain: Vec<(Part, Vec<Part>)> = Vec::with_capacity(path.len());
    let mut node = root;
    for &step in path {
        let mut children = Vec::new();
        placed(arena, node, |child| children.push(child));
        let Some(&next) = children.get(usize::from(step))
        else {
            return Err(KernelError::StageUnplaced);
        };
        chain.push((node, children));
        node = next;
    }
    let Part::Value(occurrence) = node
    else {
        return Err(KernelError::StageUnplaced);
    };
    if !matches!(arena.value_type(occurrence), Some(&ValueType::Data { .. })) {
        return Err(KernelError::StageUnplaced);
    }
    let mut rebuilt = Part::Value(arena.value_type_staged(occurrence, stage));
    for (&step, (parent, mut children)) in path.iter().rev().zip(chain.into_iter().rev()) {
        if let Some(child) = children.get_mut(usize::from(step)) {
            *child = rebuilt;
        }
        rebuilt = rebuild(arena, parent, &children)?;
    }
    Ok(rebuilt)
}

/// The stages a call of a definition declared `declared`, quantified over
/// `signature`, instantiates its binders at: each read where the first mark
/// of it lies in the domain of an argument of `spine` that is a variable of
/// `context` whose type holds a stage there.
///
/// # Specification
/// - requires: `spine` holds the call's arguments, first applied first;
///   `declared` is the thunk of the definition's arrows.
/// - ensures: one entry per binder: a stage read off an argument, a bounded
///   binder no argument shows read one step below its bound's stage, and no
///   stage otherwise. A mark at `<i` reads `i` off an argument bound `<s` at
///   `s`, and off nothing at a stage itself.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a recursion's claim handed to a helper typed at a stage
///   instantiates it at the recursion's own; a call on a value at no stage
///   instantiates nothing.
/// - witness: `tests::quantified::a_helper_at_a_stage_takes_a_recursion_s_claim`
/// - witness: `tests::quantified::a_call_at_no_stage_reads_its_result_plain`
#[spec(ensures: |ret| ret.len() == signature.bounds().len())]
pub(super) fn instantiation(
    arena: &TermArena,
    context: &[ValueTypeId],
    (declared, signature): (ValueTypeId, &StageSignature),
    spine: &[ValueId],
) -> Vec<Maybe<Stage, Unread>>
{
    let mut read: Vec<Maybe<Stage, Unread>> = signature
        .bounds()
        .iter()
        .map(|_| Maybe::Absent(Unread::Plain))
        .collect();
    for mark in signature.marks() {
        let binder = usize::from(mark.binder());
        if !matches!(read.get(binder), Some(&Maybe::Absent(_))) {
            continue;
        }
        let Maybe::Present((argument, inside)) = argument_at(arena, (declared, spine), mark.path())
        else {
            continue;
        };
        let Some(&Value::Variable(index)) = arena.value(argument)
        else {
            continue;
        };
        let Maybe::Present(found) = super::slot(context, index)
        else {
            continue;
        };
        let Maybe::Present(found) = stage_at(arena, found, inside)
        else {
            continue;
        };
        let instance = match (mark.reach(), found) {
            (StageReach::At, found) => Maybe::Present(found),
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
    }
    for (binder, &bound) in signature.bounds().iter().enumerate() {
        if let StageBound::Below(over) = bound
            && let Some(&Maybe::Absent(_)) = read.get(binder)
            && let Some(&Maybe::Present(stage)) = read.get(usize::from(over))
            && let Some(slot) = read.get_mut(binder)
        {
            *slot = Maybe::Present(below(stage));
        }
    }
    read
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
/// - witness: `tests::quantified::a_helper_at_a_stage_takes_a_recursion_s_claim`
#[spec(ensures: |ret| match ret {
    Maybe::Present((argument, rest)) => spine.contains(&argument) && rest.len() < path.len(),
    Maybe::Absent(_) => true,
})]
fn argument_at<'path>(
    arena: &TermArena,
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
/// - witness: `tests::quantified::a_helper_at_a_stage_takes_a_recursion_s_claim`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_))
    || !path.is_empty()
    || matches!(arena.value_type(found), Some(ValueType::Staged { .. })))]
fn stage_at(
    arena: &TermArena,
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
