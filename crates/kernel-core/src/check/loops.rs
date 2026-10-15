//! A case over a sort its words loop at respects each loop, re-derived.
//!
//! A case `case x { Base => b }` over the circle reads only the circle's
//! points; the loop at `Base` obliges it to carry its answer at the point
//! along the loop to itself, `transport(A, loop, b) ≡ b` in its motive `F A`,
//! as the book's dependent eliminator takes a path over the loop beside its
//! point. `b` is the value the point's branch returns, or the case at the
//! point where the branch computes ([`answer`]). A case with a loop arm per
//! loop supplies that path instead, the arm checked at `Path(A[pt],
//! ⟨transport(A, ℓ, b)⟩, b)`, or at `Path(A, b, b)` for a motive that ignores
//! its binder ([`arm_type`]), and owes nothing more. The conversion is the
//! kernel's own unfolding one, [`crate::replay::convert_unfolding`], under
//! which transport along a word computes (`crate::words`) and a definition
//! a side runs unfolds by the kernel's evaluator; the checker decides the same
//! obligation by its own unfolding conversion and the kernel re-derives it
//! with no trace, so no dialogue carries it and the artifact format is
//! unchanged.
//!
//! **Choice.** A missing loop arm is owed by conversion, a written one
//! supplies the dependent path, and a refusal of its own,
//! [`KernelError::LoopNotRespected`], names the cell. **Alternative.** A loop
//! arm required at every case over the sort, which makes every map out of
//! the circle spell the reflexivity a non-dependent case already has.
//! **Reversal.** A loop at a point of a parameterised family, whose point is
//! a term over the family's arguments and whose obligation is one per
//! instance.
//!
//! **Choice.** The obligation is decided by conversion with definitions
//! unfolding, as every other judgement "by conversion" is: a loop arm may
//! answer with a definition applied at the transported point (`mul`'s `loop
//! => selfloop(b)`), and its image is what that definition computes there.
//! The unfolding is bounded by the conversion's budget, and a run past it is
//! refused by its own name, [`KernelError::LoopUndecided`], never read as the
//! sides being apart. **Alternative.** The δ-free conversion, which compares
//! a definition by its name and so refuses every arm that calls one.
//! **Reversal.** An obligation whose unfolding diverges where a recorded
//! dialogue would close it takes the dialogue.
//!
//! The loops a case owes are the cells of every type of words looping in its
//! scrutinee's sort, by the words' admission position and then in written
//! order; a case's loop arms follow its constructors' branches in the same
//! order.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::CellIndex;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FreeCells;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::build_side;

use crate::element_identity::BinderUse;
use crate::encoding::ContentTable;
use crate::error::KernelError;
use crate::presented::Presentations;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplayDecline;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;
use crate::rewrite::substitute_comp_type;
use crate::rewrite::substitute_value_type;
use crate::support::LooseDepths;

/// One loop a case over a sort owes: its words and its cell.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Loop
{
    /// The type of words the loop is a letter of.
    words: ConstantIndex,
    /// The loop's position among its words' cells.
    cell: CellIndex,
}

/// The loops in the parameterless sort `datatype` names, in the order a
/// case's loop arms follow its constructors' branches.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one [`Loop`] per cell of every presented type of words looping in
///   the sort, words ascending by admission position and cells in written
///   order; none for a type with arguments or no sort.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's case owes its one loop.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
#[spec(ensures: |ret| ret.iter().all(|owed| presentations.presented(owed.words).is_some()))]
pub(super) fn loops(
    arena: &TermArena,
    presentations: &Presentations,
    datatype: ValueTypeId,
) -> Vec<Loop>
{
    let Some(&ValueType::Data {
        declaration: sort,
        ref arguments,
    }) = arena.value_type(datatype)
    else {
        return Vec::new();
    };
    if !arguments.is_empty() {
        return Vec::new();
    }
    let mut owed = Vec::new();
    for (words, cells) in presentations.looping(sort) {
        owed.extend((0 .. cells.cells().len()).map(|cell| Loop {
            words,
            cell: CellIndex::from(cell),
        }));
    }
    owed
}

/// The loop's point as a constructor term of `datatype`.
///
/// # Specification
/// - requires: `owed` is one of [`loops`]' answers over `datatype`.
/// - ensures: the closed term the words' cells' point spells.
/// - fails: [`KernelError::ArenaFault`] for words the presentations do not
///   hold, or a point that is open or does not build.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's point is `Base`, at which every loop
///   witness's answer is read; a wrong point would carry the wrong answer.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&built| matches!(arena.value(built), Some(&Value::Constructor { .. }))))]
fn point(
    arena: &mut TermArena,
    presentations: &Presentations,
    (datatype, owed): (ValueTypeId, Loop),
) -> Result<ValueId, KernelError>
{
    let cells = presentations
        .presented(owed.words)
        .and_then(crate::presented::PresentedType::cells)
        .ok_or(KernelError::ArenaFault)?;
    let arities: Vec<FieldCount> = presentations
        .sort_arities(owed.words)
        .ok_or(KernelError::ArenaFault)?
        .to_vec();
    let mut open = false;
    let built = build_side(cells.point(), &arities, |node, fields| match node {
        RuleNode::Constructor(tag) => arena.value_constructor(datatype, tag, fields),
        RuleNode::Variable(_) => {
            open = true;
            arena.value_unit()
        },
    })
    .map_err(|_fault| KernelError::ArenaFault)?;
    if open {
        return Err(KernelError::ArenaFault);
    }
    Ok(built)
}

/// The loop itself: its one-letter word.
///
/// # Specification
/// trivial.
fn letter(
    arena: &mut TermArena,
    owed: Loop,
) -> ValueId
{
    let words = arena.value_type_data(owed.words, Vec::new());
    let empty = arena.value_constructor(words, FreeCells::nil(), Vec::new());
    arena.value_constructor(words, FreeCells::letter(owed.cell), Vec::from([empty]))
}

/// The parts of a loop's obligation at a case.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Sides
{
    /// The answer at the loop's point carried along the loop:
    /// `transport(A, ℓ, ⟨b⟩)`.
    transported: ComputationId,
    /// The same answer carried along the empty word: `transport(A, ε, ⟨b⟩)`,
    /// which reads an answer a definition names as its word.
    stayed: ComputationId,
    /// The answer at the loop's point, `b`, as [`answer`] reads it.
    answered: ValueId,
}

/// The parts of a loop's obligation at a case.
///
/// # Specification
/// - requires: `case` is a data case whose motive is `F A`, `A` read under the
///   scrutinee's binder.
/// - ensures: [`Sides`] as its fields state, `b` the [`answer`] at the loop's
///   point, `ℓ` the loop's one-letter word and `ε` its words' empty word.
/// - fails: as [`point`], and [`KernelError::ArenaFault`] for a case node the
///   arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the sides of the circle's loop decide reflexivity at
///   `Path(Circle, Base, x)` refused and at `Path(Circle, x, x)` admitted.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| matches!(arena.computation(found.transported), Some(&Computation::PathTransport { .. })) && matches!(arena.computation(found.stayed), Some(&Computation::PathTransport { .. }))))]
fn sides(
    arena: &mut TermArena,
    presentations: &Presentations,
    (case, datatype): (ComputationId, ValueTypeId),
    (family, owed): (ValueTypeId, Loop),
) -> Result<Sides, KernelError>
{
    let Some(&Computation::DataCase {
        motive,
        ref branches,
        ..
    }) = arena.computation(case)
    else {
        return Err(KernelError::ArenaFault);
    };
    let branches = branches.clone();
    let at = point(arena, presentations, (datatype, owed))?;
    let carried = answer(arena, at, (motive, branches));
    let word = letter(arena, owed);
    let words = arena.value_type_data(owed.words, Vec::new());
    let empty = arena.value_constructor(words, FreeCells::nil(), Vec::new());
    let transported = arena.computation_path_transport(family, word, carried);
    let stayed = arena.computation_path_transport(family, empty, carried);
    Ok(Sides {
        transported,
        stayed,
        answered: carried,
    })
}

/// The case's answer at a loop's point, `b`: the value the point's branch
/// returns when the point is a constructor without fields, the case at the
/// point otherwise.
///
/// # Specification
/// - requires: `point` is a closed constructor term of the case's sort and
///   `branches` the case's branches, at `motive`.
/// - ensures: `v` exactly when `point` has no fields and the branch its tag
///   selects is `return v`, which stands in the case's own context; `⟨case
///   point { branches }⟩` otherwise, as the checker reads it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — reflexivity and the loop answered at the circle's point
///   are read as their words, so the loop at every point is respected.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
#[spec(ensures: |ret| arena.value(ret).is_some())]
fn answer(
    arena: &mut TermArena,
    point: ValueId,
    (motive, branches): (CompTypeId, Vec<ComputationId>),
) -> ValueId
{
    if let Some(&Value::Constructor {
        tag, ref fields, ..
    }) = arena.value(point)
        && fields.is_empty()
        && let Some(&branch) = branches.get(usize::from(tag))
        && let Some(&Computation::Return(value)) = arena.computation(branch)
    {
        return value;
    }
    let answered = arena.computation_data_case(point, motive, branches);
    arena.value_returned(answered)
}

/// The type a loop arm checks at: the path over the loop from the case's
/// answer at the point carried along it to that answer,
/// `F Path(A[pt], ⟨transport(A, ℓ, b)⟩, b)`, and `F Path(A, b, b)` for a
/// motive that ignores its binder.
///
/// # Specification
/// - requires: `case` is a data case over `datatype`, whose motive is `motive`.
/// - ensures: the returner of that path type, its parts as [`sides`] builds
///   them; the transport, the identity in a constant family, is left out when
///   the motive ignores its binder, as the checker leaves it out.
/// - fails: [`KernelError::LoopNotRespected`] naming the loop for a motive that
///   is no returner; as [`sides`] otherwise.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `invLooper`'s arm `loop => back(loop)` checks at
///   `Path(Circle, Base, Base)`, and a dependent arm at the wrong endpoints is
///   refused.
/// - witness: `native_formers::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&built| matches!(arena.comp_type(built), Some(&CompType::Returner(_)))))]
pub(super) fn arm_type(
    arena: &mut TermArena,
    presentations: &Presentations,
    (case, datatype, motive): (ComputationId, ValueTypeId, CompTypeId),
    owed: Loop,
) -> Result<CompTypeId, KernelError>
{
    let Some(&CompType::Returner(family)) = arena.comp_type(motive)
    else {
        return Err(KernelError::LoopNotRespected(owed.cell));
    };
    let constant = binder_use(arena, motive);
    let Sides {
        transported,
        answered,
        ..
    } = sides(arena, presentations, (case, datatype), (family, owed))?;
    let at = point(arena, presentations, (datatype, owed))?;
    let mut table = ContentTable::default();
    let fibre = substitute_value_type(arena, &mut table, &mut NullMemo, family, at);
    let left = if constant == BinderUse::Ignored {
        answered
    }
    else {
        arena.value_returned(transported)
    };
    let path = arena.value_type_path(fibre, left, answered);
    Ok(arena.comp_type_returner(path))
}

/// Decide that the case `case` over `datatype` respects every loop in its
/// sort: carried along the loop, its answer at the loop's point is itself.
///
/// # Specification
/// - requires: the case's branches have checked; it carries one branch per
///   constructor and no loop arm.
/// - ensures: `Ok(())` exactly when the motive ignores its binder, or, for
///   every loop of [`loops`] in order, [`sides`] convert under
///   [`crate::replay::convert_unfolding`] within [`ReplayBudget::DEFAULT`];
///   `arena` holds what it held on entry either way.
/// - fails: [`KernelError::LoopUndecided`] naming the first loop whose
///   conversion ran past its budget; [`KernelError::LoopNotRespected`] naming
///   the first loop whose sides do not convert otherwise, or the first loop for
///   a motive that reads its binder and is no returner;
///   [`KernelError::ArenaFault`] as [`sides`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop over the sort's finite loops, not recursion; each
///   conversion runs under its budget.
/// - measure: the loops left.
///
/// # Adequacy
/// - hypothesis: L3 — over the circle, `Base => here(Base)` at `Path(Circle,
///   Base, x)` is refused at its loop while the same arm at `Path(Circle, x,
///   x)` is admitted, as the checker refuses and admits them.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before
        && (ret.is_ok() || matches!(ret, Err(KernelError::LoopNotRespected(_) | KernelError::LoopUndecided(_) | KernelError::ArenaFault))),
)]
pub(super) fn respected(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    (case, datatype): (ComputationId, ValueTypeId),
) -> Result<(), KernelError>
{
    let presentations = unfoldings.presentations();
    let owed = loops(arena, presentations, datatype);
    let Some(&first) = owed.first()
    else {
        return Ok(());
    };
    let Some(&Computation::DataCase { motive, .. }) = arena.computation(case)
    else {
        return Err(KernelError::ArenaFault);
    };
    let watermark = arena.watermark();
    let decided = (|| {
        if binder_use(arena, motive) == BinderUse::Ignored {
            return Ok(());
        }
        let Some(&CompType::Returner(family)) = arena.comp_type(motive)
        else {
            return Err(KernelError::LoopNotRespected(first.cell));
        };
        for owed_loop in owed {
            let Sides {
                transported,
                stayed,
                ..
            } = sides(arena, presentations, (case, datatype), (family, owed_loop))?;
            let sides = ReplaySides::Computations(transported, stayed);
            match crate::replay::convert_unfolding(arena, unfoldings, sides, ReplayBudget::DEFAULT)
            {
                KernelVerdict::Convertible => {},
                KernelVerdict::Declined(ReplayDecline::Budget) => {
                    return Err(KernelError::LoopUndecided(owed_loop.cell));
                },
                KernelVerdict::NotConvertible | KernelVerdict::Declined(_) => {
                    return Err(KernelError::LoopNotRespected(owed_loop.cell));
                },
            }
        }
        Ok(())
    })();
    arena.truncate_to(watermark);
    decided
}

/// What a computation type under one binder does with it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`BinderUse::Ignored`] only when instantiating `motive` at a
///   variable past its reach leaves no variable at or past that reach, as
///   [`crate::element_identity::binder_use`] decides for a value type; a
///   saturated reach answers [`BinderUse::Read`].
/// - fails: never.
/// - panics: none.
/// - executable: none — the decision is the reach the instantiation leaves, so
///   a predicate would instantiate the motive again.
///
/// # Adequacy
/// - hypothesis: L3 — the collapse's motive `F Circle` ignores its binder and
///   owes no loop, while `F Path(Circle, x, x)` reads it and owes one.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
fn binder_use(
    arena: &mut TermArena,
    motive: CompTypeId,
) -> BinderUse
{
    let before = u32::from(LooseDepths::new().comp_type_reach(arena, motive));
    if before == 0 {
        return BinderUse::Ignored;
    }
    if before == u32::MAX {
        return BinderUse::Read;
    }
    let fresh = arena.value_variable(DeBruijnIndex::from(before));
    let mut table = ContentTable::default();
    let instantiated = substitute_comp_type(arena, &mut table, &mut NullMemo, motive, fresh);
    if u32::from(LooseDepths::new().comp_type_reach(arena, instantiated)) <= before {
        BinderUse::Ignored
    }
    else {
        BinderUse::Read
    }
}
