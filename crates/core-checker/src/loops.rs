//! A case over a sort its words loop at owes each loop.
//!
//! A data declaration's loop `loop : Base <-> Base` mints a type of words over
//! the sort, and `Path(Circle, Base, Base)` reads as those words. A case over
//! the sort itself, `case x { Base => b }`, reads only its points, so without
//! an obligation for the loop it would eliminate the circle as if it had no
//! loop: at the motive `Path(Circle, Base, x)` it would prove the circle
//! contractible. The book's dependent eliminator takes, beside `b : P(Base)`,
//! a path `ℓ : transport(P, loop, b) = b` per loop, and the case owes the same:
//!
//! - **no loop arm**: `transport(P, loop, b) ≡ b`, decided by conversion with
//!   every definition unfolding, so an arm answering with a definition at the
//!   point (`mul`'s `loop => selfloop(b)`) is read by what it computes there,
//!   the right side spelled as the transport along the empty word so that an
//!   answer a definition names (`Base => loop`) meets its word on both sides;
//! - **a loop arm per loop**: the arm `loop => e` is checked at the dependent
//!   path `Path(P(Base), transport(P, loop, b), b)` and nothing else is owed;
//!   for a non-dependent case, at `Path(B, b, b)`, where the arm chooses the
//!   loop's image (`invLooper`'s `loop => back(loop)`).
//!
//! `b` is the value the point's branch returns, or the case at the point,
//! its scrutinee replaced by the point's term, where the branch computes
//! ([`gandr_core_term::identity::answer_at`], which the lowering reads too):
//! either way the branch the point selects. A path type over a value that
//! spells the point reads as the words, so a word answers an arm at it.
//! A motive that ignores its binder is a constant family, whose
//! transport is the identity: such a case owes nothing, and with no loop arm
//! the loop's image under the map it computes is reflexivity at `b`. A case
//! that fails the obligation is refused [`CheckRefusal::LoopNotRespected`],
//! naming the case, the cell and the two sides as built; one whose conversion
//! runs past its budget is refused [`CheckRefusal::LoopUndecided`], naming the
//! case and the cell, never read as the sides being apart.
//!
//! The loops a case owes are read off the declarations whose cells loop in the
//! scrutinee's sort, in admission order and then in written order, and a loop
//! arm's position after the constructors' branches follows the same order
//! ([`loops`]).
//!
//! **Choice.** The owner's shape: a missing loop arm is owed by conversion,
//! as a rule's respect is, and a written one supplies the dependent path. A
//! refusal of its own rather than `RuleNotRespected`: a loop is a cell, not a
//! rule of the sort's presentation, and the diagnostic names the cell.
//! **Alternatives.** A loop arm required at every case over the sort, which
//! makes every map out of the circle spell the reflexivity a non-dependent case
//! already has; reading the case as a fold into a model with the loop as a
//! law, which needs a model the case does not name. **Reversal.** A loop at a
//! point of a parameterised family, whose words carry the family's arguments,
//! makes the point a term over them and the obligation one per instance.
//!
//! **Choice.** The obligation unfolds definitions, as every other judgement
//! by conversion does, and the kernel re-derives it by its own unfolding
//! conversion; the unfolding is bounded by the machine's fuel and budget.
//! **Alternative.** The δ-free stance a rule's respect is decided in, which
//! compares a definition by its name and so refuses every arm that calls one.
//! **Reversal.** An obligation whose unfolding diverges where a recorded
//! dialogue would close it takes the dialogue.
//!
//! **Choice.** A case whose answer at the loop's point is itself a case over
//! another variable of a looped sort, `case a { Base => case b { Base => … }
//! }`, owes each looped scrutinee its own obligation with the others held at
//! their constructors ([`scrutinees`]): the one over `a` is decided once per
//! constructor of `b`'s sort, `b` replaced by it, and the inner case owes its
//! own when it is checked. The square between the two loops, the 2-cell a
//! map out of the torus would owe, is not owed where the fibre is presented as
//! a set, the paths of a parameterless looped sort with no field
//! ([`presented_set`]): there every square commutes. Off a set the case is
//! refused [`CheckRefusal::LoopNotRespected`] with
//! [`crate::LoopRespect::NotPresentedSet`], naming the reason, never passed
//! silently. **Alternatives.** Owing the square everywhere, which needs the
//! 2-dimensional path algebra the tree does not have; refusing every nested
//! scrutinee, which refused `rotInv1`–`rotInv4` (#464). **Reversal.** A fibre
//! shown a set by some other means than its presentation, or a square the
//! tree computes, lifts the refusal off a set.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::DataSignature;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::TermId;
use gandr_core_term::shift_value_type;
use gandr_core_term::substitute_environment;
use gandr_kernel_term::CellIndex;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FreeCells;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::build_side;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;
use crate::LoopRespect;
use crate::code::converted;

/// One loop a case over a sort owes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Loop
{
    /// The type of words the loop is a letter of.
    pub words: ConstantIndex,
    /// The loop's position among the words' cells.
    pub cell: CellIndex,
}

/// The loops in the sort `datatype` names, in the order a case's loop arms
/// follow its constructors' branches: by the admission position of the words
/// they mint, then in written order.
///
/// # Specification
/// - requires: `datatype` is formed.
/// - ensures: one [`Loop`] per cell of every admitted type of words whose cells
///   loop in the parameterless data type `datatype` is, words ascending by
///   admission position and cells in written order; none for any other type.
///   Each type of words read is logged as consulted.
/// - provides: the loops a case over the sort owes, and the order its loop arms
///   take.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's case owes its one loop and a case over the
///   integers owes none.
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
#[spec(ensures: |ret| ret.iter().all(|owed| context.data_signatures().get(&owed.words).is_some_and(|signature| signature.presentation().cells().is_some())))]
pub fn loops(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
) -> Vec<Loop>
{
    let Some(&ValueType::Data {
        declaration: sort,
        ref arguments,
    }) = context.arena().value_type(datatype)
    else {
        return Vec::new();
    };
    if !arguments.is_empty() {
        return Vec::new();
    }
    let looped: Vec<(ConstantIndex, usize)> = context
        .data_signatures()
        .iter()
        .filter_map(|(&words, signature)| {
            let cells = signature.presentation().cells()?;
            (cells.sort() == sort).then_some((words, cells.cells().len()))
        })
        .collect();
    let mut owed = Vec::new();
    for (words, count) in looped {
        let _logged = context.consult_data(words);
        owed.extend((0 .. count).map(|cell| Loop {
            words,
            cell: CellIndex::from(cell),
        }));
    }
    owed
}

/// Decide that the case `at` over the sort `datatype` respects every loop in
/// it: carried along the loop, its answer at the loop's point is itself.
///
/// # Specification
/// - requires: the case's branches have checked, its scrutinee at `datatype`,
///   whose signature is `signature`.
/// - ensures: `Ok(())` exactly when the case carries a loop arm per loop of
///   [`loops`], whose types its branches' check decided; or the motive ignores
///   its binder; or, for every loop in [`loops`]' order, `transport(A, g, b)`
///   converts with `transport(A, ε, b)` under
///   [`crate::code::CodeDefinitions::convert_rigidly`], where the motive is `F
///   A`, `g` is the loop's one-letter word, `ε` its words' empty word and `b`
///   the answer at the loop's point ([`gandr_core_term::identity::answer_at`]).
///   Carried along the empty word, an answer a definition names reads as its
///   word — `loop` as the loop's letter — as it does carried along the loop, so
///   the two sides meet in the δ-free stance.
/// - fails: [`CheckRefusal::LoopUndecided`] at `at` naming the first loop whose
///   conversion runs past its budget; [`CheckRefusal::LoopNotRespected`] at
///   `at` naming the first loop whose sides do not convert otherwise, with the
///   two sides as built, or naming the first loop with the case itself as both
///   sides for a motive that reads its binder but is no returner;
///   [`CheckRefusal::MachineInvariant`] for a type of words the context does
///   not hold, a point that is no closed term or a case node the arena does not
///   hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop over the sort's finite loops, not recursion; each
///   conversion runs under the machine's fuel.
/// - measure: the loops left.
///
/// # Adequacy
/// - hypothesis: L3 — over the circle, `Base => here(Base)` at `Path(Circle,
///   Base, x)` is refused at its loop while the same arm at `Path(Circle, x,
///   x)` and `Base => loop` there are admitted, and a non-dependent case owes
///   nothing.
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::LoopNotRespected { at: refused, .. } | CheckRefusal::LoopUndecided { at: refused, .. }) if refused == at) || matches!(ret, Err(CheckRefusal::MachineInvariant)))]
pub fn respected(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    (datatype, signature): (ValueTypeId, &DataSignature),
) -> Result<(), CheckRefusal>
{
    let owed = loops(context, datatype);
    if owed.is_empty() {
        return Ok(());
    }
    let Some(&Computation::DataCase {
        motive,
        ref branches,
        ..
    }) = context.arena().computation(at)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    if branches.len() != signature.constructors().len() {
        return Ok(());
    }
    let branches = branches.clone();
    let arena = context.arena_mut();
    // A family that ignores its binder transports by the identity.
    if let Maybe::Present(_) = gandr_core_term::strengthen_comp_type(arena, motive) {
        return Ok(());
    }
    let Some(&CompType::Returner { result: family, .. }) = arena.comp_type(motive)
    else {
        let first = owed
            .first()
            .copied()
            .ok_or(CheckRefusal::MachineInvariant)?;
        return Err(CheckRefusal::LoopNotRespected {
            at,
            cell: first.cell,
            left: at,
            right: at,
            reason: LoopRespect::Apart,
        });
    };
    let arities: Vec<FieldCount> = signature
        .constructors()
        .iter()
        .map(|fields| FieldCount::from(fields.len()))
        .collect();
    // The substitution environment and the odometer over the held variables'
    // points, refilled per owed loop.
    let (mut environment, mut choice) = (Vec::new(), Vec::new());
    for owed in owed {
        let point = point(context, (datatype, &arities), owed.words)?;
        let arena = context.arena_mut();
        let word = letter(arena, owed);
        let words = arena.value_type_data(owed.words, Vec::new());
        let empty = arena.value_constructor(words, FreeCells::nil(), Vec::new());
        let carried =
            gandr_core_term::identity::answer_at(arena, point, motive, &branches, &arities);
        let transported = arena.computation_path_transport(family, word, carried);
        let stayed = arena.computation_path_transport(family, empty, carried);
        let held = scrutinees(context, (point, &branches))?;
        if held.is_empty() {
            owe(context, (at, owed.cell), (transported, stayed))?;
            continue;
        }
        // The answer is a case over other looped scrutinees: the loop is
        // owed with each held at each of its points, which is all a set's
        // paths owe; off a set the square between the loops is owed as well,
        // and no rule reads it.
        if presented_set(context, family)?.is_none() {
            return Err(CheckRefusal::LoopNotRespected {
                at,
                cell: owed.cell,
                left: transported,
                right: stayed,
                reason: LoopRespect::NotPresentedSet,
            });
        }
        let depth = usize::from(context.binders().depth(Zone::Intuitionistic));
        let arena = context.arena_mut();
        environment.clear();
        environment.reserve(depth);
        for index in 0 .. depth {
            let index = u32::try_from(index).map_err(|_overflow| CheckRefusal::MachineInvariant)?;
            environment
                .push(arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)));
        }
        // Each choice of a point per held scrutinee, as an odometer: the
        // first scrutinee's choice turns fastest.
        choice.clear();
        choice.resize(held.len(), 0_usize);
        loop {
            for (&chosen, variable) in choice.iter().zip(&held) {
                let slot = environment
                    .get_mut(variable.slot)
                    .ok_or(CheckRefusal::MachineInvariant)?;
                *slot = *variable
                    .points
                    .get(chosen)
                    .ok_or(CheckRefusal::MachineInvariant)?;
            }
            let arena = context.arena_mut();
            let (TermId::Computation(left), TermId::Computation(right)) = (
                substitute_environment(arena, TermId::Computation(transported), &environment),
                substitute_environment(arena, TermId::Computation(stayed), &environment),
            )
            else {
                return Err(CheckRefusal::MachineInvariant);
            };
            owe(context, (at, owed.cell), (left, right))?;
            let mut turned = false;
            for (chosen, variable) in choice.iter_mut().zip(&held) {
                *chosen = chosen.saturating_add(1);
                if *chosen < variable.points.len() {
                    turned = true;
                    break;
                }
                *chosen = 0;
            }
            if !turned {
                break;
            }
        }
    }
    Ok(())
}

/// Decide one instance of a loop's obligation: the answer carried along the
/// loop, `left`, against the answer carried along the empty word, `right`.
///
/// # Specification
/// - ensures: `Ok(())` exactly when the two convert under
///   [`crate::code::CodeDefinitions::convert_unfolding`].
/// - fails: [`CheckRefusal::LoopUndecided`] at `at` naming `cell` when the
///   conversion runs past its budget; [`CheckRefusal::LoopNotRespected`] at
///   `at` naming `cell` and the two sides, apart, otherwise.
/// - panics: none.
/// - executable: none — the conversion is the predicate, and restating it would
///   run it twice.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`respected`].
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
fn owe(
    context: &CheckingContext<'_>,
    (at, cell): (ComputationId, CellIndex),
    (left, right): (ComputationId, ComputationId),
) -> Result<(), CheckRefusal>
{
    match context
        .definitions()
        .convert_unfolding(context.arena(), (left, right))
    {
        Maybe::Present(()) => Ok(()),
        Maybe::Absent(converted::Absent::Undecided) => {
            Err(CheckRefusal::LoopUndecided { at, cell })
        },
        Maybe::Absent(converted::Absent::Apart) => Err(CheckRefusal::LoopNotRespected {
            at,
            cell,
            left,
            right,
            reason: LoopRespect::Apart,
        }),
    }
}

/// A looped scrutinee a case's answer at its point is itself a case over: the
/// variable's slot in the case's environment, and every point of its sort.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Held
{
    /// The variable's slot in the environment, innermost first.
    slot: usize,
    /// Each constructor of the variable's sort, in tag order.
    points: Vec<ValueId>,
}

/// The looped scrutinees a case's answer at `point` is itself a case over,
/// each with every point of its sort.
///
/// # Specification
/// - requires: `branches` are a case's branches, `point` a closed constructor
///   of its sort.
/// - ensures: the branch `point` selects, and in turn the branch each nested
///   case selects at its sort's first looped point, read while each is a case
///   over a variable of the case's context whose type is a parameterless sort
///   with loops and only constructors of no fields; one entry per such
///   variable, its index and its sort's constructors in tag order. Empty for a
///   point with fields or a branch that is no such case.
/// - fails: as [`crate::former::signature`] and [`point`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `loop` descends one nested case per turn into a strict
///   subterm, never recursing.
/// - measure: the answer's nodes left.
///
/// # Adequacy
/// - hypothesis: L3 — `rotInv1`'s answer at `Base` is a case over `b`, held at
///   `Base`; without it the obligation over `a` reads `b` free and sticks.
/// - witness: `tests::native_formers::a_nested_loop_obligation_holds_the_other_scrutinee_at_its_point_464`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.iter().all(|held| !held.points.is_empty())))]
fn scrutinees(
    context: &mut CheckingContext<'_>,
    (at, branches): (ValueId, &[ComputationId]),
) -> Result<Vec<Held>, CheckRefusal>
{
    let mut held: Vec<Held> = Vec::new();
    // The slots held so far, so a variable met again ends the descent in one
    // lookup.
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut arities: Vec<FieldCount> = Vec::new();
    let Some(&Value::Constructor {
        tag, ref fields, ..
    }) = context.arena().value(at)
    else {
        return Ok(held);
    };
    let (Some(&selected), true) = (branches.get(usize::from(tag)), fields.is_empty())
    else {
        return Ok(held);
    };
    let mut body = selected;
    loop {
        let Some(&Computation::DataCase { scrutinee, .. }) = context.arena().computation(body)
        else {
            return Ok(held);
        };
        let Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) = context.arena().value(scrutinee)
        else {
            return Ok(held);
        };
        let Ok(declared) = context.binders().declared(Zone::Intuitionistic, index)
        else {
            return Ok(held);
        };
        let sort = shift_value_type(context.arena_mut(), declared, Binders::past(index))
            .settle(context.arena_mut());
        let Some(first) = loops(context, sort).first().copied()
        else {
            return Ok(held);
        };
        let signature = crate::former::signature(context, sort)?;
        if signature
            .constructors()
            .iter()
            .any(|fields| !fields.is_empty())
        {
            return Ok(held);
        }
        // Every constructor of a set's sort takes no field.
        arities.clear();
        arities.resize(signature.constructors().len(), FieldCount::from(0_usize));
        let arena = context.arena_mut();
        let points = (0 .. arities.len())
            .map(|tag| arena.value_constructor(sort, ConstructorTag::from(tag), Vec::new()))
            .collect();
        let slot = usize::try_from(u32::from(index))
            .map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        if !seen.insert(slot) {
            return Ok(held);
        }
        held.push(Held { slot, points });
        let at = point(context, (sort, &arities), first.words)?;
        let Some(&Value::Constructor { tag, .. }) = context.arena().value(at)
        else {
            return Ok(held);
        };
        // The arena only grows, so the case read above still holds its
        // branches.
        let Some(&Computation::DataCase { ref branches, .. }) = context.arena().computation(body)
        else {
            return Ok(held);
        };
        let Some(&next) = branches.get(usize::from(tag))
        else {
            return Ok(held);
        };
        body = next;
    }
}

/// The sort whose paths a case's fibre is, when that sort presents them as a
/// set: a parameterless sort with loops whose constructors take no fields,
/// whose paths are its words.
///
/// # Specification
/// - requires: `family` is the motive's returner type under the scrutinee's
///   binder.
/// - ensures: `Some(D)` exactly when `family` is `Path(D, l, r)` for such a
///   `D`; `None` otherwise.
/// - fails: as [`crate::former::signature`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `rotInv1`'s fibre, a path over the circle, is a set; a
///   record holding a point of the circle is not, and its nested case is
///   refused naming the square.
/// - witness: `tests::native_formers::a_nested_loop_obligation_owes_its_square_off_a_set_464`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.is_none_or(|sort| matches!(context.arena().value_type(family), Some(&ValueType::Path { carrier, .. }) if carrier == sort))))]
fn presented_set(
    context: &mut CheckingContext<'_>,
    family: ValueTypeId,
) -> Result<Option<ValueTypeId>, CheckRefusal>
{
    let Some(&ValueType::Path { carrier, .. }) = context.arena().value_type(family)
    else {
        return Ok(None);
    };
    let Some(&ValueType::Data { ref arguments, .. }) = context.arena().value_type(carrier)
    else {
        return Ok(None);
    };
    if !arguments.is_empty() || loops(context, carrier).is_empty() {
        return Ok(None);
    }
    let signature = crate::former::signature(context, carrier)?;
    Ok(signature
        .constructors()
        .iter()
        .all(Vec::is_empty)
        .then_some(carrier))
}

/// The type the loop arm for `owed` of the case `at` over `datatype` checks
/// at: the path over the loop from the case's answer at the point carried
/// along it to that answer, `F Path(A[pt], ⟨transport(A, ℓ, b)⟩, b)`, and
/// `F Path(A, b, b)` for a motive that ignores its binder.
///
/// # Specification
/// - requires: `at` is a data case over `datatype`, whose signature is
///   `signature`, and whose motive has formed.
/// - ensures: the returner of that path type, `A` the motive's returner type
///   under the scrutinee's binder, `pt` the loop's point, `ℓ` its one-letter
///   word and `b` the answer at the point
///   ([`gandr_core_term::identity::answer_at`]), branches and loop arms alike;
///   the transport, the identity in a constant family, is left out when the
///   motive ignores its binder.
/// - fails: [`CheckRefusal::LoopNotRespected`] naming the loop, the case as
///   both sides, for a motive that is no returner; as [`point`] otherwise, and
///   [`CheckRefusal::MachineInvariant`] for a case node the arena does not
///   hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `invLooper`'s arm `loop => back(loop)` checks at
///   `Path(Circle, Base, Base)` read through its constant family, and a
///   dependent arm at the wrong endpoints is refused.
/// - witness: `tests::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::LoopNotRespected { at: refused, .. }) if refused == at) || matches!(ret, Err(CheckRefusal::MachineInvariant)))]
pub fn arm_type(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    (datatype, signature): (ValueTypeId, &DataSignature),
    owed: Loop,
) -> Result<gandr_core_term::CompTypeId, CheckRefusal>
{
    let Some(&Computation::DataCase {
        motive,
        ref branches,
        ..
    }) = context.arena().computation(at)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let branches = branches.clone();
    let Some(&CompType::Returner { result: family, .. }) = context.arena().comp_type(motive)
    else {
        return Err(CheckRefusal::LoopNotRespected {
            at,
            cell: owed.cell,
            left: at,
            right: at,
            reason: LoopRespect::Apart,
        });
    };
    let arities: Vec<FieldCount> = signature
        .constructors()
        .iter()
        .map(|fields| FieldCount::from(fields.len()))
        .collect();
    let point = point(context, (datatype, &arities), owed.words)?;
    let arena = context.arena_mut();
    let constant = matches!(
        gandr_core_term::strengthen_comp_type(arena, motive),
        Maybe::Present(_)
    );
    let carried = gandr_core_term::identity::answer_at(arena, point, motive, &branches, &arities);
    let left = if constant {
        carried
    }
    else {
        let word = letter(arena, owed);
        let transported = arena.computation_path_transport(family, word, carried);
        arena.value_returned(transported)
    };
    let fibre = gandr_core_term::instantiate_value_type(arena, family, point);
    let path = arena.value_type_path(fibre, left, carried);
    Ok(arena.comp_type_returner(path))
}

/// The point the cells of the type of words at `words` loop at, as a
/// constructor term of `datatype`, whose constructors take `arities` fields.
///
/// # Specification
/// - requires: `words` names an admitted type of words over `datatype`'s sort.
/// - ensures: the closed constructor term the cells' point spells, each node a
///   constructor of `datatype`.
/// - fails: [`CheckRefusal::MachineInvariant`] when the context holds no cells
///   at `words`, or the point is open or does not read against `arities`.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`respected`]: the circle's point is `Base`.
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&point| matches!(context.arena().value(point), Some(Value::Constructor { .. }))))]
pub fn point(
    context: &mut CheckingContext<'_>,
    (datatype, arities): (ValueTypeId, &[FieldCount]),
    words: ConstantIndex,
) -> Result<ValueId, CheckRefusal>
{
    let signature = context
        .data_signatures()
        .get(&words)
        .cloned()
        .ok_or(CheckRefusal::MachineInvariant)?;
    let cells = signature
        .presentation()
        .cells()
        .ok_or(CheckRefusal::MachineInvariant)?;
    let arena = context.arena_mut();
    let mut open = false;
    let point = build_side(cells.point(), arities, |node, fields| match node {
        RuleNode::Constructor(tag) => arena.value_constructor(datatype, tag, fields),
        RuleNode::Variable(_) => {
            open = true;
            arena.value_unit()
        },
    })
    .map_err(|_fault| CheckRefusal::MachineInvariant)?;
    if open {
        return Err(CheckRefusal::MachineInvariant);
    }
    Ok(point)
}

/// The point the type of words at `words` loops at, as a term of `carrier`,
/// when `carrier` is the sort its cells loop in.
///
/// # Specification
/// - requires: `carrier` is formed.
/// - ensures: `Some(point)` exactly when `carrier` is a parameterless data type
///   in scope and the words at `words` read the path type at `point` against
///   itself ([`CheckingContext::words`]), `point` the term [`point`] builds;
///   `None` otherwise.
/// - provides: the point a path type's endpoints are converted to where they
///   compute it without spelling it, so the path type reads as the words.
/// - fails: [`CheckRefusal::MachineInvariant`] when the words loop in the sort
///   at no closed point; as [`crate::former::signature`] for a carrier that is
///   not in scope.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's words loop at `Base`, so a path type over
///   the circle at `kept(Base)` reads as its words once both endpoints convert
///   with `Base`, in both checkers.
/// - witness: `tests::native_formers::a_path_whose_endpoints_compute_the_point_is_its_words_485`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |point| point.is_none_or(|point| matches!(context.arena().value(point), Some(Value::Constructor { .. })))))]
pub fn point_of(
    context: &mut CheckingContext<'_>,
    carrier: ValueTypeId,
    words: ConstantIndex,
) -> Result<Option<ValueId>, CheckRefusal>
{
    let Some(&ValueType::Data {
        declaration: sort,
        ref arguments,
    }) = context.arena().value_type(carrier)
    else {
        return Ok(None);
    };
    if !arguments.is_empty()
        || context
            .data_signatures()
            .get(&words)
            .and_then(|signature| signature.presentation().cells())
            .is_none_or(|cells| cells.sort() != sort)
    {
        return Ok(None);
    }
    let signature = crate::former::signature(context, carrier)?;
    let arities: Vec<FieldCount> = signature
        .constructors()
        .iter()
        .map(|fields| FieldCount::from(fields.len()))
        .collect();
    let point = point(context, (carrier, &arities), words)?;
    Ok((context.words(carrier, (point, point))? == Some(words)).then_some(point))
}

/// The word of `owed`'s one letter: the loop itself, as a path at its point.
///
/// # Specification
/// trivial.
pub fn letter(
    arena: &mut gandr_core_term::CoreArena,
    owed: Loop,
) -> ValueId
{
    let words = arena.value_type_data(owed.words, Vec::new());
    let empty = arena.value_constructor(words, FreeCells::nil(), Vec::new());
    arena.value_constructor(words, FreeCells::letter(owed.cell), Vec::from([empty]))
}
