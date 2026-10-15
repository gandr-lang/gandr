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
//! - **no loop arm**: `transport(P, loop, b) ≡ b`, decided by conversion as a
//!   rule's respect is decided, δ-free with the functions a family's endpoint
//!   calls read through their definitions, the right side spelled as the
//!   transport along the empty word so that an answer a definition names (`Base
//!   => loop`) meets its word on both sides;
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
//! naming the case, the cell and the two sides as built.
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

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::DataSignature;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::CellIndex;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FreeCells;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::build_side;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;

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
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
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
/// - fails: [`CheckRefusal::LoopNotRespected`] at `at` naming the first loop
///   whose sides do not convert, with the two sides as built, or naming the
///   first loop with the case itself as both sides for a motive that reads its
///   binder but is no returner; [`CheckRefusal::MachineInvariant`] for a type
///   of words the context does not hold, a point that is no closed term or a
///   case node the arena does not hold.
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
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::LoopNotRespected { at: refused, .. }) if refused == at) || matches!(ret, Err(CheckRefusal::MachineInvariant)))]
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
        });
    };
    let arities: Vec<FieldCount> = signature
        .constructors()
        .iter()
        .map(|fields| FieldCount::from(fields.len()))
        .collect();
    for owed in owed {
        let point = point(context, (datatype, &arities), owed.words)?;
        let arena = context.arena_mut();
        let word = letter(arena, owed);
        let words = arena.value_type_data(owed.words, Vec::new());
        let empty = arena.value_constructor(words, FreeCells::nil(), Vec::new());
        let carried = gandr_core_term::identity::answer_at(arena, point, motive, &branches);
        let transported = arena.computation_path_transport(family, word, carried);
        let stayed = arena.computation_path_transport(family, empty, carried);
        if context
            .definitions()
            .convert_rigidly(context.arena(), (transported, stayed))
            == Maybe::Present(())
        {
            continue;
        }
        return Err(CheckRefusal::LoopNotRespected {
            at,
            cell: owed.cell,
            left: transported,
            right: stayed,
        });
    }
    Ok(())
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
/// - witness: `native_formers::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
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
    let carried = gandr_core_term::identity::answer_at(arena, point, motive, &branches);
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
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
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
