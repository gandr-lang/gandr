//! Transport along a word, re-derived: the loops of a presented sort acting on
//! the families over it, as the replay's weak head reduction reads them.
//!
//! The engine's evaluator computes these rows natively (`gandr-core-nbe`'s
//! `eval::words`); the replay reaches the same words by reducts, each one step
//! of [`transport_word`] that the weak head loop fires where
//! [`crate::element_identity::transport_beta`] sticks:
//!
//! - along a path a definition names, its word: `tr(P, loop, v) ⇝ tr(P, ℓ ∷ ε,
//!   v)` when `loop`'s admitted body is a word, and likewise for an operand the
//!   empty-word and splicing rows read;
//! - along the empty word, the operand: `tr(P, ε, v) ⇝ return v`;
//! - along a longer word, letter by letter: `tr(P, ℓ ∷ u, v) ⇝ y ← tr(P, ℓ ∷ ε,
//!   v); tr(P↑, u↑, y)`;
//! - with a returned operand, the operand first, as an elimination meeting one
//!   runs it: `tr(P, w, ⟨c⟩) ⇝ y ← c; tr(P↑, w↑, y)`;
//! - along one letter in a path family `y. Path(C, l, r)` whose carrier never
//!   reads `y`, by conjugation (the book's lemma 2.11.2), `l(ℓ)⁻¹ · v · r(ℓ)`:
//!   with both endpoints fixed or moving the word is spliced at once; with an
//!   endpoint through a chain of calls the reduct binds the endpoint's image
//!   and transports along it in the family `z. Path(C, z, r(pt))` for the left
//!   one and `z. Path(C, l(pt), z)` for the right one, whose rows are again the
//!   fixed and moving ones.
//!
//! An endpoint's image of a letter is the loop arm the innermost function's
//! case carries for the letter's loop — inverted along the family `z.
//! Path(C, z, l(pt))` for an inverse letter, reflexivity for a case with no
//! loop arm — and each further function's image of that word, its `cong`: the
//! transport along it in `y. Path(C, l(pt), ⟨f y⟩)`. The functions are read
//! through the evaluator's admitted bodies, the reading cong fusion takes
//! ([`mod@crate::replay`]'s `Replay::fuse`): a loop obligation is decided
//! δ-free, and the image of a loop under a map out of the circle exists only in
//! its definition. A configuration no row reads sticks.
//!
//! **A named word is read silently.** `loop` is a constant whose body is the
//! word of its letter, and a δ-free obligation meets it rigid. The reduct
//! reads the body in place, as the evaluator does, rather than through an
//! unfolding the replay's dialogue records: the engine's dialogue under a
//! stuck transport names no unfolding the replay could read, and a
//! transport-elimination step in the trace alphabet would change the artifact
//! for one reading. The reading is confined to transport's path and operand
//! and to a constant whose body is a constructor of a type of words, so no
//! other definition unfolds by it. Reversal: a recorded trace position under
//! a transport's family, which would let the engine record the unfolding.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_term::CellIndex;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FreeCells;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::build_side;

use crate::element_identity::BinderUse;
use crate::element_identity::ElementTransport;
use crate::element_identity::Family;
use crate::element_identity::binder_use;
use crate::encoding::ContentTable;
use crate::path_universe::Reduction;
use crate::presented::Presentations;
use crate::replay::Unfoldable;
use crate::replay::Unfoldings;
use crate::rewrite::BinderDepth;
use crate::rewrite::RewriteOutcome;
use crate::rewrite::RewriteSupport;
use crate::rewrite::shift_computation;
use crate::rewrite::shift_value;
use crate::rewrite::shift_value_type;
use crate::rewrite::substitute_computation;
use crate::rewrite::substitute_value;
use crate::rewrite::substitute_value_type;

/// What a word's outermost node is.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Head
{
    /// The empty word, or reflexivity.
    Empty,
    /// A letter before the rest of the word.
    Letter
    {
        /// The letter's tag among its words' constructors.
        tag: ConstructorTag,
        /// The type of words the letter is a constructor of.
        words: ConstantIndex,
        /// The rest of the word.
        rest: ValueId,
    },
    /// Anything else: a variable, a stuck term, or a value of no type of
    /// words.
    Other,
}

/// How a path family's endpoint acts on a letter.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Action
{
    /// The endpoint never reads the family's binder: reflexivity.
    Fixed,
    /// The endpoint is the binder: the letter itself.
    Moving,
    /// The endpoint runs the binder through these definitions, innermost
    /// first.
    Through(Vec<ConstantIndex>),
}

/// The word a definition names, read through its admitted body: the cell's
/// own name, or any definition whose body is a letter or an empty word.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some(body)` exactly when `value` is a constant whose body
///   `unfoldings` holds, and that body is a constructor of a type of words;
///   `None` otherwise. The engine's evaluator reads the same names through the
///   same bodies.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `loop` answered at every point is read as its word and
///   conjugated to itself; were the name left rigid, the loop at every point
///   would be refused.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
#[spec(ensures: |ret| ret.is_none_or(|body| head(arena, unfoldings.presentations(), body) != Head::Other))]
fn named(
    arena: &TermArena,
    unfoldings: &Unfoldings,
    value: ValueId,
) -> Option<ValueId>
{
    let Some(&Value::Constant(constant)) = arena.value(value)
    else {
        return None;
    };
    let Unfoldable::Body(body) = unfoldings.unfolding(constant)
    else {
        return None;
    };
    let Some(&Value::Constructor { .. }) = arena.value(body)
    else {
        return None;
    };
    (head(arena, unfoldings.presentations(), body) != Head::Other).then_some(body)
}

/// Read a word's outermost node.
///
/// # Specification
/// - requires: nothing — unreadable ids read as [`Head::Other`].
/// - ensures: [`Head::Empty`] for reflexivity or a type of words' empty word,
///   [`Head::Letter`] for a letter of one with its one field, and
///   [`Head::Other`] otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — reflexivity, the empty word and the loop's letters are
///   told apart in every loop witness; a misread head would move or fix the
///   wrong word.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
/// - witness: `native_formers::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| match ret {
    Head::Letter { rest, .. } => arena.value(rest).is_some(),
    Head::Empty => matches!(arena.value(word), Some(&(Value::Here { .. } | Value::Constructor { .. }))),
    Head::Other => true,
})]
fn head(
    arena: &TermArena,
    presentations: &Presentations,
    word: ValueId,
) -> Head
{
    match arena.value(word) {
        | Some(&Value::Here { .. }) => Head::Empty,
        | Some(&Value::Constructor {
            datatype,
            tag,
            ref fields,
        }) => {
            let Some(&ValueType::Data {
                declaration: words, ..
            }) = arena.value_type(datatype)
            else {
                return Head::Other;
            };
            if presentations
                .presented(words)
                .and_then(crate::presented::PresentedType::cells)
                .is_none()
            {
                return Head::Other;
            }
            if tag == FreeCells::nil() {
                return Head::Empty;
            }
            match *fields.as_slice() {
                | [rest] => Head::Letter { tag, words, rest },
                | _ => Head::Other,
            }
        },
        | _ => Head::Other,
    }
}

/// The letters of a closed word, first to last, and its empty word.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some((letters, end))` exactly when following each letter's rest
///   from `word` reaches an empty word `end`; `None` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `loop` follows one field per iteration, never recursing.
/// - measure: the word's letters left, each a strict subterm.
///
/// # Adequacy
/// - hypothesis: L3 — the conjugated and mapped loop witnesses splice closed
///   words letter by letter.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|&(ref letters, end)| head(arena, presentations, end) == Head::Empty && letters.iter().all(|&letter| matches!(head(arena, presentations, letter), Head::Letter { .. }))))]
fn spelled(
    arena: &TermArena,
    presentations: &Presentations,
    word: ValueId,
) -> Option<(Vec<ValueId>, ValueId)>
{
    let mut letters = Vec::new();
    let mut at = word;
    loop {
        match head(arena, presentations, at) {
            | Head::Empty => return Some((letters, at)),
            | Head::Letter { rest, .. } => {
                letters.push(at);
                at = rest;
            },
            | Head::Other => return None,
        }
    }
}

/// The letter tag of the inverse of the letter tagged `tag`.
///
/// # Specification
/// - requires: `tag` is a letter or an inverse of a type of words.
/// - ensures: a letter's inverse for a letter, and the letter for an inverse;
///   the empty word's tag itself.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the flip once carries reflexivity to the loop twice only
///   when its image, the inverse letter, is inverted back to the loop.
/// - witness: `native_formers::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| FreeCells::generator(ret) == FreeCells::generator(tag) && (ret == tag) == (tag == FreeCells::nil()))]
fn inverse(tag: ConstructorTag) -> ConstructorTag
{
    let Some(generator) = FreeCells::generator(tag)
    else {
        return tag;
    };
    if usize::from(tag) % 2 == 1 {
        FreeCells::inverse(generator)
    }
    else {
        FreeCells::letter(generator)
    }
}

/// A letter's node copied onto another rest, its tag `tag`, or `None` for a
/// node that is no constructor.
///
/// # Specification
/// trivial.
fn relettered(
    arena: &mut TermArena,
    letter: ValueId,
    tag: ConstructorTag,
    rest: ValueId,
) -> Option<ValueId>
{
    let Some(&Value::Constructor { datatype, .. }) = arena.value(letter)
    else {
        return None;
    };
    Some(arena.value_constructor(datatype, tag, Vec::from([rest])))
}

/// The inverse of a closed word: its letters inverted, last first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a closed word `ℓ₁ ∷ … ∷ ℓₖ ∷ e`, `Some(ℓₖ⁻¹ ∷ … ∷ ℓ₁⁻¹ ∷ e)`,
///   an empty word itself; `None` for a word that is not closed.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` over the word's letters, not recursion.
/// - measure: the letters left.
///
/// # Adequacy
/// - hypothesis: L3 — conjugation at `Path(Circle, x, x)` inverts the loop on
///   the left; a word left uninverted would not cancel.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
#[spec(ensures: |ret| ret.is_none_or(|built| spelled(arena, presentations, built).is_some()))]
fn inverted(
    arena: &mut TermArena,
    presentations: &Presentations,
    word: ValueId,
) -> Option<ValueId>
{
    let (letters, end) = spelled(arena, presentations, word)?;
    let mut built = end;
    for letter in letters {
        let Some(&Value::Constructor { tag, .. }) = arena.value(letter)
        else {
            return None;
        };
        built = relettered(arena, letter, inverse(tag), built)?;
    }
    Some(built)
}

/// The word `first` then `second`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `second` when `first` is empty; `first` when `second` is empty;
///   `first`'s letters before `second` when `first` is closed; `None`
///   otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` over `first`'s letters, not recursion.
/// - measure: the letters left.
///
/// # Adequacy
/// - hypothesis: L3 — reflexivity at `Path(Circle, Base, x)` becomes the loop
///   only when the empty word is spliced before it.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
#[spec(ensures: |ret| ret.is_none_or(|built| arena.value(built).is_some()))]
fn concatenated(
    arena: &mut TermArena,
    presentations: &Presentations,
    (first, second): (ValueId, ValueId),
) -> Option<ValueId>
{
    if head(arena, presentations, first) == Head::Empty {
        return Some(second);
    }
    if head(arena, presentations, second) == Head::Empty {
        return Some(first);
    }
    let (letters, _end) = spelled(arena, presentations, first)?;
    let mut built = second;
    for &letter in letters.iter().rev() {
        let Some(&Value::Constructor { tag, .. }) = arena.value(letter)
        else {
            return None;
        };
        built = relettered(arena, letter, tag, built)?;
    }
    Some(built)
}

/// How an endpoint of a path family acts on a letter, or `None` when no row
/// reads it.
///
/// # Specification
/// - requires: `endpoint` is read under the family's one binder.
/// - ensures: [`Action::Moving`] for the binder; [`Action::Fixed`] for an
///   endpoint that ignores it; [`Action::Through`] for a chain of calls
///   [`calls`] reads; `None` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each witness family reads one action per endpoint: the
///   point fixed, `x` moving, and the flip's and the collapse's calls through a
///   chain; a misread action carries the answer elsewhere.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
/// - witness: `native_formers::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| match ret {
    Some(Action::Moving) => matches!(arena.value(endpoint), Some(&Value::Variable(_))),
    Some(Action::Through(ref chain)) => !chain.is_empty(),
    Some(Action::Fixed) | None => arena.value(endpoint).is_some(),
})]
fn action<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    endpoint: ValueId,
) -> Option<Action>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    if matches!(arena.value(endpoint), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
    {
        return Some(Action::Moving);
    }
    if binder_use(arena, table, memo, Family::Value(endpoint)) == BinderUse::Ignored {
        return Some(Action::Fixed);
    }
    calls(arena, endpoint).map(Action::Through)
}

/// The chain of definitions an endpoint runs the family's binder through,
/// innermost first.
///
/// # Specification
/// - requires: `endpoint` is read under the family's one binder.
/// - ensures: `Some(chain)` exactly when the endpoint is `⟨c⟩` for a call `c`
///   of the shape `force f a` whose argument `a` is the binder or `⟨c'⟩` for
///   such a call, or `x ← c'; force f x` for such a call `c'`, every function
///   `f` a constant; the constants innermost first.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `loop` descends one call per iteration, never recursing.
/// - measure: the endpoint's nodes left, each a strict subterm.
///
/// # Adequacy
/// - hypothesis: L3 — the flip applied twice reads as a chain of two calls and
///   the flip once as one, which the witness tells apart by their verdicts.
/// - witness: `native_formers::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|chain| !chain.is_empty() && matches!(arena.value(endpoint), Some(&Value::Returned(_)))))]
fn calls(
    arena: &TermArena,
    endpoint: ValueId,
) -> Option<Vec<ConstantIndex>>
{
    let Some(&Value::Returned(mut call)) = arena.value(endpoint)
    else {
        return None;
    };
    let bound = |argument: ValueId| matches!(arena.value(argument), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32));
    let applied = |call: ComputationId| match arena.computation(call) {
        | Some(&Computation::Application(head, argument)) => match arena.computation(head) {
            | Some(&Computation::Force(function)) => match arena.value(function) {
                | Some(&Value::Constant(constant)) => Some((constant, argument)),
                | _ => None,
            },
            | _ => None,
        },
        | _ => None,
    };
    let mut outermost_first = Vec::new();
    loop {
        if let Some(&Computation::Bind(first, then)) = arena.computation(call) {
            let (constant, argument) = applied(then)?;
            if !bound(argument) {
                return None;
            }
            outermost_first.push(constant);
            call = first;
            continue;
        }
        let (constant, argument) = applied(call)?;
        outermost_first.push(constant);
        if bound(argument) {
            outermost_first.reverse();
            return Some(outermost_first);
        }
        let Some(&Value::Returned(inner)) = arena.value(argument)
        else {
            return None;
        };
        call = inner;
    }
}

/// The point the type of words at `words` loops at, as a closed constructor
/// term of its sort.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the term the cells' point spells over `Data(sort, [])`, or `None`
///   for no type of words, or a point that does not build.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a loop arm is read at the circle's point `Base`, where
///   the flip's arm answers the inverse letter.
/// - witness: `native_formers::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| ret.is_none_or(|built| matches!(arena.value(built), Some(&Value::Constructor { .. }))))]
fn point(
    arena: &mut TermArena,
    presentations: &Presentations,
    words: ConstantIndex,
) -> Option<ValueId>
{
    let cells = presentations
        .presented(words)
        .and_then(crate::presented::PresentedType::cells)?;
    let arities = presentations.sort_arities(words)?;
    let sort = arena.value_type_data(cells.sort(), Vec::new());
    let mut open = false;
    let built = build_side(cells.point(), arities, |node, fields| match node {
        | RuleNode::Constructor(tag) => arena.value_constructor(sort, tag, fields),
        | RuleNode::Variable(_) => {
            open = true;
            arena.value_unit()
        },
    })
    .ok()?;
    (!open).then_some(built)
}

/// What a case over a looped sort carries for one of its loops.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Arm
{
    /// No loop arm: the case's image of every loop is reflexivity.
    Unwritten,
    /// The loop arm, its argument instantiated at the loop's point.
    Written(ComputationId),
}

/// The arm the definition `function`'s case carries for the loop of `cell` in
/// `words`, its argument instantiated at the loop's point, or `None` for a
/// definition that is no case over the sort.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as the summary, for a constant whose body `unfoldings` holds as
///   the thunk of a lambda over a data case on its own variable, the case's
///   arms after one per constructor of the words' sort taken in
///   [`Presentations::looping`]'s order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the flip's written arm and the collapse's unwritten one
///   decide the flip twice and the collapse admitted and the flip once refused.
/// - witness: `native_formers::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| ret.is_none_or(|arm| match arm { Arm::Written(written) => arena.computation(written).is_some(), Arm::Unwritten => matches!(unfoldings.unfolding(function), Unfoldable::Body(_)) }))]
fn loop_arm<M>(
    arena: &mut TermArena,
    (table, memo): (&mut ContentTable, &mut M),
    unfoldings: &Unfoldings,
    function: ConstantIndex,
    (words, cell): (ConstantIndex, CellIndex),
) -> Option<Arm>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let presentations = unfoldings.presentations();
    let Unfoldable::Body(body) = unfoldings.unfolding(function)
    else {
        return None;
    };
    let Some(&Value::Thunk(thunk)) = arena.value(body)
    else {
        return None;
    };
    let Some(&Computation::Lambda(case)) = arena.computation(thunk)
    else {
        return None;
    };
    let Some(&Computation::DataCase {
        scrutinee,
        ref branches,
        ..
    }) = arena.computation(case)
    else {
        return None;
    };
    if !matches!(arena.value(scrutinee), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
    {
        return None;
    }
    let count = branches.len();
    let cells = presentations
        .presented(words)
        .and_then(crate::presented::PresentedType::cells)?;
    let sort = cells.sort();
    let constructors = presentations.sort_arities(words)?.len();
    let mut total = 0_usize;
    let mut offset = None;
    for (looped, held) in presentations.looping(sort) {
        if looped == words {
            offset = Some(total.saturating_add(usize::from(cell)));
        }
        total = total.saturating_add(held.cells().len());
    }
    let offset = offset?;
    if count == constructors {
        return Some(Arm::Unwritten);
    }
    if Some(count) != constructors.checked_add(total) {
        return None;
    }
    let arm = *branches.get(constructors.checked_add(offset)?)?;
    let at = point(arena, presentations, words)?;
    Some(Arm::Written(substitute_computation(
        arena, table, memo, arm, at,
    )))
}

/// The family `z. Path(C, z, fixed)` or `z. Path(C, fixed, z)`, read `depth`
/// binders under where `carrier` and `fixed` stand, the moving endpoint on
/// `moving`'s side.
///
/// # Specification
/// trivial.
fn path_family<M>(
    arena: &mut TermArena,
    (table, memo): (&mut ContentTable, &mut M),
    (carrier, fixed): (ValueTypeId, ValueId),
    moving: gandr_kernel_term::Side,
    depth: BinderDepth,
) -> ValueTypeId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let amount = depth.deeper();
    let carrier = shift_value_type(arena, table, memo, carrier, BinderDepth::NONE, amount);
    let fixed = shift_value(arena, table, memo, fixed, BinderDepth::NONE, amount);
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    match moving {
        | gandr_kernel_term::Side::Left => arena.value_type_path(carrier, bound, fixed),
        | gandr_kernel_term::Side::Right => arena.value_type_path(carrier, fixed, bound),
    }
}

/// The image of the one-letter word `letter` under a chain of definitions, as
/// a computation returning the image word, or `None` when a definition is no
/// case over the sort.
///
/// # Specification
/// - requires: `letter` is a one-letter word; `(carrier, fixed)` a carrier and
///   a value standing where the transport does.
/// - ensures: the innermost function's loop arm for the letter — inverted along
///   `z. Path(C, z, fixed)` for an inverse letter, the letter's empty word for
///   a case with no loop arm — bound into each further function's cong of it,
///   the transport along it in `y. Path(C, fixed, ⟨f y⟩)` from `here(fixed)`.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` over the chain's later functions, not recursion.
/// - measure: the functions left.
///
/// # Adequacy
/// - hypothesis: L3 — the flip's image of the loop is its inverse and the
///   collapse's is reflexivity, and the flip twice binds the first image into
///   the second's cong; each verdict turns on the image.
/// - witness: `native_formers::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| ret.is_none_or(|built| arena.computation(built).is_some()) && (ret.is_none() || !chain.is_empty()))]
fn image<M>(
    arena: &mut TermArena,
    (table, memo): (&mut ContentTable, &mut M),
    unfoldings: &Unfoldings,
    chain: &[ConstantIndex],
    (letter, (carrier, fixed)): (ValueId, (ValueTypeId, ValueId)),
) -> Option<ComputationId>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let (&innermost, outer) = chain.split_first()?;
    let Head::Letter { tag, words, rest } = head(arena, unfoldings.presentations(), letter)
    else {
        return None;
    };
    let cell = FreeCells::generator(tag)?;
    let mut built = match loop_arm(arena, (table, memo), unfoldings, innermost, (words, cell))? {
        | Arm::Unwritten => arena.computation_return(rest),
        | Arm::Written(arm) if usize::from(tag) % 2 == 1 => arm,
        | Arm::Written(arm) => {
            let back = path_family(
                arena,
                (table, memo),
                (carrier, fixed),
                gandr_kernel_term::Side::Left,
                BinderDepth::from(1_u32),
            );
            let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
            let lifted = shift_value(
                arena,
                table,
                memo,
                fixed,
                BinderDepth::NONE,
                BinderDepth::from(1_u32),
            );
            let start = arena.value_here(lifted);
            let inverted = arena.computation_path_transport(back, bound, start);
            arena.computation_bind(arm, inverted)
        },
    };
    for &function in outer {
        let amount = BinderDepth::from(2_u32);
        let lifted_carrier =
            shift_value_type(arena, table, memo, carrier, BinderDepth::NONE, amount);
        let lifted_fixed = shift_value(arena, table, memo, fixed, BinderDepth::NONE, amount);
        let named = arena.value_constant(function);
        let forced = arena.computation_force(named);
        let moving = arena.value_variable(DeBruijnIndex::from(0_u32));
        let applied = arena.computation_application(forced, moving);
        let endpoint = arena.value_returned(applied);
        let family = arena.value_type_path(lifted_carrier, lifted_fixed, endpoint);
        let start_fixed = shift_value(
            arena,
            table,
            memo,
            fixed,
            BinderDepth::NONE,
            BinderDepth::from(1_u32),
        );
        let start = arena.value_here(start_fixed);
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let cong = arena.computation_path_transport(family, bound, start);
        built = arena.computation_bind(built, cong);
    }
    Some(built)
}

/// One transport step along a word, by the module's rows, where
/// [`crate::element_identity::transport_beta`] sticks.
///
/// # Specification
/// - requires: nothing; an ill-typed term reduces or sticks without panicking.
/// - ensures: `Reduced` with the transport along a named path's word; with the
///   operand returned along the empty word, or its named word reread; with the
///   first letter's transport bound into the rest's along a longer word; with a
///   returned operand run first; along one letter in a path family over a
///   carrier its binder never reads, with the spliced word returned when both
///   endpoints are fixed or moving and the words splice, or with the images of
///   the endpoints bound and the operand transported along them as the module
///   states; `Stuck` otherwise.
/// - provides: the replay's reading of transport along a word, the engine's
///   evaluator's rows as reducts.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the loop moves reflexivity to the loop in `y. Path(S,
///   Base, y)`, conjugates a loop to itself in `y. Path(S, y, y)`, and a map
///   with a loop arm carries the loop to the arm's image, as the loop
///   obligations the witnesses admit and refuse read them. The circle's corpus
///   rows replay through the same reducts in `gandr-surface-corpus`'s
///   `kernel_export::kernel_loop_elimination_readmission`.
/// - witness: `native_formers::native_formers::a_case_over_the_circle_owes_its_loop`
/// - witness: `native_formers::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| match ret {
    Reduction::Reduced(reduct) => arena.computation(reduct).is_some(),
    Reduction::Stuck => true,
})]
pub fn transport_word<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    unfoldings: &Unfoldings,
    term: ElementTransport,
) -> Reduction
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let ElementTransport {
        motive,
        path,
        value,
    } = term;
    let presentations = unfoldings.presentations();
    // A path a definition names reads as its word, as the evaluator reads it.
    if let Some(body) = named(arena, unfoldings, path) {
        return Reduction::Reduced(arena.computation_path_transport(motive, body, value));
    }
    let (tag, words, rest) = match head(arena, presentations, path) {
        | Head::Empty => (FreeCells::nil(), None, path),
        | Head::Letter { tag, words, rest } => (tag, Some(words), rest),
        | Head::Other => return Reduction::Stuck,
    };
    if words.is_some() && head(arena, presentations, rest) != Head::Empty {
        let Some(&Value::Constructor { datatype, .. }) = arena.value(path)
        else {
            return Reduction::Stuck;
        };
        let empty = arena.value_constructor(datatype, FreeCells::nil(), Vec::new());
        let first = arena.value_constructor(datatype, tag, Vec::from([empty]));
        let step = arena.computation_path_transport(motive, first, value);
        let one = BinderDepth::from(1_u32);
        let lifted = shift_value_type(arena, table, memo, motive, one, one);
        let onward = shift_value(arena, table, memo, rest, BinderDepth::NONE, one);
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let along = arena.computation_path_transport(lifted, onward, bound);
        return Reduction::Reduced(arena.computation_bind(step, along));
    }
    // A returned operand runs first, as an elimination meeting one does:
    // `tr(P, w, ⟨c⟩) ⇝ y ← c; tr(P↑, w↑, y)`.
    if let Some(&Value::Returned(operand)) = arena.value(value) {
        let one = BinderDepth::from(1_u32);
        let lifted = shift_value_type(arena, table, memo, motive, one, one);
        let onward = shift_value(arena, table, memo, path, BinderDepth::NONE, one);
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let along = arena.computation_path_transport(lifted, onward, bound);
        return Reduction::Reduced(arena.computation_bind(operand, along));
    }
    let Some(words) = words
    else {
        // Along the empty word an operand a definition names reads as its
        // word, as it does along a letter.
        if let Some(body) = named(arena, unfoldings, value) {
            return Reduction::Reduced(arena.computation_path_transport(motive, path, body));
        }
        return Reduction::Reduced(arena.computation_return(value));
    };
    let Some(&ValueType::Path {
        domain: carrier,
        left,
        right,
    }) = arena.value_type(motive)
    else {
        return Reduction::Stuck;
    };
    if binder_use(arena, table, memo, Family::Type(carrier)) != BinderUse::Ignored {
        return Reduction::Stuck;
    }
    let (Some(left_action), Some(right_action)) = (
        action(arena, table, memo, left),
        action(arena, table, memo, right),
    )
    else {
        return Reduction::Stuck;
    };
    let fixed_image = |action: &Action| match *action {
        | Action::Fixed => Some(rest),
        | Action::Moving => Some(path),
        | Action::Through(_) => None,
    };
    if let (Some(left_image), Some(right_image)) =
        (fixed_image(&left_action), fixed_image(&right_action))
    {
        if let Some(body) = named(arena, unfoldings, value) {
            return Reduction::Reduced(arena.computation_path_transport(motive, path, body));
        }
        let spliced = inverted(arena, presentations, left_image)
            .and_then(|back| concatenated(arena, presentations, (back, value)))
            .and_then(|before| concatenated(arena, presentations, (before, right_image)));
        return spliced.map_or(Reduction::Stuck, |moved| {
            Reduction::Reduced(arena.computation_return(moved))
        });
    }
    let Some(at) = point(arena, presentations, words)
    else {
        return Reduction::Stuck;
    };
    let base = substitute_value_type(arena, table, memo, carrier, at);
    let left_at = substitute_value(arena, table, memo, left, at);
    let right_at = substitute_value(arena, table, memo, right, at);
    let mut images = |action: &Action, fixed: ValueId| match *action {
        | Action::Fixed => Some(None),
        | Action::Moving => Some(Some(arena.computation_return(path))),
        | Action::Through(ref chain) => image(
            arena,
            (table, memo),
            unfoldings,
            chain,
            (path, (base, fixed)),
        )
        .map(Some),
    };
    let (Some(left_image), Some(right_image)) = (
        images(&left_action, left_at),
        images(&right_action, right_at),
    )
    else {
        return Reduction::Stuck;
    };
    // `w = l(ℓ)⁻¹ · v`, along the left image in `z. Path(C, z, r(pt))`.
    let before = left_image.map(|left_image| {
        let family = path_family(
            arena,
            (table, memo),
            (base, right_at),
            gandr_kernel_term::Side::Left,
            BinderDepth::from(1_u32),
        );
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let lifted = shift_value(
            arena,
            table,
            memo,
            value,
            BinderDepth::NONE,
            BinderDepth::from(1_u32),
        );
        let moved = arena.computation_path_transport(family, bound, lifted);
        arena.computation_bind(left_image, moved)
    });
    // `w · r(ℓ)`, along the right image in `z. Path(C, l(pt), z)`.
    let reduct = match (before, right_image) {
        | (Some(before), None) => before,
        | (None, Some(right_image)) => {
            let family = path_family(
                arena,
                (table, memo),
                (base, left_at),
                gandr_kernel_term::Side::Right,
                BinderDepth::from(1_u32),
            );
            let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
            let lifted = shift_value(
                arena,
                table,
                memo,
                value,
                BinderDepth::NONE,
                BinderDepth::from(1_u32),
            );
            let moved = arena.computation_path_transport(family, bound, lifted);
            arena.computation_bind(right_image, moved)
        },
        | (Some(before), Some(right_image)) => {
            let one = BinderDepth::from(1_u32);
            let lifted_image =
                shift_computation(arena, table, memo, right_image, BinderDepth::NONE, one);
            let family = path_family(
                arena,
                (table, memo),
                (base, left_at),
                gandr_kernel_term::Side::Right,
                BinderDepth::from(2_u32),
            );
            let image_bound = arena.value_variable(DeBruijnIndex::from(0_u32));
            let start = arena.value_variable(DeBruijnIndex::from(1_u32));
            let moved = arena.computation_path_transport(family, image_bound, start);
            let after = arena.computation_bind(lifted_image, moved);
            arena.computation_bind(before, after)
        },
        | (None, None) => return Reduction::Stuck,
    };
    Reduction::Reduced(reduct)
}
