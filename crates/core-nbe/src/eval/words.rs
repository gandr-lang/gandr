//! Transport along a word: the loops of a presented sort acting on the
//! families over it.
//!
//! A path at a looped point is a word over the loops and their inverses, and
//! transport along it is transport along each letter in turn, first letter
//! first: `tr(P, ℓ ∷ u, v) = tr(P, u, tr(P, ℓ, v))`, the empty word moving
//! nothing. Along one letter `ℓ`, the book's lemma 2.11.2 computes a path
//! family `y. Path(C, l(y), r(y))` whose carrier `C` never reads `y` by
//! conjugation: `tr(P, ℓ, v) = l(ℓ)⁻¹ · v · r(ℓ)`, where an endpoint acts on
//! the letter by what it is —
//!
//! - **fixed**, never reading `y`: reflexivity, the empty word;
//! - **moving**, `y` itself: the letter;
//! - **through a chain of calls**, `⟨f(… g(y))⟩`: each function's image of the
//!   word its inner call answered, innermost first, a function's image of a
//!   letter the loop arm its case over the sort carries for the letter's loop,
//!   inverted for an inverse letter, and reflexivity for a case with no loop
//!   arm.
//!
//! The three pieces splice as words: a piece that is reflexivity drops out,
//! and the others concatenate when every piece but the last is a closed word.
//! Cancellations are left to conversion, which reads a word by its normal form.
//! A family of any other shape, an endpoint read otherwise, a function whose
//! body is no case over the sort, or a piece that does not splice keeps the
//! transport where the evaluator had it, so it sticks as it did.
//!
//! **`then` appends on its first word.** In the singleton family `y. Path(C,
//! a, y)` — `p then q` is `p` transported along `q` there — a path no row
//! above reads, a parameter or a word that does not splice, still moves the
//! empty word and a letter-headed word, as the free model's append computes
//! on its first argument: `tr(P, q, ε) = q` and `tr(P, q, ℓ ∷ p) = ℓ ∷ tr(P,
//! q, p)`, every letter looping at the one point. When the rest's transport
//! sticks, the letter stands before it held as the value it returns, as `ℓ ∷
//! ⟨c⟩` reads its field, so the composite and the word written with the
//! composite inside are one value. The rows are list append's on words; the
//! alternative, a row on the path (`tr(P, q ∷ ℓ, v)`), would need the path
//! closed, which a parameter is not. Reversal: a presented sort whose letters
//! join two points, where the rest's family starts at the letter's end.
//!
//! **The functions are read through their definitions in every stance.** The
//! case a constant's body holds is read as the scope reads it manifest,
//! whatever the run's constant stance, the transparency scope still sealing
//! what it seals — the reading cong fusion gives its chain's functions
//! (`crate::fusion`). A loop obligation is decided δ-free, and the image of a
//! loop under `invLooper` exists only in its definition. A loop arm that reads
//! the case's own binder is no image this reading takes: the arm stands at the
//! loop's point, and a run binding the binder to anything else could read a
//! different term. Alternatives: a recorded unfolding per function, which needs
//! a trace position under a transport's family, as fusion's reading found;
//! substituting the point for the binder, which needs the sort's type as a
//! term the run's arena holds. Reversal: a corpus row whose loop arm reads its
//! scrutinee.
//!
//! **A map's image of a loop is its case's loop arm**, the arm that case owes
//! the loop or chooses for it, and a case with none sends the loop to
//! reflexivity, as the checker reads a non-dependent case. Alternative: a loop
//! arm required at every case over the sort, which would leave no image to
//! default. Reversal: a loop at a point of a parameterised family, whose arm
//! would read the family's arguments and whose image is one per instance.
//!
//! **A named word is read silently.** `loop` is a constant whose body is the
//! word of its letter, and a δ-free obligation meets it rigid: transport's
//! path, and the operand the empty-word and splicing rows read, are reread
//! through the body when the constant's body is a constructor of a type of
//! words ([`named`]), and no other definition unfolds by it. The run records
//! no unfolding for the reading, since the kernel's replay has no trace
//! position under a stuck transport's family to read one at, and the kernel
//! reads the same bodies by the same rule (`gandr-kernel-core`'s `words`).

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_kernel_term::CellIndex;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FreeCells;
use gandr_kernel_term::Side;

use super::EvalFault;
use super::Machine;
use super::Task;
use crate::arena::DomainArena;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::ValueClosureId;
use crate::closure::Call;
use crate::closure::CompBody;
use crate::closure::Conjugating;
use crate::closure::Environment;
use crate::closure::Orientation;
use crate::closure::ValueBody;
use crate::domain::CompTermFace;
use crate::domain::DomainValue;
use crate::domain::TermFace;
use crate::free::CoreTerm;
use crate::free::FreeFault;
use crate::free::FreeIndices;
use crate::free::Membership;

/// Whether a word transport took a step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Moved
{
    /// The step's tasks or result are on the machine.
    Stepped,
    /// No rule of the module applies; the machine is as it was.
    Unmoved,
}

/// How a path family's endpoint acts on a letter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Action
{
    /// The endpoint never reads the family's binder: reflexivity.
    Fixed,
    /// The endpoint is the binder: the letter itself.
    Moving,
    /// The endpoint runs the binder through a chain of calls.
    Through,
}

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
        rest: DomainValueId,
    },
    /// Anything else: a neutral, or a value of no type of words.
    Other,
}

/// Map a free-index fault into the evaluator's vocabulary.
///
/// # Specification
/// trivial.
fn free_fault(fault: FreeFault) -> EvalFault
{
    match fault {
        FreeFault::Dangling => EvalFault::DanglingTerm,
        FreeFault::MachineInvariant => EvalFault::MachineInvariant,
    }
}

/// The type of words a constructor's classifier closure names, when it names
/// one.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok(Some(w))` exactly when the closure suspends the nominal head
///   of a declaration `w` the run presents with cells; `Ok(None)` otherwise.
/// - fails: [`EvalFault::Domain`] for a closure the arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the loop's letters are read as words of the presented
///   type while the circle's point is not; a misread classifier leaves every
///   transport stuck.
/// - witness: `eval::words::tests::transport_along_the_loop_moves_the_endpoint`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| found.is_none_or(|words| machine.definitions.presented(words).and_then(crate::presented::Presented::cells).is_some())))]
fn words_of(
    core: &CoreArena,
    domain: &DomainArena,
    machine: &Machine<'_>,
    datatype: ValueClosureId,
) -> Result<Option<ConstantIndex>, EvalFault>
{
    let closure = domain
        .value_closure(datatype)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
    let ValueBody::ValueType(classifier) = closure.body()
    else {
        return Ok(None);
    };
    let Some(&ValueType::Data { declaration, .. }) = core.value_type(classifier)
    else {
        return Ok(None);
    };
    Ok(machine
        .definitions
        .presented(declaration)
        .and_then(crate::presented::Presented::cells)
        .map(|_| declaration))
}

/// The word a definition names, its body read through the definition: the
/// cell's own name, or any definition whose body is a letter or an empty word.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok(Some(body))` exactly when `value` is a neutral headed by a
///   constant with an empty spine whose body [`super::Definitions::definition`]
///   reads, and that body is a constructor of a declaration the run presents
///   with cells; `Ok(None)` otherwise. The kernel's replay reads the same names
///   through the same bodies.
/// - fails: [`EvalFault::Domain`] for a node the arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — transport along the constant `loop` moves the endpoint as
///   transport along its word does; were the name left neutral, the transport
///   would stick.
/// - witness: `eval::words::tests::transport_along_the_loop_moves_the_endpoint`
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| found.is_none_or(|body| matches!(core.value(body), Some(&Value::Constructor { .. })))))]
pub(super) fn named(
    core: &CoreArena,
    domain: &DomainArena,
    machine: &Machine<'_>,
    value: DomainValueId,
) -> Result<Option<ValueId>, EvalFault>
{
    let dangling = EvalFault::Domain(DomainFault::Dangling);
    let DomainValue::Neutral { neutral, .. } = *domain.value(value).ok_or(dangling)?
    else {
        return Ok(None);
    };
    let held = domain.neutral(neutral).ok_or(dangling)?;
    let crate::domain::NeutralHead::Constant(constant) = held.head()
    else {
        return Ok(None);
    };
    if !held.spine().is_empty() {
        return Ok(None);
    }
    let Some(body) = machine.definitions.definition(constant)
    else {
        return Ok(None);
    };
    let Some(&Value::Constructor { datatype, .. }) = core.value(body)
    else {
        return Ok(None);
    };
    let Some(&ValueType::Data { declaration, .. }) = core.value_type(datatype)
    else {
        return Ok(None);
    };
    Ok(machine
        .definitions
        .presented(declaration)
        .and_then(crate::presented::Presented::cells)
        .map(|_| body))
}

/// Run a transport again with one of its sides read through the definition
/// that names it: the path's when `side` is the left, the operand's when it
/// is the right.
///
/// # Specification
/// - requires: `body` is what [`named`] read for that side.
/// - ensures: the body's evaluation, the other side and the transport queued in
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the transport along `loop` is reread along its word in
///   both witnesses; queueing the sides in the other order would transport the
///   operand along it.
/// - witness: `eval::words::tests::transport_along_the_loop_moves_the_endpoint`
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
#[spec(
    captures: entry_tasks = machine.tasks.len(),
    ensures: machine.tasks.len() == entry_tasks.saturating_add(3_usize),
)]
pub(super) fn reread(
    machine: &mut Machine<'_>,
    motive: ValueClosureId,
    (path, value): (DomainValueId, DomainValueId),
    (side, body): (Side, ValueId),
)
{
    machine.tasks.push(Task::PathTransport(motive));
    let evaluated = Task::Value {
        term: body,
        env: Machine::root_env(),
    };
    match side {
        Side::Left => {
            machine.tasks.push(Task::Supply(value));
            machine.tasks.push(evaluated);
        },
        Side::Right => {
            machine.tasks.push(evaluated);
            machine.tasks.push(Task::Supply(path));
        },
    }
}

/// Read a word's outermost node.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Head::Empty`] for reflexivity or a type of words' empty word,
///   [`Head::Letter`] for a letter of one with its one field, and
///   [`Head::Other`] for anything else.
/// - fails: [`EvalFault::Domain`] for a node, a span or a closure the arena
///   does not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — reflexivity, the empty word, the loop's letter and its
///   inverse are each read in the witnesses; a misread head moves or fixes the
///   wrong word.
/// - witness: `eval::words::tests::transport_along_the_loop_moves_the_endpoint`
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|read| match *read {
    Head::Letter { rest, .. } => domain.value(rest).is_some(),
    Head::Empty | Head::Other => domain.value(word).is_some(),
}))]
fn head(
    core: &CoreArena,
    domain: &DomainArena,
    machine: &Machine<'_>,
    word: DomainValueId,
) -> Result<Head, EvalFault>
{
    let dangling = EvalFault::Domain(DomainFault::Dangling);
    match *domain.value(word).ok_or(dangling)? {
        DomainValue::Here { .. } => Ok(Head::Empty),
        DomainValue::Constructor {
            datatype,
            tag,
            fields,
            ..
        } => {
            let Some(words) = words_of(core, domain, machine, datatype)?
            else {
                return Ok(Head::Other);
            };
            if tag == FreeCells::nil() {
                return Ok(Head::Empty);
            }
            match *domain.fields(fields).map_err(EvalFault::Domain)? {
                [rest] => Ok(Head::Letter { tag, words, rest }),
                _ => Ok(Head::Other),
            }
        },
        DomainValue::Record { .. }
        | DomainValue::PathCertificate { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Flow { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Tuple { .. }
        | DomainValue::ListNil { .. }
        | DomainValue::ListCons { .. }
        | DomainValue::Injection { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. }
        | DomainValue::Neutral { .. }
        | DomainValue::Code { .. }
        | DomainValue::StaticLambda { .. } => Ok(Head::Other),
    }
}

/// The closed word `word` spells, its letters first to last and its empty
/// word, or `None` for a word that ends in no empty word.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some((letters, end))` exactly when following each letter's rest
///   from `word` reaches an empty word `end`, every node passed a letter listed
///   with its own id; `None` otherwise.
/// - fails: as [`head`].
/// - panics: none.
///
/// # Errors
/// As [`head`].
///
/// # Termination
/// - reason: the `loop` follows one field per iteration, never recursing.
/// - measure: the word's letters left, each a strict subterm.
///
/// # Adequacy
/// - hypothesis: L3 — conjugation spells the loop, its inverse and the empty
///   word in turn; a word misspelt splices to the wrong loop.
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| found.as_ref().is_none_or(|&(ref letters, end)| domain.value(end).is_some() && letters.iter().all(|&letter| domain.value(letter).is_some()))))]
fn spelled(
    core: &CoreArena,
    domain: &DomainArena,
    machine: &Machine<'_>,
    word: DomainValueId,
) -> Result<Option<(Vec<DomainValueId>, DomainValueId)>, EvalFault>
{
    let mut letters = Vec::new();
    let mut at = word;
    loop {
        match head(core, domain, machine, at)? {
            Head::Empty => return Ok(Some((letters, at))),
            Head::Letter { rest, .. } => {
                letters.push(at);
                at = rest;
            },
            Head::Other => return Ok(None),
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
/// - hypothesis: L3 — conjugation by the loop fixes its inverse only when the
///   left endpoint's letter is inverted.
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
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

/// A letter's node copied onto another rest, its tag `tag`.
///
/// # Specification
/// - requires: `letter` is a letter node of a type of words.
/// - ensures: a constructor of the letter's own classifier, tagged `tag`, whose
///   one field is `rest`.
/// - fails: [`EvalFault::Domain`] for a node the arena does not hold;
///   [`EvalFault::MachineInvariant`] for a node that is no constructor.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — every spliced word in the witnesses is rebuilt letter by
///   letter; a letter copied onto the wrong rest drops the rest of the word.
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|&built| matches!(domain.value(built), Some(&DomainValue::Constructor { tag: written, .. }) if written == tag)))]
pub(super) fn relettered(
    domain: &mut DomainArena,
    letter: DomainValueId,
    tag: ConstructorTag,
    rest: DomainValueId,
) -> Result<DomainValueId, EvalFault>
{
    let Some(&DomainValue::Constructor { datatype, .. }) = domain.value(letter)
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let fields = domain.hold_fields([rest]);
    Ok(domain.value_constructor(datatype, tag, fields, TermFace::Reduced))
}

/// The inverse of a closed word: its letters inverted, last first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some(word)` for an empty word; for a closed word `ℓ₁ ∷ … ∷ ℓₖ ∷
///   e`, `Some(ℓₖ⁻¹ ∷ … ∷ ℓ₁⁻¹ ∷ e)`; `None` for a word that is not closed.
/// - fails: as [`head`].
/// - panics: none.
///
/// # Errors
/// As [`head`].
///
/// # Termination
/// - reason: one `for` over the word's letters, not recursion.
/// - measure: the letters left.
///
/// # Adequacy
/// - hypothesis: L3 — conjugation inverts the left endpoint's image of the
///   loop; an uninverted word moves the loop to a word of three letters.
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| found.is_none_or(|built| domain.value(built).is_some())))]
fn inverted(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &Machine<'_>,
    word: DomainValueId,
) -> Result<Option<DomainValueId>, EvalFault>
{
    let Some((letters, end)) = spelled(core, domain, machine, word)?
    else {
        return Ok(None);
    };
    let mut built = end;
    for letter in letters {
        let Some(&DomainValue::Constructor { tag, .. }) = domain.value(letter)
        else {
            return Err(EvalFault::MachineInvariant);
        };
        built = relettered(domain, letter, inverse(tag), built)?;
    }
    Ok(Some(built))
}

/// The word `first` then `second`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `second` when `first` is empty; `first` when `second` is empty;
///   `first`'s letters before `second` when `first` is closed; `None`
///   otherwise.
/// - fails: as [`head`].
/// - panics: none.
///
/// # Errors
/// As [`head`].
///
/// # Termination
/// - reason: one `for` over `first`'s letters, not recursion.
/// - measure: the letters left.
///
/// # Adequacy
/// - hypothesis: L3 — reflexivity at the point carried along the loop is the
///   loop only when the empty word is spliced before it.
/// - witness: `eval::words::tests::transport_along_the_loop_moves_the_endpoint`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| found.is_none_or(|built| domain.value(built).is_some())))]
fn concatenated(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &Machine<'_>,
    (first, second): (DomainValueId, DomainValueId),
) -> Result<Option<DomainValueId>, EvalFault>
{
    if head(core, domain, machine, first)? == Head::Empty {
        return Ok(Some(second));
    }
    if head(core, domain, machine, second)? == Head::Empty {
        return Ok(Some(first));
    }
    let Some((letters, _end)) = spelled(core, domain, machine, first)?
    else {
        return Ok(None);
    };
    let mut built = second;
    for &letter in letters.iter().rev() {
        let Some(&DomainValue::Constructor { tag, .. }) = domain.value(letter)
        else {
            return Err(EvalFault::MachineInvariant);
        };
        built = relettered(domain, letter, tag, built)?;
    }
    Ok(Some(built))
}

/// The path `left⁻¹ · value · right`, or `None` when the pieces do not splice.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the concatenation of `left`'s inverse, `value` and `right` by
///   [`inverted`] and [`concatenated`], when each step answers.
/// - fails: as [`head`].
/// - panics: none.
///
/// # Errors
/// As [`head`].
///
/// # Adequacy
/// - hypothesis: L3 — conjugation fixes the loop, its inverse and the empty
///   word, and does not move the loop to the empty word.
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| found.is_none_or(|built| domain.value(built).is_some())))]
fn spliced(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &Machine<'_>,
    (left, value, right): (DomainValueId, DomainValueId, DomainValueId),
) -> Result<Option<DomainValueId>, EvalFault>
{
    let Some(back) = inverted(core, domain, machine, left)?
    else {
        return Ok(None);
    };
    let Some(before) = concatenated(core, domain, machine, (back, value))?
    else {
        return Ok(None);
    };
    concatenated(core, domain, machine, (before, right))
}

/// Whether a term reads a binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// Some index at or below the binder is free in the term.
    Reads,
    /// None is.
    Ignores,
}

/// Whether `term` reads the variable `index` of the intuitionistic zone, or
/// any below it.
///
/// # Specification
/// - requires: `term` lives in `core`.
/// - ensures: [`Reading::Reads`] exactly when some intuitionistic index at or
///   below `index` is free in `term`.
/// - fails: the free-index walk's fault.
/// - panics: none.
/// - executable: none — the free-index walk is the only reading of the clause,
///   so a predicate would restate the body.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the point is a fixed endpoint and the flip's call reads
///   the binder; were the call read as fixed, cong would not reach the arm.
/// - witness: `eval::words::tests::transport_along_the_loop_moves_the_endpoint`
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
fn reads_through(
    core: &CoreArena,
    term: CoreTerm,
    index: DeBruijnIndex,
) -> Result<Reading, EvalFault>
{
    let mut free = FreeIndices::default();
    let read = free.of(core, term).map_err(free_fault)?;
    if read
        .intuitionistic()
        .least()
        .is_some_and(|least| least <= index)
    {
        Ok(Reading::Reads)
    }
    else {
        Ok(Reading::Ignores)
    }
}

/// How an endpoint of a path family acts on a letter, or `None` when no rule
/// reads it.
///
/// # Specification
/// - requires: `endpoint` is read under the family's one binder.
/// - ensures: [`Action::Moving`] for the binder; [`Action::Fixed`] for an
///   endpoint that never reads it; [`Action::Through`] for a chain of calls
///   [`calls`] reads; `None` otherwise.
/// - fails: the free-index walk's fault.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the point is fixed, `y` moving and the flip's call a
///   chain in the witnesses' families; a misread action carries the operand
///   elsewhere.
/// - witness: `eval::words::tests::transport_along_the_loop_moves_the_endpoint`
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| match *found {
    Some(Action::Moving) => matches!(core.value(endpoint), Some(&Value::Variable { .. })),
    Some(Action::Through) => calls(core, endpoint).is_some(),
    Some(Action::Fixed) | None => core.value(endpoint).is_some(),
}))]
fn action(
    core: &CoreArena,
    endpoint: ValueId,
) -> Result<Option<Action>, EvalFault>
{
    let bound = DeBruijnIndex::from(0_u32);
    if matches!(core.value(endpoint), Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if index == bound)
    {
        return Ok(Some(Action::Moving));
    }
    if reads_through(core, CoreTerm::Value(endpoint), bound)? == Reading::Ignores {
        return Ok(Some(Action::Fixed));
    }
    Ok(calls(core, endpoint).map(|_| Action::Through))
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
/// - hypothesis: L3 — `flip(y)` reads as a chain of one call, whose loop arm
///   gives cong its image.
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|chain| !chain.is_empty() && matches!(core.value(endpoint), Some(&Value::Returned(_)))))]
fn calls(
    core: &CoreArena,
    endpoint: ValueId,
) -> Option<Vec<ConstantIndex>>
{
    let Some(&Value::Returned(mut call)) = core.value(endpoint)
    else {
        return None;
    };
    let bound = |argument: ValueId| matches!(core.value(argument), Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if u32::from(index) == 0);
    let applied = |call: ComputationId| match core.computation(call) {
        Some(&Computation::Application(head, argument)) => match core.computation(head) {
            Some(&Computation::Force(function)) => match core.value(function) {
                Some(&Value::Constant(constant)) => Some((constant, argument)),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    };
    let mut outermost_first = Vec::new();
    loop {
        if let Some(&Computation::Bind(first, then)) = core.computation(call) {
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
        let Some(&Value::Returned(inner)) = core.value(argument)
        else {
            return None;
        };
        call = inner;
    }
}

/// Read a definition as a case over its argument: the thunk of a lambda whose
/// body is a data case on the lambda's own variable.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the case, for a constant whose manifest body
///   ([`super::Definitions::definition`]) is such a thunk; `None` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `flip`'s manifest body is read as its case, and without
///   the sort's constructor count the arm after it is not found.
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
#[spec(ensures: |ret| ret.is_none_or(|case| matches!(core.computation(case), Some(&Computation::DataCase { .. }))))]
fn cased(
    core: &CoreArena,
    machine: &Machine<'_>,
    function: ConstantIndex,
) -> Option<ComputationId>
{
    let body = machine.definitions.definition(function)?;
    let Some(&Value::Thunk(thunk)) = core.value(body)
    else {
        return None;
    };
    let Some(&Computation::Lambda(body)) = core.computation(thunk)
    else {
        return None;
    };
    let Some(&Computation::DataCase { scrutinee, .. }) = core.computation(body)
    else {
        return None;
    };
    matches!(core.value(scrutinee), Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if u32::from(index) == 0)
        .then_some(body)
}

/// What a case over a looped sort carries for one of its loops.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Arm
{
    /// No loop arm: the case's image of every loop is reflexivity.
    Unwritten,
    /// The loop arm, which reads no binder its case's argument is.
    Written(ComputationId),
}

/// The arm a case carries for a letter's loop, or `None` when the case is
/// over no sort the letter's words loop in, or its arm reads the argument.
///
/// # Specification
/// - requires: `case` is a data case in `core`; `words` an admitted type of
///   words whose `cell`'s loop the image is asked of.
/// - ensures: as the summary, a case's arms after one per constructor of the
///   words' sort taken in [`super::Definitions::looping`]'s order.
/// - fails: the free-index walk's fault.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `flip`'s arm after its one constructor branch is the
///   loop's image, and without the sort's constructor count no arm is read.
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| found.is_none_or(|arm| match arm { Arm::Written(written) => core.computation(written).is_some(), Arm::Unwritten => matches!(core.computation(case), Some(&Computation::DataCase { .. })) })))]
fn loop_arm(
    core: &CoreArena,
    machine: &Machine<'_>,
    case: ComputationId,
    (words, cell): (ConstantIndex, CellIndex),
) -> Result<Option<Arm>, EvalFault>
{
    let Some(computation) = core.computation(case)
    else {
        return Ok(None);
    };
    let Computation::DataCase { ref branches, .. } = *computation
    else {
        return Ok(None);
    };
    let Some(cells) = machine
        .definitions
        .presented(words)
        .and_then(crate::presented::Presented::cells)
    else {
        return Ok(None);
    };
    let sort = cells.sort();
    let Some(constructors) = machine.definitions.constructors(sort)
    else {
        return Ok(None);
    };
    let constructors = usize::from(constructors);
    let mut total = 0_usize;
    let mut offset = None;
    for (looped, held) in machine.definitions.looping(sort) {
        if looped == words {
            offset = Some(total.saturating_add(usize::from(cell)));
        }
        total = total.saturating_add(held.cells().len());
    }
    let Some(offset) = offset
    else {
        return Ok(None);
    };
    if branches.len() == constructors {
        return Ok(Some(Arm::Unwritten));
    }
    if Some(branches.len()) != constructors.checked_add(total) {
        return Ok(None);
    }
    let Some(&arm) = constructors
        .checked_add(offset)
        .and_then(|position| branches.get(position))
    else {
        return Ok(None);
    };
    if reads_through(core, CoreTerm::Computation(arm), DeBruijnIndex::from(0_u32))?
        == Reading::Reads
    {
        return Ok(None);
    }
    Ok(Some(Arm::Written(arm)))
}

/// Take one transport step along a word, when a rule of the module applies.
///
/// # Specification
/// - requires: `path` is the evaluated path and `value` the evaluated operand
///   of a transport in `motive`, both already taken off the value stack.
/// - ensures: [`Moved::Stepped`] with the result returned or the step's tasks
///   pushed — the operand unchanged along the empty word; the first letter's
///   transport with the rest's bound after it along a longer word; a one-letter
///   word in a path family conjugating as the module states — and
///   [`Moved::Unmoved`] with the machine unchanged otherwise.
/// - fails: as [`head`], and the free-index walk's fault.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the loop transports reflexivity to itself in `y.
///   Path(Circle, Base, y)`, conjugates the loop to itself in `y. Path(Circle,
///   y, y)`, a word of two letters takes two steps, and a map with a loop arm
///   carries the loop to the arm's image.
/// - witness: `eval::words::tests::transport_along_the_loop_moves_the_endpoint`
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
#[spec(
    captures: [tasks = machine.tasks.len(), comps = machine.comps.len()],
    ensures: |ret| ret.is_err() || matches!(ret, Ok(Moved::Unmoved)) && machine.tasks.len() == tasks && machine.comps.len() == comps
        || matches!(ret, Ok(Moved::Stepped)) && (machine.tasks.len() > tasks || machine.comps.len() > comps),
)]
pub(super) fn transport(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    motive: ValueClosureId,
    (path, value): (DomainValueId, DomainValueId),
) -> Result<Moved, EvalFault>
{
    let (tag, rest) = match head(core, domain, machine, path)? {
        Head::Empty => {
            // Along the empty word an operand a definition names reads as its
            // word, as it does along a letter.
            if let Some(body) = named(core, domain, machine, value)? {
                reread(machine, motive, (path, value), (Side::Right, body));
                return Ok(Moved::Stepped);
            }
            machine
                .comps
                .push(domain.comp_return(value, CompTermFace::Reduced));
            return Ok(Moved::Stepped);
        },
        Head::Letter { tag, rest, .. } => (tag, rest),
        Head::Other => return Ok(Moved::Unmoved),
    };
    if head(core, domain, machine, rest)? != Head::Empty {
        let Some(&DomainValue::Constructor { datatype, .. }) = domain.value(path)
        else {
            return Err(EvalFault::MachineInvariant);
        };
        let none = domain.hold_fields([]);
        let empty = domain.value_constructor(datatype, FreeCells::nil(), none, TermFace::Reduced);
        let first = relettered(domain, path, tag, empty)?;
        let onward = domain.native_continuation(CompBody::AlongWord { motive, rest });
        machine.tasks.push(Task::BindClosure(onward));
        machine.tasks.push(Task::PathTransport(motive));
        machine.values.extend([first, value]);
        return Ok(Moved::Stepped);
    }
    let Some((left, right)) = family_actions(core, domain, motive)?
    else {
        return Ok(Moved::Unmoved);
    };
    let static_image = |action: Action| match action {
        Action::Fixed => Some(rest),
        Action::Moving => Some(path),
        Action::Through => None,
    };
    match (static_image(left), static_image(right)) {
        (Some(left), Some(right)) => {
            if let Some(body) = named(core, domain, machine, value)? {
                reread(machine, motive, (path, value), (Side::Right, body));
                return Ok(Moved::Stepped);
            }
            let Some(moved) = spliced(core, domain, machine, (left, value, right))?
            else {
                return Ok(Moved::Unmoved);
            };
            machine
                .comps
                .push(domain.comp_return(moved, CompTermFace::Reduced));
            Ok(Moved::Stepped)
        },
        (None, _) => {
            let onward = domain.native_continuation(CompBody::Conjugated {
                motive,
                along: path,
                value,
                stage: Conjugating::Left,
            });
            machine.tasks.push(Task::BindClosure(onward));
            map(core, domain, machine, Mapping {
                motive,
                side: Side::Left,
                call: Call::from(0_usize),
                rest: path,
                mapped: rest,
                orientation: Orientation::Forward,
            })?;
            Ok(Moved::Stepped)
        },
        (Some(left), None) => {
            let onward = domain.native_continuation(CompBody::Conjugated {
                motive,
                along: path,
                value,
                stage: Conjugating::Right(left),
            });
            machine.tasks.push(Task::BindClosure(onward));
            map(core, domain, machine, Mapping {
                motive,
                side: Side::Right,
                call: Call::from(0_usize),
                rest: path,
                mapped: rest,
                orientation: Orientation::Forward,
            })?;
            Ok(Moved::Stepped)
        },
    }
}

/// Take one transport step in a singleton family by the word moved, where the
/// word moved along reads no further: `then` appends on its first word.
///
/// # Specification
/// - requires: `path` is the evaluated path and `value` the evaluated operand
///   of a transport in `motive`, both already taken off the value stack.
/// - ensures: in a family `y. Path(C, a, y)` whose carrier and left endpoint
///   never read `y`, [`Moved::Stepped`] with `path` returned when `value` is
///   the empty word — `tr(P, q, here(a)) ⇝ q` — with the transport of the rest
///   bound into `w. return ℓ ∷ w` when `value` is `ℓ ∷ p` — `tr(P, q, ℓ ∷ p) ⇝
///   ℓ ∷ tr(P, q, p)`, a letter looping at the one point — and with the operand
///   reread when a definition names it; [`Moved::Unmoved`] with the machine
///   unchanged otherwise.
/// - fails: as [`head`] and [`family_actions`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the empty word moved along a path parameter is that
///   parameter, and a letter before a parameter moved along another is the
///   letter before the parameters' composite, as the free model's append
///   computes on its first word; a row on the path instead leaves both stuck.
/// - witness: `eval::words::tests::a_word_appends_on_its_first_word`
#[spec(
    captures: [tasks = machine.tasks.len(), comps = machine.comps.len()],
    ensures: |ret| ret.is_err() || matches!(ret, Ok(Moved::Unmoved)) && machine.tasks.len() == tasks && machine.comps.len() == comps
        || matches!(ret, Ok(Moved::Stepped)) && (machine.tasks.len() > tasks || machine.comps.len() > comps),
)]
pub(super) fn appended(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    motive: ValueClosureId,
    (path, value): (DomainValueId, DomainValueId),
) -> Result<Moved, EvalFault>
{
    let Some((Action::Fixed, Action::Moving)) = family_actions(core, domain, motive)?
    else {
        return Ok(Moved::Unmoved);
    };
    match head(core, domain, machine, value)? {
        Head::Empty => {
            machine
                .comps
                .push(domain.comp_return(path, CompTermFace::Reduced));
        },
        Head::Letter { rest, .. } => {
            let onward = domain.native_continuation(CompBody::Prefixed(value));
            machine.tasks.push(Task::BindClosure(onward));
            machine.tasks.push(Task::PathTransport(motive));
            machine.values.extend([path, rest]);
        },
        Head::Other => {
            let Some(body) = named(core, domain, machine, value)?
            else {
                return Ok(Moved::Unmoved);
            };
            reread(machine, motive, (path, value), (Side::Right, body));
        },
    }
    Ok(Moved::Stepped)
}

/// How a path family's two endpoints act on a letter, or `None` for a family
/// that is no path type over a carrier its binder never reads, or an endpoint
/// no rule reads.
///
/// # Specification
/// - requires: `motive` suspends a value type under one binder.
/// - ensures: the [`action`] of the left then the right endpoint.
/// - fails: [`EvalFault::Domain`] for a closure the arena does not hold;
///   [`EvalFault::MachineInvariant`] for a closure holding no value type; the
///   free-index walk's fault.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — each witness family's endpoints are read as a pair, fixed
///   and moving, moving and moving, fixed and through a call; swapping them
///   conjugates on the wrong side.
/// - witness: `eval::words::tests::transport_along_the_loop_moves_the_endpoint`
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| found.is_none() || domain.value_closure(motive).is_some_and(|closure| matches!(closure.body(), ValueBody::ValueType(family) if matches!(core.value_type(family), Some(&ValueType::Path { .. }))))))]
fn family_actions(
    core: &CoreArena,
    domain: &DomainArena,
    motive: ValueClosureId,
) -> Result<Option<(Action, Action)>, EvalFault>
{
    let closure = domain
        .value_closure(motive)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
    let ValueBody::ValueType(family) = closure.body()
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let Some(&ValueType::Path {
        carrier,
        left,
        right,
    }) = core.value_type(family)
    else {
        return Ok(None);
    };
    let mut free = FreeIndices::default();
    if free
        .of_type(core, carrier)
        .map_err(free_fault)?
        .intuitionistic()
        .holds(DeBruijnIndex::from(0_u32))
        == Membership::Held
    {
        return Ok(None);
    }
    let (Some(left), Some(right)) = (action(core, left)?, action(core, right)?)
    else {
        return Ok(None);
    };
    Ok(Some((left, right)))
}

/// The state of mapping a word through one endpoint's chain of calls.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Mapping
{
    /// The path family, closed over its environment.
    pub motive: ValueClosureId,
    /// The endpoint whose chain maps the word.
    pub side: Side,
    /// The function of the chain mapping the word now.
    pub call: Call,
    /// The letters still to map.
    pub rest: DomainValueId,
    /// The image of the letters mapped so far.
    pub mapped: DomainValueId,
    /// Whether the letter whose image binds next is inverted.
    pub orientation: Orientation,
}

/// Map the rest of a word through the endpoint's chain of calls: skip each
/// letter whose image is reflexivity, and run the first loop arm an image
/// needs, binding it into the next mapping step; once a call has read its
/// whole word, its image is the next call's word, and when the chain is
/// through that word is the image returned.
///
/// # Specification
/// - requires: `state.mapped` is a closed word or empty; the endpoint at
///   `state.side` of `state.motive`'s family reads as a chain of calls.
/// - ensures: on success, either the image returned or one loop arm's run
///   pushed with a [`CompBody::Mapping`] continuation bound after it.
/// - fails: [`EvalFault::TransportedNonPath`] for a word, a function or an
///   image no rule maps; as [`head`] otherwise.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `loop` consumes one letter or one call per iteration, never
///   recursing.
/// - measure: the calls left, then the letters left.
///
/// # Adequacy
/// - hypothesis: L3 — the flip's chain maps the loop to its arm's answer, the
///   inverse, and not to the loop; skipping the arm returns the loop unmapped.
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
#[spec(
    captures: [entry_comps = machine.comps.len(), entry_tasks = machine.tasks.len()],
    ensures: |ret| ret.is_err() || machine.comps.len() > entry_comps || machine.tasks.len() > entry_tasks,
)]
pub(super) fn map(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    mut state: Mapping,
) -> Result<(), EvalFault>
{
    let stuck = EvalFault::TransportedNonPath;
    let closure = domain
        .value_closure(state.motive)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
    let ValueBody::ValueType(family) = closure.body()
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let placeholder = state.rest;
    let Some(&ValueType::Path { left, right, .. }) = core.value_type(family)
    else {
        return Err(stuck);
    };
    let endpoint = match state.side {
        Side::Left => left,
        Side::Right => right,
    };
    let chain = calls(core, endpoint).ok_or(stuck)?;
    loop {
        let Some(&function) = chain.get(usize::from(state.call))
        else {
            machine
                .comps
                .push(domain.comp_return(state.rest, CompTermFace::Reduced));
            return Ok(());
        };
        let (tag, words, rest) = match head(core, domain, machine, state.rest)? {
            Head::Empty => {
                state.call = Call::from(usize::from(state.call).saturating_add(1));
                state.rest = state.mapped;
                // The empty image of the word mapped so far, which is its own
                // end: an image adds letters after it only once one is read.
                state.mapped = match spelled(core, domain, machine, state.mapped)? {
                    Some((_, end)) => end,
                    None => return Err(stuck),
                };
                continue;
            },
            Head::Letter { tag, words, rest } => (tag, words, rest),
            Head::Other => return Err(stuck),
        };
        let cell = FreeCells::generator(tag).ok_or(stuck)?;
        let case = cased(core, machine, function).ok_or(stuck)?;
        state.rest = rest;
        let Arm::Written(arm) = loop_arm(core, machine, case, (words, cell))?.ok_or(stuck)?
        else {
            continue;
        };
        let orientation = if usize::from(tag) % 2 == 1 {
            Orientation::Forward
        }
        else {
            Orientation::Inverse
        };
        let onward = domain.native_continuation(CompBody::Mapping {
            motive: state.motive,
            side: state.side,
            call: state.call,
            rest: state.rest,
            mapped: state.mapped,
            orientation,
        });
        machine.tasks.push(Task::BindClosure(onward));
        // The arm stands under the case's argument, which it does not read:
        // any value binds it.
        let mut arms = Environment::new();
        arms.extend(Zone::Intuitionistic, placeholder);
        let env = machine.hold_env(arms);
        machine.tasks.push(Task::Comp { term: arm, env });
        return Ok(());
    }
}

/// Append a letter's image, bound by a [`CompBody::Mapping`] continuation,
/// and map on.
///
/// # Specification
/// - requires: `image` is the loop arm's answer for the letter `state` was
///   mapping.
/// - ensures: as [`map`], the image, inverted for an inverse letter, after
///   `state.mapped`.
/// - fails: [`EvalFault::TransportedNonPath`] for an image that does not
///   splice; as [`map`] otherwise.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the flip's arm answer is appended as the loop's image;
///   dropping it returns the empty word.
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
#[spec(
    captures: [entry_comps = machine.comps.len(), entry_tasks = machine.tasks.len()],
    ensures: |ret| ret.is_err() || machine.comps.len() > entry_comps || machine.tasks.len() > entry_tasks,
)]
pub(super) fn mapped(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    mut state: Mapping,
    image: DomainValueId,
) -> Result<(), EvalFault>
{
    let stuck = EvalFault::TransportedNonPath;
    let image = match state.orientation {
        Orientation::Forward => image,
        Orientation::Inverse => inverted(core, domain, machine, image)?.ok_or(stuck)?,
    };
    state.mapped = concatenated(core, domain, machine, (state.mapped, image))?.ok_or(stuck)?;
    map(core, domain, machine, state)
}

/// Splice the transported path between the images a [`CompBody::Conjugated`]
/// continuation gathers, running the right endpoint's chain first when it has
/// one.
///
/// # Specification
/// - requires: `image` is the image the stage names; `along` the one-letter
///   word, whose rest is empty.
/// - ensures: the spliced path returned, or the right endpoint's mapping pushed
///   under a continuation at [`Conjugating::Right`].
/// - fails: [`EvalFault::TransportedNonPath`] for pieces that do not splice; as
///   [`map`] otherwise.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — cong along the loop splices reflexivity between the fixed
///   endpoint's empty image and the flip's image of the loop.
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
#[spec(
    captures: [entry_comps = machine.comps.len(), entry_tasks = machine.tasks.len()],
    ensures: |ret| ret.is_err() || machine.comps.len() > entry_comps || machine.tasks.len() > entry_tasks,
)]
pub(super) fn conjugated(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    (motive, along, value): (ValueClosureId, DomainValueId, DomainValueId),
    (stage, image): (Conjugating, DomainValueId),
) -> Result<(), EvalFault>
{
    let stuck = EvalFault::TransportedNonPath;
    let Head::Letter { rest: empty, .. } = head(core, domain, machine, along)?
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let (left, right) = match stage {
        Conjugating::Right(left) => (left, image),
        Conjugating::Left => {
            let (_, right) = family_actions(core, domain, motive)?.ok_or(stuck)?;
            match right {
                Action::Fixed => (image, empty),
                Action::Moving => (image, along),
                Action::Through => {
                    let onward = domain.native_continuation(CompBody::Conjugated {
                        motive,
                        along,
                        value,
                        stage: Conjugating::Right(image),
                    });
                    machine.tasks.push(Task::BindClosure(onward));
                    return map(core, domain, machine, Mapping {
                        motive,
                        side: Side::Right,
                        call: Call::from(0_usize),
                        rest: along,
                        mapped: empty,
                        orientation: Orientation::Forward,
                    });
                },
            }
        },
    };
    let moved = spliced(core, domain, machine, (left, value, right))?.ok_or(stuck)?;
    machine
        .comps
        .push(domain.comp_return(moved, CompTermFace::Reduced));
    Ok(())
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Transparency;
    use gandr_core_term::ValueId;
    use gandr_core_term::Zone;
    use gandr_kernel_check_memo::NullMemo;
    use gandr_kernel_conversion_trace::TraceLog;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorCount;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::FieldCount;
    use gandr_kernel_term::FreeCell;
    use gandr_kernel_term::FreeCells;
    use gandr_kernel_term::GlobalIndex;
    use gandr_kernel_term::Presentation;
    use gandr_kernel_term::RuleNode;

    use crate::arena::DomainArena;
    use crate::eval::Definitions;
    use crate::eval::Fuel;
    use crate::eval::LoweredChain;
    use crate::eval::eval_computation;
    use crate::machine::MachineSettings;
    use crate::machine::MachineVerdict;
    use crate::machine::Problem;
    use crate::machine::TraceNode;
    use crate::machine::decide;
    use crate::presented::Presented;

    /// The sort `S` of one point, `Base`.
    const SORT: usize = 0;
    /// The words of one loop at `Base`.
    const WORDS: usize = 1;
    /// `loop`, whose body is the word of its letter.
    const LOOP: usize = 2;
    /// `flip`, the case over `S` whose loop arm answers the inverse letter.
    const FLIP: usize = 3;

    /// The terms the witnesses build on, in the checker's arena.
    struct Circle
    {
        /// `S`.
        carrier: gandr_core_term::ValueTypeId,
        /// `Base`.
        point: ValueId,
        /// The empty word.
        empty: ValueId,
        /// The word of the loop's letter.
        letter: ValueId,
        /// The word of its inverse.
        inverse: ValueId,
        /// The constant `loop`.
        named: ValueId,
        /// `flip`'s body: `thunk (λx. case x { Base ⇒ return Base; loop ⇒
        /// return back(loop) })`.
        flip: ValueId,
    }

    /// The circle's terms.
    ///
    /// # Specification
    /// trivial.
    fn circle(core: &mut CoreArena) -> Circle
    {
        let carrier = core.value_type_data(ConstantIndex::from(SORT), Vec::new());
        let own = core.value_type_data(ConstantIndex::from(WORDS), Vec::new());
        let point = core.value_constructor(carrier, ConstructorTag::from(0_usize), Vec::new());
        let empty = core.value_constructor(own, ConstructorTag::from(0_usize), Vec::new());
        let letter = core.value_constructor(own, ConstructorTag::from(1_usize), vec![empty]);
        let inverse = core.value_constructor(own, ConstructorTag::from(2_usize), vec![empty]);
        let named = core.value_constant(ConstantIndex::from(LOOP));
        let kept = core.comp_type_returner(carrier);
        let at_point = core.computation_return(point);
        let at_loop = core.computation_return(inverse);
        let scrutinee = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = core.computation_data_case(scrutinee, kept, vec![at_point, at_loop]);
        let lambda = core.computation_lambda(case);
        let flip = core.value_thunk(lambda);
        Circle {
            carrier,
            point,
            empty,
            letter,
            inverse,
            named,
            flip,
        }
    }

    /// Whether a chain records the sort's constructor count.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Count
    {
        /// The count is recorded.
        Recorded,
        /// It is not.
        Missing,
    }

    /// The chain the witnesses run over: the words presented, `loop` and
    /// `flip` defined, and the sort's constructor count as `count` says.
    ///
    /// # Specification
    /// trivial.
    fn chain(
        circle: &Circle,
        count: Count,
    ) -> LoweredChain
    {
        let base = || -> alloc::boxed::Box<[RuleNode]> {
            [RuleNode::Constructor(ConstructorTag::from(0_usize))].into()
        };
        let cells = FreeCells::new(ConstantIndex::from(SORT), vec![FreeCell::new(
            base(),
            base(),
        )]);
        let mut chain = LoweredChain::new();
        chain.present(
            ConstantIndex::from(WORDS),
            Presented::new(
                Presentation::words(cells),
                [0_usize, 1, 1].map(FieldCount::from).into(),
            ),
        );
        if count == Count::Recorded {
            chain.admit_data(ConstantIndex::from(SORT), ConstructorCount::from(1_usize));
        }
        for (constant, global, body) in [
            (ConstantIndex::from(LOOP), 0_u32, circle.letter),
            (ConstantIndex::from(FLIP), 1_u32, circle.flip),
        ] {
            let _height = chain
                .define(
                    constant,
                    GlobalIndex::from(global),
                    Transparency::Manifest,
                    &[],
                    body,
                )
                .expect("the definition admits");
        }
        chain
    }

    /// Decide `left` against `right` over `chain`, or `None` when `left` does
    /// not evaluate.
    ///
    /// # Specification
    /// trivial.
    fn decided(
        core: &CoreArena,
        chain: &LoweredChain,
        (left, right): (ComputationId, ComputationId),
    ) -> Option<MachineVerdict>
    {
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let fuel = Fuel::from(512_u32);
        let left = eval_computation(core, &mut domain, definitions, fuel, left).ok()?;
        let right = eval_computation(core, &mut domain, definitions, fuel, right)
            .expect("the expected side evaluates");
        let mut log = TraceLog::<TraceNode>::new();
        let report = decide::<_, NullMemo>(
            core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::computations(left, right),
            &mut log,
        )
        .expect("the machine answers");
        Some(report.verdict())
    }

    #[test]
    fn transport_along_the_loop_moves_the_endpoint()
    {
        let mut core = CoreArena::new();
        let circle = circle(&mut core);
        let chain = chain(&circle, Count::Recorded);
        let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let family = core.value_type_path(circle.carrier, circle.point, moving);
        let moved = core.computation_return(circle.letter);
        let stayed = core.computation_return(circle.empty);
        // Along the word and along the constant naming it alike.
        for path in [circle.letter, circle.named] {
            let transported = core.computation_path_transport(family, path, circle.empty);
            assert_eq!(
                decided(&core, &chain, (transported, moved)),
                Some(MachineVerdict::Convertible),
                "reflexivity at the point carried along the loop is the loop"
            );
            assert_eq!(
                decided(&core, &chain, (transported, stayed)),
                Some(MachineVerdict::NotConvertible),
                "and not reflexivity"
            );
        }
    }

    #[test]
    fn the_loop_conjugates_a_loop_to_itself()
    {
        let mut core = CoreArena::new();
        let circle = circle(&mut core);
        let chain = chain(&circle, Count::Recorded);
        let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let family = core.value_type_path(circle.carrier, moving, moving);
        for operand in [circle.letter, circle.inverse, circle.empty] {
            let transported = core.computation_path_transport(family, circle.named, operand);
            let fixed = core.computation_return(operand);
            assert_eq!(
                decided(&core, &chain, (transported, fixed)),
                Some(MachineVerdict::Convertible),
                "conjugation by the loop fixes every loop at the point"
            );
        }
        let transported = core.computation_path_transport(family, circle.named, circle.letter);
        let moved = core.computation_return(circle.empty);
        assert_eq!(
            decided(&core, &chain, (transported, moved)),
            Some(MachineVerdict::NotConvertible),
            "and moves no loop to another"
        );
    }

    #[test]
    fn cong_along_the_loop_is_the_arm_s_image()
    {
        let mut core = CoreArena::new();
        let circle = circle(&mut core);
        let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let flip = core.value_constant(ConstantIndex::from(FLIP));
        let forced = core.computation_force(flip);
        let applied = core.computation_application(forced, moving);
        let through = core.value_returned(applied);
        // `cong(flip, loop)`: reflexivity at `flip(Base)`, carried along the
        // loop in the family of paths from it to `flip(y)`.
        let family = core.value_type_path(circle.carrier, circle.point, through);
        let cong = core.computation_path_transport(family, circle.named, circle.empty);
        let image = core.computation_return(circle.inverse);
        assert_eq!(
            decided(&core, &chain(&circle, Count::Recorded), (cong, image)),
            Some(MachineVerdict::Convertible),
            "the flip's image of the loop is its loop arm's answer, the inverse"
        );
        let looped = core.computation_return(circle.letter);
        assert_eq!(
            decided(&core, &chain(&circle, Count::Recorded), (cong, looped)),
            Some(MachineVerdict::NotConvertible),
            "and not the loop"
        );
        assert_ne!(
            decided(&core, &chain(&circle, Count::Missing), (cong, image)),
            Some(MachineVerdict::Convertible),
            "without the sort's constructor count the arm is not found"
        );
    }

    #[test]
    fn a_word_appends_on_its_first_word()
    {
        let mut core = CoreArena::new();
        let circle = circle(&mut core);
        let chain = chain(&circle, Count::Recorded);
        let own = core.value_type_data(ConstantIndex::from(WORDS), Vec::new());
        let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let family = core.value_type_path(circle.carrier, circle.point, moving);
        // Under `λq. λp.`: `q` is index 1, `p` index 0.
        let after = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let before = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let binary = |core: &mut CoreArena, body: ComputationId| {
            let inner = core.computation_lambda(body);
            core.computation_lambda(inner)
        };
        // `here(Base) then q` is `q`.
        let unit = core.computation_path_transport(family, after, circle.empty);
        let unit = binary(&mut core, unit);
        let itself = core.computation_return(after);
        let itself = binary(&mut core, itself);
        assert_eq!(
            decided(&core, &chain, (unit, itself)),
            Some(MachineVerdict::Convertible),
            "the empty word moved along a path is the path"
        );
        // `(loop ∷ p) then q` is `loop ∷ (p then q)`.
        let consed = core.value_constructor(own, ConstructorTag::from(1_usize), vec![before]);
        let appended = core.computation_path_transport(family, after, consed);
        let appended = binary(&mut core, appended);
        let rest = core.computation_path_transport(family, after, before);
        let held = core.value_returned(rest);
        let prefixed = core.value_constructor(own, ConstructorTag::from(1_usize), vec![held]);
        let prefixed = core.computation_return(prefixed);
        let prefixed = binary(&mut core, prefixed);
        assert_eq!(
            decided(&core, &chain, (appended, prefixed)),
            Some(MachineVerdict::Convertible),
            "a letter before a path moved along another stays first"
        );
        let inverted = core.value_constructor(own, ConstructorTag::from(2_usize), vec![held]);
        let inverted = core.computation_return(inverted);
        let inverted = binary(&mut core, inverted);
        assert_eq!(
            decided(&core, &chain, (appended, inverted)),
            Some(MachineVerdict::NotConvertible),
            "and is no other letter"
        );
    }
}
