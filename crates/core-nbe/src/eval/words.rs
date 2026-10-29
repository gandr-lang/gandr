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
//! - **through calls**, `⟨f(… g(y) … y …)⟩`: a route per occurrence of `y`, the
//!   leftmost first, each route's image appended after the one before — `ap`
//!   through each argument in turn, the others standing at the point. Along one
//!   route, each function's image of the word its inner call answered,
//!   innermost first: a function's image of a letter is the loop arm its case
//!   over the sort carries for the letter's loop, inverted for an inverse
//!   letter, and reflexivity for a case with no loop arm. A case over another
//!   argument, standing at the point, selects its branch at that argument's
//!   constructor: the letter itself where the branch returns the route's
//!   argument, reflexivity where it ignores it; any other branch sticks.
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
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::CellIndex;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FreeCells;
use gandr_kernel_term::RuleNode;
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
use crate::closure::Mapping;
use crate::closure::Orientation;
use crate::closure::Route;
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

/// One call of an endpoint's reading: the function, every argument it
/// applies in written order, and the call one of whose arguments it answers.
///
/// # Specification
/// - ensures: some argument of `arguments` reads the binder; `parent` names the
///   call this one answers an argument of and that argument's position, `None`
///   for the endpoint's own call; for a call bound after another, the one
///   argument is that call's result.
/// - executable: none — the ids hold no arena to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — `mul(b, Base)` is one call of two arguments moving at the
///   first, and its loop arm reads the second as `Base`.
/// - witness: `eval::words::tests::cong_along_the_loop_reads_a_map_of_two_arguments`
#[derive(Clone, Debug, Eq, PartialEq)]
struct Node
{
    /// The function called.
    function: ConstantIndex,
    /// Every argument the call applies, the first outermost.
    arguments: Vec<ValueId>,
    /// The call whose argument this call answers, and that argument's
    /// position.
    parent: Option<(usize, usize)>,
}

/// What the walk over an endpoint's calls still reads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Pending
{
    /// A call answering the argument at a position of a read call, or the
    /// endpoint's own.
    Call(ComputationId, Option<(usize, usize)>),
    /// The binder itself, as the argument at a position of a read call.
    Leaf(usize, usize),
}

/// An endpoint read as the calls it runs the family's binder through: each
/// call once, and a route per occurrence of the binder, from the call it is
/// an argument of out to the endpoint, the leftmost occurrence first.
///
/// # Specification
/// - ensures: each leaf names a call of `nodes` and an argument position of it;
///   following `parent` from any call reaches the endpoint's own.
/// - executable: none — the ids hold no arena to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — `mul(mul(b, Base), invLooper(b))` reads as two routes,
///   through the first argument and then the second, and the image of the loop
///   is the first's then the second's.
/// - witness: `eval::words::tests::cong_along_the_loop_reads_both_arguments_of_a_diagonal_464`
#[derive(Clone, Debug, Eq, PartialEq)]
struct Routes
{
    /// Every call read, each once.
    nodes: Vec<Node>,
    /// The call and argument position of each occurrence of the binder,
    /// leftmost first.
    leaves: Vec<(usize, usize)>,
}

/// An argument's position in a call, the first outermost.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Argument(usize);

impl Routes
{
    /// The call `call` steps out along `route` from the binder, and the
    /// argument position the route moves it at.
    ///
    /// # Specification
    /// - ensures: `None` once the route has left the endpoint's own call, or
    ///   for no route at `route`; the call and position otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the `for` steps one parent per turn.
    /// - measure: the steps left.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Routes`].
    /// - witness: `eval::words::tests::cong_along_the_loop_reads_both_arguments_of_a_diagonal_464`
    #[spec(ensures: |ret| ret.is_none_or(|(node, position)| position.0 < node.arguments.len()))]
    fn link(
        &self,
        route: Route,
        call: Call,
    ) -> Option<(&Node, Argument)>
    {
        let &(mut node, mut moving) = self.leaves.get(usize::from(route))?;
        for _step in 0 .. usize::from(call) {
            (node, moving) = self.nodes.get(node)?.parent?;
        }
        Some((self.nodes.get(node)?, Argument(moving)))
    }
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
        | DomainValue::Recorded { .. }
        | DomainValue::PathCertificate { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Univalence { .. }
        | DomainValue::HeldTransport { .. }
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
///   endpoint that never reads it; [`Action::Through`] for calls [`routes`]
///   reads; `None` otherwise.
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
    Some(Action::Through) => routes(core, endpoint).is_ok_and(|found| found.is_some()),
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
    Ok(routes(core, endpoint)?.map(|_| Action::Through))
}

/// The calls an endpoint runs the family's binder through, and a route per
/// occurrence of the binder, the leftmost first.
///
/// # Specification
/// - requires: `endpoint` is read under the family's one binder.
/// - ensures: `Some(routes)` exactly when the endpoint is `⟨c⟩` for a call `c`
///   of the shape `force f a₁ … aₙ` some of whose arguments read the binder,
///   each of those the binder itself or `⟨c'⟩` for such a call, or `x ← c';
///   force f x` for such a call `c'`, every function `f` a constant; each call
///   once with its arguments, and a leaf per argument that is the binder.
/// - fails: the free-index walk's fault.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `while` takes one pending call or leaf per turn, each call
///   pending its arguments' strict subterms only, never recursing.
/// - measure: the endpoint's nodes left.
///
/// # Adequacy
/// - hypothesis: L3 — `flip(y)` reads as one route of one call, whose loop arm
///   gives cong its image; `mul(b, Base)` as one call of two arguments moving
///   at the first; `mul(mul(b, Base), invLooper(b))` as two routes, through the
///   first argument and then the second.
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
/// - witness: `eval::words::tests::cong_along_the_loop_reads_a_map_of_two_arguments`
/// - witness: `eval::words::tests::cong_along_the_loop_reads_both_arguments_of_a_diagonal_464`
/// - witness: `eval::words::tests::cong_along_the_loop_reads_a_call_bound_into_the_next`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| found.as_ref().is_none_or(|read| !read.leaves.is_empty()
    && read.leaves.iter().all(|&(node, position)| read.nodes.get(node).is_some_and(|node| position < node.arguments.len()))
    && matches!(core.value(endpoint), Some(&Value::Returned(_))))))]
fn routes(
    core: &CoreArena,
    endpoint: ValueId,
) -> Result<Option<Routes>, EvalFault>
{
    let Some(&Value::Returned(call)) = core.value(endpoint)
    else {
        return Ok(None);
    };
    let binder = DeBruijnIndex::from(0_u32);
    let bound = |argument: ValueId| matches!(core.value(argument), Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if index == binder);
    let mut read = Routes {
        nodes: Vec::new(),
        leaves: Vec::new(),
    };
    let mut pending = Vec::from([Pending::Call(call, None)]);
    while let Some(next) = pending.pop() {
        let (call, parent) = match next {
            Pending::Leaf(node, position) => {
                read.leaves.push((node, position));
                continue;
            },
            Pending::Call(call, parent) => (call, parent),
        };
        let at = read.nodes.len();
        if let Some(&Computation::Bind(first, then)) = core.computation(call) {
            let Some((function, arguments)) = spine(core, then)
            else {
                return Ok(None);
            };
            let [argument] = *arguments.as_slice()
            else {
                return Ok(None);
            };
            if !bound(argument) {
                return Ok(None);
            }
            read.nodes.push(Node {
                function,
                arguments,
                parent,
            });
            pending.push(Pending::Call(first, Some((at, 0))));
            continue;
        }
        let Some((function, arguments)) = spine(core, call)
        else {
            return Ok(None);
        };
        // The arguments last first, so the leftmost is read first.
        let mut moves = false;
        for (position, &argument) in arguments.iter().enumerate().rev() {
            let mut free = FreeIndices::default();
            if free
                .of(core, CoreTerm::Value(argument))
                .map_err(free_fault)?
                .intuitionistic()
                .holds(binder)
                != Membership::Held
            {
                continue;
            }
            moves = true;
            if bound(argument) {
                pending.push(Pending::Leaf(at, position));
            }
            else if let Some(&Value::Returned(inner)) = core.value(argument) {
                pending.push(Pending::Call(inner, Some((at, position))));
            }
            else {
                return Ok(None);
            }
        }
        if !moves {
            return Ok(None);
        }
        read.nodes.push(Node {
            function,
            arguments,
            parent,
        });
    }
    Ok(Some(read))
}

/// The function and the arguments, the first outermost, of the call `call`
/// when it is `force f a₁ … aₙ` for a constant `f` and at least one argument.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as the summary; `None` for any other computation.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `while` steps to the head of one application per turn.
/// - measure: the spine's applications left.
///
/// # Adequacy
/// - hypothesis: L3 — as [`routes`].
/// - witness: `eval::words::tests::cong_along_the_loop_reads_a_map_of_two_arguments`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|&(_, ref arguments)| !arguments.is_empty()))]
fn spine(
    core: &CoreArena,
    call: ComputationId,
) -> Option<(ConstantIndex, Vec<ValueId>)>
{
    let mut arguments = Vec::new();
    let mut head = call;
    while let Some(&Computation::Application(inner, argument)) = core.computation(head) {
        arguments.push(argument);
        head = inner;
    }
    let Some(&Computation::Force(function)) = core.computation(head)
    else {
        return None;
    };
    let Some(&Value::Constant(constant)) = core.value(function)
    else {
        return None;
    };
    if arguments.is_empty() {
        return None;
    }
    arguments.reverse();
    Some((constant, arguments))
}

/// Read a definition as a case over one of its arguments: the thunk of one
/// lambda per argument whose body is a data case on an argument's variable.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the case and the position, first outermost, of the argument it is
///   over, for a constant whose manifest body
///   ([`super::Definitions::definition`]) is such a thunk; `None` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `for` opens one lambda per argument.
/// - measure: the arguments left.
///
/// # Adequacy
/// - hypothesis: L3 — `flip`'s manifest body is read as its case, and without
///   the sort's constructor count the arm after it is not found; `mul`'s as a
///   case on its first of two arguments, which `mul(Base, y)` holds fixed.
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
/// - witness: `eval::words::tests::cong_along_the_loop_reads_a_map_of_two_arguments`
/// - witness: `eval::words::tests::cong_along_the_loop_reads_both_arguments_of_a_diagonal_464`
#[spec(ensures: |ret| ret.is_none_or(|(case, position)| position.0 < node.arguments.len() && matches!(core.computation(case), Some(&Computation::DataCase { .. }))))]
fn case_of(
    core: &CoreArena,
    machine: &Machine<'_>,
    node: &Node,
) -> Option<(ComputationId, Argument)>
{
    let body = machine.definitions.definition(node.function)?;
    let Some(&Value::Thunk(mut body)) = core.value(body)
    else {
        return None;
    };
    for _argument in &node.arguments {
        let Some(&Computation::Lambda(inner)) = core.computation(body)
        else {
            return None;
        };
        body = inner;
    }
    let Some(&Computation::DataCase { scrutinee, .. }) = core.computation(body)
    else {
        return None;
    };
    let Some(&Value::Variable {
        zone: Zone::Intuitionistic,
        index,
    }) = core.value(scrutinee)
    else {
        return None;
    };
    let index = usize::try_from(u32::from(index)).ok()?;
    let position = node.arguments.len().checked_sub(index)?.checked_sub(1)?;
    Some((body, Argument(position)))
}

/// The index the argument at `position` of `node` has under the lambdas of
/// its function, the first outermost.
///
/// # Specification
/// - ensures: the arguments' count less one less `position`, or `None` past the
///   last argument.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`case_of`]: `mul`'s first argument is index 1.
/// - witness: `eval::words::tests::cong_along_the_loop_reads_a_map_of_two_arguments`
#[spec(ensures: |ret| ret.is_none() == (position.0 >= node.arguments.len()))]
fn index_of(
    node: &Node,
    position: Argument,
) -> Option<DeBruijnIndex>
{
    let after = node
        .arguments
        .len()
        .checked_sub(position.0)?
        .checked_sub(1)?;
    Some(DeBruijnIndex::from(u32::try_from(after).ok()?))
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
/// over no sort the letter's words loop in, or its arm reads the argument at
/// `scrutinee`.
///
/// # Specification
/// - requires: `case` is a data case in `core` over the variable `scrutinee`;
///   `words` an admitted type of words whose `cell`'s loop the image is asked
///   of.
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
///   loop's image, and without the sort's constructor count no arm is read;
///   `mul`'s arm reads its second argument and not its first.
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
/// - witness: `eval::words::tests::cong_along_the_loop_reads_a_map_of_two_arguments`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|found| found.is_none_or(|arm| match arm { Arm::Written(written) => core.computation(written).is_some(), Arm::Unwritten => matches!(core.computation(case), Some(&Computation::DataCase { .. })) })))]
fn loop_arm(
    core: &CoreArena,
    machine: &Machine<'_>,
    (case, scrutinee): (ComputationId, DeBruijnIndex),
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
    let mut free = FreeIndices::default();
    if free
        .of(core, CoreTerm::Computation(arm))
        .map_err(free_fault)?
        .intuitionistic()
        .holds(scrutinee)
        == Membership::Held
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
///   transport with the rest's bound after it along a longer word; along a
///   one-letter word in a path family, an operand a definition names reread as
///   its word whichever way the endpoints act, and any other operand
///   conjugating as the module states — and [`Moved::Unmoved`] with the machine
///   unchanged otherwise.
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
///   carries the loop to the arm's image. Over every pairing of a fixed, a
///   moving and a called endpoint, words of up to two letters and the named
///   loop, spelled and named operands land on the word the free group computes,
///   a named operand under a called endpoint included.
/// - witness: `eval::words::tests::transport_along_the_loop_moves_the_endpoint`
/// - witness: `eval::words::tests::the_loop_conjugates_a_loop_to_itself`
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
/// - witness: `eval::words::tests::transport_along_a_word_conjugates_by_its_moving_endpoints`
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
    // The operand a definition names reads as its word before any row
    // splices it, whichever way the endpoints act on the letter.
    if let Some(body) = named(core, domain, machine, value)? {
        reread(machine, motive, (path, value), (Side::Right, body));
        return Ok(Moved::Stepped);
    }
    let static_image = |action: Action| match action {
        Action::Fixed => Some(rest),
        Action::Moving => Some(path),
        Action::Through => None,
    };
    match (static_image(left), static_image(right)) {
        (Some(left), Some(right)) => {
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
            map(
                core,
                domain,
                machine,
                starting(motive, Side::Left, (path, rest)),
            )?;
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
            map(
                core,
                domain,
                machine,
                starting(motive, Side::Right, (path, rest)),
            )?;
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
///   ℓ ∷ tr(P, q, p)`, a letter looping at the one point — with the operand
///   reread when a definition names it, and supplied again as what it returns
///   when the run holds it as a call; [`Moved::Unmoved`] with the machine
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
/// - witness: `eval::words::tests::a_composite_over_a_call_to_the_empty_word_is_its_second_word_473`
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
            if let Some(body) = named(core, domain, machine, value)? {
                reread(machine, motive, (path, value), (Side::Right, body));
                return Ok(Moved::Stepped);
            }
            // An operand the run holds, a call such as `spin(Z)`, reads as
            // what it returns, as the kernel runs a returned operand first:
            // its computation runs on through its definitions, and what it
            // returns moves along the path ([`ran`]).
            let Some(computation) =
                super::held_endpoint(domain, value).map_err(EvalFault::Domain)?
            else {
                return Ok(Moved::Unmoved);
            };
            let onward = domain.native_continuation(CompBody::Appending {
                motive,
                path,
                operand: value,
            });
            machine.tasks.push(Task::BindClosure(onward));
            machine.tasks.push(Task::Yield);
            machine.tasks.push(Task::Running);
            machine.comps.push(computation);
        },
    }
    Ok(Moved::Stepped)
}

/// Move what a held operand's run returned along the path, bound by a
/// [`CompBody::Appending`] continuation.
///
/// # Specification
/// - requires: `read` is what the run of `operand`'s held computation returned;
///   `path` and `operand` are the transport's in `motive`.
/// - ensures: the transport of `read` along `path` in `motive` queued when
///   `read` is no held endpoint; otherwise the transport stuck as the evaluator
///   leaves one no rule moves, over `operand`, on the computation stack.
/// - fails: [`EvalFault::TransportedNonPath`] for a stuck run along a path that
///   is no neutral; as [`super::held_endpoint`] and the spine's growth
///   otherwise.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `spin(Z) then q` reads as `q` once `spin(Z)` returns the
///   empty word; read as its call, the transport sticks.
/// - witness: `eval::words::tests::a_composite_over_a_call_to_the_empty_word_is_its_second_word_473`
#[spec(
    captures: [tasks = machine.tasks.len(), comps = machine.comps.len()],
    ensures: |ret| ret.is_err() || machine.tasks.len() > tasks || machine.comps.len() > comps,
)]
pub(super) fn ran(
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    (motive, path, operand): (ValueClosureId, DomainValueId, DomainValueId),
    read: DomainValueId,
) -> Result<(), EvalFault>
{
    if super::held_endpoint(domain, read)
        .map_err(EvalFault::Domain)?
        .is_none()
    {
        machine.tasks.push(Task::PathTransport(motive));
        machine.values.extend([path, read]);
        return Ok(());
    }
    let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(path)
    else {
        return Err(EvalFault::TransportedNonPath);
    };
    let grown = super::extend_spine(domain, neutral, crate::domain::Elimination::PathTransport {
        motive,
        value: operand,
    })?;
    machine
        .comps
        .push(domain.comp_neutral(grown, CompTermFace::Reduced));
    Ok(())
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

/// The state that maps `word` through the endpoint at `side` of `motive`'s
/// family from its first route's innermost call, `empty` the word's empty
/// end.
///
/// # Specification
/// trivial.
fn starting(
    motive: ValueClosureId,
    side: Side,
    (word, empty): (DomainValueId, DomainValueId),
) -> Mapping
{
    Mapping {
        motive,
        side,
        route: Route::from(0_usize),
        call: Call::from(0_usize),
        word,
        routed: empty,
        rest: word,
        mapped: empty,
        orientation: Orientation::Forward,
    }
}

/// The routes of the endpoint at `state.side` of `state.motive`'s path family,
/// with the family's carrier and environment.
///
/// # Specification
/// - requires: `state.motive` suspends a value type under one binder.
/// - ensures: the [`routes`] of that endpoint, the family's carrier, and the
///   environment the family is closed over.
/// - fails: [`EvalFault::Domain`] for a closure the arena does not hold;
///   [`EvalFault::MachineInvariant`] for one holding no value type;
///   [`EvalFault::TransportedNonPath`] for a family that is no path type or an
///   endpoint no route reads; the free-index walk's fault.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`map`].
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(ref read, _, _)| !read.leaves.is_empty()))]
fn endpoint_routes(
    core: &CoreArena,
    domain: &DomainArena,
    state: Mapping,
) -> Result<(Routes, ValueTypeId, Environment), EvalFault>
{
    let stuck = EvalFault::TransportedNonPath;
    let closure = domain
        .value_closure(state.motive)
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
        return Err(stuck);
    };
    let endpoint = match state.side {
        Side::Left => left,
        Side::Right => right,
    };
    let read = routes(core, endpoint)?.ok_or(stuck)?;
    Ok((read, carrier, closure.environment().clone()))
}

/// The point the words at `words` loop at, as a value of `carrier`, when the
/// carrier is their sort and the point one constructor of no fields.
///
/// # Specification
/// - ensures: the constructor of `carrier` the cells' point spells, exactly
///   when `carrier` is the parameterless sort the words' cells loop in and
///   their point is one constructor of no fields; `None` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the diagonal's second route evaluates `mul(b, Base)` with
///   `b` at `Base`, whose case then selects its branch; at any other value no
///   branch returns the route's argument.
/// - witness: `eval::words::tests::cong_along_the_loop_reads_both_arguments_of_a_diagonal_464`
#[spec(ensures: |ret| ret.is_none_or(|built| matches!(domain.value(built), Some(&DomainValue::Constructor { .. }))))]
fn point(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &Machine<'_>,
    (carrier, words): (ValueTypeId, ConstantIndex),
) -> Option<DomainValueId>
{
    let cells = machine
        .definitions
        .presented(words)
        .and_then(crate::presented::Presented::cells)?;
    let Some(&ValueType::Data {
        declaration,
        ref arguments,
    }) = core.value_type(carrier)
    else {
        return None;
    };
    if declaration != cells.sort() || !arguments.is_empty() {
        return None;
    }
    let [RuleNode::Constructor(tag)] = *cells.point()
    else {
        return None;
    };
    let datatype = domain.value_closure_node(ValueBody::ValueType(carrier), Environment::new());
    let none = domain.hold_fields([]);
    Some(domain.value_constructor(datatype, tag, none, TermFace::Reduced))
}

/// The value the family's binder is bound to while the arguments off a route
/// evaluate: the words' point when the endpoint has more than one route, and
/// any value otherwise, since an argument off the only route never reads it.
///
/// # Specification
/// - ensures: as the summary.
/// - fails: [`EvalFault::TransportedNonPath`] for more than one route and a
///   carrier holding no point of the words ([`point`]).
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`point`].
/// - witness: `eval::words::tests::cong_along_the_loop_reads_both_arguments_of_a_diagonal_464`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&bound| routes.leaves.len() > 1 || bound == placeholder))]
fn held(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &Machine<'_>,
    (routes, placeholder): (&Routes, DomainValueId),
    (carrier, words): (ValueTypeId, ConstantIndex),
) -> Result<DomainValueId, EvalFault>
{
    if routes.leaves.len() > 1 {
        point(core, domain, machine, (carrier, words)).ok_or(EvalFault::TransportedNonPath)
    }
    else {
        Ok(placeholder)
    }
}

/// Map a word through the endpoint's routes, one after another. Along each,
/// skip each letter whose image is reflexivity, and run the first loop arm an
/// image needs, binding it into the next mapping step; once a call has read
/// its whole word, its image is the next call's word. Once a route is
/// through, its image follows the routes' before it and the next route maps
/// the word afresh; when the last is through, their images are returned.
///
/// A call whose case is over another argument than the route's evaluates that
/// argument where the family stands, and the branch it selects is the call's
/// image ([`selected`]). The arguments off a route are evaluated with the
/// binder at the words' point, where each route starts and ends: for `f(u(y),
/// v(y))`, `ap_f(p) = ap_{f(-, v(pt))}(ap_u(p)) · ap_{f(u(pt), -)}(ap_v(p))`.
///
/// # Specification
/// - requires: `state.mapped` and `state.routed` are closed words or empty; the
///   endpoint at `state.side` of `state.motive`'s family reads as routes.
/// - ensures: on success, either the routes' images returned; or one loop arm's
///   run pushed with a [`CompBody::Mapping`] continuation bound after it; or
///   the evaluation of the argument a case is over pushed with a
///   [`CompBody::Selecting`] continuation bound after it.
/// - fails: [`EvalFault::TransportedNonPath`] for a word, a function or an
///   image no rule maps, or for more than one route over a carrier holding no
///   point of the words; as [`head`] otherwise.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `loop` consumes one letter, one call or one route per
///   iteration, never recursing.
/// - measure: the routes left, then the calls left, then the letters left.
///
/// # Adequacy
/// - hypothesis: L3 — the flip's chain maps the loop to its arm's answer, the
///   inverse, and not to the loop; skipping the arm returns the loop unmapped.
///   The diagonal maps the loop along both routes, `mul(Base, y)` reading as
///   its argument; mapping one route only leaves the loop.
/// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
/// - witness: `eval::words::tests::cong_along_the_loop_reads_both_arguments_of_a_diagonal_464`
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
    let (routes, carrier, environment) = endpoint_routes(core, domain, state)?;
    let placeholder = state.rest;
    loop {
        let Some((node, moving)) = routes.link(state.route, state.call)
        else {
            // The route is through: its image follows the routes' before it,
            // and the next one maps the word afresh.
            let routed = if usize::from(state.route) == 0 {
                state.rest
            }
            else {
                concatenated(core, domain, machine, (state.routed, state.rest))?.ok_or(stuck)?
            };
            let next = usize::from(state.route).saturating_add(1);
            if next >= routes.leaves.len() {
                machine
                    .comps
                    .push(domain.comp_return(routed, CompTermFace::Reduced));
                return Ok(());
            }
            let (_, end) = spelled(core, domain, machine, state.word)?.ok_or(stuck)?;
            state.route = Route::from(next);
            state.call = Call::from(0_usize);
            state.routed = routed;
            state.rest = state.word;
            state.mapped = end;
            continue;
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
        let (case, over) = case_of(core, machine, node).ok_or(stuck)?;
        if over != moving {
            // A case over another argument: that argument where the family
            // stands selects the branch that is the call's image.
            let &argument = node.arguments.get(over.0).ok_or(stuck)?;
            let bound = held(
                core,
                domain,
                machine,
                (&routes, placeholder),
                (carrier, words),
            )?;
            let mut within = environment;
            within.extend(Zone::Intuitionistic, bound);
            let onward = domain.native_continuation(CompBody::Selecting(state));
            machine.tasks.push(Task::BindClosure(onward));
            machine.tasks.push(Task::Yield);
            let within = machine.hold_env(within);
            machine.tasks.push(Task::Value {
                term: argument,
                env: within,
            });
            return Ok(());
        }
        let scrutinee = index_of(node, moving).ok_or(stuck)?;
        state.rest = rest;
        let Arm::Written(arm) =
            loop_arm(core, machine, (case, scrutinee), (words, cell))?.ok_or(stuck)?
        else {
            continue;
        };
        let orientation = if usize::from(tag) % 2 == 1 {
            Orientation::Forward
        }
        else {
            Orientation::Inverse
        };
        let onward = domain.native_continuation(CompBody::Mapping(Mapping {
            orientation,
            ..state
        }));
        machine.tasks.push(Task::BindClosure(onward));
        // The arm stands under the function's arguments, the first outermost.
        // It does not read the one the case is over: any value binds it. Each
        // other argument is its value where the family stands, evaluated by
        // this machine before the arm runs, the first first.
        machine.tasks.push(Task::Arm(ArmEntry {
            arm,
            count: node.arguments.len(),
            moving: moving.0,
            placeholder,
        }));
        let bound = held(
            core,
            domain,
            machine,
            (&routes, placeholder),
            (carrier, words),
        )?;
        let mut within = environment;
        within.extend(Zone::Intuitionistic, bound);
        let within = machine.hold_env(within);
        for (_, &argument) in node
            .arguments
            .iter()
            .enumerate()
            .filter(|&(position, _)| Argument(position) != moving)
            .rev()
        {
            machine.tasks.push(Task::Value {
                term: argument,
                env: within,
            });
        }
        return Ok(());
    }
}

/// Read the branch a call's case selects, bound by a [`CompBody::Selecting`]
/// continuation at the value the argument it is over takes where the family
/// stands, as that call's image of the rest of the word, and map on.
///
/// # Specification
/// - requires: `value` is the argument the case of the call `state` maps
///   through is over, evaluated where the family stands; `state.rest` the word
///   that call still maps.
/// - ensures: as [`map`], the call's image of `state.rest` after `state.mapped`
///   read as the next call's word: the word itself when the selected branch
///   returns the route's argument, the empty word when it returns a value that
///   never reads it.
/// - fails: [`EvalFault::TransportedNonPath`] for a value that is no
///   constructor, or a branch of any other shape; as [`map`] otherwise.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `mul(Base, y)` selects `Base => y` and maps the loop to
///   itself; reading the branch as the empty word leaves the diagonal's image
///   one letter short.
/// - witness: `eval::words::tests::cong_along_the_loop_reads_both_arguments_of_a_diagonal_464`
#[spec(
    captures: [entry_comps = machine.comps.len(), entry_tasks = machine.tasks.len()],
    ensures: |ret| ret.is_err() || machine.comps.len() > entry_comps || machine.tasks.len() > entry_tasks,
)]
pub(super) fn selected(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    mut state: Mapping,
    value: DomainValueId,
) -> Result<(), EvalFault>
{
    let stuck = EvalFault::TransportedNonPath;
    let Some(&DomainValue::Constructor { tag, fields, .. }) = domain.value(value)
    else {
        return Err(stuck);
    };
    let fields = domain.fields(fields).map_err(EvalFault::Domain)?.len();
    let (routes, ..) = endpoint_routes(core, domain, state)?;
    let (node, moving) = routes
        .link(state.route, state.call)
        .ok_or(EvalFault::MachineInvariant)?;
    let (case, _) = case_of(core, machine, node).ok_or(EvalFault::MachineInvariant)?;
    let Some(&Computation::DataCase { ref branches, .. }) = core.computation(case)
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let &branch = branches.get(usize::from(tag)).ok_or(stuck)?;
    let Some(&Computation::Return(answer)) = core.computation(branch)
    else {
        return Err(stuck);
    };
    // The route's argument under the lambdas, and then the branch's fields.
    let index = index_of(node, moving)
        .and_then(|index| u32::from(index).checked_add(u32::try_from(fields).ok()?))
        .map(DeBruijnIndex::from)
        .ok_or(stuck)?;
    let image = if matches!(core.value(answer), Some(&Value::Variable { zone: Zone::Intuitionistic, index: read }) if read == index)
    {
        concatenated(core, domain, machine, (state.mapped, state.rest))?.ok_or(stuck)?
    }
    else if reads_through(core, CoreTerm::Value(answer), index)? == Reading::Ignores {
        state.mapped
    }
    else {
        return Err(stuck);
    };
    let (_, end) = spelled(core, domain, machine, image)?.ok_or(stuck)?;
    state.call = Call::from(usize::from(state.call).saturating_add(1));
    state.rest = image;
    state.mapped = end;
    map(core, domain, machine, state)
}

/// A loop arm waiting for its fixed arguments' values.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ArmEntry
{
    /// The loop arm.
    pub arm: ComputationId,
    /// How many arguments the function takes.
    pub count: usize,
    /// The argument the case is over, which the arm does not read.
    pub moving: usize,
    /// The value bound at the moving argument.
    pub placeholder: DomainValueId,
}

/// Bind a loop arm's arguments and queue the arm: one value per fixed
/// argument taken off the stack, the first deepest, and the placeholder at
/// the moving one.
///
/// # Specification
/// - requires: the stack holds the fixed arguments' values on top, the first
///   deepest, as [`map`] queues them.
/// - ensures: those values taken off the stack and the arm queued in the
///   environment binding every argument in order, the first outermost.
/// - fails: [`EvalFault::MachineInvariant`] when the stack holds fewer values
///   than the fixed arguments, or the moving position is no argument's.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop over the function's arguments, not recursion.
/// - measure: the arguments left.
///
/// # Adequacy
/// - hypothesis: L3 — `first`'s arm reads its fixed second argument at the
///   value the family gives it; bound in the other order, the image would be
///   another argument's.
/// - witness: `eval::words::tests::cong_along_the_loop_reads_a_map_of_two_arguments`
#[spec(
    captures: [entry_tasks = machine.tasks.len(), entry_values = machine.values.len()],
    ensures: |ret| ret.is_err() || machine.tasks.len() == entry_tasks.saturating_add(1_usize)
        && entry_values.checked_sub(entry.count.saturating_sub(1_usize)) == Some(machine.values.len()),
)]
pub(super) fn arm_entered(
    machine: &mut Machine<'_>,
    entry: ArmEntry,
) -> Result<(), EvalFault>
{
    let ArmEntry {
        arm,
        count,
        moving,
        placeholder,
    } = entry;
    let fixed = count.checked_sub(1).ok_or(EvalFault::MachineInvariant)?;
    if moving >= count {
        return Err(EvalFault::MachineInvariant);
    }
    let start = machine
        .values
        .len()
        .checked_sub(fixed)
        .ok_or(EvalFault::MachineInvariant)?;
    let mut values = machine.values.split_off(start).into_iter();
    let mut arms = Environment::new();
    for position in 0 .. count {
        let bound = if position == moving {
            placeholder
        }
        else {
            values.next().ok_or(EvalFault::MachineInvariant)?
        };
        arms.extend(Zone::Intuitionistic, bound);
    }
    let env = machine.hold_env(arms);
    machine.tasks.push(Task::Comp { term: arm, env });
    Ok(())
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
    // An arm answering a cell's name, `loop`, answers its word: the name is
    // read through its body, as a transport along it is, and the mapping
    // resumes at the word.
    if let Some(body) = named(core, domain, machine, image)? {
        let onward = domain.native_continuation(CompBody::Mapping(state));
        machine.tasks.push(Task::BindClosure(onward));
        machine.tasks.push(Task::Yield);
        machine.tasks.push(Task::Value {
            term: body,
            env: Machine::root_env(),
        });
        return Ok(());
    }
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
                    return map(
                        core,
                        domain,
                        machine,
                        starting(motive, Side::Right, (along, empty)),
                    );
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
mod tests;
