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
//! - along a closed word of more letters in a path family whose carrier never
//!   reads `y`, where each endpoint is fixed, moving or through calls, the
//!   whole word in one step: `l(w)⁻¹ · v · r(w)`, each endpoint's image of the
//!   word its letters' images in order ([`word_image`]);
//! - along any other longer word, letter by letter: `tr(P, ℓ ∷ u, v) ⇝ y ←
//!   tr(P, ℓ ∷ ε, v); tr(P↑, u↑, y)`;
//! - with a returned operand or path, that value first — the operand before the
//!   path, as the evaluator's append runs a held operand — as an elimination
//!   meeting one runs it: `tr(P, w, ⟨c⟩) ⇝ y ← c; tr(P↑, w↑, y)` and `tr(P,
//!   ⟨c⟩, v) ⇝ w ← c; tr(P↑, w, v↑)`; the empty word's row first of all, since
//!   it reads neither side's run;
//! - along one letter in a path family `y. Path[.A = C](l, r)` whose carrier
//!   never reads `y`, by conjugation (the book's lemma 2.11.2), `l(ℓ)⁻¹ · v ·
//!   r(ℓ)`: with both endpoints fixed or moving the word is spliced at once;
//!   with an endpoint through a chain of calls the reduct binds the endpoint's
//!   image and transports along it in the family `z. Path[.A = C](z, r(pt))`
//!   for the left one and `z. Path[.A = C](l(pt), z)` for the right one, whose
//!   rows are again the fixed and moving ones.
//! - in a singleton family `y. Path[.A = C](a, y)`, where no row above reads
//!   the path, by the word moved, as `then` appends on its first word: `tr(P,
//!   q, ε) ⇝ return q`, `tr(P, ⟨c⟩, ε) ⇝ c`, and `tr(P, q, ℓ ∷ p) ⇝ return ℓ ∷
//!   ⟨tr(P, q, p)⟩`, the rest's transport held as the value it returns, as the
//!   evaluator reads a stuck one under its letter.
//!
//! An endpoint's image of a letter is one image per occurrence of the binder,
//! the leftmost first, each appended after the one before by the transport in
//! `z. Path[.A = C](l(pt), z)`. Along one occurrence, the innermost function's
//! image is the loop arm its case carries for the letter's loop — inverted
//! along the family `z. Path[.A = C](z, l(pt))` for an inverse letter,
//! reflexivity for a case with no loop arm — or, for a case over another
//! argument, the branch that argument's constructor selects: the letter where
//! it returns the occurrence's argument, reflexivity where it ignores it, and
//! the run of that argument first where it is a call. A letter of a cell above
//! dimension one maps through `Path.ap` layers of a case, one per wrapping, to
//! that case's arm for the cell ([`cong_case`]): first the layers the endpoint
//! writes in place ([`layered`]), then the bodies of `Path.ap` the definitions
//! give.
//! Each further function's image of that word is its `cong`: the transport
//! along it in `y. Path[.A = C](l(pt), ⟨f y⟩)`. The functions are read through
//! the evaluator's admitted bodies, the reading cong fusion takes
//! ([`mod@crate::replay`]'s `Replay::fuse`): a loop obligation is decided
//! δ-free, and the image of a loop under a map out of the circle exists only in
//! its definition. A configuration no row reads sticks.
//!
//! **A carried endpoint maps a cell by its family's endpoints.** The endpoint
//! `⟨tr(x. Path[.A = C](l, r), y, b)⟩`, for the family's binder `y` and `b`
//! reflexivity, maps a cell as the evaluator reads it: `l`'s image inverted,
//! then `r`'s, each one `Path.ap` layer deeper ([`carried`],
//! [`carried_image`]). A `b` that holds a letter whiskers the images, and the
//! transport sticks.
//!
//! **A named word is read silently.** `loop` is a constant whose body is the
//! word of its letter, and a δ-free obligation meets it rigid. The reduct
//! reads the body in place, as the evaluator does, rather than through an
//! unfolding the replay's dialogue records: the engine's dialogue under a
//! stuck transport names no unfolding the replay could read, and a
//! transport-elimination step in the trace alphabet would change the artifact
//! for one reading. The reading is confined to transport's path and operand
//! and to a constant whose body is a constructor of a type of words, so no
//! other definition unfolds by it — with one exception the evaluator shares:
//! a returned operand the append rows read, a call held at its definition such
//! as `spin(Z)`, runs through each definition its run meets (the replay's
//! held run in `reduce`), as the evaluator's append runs a held operand.
//! Reversal: a recorded trace position under a transport's family, which would
//! let the engine record the unfolding.
//!
//! # References
//!
//! - `vault:01a1b48c-2d17-7fc1-80ce-cb35e5cffd0e` — background: § 2.2, the
//!   spheres as presentations with one cell per dimension, and the eliminator
//!   whose arm at the cell is a cell of the answer at the reflexivity of the
//!   arm at the point.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CellIndex;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FreeCells;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Reflexivities;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::build_side;
use quenchant_shape::shape::Maybe;

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
    /// The endpoint runs the binder through these calls, a route per
    /// occurrence of the binder.
    Through(Routes),
    /// The endpoint carries a value along the binder in a path family whose
    /// endpoints act in turn, read whole ([`carried`]).
    Carried(Carrying),
}

/// A carried endpoint read whole: the endpoint first, then the two endpoints
/// of each family a carried piece transports in, the left before the right,
/// so every piece stands before the pieces below it.
///
/// # Specification
/// - ensures: the first piece is [`Shape::Carried`]; each carried piece names
///   two later pieces, each one carried transport deeper.
/// - executable: none — the ids hold no arena to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — the family at the 3-sphere's cell carries the family at
///   the 2-cell, whose pieces stand one layer deeper again.
/// - witness: `tests::native_formers::a_carried_endpoint_maps_a_cell_6458`
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Carrying
{
    /// Every piece, each above the pieces it names.
    pieces: Vec<Piece>,
}

/// One endpoint of a [`Carrying`]: how it acts on a cell, and how many
/// carried transports stand around it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Piece
{
    /// The carried transports around the endpoint, each one `Path.ap` layer.
    depth: Reflexivities,
    /// How the endpoint acts on a cell.
    shape: Shape,
}

/// How one endpoint of a [`Carrying`] acts on a cell.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Shape
{
    /// The endpoint never reads its family's binder: the empty word.
    Fixed,
    /// The endpoint is its family's binder: the cell itself.
    Moving,
    /// The endpoint is one call of one argument, its layers raised by the
    /// piece's depth.
    Call(Routes),
    /// The endpoint carries a value along its family's binder: the inverse of
    /// the left piece's image, then the right piece's.
    Carried
    {
        /// The position of the left endpoint's piece.
        left: usize,
        /// The position of the right endpoint's piece.
        right: usize,
    },
}

/// One call of an endpoint's reading: the function, every argument it
/// applies in written order, and the call one of whose arguments it answers.
/// A call read through `Path.ap` written in place, `⟨tr(y. Path[.A = B](s,
/// ⟨f y⟩), q, here(s))⟩`, is the call `f q` under one layer per such
/// transport.
///
/// # Specification
/// - ensures: some argument of `arguments` reads the binder; `parent` names the
///   call this one answers an argument of and that argument's position, `None`
///   for the endpoint's own call; for a call bound after another, the one
///   argument is that call's result; a call under `Path.ap` layers has the
///   binder as its one argument.
/// - executable: none — the ids hold no arena to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — `mul(b, Base)` is one call of two arguments moving at the
///   first, and its loop arm reads the second as `Base`; `Path.ap f q` written
///   in place is `f` under one layer.
/// - witness: `tests::native_formers::a_loop_obligation_reads_a_map_of_two_arguments`
#[derive(Clone, Debug, Eq, PartialEq)]
struct Node
{
    /// The function called.
    function: ConstantIndex,
    /// Every argument the call applies, the first outermost, under the
    /// family's binder.
    arguments: Vec<ValueId>,
    /// The call whose argument this call answers, and that argument's
    /// position.
    parent: Option<(usize, usize)>,
    /// How many `Path.ap` layers written in place stand around the call.
    layers: Reflexivities,
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
///   and the image of the loop is the first's then the second's.
/// - witness: `tests::native_formers::a_loop_obligation_reads_both_arguments_of_a_diagonal_464`
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

/// How many arguments a function takes: the lambdas its body opens.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Arity(usize);

/// The calls along one route of an endpoint's [`Routes`], from the call the
/// binder is an argument of out to the endpoint's own, each with the position
/// of the argument the route moves it at.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
struct Walk<'routes>
{
    /// The routes walked.
    routes: &'routes Routes,
    /// The call and argument position the next step reads.
    next: Option<(usize, usize)>,
}

impl<'routes> Iterator for Walk<'routes>
{
    type Item = (&'routes Node, Argument);

    /// The next call out along the route, or `None` once the route has left
    /// the endpoint's own call.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> Option<Self::Item>
    {
        let (node, moving) = self.next.take()?;
        let found = self.routes.nodes.get(node)?;
        self.next = found.parent;
        Some((found, Argument(moving)))
    }
}

impl Routes
{
    /// One [`Walk`] per occurrence of the binder, the leftmost first.
    ///
    /// # Specification
    /// trivial.
    fn walks(&self) -> impl Iterator<Item = Walk<'_>>
    {
        self.leaves.iter().map(|&leaf| Walk {
            routes: self,
            next: Some(leaf),
        })
    }
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
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
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
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
/// - witness: `tests::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
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
        Some(&Value::Here { .. }) => Head::Empty,
        Some(&Value::Constructor {
            datatype,
            tag,
            ref fields,
            ..
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
                [rest] => Head::Letter { tag, words, rest },
                _ => Head::Other,
            }
        },
        _ => Head::Other,
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
///   words, and a word of four letters moves whole to its letters' images.
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
/// - witness: `tests::native_formers::a_closed_word_moves_whole_to_its_letters_images`
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
            Head::Empty => return Some((letters, at)),
            Head::Letter { rest, .. } => {
                letters.push(at);
                at = rest;
            },
            Head::Other => return None,
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
/// - witness: `tests::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
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
    let Some(&Value::Constructor {
        family, datatype, ..
    }) = arena.value(letter)
    else {
        return None;
    };
    Some(arena.value_constructor(family, datatype, tag, Vec::from([rest])))
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
/// - hypothesis: L3 — conjugation at `Path[.A = Circle](x, x)` inverts the loop
///   on the left; a word left uninverted would not cancel.
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
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
/// - hypothesis: L3 — reflexivity at `Path[.A = Circle](Base, x)` becomes the
///   loop only when the empty word is spliced before it.
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
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
///   endpoint that ignores it; [`Action::Through`] for calls [`routes`] reads;
///   `None` otherwise, a carried endpoint included, which [`carried`] reads.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each witness family reads one action per endpoint: the
///   point fixed, `x` moving, and the flip's and the collapse's calls as
///   routes; a misread action carries the answer elsewhere.
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
/// - witness: `tests::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| match ret {
    Some(Action::Moving) => matches!(arena.value(endpoint), Some(&Value::Variable(_))),
    Some(Action::Through(ref read)) => !read.leaves.is_empty(),
    Some(Action::Carried(_)) => false,
    Some(Action::Fixed) | None => arena.value(endpoint).is_some(),
})]
fn action(
    arena: &TermArena,
    endpoint: ValueId,
) -> Option<Action>
{
    if matches!(arena.value(endpoint), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
    {
        return Some(Action::Moving);
    }
    if binder_use(arena, Family::Value(endpoint)) == BinderUse::Ignored {
        return Some(Action::Fixed);
    }
    routes(arena, endpoint).map(Action::Through)
}

/// An endpoint that carries a value along the binder, read whole, when every
/// endpoint below it acts on a cell.
///
/// # Specification
/// - requires: `endpoint` is read under the family's one binder.
/// - ensures: `Some(carrying)` exactly when [`transported`] reads the endpoint
///   as a transport in a family, and each endpoint below it — the family's two,
///   and in turn the two of each family read below — is its family's binder,
///   ignores it, is one call of one argument as [`routes`] reads it, or is a
///   transport [`transported`] reads; each piece's depth counts the carried
///   transports around it, and a call's layers are raised by it; `None`
///   otherwise. The engine's evaluator reads the same endpoints.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `while` takes one pending family per turn, each pending only
///   the families its endpoints transport in, strict subterms.
/// - measure: the endpoint's nodes left.
///
/// # Adequacy
/// - hypothesis: L3 — the family at the 2-sphere's cell carries its answer
///   along its binder in `x. Path[.A = S2](x, x)`, and the family at the
///   3-sphere's cell the 2-cell's family in turn; a carried endpoint left
///   unread leaves the obligation stuck, and a depth misread maps the cell
///   through the wrong case.
/// - witness: `tests::native_formers::a_carried_endpoint_maps_a_cell_6458`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|read| matches!(read.pieces.first(), Some(&Piece { shape: Shape::Carried { .. }, .. }))))]
fn carried(
    arena: &TermArena,
    presentations: &Presentations,
    endpoint: ValueId,
) -> Option<Carrying>
{
    let binder = DeBruijnIndex::from(0_u32);
    let root = transported(arena, presentations, endpoint)?;
    let mut pieces = Vec::from([Piece {
        depth: Reflexivities::NONE,
        shape: Shape::Fixed,
    }]);
    let mut pending = Vec::from([(root, 0_usize)]);
    while let Some((family, at)) = pending.pop() {
        let &ValueType::Path { left, right, .. } = arena.value_type(family)?
        else {
            return None;
        };
        let depth = Reflexivities::from(usize::from(pieces.get(at)?.depth).saturating_add(1));
        let first = pieces.len();
        for side in [left, right] {
            let shape = if matches!(arena.value(side), Some(&Value::Variable(index)) if index == binder)
            {
                Shape::Moving
            }
            else if binder_use(arena, Family::Value(side)) == BinderUse::Ignored {
                Shape::Fixed
            }
            else if let Some(mut read) = routes(arena, side) {
                // A cell maps through one call of one argument: the `Path.ap`
                // layers act on a cell, and a chain's later calls act on a
                // loop.
                let [ref mut node] = *read.nodes.as_mut_slice()
                else {
                    return None;
                };
                let [_] = *node.arguments.as_slice()
                else {
                    return None;
                };
                node.layers = Reflexivities::from(
                    usize::from(node.layers).saturating_add(usize::from(depth)),
                );
                Shape::Call(read)
            }
            else {
                // The piece is rewritten when its own family is read.
                pending.push((transported(arena, presentations, side)?, pieces.len()));
                Shape::Fixed
            };
            pieces.push(Piece { depth, shape });
        }
        pieces.get_mut(at)?.shape = Shape::Carried {
            left: first,
            right: first.saturating_add(1),
        };
    }
    Some(Carrying { pieces })
}

/// The family of a transport an endpoint carries along the binder.
///
/// The transport of `b` along `q` in `x. Path[.A = C](l, r)` is the
/// conjugation `ap(l, q)⁻¹ · b · ap(r, q)` for every `b`. The rule reduces it
/// only at reflexivity: a `b` that holds a letter whiskers the two images, and
/// the transport stays held.
///
/// # Specification
/// - requires: `endpoint` is read under its family's binder `y`.
/// - ensures: `Some(A)` exactly when the endpoint is `⟨tr(A, y, b)⟩`, `A` is a
///   path family `x. Path[.A = C](l, r)` that never reads `y` and whose carrier
///   `C` reads neither `x` nor `y`, and `b` reads as the empty word ([`head`])
///   and ignores `y`; `None` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the family at the 2-sphere's cell carries reflexivity at
///   the point along its binder; read with any other operand, the conjugation
///   would drop a whiskering.
/// - witness: `tests::native_formers::a_carried_endpoint_maps_a_cell_6458`
#[spec(ensures: |ret| ret.is_none_or(|family| matches!(arena.value_type(family), Some(&ValueType::Path { .. }))))]
fn transported(
    arena: &TermArena,
    presentations: &Presentations,
    endpoint: ValueId,
) -> Option<ValueTypeId>
{
    let &Value::Returned(call) = arena.value(endpoint)?
    else {
        return None;
    };
    let &Computation::PathTransport {
        motive: family,
        path,
        value,
    } = arena.computation(call)?
    else {
        return None;
    };
    if !matches!(arena.value(path), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
        || head(arena, presentations, value) != Head::Empty
        || binder_use(arena, Family::Value(value)) != BinderUse::Ignored
    {
        return None;
    }
    let &ValueType::Path {
        domain: carrier, ..
    } = arena.value_type(family)?
    else {
        return None;
    };
    // Inside the family, its own binder is index 0 and `y` index 1.
    let carrying = DeBruijnIndex::from(1_u32);
    let Maybe::Present(mut read) = arena.value_type_support(family).indices()
    else {
        return None;
    };
    if read.any(|index| index == carrying) {
        return None;
    }
    let Maybe::Present(mut read) = arena.value_type_support(carrier).indices()
    else {
        return None;
    };
    if read.any(|index| index <= carrying) {
        return None;
    }
    Some(family)
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
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `while` takes one pending call or leaf per turn, each call
///   pending its arguments' strict subterms only, never recursing.
/// - measure: the endpoint's nodes left.
///
/// # Adequacy
/// - hypothesis: L3 — the flip applied twice reads as one route of two calls
///   and the flip once as one call, which the witness tells apart by their
///   verdicts; `mul(b, Base)` reads as one call of two arguments moving at the
///   first; `mul(mul(b, Base), invLooper(b))` as two routes.
/// - witness: `tests::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
/// - witness: `tests::native_formers::a_loop_obligation_reads_a_map_of_two_arguments`
/// - witness: `tests::native_formers::a_loop_obligation_reads_both_arguments_of_a_diagonal_464`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|read| !read.leaves.is_empty()
    && read.leaves.iter().all(|&(node, position)| read.nodes.get(node).is_some_and(|node| position < node.arguments.len()))))]
fn routes(
    arena: &TermArena,
    endpoint: ValueId,
) -> Option<Routes>
{
    let Some(&Value::Returned(call)) = arena.value(endpoint)
    else {
        return None;
    };
    let binder = DeBruijnIndex::from(0_u32);
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
        if let Some(&Computation::Bind(first, then)) = arena.computation(call) {
            let (function, arguments) = spine(arena, then)?;
            let [argument] = *arguments.as_slice()
            else {
                return None;
            };
            if !matches!(arena.value(argument), Some(&Value::Variable(index)) if index == binder) {
                return None;
            }
            read.nodes.push(Node {
                function,
                arguments,
                parent,
                layers: Reflexivities::NONE,
            });
            pending.push(Pending::Call(first, Some((at, 0))));
            continue;
        }
        if let Some((function, layers, along)) = layered(arena, call) {
            // `Path.ap` written in place along the binder: the call it layers,
            // moving at its one argument.
            if !matches!(arena.value(along), Some(&Value::Variable(index)) if index == binder) {
                return None;
            }
            pending.push(Pending::Leaf(at, 0));
            read.nodes.push(Node {
                function,
                arguments: Vec::from([along]),
                parent,
                layers,
            });
            continue;
        }
        let (function, arguments) = spine(arena, call)?;
        // The arguments last first, so the leftmost is read first.
        let mut moves = false;
        for (position, &argument) in arguments.iter().enumerate().rev() {
            if binder_use(arena, Family::Value(argument)) == BinderUse::Ignored {
                continue;
            }
            moves = true;
            if matches!(arena.value(argument), Some(&Value::Variable(index)) if index == binder) {
                pending.push(Pending::Leaf(at, position));
            }
            else if let Some(&Value::Returned(inner)) = arena.value(argument) {
                pending.push(Pending::Call(inner, Some((at, position))));
            }
            else {
                return None;
            }
        }
        if !moves {
            return None;
        }
        read.nodes.push(Node {
            function,
            arguments,
            parent,
            layers: Reflexivities::NONE,
        });
    }
    Some(read)
}

/// The call `call` layers when it is `Path.ap` written in place, one or more
/// times: the function, how many layers, and the path the outermost layer
/// moves along.
///
/// Each layer is the transport `tr(y. Path[.A = B](s, ⟨e⟩), q, here(s))`
/// whose `e` is the next layer along `y`, the innermost `e` the call `force f
/// y`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some((f, n, q))` exactly when `call` is `n` such layers, `n` at
///   least one, around `force f y` for a constant `f`, `q` the outermost
///   transport's path; `None` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` opens one layer per turn.
/// - measure: the layers left inside `call`.
///
/// # Adequacy
/// - hypothesis: L3 — `Path.ap` of the sphere's identity on the 2-cell is the
///   identity under one layer, as the evaluator reads it.
/// - witness: `tests::native_formers::a_map_s_image_of_a_2_cell_in_place_is_its_arm`
#[spec(ensures: |ret| ret.is_none_or(|(_, layers, _)| layers != Reflexivities::NONE))]
fn layered(
    arena: &TermArena,
    call: ComputationId,
) -> Option<(ConstantIndex, Reflexivities, ValueId)>
{
    let innermost = |value: ValueId| matches!(arena.value(value), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32));
    let (mut body, mut layers, mut along) = (call, 0_usize, None);
    while let Some(&Computation::PathTransport { motive, path, .. }) = arena.computation(body) {
        if along.is_some() && !innermost(path) {
            return None;
        }
        along = along.or(Some(path));
        let &ValueType::Path { right, .. } = arena.value_type(motive)?
        else {
            return None;
        };
        let &Value::Returned(inner) = arena.value(right)?
        else {
            return None;
        };
        body = inner;
        layers = layers.saturating_add(1);
    }
    let (function, arguments) = spine(arena, body)?;
    let [argument] = *arguments.as_slice()
    else {
        return None;
    };
    (layers > 0 && innermost(argument)).then_some((function, Reflexivities::from(layers), along?))
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
/// - witness: `tests::native_formers::a_loop_obligation_reads_a_map_of_two_arguments`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|&(_, ref arguments)| !arguments.is_empty()))]
fn spine(
    arena: &TermArena,
    call: ComputationId,
) -> Option<(ConstantIndex, Vec<ValueId>)>
{
    let mut arguments = Vec::new();
    let mut head = call;
    while let Some(&Computation::Application(inner, argument)) = arena.computation(head) {
        arguments.push(argument);
        head = inner;
    }
    let Some(&Computation::Force(function)) = arena.computation(head)
    else {
        return None;
    };
    let Some(&Value::Constant(constant)) = arena.value(function)
    else {
        return None;
    };
    if arguments.is_empty() {
        return None;
    }
    arguments.reverse();
    Some((constant, arguments))
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
/// - witness: `tests::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| ret.is_none_or(|built| matches!(arena.value(built), Some(&Value::Constructor { .. }))))]
pub fn point(
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
        RuleNode::Constructor(tag) => arena.value_constructor(cells.sort(), sort, tag, fields),
        RuleNode::Variable(_) => {
            open = true;
            arena.value_unit()
        },
    })
    .ok()?;
    (!open).then_some(built)
}

/// The carrier and endpoints of the path a transport follows, read off its
/// type `ty`: a parameterless type of words is the path at its cells' point,
/// `Path_U(x, y)` is the path from `x` to `y` in the level-zero value universe,
/// and any other type is read as [`crate::element_identity::path_parts`] reads
/// it.
///
/// A cell above dimension one stands at its point's reflexivity, so its words
/// follow a path one path type up per wrapping: a 2-cell's words follow a
/// path in `Path[.A = S](pt, pt)` from `here(pt)` to `here(pt)`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for `ty` a `Data(words, [])` whose presentation carries free
///   cells over the sort `S` looping at the closed point `pt` ([`point`]),
///   `(Data(S, []), pt, pt)` wrapped once per reflexivity of the cells, each
///   wrapping taking `(C, x, x)` to `(Path[.A = C](x, x), here(x), here(x))`:
///   the path type `Presentations::words` reads as those words; `(U₀, x, y)`
///   for `ty` a `PathUniverse(x, y)`, the level-zero value universe at which
///   `Path[.A = U₀](x, y)` and `Path_U(x, y)` are two readings of one
///   classifier, as `equiv` checks at either; the parts of a `Path` type
///   otherwise.
/// - provides: the reading the element and telescope transports give the path
///   they follow, the checker's own.
/// - fails: the value-shape mismatch naming `ty` for any other type.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Termination
/// - reason: one `for` over the cells' wrappings.
/// - measure: the wrappings left.
///
/// # Adequacy
/// - hypothesis: L3 — a composite and an inverse transported along a word
///   written inline admit at the circle's point and refuse at the wrong
///   endpoints; reading the words as their own type refuses by shape; a list
///   transported along a native path written in place admits as along one
///   declared at the identity; `Path.ap` of a map along a word of a 2-cell's
///   words written in place admits at the point's reflexivity.
/// - witness: `tests::native_formers::a_word_written_as_a_transport_path_is_that_path`
/// - witness: `tests::native_formers::a_map_s_image_of_a_written_2_cell_word_is_that_word`
/// - witness: `path_universe::tests::an_element_transport_follows_a_native_path_written_in_place_1064`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|&(domain, left, right)|
    matches!(arena.value_type(ty), Some(&ValueType::Path { domain: d, left: l, right: r }) if d == domain && l == left && r == right)
        || (matches!(arena.value_type(ty), Some(&ValueType::PathUniverse(l, r)) if l == left && r == right)
            && matches!(arena.value_type(domain), Some(&ValueType::Universe { sort: GroundSort::Value, ref level }) if *level == Level::zero()))
        || (left == right && matches!(arena.value(left), Some(&Value::Constructor { .. } | &Value::Here { .. })))))]
pub fn followed(
    arena: &mut TermArena,
    presentations: &Presentations,
    ty: ValueTypeId,
) -> Result<(ValueTypeId, ValueId, ValueId), crate::error::KernelError>
{
    if let Some(&ValueType::Data {
        declaration: words,
        ref arguments,
    }) = arena.value_type(ty)
        && arguments.is_empty()
        && let Some(cells) = presentations
            .presented(words)
            .and_then(crate::presented::PresentedType::cells)
        && let Some(point) = point(arena, presentations, words)
    {
        let (mut carrier, mut at) = (arena.value_type_data(cells.sort(), Vec::new()), point);
        for _ in 0 .. usize::from(cells.reflexivities()) {
            carrier = arena.value_type_path(carrier, at, at);
            at = arena.value_here(at);
        }
        return Ok((carrier, at, at));
    }
    if let Some(&ValueType::PathUniverse(source, target)) = arena.value_type(ty) {
        let carrier = arena.value_type_universe(GroundSort::Value, Level::zero());
        return Ok((carrier, source, target));
    }
    crate::element_identity::path_parts(arena, ty)
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

/// The data case a definition's body is, under one lambda per argument, and
/// the position of the argument it is over, or `None` for a definition whose
/// body is no such case.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some((case, over))` exactly when `unfoldings` holds `function`'s
///   body as the thunk of `count` lambdas over the data case `case` whose
///   scrutinee is the variable of argument `over`, the first argument
///   outermost.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` opens a lambda per argument.
/// - measure: the arguments left.
///
/// # Adequacy
/// - hypothesis: L3 — `mul`'s case is over its first argument, which the loop
///   moves along one route of `mul(mul(b, Base), invLooper(b))` and leaves at
///   the point along the other.
/// - witness: `tests::native_formers::a_loop_obligation_reads_both_arguments_of_a_diagonal_464`
#[spec(ensures: |ret| ret.is_none_or(|(case, over)| over.0 < arguments.len() && matches!(arena.computation(case), Some(&Computation::DataCase { .. }))))]
fn case_of(
    arena: &TermArena,
    unfoldings: &Unfoldings,
    (function, arguments): (ConstantIndex, &[ValueId]),
) -> Option<(ComputationId, Argument)>
{
    let Unfoldable::Body(body) = unfoldings.unfolding(function)
    else {
        return None;
    };
    let Some(&Value::Thunk(mut case)) = arena.value(body)
    else {
        return None;
    };
    for _argument in arguments {
        let Some(&Computation::Lambda(inner)) = arena.computation(case)
        else {
            return None;
        };
        case = inner;
    }
    let Some(&Computation::DataCase { scrutinee, .. }) = arena.computation(case)
    else {
        return None;
    };
    let Some(&Value::Variable(index)) = arena.value(scrutinee)
    else {
        return None;
    };
    let over = arguments
        .len()
        .checked_sub(usize::try_from(u32::from(index)).ok()?)?
        .checked_sub(1)?;
    Some((case, Argument(over)))
}

/// The data case a definition reaches through `Path.ap` layers, one per
/// wrapping of a cell's point: the case a cell above dimension one maps by.
///
/// A call `g(… q …)` whose body is `Path.ap f q` along its argument `q` acts
/// on a 2-cell as `f` acts on it: `Path.ap g` of the 2-cell is `f`'s arm for
/// it. Each wrapping takes one such layer, so a 3-cell reads through two.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some(case)` exactly when `function`, of `count` arguments,
///   through `wrapping` layers, each a thunk of one lambda per argument whose
///   body is the transport `tr(y. Path[.A = B](s, ⟨force h y⟩), q, here(s))`
///   along the argument at `moving` for a constant `h` of one argument, reaches
///   a constant whose body is a data case on its one argument; `case` is that
///   case. `None` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `for` reads one layer per wrapping.
/// - measure: the wrappings left.
///
/// # Adequacy
/// - hypothesis: L3 — `Path.ap` of the sphere's identity on its loops maps the
///   2-cell to the identity's arm for it, `surf`, as the evaluator maps it.
/// - witness: `tests::native_formers::a_map_s_image_of_a_2_cell_in_place_is_its_arm`
#[spec(ensures: |ret| ret.is_none_or(|case| matches!(arena.computation(case), Some(&Computation::DataCase { .. }))))]
fn cong_case(
    arena: &TermArena,
    unfoldings: &Unfoldings,
    (function, arity): (ConstantIndex, Arity),
    (moving, wrapping): (Argument, Reflexivities),
) -> Option<ComputationId>
{
    let bound = |value: ValueId, at: usize| {
        matches!(arena.value(value), Some(&Value::Variable(index))
            if usize::try_from(u32::from(index)).ok() == Some(at))
    };
    let (mut function, mut arity, mut along) = (function, arity, moving.0);
    for _ in 0 .. usize::from(wrapping) {
        let body = lambdas(arena, unfoldings, (function, arity))?;
        let Some(&Computation::PathTransport { motive, path, .. }) = arena.computation(body)
        else {
            return None;
        };
        if !bound(path, arity.0.checked_sub(along)?.checked_sub(1)?) {
            return None;
        }
        let Some(&ValueType::Path { right, .. }) = arena.value_type(motive)
        else {
            return None;
        };
        let Some(&Value::Returned(applied)) = arena.value(right)
        else {
            return None;
        };
        let Some(&Computation::Application(forced, argument)) = arena.computation(applied)
        else {
            return None;
        };
        let Some(&Computation::Force(head)) = arena.computation(forced)
        else {
            return None;
        };
        let Some(&Value::Constant(inner)) = arena.value(head)
        else {
            return None;
        };
        if !bound(argument, 0) {
            return None;
        }
        (function, arity, along) = (inner, Arity(1), 0);
    }
    let body = lambdas(arena, unfoldings, (function, arity))?;
    let Some(&Computation::DataCase { scrutinee, .. }) = arena.computation(body)
    else {
        return None;
    };
    bound(scrutinee, 0).then_some(body)
}

/// The body of the constant `function` under its `arity` lambdas.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some(body)` exactly when `unfoldings` holds the constant's body
///   as a thunk of `arity` lambdas around `body`.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `for` opens one lambda per count.
/// - measure: the lambdas left.
///
/// # Adequacy
/// - hypothesis: L3 — as [`cong_case`].
/// - witness: `tests::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| ret.is_none_or(|body| arena.computation(body).is_some()))]
fn lambdas(
    arena: &TermArena,
    unfoldings: &Unfoldings,
    (function, arity): (ConstantIndex, Arity),
) -> Option<ComputationId>
{
    let Unfoldable::Body(body) = unfoldings.unfolding(function)
    else {
        return None;
    };
    let Some(&Value::Thunk(mut body)) = arena.value(body)
    else {
        return None;
    };
    for _ in 0 .. arity.0 {
        let Some(&Computation::Lambda(inner)) = arena.computation(body)
        else {
            return None;
        };
        body = inner;
    }
    arena.computation(body).map(|_| body)
}

/// The arm `case` carries for the loop of `cell` in `words`, its arguments
/// instantiated — the one the case is over, `moving`, at the loop's point,
/// each other at `fixed` — or `None` for a case whose arms are not one per
/// constructor of the words' sort and one per loop.
///
/// # Specification
/// - requires: `case` is a definition's data case over its argument `moving`,
///   read by [`case_of`]; `fixed` holds one value per argument, standing where
///   the transport does.
/// - ensures: as the summary, the case's arms after one per constructor of the
///   words' sort taken in [`Presentations::looping`]'s order.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` substitutes one argument per turn.
/// - measure: the arguments left.
///
/// # Adequacy
/// - hypothesis: L3 — the flip's written arm and the collapse's unwritten one
///   decide the flip twice and the collapse admitted and the flip once refused;
///   `mul`'s arm reads its second argument at the value the call passes.
/// - witness: `tests::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
/// - witness: `tests::native_formers::a_loop_obligation_reads_a_map_of_two_arguments`
#[spec(ensures: |ret| ret.is_none_or(|arm| match arm { Arm::Written(written) => arena.computation(written).is_some(), Arm::Unwritten => true }))]
fn loop_arm<M>(
    arena: &mut TermArena,
    (table, memo): (&mut ContentTable, &mut M),
    presentations: &Presentations,
    (case, moving, fixed): (ComputationId, Argument, &[ValueId]),
    (words, cell): (ConstantIndex, CellIndex),
) -> Option<Arm>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let Some(&Computation::DataCase { ref branches, .. }) = arena.computation(case)
    else {
        return None;
    };
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
    let mut arm = *branches.get(constructors.checked_add(offset)?)?;
    let at = point(arena, presentations, words)?;
    // The innermost argument first: each substitution leaves the arm under
    // the arguments before it, which the value is lifted past.
    for position in (0 .. fixed.len()).rev() {
        let value = if Argument(position) == moving {
            at
        }
        else {
            *fixed.get(position)?
        };
        let depth = BinderDepth::from(u32::try_from(position).ok()?);
        let lifted = shift_value(arena, table, memo, value, BinderDepth::NONE, depth);
        arm = substitute_computation(arena, table, memo, arm, lifted);
    }
    Some(Arm::Written(arm))
}

/// A loop arm read as the evaluator's mapping reads it: an arm that returns a
/// cell's name, `loop`, answers the name's word.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Written(return w)` when `arm` is `Written(return n)` and
///   [`named`] reads `n` as the word `w`; `arm` otherwise.
/// - provides: the image of a loop under a map whose loop arm is a cell's name,
///   as the evaluator's `mapped` (`gandr-core-nbe`'s `eval::words::mapped`)
///   computes it before it inverts or splices the image.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the evaluator splices the word that the name `loop`
///   names, and the checker's dialogue compares that word. Kept as the name,
///   the image sticks at the name, the dialogue's next decision does not apply,
///   and the kernel refuses what the checker accepted.
/// - witness: `replay::tests::a_named_loop_arm_answers_its_word_5489`
#[spec(ensures: |ret| match (arm, ret) {
    (Arm::Unwritten, Arm::Unwritten) => true,
    (Arm::Written(_), Arm::Written(read)) => arena.computation(read).is_some(),
    _ => false,
})]
fn answered(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    arm: Arm,
) -> Arm
{
    let Arm::Written(written) = arm
    else {
        return arm;
    };
    let Some(&Computation::Return(answer)) = arena.computation(written)
    else {
        return arm;
    };
    named(arena, unfoldings, answer)
        .map_or(arm, |word| Arm::Written(arena.computation_return(word)))
}

/// What a case over an argument the loop leaves standing makes of the moving
/// one, the branch its argument's constructor selects read under a binder for
/// the moving argument: the letter itself where the branch returns that
/// binder, the empty word where it ignores it, the run of the selecting
/// argument before the call's cong where that argument is a call; `None`
/// otherwise.
///
/// # Specification
/// - requires: `case` is a definition's data case over its argument `over`,
///   read by [`case_of`]; `fixed` holds one value per argument, standing where
///   the transport does; `moving` differs from `over`; `(carrier, fixed)` a
///   carrier and a value standing there; `letter` a one-letter word and `rest`
///   its empty word.
/// - ensures: for `fixed[over]` a constructor, `return letter` when its branch,
///   its fields and the arguments substituted and the moving one a binder `y`,
///   is `return y`, and `return rest` when it is `return v` for a `v` that
///   ignores `y`; for `fixed[over]` the returned call `⟨c⟩`, `x ← c; tr(y.
///   Path[.A = C](fixed, ⟨f … x … y …⟩), letter, here(fixed))`, the case's
///   function applied at `x` where the case is over and at `y` where the letter
///   moves, which the next step reads at `x`'s constructor; `None` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` opens a lambda per field and substitutes one per turn,
///   another substitutes one argument per turn.
/// - measure: the fields left, then the arguments left.
///
/// # Adequacy
/// - hypothesis: L3 — `mul(⟨mul(Base, Base)⟩, y)` runs its first argument, and
///   at `Base` the branch is the second: the loop through `mul`'s second
///   argument is itself, the second route of `rotInv1`'s diagonal.
/// - witness: `tests::native_formers::a_loop_obligation_reads_both_arguments_of_a_diagonal_464`
#[spec(ensures: |ret| ret.is_none_or(|built| arena.computation(built).is_some()))]
fn select<M>(
    arena: &mut TermArena,
    (table, memo): (&mut ContentTable, &mut M),
    (function, case): (ConstantIndex, ComputationId),
    (over, moving, fixed): (Argument, Argument, &[ValueId]),
    (letter, rest, (carrier, standing)): (ValueId, ValueId, (ValueTypeId, ValueId)),
) -> Option<ComputationId>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let selector = *fixed.get(over.0)?;
    let count = fixed.len();
    if let Some(&Value::Returned(call)) = arena.value(selector) {
        // `x ← c; tr(y. Path[.A = C](fixed, ⟨f … x … y …⟩), letter, here(fixed))`:
        // `x` one binder in, `y` two.
        let two = BinderDepth::from(2_u32);
        let one = BinderDepth::from(1_u32);
        let named = arena.value_constant(function);
        let mut applied = arena.computation_force(named);
        for (position, &argument) in fixed.iter().enumerate() {
            let passed = if Argument(position) == moving {
                arena.value_variable(DeBruijnIndex::from(0_u32))
            }
            else if Argument(position) == over {
                arena.value_variable(DeBruijnIndex::from(1_u32))
            }
            else {
                shift_value(arena, table, memo, argument, BinderDepth::NONE, two)
            };
            applied = arena.computation_application(applied, passed);
        }
        let endpoint = arena.value_returned(applied);
        let lifted_carrier = shift_value_type(arena, table, memo, carrier, BinderDepth::NONE, two);
        let lifted_standing = shift_value(arena, table, memo, standing, BinderDepth::NONE, two);
        let family = arena.value_type_path(lifted_carrier, lifted_standing, endpoint);
        let moved = shift_value(arena, table, memo, letter, BinderDepth::NONE, one);
        let start_standing = shift_value(arena, table, memo, standing, BinderDepth::NONE, one);
        let start = arena.value_here(start_standing);
        let cong = arena.computation_path_transport(family, moved, start);
        return Some(arena.computation_bind(call, cong));
    }
    let Some(&Value::Constructor {
        tag, ref fields, ..
    }) = arena.value(selector)
    else {
        return None;
    };
    let fields = fields.clone();
    let Some(&Computation::DataCase { ref branches, .. }) = arena.computation(case)
    else {
        return None;
    };
    let mut branch = *branches.get(usize::from(tag))?;
    for _field in &fields {
        let Some(&Computation::Lambda(inner)) = arena.computation(branch)
        else {
            return None;
        };
        branch = inner;
    }
    // The innermost first: the fields under every argument and the fields
    // before them, then the arguments under those before them, all under the
    // moving argument's binder `y`, which stands outside the arguments.
    for (position, &field) in fields.iter().enumerate().rev() {
        let depth =
            BinderDepth::from(u32::try_from(count.checked_add(position)?.checked_add(1)?).ok()?);
        let lifted = shift_value(arena, table, memo, field, BinderDepth::NONE, depth);
        branch = substitute_computation(arena, table, memo, branch, lifted);
    }
    for position in (0 .. count).rev() {
        let lifted = if Argument(position) == moving {
            arena.value_variable(DeBruijnIndex::from(u32::try_from(position).ok()?))
        }
        else {
            let depth = BinderDepth::from(u32::try_from(position.checked_add(1)?).ok()?);
            shift_value(
                arena,
                table,
                memo,
                *fixed.get(position)?,
                BinderDepth::NONE,
                depth,
            )
        };
        branch = substitute_computation(arena, table, memo, branch, lifted);
    }
    let Some(&Computation::Return(answer)) = arena.computation(branch)
    else {
        return None;
    };
    if matches!(arena.value(answer), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
    {
        return Some(arena.computation_return(letter));
    }
    if binder_use(arena, Family::Value(answer)) == BinderUse::Ignored {
        return Some(arena.computation_return(rest));
    }
    None
}

/// The family `z. Path[.A = C](z, fixed)` or `z. Path[.A = C](fixed, z)`, read
/// `depth` binders under where `carrier` and `fixed` stand, the moving endpoint
/// on `moving`'s side.
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
        gandr_kernel_term::Side::Left => arena.value_type_path(carrier, bound, fixed),
        gandr_kernel_term::Side::Right => arena.value_type_path(carrier, fixed, bound),
    }
}

/// The image of the one-letter word `letter` under an endpoint's calls, as a
/// computation returning the image word: each route's image, the leftmost
/// first, appended — `ap` through each occurrence of the binder in turn, the
/// others standing at the point — or `None` when a route reads no further.
///
/// # Specification
/// - requires: `letter` is a one-letter word; `(carrier, fixed)` a carrier and
///   a value standing where the transport does; `at` the loop's point there;
///   `routes` read by [`routes`] under the family's binder.
/// - ensures: the first route's [`route_image`], and each later route's bound
///   after it and appended to it, `tr(z. Path[.A = C](fixed, z), wₖ, w)`.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` over the routes, not recursion.
/// - measure: the routes left.
///
/// # Adequacy
/// - hypothesis: L3 — `mul(mul(b, Base), invLooper(b))` moves the loop through
///   the outer `mul`'s first argument, then its second: `loop` then
///   `back(loop)`, which the obligation over `b` reads as the empty word.
/// - witness: `tests::native_formers::a_loop_obligation_reads_both_arguments_of_a_diagonal_464`
#[spec(ensures: |ret| ret.is_none_or(|built| arena.computation(built).is_some()) && (ret.is_none() || !routes.leaves.is_empty()))]
fn image<M>(
    arena: &mut TermArena,
    (table, memo): (&mut ContentTable, &mut M),
    unfoldings: &Unfoldings,
    (routes, at): (&Routes, ValueId),
    (letter, (carrier, fixed)): (ValueId, (ValueTypeId, ValueId)),
) -> Option<ComputationId>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let mut built = None;
    for walk in routes.walks() {
        let next = route_image(
            arena,
            (table, memo),
            unfoldings,
            (walk, at),
            (letter, (carrier, fixed)),
        )?;
        built = Some(built.map_or(next, |before| {
            // `w · wₖ`: `wₖ` bound one binder in, `w` two, the append the
            // transport of `w` along `wₖ` in `z. Path[.A = C](fixed, z)`.
            let one = BinderDepth::from(1_u32);
            let lifted = shift_computation(arena, table, memo, next, BinderDepth::NONE, one);
            let family = path_family(
                arena,
                (table, memo),
                (carrier, fixed),
                gandr_kernel_term::Side::Right,
                BinderDepth::from(2_u32),
            );
            let along = arena.value_variable(DeBruijnIndex::from(0_u32));
            let start = arena.value_variable(DeBruijnIndex::from(1_u32));
            let appended = arena.computation_path_transport(family, along, start);
            let after = arena.computation_bind(lifted, appended);
            arena.computation_bind(before, after)
        }));
    }
    built
}

/// The image of the closed word `letters` under an endpoint's calls, as a
/// computation returning the image word: the images of its letters in order,
/// as [`image`] gives each, the image of each distinct letter computed once.
///
/// The images bind first, one binder per distinct letter. The word's image
/// then gathers inverted, from `here(fixed)`: each letter's step transports
/// the image so far along that letter's image in `z. Path[.A = C](z, fixed)`,
/// which puts the inverse of the letter's image before it and copies that
/// image alone. The steps nest to the left, so each continuation stands under
/// the same binders and the replay unloads a term of constant size at each
/// step. A last transport along the gathered word from `here(fixed)` inverts
/// it once.
///
/// # Specification
/// - requires: as [`image`]; `letters` are the letters of the closed word
///   `path`, first to last, at least one.
/// - ensures: `x₁ ← I₁; …; xₖ ← Iₖ; F` for the images `Iⱼ` of the `k` distinct
///   one-letter words, where `F` moves `here(fixed)` along `xⱼ` for each letter
///   in turn and then along the gathered word; `None` when [`image`] gives no
///   image of some letter, or `path` is no constructor.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` over the letters, one over the distinct letters, and one
///   over their images, not recursion.
/// - measure: the letters left, then the distinct letters left.
///
/// # Adequacy
/// - hypothesis: L3 — the identity's image of a word of four letters, two of
///   them distinct, is the word, and the flip's is each letter inverted in
///   place; the gathered word read back uninverted is the image's inverse,
///   which the claim refuses.
/// - witness: `tests::native_formers::a_closed_word_moves_whole_to_its_letters_images`
#[spec(ensures: |ret| ret.is_none_or(|built| arena.computation(built).is_some()))]
fn word_image<M>(
    arena: &mut TermArena,
    (table, memo): (&mut ContentTable, &mut M),
    unfoldings: &Unfoldings,
    (routes, at): (&Routes, ValueId),
    (letters, path): (&[ValueId], ValueId),
    (carrier, fixed): (ValueTypeId, ValueId),
) -> Option<ComputationId>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let presentations = unfoldings.presentations();
    let &Value::Constructor {
        family, datatype, ..
    } = arena.value(path)?
    else {
        return None;
    };
    // Each letter's position among the distinct letters, first seen first.
    let mut distinct: Vec<ConstructorTag> = Vec::new();
    let mut seen: BTreeMap<ConstructorTag, usize> = BTreeMap::new();
    let mut order: Vec<usize> = Vec::with_capacity(letters.len());
    for &letter in letters {
        let Head::Letter { tag, .. } = head(arena, presentations, letter)
        else {
            return None;
        };
        let next = distinct.len();
        let position = *seen.entry(tag).or_insert(next);
        if position == next {
            distinct.push(tag);
        }
        order.push(position);
    }
    let mut images = Vec::with_capacity(distinct.len());
    for &tag in &distinct {
        let empty = arena.value_constructor(family, datatype, FreeCells::nil(), Vec::new());
        let one = arena.value_constructor(family, datatype, tag, Vec::from([empty]));
        images.push(image(
            arena,
            (table, memo),
            unfoldings,
            (routes, at),
            (one, (carrier, fixed)),
        )?);
    }
    let kinds = u32::try_from(distinct.len()).ok()?;
    // Each step stands under the images' binders and the image so far.
    let inside = BinderDepth::from(kinds.checked_add(1)?);
    let family = path_family(
        arena,
        (table, memo),
        (carrier, fixed),
        gandr_kernel_term::Side::Left,
        inside,
    );
    let gathered = arena.value_variable(DeBruijnIndex::from(0_u32));
    let mut steps = Vec::with_capacity(distinct.len());
    for position in 0 .. kinds {
        // `xⱼ` read under the image so far: the binders after it, and that one.
        let along = arena.value_variable(DeBruijnIndex::from(kinds.checked_sub(position)?));
        steps.push(arena.computation_path_transport(family, along, gathered));
    }
    let here_at = |arena: &mut TermArena, table: &mut ContentTable, memo: &mut M, depth| {
        let lifted = shift_value(arena, table, memo, fixed, BinderDepth::NONE, depth);
        arena.value_here(lifted)
    };
    let start = here_at(arena, table, memo, BinderDepth::from(kinds));
    let mut built = arena.computation_return(start);
    for position in order {
        built = arena.computation_bind(built, *steps.get(position)?);
    }
    let end = here_at(arena, table, memo, inside);
    let read_back = arena.computation_path_transport(family, gathered, end);
    built = arena.computation_bind(built, read_back);
    for (position, &computed) in images.iter().enumerate().rev() {
        let lifted = shift_computation(
            arena,
            table,
            memo,
            computed,
            BinderDepth::NONE,
            BinderDepth::from(u32::try_from(position).ok()?),
        );
        built = arena.computation_bind(lifted, built);
    }
    Some(built)
}

/// The image of the one-letter word `letter` along one route of an
/// endpoint's calls, as a computation returning the image word, or `None`
/// when a definition is no case the route reads.
///
/// # Specification
/// - requires: as [`image`]; `walk` is one of [`Routes::walks`].
/// - ensures: the innermost call's loop arm for the letter where its case is
///   over the moving argument, read by [`answered`], its other arguments at the
///   point — inverted along `z. Path[.A = C](z, fixed)` for an inverse letter,
///   the letter's empty word for a case with no loop arm — or [`select`]'s
///   reading where the case is over another argument; bound into each further
///   call's cong of it, the transport along it in `y. Path[.A = C](fixed, ⟨f …
///   y …⟩)` from `here(fixed)`, every argument off the route at the point.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` over the route's later calls and one over each call's
///   arguments, not recursion.
/// - measure: the calls left, then the arguments left.
///
/// # Adequacy
/// - hypothesis: L3 — the flip's image of the loop is its inverse and the
///   collapse's is reflexivity, and the flip twice binds the first image into
///   the second's cong; `mul(b, Base)`'s image of the loop is `selfloop(Base)`;
///   `Path.ap` of the sphere's identity in place maps the 2-cell to its arm,
///   and of a case with no arm there to the empty word; each verdict turns on
///   the image.
/// - witness: `tests::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
/// - witness: `tests::native_formers::a_loop_obligation_reads_a_map_of_two_arguments`
/// - witness: `tests::native_formers::a_map_s_image_of_a_2_cell_in_place_is_its_arm`
#[spec(ensures: |ret| ret.is_none_or(|built| arena.computation(built).is_some()))]
fn route_image<M>(
    arena: &mut TermArena,
    (table, memo): (&mut ContentTable, &mut M),
    unfoldings: &Unfoldings,
    (mut walk, at): (Walk<'_>, ValueId),
    (letter, (carrier, fixed)): (ValueId, (ValueTypeId, ValueId)),
) -> Option<ComputationId>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let (innermost, moving) = walk.next()?;
    let Head::Letter { tag, words, rest } = head(arena, unfoldings.presentations(), letter)
    else {
        return None;
    };
    let cell = FreeCells::generator(tag)?;
    let wrapping = unfoldings
        .presentations()
        .presented(words)
        .and_then(crate::presented::PresentedType::cells)?
        .reflexivities();
    // Each argument where the transport stands: the binder it never reads
    // read at the point.
    let arguments: Vec<ValueId> = innermost
        .arguments
        .iter()
        .map(|&argument| substitute_value(arena, table, memo, argument, at))
        .collect();
    // A loop maps by the call's own case; a cell above dimension one by the
    // case the call's `Path.ap` layers act by, whose arm stands under that
    // case's one argument alone.
    let (case, over, moving, arguments) = if wrapping == Reflexivities::NONE {
        if innermost.layers != Reflexivities::NONE {
            return None;
        }
        let (case, over) = case_of(arena, unfoldings, (innermost.function, &arguments))?;
        (case, over, moving, arguments)
    }
    else {
        // The layers the endpoint writes in place come first, and the
        // definitions give the rest.
        let layers = usize::from(wrapping).checked_sub(usize::from(innermost.layers))?;
        let case = cong_case(
            arena,
            unfoldings,
            (innermost.function, Arity(arguments.len())),
            (moving, Reflexivities::from(layers)),
        )?;
        (case, Argument(0), Argument(0), Vec::from([at]))
    };
    let mut built = if over == moving {
        let arm = loop_arm(
            arena,
            (table, memo),
            unfoldings.presentations(),
            (case, moving, &arguments),
            (words, cell),
        )?;
        match answered(arena, unfoldings, arm) {
            Arm::Unwritten => arena.computation_return(rest),
            Arm::Written(arm) if usize::from(tag) % 2 == 1 => arm,
            Arm::Written(arm) => {
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
        }
    }
    else {
        select(
            arena,
            (table, memo),
            (innermost.function, case),
            (over, moving, &arguments),
            (letter, rest, (carrier, fixed)),
        )?
    };
    for (link, moving) in walk {
        let amount = BinderDepth::from(2_u32);
        let lifted_carrier =
            shift_value_type(arena, table, memo, carrier, BinderDepth::NONE, amount);
        let lifted_fixed = shift_value(arena, table, memo, fixed, BinderDepth::NONE, amount);
        let named = arena.value_constant(link.function);
        let mut applied = arena.computation_force(named);
        for (position, &argument) in link.arguments.iter().enumerate() {
            let passed = if Argument(position) == moving {
                arena.value_variable(DeBruijnIndex::from(0_u32))
            }
            else {
                let standing = substitute_value(arena, table, memo, argument, at);
                shift_value(arena, table, memo, standing, BinderDepth::NONE, amount)
            };
            applied = arena.computation_application(applied, passed);
        }
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

/// The image of the one-letter word `letter` under a carried endpoint, as a
/// computation returning the image word, or `None` when a piece's call is no
/// case its layers read.
///
/// A fixed piece's image is the letter's empty word, a moving one's the
/// letter, and a call's its [`image`] through its raised layers. A carried
/// piece binds its left piece's image, then its right one's, and transports
/// the right image along the left in `z. Path[.A = C](z, fixed)`: the left
/// image inverted, then the right.
///
/// # Specification
/// - requires: as [`image`]; `carrying` is read by [`carried`].
/// - ensures: the first piece's image, each piece's built after the pieces it
///   names.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` over the pieces, the last first, not recursion.
/// - measure: the pieces left.
///
/// # Adequacy
/// - hypothesis: L3 — the 2-sphere's cell maps under the family's carried
///   endpoint in `x. Path[.A = S2](x, x)` to its inverse then itself, the empty
///   word, and under `sphereId`'s in `x. Path[.A = S2](sphereId x, x)` to the
///   arm's inverse then the cell; an image uninverted or a call one layer short
///   refuses the obligation.
/// - witness: `tests::native_formers::a_carried_endpoint_maps_a_cell_6458`
#[spec(ensures: |ret| ret.is_none_or(|built| arena.computation(built).is_some()))]
fn carried_image<M>(
    arena: &mut TermArena,
    (table, memo): (&mut ContentTable, &mut M),
    unfoldings: &Unfoldings,
    (carrying, at): (&Carrying, ValueId),
    (letter, (carrier, fixed)): (ValueId, (ValueTypeId, ValueId)),
) -> Option<ComputationId>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let Head::Letter { rest, .. } = head(arena, unfoldings.presentations(), letter)
    else {
        return None;
    };
    let mut images: Vec<Option<ComputationId>> = Vec::new();
    images.resize(carrying.pieces.len(), None);
    for (position, piece) in carrying.pieces.iter().enumerate().rev() {
        let built = match piece.shape {
            Shape::Fixed => arena.computation_return(rest),
            Shape::Moving => arena.computation_return(letter),
            Shape::Call(ref read) => image(
                arena,
                (table, memo),
                unfoldings,
                (read, at),
                (letter, (carrier, fixed)),
            )?,
            Shape::Carried { left, right } => {
                let first = (*images.get(left)?)?;
                let second = (*images.get(right)?)?;
                // `l⁻¹ · r`: `r` bound one binder in, `l` two, moved along `l`
                // in `z. Path[.A = C](z, fixed)`.
                let one = BinderDepth::from(1_u32);
                let lifted = shift_computation(arena, table, memo, second, BinderDepth::NONE, one);
                let family = path_family(
                    arena,
                    (table, memo),
                    (carrier, fixed),
                    gandr_kernel_term::Side::Left,
                    BinderDepth::from(2_u32),
                );
                let along = arena.value_variable(DeBruijnIndex::from(1_u32));
                let start = arena.value_variable(DeBruijnIndex::from(0_u32));
                let moved = arena.computation_path_transport(family, along, start);
                let after = arena.computation_bind(lifted, moved);
                arena.computation_bind(first, after)
            },
        };
        *images.get_mut(position)? = Some(built);
    }
    images.first().copied().flatten()
}

/// One transport step along a word, by the module's rows, where
/// [`crate::element_identity::transport_beta`] sticks.
///
/// # Specification
/// - requires: nothing; an ill-typed term reduces or sticks without panicking.
/// - ensures: `Reduced` with the transport along a named path's word; with the
///   path returned along the empty word by [`appended`]'s row, before either
///   side runs; with a returned operand that is no held transport
///   ([`crate::element_identity::held_path`]) run first, and a returned path
///   next; with the operand returned along the empty word, or its named word
///   reread; along a closed word of more than one letter in a path family over
///   a carrier its binder never reads, whose endpoints are each fixed, moving
///   or calls, with one step along the whole word, the calls' image by
///   [`word_image`]; with the first letter's transport bound into the rest's
///   along any other longer word; along one letter or such a whole word in a
///   path family over a carrier its binder never reads, with the spliced word
///   returned when both endpoints are fixed or moving and the words splice, or
///   with the images of the endpoints bound and the operand transported along
///   them as the module states; along a path no row reads, or a word whose
///   splice fails, by [`appended`]'s rows; `Stuck` otherwise.
/// - provides: the replay's reading of transport along a word, the engine's
///   evaluator's rows as reducts.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the loop moves reflexivity to the loop in `y. Path[.A =
///   S]( Base, y)`, conjugates a loop to itself in `y. Path[.A = S](y, y)`, and
///   a map with a loop arm carries the loop to the arm's image, as the loop
///   obligations the witnesses admit and refuse read them; a composite along
///   the inverse's returned transport runs that path and cancels to the empty
///   word; a word of two letters moves a path whole, appended on the right and
///   inverted on the left; a map moves a word of four letters whole to its
///   letters' images in order. The circle's corpus rows replay through the same
///   reducts in `gandr-surface-corpus`'s
///   `kernel_export::kernel_loop_elimination_readmission`.
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
/// - witness: `tests::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
/// - witness: `tests::native_formers::a_composite_along_a_returned_path_cancels_to_the_empty_word`
/// - witness: `tests::native_formers::a_word_appends_on_its_first_word`
/// - witness: `tests::native_formers::a_composite_over_a_call_to_the_empty_word_is_its_second_word_473`
/// - witness: `tests::native_formers::a_word_of_two_letters_moves_a_path_whole`
/// - witness: `tests::native_formers::a_closed_word_moves_whole_to_its_letters_images`
/// - witness: `replay::tests::a_bind_over_a_link_on_a_named_univalence_runs_it_6321`
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
    // The empty word moved along a path is the path, whatever the path runs
    // to, as the evaluator's append reads it before a held path would run:
    // `tr(P, q, ε) ⇝ return q`.
    if head(arena, presentations, value) == Head::Empty
        && let Reduction::Reduced(reduct) = appended(arena, unfoldings, term)
    {
        return Reduction::Reduced(reduct);
    }
    // A returned operand runs first, as an elimination meeting one does and as
    // the evaluator's append runs a held operand: `tr(P, w, ⟨c⟩) ⇝ y ← c;
    // tr(P↑, w↑, y)`. A held transport is a value the evaluator never runs.
    if let Some(&Value::Returned(operand)) = arena.value(value)
        && !bool::from(crate::element_identity::held_path(arena, value))
    {
        let one = BinderDepth::from(1_u32);
        let lifted = shift_value_type(arena, table, memo, motive, one, one);
        let onward = shift_value(arena, table, memo, path, BinderDepth::NONE, one);
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let along = arena.computation_path_transport(lifted, onward, bound);
        return Reduction::Reduced(arena.computation_bind(operand, along));
    }
    // A returned path runs next, as the evaluator reads every returned value.
    if let Some(reduct) = run_path(arena, table, memo, term) {
        return Reduction::Reduced(reduct);
    }
    let (tag, words, rest) = match head(arena, presentations, path) {
        Head::Empty => (FreeCells::nil(), None, path),
        Head::Letter { tag, words, rest } => (tag, Some(words), rest),
        Head::Other => return appended(arena, unfoldings, term),
    };
    // A closed word moves whole in a path family over a carrier its binder
    // never reads, whose endpoints are each fixed, moving or calls: each
    // endpoint's image of the word is then its letters' images in order, as
    // the evaluator reads it. A carried endpoint moves letter by letter.
    let whole = match arena.value_type(motive) {
        Some(&ValueType::Path {
            domain: carrier,
            left,
            right,
        }) if words.is_some()
            && head(arena, presentations, rest) != Head::Empty
            && binder_use(arena, Family::Type(carrier)) == BinderUse::Ignored
            && action(arena, left).is_some()
            && action(arena, right).is_some() =>
        {
            spelled(arena, presentations, path)
        },
        _ => None,
    };
    let rest = whole.as_ref().map_or(rest, |&(_, end)| end);
    if whole.is_none() && words.is_some() && head(arena, presentations, rest) != Head::Empty {
        let Some(&Value::Constructor {
            family, datatype, ..
        }) = arena.value(path)
        else {
            return Reduction::Stuck;
        };
        let empty = arena.value_constructor(family, datatype, FreeCells::nil(), Vec::new());
        let first = arena.value_constructor(family, datatype, tag, Vec::from([empty]));
        let step = arena.computation_path_transport(motive, first, value);
        let one = BinderDepth::from(1_u32);
        let lifted = shift_value_type(arena, table, memo, motive, one, one);
        let onward = shift_value(arena, table, memo, rest, BinderDepth::NONE, one);
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let along = arena.computation_path_transport(lifted, onward, bound);
        return Reduction::Reduced(arena.computation_bind(step, along));
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
    if binder_use(arena, Family::Type(carrier)) != BinderUse::Ignored {
        return Reduction::Stuck;
    }
    let read = |endpoint: ValueId| {
        action(arena, endpoint)
            .or_else(|| carried(arena, presentations, endpoint).map(Action::Carried))
    };
    let (Some(left_action), Some(right_action)) = (read(left), read(right))
    else {
        return Reduction::Stuck;
    };
    let fixed_image = |action: &Action| match *action {
        Action::Fixed => Some(rest),
        Action::Moving => Some(path),
        Action::Through(_) | Action::Carried(_) => None,
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
        return match spliced {
            Some(moved) => Reduction::Reduced(arena.computation_return(moved)),
            None => appended(arena, unfoldings, term),
        };
    }
    let Some(at) = point(arena, presentations, words)
    else {
        return Reduction::Stuck;
    };
    let base = substitute_value_type(arena, table, memo, carrier, at);
    let left_at = substitute_value(arena, table, memo, left, at);
    let right_at = substitute_value(arena, table, memo, right, at);
    let mut images = |action: &Action, fixed: ValueId| match *action {
        Action::Fixed => Some(None),
        Action::Moving => Some(Some(arena.computation_return(path))),
        Action::Through(ref read) => match whole {
            Some((ref letters, _)) => word_image(
                arena,
                (table, memo),
                unfoldings,
                (read, at),
                (letters, path),
                (base, fixed),
            ),
            None => image(
                arena,
                (table, memo),
                unfoldings,
                (read, at),
                (path, (base, fixed)),
            ),
        }
        .map(Some),
        Action::Carried(ref carrying) => carried_image(
            arena,
            (table, memo),
            unfoldings,
            (carrying, at),
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
    // `w = l(ℓ)⁻¹ · v`, along the left image in `z. Path[.A = C](z, r(pt))`.
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
    // `w · r(ℓ)`, along the right image in `z. Path[.A = C](l(pt), z)`.
    let reduct = match (before, right_image) {
        (Some(before), None) => before,
        (None, Some(right_image)) => {
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
        (Some(before), Some(right_image)) => {
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
        (None, None) => return Reduction::Stuck,
    };
    Reduction::Reduced(reduct)
}

/// The transport `term` with its returned path run first: `tr(P, ⟨c⟩, v) ⇝ w
/// ← c; tr(P↑, w, v↑)`.
///
/// # Specification
/// - requires: nothing; an ill-typed term reduces without panicking.
/// - ensures: `Some` of that bind exactly when the path is a returned endpoint
///   `⟨c⟩`; `None` otherwise.
/// - provides: [`transport_word`]'s returned-path row, and the replay's reading
///   of a transport the evaluator leaves on its held path.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a composite whose second word is a call stands on that
///   call, so the replay unfolds the call where the checker does; run after a
///   stuck operand, the composite stands on the operand and the replay refuses
///   what the checker accepted.
/// - witness: `tests::native_formers::a_composite_along_a_returned_path_cancels_to_the_empty_word`
#[spec(ensures: |ret| ret.is_some() == matches!(arena.value(term.path), Some(&Value::Returned(_)))
    && ret.is_none_or(|reduct| matches!(arena.computation(reduct), Some(&gandr_kernel_term::Computation::Bind(..)))))]
pub fn run_path<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    term: ElementTransport,
) -> Option<ComputationId>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let ElementTransport {
        motive,
        path,
        value,
    } = term;
    let Some(&Value::Returned(along)) = arena.value(path)
    else {
        return None;
    };
    let one = BinderDepth::from(1_u32);
    let lifted = shift_value_type(arena, table, memo, motive, one, one);
    let onward = shift_value(arena, table, memo, value, BinderDepth::NONE, one);
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let transported = arena.computation_path_transport(lifted, bound, onward);
    Some(arena.computation_bind(along, transported))
}

/// One transport step in a singleton family by the word moved, where the word
/// moved along reads no further: `then` appends on its first word.
///
/// # Specification
/// - requires: nothing; an ill-typed term reduces or sticks without panicking.
/// - ensures: in a family `y. Path[.A = C](a, y)` whose carrier and left
///   endpoint never read `y`, `Reduced` with the path returned when the operand
///   is the empty word — `tr(P, q, ε) ⇝ return q`, and `tr(P, ⟨c⟩, ε) ⇝ c` for
///   a returned path, as the evaluator returns a held one — with the operand's
///   first letter returned before the rest's transport, held as the value it
///   returns, when the operand is `ℓ ∷ p` — `tr(P, q, ℓ ∷ p) ⇝ return ℓ ∷
///   ⟨tr(P, q, p)⟩`, a letter looping at the one point — and with the operand
///   reread when a definition names it; `Stuck` otherwise.
/// - provides: the replay's reading of the evaluator's append row
///   (`gandr-core-nbe`'s `eval::words::appended`) as reducts.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the empty word moved along a path parameter is that
///   parameter, and a letter before a parameter moved along another is the
///   letter before the parameters' composite; the replay re-derives what the
///   checker accepted by those rows only when it reads them too.
/// - witness: `tests::native_formers::a_word_appends_on_its_first_word`
/// - witness: `tests::native_formers::a_composite_over_a_call_to_the_empty_word_is_its_second_word_473`
#[spec(ensures: |ret| match ret {
    Reduction::Reduced(reduct) => arena.computation(reduct).is_some(),
    Reduction::Stuck => true,
})]
pub fn appended(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    term: ElementTransport,
) -> Reduction
{
    let ElementTransport {
        motive,
        path,
        value,
    } = term;
    if singleton(arena, motive).is_none() {
        return Reduction::Stuck;
    }
    match head(arena, unfoldings.presentations(), value) {
        // A returned path is the computation it holds, as the evaluator's
        // append returns a held path: `tr(P, ⟨c⟩, ε) ⇝ c`.
        Head::Empty => {
            if let Some(&Value::Returned(along)) = arena.value(path) {
                return Reduction::Reduced(along);
            }
            Reduction::Reduced(arena.computation_return(path))
        },
        Head::Letter { tag, rest, .. } => {
            let Some(&Value::Constructor {
                family, datatype, ..
            }) = arena.value(value)
            else {
                return Reduction::Stuck;
            };
            let moved = arena.computation_path_transport(motive, path, rest);
            let held = arena.value_returned(moved);
            let prefixed = arena.value_constructor(family, datatype, tag, Vec::from([held]));
            Reduction::Reduced(arena.computation_return(prefixed))
        },
        Head::Other => named(arena, unfoldings, value).map_or(Reduction::Stuck, |body| {
            Reduction::Reduced(arena.computation_path_transport(motive, path, body))
        }),
    }
}

/// The left endpoint of `motive` when it is a singleton family `y. Path[.A =
/// C](a, y)` whose carrier and left endpoint never read `y`: the family the
/// append rows read.
///
/// # Specification
/// - requires: nothing; an ill-typed motive reads as `None`.
/// - ensures: `Some(a)` exactly when `motive` is a path type whose carrier
///   ignores its binder, whose left endpoint is fixed and whose right endpoint
///   moves; `None` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`appended`], whose rows fire only in this family.
/// - witness: `tests::native_formers::a_word_appends_on_its_first_word`
#[spec(ensures: |ret| ret.is_none_or(|left| arena.value(left).is_some()))]
pub fn singleton(
    arena: &TermArena,
    motive: ValueTypeId,
) -> Option<ValueId>
{
    let Some(&ValueType::Path {
        domain: carrier,
        left,
        right,
    }) = arena.value_type(motive)
    else {
        return None;
    };
    if binder_use(arena, Family::Type(carrier)) != BinderUse::Ignored {
        return None;
    }
    let (Some(Action::Fixed), Some(Action::Moving)) = (action(arena, left), action(arena, right))
    else {
        return None;
    };
    Some(left)
}

/// The computation a returned operand holds where the append rows read it:
/// the call the evaluator's append runs, a held operand, before it reads the
/// operand's word.
///
/// # Specification
/// - requires: nothing; an ill-typed term reads as `None`.
/// - ensures: `Some(c)` exactly when the operand is `⟨c⟩` and no held transport
///   ([`crate::element_identity::held_path`]), no definition names the path,
///   the path is no word's letter or empty word, and `motive` is a
///   [`singleton`] family; `None` otherwise.
/// - provides: where the replay runs the held operand as the evaluator's append
///   runs it, so both engines read `spin(Z) then q` as `q`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a composite whose first word is a call returning the
///   empty word reduces to its second word in both engines; were the call left
///   held, the replay would refuse what the checker accepted.
/// - witness: `tests::native_formers::a_composite_over_a_call_to_the_empty_word_is_its_second_word_473`
/// - witness: `replay::tests::a_bind_over_a_link_on_a_named_univalence_runs_it_6321`
#[spec(ensures: |ret| ret.is_none_or(|held| arena.computation(held).is_some()))]
pub fn held_operand(
    arena: &TermArena,
    unfoldings: &Unfoldings,
    term: ElementTransport,
) -> Option<ComputationId>
{
    let Some(&Value::Returned(operand)) = arena.value(term.value)
    else {
        return None;
    };
    if named(arena, unfoldings, term.path).is_some()
        || head(arena, unfoldings.presentations(), term.path) != Head::Other
        || bool::from(crate::element_identity::held_path(arena, term.value))
    {
        return None;
    }
    singleton(arena, term.motive).map(|_left| operand)
}
