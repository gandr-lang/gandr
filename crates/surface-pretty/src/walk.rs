//! The walk from a source's nodes to one layout document.
//!
//! The walk drains an explicit task stack: visiting a node either finishes a
//! piece at once or schedules its children and the join that combines them,
//! and a join pops the finished pieces it needs. Nothing recurses, so a deep
//! type or value costs heap, never native stack.
//!
//! Every break point is a choice whose inline branch carries the exact bytes
//! the one-line spelling carries there, so the flattened image of a document
//! is its one-line spelling and a wide page selects it unchanged; under width
//! pressure the same document breaks, a continuation indented two columns.
//!
//! Before the walk builds anything, a scan over the same nodes collects the
//! names the term spells, so a generated binder never reads as a constant or
//! an abstract type the term mentions. Both passes bound their scheduled
//! visits, including when the source changes between passes.
//!
//! # Products, sums and tuples: braces at every arity, infix from two
//!
//! The core's product and sum hold a list of components
//! ([#134](https://github.com/gandr-lang/gandr/issues/134)), and the explicit
//! form writes each between its delimiters at any arity from one: `#{A}` and
//! `#{A, B, C}`, `+{A}` and `+{A, B, C}`, a nested product or sum one
//! component among them. The 0-ary product is `Unit`, the 0-ary sum `Void`,
//! and the sum of two units `Bool`, the fixed names the lowering resolves. A
//! `Former` counts the components rather than holding them, and the printer
//! asks the source for each one by position (`Source::component`), because
//! the core's components are value-type ids while its handles are
//! `CoreNode`s; a component the source does not answer is written `?`. A
//! tuple is read the same way, `#{a}` and `#{a, b, c}`, the empty tuple
//! `unit`; an injection is `+{.i = v}` at its summand's position. A record
//! type and a record are `#{a : A, b : B}` and `#{.a = v, .b = w}`, in label
//! order; the empty record, which the surface does not write (`#{}` is the
//! unit), is `?`. The lazy product is `&{C, D}`, binary as the core holds it.
//!
//! The sugared form writes a product or a sum of two components or more
//! infix, `A * B * C` and `A + B + C`, one flat chain as the lowering reads
//! an unparenthesized one; a tuple of two or more `(a, b, c)`; the lazy
//! product `C & D`, right-nested as the grammar associates it. A product or
//! a sum of one component, an injection and a record keep their braces in
//! both forms: the surface has no infix spelling for them.
//!
//! - **Alternatives.** A former holding its components' handles would need
//!   every source to keep them as a slice of its own handle type, which the
//!   core arena does not. The binary sugar alone, in both forms, would leave
//!   the 1-ary product, an injection past the second summand and a record
//!   without a spelling.
//! - **Reversal.** A source whose components are costly to reach one at a time,
//!   measured, answers them as a slice instead.
//!
//! # Native universe paths
//!
//! The native presentations are `Path_U(a, b)`, `refl(a)` and `equiv(f, g)`.
//! Endpoint and map order is retained. Each is explicitly
//! `Fidelity::Approximate`: these forms have no surface parser syntax, and an
//! equivalence’s display does not include its classifier or replay evidence.
//! The core adapter and checkpoint adapter expose the same value-child
//! positions. The product of two universe paths, `pathProduct(p, q)`, is the
//! one native former the surface writes: the lowering reads the call back to
//! the same node, so it is faithful, its components in order and each as
//! faithful as its own spelling. Its directed twin `flowProduct(p, q)` is the
//! kernel's own former, written and printed the same way.
//!
//! **Choice.** Show the structural constructor instead of an unreadable marker,
//! while withholding a surface round-trip claim. The printer neither compares
//! certified maps nor replays transport. **Reversal.** A faithful notation
//! requires parser and lowering rules that preserve all required information.
//! `native_paths_preserve_ordered_endpoints_and_maps` checks the order and
//! approximation boundary through public presentation,
//! `a_product_of_written_paths_spells_as_written` the product's faithful
//! spelling and `a_product_of_flows_spells_as_written` its twin's.
//!
//! # Element identity
//!
//! `here(a)` is the surface spelling of element identity, and it is faithful:
//! the grammar parses the call and the lowering mints the witness. It is not
//! the native `refl`, which stays approximate. The point is the call's one
//! argument, so a pair reads `here(#{2, 2})`. Function extensionality is
//! `funext(f, g)` and a universe equivalence `equiv(f, g)` by the same
//! reasoning, their two functions in order; the native certificate a checked
//! `equiv` erases to prints the same call, approximately, without its evidence.
//! Univalence at a stratum is `ua[n, k](a, b, f, g)`, faithful too: the
//! stratum's degree and bound in the head, the descriptions by name and the
//! translator records in label order, as the lowering reads them.
//!
//! - **Alternatives.** Writing `?`, the spelling of a node the surface does not
//!   write, would hide a former the grammar parses.
//! - **Reversal.** A ruled change to the identity spelling.
//!
//! # Native lists
//!
//! The native list type is `List(A)`, its empty list `nil` and its cell
//! `cons(h, t)`, each faithful: the lowering reads the three spellings back to
//! the same formers. A list is written cell by cell, never as a literal
//! `[a, b]`, because a cell whose tail is no literal has no literal spelling.
//!
//! - **Alternatives.** The literal, which the grammar parses, declined above.
//! - **Reversal.** A literal spelling for a list whose spine is all cells.
//!
//! # Break points
//!
//! A break point is a choice between the byte the one-line spelling carries
//! there and a line break: after an arrow, an infix symbol and a comma, a space
//! or a break indented two columns; before a bracket's closer, nothing or a
//! break. The broken branch stands first, matching the layout engine's
//! left-biased fallback when both alternatives are width-tainted. Each choice
//! is independent of the others, so the least-cost layout may break inside a
//! parenthesized operand where that alone fits the page: the narrow page of the
//! example above breaks inside `+U (a -> -F b)`.
//!
//! - **Alternatives.** A group per arrow chain would break all arrows or none,
//!   outer chains before inner ones. Under the cost order, overflow then line
//!   count, this can take more lines than a single inner break. Independent
//!   choices allow that shorter layout.
//! - **Reversal.** A reader rules that a chain breaks whole; the walk then
//!   builds chain groups and the goldens move with it.
//!
//! The computation width is twice the page, saturating at its maximum. Past it
//! the engine resolves without its optimality guarantee: a frontier wins over a
//! tainted promise, and two tainted promises retain the left alternative. At
//! zero columns, both the inline space and the two-column continuation
//! indentation exceed the computation width; the broken separator remains the
//! fallback (`tests::goldens::doubly_tainted_pair_keeps_the_broken_separator`).
//! A wider computation width admits more memoized states. The choice reverses
//! when a wider computation width improves a presentation at an acceptable
//! cost.
//!
//! # A body's statements break together
//!
//! A body's statements, `run x <- c ; rest`, are separated by soft lines that
//! break with the group around them rather than one choice each: the whole
//! body, and the body of each lambda, thunk and block `{ … }` within it, is a
//! group, on one line when it fits and one statement per line otherwise, a
//! block's statements two columns in and its closer on a line of its own.
//!
//! - **Alternatives.** Independent choices, as at the break points above, would
//!   leave some statements of one body joined and others split, which no
//!   formatted source writes.
//! - **Reversal.** A ruled layout for bodies that joins short statements; the
//!   walk then builds choices per statement and the goldens move with it.
//!
//! # Binder names
//!
//! The core is nameless, so the binders of dependent arrows, static
//! abstractions, lambdas and binds are generated: `a` through `z`, then `a1`,
//! `b1`, and so on, the outermost binder first, skipping every constant or
//! abstract-type name encountered by the scan. Two binders whose scopes do not
//! nest, such as a bind inside the computation another bind runs and that
//! other bind's own, take the same name. A new binder is refused when the
//! candidate counter cannot advance; cached names remain available. Name
//! avoidance refers to the scanned view, not an atomic snapshot of a changing
//! source.
//!
//! - **Alternatives.** Printing a de Bruijn index reads as nothing the surface
//!   parses; reusing a mentioned name would make the codomain ambiguous.
//! - **Reversal.** The core carries a binder's source name as an origin hint,
//!   and the printer prints it when no mentioned name collides.
//!
//! # Bounds
//!
//! Nothing here recurses. Values stop at `DEPTH_LIMIT`, 32 value formers, with
//! one `<deep>` leaf; static-spine inspection obeys that depth limit too. The
//! naming scan and scheduled document walk each allow at most 65,536 visits.
//! The walk has its own budget because a source may change after the scan;
//! either pass can refuse with `?`, approximate, rather than loop. A late walk
//! refusal can leave unused documents charged to the builder. A layout ceiling
//! returns `PresentationError`, never partial output. Witness:
//! `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`.
//!
//! # Session types
//!
//! A session type is spelled as the grammar writes it: `!A. S`, `?A. S`,
//! `+{l : S, …}`, `&{l : S, …}`, `mu t. S` and `end`, each payload type a
//! child the walk spells and parenthesizes past an atom. The protocol is
//! spelled from the state the type stands at; a recursion variable whose
//! binder lies outside that state unfolds once to its binder, so the spelling
//! is closed and reads back to an equivalent type. Recursion binders are
//! named `t`, `t1`, … by nesting, apart from the binders of terms.
//!
//! - **Alternatives.** Spelling the whole protocol and marking the state would
//!   print what the endpoint no longer follows; `?`, the spelling of a node the
//!   surface does not write, would hide a type the grammar parses.
//! - **Reversal.** A ruled spelling for a state, or binder names avoiding the
//!   names a term mentions as term binders do.

use alloc::borrow::Cow;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_core_term::effect::capability::RegionDepth;
use gandr_core_term::identity::Relation;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::session::ActionKind;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolNode;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::SessionRelation;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Sign;
use gandr_surface_grammar as grammar;
use gandr_surface_layout::units::NestAmount;
use quenchant_shape::shape::Maybe;

use crate::DEPTH_LIMIT;
use crate::Fidelity;
use crate::Form;
use crate::Style;
use crate::ValueDepth;
use crate::compose::Compose;
use crate::compose::Doc;
use crate::compose::Glyphs;
use crate::error::PresentationError;
use crate::former::Component;
use crate::former::Elided;
use crate::former::Former;
use crate::former::Name;
use crate::former::Notation;
use crate::former::Placement;
use crate::former::Recursion;
use crate::former::Source;
use crate::former::Unreadable;
use crate::former::Unspelled;

/// The relation `relation` names, as the grammar's spelling table pairs its
/// glyph with its ASCII spelling: the equivalence `≃`, the quasi-inverse `≅`
/// and the flow between types `⇝`, one entry per former.
///
/// # Specification
/// trivial.
const fn relation_spelled(relation: Relation) -> grammar::Spelled
{
    match relation {
        Relation::Isomorphism => writes(Production("isomorphism_type"), grammar::ISOMORPHISM),
        Relation::Equivalence => writes(Production("equivalence_type"), grammar::EQUIVALENCE),
        Relation::Flow => writes(Production("universe_flow_type"), grammar::FLOW),
    }
}

/// Why `text`, a name, cannot be written in `spelling`, if it cannot.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Unspelled::Unprintable`] for an empty name and one holding a
///   line feed, a carriage return or a tab; else [`Unspelled::Primed`] for a
///   name holding the prime in [`grammar::Spelling::Ascii`]; else none.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an empty name, a primed one in each spelling and a plain
///   one distinguish the three answers.
/// - witness: `walk::tests::unprintable_names_are_approximate_atoms`
/// - witness: `tests::goldens::a_primed_name_has_no_ascii_spelling_782`
#[spec(ensures: |ret| {
    let text: &str = name.as_ref();
    match ret {
        Some(Unspelled::Unprintable) => text.is_empty() || text.contains(['\n', '\r', '\t']),
        Some(Unspelled::Primed) => spelling == grammar::Spelling::Ascii && text.contains(grammar::PRIME.0),
        Some(_) => false,
        None => !text.is_empty() && !text.contains(['\n', '\r', '\t'])
            && (spelling == grammar::Spelling::Unicode || !text.contains(grammar::PRIME.0)),
    }
})]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        answer_totality,
        reason = "a name a line cannot hold, or a primed name in ASCII, has no spelling: each \
                  caller writes `?` for the reason answered"
    )
)]
fn unwritable(
    name: Name<'_>,
    spelling: grammar::Spelling,
) -> Option<Unspelled>
{
    let text: &str = name.as_ref();
    if text.is_empty() || text.contains(['\n', '\r', '\t']) {
        Some(Unspelled::Unprintable)
    }
    else if spelling == grammar::Spelling::Ascii && text.contains(grammar::PRIME.0) {
        Some(Unspelled::Primed)
    }
    else {
        None
    }
}

quenchant_shape::reason_enum! {
    /// Why a universe has no surface spelling.
    pub mod universe {
        /// The reason no spelling is written.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The universe's sort is a parameter, which has no spelling.
            ParameterSort,
            /// The level mentions a level variable, which has no spelling.
            LevelVariable,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a binder has no generated name.
    pub mod binder {
        /// The reason no name is generated.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The candidate names ran out.
            Exhausted,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a scan collected no names.
    pub mod scan {
        /// The reason the scan stopped.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source took more node visits than one presentation makes.
            OverBudget,
        }
    }
}

/// The columns a broken continuation is indented by.
const CONTINUATION: u32 = 2;

/// The maximum scheduled node visits in either presentation pass.
///
/// A well-formed type or value of any size a reader would read fits many
/// times over; the bound is reached by a malformed source — a cycle — whose
/// presentation is then `?` rather than a walk that does not end.
const VISIT_BUDGET: u32 = 0x0001_0000;

/// An owned spelling computed for one leaf.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Spelled(String);

/// A name generated for a binder the core leaves nameless.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct BinderName(String);

/// The position of a candidate binder name in the order names are tried.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Ordinal(u32);

/// How many binders — of dependent arrows, static abstractions, lambdas and
/// binds — are open at a point of the walk; read as a position, the binder
/// that many binders in.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct OpenBinders(usize);

/// How many arguments one spelled application holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Arity(usize);

/// The sort of node a former is, as far as a position cares.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// A value type.
    ValueType,
    /// A computation type.
    CompType,
    /// A value.
    Value,
    /// A computation term.
    Computation,
    /// No former at all: admitted anywhere, spelled `?`.
    Unknown,
}

/// The sort of node `former` is.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the value-type formers answer [`Kind::ValueType`], the
///   computation-type formers [`Kind::CompType`], the value formers
///   [`Kind::Value`], the computation formers [`Kind::Computation`], and an
///   unreadable handle [`Kind::Unknown`].
/// - provides: the check that a node fills the position it stands in.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the finite golden type and value fixtures observe the
///   former partition through exact spelling, while misplaced bridges expose
///   cross-family classifications. Payload values are not classified here.
/// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
/// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
/// - witness: `tests::goldens::native_paths_preserve_ordered_endpoints_and_maps`
#[spec(ensures: |ret| match ret {
    | Kind::ValueType => matches!(*former, Former::BaseType(_) | Former::Product(_) | Former::RecordType(_)
        | Former::Stack(..) | Former::List(_)
        | Former::Sum(_) | Former::ThunkType(_) | Former::Universe { .. }
        | Former::Element(_) | Former::Abstract(_) | Former::StaticPi { .. } | Former::Sigma { .. } | Former::Capability { .. } | Former::PathUniverse(..) | Former::Session { .. }
        | Former::Path { .. } | Former::Flow { .. } | Former::Relation { .. } | Former::Data { .. } | Former::RunType(_) | Former::Located { .. } | Former::Kept { .. }),
    | Kind::CompType => matches!(*former, Former::Returner(_) | Former::EffectfulReturner { .. } | Former::Arrow { .. }
        | Former::With(..) | Former::Pi { .. } | Former::ComputationElement(_) | Former::Codata { .. }),
    | Kind::Value => matches!(*former, Former::Variable { .. } | Former::Constant(_) | Former::Unit
        | Former::Literal(_) | Former::Tuple(_) | Former::Record(_) | Former::Injection(..) | Former::Thunk(_)
        | Former::Reify | Former::ListNil | Former::ListCons(..)
        | Former::Quote(_) | Former::QuoteComputation(_) | Former::StaticLambda(_) | Former::StaticApplication(..)
        | Former::PathRefl(_) | Former::PathEquiv(..) | Former::PathProduct(..) | Former::Here(_) | Former::Funext(..) | Former::Equiv(..) | Former::Univalence(_)
        | Former::Ua { .. } | Former::Nested(_) | Former::Run(_) | Former::Constructor { .. } | Former::Returned(_)
        | Former::SessionRelated(..) | Former::Stay(_) | Former::Then(..) | Former::Back(_) | Former::Cong(..) | Former::FlowProduct(..) | Former::Forward(_) | Former::FunctionFlow(..) | Former::Recorded { .. }),
    | Kind::Computation => matches!(*former, Former::Return(_) | Former::Bind(..) | Former::Force(_)
        | Former::Application(..) | Former::Lambda(_) | Former::Primitive { .. } | Former::Transport(..)
        | Former::PathTransport { .. } | Former::Ride { .. } | Former::TelescopeTransport { .. } | Former::Fixpoint(_) | Former::Case { .. }
        | Former::Split { .. } | Former::DataCase { .. } | Former::RecordProjection(..) | Former::TupleProjection(..)
        | Former::ListFold { .. } | Former::ListCase { .. } | Former::Perform { .. } | Former::Handle { .. } | Former::Exercise { .. }
        | Former::Scope { .. } | Former::Resume(..) | Former::Reset(_) | Former::Shift(_) | Former::Lazy(..) | Former::Ascription { .. }
        | Former::Project(..) | Former::Send { .. } | Former::Receive { .. } | Former::Select { .. } | Former::Offer { .. }
        | Former::Close(_) | Former::Fork { .. } | Former::Hold { .. } | Former::Access { .. } | Former::ResumeView { .. }
        | Former::AbortView(_) | Former::WorldHold(_) | Former::Leta { .. } | Former::Migrate { .. }),
    | Kind::Unknown => matches!(*former, Former::Unreadable(_)),
})]
const fn kind<Node>(former: &Former<'_, Node>) -> Kind
{
    match *former {
        Former::Stack(..)
        | Former::PathUniverse(..)
        | Former::BaseType(_)
        | Former::Product(_)
        | Former::RecordType(_)
        | Former::Sum(_)
        | Former::List(_)
        | Former::ThunkType(_)
        | Former::Universe { .. }
        | Former::Element(_)
        | Former::Abstract(_)
        | Former::Session { .. }
        | Former::StaticPi { .. }
        | Former::Sigma { .. }
        | Former::Capability { .. }
        | Former::Path { .. }
        | Former::Flow { .. }
        | Former::Relation { .. }
        | Former::Data { .. }
        | Former::RunType(_)
        | Former::Located { .. }
        | Former::Kept { .. } => Kind::ValueType,
        Former::Returner(_)
        | Former::With(..)
        | Former::EffectfulReturner { .. }
        | Former::Arrow { .. }
        | Former::Pi { .. }
        | Former::ComputationElement(_)
        | Former::Codata { .. } => Kind::CompType,
        Former::PathRefl(_)
        | Former::PathProduct(..)
        | Former::PathEquiv(..)
        | Former::Variable { .. }
        | Former::Constant(_)
        | Former::Unit
        | Former::Literal(_)
        | Former::Tuple(_)
        | Former::Record(_)
        | Former::ListNil
        | Former::ListCons(..)
        | Former::Injection(..)
        | Former::Thunk(_)
        | Former::Reify
        | Former::Quote(_)
        | Former::QuoteComputation(_)
        | Former::StaticLambda(_)
        | Former::StaticApplication(..)
        | Former::Here(_)
        | Former::Funext(..)
        | Former::Equiv(..)
        | Former::Univalence(_)
        | Former::SessionRelated(..)
        | Former::Stay(_)
        | Former::Then(..)
        | Former::Back(_)
        | Former::Cong(..)
        | Former::FlowProduct(..)
        | Former::Forward(_)
        | Former::FunctionFlow(..)
        | Former::Ua { .. }
        | Former::Nested(_)
        | Former::Run(_)
        | Former::Constructor { .. }
        | Former::Recorded { .. }
        | Former::Returned(_) => Kind::Value,
        Former::Return(_)
        | Former::Bind(..)
        | Former::Force(_)
        | Former::Application(..)
        | Former::Lambda(_)
        | Former::Primitive { .. }
        | Former::Transport(..)
        | Former::PathTransport { .. }
        | Former::Ride { .. }
        | Former::TelescopeTransport { .. }
        | Former::Fixpoint(_)
        | Former::Case { .. }
        | Former::Split { .. }
        | Former::DataCase { .. }
        | Former::RecordProjection(..)
        | Former::TupleProjection(..)
        | Former::ListFold { .. }
        | Former::ListCase { .. }
        | Former::Perform { .. }
        | Former::Handle { .. }
        | Former::Exercise { .. }
        | Former::Scope { .. }
        | Former::Resume(..)
        | Former::Reset(_)
        | Former::Shift(_)
        | Former::Lazy(..)
        | Former::Ascription { .. }
        | Former::Project(..)
        | Former::Send { .. }
        | Former::Receive { .. }
        | Former::Select { .. }
        | Former::Offer { .. }
        | Former::Close(_)
        | Former::Fork { .. }
        | Former::Hold { .. }
        | Former::Access { .. }
        | Former::ResumeView { .. }
        | Former::AbortView(_)
        | Former::WorldHold(_)
        | Former::Leta { .. }
        | Former::Migrate { .. } => Kind::Computation,
        #[cfg_attr(
            dylint_lib = "quenchant_dylints",
            expect(
                answer_totality,
                reason = "a node of the honest set carries no sort of its own; the walk writes it \
                          `?` wherever it stands"
            )
        )]
        Former::Unreadable(_) => Kind::Unknown,
    }
}

/// The node sorts a position admits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Admits
{
    /// A value type or a computation type.
    Type,
    /// A value type.
    ValueType,
    /// A computation type.
    CompType,
    /// A value.
    Value,
    /// A value whose type its position states: a family's argument, typed by
    /// the family's parameter, where a parameterised constructor stands bare.
    Stated,
    /// A value whose type nothing states: a transport's path and the value it
    /// moves, which the lowering reads with no type to bind a computation at.
    Operand,
    /// A computation, where a path through a body ends or where it goes on.
    Computation(Tail),
}

/// Whether a path through a body ends at a computation's position.
///
/// A returner where a path ends is written as its value and every other
/// computation there bare, the exit the lowering infers left out; anywhere
/// else a returner is `pure v`, since a written `return` there would leave
/// the body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Tail
{
    /// The body ends here: a definition's body, the rest of a bind there, a
    /// lambda's or a thunk's body.
    Ends,
    /// The body ends here, and nothing states its type: a thunk's body below
    /// a value, as a constructor's field, a lambda's body there.
    Unstated,
    /// The body goes on: the computation a bind runs, the function a call
    /// applies.
    Continues,
}

/// Whether a thunk's body is spelled or the thunk written opaque, and whether
/// a parameterised constructor is written against its family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Bodies
{
    /// `<thunk>`: a value presented alone is a normal form, whose thunks are
    /// closures a reader does not read; its constructors stand bare,
    /// `Some(1)`, as a run's value is written.
    Opaque,
    /// `thunk { c }`: a computation presented is a body a reader reads, and
    /// so is a definition's value, a thunk a type mentions, a path's
    /// endpoint, which the author wrote; a parameterised constructor there is
    /// source that reads back, written against its family, `(MkIx : Ix(3))`,
    /// except as a family's argument, whose parameter states its type,
    /// `Vec(MkIx)`.
    Spelled,
}

/// How the walk treats a node it reaches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// The node fits its position: spell its former.
    Spell,
    /// The node is a value at the depth limit: write `<deep>`.
    Deep,
    /// The node is of a sort its position does not admit: write `?`.
    Misplaced,
}

/// How the walk treats a node of `kind` at `depth` in a position admitting
/// `admits`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Reach::Deep`] for a value position at or past [`DEPTH_LIMIT`];
///   otherwise [`Reach::Spell`] when the position admits the kind — an unknown
///   node is admitted everywhere — and [`Reach::Misplaced`] when it does not.
/// - provides: the one rule both the scan and the walk stop by, so the two
///   reach the same nodes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — misplaced bridges and deep values observe refusal; the
///   exact depth boundary with an unknown former separates depth-first
///   precedence from admission. Arbitrary source behavior is not involved.
/// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
/// - witness: `tests::goldens::beyond_the_depth_limit_renders_deep`
/// - witness: `walk::tests::depth_boundaries_preserve_precedence_and_saturation`
#[spec(ensures: |ret| {
    let valued = matches!(admits, Admits::Value | Admits::Stated | Admits::Operand);
    let deep = valued && depth.0 >= DEPTH_LIMIT.0;
    let admitted = matches!((admits, kind), (_, Kind::Unknown)
        | (Admits::Type, Kind::ValueType | Kind::CompType)
        | (Admits::ValueType, Kind::ValueType) | (Admits::CompType, Kind::CompType)
        | (Admits::Value | Admits::Stated | Admits::Operand, Kind::Value) | (Admits::Computation(_), Kind::Computation));
    (ret == Reach::Deep) == deep && (ret == Reach::Spell) == (!deep && admitted)
        && (ret == Reach::Misplaced) == (!deep && !admitted)
})]
fn reach(
    admits: Admits,
    depth: ValueDepth,
    kind: Kind,
) -> Reach
{
    if matches!(admits, Admits::Value | Admits::Stated | Admits::Operand) && depth >= DEPTH_LIMIT {
        return Reach::Deep;
    }
    match (admits, kind) {
        (_, Kind::Unknown)
        | (Admits::Type, Kind::ValueType | Kind::CompType)
        | (Admits::ValueType, Kind::ValueType)
        | (Admits::CompType, Kind::CompType)
        | (Admits::Value | Admits::Stated | Admits::Operand, Kind::Value)
        | (Admits::Computation(_), Kind::Computation) => Reach::Spell,
        (Admits::Type, Kind::Value | Kind::Computation)
        | (Admits::ValueType, Kind::CompType | Kind::Value | Kind::Computation)
        | (Admits::CompType, Kind::ValueType | Kind::Value | Kind::Computation)
        | (
            Admits::Value | Admits::Stated | Admits::Operand,
            Kind::ValueType | Kind::CompType | Kind::Computation,
        )
        | (Admits::Computation(_), Kind::ValueType | Kind::CompType | Kind::Value) => {
            Reach::Misplaced
        },
    }
}

/// How many binders a child stands under beyond its parent's, and the zone
/// they open in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Binds
{
    /// The zone each binder opens in.
    pub zone: Zone,
    /// How many open.
    pub count: usize,
}

impl Binds
{
    /// No binder.
    const NONE: Self = Self::intuitionistic(OpenBinders(0_usize));
    /// One intuitionistic binder.
    const ONE: Self = Self::intuitionistic(OpenBinders(1_usize));

    /// `count` intuitionistic binders.
    ///
    /// # Specification
    /// trivial.
    const fn intuitionistic(count: OpenBinders) -> Self
    {
        Self {
            zone: Zone::Intuitionistic,
            count: count.0,
        }
    }
}

/// The label an entry is written after, which the source answers for the
/// former `of` holding the entry.
#[derive(Clone, Copy, Debug)]
struct Labelled<Node>
{
    /// The record, the record type or the injection.
    of: Node,
    /// The entry's position; an injection's summand.
    index: Component,
    /// What the label is.
    label: Label,
}

/// One child a former reads: the node, what its position admits, the
/// binders it stands under and the label written before it.
#[derive(Clone, Copy, Debug)]
pub struct Slot<Node>
{
    /// The child; none for a component the source does not answer, spelled
    /// `?`.
    pub node: Option<Node>,
    /// What its position admits.
    pub admits: Admits,
    /// The binders it stands under.
    pub binds: Binds,
    /// The label written before it, a piece of its own.
    label: Option<Labelled<Node>>,
}

impl<Node> Slot<Node>
{
    /// `node` at a position admitting `admits`, under `binds`, unlabelled.
    ///
    /// # Specification
    /// trivial.
    const fn of(
        node: Node,
        admits: Admits,
        binds: Binds,
    ) -> Self
    {
        Self {
            node: Some(node),
            admits,
            binds,
            label: None,
        }
    }
}

/// One branch of a data case as the printer reads it: its body below the
/// lambdas binding its constructor's fields, the constructor's name, how
/// many fields the body stands under, and where the name stands to them.
#[derive(Clone, Copy, Debug)]
struct Arm<'source, Node>
{
    /// The body, or the whole branch when the constructor is unknown; none
    /// for a branch the source does not answer.
    body: Option<Node>,
    /// The constructor's name, when the source knows it and the branch binds
    /// its fields.
    name: Option<Name<'source>>,
    /// How many field binders the body stands under.
    fields: usize,
    /// Where the name stands to its field binders: a letter of a word
    /// before the rest, `loop ∷ p`.
    placement: Placement,
}

/// Branch `index` of the data case `case`.
///
/// # Specification
/// - requires: nothing; a malformed source is admissible.
/// - ensures: when the source names the constructor and the branch is that many
///   lambdas deep, at most [`DEPTH_LIMIT`], the body below them, the name and
///   the field count; otherwise the whole branch, no name and no fields.
/// - provides: the one reading of a branch both the child table and the pattern
///   share, so a pattern names exactly the binders its body opens.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// The loop peels one lambda per field, at most [`DEPTH_LIMIT`].
///
/// # Adequacy
/// - hypothesis: L3 — a data case over a nullary and a unary constructor spells
///   each branch under its pattern, the unary one's field bound.
/// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
/// - witness: `tests::goldens::a_constructor_at_the_depth_limit_binds_every_field`
#[spec(ensures: |ret| ret.name.is_some() || ret.fields == 0_usize)]
fn arm<S>(
    source: &S,
    case: S::Node,
    index: Component,
) -> Arm<'_, S::Node>
where
    S: Source + ?Sized,
{
    let branch = source.component(case, index);
    let unknown = Arm {
        body: branch,
        name: None,
        fields: 0_usize,
        placement: Placement::Applied,
    };
    let (Some(branch), Some((name, fields, placement))) = (branch, source.constructor(case, index))
    else {
        return unknown;
    };
    let fields = usize::from(fields);
    if u32::try_from(fields).is_ok_and(|count| count > DEPTH_LIMIT.0) {
        return unknown;
    }
    let mut body = branch;
    for _ in 0_usize .. fields {
        let Former::Lambda(inner) = source.read(body)
        else {
            return unknown;
        };
        body = inner;
    }
    Arm {
        body: Some(body),
        name: Some(name),
        fields,
        placement,
    }
}

/// The children `former` reads at `node`, each with what its position
/// admits and the binders it stands under, in reading order, in a position
/// admitting `admits` of a presentation writing its thunks as `bodies` says.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the slots [`slots`] reads, a data case's motive among them where
///   [`case_motive`] writes it.
/// - provides: the one table of child positions the scan and the walk share.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`slots`].
/// - witness: `tests::goldens::a_case_nothing_types_writes_its_motive_815`
#[spec(ensures: |ref ret| if let Former::DataCase { motive, arity, .. } = *former {
    ret.len() == usize::from(arity).saturating_add(1_usize).saturating_add(usize::from(case_motive(source, motive, admits) == Motive::Written))
} else {
    true
})]
pub fn children<S>(
    source: &S,
    node: S::Node,
    former: &Former<'_, S::Node>,
    admits: Admits,
    bodies: Bodies,
) -> Vec<Slot<S::Node>>
where
    S: Source + ?Sized,
{
    let written = if let Former::DataCase { motive, .. } = *former {
        case_motive(source, motive, admits)
    }
    else {
        Motive::Left
    };
    slots(source, node, former, (admits, bodies), written)
}

/// The children `former` reads at `node`, each with what its position
/// admits and the binders it stands under, in reading order, in a position
/// admitting `admits` of a presentation writing its thunks as `bodies` says,
/// a data case writing its motive as `written` says.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an n-ary former's components, answered by the source for `node`,
///   a record's and a record type's after their field labels and an injection's
///   body after its summand; type children admit types and term children terms
///   as the grammar places them; a dependent arrow's codomain, a dependent
///   pair's second factor, a static abstraction's, a lambda's and a fixpoint's
///   body, a bind's rest, a case's branches, a transport's motive, a return
///   clause and a stack capture's body stand under one binder, a split's body
///   under one per component, a data case's branch under one per field of its
///   constructor, a fold's cell branch and a handler's operation clauses under
///   two, a scope's subject under the capability's and a fork's child and
///   parent each under one linear binder, a hold's scope and an access's body
///   each under one linear binder; the computation a bind runs, the function an
///   application applies, a computation where a value is read, an offer's arms
///   and a fork's child admit computations where the body goes on, a body in
///   braces one where it ends, a thunk's body below a value and a lambda's body
///   there one whose type nothing states, and a bind's rest and the branches of
///   a case what its own position admits; a data case's motive is a type under
///   one binder where `written` writes it; a thunk's body is a child only where
///   bodies are spelled; a family's arguments, a codata family's included,
///   admit values their parameters state the type of, and a constructor's
///   classifier is a child only where bodies are spelled and its position
///   states no type; every leaf former has none.
/// - provides: the one table of child positions the scan and the walk share.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — finite composite grammar fixtures and misplaced bridge
///   children observe arity, child order, binders and admitted families.
///   Arbitrary node representations are outside this spelling evidence.
/// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `tests::goldens::records_spell_their_fields_in_label_order`
/// - witness: `tests::goldens::static_operators_spell_as_the_grammar_writes_them`
/// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
/// - witness: `tests::goldens::native_paths_preserve_ordered_endpoints_and_maps`
/// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
/// - witness: `tests::goldens::a_parameterised_constructor_is_written_against_its_family_where_source_reads_it`
#[spec(ensures: |ref ret| match *former {
    | Former::Product(arity) | Former::Sum(arity) | Former::RecordType(arity) => ret.len() == usize::from(arity)
        && ret.iter().all(|slot| slot.admits == Admits::ValueType && slot.binds == Binds::NONE),
    | Former::Tuple(arity) | Former::Record(arity) | Former::Primitive { arity, .. } => ret.len() == usize::from(arity)
        && ret.iter().all(|slot| slot.admits == Admits::Value && slot.binds == Binds::NONE),
    | Former::Data { arity, .. } | Former::Codata { arity, .. } => ret.len() == usize::from(arity)
        && ret.iter().all(|slot| slot.admits == Admits::Stated && slot.binds == Binds::NONE),
    | Former::With(arity) => ret.len() == usize::from(arity)
        && ret.iter().all(|slot| slot.admits == Admits::CompType && slot.binds == Binds::NONE),
    | Former::Lazy(arity) => ret.len() == usize::from(arity)
        && ret.iter().all(|slot| slot.admits == Admits::Computation(Tail::Continues) && slot.binds == Binds::NONE),
    | Former::Constructor { arity, classifier, .. } => {
        let annotated = classifier.is_some() && bodies == Bodies::Spelled && admits != Admits::Stated;
        ret.len() == usize::from(arity).saturating_add(usize::from(annotated))
            && ret.iter().take(usize::from(arity)).all(|slot| slot.admits == Admits::Value && slot.binds == Binds::NONE)
            && (!annotated || ret.last().is_some_and(|slot| slot.admits == Admits::ValueType))
    },
    | Former::Pi { .. } | Former::Sigma { .. } | Former::StaticLambda(_) | Former::Lambda(_) | Former::Bind(..) | Former::Fixpoint(_)
        | Former::Shift(_) | Former::Leta { .. } => ret.last().is_some_and(|slot| slot.binds == Binds::ONE),
    | Former::Case { arity, .. } => ret.len() == usize::from(arity).saturating_add(1_usize)
        && ret.first().is_some_and(|slot| slot.admits == Admits::Value && slot.binds == Binds::NONE),
    | Former::DataCase { arity, .. } => ret.len() == usize::from(arity).saturating_add(1_usize).saturating_add(usize::from(written == Motive::Written))
        && ret.first().is_some_and(|slot| slot.admits == Admits::Value && slot.binds == Binds::NONE),
    | Former::Thunk(_) => ret.len() == match bodies { Bodies::Spelled => 1_usize, Bodies::Opaque => 0_usize },
    | Former::Session { payloads, .. } => ret.len() == usize::from(payloads)
        && ret.iter().all(|slot| slot.admits == Admits::ValueType && slot.binds == Binds::NONE),
    | Former::Offer { arms, .. } => ret.len() == usize::from(arms)
        && ret.iter().all(|slot| slot.admits == Admits::Computation(Tail::Continues)),
    | Former::Fork { .. } => ret.len() == 3_usize
        && ret.iter().skip(1_usize).all(|slot| slot.binds == Binds { zone: Zone::Linear, count: 1_usize })
        && ret.get(1_usize).is_some_and(|slot| slot.admits == Admits::Computation(Tail::Continues)),
    | Former::Hold { .. } => ret.len() == 2_usize
        && ret.last().is_some_and(|slot| slot.binds == Binds { zone: Zone::Linear, count: 1_usize }),
    | Former::Receive { .. } => ret.len() == 1_usize
        && ret.last().is_some_and(|slot| slot.binds == Binds { zone: Zone::Linear, count: 1_usize }),
    | Former::Access { mode, place, .. } => {
        let indexed = usize::from(matches!(place, gandr_core_term::memory::Place::At { .. }));
        ret.len() == indexed.saturating_add(match mode { AccessMode::Exclusive { .. } => 2_usize, AccessMode::Shared => 1_usize })
            && ret.get(indexed).is_some_and(|slot| slot.binds == Binds { zone: Zone::Linear, count: 1_usize })
    },
    | Former::BaseType(_) | Former::Universe { .. } | Former::Abstract(_) | Former::Capability { .. }
        | Former::Variable { .. } | Former::Constant(_) | Former::Unit | Former::ListNil | Former::Literal(_)
        | Former::Reify | Former::Select { .. } | Former::Close(_) | Former::AbortView(_) | Former::Unreadable(_) => ret.is_empty(),
    | _ => !ret.is_empty(),
})]
fn slots<S>(
    source: &S,
    node: S::Node,
    former: &Former<'_, S::Node>,
    (admits, bodies): (Admits, Bodies),
    written: Motive,
) -> Vec<Slot<S::Node>>
where
    S: Source + ?Sized,
{
    let value = |node| Slot::of(node, Admits::Value, Binds::NONE);
    let operand = |node| Slot::of(node, Admits::Operand, Binds::NONE);
    let value_type = |node| Slot::of(node, Admits::ValueType, Binds::NONE);
    let comp_type = |node| Slot::of(node, Admits::CompType, Binds::NONE);
    let continues = |node| Slot::of(node, Admits::Computation(Tail::Continues), Binds::NONE);
    let ends = |node, binds| Slot::of(node, Admits::Computation(Tail::Ends), binds);
    let components =
        |arity: crate::former::Arity, admits: Admits, binds: Binds, label: Option<Label>| {
            (0_usize .. usize::from(arity))
                .map(|index| {
                    let index = Component::from(index);
                    Slot {
                        node: source.component(node, index),
                        admits,
                        binds,
                        label: label.map(|label| Labelled {
                            of: node,
                            index,
                            label,
                        }),
                    }
                })
                .collect::<Vec<_>>()
        };
    let clauses = |subject: Slot<S::Node>, on_return, count| {
        let mut slots = Vec::from([subject, ends(on_return, Binds::ONE)]);
        slots.extend(components(
            count,
            Admits::Computation(Tail::Ends),
            Binds::intuitionistic(OpenBinders(2_usize)),
            None,
        ));
        slots
    };
    match *former {
        Former::Stack(first, second) => Vec::from([comp_type(first), comp_type(second)]),
        Former::With(arity) => components(arity, Admits::CompType, Binds::NONE, None),
        Former::Product(arity) | Former::Sum(arity) => {
            components(arity, Admits::ValueType, Binds::NONE, None)
        },
        Former::Session { payloads, .. } => {
            components(payloads, Admits::ValueType, Binds::NONE, None)
        },
        Former::RecordType(arity) => {
            components(arity, Admits::ValueType, Binds::NONE, Some(Label::Field))
        },
        Former::Tuple(arity)
        | Former::Primitive { arity, .. }
        | Former::Recorded {
            payloads: arity, ..
        } => components(arity, Admits::Value, Binds::NONE, None),
        Former::Data { arity, .. } | Former::Codata { arity, .. } => {
            components(arity, Admits::Stated, Binds::NONE, None)
        },
        Former::Constructor {
            arity, classifier, ..
        } => {
            let mut slots = components(arity, Admits::Value, Binds::NONE, None);
            if let (Some(classifier), Bodies::Spelled) = (classifier, bodies)
                && admits != Admits::Stated
            {
                slots.push(value_type(classifier));
            }
            slots
        },
        Former::Record(arity) => {
            components(arity, Admits::Value, Binds::NONE, Some(Label::Assignment))
        },
        Former::StaticPi { domain, codomain } => {
            Vec::from([value_type(domain), value_type(codomain)])
        },
        Former::Sigma { first, second } => Vec::from([
            value_type(first),
            Slot::of(second, Admits::ValueType, Binds::ONE),
        ]),
        Former::Arrow { domain, codomain } => Vec::from([value_type(domain), comp_type(codomain)]),
        // The map stands as the derived transport's motive holds it, one
        // binder deeper; it names no binder there, so it spells as written.
        Former::Cong(map, path) => {
            Vec::from([Slot::of(map, Admits::Value, Binds::ONE), value(path)])
        },
        Former::Pi { domain, codomain } => Vec::from([
            value_type(domain),
            Slot::of(codomain, Admits::CompType, Binds::ONE),
        ]),
        Former::PathUniverse(first, second)
        | Former::PathProduct(first, second)
        | Former::Funext(first, second)
        | Former::Equiv(first, second)
        | Former::SessionRelated(_, first, second)
        | Former::Then(first, second)
        | Former::FlowProduct(first, second)
        | Former::FunctionFlow(first, second)
        | Former::Ua {
            forward: first,
            backward: second,
            ..
        }
        | Former::PathEquiv(first, second)
        | Former::ListCons(first, second)
        | Former::StaticApplication(first, second)
        | Former::Transport(first, second) => Vec::from([value(first), value(second)]),
        Former::Path {
            carrier,
            left,
            right,
        }
        | Former::Flow {
            carrier,
            left,
            right,
        } => Vec::from([value_type(carrier), value(left), value(right)]),
        Former::Relation {
            relation: Relation::Flow,
            left,
            right,
        } => Vec::from([value(left), value(right)]),
        Former::Relation {
            relation: Relation::Isomorphism | Relation::Equivalence,
            left,
            right,
        } => Vec::from([value_type(left), value_type(right)]),
        Former::ThunkType(child) | Former::QuoteComputation(child) => Vec::from([comp_type(child)]),
        Former::List(child)
        | Former::Returner(child)
        | Former::EffectfulReturner { result: child, .. }
        | Former::Quote(child)
        | Former::Located { inner: child, .. }
        | Former::Kept { inner: child, .. } => Vec::from([value_type(child)]),
        Former::PathRefl(child)
        | Former::Element(child)
        | Former::ComputationElement(child)
        | Former::Here(child)
        | Former::Univalence(child)
        | Former::Stay(child)
        | Former::Back(child)
        | Former::Forward(child)
        | Former::RunType(child)
        | Former::Return(child)
        | Former::Force(child)
        | Former::RecordProjection(child, _)
        | Former::TupleProjection(child, _)
        | Former::Perform { payload: child, .. }
        | Former::Send { payload: child, .. }
        | Former::ResumeView { value: child, .. }
        | Former::WorldHold(child) => Vec::from([value(child)]),
        Former::Injection(summand, child) => Vec::from([Slot {
            label: Some(Labelled {
                of: node,
                index: summand,
                label: Label::Summand,
            }),
            ..value(child)
        }]),
        Former::StaticLambda(body) => Vec::from([Slot::of(body, Admits::Value, Binds::ONE)]),
        Former::Bind(bound, rest) => {
            Vec::from([continues(bound), Slot::of(rest, admits, Binds::ONE)])
        },
        Former::Application(function, argument) => {
            Vec::from([continues(function), value(argument)])
        },
        // A lambda's body below a value states no more than the lambda.
        Former::Lambda(body) | Former::Fixpoint(body) | Former::Shift(body) => {
            Vec::from([match admits {
                Admits::Computation(Tail::Unstated) => Slot::of(body, admits, Binds::ONE),
                Admits::Computation(Tail::Ends | Tail::Continues)
                | Admits::Type
                | Admits::ValueType
                | Admits::CompType
                | Admits::Value
                | Admits::Operand
                | Admits::Stated => ends(body, Binds::ONE),
            }])
        },
        // A thunk's body states its type only where the thunk's position
        // does: a definition's value, a family's argument; below any other
        // value, as a constructor's field, nothing states it.
        Former::Thunk(body) => match bodies {
            Bodies::Spelled if matches!(admits, Admits::Value | Admits::Operand) => {
                Vec::from([Slot::of(
                    body,
                    Admits::Computation(Tail::Unstated),
                    Binds::NONE,
                )])
            },
            Bodies::Spelled => Vec::from([ends(body, Binds::NONE)]),
            Bodies::Opaque => Vec::new(),
        },
        Former::Nested(body)
        | Former::Run(body)
        | Former::Returned(body)
        | Former::Project(_, body) => Vec::from([continues(body)]),
        Former::PathTransport {
            motive,
            path,
            value: transported,
        }
        | Former::Ride {
            motive,
            flow: path,
            value: transported,
        } => Vec::from([
            Slot::of(motive, Admits::ValueType, Binds::ONE),
            operand(path),
            operand(transported),
        ]),
        Former::TelescopeTransport {
            motive,
            path,
            start,
            over,
            value: transported,
        } => Vec::from([
            comp_type(motive),
            operand(path),
            operand(start),
            operand(over),
            operand(transported),
        ]),
        Former::Case { scrutinee, arity } => {
            let mut slots = Vec::from([value(scrutinee)]);
            slots.extend(components(arity, admits, Binds::ONE, None));
            slots
        },
        Former::Split {
            scrutinee,
            arity,
            body,
        } => Vec::from([
            value(scrutinee),
            Slot::of(
                body,
                admits,
                Binds::intuitionistic(OpenBinders(usize::from(arity))),
            ),
        ]),
        Former::DataCase {
            scrutinee,
            motive,
            arity,
        } => {
            let mut slots = Vec::from([value(scrutinee)]);
            if written == Motive::Written {
                slots.push(Slot::of(motive, Admits::CompType, Binds::ONE));
            }
            slots.extend((0_usize .. usize::from(arity)).map(|index| {
                let arm = arm(source, node, Component::from(index));
                Slot {
                    node: arm.body,
                    admits,
                    binds: Binds::intuitionistic(OpenBinders(arm.fields)),
                    label: None,
                }
            }));
            slots
        },
        Former::ListFold { list, nil, cons } | Former::ListCase { list, nil, cons } => Vec::from([
            value(list),
            Slot::of(nil, admits, Binds::NONE),
            Slot::of(cons, admits, Binds::intuitionistic(OpenBinders(2_usize))),
        ]),
        Former::Handle {
            subject,
            on_return,
            clauses: count,
        } => clauses(ends(subject, Binds::NONE), on_return, count),
        Former::Scope {
            subject,
            on_return,
            clauses: count,
            ..
        } => clauses(ends(subject, Binds::ONE), on_return, count),
        Former::Exercise {
            capability,
            payload,
            ..
        } => Vec::from([value(capability), value(payload)]),
        Former::Resume(stack, computation) => Vec::from([value(stack), continues(computation)]),
        Former::Reset(body) | Former::Migrate { body, .. } => Vec::from([ends(body, Binds::NONE)]),
        Former::Leta {
            value: opened,
            body,
        } => Vec::from([value(opened), Slot::of(body, admits, Binds::ONE)]),
        Former::Lazy(arity) => components(
            arity,
            Admits::Computation(Tail::Continues),
            Binds::NONE,
            None,
        ),
        Former::Ascription { body, ty } => {
            Vec::from([Slot::of(body, admits, Binds::NONE), comp_type(ty)])
        },
        // An offer's arm and a fork's child end in a computation the surface
        // reads only as one, `retire => pure unit`: no exit is elided there.
        Former::Offer { arms, .. } => components(
            arms,
            Admits::Computation(Tail::Continues),
            Binds::NONE,
            None,
        ),
        Former::Fork {
            protocol,
            child,
            parent,
        } => {
            let linear = Binds {
                zone: Zone::Linear,
                count: 1_usize,
            };
            Vec::from([
                value_type(protocol),
                Slot::of(child, Admits::Computation(Tail::Continues), linear),
                Slot::of(parent, admits, linear),
            ])
        },
        Former::Hold {
            value: held, body, ..
        } => Vec::from([
            value(held),
            Slot::of(body, admits, Binds {
                zone: Zone::Linear,
                count: 1_usize,
            }),
        ]),
        Former::Receive { body, .. } => Vec::from([Slot::of(body, admits, Binds {
            zone: Zone::Linear,
            count: 1_usize,
        })]),
        Former::Access {
            place, body, mode, ..
        } => {
            let mut slots = Vec::with_capacity(3_usize);
            if let gandr_core_term::memory::Place::At { index } = place {
                slots.push(value(index));
            }
            slots.push(ends(body, Binds {
                zone: Zone::Linear,
                count: 1_usize,
            }));
            if let AccessMode::Exclusive { unwind } = mode {
                slots.push(ends(unwind, Binds::NONE));
            }
            slots
        },
        Former::BaseType(_)
        | Former::Universe { .. }
        | Former::Abstract(_)
        | Former::Capability { .. }
        | Former::Variable { .. }
        | Former::Constant(_)
        | Former::Unit
        | Former::ListNil
        | Former::Literal(_)
        | Former::Reify
        | Former::Select { .. }
        | Former::Close(_)
        | Former::AbortView(_)
        | Former::Unreadable(_) => Vec::new(),
    }
}

/// The depth a former's children stand at.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one deeper than `depth` below a value former, saturating at the
///   counter ceiling; `depth` itself below any other former.
/// - provides: the value-depth count [`DEPTH_LIMIT`] bounds.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the exact cutoff and maximum counter distinguish missed
///   increments, increments in type positions and wrapping; the deep value
///   golden observes the resulting presentation boundary.
/// - witness: `walk::tests::depth_boundaries_preserve_precedence_and_saturation`
/// - witness: `tests::goldens::beyond_the_depth_limit_renders_deep`
#[spec(ensures: |ret| ret.0 == if kind == Kind::Value { depth.0.saturating_add(1_u32) } else { depth.0 })]
fn below(
    depth: ValueDepth,
    kind: Kind,
) -> ValueDepth
{
    if kind == Kind::Value {
        depth.deeper()
    }
    else {
        depth
    }
}

/// The grammar sort the text at a node is read in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Surface
{
    /// As an expression: a definition's body, an argument, a quoted type.
    Expression,
    /// As a type: a signature, an annotation, a type application's argument.
    Type,
}

/// The grammar sort a slot of `former`, spelled in `surface`, is read in.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a type for a type slot of a value or a computation that writes
///   itself — an annotation, a binder's type, a typed bind's result — where the
///   expression grammar embeds a type, and for a static abstraction's body,
///   which the grammar reads as a type; `surface` itself otherwise. A quote, a
///   nested or returned computation and an elided ascription write nothing of
///   their own, so their slot is read as they are; a type former's value slot
///   is read as the type is, since every type application reads its arguments
///   in the type's own sort and a path or a flow whose endpoints are codes is
///   over a universe, which reads them as types.
/// - provides: whether a quote in the slot stands where an expression reads.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a quote as an argument, as a definition's body, as a
///   static abstraction's body and as a decoded code in a type position
///   distinguish the slots an expression reads from those a type reads.
/// - witness: `tests::goldens::a_type_no_expression_reads_is_quoted_839`
/// - witness: `tests::goldens::a_quoted_chain_is_quoted_1127`
#[spec(ensures: |ret| ret == if matches!(*former, Former::StaticLambda(_)) || (!matches!(*former,
    Former::Quote(_) | Former::QuoteComputation(_) | Former::Nested(_) | Former::Returned(_) | Former::Ascription { .. })
    && matches!(kind(former), Kind::Value | Kind::Computation)
    && matches!(admits, Admits::Type | Admits::ValueType | Admits::CompType))
{
    Surface::Type
} else {
    surface
})]
fn surface_below<Node>(
    surface: Surface,
    former: &Former<'_, Node>,
    admits: Admits,
) -> Surface
{
    let writes_nothing = matches!(
        *former,
        Former::Quote(_)
            | Former::QuoteComputation(_)
            | Former::Nested(_)
            | Former::Returned(_)
            | Former::Ascription { .. }
    );
    // A static abstraction `\A. T` is a type form: its body is read as a type.
    let typed_body = matches!(*former, Former::StaticLambda(_));
    if typed_body
        || (!writes_nothing
            && matches!(kind(former), Kind::Value | Kind::Computation)
            && matches!(admits, Admits::Type | Admits::ValueType | Admits::CompType))
    {
        Surface::Type
    }
    else {
        surface
    }
}

/// How loosely a spelled piece binds, tightest first.
///
/// A piece stands bare in a slot that admits its binding and is parenthesized
/// in one that admits only tighter pieces. The order is the grammar's: an
/// atom, then the bridges and the keyword-led computations, then a word's
/// cons, then the infix `*`, `+` and `&` the sugared form writes, then the
/// relations `≃`, `≅` and `⇝` between types, then `->` and `=>`, then a
/// bind's statements. Every arity-shaped former is an atom, its entries
/// between its own delimiters.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Binding
{
    /// A qualified name `M.T`: an atom everywhere but a session type's
    /// payload, where the send's or receive's own `.` would end the payload at
    /// the path's first `.`, so it is parenthesized there, `!(M.T). S`.
    Qualified,
    /// A name, a literal, a universe, a bracketed or braced form, a call.
    Atom,
    /// `+U C`, `-F A`, `pure v`, `force v`, `run c`, `fn (x) { c }` or
    /// `thunk { c }`.
    Prefix,
    /// `g ∷ p`, a word's letter before the rest, nested to the right.
    Cons,
    /// `A * B`.
    Product,
    /// `A + B`.
    Sum,
    /// `C & D`.
    Lazy,
    /// `A ≃ B`, `A ≅ B` or `A ⇝ B`, nested to the right.
    Relation,
    /// `A -> C`, `(x : A) -> C`, `A => B`, or the static abstraction `\a. v`,
    /// whose body runs as far right as an arrow's codomain.
    Arrow,
    /// `run x <- c ; rest`, whose rest runs to the end of the block it stands
    /// in; anywhere else it is a block of its own, `{ … }`.
    Sequence,
}

/// One finished document and how it binds.
#[derive(Clone, Copy, Debug)]
struct Piece
{
    /// The document.
    doc: Doc,
    /// How loosely it binds.
    binding: Binding,
}

/// The argument a redex's binder stands for: its piece, and the binders its
/// spelling named, which occur in the reduct only where the binder does.
#[derive(Clone, Debug)]
struct Substituted
{
    /// The argument's spelling.
    piece: Piece,
    /// The positions of the binders the spelling named.
    occurring: BTreeSet<OpenBinders>,
}

/// One run of a session type's spelling: fixed text, or the payload type in a
/// slot.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Segment
{
    /// Text, written as it stands.
    Text(String),
    /// The payload type in this slot.
    Payload(PayloadSlot),
}

/// A pending step of a protocol's spelling.
#[derive(Clone, Copy, Debug)]
enum Spelling<'protocol>
{
    /// Spell the session type at this state.
    State(ProtocolState),
    /// Write fixed text.
    Text(&'static str),
    /// Write a branch's label and its colon.
    Label(&'protocol gandr_kernel_term::FieldLabel),
    /// Close the innermost recursion binder.
    Leave,
}

/// The nesting position of a recursion binder among the binders open around
/// it, outermost zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Nesting(usize);

impl Nesting
{
    /// The binder's name: `t`, then `t1`, `t2`, ….
    ///
    /// # Specification
    /// trivial.
    fn name(self) -> String
    {
        if self.0 == 0_usize {
            String::from("t")
        }
        else {
            format!("t{}", self.0)
        }
    }
}

/// The spelling of the session type `protocol` stands for at `state`, its
/// payload types left as slots, how loosely it binds, and whether it reads
/// every state it reaches.
///
/// # Specification
/// - requires: nothing; a state past the protocol spells `?`.
/// - ensures: `!` and `?` prefix their payload slot and `. ` their
///   continuation; a selection is `+{l : S, …}` and an offer `&{l : S, …}` in
///   label order; `end` is `end`; a `mu` is `mu t. S`, its binder named by its
///   nesting; a variable is its binder's name, and a variable whose binder
///   encloses the state rather than the spelling unfolds to that binder, so the
///   spelling is closed. A selection, an offer and `end` bind as atoms, every
///   other head as an arrow does.
/// - provides: the one session-type spelling both sources share, since both
///   read the same protocol.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` pops one pending step per iteration.
/// - measure: the protocol's nodes are reached along tree edges, and a variable
///   unfolds only to a binder no open binder repeats, which a contractive
///   protocol's finite binders bound.
/// - input recursion: none.
///
/// # Adequacy
/// - hypothesis: L3 — a recursive protocol with every former spells as the
///   grammar writes it at its root and at a state inside its recursion.
/// - witness: `tests::goldens::session_types_spell_their_protocol_and_payloads`
#[spec(ensures: |ret| ret.0.iter().all(|segment| match *segment {
    | Segment::Text(ref text) => !text.is_empty(),
    | Segment::Payload(slot) => protocol.nodes().iter().any(|node| {
        matches!(*node, ProtocolNode::Send { payload, .. } | ProtocolNode::Receive { payload, .. } if payload == slot)
    }),
}) && (protocol.node(state).is_ok() || ret.2 == Fidelity::Approximate) && (ret.1 == Binding::Atom)
    == matches!(protocol.node(state), Ok(&(ProtocolNode::Select(_) | ProtocolNode::Offer(_) | ProtocolNode::End))))]
fn protocol_template(
    protocol: &Protocol,
    state: ProtocolState,
) -> (Vec<Segment>, Binding, Fidelity)
{
    let mut segments = Vec::new();
    let mut text = String::new();
    let mut binders: Vec<ProtocolState> = Vec::new();
    let mut pending = Vec::from([Spelling::State(state)]);
    let mut fidelity = Fidelity::Faithful;
    while let Some(step) = pending.pop() {
        let at = match step {
            Spelling::Text(glyphs) => {
                text.push_str(glyphs);
                continue;
            },
            Spelling::Label(label) => {
                text.push_str(label.as_ref());
                text.push_str(" : ");
                continue;
            },
            Spelling::Leave => {
                let _closed = binders.pop();
                continue;
            },
            Spelling::State(at) => at,
        };
        match protocol.node(at) {
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a session state its protocol does not hold: a malformed protocol, \
                              with no session former to spell"
                )
            )]
            Err(_) => {
                fidelity = Fidelity::Approximate;
                text.push('?');
            },
            Ok(&ProtocolNode::Send { payload, next }) => {
                text.push('!');
                segments.push(Segment::Text(core::mem::take(&mut text)));
                segments.push(Segment::Payload(payload));
                text.push_str(". ");
                pending.push(Spelling::State(next));
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "the receive session type's own `?A. S`, which \
                              `receive_session_type` reads: an answer, not a placeholder"
                )
            )]
            Ok(&ProtocolNode::Receive { payload, next }) => {
                text.push('?');
                segments.push(Segment::Text(core::mem::take(&mut text)));
                segments.push(Segment::Payload(payload));
                text.push_str(". ");
                pending.push(Spelling::State(next));
            },
            Ok(&(ProtocolNode::Select(ref branches) | ProtocolNode::Offer(ref branches))) => {
                text.push_str(match protocol.node(at) {
                    Ok(&ProtocolNode::Offer(_)) => "&{",
                    _ => "+{",
                });
                pending.push(Spelling::Text("}"));
                for (position, (label, &target)) in branches.iter().enumerate().rev() {
                    pending.push(Spelling::State(target));
                    pending.push(Spelling::Label(label));
                    if position > 0_usize {
                        pending.push(Spelling::Text(", "));
                    }
                }
            },
            Ok(&ProtocolNode::End) => text.push_str("end"),
            Ok(&ProtocolNode::Mu(body)) => {
                text.push_str("mu ");
                text.push_str(&Nesting(binders.len()).name());
                text.push_str(". ");
                binders.push(at);
                pending.push(Spelling::Leave);
                pending.push(Spelling::State(body));
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    linear_search_in_loop,
                    reason = "bounded: `binders` holds the `mu`s open around one session type, \
                              innermost last"
                )
            )]
            Ok(&ProtocolNode::Recur(binder)) => {
                match binders.iter().rposition(|&open| open == binder) {
                    Some(position) => text.push_str(&Nesting(position).name()),
                    None => pending.push(Spelling::State(binder)),
                }
            },
        }
    }
    if !text.is_empty() {
        segments.push(Segment::Text(text));
    }
    let binding = match protocol.node(state) {
        Ok(&(ProtocolNode::Select(_) | ProtocolNode::Offer(_) | ProtocolNode::End)) => {
            Binding::Atom
        },
        _ => Binding::Arrow,
    };
    (segments, binding, fidelity)
}

/// The fixed name the surface spells the sum `node` by: `Bool` for two
/// components, each the empty product.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: `Bool` exactly when `node` reads as a sum of two components that
///   both read as the product of none; none otherwise.
/// - provides: the one reading of `Bool` the spelling and the quote share, as
///   the lowering reads the fixed name.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `Bool`, a sum of a unit and an integer, and a sum of one
///   unit spell apart.
/// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
#[spec(ensures: |ret| ret.is_some() == (matches!(source.read(node), Former::Sum(arity) if usize::from(arity) == 2_usize)
    && [0_usize, 1_usize].into_iter().all(|index| source.component(node, Component::from(index))
        .is_some_and(|part| matches!(source.read(part), Former::Product(inner) if usize::from(inner) == 0_usize))))
    && ret.is_none_or(|name| name.0 == "Bool"))]
fn named_sum<S>(
    source: &S,
    node: S::Node,
) -> Option<Glyphs<'static>>
where
    S: Source + ?Sized,
{
    let two_units = matches!(source.read(node), Former::Sum(arity) if usize::from(arity) == 2_usize)
        && [0_usize, 1_usize].into_iter().all(|index| {
            source
                .component(node, Component::from(index))
                .is_some_and(|part| {
                    matches!(source.read(part), Former::Product(inner) if usize::from(inner) == 0_usize)
                })
        });
    two_units.then_some(Glyphs("Bool"))
}

/// Whether an expression reads a type written bare where it stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Bare
{
    /// It reads, as the code of the type.
    Reads,
    /// It does not: a part of it reads as another form or not at all.
    Unread,
}

/// The bridges between the sorts, and the keywords that lead a computation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Prefix
{
    /// The suspension `+U C`.
    Thunk,
    /// The returner `-F A`.
    Returner,
    /// A returner where the body goes on, `pure v`.
    Pure,
    /// A force, `force v`.
    Force,
    /// A run where a value is read, `run c`.
    Run,
}

/// The delimiters of the arity-shaped formers, one per polarity of the
/// former.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Brace
{
    /// `#{…}`: a product, a tuple, a record type or a record.
    Hash,
    /// `+{…}`: a sum or an injection.
    Plus,
    /// `&{…}`: a lazy product.
    Ampersand,
}

impl Brace
{
    /// The opening delimiter.
    ///
    /// # Specification
    /// - ensures: `#{` for [`Self::Hash`], `+{` for [`Self::Plus`] and `&{` for
    ///   [`Self::Ampersand`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — products, sums and lazy products in the grammar
    ///   fixtures distinguish a swapped delimiter.
    /// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
    #[spec(ensures: |ret| matches!((self, ret.0.as_bytes()),
        (Self::Hash, b"#{") | (Self::Plus, b"+{") | (Self::Ampersand, b"&{")
    ))]
    const fn opener(self) -> Glyphs<'static>
    {
        match self {
            Self::Hash => Glyphs("#{"),
            Self::Plus => Glyphs("+{"),
            Self::Ampersand => Glyphs("&{"),
        }
    }
}

/// What an entry of a braced former is written after.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Label
{
    /// A record type's field label: `l : A`.
    Field,
    /// A record's field label: `.l = a`.
    Assignment,
    /// The summand an injection enters: `.i = v`.
    Summand,
}

/// How the entries of a braced former are written.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Entries
{
    /// By position alone.
    Positional,
    /// Each after its label.
    Labelled(Label),
}

/// The bracketed value formers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Bracket
{
    /// A stack classifier with ordered computation endpoints.
    Stack,
    /// The native list former, `List(A)`.
    List,
    /// A native path classifier.
    PathUniverse,
    /// Element identity, `here(a)`.
    Here,
    /// Function extensionality, `funext(f, g)`.
    Funext,
    /// A universe equivalence, `equiv(f, g)`.
    Equiv,
    /// Univalence, `ua(e)`.
    Univalence,
    /// Native reflexivity.
    PathRefl,
    /// A native equivalence's maps.
    PathEquiv,
    /// A native product path.
    PathProduct,
    /// A native cell, `cons(head, tail)`.
    ListCons,
    /// A session equivalence, `bisim(a, b)`.
    Bisim,
    /// A session simulation, `sim(a, b)`.
    Sim,
    /// Directed reflexivity, `stay(a)`.
    Stay,
    /// A path's inverse, `back(p)`.
    Back,
    /// A map's action on a path, `cong(f, p)`.
    Cong,
    /// The product of two universe flows, `flowProduct(p, q)`.
    FlowProduct,
    /// A forward flow, `forward(f)`.
    Forward,
    /// A function flow, `arrow(d, c)`.
    Arrow,
    /// The recorded runs of a session code, `Run(s)`.
    Run,
    /// A type quoted where an expression stands, `type(T)`.
    TypeQuote,
}

impl Bracket
{
    /// The head and opening parenthesis a bracketed former is spelled with.
    ///
    /// # Specification
    /// trivial.
    const fn opener(self) -> Glyphs<'static>
    {
        Glyphs(match self {
            Self::Stack => "Stack(",
            Self::List => "List(",
            Self::PathUniverse => "Path_U(",
            Self::Here => "here(",
            Self::Funext => "funext(",
            Self::Equiv | Self::PathEquiv => "equiv(",
            Self::Univalence => "ua(",
            Self::PathRefl => "refl(",
            Self::PathProduct => "pathProduct(",
            Self::ListCons => "cons(",
            Self::Bisim => "bisim(",
            Self::Sim => "sim(",
            Self::Stay => "stay(",
            Self::Back => "back(",
            Self::Cong => "cong(",
            Self::FlowProduct => "flowProduct(",
            Self::Forward => "forward(",
            Self::Arrow => "arrow(",
            Self::Run => "Run(",
            Self::TypeQuote => "type(",
        })
    }
}

/// The infix type formers the sugared form writes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Infix
{
    /// The eager product `A * B * …`, a chain of one product.
    Product,
    /// The sum `A + B + …`, a chain of one sum.
    Sum,
    /// The lazy product `C & D & …`, a chain of one lazy product.
    Lazy,
}

impl Infix
{
    /// The symbol between two operands, after the space before it.
    ///
    /// # Specification
    /// trivial.
    const fn symbol(self) -> Glyphs<'static>
    {
        Glyphs(match self {
            Self::Product => " *",
            Self::Sum => " +",
            Self::Lazy => " &",
        })
    }

    /// How loosely the spelled chain binds.
    ///
    /// # Specification
    /// trivial.
    const fn binding(self) -> Binding
    {
        match self {
            Self::Product => Binding::Product,
            Self::Sum => Binding::Sum,
            Self::Lazy => Binding::Lazy,
        }
    }

    /// The loosest operand of the chain stands bare as: every operand tighter
    /// than the chain, since the lowering reads an unparenthesized inner chain
    /// as more components of the outer one.
    ///
    /// # Specification
    /// trivial.
    const fn operand(self) -> Binding
    {
        match self {
            Self::Product => Binding::Prefix,
            Self::Sum => Binding::Product,
            Self::Lazy => Binding::Sum,
        }
    }
}

/// How one join combines the finished pieces below it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Join
{
    /// A bridge over one operand.
    Prefix(Prefix),
    /// A returner prefixed by its row of interfaces, `-F [I, …] `.
    EffectReturner(Doc),
    /// A braced former over this many entries.
    Braced
    {
        /// Its delimiter.
        brace: Brace,
        /// How many entries it holds.
        arity: Arity,
        /// Whether each entry is written after a label, finished just below
        /// it.
        entries: Entries,
    },
    /// An infix chain over this many operands, two or more.
    Infix
    {
        /// Its former.
        infix: Infix,
        /// How many operands it joins.
        arity: Arity,
    },
    /// A tuple of this many components, two or more, `(a, b)`.
    Tuple(Arity),
    /// The value-function alias over this many domains and then its
    /// codomain: `() => C`, `A => C`, `(A, B) => C`; where an occurrence named
    /// a dependent arrow's binder, the thunk over the arrows it stands for.
    ValueFunction(Arity, Dependent),
    /// An arrow over its domain and codomain.
    Arrow,
    /// A dependent arrow over its domain and codomain, its binder named by the
    /// binders open where the join runs; written as the plain arrow when the
    /// walk spelled every node so far and no occurrence named its binder.
    Pi,
    /// A dependent pair type over its two factors, its first label named as
    /// a dependent arrow's binder is and its second by the next name.
    Sigma,
    /// A static abstraction over its body, its binder named as a dependent
    /// arrow's is.
    StaticLambda,
    /// An operator applied to this many arguments: the spine of static
    /// applications it was written as, or of a call.
    Apply(Arity),
    /// A bind over the computation it runs and the rest, its binder named as
    /// a dependent arrow's is.
    Sequence,
    /// A typed bind over the computation it ascribes, the value type its
    /// returner returns, and the rest under the bind's binder, named as a
    /// dependent arrow's is: `run x : A <- c ; rest`.
    TypedSequence,
    /// A lambda over its body, its binder named as a dependent arrow's is.
    Lambda,
    /// A thunk over its body.
    Thunk,
    /// A bracketed value former over its items.
    Bracket(Bracket),
    /// Univalence at a stratum over its two translator records, after the
    /// head spelling its stratum and its descriptions, `ua[n, k](a, b,`.
    Ua(Doc),
    /// A session type over its payloads, spelled by the template the visit
    /// pushed, binding as the template's head does.
    Session
    {
        /// How many payload pieces it takes, in slot order.
        payloads: Arity,
        /// How loosely the spelling binds.
        binding: Binding,
    },
    /// A former spelled by the parts the visit pushed, over this many child
    /// pieces, binding as given.
    Form
    {
        /// How many child pieces its parts take, in reading order.
        pieces: Arity,
        /// How loosely the spelling binds.
        binding: Binding,
    },
}

/// The grammar rule a production of the walk writes, named at the arm that
/// writes it, as the grammar's builders name it.
///
/// Every rule the grammar builds is written by some arm or is listed with the
/// reason no presentation writes it, and every name here is a rule the grammar
/// builds: the policy library's `mold_coverage` holds the two sets equal at
/// compile time, reading this constructor's literal at every arm and the
/// grammar's builder sources (`check:dylint`'s `productions` table). The name
/// is read there, never at run time.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Production(&'static str);

/// `produced`, the production of `rule`.
///
/// # Specification
/// trivial.
#[inline]
const fn writes<T>(
    rule: Production,
    produced: T,
) -> T
{
    let _ = rule;
    produced
}

/// The bound call and the rest of `node` when it is a run binding a call, `x
/// ← f(a); …`: a bind whose bound computation applies a forced value to at
/// least one argument.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the bind's bound and rest exactly when `node` reads as a bind
///   whose bound reads as an application whose spine, read down through every
///   application, ends at a force; absent otherwise.
/// - provides: the runs [`Walk::inlined`] spells as the calls they bind.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// Every turn reads one application nearer the spine's head, a finite term.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Walk::inlined`].
/// - witness: `tests::goldens::a_run_bound_call_in_a_type_prints_nested_676`
#[spec(ensures: |ret| ret.is_none() || matches!(source.read(node), Former::Bind(..)))]
fn bound_call<S>(
    source: &S,
    node: S::Node,
) -> Option<(S::Node, S::Node)>
where
    S: Source + ?Sized,
{
    let Former::Bind(bound, rest) = source.read(node)
    else {
        return None;
    };
    let Former::Application(mut head, _) = source.read(bound)
    else {
        return None;
    };
    while let Former::Application(inner, _) = source.read(head) {
        head = inner;
    }
    matches!(source.read(head), Former::Force(_)).then_some((bound, rest))
}

/// A derived path operation a transport is the derivation of
/// (`gandr_core_term::identity`), over the nodes its spelling writes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Derived<Node>
{
    /// `p then q`: `transport(\y. Path(A, a, y), q, p)`.
    Composite
    {
        /// The first path, the transported value.
        value: Node,
        /// The second path, along which it moves.
        path: Node,
    },
    /// `back(p)`: `transport(\y. Path(A, y, a), p, here(a))`.
    Inverse(Node),
    /// `cong(f, p)`: `transport(\y. Path(B, f(a), f(y)), p, here(f(a)))`.
    Congruence
    {
        /// The map, as the motive holds it, one binder deeper.
        map: Node,
        /// The path it acts on.
        path: Node,
    },
}

/// The derived path operation `body` is the transport of: a path transport
/// whose motive is `Path(A, a, y)` over its own binder `y` (a composite), or
/// `Path(A, y, a)` moving reflexivity, `here(a)` or the empty word at a looped
/// point `a` (an inverse), or `Path(B, f(a), f(y))` moving `here` (an action
/// on a path), where every other part of the
/// motive names no `y`.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: the operation exactly when `body` reads as a path transport whose
///   motive reads as a path type with one endpoint the intuitionistic variable
///   of index zero, or for an action the forced map applied to it and returned
///   and the other endpoint the same map, the same constant or variable,
///   applied and returned; an inverse moves `here` or a nullary constructor,
///   the only one a path type at a looped point holds, and an action moves
///   `here`. The motive's carrier, its other endpoint and an action's map, read
///   down through every child [`children`] lists, name no intuitionistic
///   variable counting out to the motive's binder; absent otherwise, and absent
///   when that scan reads more than [`VISIT_BUDGET`] nodes. A well-typed
///   transport of these shapes moves the reflexivity at the endpoint the
///   derivation would, up to conversion, so the operation stands for it.
/// - provides: the shapes `p then q`, `back(p)` and `cong(f, p)` derive
///   (`gandr_core_term::identity`), which the sugared form writes as the
///   lowering reads them back.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// Every turn pops one pending node and spends one of at most
/// [`VISIT_BUDGET`] visits.
///
/// # Adequacy
/// - hypothesis: L3 — a composite of two loops and a transport whose fixed
///   endpoint names the motive's binder, an inverse and an action on a loop; a
///   scan that skipped the endpoints, read the wrong index or ignored the
///   binder count fails the goldens.
/// - witness: `tests::goldens::a_returned_composite_of_paths_is_written_infix_754`
/// - witness: `tests::goldens::an_inverse_and_an_action_on_a_path_are_written_as_derived_778`
#[spec(ensures: |ret| ret.is_none() || matches!(source.read(body), Former::PathTransport { .. }))]
fn derived<S>(
    source: &S,
    body: S::Node,
) -> Option<Derived<S::Node>>
where
    S: Source + ?Sized,
{
    let Former::PathTransport {
        motive,
        path,
        value,
    } = source.read(body)
    else {
        return None;
    };
    let Former::Path {
        carrier,
        left,
        right,
    } = source.read(motive)
    else {
        return None;
    };
    let moving = |node: S::Node| {
        matches!(
            source.read(node),
            Former::Variable {
                zone: Zone::Intuitionistic,
                index,
            } if u32::from(index) == 0_u32
        )
    };
    let reflexive = matches!(source.read(value), Former::Here(_));
    // A nullary constructor at `Path(A, a, a)` is the empty word of the words
    // at a looped point `a`, which an inverse moves there.
    let empty = matches!(source.read(value), Former::Constructor { arity, .. } if usize::from(arity) == 0_usize);
    // The map applied and returned, as an action's endpoints are: `f(x)`.
    let image = |node: S::Node| {
        if let Former::Returned(applied) = source.read(node)
            && let Former::Application(forced, argument) = source.read(applied)
            && let Former::Force(map) = source.read(forced)
        {
            Some((map, argument))
        }
        else {
            None
        }
    };
    // The same map, by what it reads as: a constant or a variable.
    let same = |one: S::Node, other: S::Node| match (source.read(one), source.read(other)) {
        (Former::Constant(one), Former::Constant(other)) => one == other,
        (
            Former::Variable { zone, index },
            Former::Variable {
                zone: other_zone,
                index: other_index,
            },
        ) => zone == other_zone && index == other_index,
        _ => false,
    };
    // The parts of the motive that must not name its binder, with the
    // operation they make.
    let (operation, apart) = if moving(right) {
        (Derived::Composite { value, path }, [carrier, left, carrier])
    }
    else if moving(left) && (reflexive || empty) {
        (Derived::Inverse(path), [carrier, right, carrier])
    }
    else if reflexive
        && let Some((map, argument)) = image(right)
        && moving(argument)
        && let Some((fixed, _)) = image(left)
        && same(map, fixed)
    {
        (Derived::Congruence { map, path }, [carrier, left, map])
    }
    else {
        return None;
    };
    let [ty, endpoint, other] = apart;
    let mut pending = Vec::from([
        (ty, Admits::ValueType, 0_usize),
        (endpoint, Admits::Value, 0_usize),
        (other, Admits::Value, 0_usize),
    ]);
    let mut visits = 0_u32;
    while let Some((node, admits, above)) = pending.pop() {
        visits = visits
            .checked_add(1_u32)
            .filter(|&visits| visits <= VISIT_BUDGET)?;
        let former = source.read(node);
        if let Former::Variable {
            zone: Zone::Intuitionistic,
            index,
        } = former
            && usize::try_from(u32::from(index)).ok()? == above
        {
            return None;
        }
        for slot in children(source, node, &former, admits, Bodies::Spelled) {
            let Some(child) = slot.node
            else {
                continue;
            };
            let deeper = if slot.binds.zone == Zone::Intuitionistic {
                above.checked_add(slot.binds.count)?
            }
            else {
                above
            };
            pending.push((child, slot.admits, deeper));
        }
    }
    Some(operation)
}

/// The former the walk reads at `node` in `form`, in a position admitting
/// `admits`: the source's, but in the sugared form a returned transport that
/// a derived path operation builds reads as that operation, `p then q`,
/// `back(p)` or `cong(f, p)`, where the position states its type.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: [`Former::Then`], [`Former::Back`] or [`Former::Cong`] over what
///   [`derived`] answers when `form` is [`Form::Sugared`], `admits` is not
///   [`Admits::Operand`] and `node` reads as [`Former::Returned`] over a body
///   [`derived`] answers; what `source` reads at `node` otherwise.
/// - provides: the one read of each node the walk visits.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each operation's golden in both forms and as a
///   transport's operand; a read that rewrote the explicit form, a transport
///   standing as a computation rather than a returned value, or an operation
///   written where nothing states its type changes a spelling.
/// - witness: `tests::goldens::a_returned_composite_of_paths_is_written_infix_754`
/// - witness: `tests::goldens::a_composite_a_transport_moves_stays_explicit_815`
/// - witness: `tests::goldens::an_inverse_and_an_action_on_a_path_are_written_as_derived_778`
#[spec(ensures: |ref ret| (form == Form::Sugared && admits != Admits::Operand)
    || core::mem::discriminant(ret) == core::mem::discriminant(&source.read(node)))]
fn reading<S>(
    source: &S,
    node: S::Node,
    form: Form,
    admits: Admits,
) -> Former<'_, S::Node>
where
    S: Source + ?Sized,
{
    let former = source.read(node);
    if form == Form::Sugared
        && admits != Admits::Operand
        && let Former::Returned(body) = former
        && let Some(operation) = derived(source, body)
    {
        return match operation {
            Derived::Composite { value, path } => Former::Then(value, path),
            Derived::Inverse(path) => Former::Back(path),
            Derived::Congruence { map, path } => Former::Cong(map, path),
        };
    }
    former
}

/// A name as a former spelled by parts writes it: the name itself, or `?`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Written(Cow<'static, str>);

impl From<Written> for Cow<'static, str>
{
    /// The text written.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(written: Written) -> Self
    {
        written.0
    }
}

/// One run of a former's spelling by parts.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Part
{
    /// Text, written as it stands.
    Text(Cow<'static, str>),
    /// The next child's piece, bare when it binds at most this loosely, a
    /// block when it is a bind's statements, parenthesized otherwise.
    Piece(Binding),
    /// The name of the binder at this offset among those the former's
    /// children open.
    Binder(usize),
    /// The linear variable at this index, by its binder's name.
    Endpoint(DeBruijnIndex),
    /// A space, or a line break indented two columns.
    Space,
    /// Nothing, or a line break.
    Tight,
    /// A line break that breaks with the block around it.
    Line,
    /// The parts so far are a block's head, ending with its opening brace.
    Open,
    /// The block opened last ends: its body two columns in, the brace
    /// closing it on a line of its own.
    Close,
}

/// The parts of one former's spelling as they are built, and how many child
/// pieces they take.
#[derive(Debug, Default)]
struct Parts
{
    /// The parts, in writing order.
    parts: Vec<Part>,
    /// How many of them are child pieces.
    pieces: usize,
}

impl Parts
{
    /// Appends `part`; a child piece is counted.
    ///
    /// # Specification
    /// trivial.
    fn part(
        &mut self,
        part: Part,
    ) -> &mut Self
    {
        if matches!(part, Part::Piece(_)) {
            self.pieces = self.pieces.saturating_add(1_usize);
        }
        self.parts.push(part);
        self
    }

    /// Appends fixed or computed text.
    ///
    /// # Specification
    /// trivial.
    fn text(
        &mut self,
        text: impl Into<Cow<'static, str>>,
    ) -> &mut Self
    {
        self.part(Part::Text(text.into()))
    }

    /// Appends the next child's piece, bare up to `loosest`.
    ///
    /// # Specification
    /// trivial.
    fn piece(
        &mut self,
        loosest: Binding,
    ) -> &mut Self
    {
        self.part(Part::Piece(loosest))
    }

    /// Appends `, ` and a soft line before every entry of a block but the
    /// first, `index` counting the entries.
    ///
    /// # Specification
    /// trivial.
    fn separated(
        &mut self,
        index: Component,
    ) -> &mut Self
    {
        if usize::from(index) > 0_usize {
            let _ = self.text(",").part(Part::Line);
        }
        self
    }

    /// Appends the names of the first `count` binders the children open,
    /// separated by `, `.
    ///
    /// # Specification
    /// trivial.
    fn binders(
        &mut self,
        count: Arity,
    ) -> &mut Self
    {
        for offset in 0_usize .. count.0 {
            if offset > 0_usize {
                let _ = self.text(", ");
            }
            let _ = self.part(Part::Binder(offset));
        }
        self
    }

    /// Appends `count` more arguments of a call already opened, each after a
    /// comma, then the closing parenthesis.
    ///
    /// # Specification
    /// trivial.
    fn rest(
        &mut self,
        count: Arity,
    ) -> &mut Self
    {
        for _ in 0_usize .. count.0 {
            let _ = self.text(",").part(Part::Space).piece(Binding::Sequence);
        }
        self.part(Part::Tight).text(")")
    }

    /// Appends a call's `count` arguments between parentheses.
    ///
    /// # Specification
    /// trivial.
    fn arguments(
        &mut self,
        count: Arity,
    ) -> &mut Self
    {
        let _ = self.text("(");
        for index in 0_usize .. count.0 {
            if index > 0_usize {
                let _ = self.text(",").part(Part::Space);
            }
            let _ = self.piece(Binding::Sequence);
        }
        self.part(Part::Tight).text(")")
    }

    /// Appends a block over the next child's piece: the parts so far its
    /// head, ending with its opening brace.
    ///
    /// # Specification
    /// trivial.
    fn body(&mut self) -> &mut Self
    {
        self.part(Part::Open)
            .piece(Binding::Sequence)
            .part(Part::Close)
    }
}

/// The codomain of a value-function alias, as [`Walk::alias`] found it.
#[derive(Clone, Copy, Debug)]
enum Codomain<Node>
{
    /// The value type the chain's returner returns.
    Result(Node),
    /// A static redex whose reduct is the returner.
    Reduct(Node),
}

/// One arrow of a value-function alias's chain, as [`Walk::alias`] found it.
#[derive(Clone, Copy, Debug)]
struct Link<Node>
{
    /// The arrow's domain.
    domain: Node,
    /// The arrow itself where it is dependent, which opens a binder over the
    /// arrows after it and may write that binder's name.
    opener: Option<Node>,
}

/// The arrows of a value-function alias's chain that are dependent, one bit
/// per arrow from the outermost: each opens a binder over the arrows after
/// it, and the chain is written as the alias only where no occurrence names
/// one (#736).
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Dependent(u64);

/// A value-function alias as [`Walk::alias`] found it: its arrows, outermost
/// first, which of them are dependent, and its codomain.
type AliasChain<Node> = (Vec<Link<Node>>, Dependent, Codomain<Node>);

/// How a static redex's reduct is spelled.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ReductAs
{
    /// As the term it is.
    Term,
    /// As the value type it returns, the codomain of an alias.
    Result,
}

/// One unit of the walk's pending work.
#[derive(Clone, Copy, Debug)]
enum Task<Node>
{
    /// Spell one node in a position admitting `admits`.
    Visit
    {
        /// The node.
        node: Node,
        /// What the position admits.
        admits: Admits,
        /// How many value formers enclose the node.
        depth: ValueDepth,
    },
    /// Spell the value type a computation type returns, as the codomain of a
    /// value-function alias: the returner's result, read on through the
    /// static redexes, decodes and quotes [`Walk::alias`] read through to it.
    Returned
    {
        /// The computation type.
        node: Node,
        /// How many value formers enclose the node.
        depth: ValueDepth,
    },
    /// Open a binder in a zone, of the former whose child follows: the former
    /// itself when it opens that one binder, whose name the source may write.
    Bind(Zone, Option<Node>),
    /// Open the binder that names a region — a capability scope's capability
    /// or a hold's held name — as [`Task::Bind`] does, its region the
    /// innermost the walk is inside.
    BindScope(Zone, Option<Node>),
    /// Close the innermost binder.
    Unbind,
    /// Set the occurrences named so far aside, so the argument visited next
    /// collects its own: the binder a redex opens for it credits them only
    /// where the reduct reads the binder.
    Hold,
    /// Open one binder per finished piece of the top this many, the deepest
    /// outermost, each standing for its piece: the binders of a static redex's
    /// abstraction, bound to the arguments it is applied to.
    Substitute(Arity),
    /// Spell a component the source did not answer, as `?`.
    Missing,
    /// Spell the label an entry is written after.
    Label(Labelled<Node>),
    /// Combine finished pieces.
    Join(Join),
    /// Read the nodes visited next in this grammar sort.
    Surface(Surface),
}

/// What a walk produced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Walked
{
    /// The document of the root, and whether it says the whole of it.
    Built
    {
        /// The root's document.
        doc: Doc,
        /// Whether every node was spelled in full.
        fidelity: Fidelity,
        /// Why each `?` the document holds was written.
        unspelled: BTreeSet<Unspelled>,
    },
    /// The source took more visits than one presentation makes.
    OverBudget,
}

/// The names generated binders take, by position.
///
/// The names are `a`, `b`, …, `z`, then `a1`, `b1`, …, skipping every name a
/// node of the term already spells, so a binder never reads as a constant or
/// an abstract type the term mentions.
#[derive(Debug)]
struct Binders<'names>
{
    /// The names the term's constants and abstract types spell.
    mentioned: BTreeSet<Name<'names>>,
    /// The names generated so far, outermost binder first.
    generated: Vec<BinderName>,
    /// The next candidate to consider.
    next: Ordinal,
}

impl<'names> Binders<'names>
{
    /// Binders that avoid every name in `mentioned`.
    ///
    /// # Specification
    /// trivial.
    const fn new(mentioned: BTreeSet<Name<'names>>) -> Self
    {
        Self {
            mentioned,
            generated: Vec::new(),
            next: Ordinal(0_u32),
        }
    }

    /// The name of the binder at `position`, outermost first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: cached positions borrow their stored names; distinct
    ///   positions answer distinct names; no answer is a mentioned name.
    /// - provides: the binder of a dependent arrow, a static abstraction, a
    ///   lambda or a bind, and the occurrences that name it.
    /// - fails: [`binder::Absent::Exhausted`] when the candidate counter cannot
    ///   advance, before issuing its maximum ordinal; cached names still
    ///   resolve.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested arrows and a mentioned first name distinguish
    ///   capture and reordered generation. A counter at its maximum exposes the
    ///   refusal boundary and verifies that cached positions remain available;
    ///   the intervening billions of candidates are not allocated.
    /// - witness: `tests::goldens::long_dependent_function_type_breaks_at_the_narrow_page`
    /// - witness: `tests::goldens::a_binder_skips_the_names_the_type_mentions`
    /// - witness: `walk::tests::binder_exhaustion_preserves_existing_names`
    #[spec(
        captures: [cached = self.generated.get(position.0).map(|name| name.0.as_ptr())],
        ensures: |ret| match ret {
            | Maybe::Present(name) => cached.is_none_or(|held| core::ptr::eq(held, name.0.as_ptr()))
                && name.0.as_bytes().first().is_some_and(u8::is_ascii_lowercase)
                && name.0.get(1..).is_some_and(|round| round.is_empty()
                    || round.parse::<u32>().is_ok_and(|value| value > 0_u32)),
            | Maybe::Absent(_) => cached.is_none(),
        },
    )]
    fn name_at(
        &mut self,
        position: OpenBinders,
    ) -> Maybe<&BinderName, binder::Absent>
    {
        while self.generated.len() <= position.0 {
            let Maybe::Present(name) = candidate(self.next)
            else {
                return Maybe::Absent(binder::Absent::Exhausted);
            };
            let Some(next) = self.next.0.checked_add(1_u32)
            else {
                return Maybe::Absent(binder::Absent::Exhausted);
            };
            self.next = Ordinal(next);
            if !self.mentioned.contains(name.0.as_str()) {
                self.generated.push(name);
            }
        }
        self.generated
            .get(position.0)
            .map_or(Maybe::Absent(binder::Absent::Exhausted), Maybe::Present)
    }
}

/// The candidate binder name at `ordinal`: a letter, then the round after the
/// first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `a` through `z` for the first twenty-six ordinals, then the
///   letters again followed by their round; distinct ordinals answer distinct
///   names.
/// - provides: the candidates [`Binders::name_at`] filters.
/// - fails: never on a representable ordinal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — alphabet endpoints, two round transitions and the maximum
///   ordinal distinguish off-by-one letters, missing suffixes and overflow. The
///   remaining ordinal interval is not enumerated.
/// - witness: `walk::tests::candidate_names_cross_rounds_without_losing_the_last_ordinal`
/// - witness: `tests::goldens::a_binder_skips_the_names_the_type_mentions`
#[spec(ensures: |ref ret| match *ret {
    | Maybe::Present(ref name) => {
        let letter = name.0.as_bytes().first().copied().and_then(|byte| byte.checked_sub(b'a'));
        let round = name.0.get(1..).and_then(|text| if text.is_empty() { Some(0_u32) } else { text.parse::<u32>().ok() });
        letter.is_some_and(|offset| offset < 26_u8)
            && round.and_then(|value| value.checked_mul(26_u32))
                .and_then(|base| base.checked_add(u32::from(letter?))) == Some(ordinal.0)
    },
    | Maybe::Absent(_) => false,
})]
fn candidate(ordinal: Ordinal) -> Maybe<BinderName, binder::Absent>
{
    let letters = 26_u32;
    let (Some(offset), Some(round)) = (
        ordinal.0.checked_rem(letters),
        ordinal.0.checked_div(letters),
    )
    else {
        return Maybe::Absent(binder::Absent::Exhausted);
    };
    let Some(letter) = u8::try_from(offset)
        .ok()
        .and_then(|offset| b'a'.checked_add(offset))
    else {
        return Maybe::Absent(binder::Absent::Exhausted);
    };
    let letter = char::from(letter);
    Maybe::Present(BinderName(if round == 0_u32 {
        String::from(letter)
    }
    else {
        format!("{letter}{round}")
    }))
}

/// Every constant or abstract-type name encountered under `root`, including
/// malformed names that the spelling pass will replace with `?`.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: the names encountered from `root` in a position admitting
///   `admits`, its thunks read as `bodies` says, at most one distinct name per
///   allowed visit; absent when that scan takes more than the visit budget.
/// - provides: the names binders must avoid, and the bound on the walk.
/// - fails: never; an over-long scan is an absence.
/// - panics: none.
/// - intension: the walk's traversal on an explicit stack, stopped by [`reach`]
///   and descending by [`children`] exactly as the walk does.
///
/// # Adequacy
/// - hypothesis: L3 — a stable cyclic source refuses, and a binder skips an
///   encountered name. The retained scan-to-walk mutation fixture bounds only
///   subsequent traversal, not name consistency for changing sources.
/// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
/// - witness: `tests::goldens::a_binder_skips_the_names_the_type_mentions`
/// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
/// - witness: `walk::tests::the_name_scan_visits_exactly_its_budget`
#[spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref names) => u32::try_from(names.len()).is_ok_and(|count| count <= VISIT_BUDGET),
    Maybe::Absent(scan::Absent::OverBudget) => true,
})]
fn mentioned<S>(
    source: &S,
    root: S::Node,
    admits: Admits,
    bodies: Bodies,
) -> Maybe<BTreeSet<Name<'_>>, scan::Absent>
where
    S: Source + ?Sized,
{
    let mut names = BTreeSet::new();
    let mut pending = Vec::from([(root, admits, ValueDepth::ROOT)]);
    let mut visits = 0_u32;
    while let Some((node, admits, depth)) = pending.pop() {
        visits = visits.saturating_add(1_u32);
        if visits > VISIT_BUDGET {
            return Maybe::Absent(scan::Absent::OverBudget);
        }
        let former = source.read(node);
        let kind = kind(&former);
        if reach(admits, depth, kind) != Reach::Spell {
            continue;
        }
        if let Former::Abstract(name)
        | Former::Constant(name)
        | Former::Data {
            name: Some(name), ..
        }
        | Former::Codata {
            name: Some(name), ..
        }
        | Former::Constructor {
            name: Some(name), ..
        }
        | Former::Primitive { name, .. } = former
        {
            let _fresh = names.insert(name);
        }
        let below = below(depth, kind);
        for slot in children(source, node, &former, admits, bodies)
            .into_iter()
            .rev()
        {
            if let Some(child) = slot.node {
                pending.push((child, slot.admits, below));
            }
        }
    }
    Maybe::Present(names)
}

/// The names of binders opened above every one of `roots`, one per entry of
/// `preferred`, outermost first: each entry's name when no root mentions it,
/// it is not `taken` and no earlier binder took it, otherwise the next
/// generated name that is none of these.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: one distinct name per entry of `preferred`, none mentioned by a
///   root, each scanned at the position admitting its [`Admits`] with its
///   thunks spelled, and none `taken`; a preferred name where it is such a
///   name, otherwise the candidates in their order. Absent when a scan takes
///   more than the visit budget or the candidates run out.
/// - provides: the parameters a recursive definition's header binds, which the
///   binders its body opens avoid as they avoid a context name.
/// - fails: never; an over-long scan or exhausted candidates is an absence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a header over a body that mentions the first candidate
///   names its parameter past it, a preferred name the body mentions is passed
///   over, and two parameters take distinct names; other mutations of the scan
///   are those of [`mentioned`].
/// - witness: `tests::goldens::a_recursive_definition_spells_as_written_941`
/// - witness: `tests::goldens::a_recursive_parameter_skips_the_names_its_body_mentions_941`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|names| names.len() == preferred.len()
    && names.iter().all(|name| !taken.contains(&Name::from(name.as_str())))
    && names.iter().enumerate().all(|(at, name)| names.get(.. at).is_some_and(|before| !before.contains(name)))))]
pub fn parameters<S>(
    source: &S,
    roots: &[(S::Node, Admits)],
    taken: &[Name<'_>],
    preferred: &[Option<Name<'_>>],
) -> Option<Vec<String>>
where
    S: Source + ?Sized,
{
    let mut names = BTreeSet::new();
    for &(root, admits) in roots {
        match mentioned(source, root, admits, Bodies::Spelled) {
            Maybe::Present(found) => names.extend(found),
            Maybe::Absent(scan::Absent::OverBudget) => return None,
        }
    }
    names.extend(taken.iter().copied());
    let free = |name: &str, chosen: &[String]| {
        !names.contains(&Name::from(name)) && !chosen.iter().any(|held| held == name)
    };
    let mut chosen: Vec<String> = Vec::with_capacity(preferred.len());
    let mut next = Ordinal(0_u32);
    for &wanted in preferred {
        if let Some(name) = wanted
            && free(name.as_ref(), &chosen)
        {
            chosen.push(String::from(name.as_ref()));
            continue;
        }
        loop {
            let Maybe::Present(name) = candidate(next)
            else {
                return None;
            };
            next = Ordinal(next.0.checked_add(1_u32)?);
            if free(name.0.as_str(), &chosen) {
                chosen.push(name.0);
                break;
            }
        }
    }
    Some(chosen)
}

/// Whether a data case writes its motive, `case n -> C { … }`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Motive
{
    /// `case n -> C { … }`: nothing else states the case's type.
    Written,
    /// `case n { … }`: its position states the type, or the motive names
    /// the scrutinee its binder stands for, which no written motive can.
    Left,
}

/// Whether a data case at a position admitting `admits` writes its motive
/// `motive`.
///
/// # Specification
/// - requires: `motive` is a data case's motive in `source`.
/// - ensures: [`Motive::Written`] where nothing states the case's type — the
///   computation a bind runs or a call applies, a body whose type nothing
///   states — and no variable in the motive names its own binder;
///   [`Motive::Left`] otherwise, and where the scan takes more than the visit
///   budget.
/// - provides: the one decision a case's slots and its spelling share.
/// - fails: never.
/// - panics: none.
/// - intension: the scan [`mentioned`] makes, counting the intuitionistic
///   binders each slot opens.
///
/// # Adequacy
/// - hypothesis: L3 — a case a bind runs, one in a constructor's thunk and one
///   ending a definition's body observe the motive written, written and left.
/// - witness: `tests::goldens::a_case_nothing_types_writes_its_motive_815`
#[spec(ensures: |ret| ret == Motive::Left || matches!(admits, Admits::Computation(Tail::Continues | Tail::Unstated)))]
fn case_motive<S>(
    source: &S,
    motive: S::Node,
    admits: Admits,
) -> Motive
where
    S: Source + ?Sized,
{
    if !matches!(
        admits,
        Admits::Computation(Tail::Continues | Tail::Unstated)
    ) {
        return Motive::Left;
    }
    let mut pending = Vec::from([(motive, Admits::CompType, ValueDepth::ROOT, 0_usize)]);
    let mut visits = 0_u32;
    while let Some((node, admits, depth, opened)) = pending.pop() {
        visits = visits.saturating_add(1_u32);
        if visits > VISIT_BUDGET {
            return Motive::Left;
        }
        let former = source.read(node);
        let kind = kind(&former);
        if reach(admits, depth, kind) != Reach::Spell {
            continue;
        }
        if let Former::Variable {
            zone: Zone::Intuitionistic,
            index,
        } = former
            && usize::try_from(u32::from(index)).ok() == Some(opened)
        {
            return Motive::Left;
        }
        let below = below(depth, kind);
        // A case inside the motive is scanned with its own motive, so a
        // mention there counts whether or not that motive is written.
        let read = slots(
            source,
            node,
            &former,
            (admits, Bodies::Spelled),
            Motive::Written,
        );
        for slot in read {
            if let Some(child) = slot.node {
                let opened = if slot.binds.zone == Zone::Intuitionistic {
                    opened.saturating_add(slot.binds.count)
                }
                else {
                    opened
                };
                pending.push((child, slot.admits, below, opened));
            }
        }
    }
    Motive::Written
}

/// The surface spelling of the universe of `sort` at `level`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Type` for the value universe at level zero, `Type[-]` for the
///   computation universe there, `Type[+, l]` and `Type[-, l]` at a constant
///   level `l` above zero; absent for a parameter sort or a level that mentions
///   a variable.
/// - provides: the universe spellings the grammar writes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — both ground sorts at zero and positive levels, a
///   parameter sort and a variable level distinguish polarity, lost levels and
///   unsupported forms. The fixtures do not enumerate large constants.
/// - witness: `tests::goldens::universes_spell_their_sort_and_level`
#[spec(ensures: |ref ret| match (sort, ret) {
    | (Sort::Parameter(_), &Maybe::Absent(universe::Absent::ParameterSort)) => true,
    | (Sort::Ground(_), &Maybe::Absent(universe::Absent::LevelVariable)) => level.atoms().next().is_some(),
    | (Sort::Ground(ground), &Maybe::Present(ref text)) => {
        let constant = u64::from(level.constant_part());
        level.atoms().next().is_none() && if constant == 0_u64 {
            text.0 == match ground { GroundSort::Value => "Type", GroundSort::Computation => "Type[-]" }
        } else {
            text.0.strip_prefix(match ground { GroundSort::Value => "Type[+, ", GroundSort::Computation => "Type[-, " })
                .and_then(|tail| tail.strip_suffix(']')).and_then(|digits| digits.parse::<u64>().ok()) == Some(constant)
        }
    },
    | _ => false,
})]
fn universe(
    sort: Sort,
    level: &Level,
) -> Maybe<Spelled, universe::Absent>
{
    let Sort::Ground(ground) = sort
    else {
        return Maybe::Absent(universe::Absent::ParameterSort);
    };
    if level.atoms().next().is_some() {
        return Maybe::Absent(universe::Absent::LevelVariable);
    }
    let constant = u64::from(level.constant_part());
    Maybe::Present(Spelled(match (ground, constant) {
        (GroundSort::Value, 0_u64) => String::from("Type"),
        (GroundSort::Computation, 0_u64) => String::from("Type[-]"),
        (GroundSort::Value, _) => format!("Type[+, {constant}]"),
        (GroundSort::Computation, _) => format!("Type[-, {constant}]"),
    }))
}

/// The surface spelling of a literal.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an integer as its sign and digits; a string between double quotes
///   with a backslash, a double quote, a line feed, a tab, a carriage return
///   and a nul written as the escapes the lowering decodes, every other
///   character as itself; a numeric literal as its sign, its digits, and its
///   fraction after a point when it has one.
/// - provides: the one spelling of every literal, which holds no line break, so
///   a literal never splits across lines.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the finite escaped-control string, signed integer and
///   numeric fixtures observe delimiters, sign, digits and fractional parts.
///   Arbitrary Unicode strings and all magnitudes are not enumerated.
/// - witness: `tests::goldens::string_controls_stay_in_one_escaped_literal`
/// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
#[spec(ensures: |ref ret| !ret.0.contains(['\r', '\n', '\t', '\0']) && match *literal {
    | Literal::Integer(ref integer) => {
        let digits = match integer.sign() {
            Sign::Negative => ret.0.strip_prefix('-'),
            Sign::NonNegative => Some(ret.0.as_str()),
        };
        digits == Some(integer.magnitude().as_ref())
    },
    | Literal::Numeric(ref numeric) => {
        let digits = match numeric.sign() {
            Sign::Negative => ret.0.strip_prefix('-'),
            Sign::NonNegative => Some(ret.0.as_str()),
        };
        let fraction: &str = numeric.fraction().as_ref();
        if fraction.is_empty() { digits == Some(numeric.integer_part().as_ref()) }
        else { digits.and_then(|text| text.split_once('.')) == Some((numeric.integer_part().as_ref(), fraction)) }
    },
    | Literal::Text(_) => ret.0.len() >= 2_usize && ret.0.starts_with('"') && ret.0.ends_with('"'),
})]
fn literal(literal: &Literal) -> Spelled
{
    let sign = |sign: Sign| match sign {
        Sign::Negative => "-",
        Sign::NonNegative => "",
    };
    Spelled(match *literal {
        Literal::Integer(ref integer) => {
            format!("{}{}", sign(integer.sign()), integer.magnitude().as_ref())
        },
        Literal::Text(ref text) => {
            let content: &str = text.as_ref();
            let mut spelled = String::with_capacity(content.len().saturating_add(2_usize));
            spelled.push('"');
            for character in content.chars() {
                match character {
                    '\\' => spelled.push_str("\\\\"),
                    '"' => spelled.push_str("\\\""),
                    '\n' => spelled.push_str("\\n"),
                    '\t' => spelled.push_str("\\t"),
                    '\r' => spelled.push_str("\\r"),
                    '\0' => spelled.push_str("\\0"),
                    other => spelled.push(other),
                }
            }
            spelled.push('"');
            spelled
        },
        Literal::Numeric(ref numeric) => {
            let fraction: &str = numeric.fraction().as_ref();
            let whole = format!(
                "{}{}",
                sign(numeric.sign()),
                numeric.integer_part().as_ref()
            );
            if fraction.is_empty() {
                whole
            }
            else {
                format!("{whole}.{fraction}")
            }
        },
    })
}

/// The walk's state: the builder it writes into, the finished pieces, the
/// open binders and what it has had to approximate.
struct Walk<'walk, 'names>
{
    /// The composer every leaf and join is written into.
    builder: &'walk mut dyn Compose,
    /// Finished pieces, innermost last.
    pieces: Vec<Piece>,
    /// The binder names by position.
    binders: Binders<'names>,
    /// The name each binder position took when a binder last opened there:
    /// the one the source writes, when it captures no other, else the first
    /// generated name no binder around it holds; none for a redex's binder,
    /// which spells as its argument, and once the names ran out.
    names: Vec<Option<BinderName>>,
    /// The zone of each open binder, outermost first; a binder's position
    /// among them names it.
    opened: Vec<Zone>,
    /// The positions of the open binders that name a region, a capability
    /// scope's or a hold's, outermost first: the regions the walk is inside,
    /// after the ones the source's roots stand in.
    scopes: Vec<usize>,
    /// The positions whose binder an occurrence named since it last opened:
    /// a dependent arrow whose binder no occurrence names is spelled as the
    /// plain arrow.
    occurring: BTreeSet<OpenBinders>,
    /// The occurrences set aside by each [`Task::Hold`] whose argument has not
    /// yet been bound, the outermost first.
    held: Vec<BTreeSet<OpenBinders>>,
    /// The arguments the binders of a static redex stand for, by the binder's
    /// position among the open ones: a redex is written as its reduct, each
    /// occurrence of such a binder as the argument's piece.
    substituted: BTreeMap<OpenBinders, Substituted>,
    /// The names of the intuitionistic binders the root stands under,
    /// outermost first.
    context: &'names [Option<Name<'names>>],
    /// The claim the calls of the outermost binder in `context` write, where
    /// it is a recursive definition's own.
    recursive: Option<Recursion>,
    /// Whether every node so far was spelled in full.
    fidelity: Fidelity,
    /// Why each `?` written so far was written.
    unspelled: BTreeSet<Unspelled>,
    /// How the presentation writes its thunks.
    bodies: Bodies,
    /// The spellings of the session types whose payloads are being walked,
    /// innermost last; each join takes its own.
    protocols: Vec<Vec<Segment>>,
    /// The parts of the formers spelled by parts whose children are being
    /// walked, innermost last; each join takes its own.
    forms: Vec<Vec<Part>>,
    /// Whether the sugar the grammar parses is written where it fits.
    form: Form,
    /// Which glyphs the walk writes where a construct has two spellings.
    spelling: grammar::Spelling,
    /// The node reads the walk may still make: one per visit, and one per
    /// link the alias's look-ahead reads.
    remaining: u32,
    /// The grammar sort the node visited now is read in.
    surface: Surface,
}

impl Walk<'_, '_>
{
    /// Pushes `?` for a node the walk cannot spell, and records why.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::approximate`] over `?`; `reason` is among the
    ///   reasons recorded.
    /// - provides: every `?` the walk writes.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — misplaced, unreadable and unbound nodes each spell
    ///   `?` under their own reason.
    /// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
    #[spec(ensures: |ref ret| self.unspelled.contains(&reason) && self.fidelity == Fidelity::Approximate
        && matches!(*ret, Ok(()) | Err(PresentationError::Build(_))))]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            answer_totality,
            reason = "the one writer of the printer's `?`: each caller states the reason it \
                      records under its own expectation"
        )
    )]
    fn unspell(
        &mut self,
        reason: Unspelled,
    ) -> Result<(), PresentationError>
    {
        self.approximate(Glyphs("?"), reason)
    }

    /// A text leaf.
    ///
    /// # Specification
    /// - requires: `glyphs` holds no line feed, carriage return or tab.
    /// - ensures: one text node holding exactly `glyphs`.
    /// - provides: every leaf of the document.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Build`] when the builder refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact literal spellings expose corrupted leaf text; a
    ///   zero text-byte budget exposes swallowed build refusals. Other meters
    ///   and allocation failures are outside these fixtures.
    /// - witness: `tests::goldens::string_controls_stay_in_one_escaped_literal`
    /// - witness: `walk::tests::failed_atoms_do_not_push_pieces_or_restore_fidelity`
    #[spec(
        requires: !glyphs.0.contains(['\r', '\n', '\t']),
        ensures: |ref ret| match *ret {
            | Ok(doc) => glyphs.0.is_empty() || doc != Doc::EMPTY,
            | Err(PresentationError::Build(_)) => true,
            | Err(_) => false,
        },
    )]
    fn leaf(
        &mut self,
        glyphs: Glyphs<'_>,
    ) -> Result<Doc, PresentationError>
    {
        self.builder.text(glyphs)
    }

    /// Pushes a finished atom holding `glyphs`.
    ///
    /// # Specification
    /// - requires: as [`Self::leaf`].
    /// - ensures: one atom piece on the finished stack.
    /// - provides: every leaf former's piece.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — leaf spellings and a zero text-byte budget
    ///   distinguish a missing atom, phantom pieces on failure and a wrong
    ///   failure phase.
    /// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `walk::tests::failed_atoms_do_not_push_pieces_or_restore_fidelity`
    #[spec(
        requires: !glyphs.0.contains(['\r', '\n', '\t']),
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| match *ret {
            | Ok(()) => entry.checked_add(1_usize) == Some(self.pieces.len())
                    && self.pieces.last().is_some_and(|piece| piece.binding == Binding::Atom),
            | Err(PresentationError::Build(_)) => self.pieces.len() == entry,
            | Err(_) => false,
        },
    )]
    fn atom(
        &mut self,
        glyphs: Glyphs<'_>,
    ) -> Result<(), PresentationError>
    {
        let doc = self.leaf(glyphs)?;
        self.pieces.push(Piece {
            doc,
            binding: Binding::Atom,
        });
        Ok(())
    }

    /// Pushes an atom that stands for more than it says, marks the
    /// presentation approximate and records why.
    ///
    /// # Specification
    /// - requires: as [`Self::leaf`].
    /// - ensures: one atom piece holding `glyphs`; the fidelity is approximate
    ///   from here on and `reason` is among the reasons recorded.
    /// - provides: `?`, `<thunk>`, `<stack>` and `<deep>`.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — deep, opaque and unreadable nodes expose omitted
    ///   approximation under their reason; a refused atom exposes a fidelity
    ///   reset on failure. Unrepresented allocator failures are outside this
    ///   evidence.
    /// - witness: `tests::goldens::beyond_the_depth_limit_renders_deep`
    /// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `walk::tests::failed_atoms_do_not_push_pieces_or_restore_fidelity`
    #[spec(
        requires: !glyphs.0.contains(['\r', '\n', '\t']),
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| self.fidelity == Fidelity::Approximate && self.unspelled.contains(&reason)
            && match *ret {
            | Ok(()) => entry.checked_add(1_usize) == Some(self.pieces.len())
                    && self.pieces.last().is_some_and(|piece| piece.binding == Binding::Atom),
            | Err(PresentationError::Build(_)) => self.pieces.len() == entry,
            | Err(_) => false,
        },
    )]
    fn approximate(
        &mut self,
        glyphs: Glyphs<'_>,
        reason: Unspelled,
    ) -> Result<(), PresentationError>
    {
        self.note(reason);
        self.atom(glyphs)
    }

    /// Marks the presentation approximate and records why: the walk writes a
    /// former in its own notation, or leaves part of a node out.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the fidelity is approximate from here on and `reason` is
    ///   among the reasons recorded.
    /// - provides: every approximation the walk makes, so none goes unnamed.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each former the walk writes in its own notation
    ///   records the notation it wrote.
    /// - witness: `tests::goldens::an_approximate_printing_names_its_reason_820`
    #[spec(ensures: self.fidelity == Fidelity::Approximate && self.unspelled.contains(&reason))]
    fn note(
        &mut self,
        reason: Unspelled,
    )
    {
        self.fidelity = Fidelity::Approximate;
        let _fresh = self.unspelled.insert(reason);
    }

    /// Pushes a name, or `?` for a name the walk's spelling cannot write.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an atom holding the name; `?`, approximate, for an empty
    ///   name, one holding a line feed, a carriage return or a tab, and in
    ///   ASCII one holding the prime.
    /// - provides: the spelling of constants and abstract types.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary names, a literal question mark, empty names
    ///   and each forbidden control distinguish content from approximation; a
    ///   primed name in each spelling distinguishes the ASCII refusal. Other
    ///   Unicode names are outside these finite fixtures.
    /// - witness: `tests::goldens::fidelity_follows_nodes_not_the_characters_of_a_name`
    /// - witness: `tests::goldens::a_primed_name_has_no_ascii_spelling_782`
    /// - witness: `walk::tests::unprintable_names_are_approximate_atoms`
    #[spec(
        captures: [entry = self.pieces.len(), fidelity = self.fidelity],
        ensures: |ref ret| {
            let text: &str = name.as_ref();
            self.fidelity == if unwritable(name, self.spelling).is_some() { Fidelity::Approximate } else { fidelity }
                && match *ret {
                    | Ok(()) => entry.checked_add(1_usize) == Some(self.pieces.len())
                    && self.pieces.last().is_some_and(|piece| piece.binding == if text.contains('.') { Binding::Qualified } else { Binding::Atom }),
                    | Err(PresentationError::Build(_)) => self.pieces.len() == entry,
                    | Err(_) => false,
                }
        },
    )]
    fn name(
        &mut self,
        name: Name<'_>,
    ) -> Result<(), PresentationError>
    {
        let text: &str = name.as_ref();
        if let Some(reason) = unwritable(name, self.spelling) {
            return self.unspell(reason);
        }
        if text.contains('.') {
            let doc = self.leaf(Glyphs(text))?;
            self.pieces.push(Piece {
                doc,
                binding: Binding::Qualified,
            });
            return Ok(());
        }
        self.atom(Glyphs(text))
    }

    /// Pushes the label an entry of a braced former is written after: `l : `
    /// before a record type's field, `.l = ` before a record's, `.i = ` before
    /// an injection's body.
    ///
    /// # Specification
    /// - requires: nothing; a source may answer no label.
    /// - ensures: one atom piece: the field label the source answers for `of`
    ///   at `index`, or the summand `index` in decimal, then its separator; `?`
    ///   in place of a label the source does not answer, a line cannot hold or,
    ///   primed, ASCII cannot write, which makes the presentation approximate.
    /// - provides: the labelled entries of records and injections.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — record types and records of two fields, injections
    ///   into the first and the third summand, and a table record that answers
    ///   no label distinguish a swapped label, a wrong separator and a missing
    ///   label claimed faithful.
    /// - witness: `tests::goldens::records_spell_their_fields_in_label_order`
    /// - witness: `tests::goldens::n_ary_tuples_and_injections_spell_between_their_braces`
    /// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
    #[spec(
        captures: [entry = self.pieces.len(), fidelity = self.fidelity],
        ensures: |ref ret| (fidelity != Fidelity::Approximate || self.fidelity == Fidelity::Approximate)
            && match *ret {
                | Ok(()) => entry.checked_add(1_usize) == Some(self.pieces.len())
                    && self.pieces.last().is_some_and(|piece| piece.binding == Binding::Atom),
                | Err(PresentationError::Build(_)) => self.pieces.len() == entry,
                | Err(_) => false,
            },
    )]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            answer_totality,
            reason = "a label the source does not answer, a malformed source, or a line or the \
                      spelling cannot hold has no spelling"
        )
    )]
    fn label<S>(
        &mut self,
        source: &S,
        of: S::Node,
        index: Component,
        label: Label,
    ) -> Result<(), PresentationError>
    where
        S: Source + ?Sized,
    {
        let spelled = match label {
            Label::Summand => format!(".{} = ", usize::from(index)),
            Label::Field | Label::Assignment => {
                let held = source.label(of, index);
                let mut text: &str = held.as_ref().map_or("", AsRef::as_ref);
                if let Some(reason) = unwritable(Name::from(text), self.spelling) {
                    self.fidelity = Fidelity::Approximate;
                    let _fresh = self.unspelled.insert(if text.is_empty() {
                        Unspelled::Missing
                    }
                    else {
                        reason
                    });
                    text = "?";
                }
                match label {
                    Label::Field => format!("{text} : "),
                    Label::Assignment | Label::Summand => format!(".{text} = "),
                }
            },
        };
        self.atom(Glyphs(spelled.as_str()))
    }

    /// A leaf naming the variable `index` binders out in `zone`: the open
    /// binder it counts to, else the context binder past them, else `?`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the name of the open binder of `zone` that `index` counts out
    ///   to from the occurrence; past every open binder of the zone, an
    ///   intuitionistic variable reads as the context binder it counts out to,
    ///   innermost last, a recursive definition's own written with its claim,
    ///   `name[<]` or `name[>]`; `?`, approximate and recorded unbound, for a
    ///   linear variable past every open binder, one past the context, and a
    ///   context binder the source cannot name, recorded primed for a context
    ///   binder whose prime ASCII cannot write, and recorded exhausted when the
    ///   generated names ran out.
    /// - provides: the spelling of a bound variable and of an endpoint.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Build`] when the builder refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested binders distinguish reversed de Bruijn order
    ///   and capture; a free variable reads its context binder's name and one
    ///   past the context exposes a fabricated name. The fixtures do not open
    ///   enough binders to exhaust the candidate counter.
    /// - witness: `tests::goldens::long_dependent_function_type_breaks_at_the_narrow_page`
    /// - witness: `tests::goldens::a_binder_skips_the_names_the_type_mentions`
    /// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
    #[spec(
        captures: [entry = self.pieces.len(), fidelity = self.fidelity],
        ensures: |ref ret| self.pieces.len() == entry
            && (fidelity != Fidelity::Approximate || self.fidelity == Fidelity::Approximate)
            && matches!(*ret, Ok(_) | Err(PresentationError::Build(_))),
    )]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            answer_totality,
            reason = "a variable past every open binder and the context, or a binder the \
                      generated names ran out for, names no binder to spell"
        )
    )]
    fn variable_leaf(
        &mut self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Result<Doc, PresentationError>
    {
        let found = self.opened_at(zone, index);
        let open = self.opened.iter().filter(|&&open| open == zone).count();
        let remaining = usize::try_from(u32::from(index))
            .unwrap_or(usize::MAX)
            .saturating_sub(open);
        let spelled = match found {
            Some(position) => {
                let _fresh = self.occurring.insert(position);
                match self.names.get(position.0) {
                    Some(&Some(ref name)) => Ok(name.0.clone()),
                    Some(&None) | None => Err(Unspelled::Exhausted),
                }
            },
            None => match zone {
                Zone::Intuitionistic => {
                    let position = self
                        .context
                        .len()
                        .checked_sub(remaining)
                        .and_then(|outer| outer.checked_sub(1_usize));
                    match position.and_then(|at| self.context.get(at).copied().flatten()) {
                        Some(name) => match (unwritable(name, self.spelling), self.recursive) {
                            // A recursive definition's call of itself writes
                            // its claim.
                            (None, Some(recursion)) if position == Some(0_usize) => {
                                Ok(format!("{}{}", name.as_ref(), match recursion {
                                    Recursion::Descends => "[<]",
                                    Recursion::Productive => "[>]",
                                }))
                            },
                            (None, _) => Ok(String::from(name.as_ref())),
                            (Some(Unspelled::Primed), _) => Err(Unspelled::Primed),
                            (Some(_), _) => Err(Unspelled::Unbound),
                        },
                        None => Err(Unspelled::Unbound),
                    }
                },
                Zone::Linear => Err(Unspelled::Unbound),
            },
        };
        match spelled {
            Ok(name) => self.leaf(Glyphs(name.as_str())),
            Err(reason) => {
                self.fidelity = Fidelity::Approximate;
                let _fresh = self.unspelled.insert(reason);
                self.leaf(Glyphs("?"))
            },
        }
    }

    /// Pushes the name the variable `index` binders out in `zone` reads as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one atom piece holding [`Self::variable_leaf`]'s leaf.
    /// - provides: the spelling of a bound variable.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::variable_leaf`].
    /// - witness: `tests::goldens::long_dependent_function_type_breaks_at_the_narrow_page`
    /// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
    #[spec(
        captures: [entry = self.pieces.len(), fidelity = self.fidelity],
        ensures: |ref ret| (fidelity != Fidelity::Approximate || self.fidelity == Fidelity::Approximate)
            && match *ret {
                | Ok(()) => entry.checked_add(1_usize) == Some(self.pieces.len())
                    && self.pieces.last().is_some_and(|piece| piece.binding == Binding::Atom),
                | Err(PresentationError::Build(_)) => self.pieces.len() == entry,
                | Err(_) => false,
            },
    )]
    fn variable(
        &mut self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Result<(), PresentationError>
    {
        if let Some(position) = self.opened_at(zone, index)
            && let Some(argument) = self.substituted.get(&position)
        {
            self.pieces.push(argument.piece);
            self.occurring.extend(argument.occurring.iter().copied());
            return Ok(());
        }
        let doc = self.variable_leaf(zone, index)?;
        self.pieces.push(Piece {
            doc,
            binding: Binding::Atom,
        });
        Ok(())
    }

    /// The position among the open binders of the one of `zone` that `index`
    /// counts out to, if one is open.
    ///
    /// # Specification
    /// trivial.
    fn opened_at(
        &self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> Option<OpenBinders>
    {
        let mut remaining = usize::try_from(u32::from(index)).unwrap_or(usize::MAX);
        for (position, &open) in self.opened.iter().enumerate().rev() {
            if open != zone {
                continue;
            }
            if remaining == 0_usize {
                return Some(OpenBinders(position));
            }
            remaining = remaining.saturating_sub(1_usize);
        }
        None
    }

    /// Opens one binder for each of the top `arity` pieces, the deepest
    /// outermost, each standing for its piece and carrying the occurrences its
    /// spelling named, which the [`Task::Hold`] before each argument set apart.
    ///
    /// # Specification
    /// - requires: nothing; a stack holding fewer pieces, or fewer held sets
    ///   than the arguments and the occurrences around them, is reported as
    ///   unbalanced.
    /// - ensures: the pieces removed, `arity` intuitionistic binders opened,
    ///   and each opened binder's position mapped to its piece and to the
    ///   occurrences its argument named; the occurrences around the arguments
    ///   restored, so an argument's occurrences count only where the reduct
    ///   reads its binder (#736).
    /// - provides: the binders a redex's reduct is walked under.
    /// - fails: as [`Self::take`], and [`PresentationError::Unbalanced`] for a
    ///   missing held set.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a redex of one and of two arguments, each argument
    ///   occurring in the reduct, observe the order the binders open in; a
    ///   called literal that drops its argument and one that returns it
    ///   separate a binder named by the dropped argument from one the reduct
    ///   names.
    /// - witness: `tests::goldens::a_static_redex_prints_as_its_reduct_401`
    /// - witness: `tests::goldens::a_binder_only_a_dropped_argument_names_is_unnamed_736`
    #[spec(
        captures: [opened = self.opened.len()],
        ensures: |ref ret| ret.is_err() || self.opened.len() == opened.saturating_add(arity.0),
    )]
    fn substitute(
        &mut self,
        arity: Arity,
    ) -> Result<(), PresentationError>
    {
        let arguments = self.take(arity)?;
        // The last argument's occurrences are the current set; each earlier
        // one's was set aside by the hold before the argument after it, and
        // the occurrences around them all by the first hold.
        let mut named = Vec::with_capacity(arguments.len());
        named.push(core::mem::take(&mut self.occurring));
        for _ in 1_usize .. arguments.len() {
            named.push(self.held.pop().ok_or(PresentationError::Unbalanced)?);
        }
        self.occurring = self.held.pop().ok_or(PresentationError::Unbalanced)?;
        for (piece, occurring) in arguments.into_iter().zip(named.into_iter().rev()) {
            let position = self.opened.len();
            let _fresh = self
                .substituted
                .insert(OpenBinders(position), Substituted { piece, occurring });
            let _named = self.occurring.remove(&OpenBinders(position));
            if self.names.len() <= position {
                self.names.resize(position.saturating_add(1_usize), None);
            }
            if let Some(slot) = self.names.get_mut(position) {
                *slot = None;
            }
            self.opened.push(Zone::Intuitionistic);
        }
        Ok(())
    }

    /// The finished piece on top of the stack.
    ///
    /// # Specification
    /// - requires: nothing; an empty stack is reported as unbalanced.
    /// - ensures: the top piece, removed.
    /// - provides: every join's operands.
    /// - fails: an empty stack, which the walk's own scheduling excludes.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Unbalanced`] on an empty stack.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite composite spellings expose reordered operands;
    ///   an incomplete join and an empty stack expose a swallowed underflow.
    /// - witness: `tests::goldens::pair_of_injections_pins_sum_notation`
    /// - witness: `walk::tests::missing_operands_are_unbalanced_not_layout_failures`
    #[spec(
        captures: [entry = self.pieces.len(), top = self.pieces.last().copied()],
        ensures: |ref ret| match *ret {
            | Ok(piece) => top.is_some_and(|held| held.doc == piece.doc && held.binding == piece.binding)
                && self.pieces.len().checked_add(1_usize) == Some(entry),
            | Err(PresentationError::Unbalanced) => entry == 0_usize && self.pieces.is_empty(),
            | Err(_) => false,
        },
    )]
    fn pop(&mut self) -> Result<Piece, PresentationError>
    {
        self.pieces.pop().ok_or(PresentationError::Unbalanced)
    }

    /// The top `arity` finished pieces, in the order they were finished.
    ///
    /// # Specification
    /// - requires: nothing; a stack holding fewer is reported as unbalanced.
    /// - ensures: the top `arity` pieces, removed, the deepest first.
    /// - provides: the operands of a join over a counted list.
    /// - fails: a stack holding fewer than `arity`, which the walk's own
    ///   scheduling excludes.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Unbalanced`] on a stack holding fewer than
    /// `arity`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the sugared goldens' chains and tuples of two and
    ///   three expose reordered operands.
    /// - witness: `tests::goldens::the_sugared_form_writes_every_sugar_its_shape_admits`
    #[spec(
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| match *ret {
            | Ok(ref taken) => taken.len() == arity.0 && self.pieces.len().checked_add(arity.0) == Some(entry),
            | Err(PresentationError::Unbalanced) => entry < arity.0,
            | Err(_) => false,
        },
    )]
    fn take(
        &mut self,
        arity: Arity,
    ) -> Result<Vec<Piece>, PresentationError>
    {
        let start = self
            .pieces
            .len()
            .checked_sub(arity.0)
            .ok_or(PresentationError::Unbalanced)?;
        Ok(self.pieces.split_off(start))
    }

    /// The arrows and the codomain of the value-function alias the thunk type
    /// over `body` may be: `body` a chain of arrows, none or more, ending in a
    /// pure returner.
    ///
    /// # Specification
    /// - requires: nothing; `source` may be malformed.
    /// - ensures: the arrows from `body` down, outermost first, each with its
    ///   domain and, for a dependent arrow, the arrow itself, marked in the
    ///   dependent set; and the codomain: the value type the returner they end
    ///   in returns, or, when the chain reaches its returner through a static
    ///   redex — an abstraction applied to as many arguments as it binds, which
    ///   prints as its reduct — the redex, whose reduct holds no further arrow.
    ///   A decode and a quote are read through, as they print. Whether a
    ///   dependent arrow's binder occurs is known only once the walk spelled
    ///   the arrows after it, so the join decides between the alias and the
    ///   thunk (#736). None when a link is anything else — an effectful
    ///   returner, an arrow under a redex, a dependent arrow past the
    ///   sixty-fourth link, a missing or misplaced node — or the walk's
    ///   remaining visits run out first. Every link read is one visit spent.
    /// - provides: the shape `+U (A1 -> … -> An -> -F C)` the alias `(A1, …,
    ///   An) => C` stands for, which the lowering reads back to the same type.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Each round reads one link and spends one remaining visit, and the loop
    /// stops when none is left.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the sugared goldens spell the alias at no, one and
    ///   two domains, over a domain and a codomain that are themselves aliases,
    ///   over a codomain a static redex returns, and keep the thunk over a
    ///   dependent arrow whose binder occurs; a dependent arrow whose binder
    ///   only a dropped argument names takes the alias; a source that becomes a
    ///   cycle of thunks over returners after its scan stays within the walk's
    ///   reads.
    /// - witness: `tests::goldens::the_sugared_form_writes_every_sugar_its_shape_admits`
    /// - witness: `tests::goldens::a_static_redex_prints_as_its_reduct_401`
    /// - witness: `tests::goldens::a_binder_only_a_dropped_argument_names_is_unnamed_736`
    /// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
    #[spec(
        captures: [entry = self.remaining],
        ensures: |ret| self.remaining <= entry
            && ret.as_ref().is_none_or(|found| u32::try_from(found.0.len()).is_ok_and(|links| links < entry)),
    )]
    fn alias<S>(
        &mut self,
        source: &S,
        body: S::Node,
    ) -> Option<AliasChain<S::Node>>
    where
        S: Source + ?Sized,
    {
        let mut links = Vec::new();
        let mut dependent = Dependent(0_u64);
        let mut link = body;
        // The first redex the chain entered, whose reduct the codomain is.
        let mut entered = None;
        while let Some(left) = self.remaining.checked_sub(1_u32) {
            self.remaining = left;
            match source.read(link) {
                Former::Arrow { domain, codomain } => {
                    if entered.is_some() {
                        return None;
                    }
                    links.push(Link {
                        domain,
                        opener: None,
                    });
                    link = codomain;
                },
                Former::Pi { domain, codomain } => {
                    if entered.is_some() {
                        return None;
                    }
                    let bit = 1_u64.checked_shl(u32::try_from(links.len()).ok()?)?;
                    dependent = Dependent(dependent.0 | bit);
                    links.push(Link {
                        domain,
                        opener: Some(link),
                    });
                    link = codomain;
                },
                Former::Returner(result) => {
                    return Some((
                        links,
                        dependent,
                        entered.map_or(Codomain::Result(result), Codomain::Reduct),
                    ));
                },
                // A decode and a quote print as the node they hold, so the
                // chain reads on through them as the spelling does.
                Former::ComputationElement(child) | Former::QuoteComputation(child) => {
                    link = child;
                },
                // A redex prints as its reduct: the abstraction's body once
                // every binder it opens takes an argument.
                Former::StaticApplication(mut operator, _) => {
                    let mut arguments = 1_usize;
                    while let Former::StaticApplication(inner, _) = source.read(operator) {
                        self.remaining = self.remaining.checked_sub(1_u32)?;
                        arguments = arguments.saturating_add(1_usize);
                        operator = inner;
                    }
                    for _ in 0_usize .. arguments {
                        self.remaining = self.remaining.checked_sub(1_u32)?;
                        let Former::StaticLambda(reduct) = source.read(operator)
                        else {
                            return None;
                        };
                        operator = reduct;
                    }
                    entered = entered.or(Some(link));
                    link = operator;
                },
                Former::Reify
                | Former::Stack(..)
                | Former::With(..)
                | Former::ListNil
                | Former::ListCons(..)
                | Former::PathUniverse(..)
                | Former::PathRefl(_)
                | Former::PathEquiv(..)
                | Former::PathProduct(..)
                | Former::BaseType(_)
                | Former::Product(_)
                | Former::Sum(_)
                | Former::RecordType(_)
                | Former::ThunkType(_)
                | Former::Universe { .. }
                | Former::Element(_)
                | Former::Abstract(_)
                | Former::StaticPi { .. }
                | Former::Sigma { .. }
                | Former::Capability { .. }
                | Former::Session { .. }
                | Former::EffectfulReturner { .. }
                | Former::List(_)
                | Former::Variable { .. }
                | Former::Constant(_)
                | Former::Unit
                | Former::Literal(_)
                | Former::Tuple(_)
                | Former::Record(_)
                | Former::Injection(..)
                | Former::Thunk(_)
                | Former::Quote(_)
                | Former::StaticLambda(_)
                | Former::Here(_)
                | Former::Funext(..)
                | Former::Equiv(..)
                | Former::Univalence(_)
                | Former::SessionRelated(..)
                | Former::Stay(_)
                | Former::Then(..)
                | Former::Back(_)
                | Former::Cong(..)
                | Former::FlowProduct(..)
                | Former::Forward(_)
                | Former::FunctionFlow(..)
                | Former::RunType(_)
                | Former::Return(_)
                | Former::Bind(..)
                | Former::Force(_)
                | Former::Application(..)
                | Former::Lambda(_)
                | Former::Nested(_)
                | Former::Run(_)
                | Former::Ua { .. }
                | Former::Path { .. }
                | Former::Data { .. }
                | Former::Codata { .. }
                | Former::Constructor { .. }
                | Former::Flow { .. }
                | Former::Relation { .. }
                | Former::Recorded { .. }
                | Former::Returned(_)
                | Former::Primitive { .. }
                | Former::Transport(..)
                | Former::PathTransport { .. }
                | Former::TelescopeTransport { .. }
                | Former::Ride { .. }
                | Former::Fixpoint(_)
                | Former::Case { .. }
                | Former::Split { .. }
                | Former::DataCase { .. }
                | Former::RecordProjection(..)
                | Former::TupleProjection(..)
                | Former::ListFold { .. }
                | Former::ListCase { .. }
                | Former::Perform { .. }
                | Former::Handle { .. }
                | Former::Exercise { .. }
                | Former::Scope { .. }
                | Former::Resume(..)
                | Former::Reset(_)
                | Former::Shift(_)
                | Former::Lazy(..)
                | Former::Ascription { .. }
                | Former::Project(..)
                | Former::Send { .. }
                | Former::Receive { .. }
                | Former::Select { .. }
                | Former::Offer { .. }
                | Former::Close(_)
                | Former::Fork { .. }
                | Former::Hold { .. }
                | Former::Access { .. }
                | Former::ResumeView { .. }
                | Former::AbortView(_)
                | Former::Located { .. }
                | Former::Kept { .. }
                | Former::WorldHold(_)
                | Former::Leta { .. }
                | Former::Migrate { .. }
                | Former::Unreadable(_) => return None,
            }
        }
        None
    }

    /// The dependent value-function alias, `(a : A, B) => C`, over its spelled
    /// domains and codomain: the spelling of an alias chain where an
    /// occurrence named a dependent arrow's binder, the grammar's sugar for
    /// `+U ((a : A) -> B -> -F C)`.
    ///
    /// # Specification
    /// - requires: `domains` are the chain's arrows' domains, outermost first,
    ///   `dependent` marks the dependent ones, and their binders, closed, sat
    ///   from the open count up, one per dependent arrow in order.
    /// - ensures: the domains between parentheses, separated by commas, each
    ///   written as the walk writes its arrow alone: a dependent domain as `a :
    ///   A`, named by its binder, where an occurrence named it or the walk
    ///   approximated, and bare otherwise; then `=>` and the codomain.
    /// - provides: the alias join's dependent spelling, which decides only once
    ///   every occurrence was met.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the sugared golden writes the alias over a dependent
    ///   arrow its codomain names, a chain mixing a named and a bare domain
    ///   reads back to the thunk it stands for, and the #736 golden names a
    ///   binder the reduct reads.
    /// - witness: `tests::goldens::the_sugared_form_writes_every_sugar_its_shape_admits`
    /// - witness: `tests::goldens::a_dependent_alias_names_each_binder_its_codomain_reads_800`
    /// - witness: `tests::goldens::a_binder_only_a_dropped_argument_names_is_unnamed_736`
    #[spec(ensures: |ref ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|&(_, binding)| binding == Binding::Arrow))]
    fn dependent_alias(
        &mut self,
        domains: &[Piece],
        dependent: Dependent,
        codomain: Piece,
    ) -> Result<(Doc, Binding), PresentationError>
    {
        let open = self.opened.len();
        let mut binders = usize::try_from(dependent.0.count_ones())
            .ok()
            .ok_or(PresentationError::Unbalanced)?;
        let mut entries = Vec::with_capacity(domains.len());
        for (at, &domain) in domains.iter().enumerate().rev() {
            let bit = u32::try_from(at)
                .ok()
                .and_then(|at| 1_u64.checked_shl(at))
                .unwrap_or(0_u64);
            let named = if dependent.0 & bit == 0_u64 {
                None
            }
            else {
                binders = binders.saturating_sub(1_usize);
                let position = OpenBinders(open.saturating_add(binders));
                (self.fidelity != Fidelity::Faithful || self.occurring.contains(&position))
                    .then_some(OpenBinders(binders))
            };
            let doc = if let Some(offset) = named {
                let binder = self.binder(offset)?;
                let colon = self.leaf(Glyphs(" : "))?;
                self.builder.concat_all(&[binder, colon, domain.doc])?
            }
            else {
                domain.doc
            };
            entries.push(Piece {
                doc,
                binding: domain.binding,
            });
        }
        entries.reverse();
        let domain = self.listed(&entries)?;
        let arrow = self.leaf(Glyphs(" =>"))?;
        let head = self.builder.concat(domain, arrow)?;
        let head = self.space_or_break(head)?;
        Ok((self.builder.concat(head, codomain.doc)?, Binding::Arrow))
    }

    /// The computation and the value type of the typed bind whose bound
    /// computation is `bound`, when it is one: `bound` the ascription of a
    /// computation to a returner `-F A`.
    ///
    /// # Specification
    /// - requires: nothing; `source` may be malformed.
    /// - ensures: the ascribed computation and `A` when `bound` reads as an
    ///   ascription to a pure returner; none when any link is anything else or
    ///   the walk's remaining visits run out first. Every link read is one
    ///   visit spent, so a recognised bind spends exactly two.
    /// - provides: the shape the lowering gives `run x : A <- c ; rest`, which
    ///   the printer spells back as written.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lowered typed bind spells as its source, and an
    ///   ascription outside that shape stands as its body.
    /// - witness: `tests::goldens::a_typed_bind_spells_as_written`
    #[spec(
        captures: [entry = self.remaining],
        ensures: |ref ret| self.remaining <= entry
            && (ret.is_none() || self.remaining.checked_add(2_u32) == Some(entry)),
    )]
    fn typed_bind<S>(
        &mut self,
        source: &S,
        bound: S::Node,
    ) -> Option<(S::Node, S::Node)>
    where
        S: Source + ?Sized,
    {
        let mut read = |node| {
            self.remaining = self.remaining.checked_sub(1_u32)?;
            Some(source.read(node))
        };
        let Former::Ascription { body, ty } = read(bound)?
        else {
            return None;
        };
        let Former::Returner(result) = read(ty)?
        else {
            return None;
        };
        Some((body, result))
    }

    /// Whether `node` is written with a head no expression reads as the type:
    /// a session type standing at a receive `?A. S`, a selection `+{…}` or an
    /// offer `&{…}`; a sum or a lazy product, written between braces or, in
    /// the sugared form, as a chain an expression reads as arithmetic; or a
    /// product written as such a chain, `A * B`.
    ///
    /// # Specification
    /// - requires: nothing; `source` may be malformed.
    /// - ensures: true exactly when `node` reads as a session type whose
    ///   state's own node is a receive, a selection or an offer; as a sum of
    ///   one or more components that is not `Bool`; as a lazy product of one or
    ///   more components; or, in the sugared form, as a product of two or more
    ///   components.
    /// - provides: the heads [`Self::unread_as_expression`] looks for.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a braced sum, `Bool` and a base type quoted as
    ///   values, in both forms, distinguish the braced spellings from the bare
    ///   ones; a product, a sum and a lazy product chain quoted alone and as an
    ///   argument distinguish the sugared chains from the explicit braces an
    ///   expression reads.
    /// - witness: `tests::goldens::a_type_no_expression_reads_is_quoted_839`
    /// - witness: `tests::goldens::a_quoted_chain_is_quoted_1127`
    #[spec(ensures: |ret| (ret == Bare::Unread) == match source.read(node) {
        | Former::Session { protocol, state, .. } => matches!(
            protocol.node(state),
            Ok(&(ProtocolNode::Receive { .. } | ProtocolNode::Select(_) | ProtocolNode::Offer(_)))
        ),
        | Former::Sum(arity) => usize::from(arity) >= 1_usize && named_sum(source, node).is_none(),
        | Former::With(arity) => usize::from(arity) >= 1_usize,
        | Former::Product(arity) => self.form == Form::Sugared && usize::from(arity) >= 2_usize,
        | _ => false,
    })]
    fn unread_head<S>(
        &self,
        source: &S,
        node: S::Node,
    ) -> Bare
    where
        S: Source + ?Sized,
    {
        let former = source.read(node);
        let unread = if let Former::Session {
            protocol, state, ..
        } = former
        {
            matches!(
                protocol.node(state),
                Ok(&(ProtocolNode::Receive { .. }
                    | ProtocolNode::Select(_)
                    | ProtocolNode::Offer(_)))
            )
        }
        // Braced, no expression reads the head; chained, an expression reads
        // `+` and `&` as operators over the components.
        else if let Former::Sum(arity) = former {
            usize::from(arity) >= 1_usize && named_sum(source, node).is_none()
        }
        else if let Former::With(arity) = former {
            usize::from(arity) >= 1_usize
        }
        // `#{A, B}` reads as the product's code, `A * B` as the product of two
        // codes.
        else if let Former::Product(arity) = former {
            self.form == Form::Sugared && usize::from(arity) >= 2_usize
        }
        else {
            false
        };
        if unread { Bare::Unread } else { Bare::Reads }
    }

    /// Whether the type `quoted`, written bare where an expression is read,
    /// holds a part no expression reads: its own head or the head of a type
    /// among its parts, which an expression reads as its own parts — `#{Unit,
    /// +{Unit}}` does not read where `#{Unit, Integer}` does.
    ///
    /// # Specification
    /// - requires: nothing; `source` may be malformed.
    /// - ensures: [`Bare::Unread`] when [`Self::unread_head`] says so of
    ///   `quoted` or of a node reached from it through type slots alone,
    ///   visited within the walk's remaining visits; a value slot is not
    ///   entered, since a quote there is written by its own visit. Every node
    ///   read is one visit spent; none left, the scan stops and answers
    ///   [`Bare::Reads`].
    /// - provides: the quotes the walk writes `type(T)`, which the lowering
    ///   reads back to the same code; every other quote stands bare.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Each round reads one node and spends one remaining visit, and the loop
    /// stops when none is left.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a braced sum quoted alone, as an argument and as a
    ///   product's component, against a product of base types and a sum chain,
    ///   distinguish a scan that stops at the head from one that enters the
    ///   parts.
    /// - witness: `tests::goldens::a_type_no_expression_reads_is_quoted_839`
    #[spec(
        captures: [entry = self.remaining, head = self.unread_head(source, quoted)],
        ensures: |ret| self.remaining <= entry && (entry == 0_u32 || head == Bare::Reads || ret == Bare::Unread),
    )]
    fn unread_as_expression<S>(
        &mut self,
        source: &S,
        quoted: S::Node,
    ) -> Bare
    where
        S: Source + ?Sized,
    {
        let mut pending = Vec::from([quoted]);
        while let Some(node) = pending.pop() {
            let Some(left) = self.remaining.checked_sub(1_u32)
            else {
                return Bare::Reads;
            };
            self.remaining = left;
            if self.unread_head(source, node) == Bare::Unread {
                return Bare::Unread;
            }
            let former = source.read(node);
            pending.extend(
                children(source, node, &former, Admits::ValueType, self.bodies)
                    .into_iter()
                    .filter(|slot| {
                        matches!(
                            slot.admits,
                            Admits::Type | Admits::ValueType | Admits::CompType
                        )
                    })
                    .filter_map(|slot| slot.node),
            );
        }
        Bare::Reads
    }

    /// `(a, b, …)`: `items` between parentheses, each bare, a break after
    /// each comma and before the closer.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the opener, the items' documents separated by a comma and a
    ///   space or a break, then nothing or a break, then the closer.
    /// - provides: the tuple and the alias's domain list.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Build`] when the builder refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the sugared goldens' tuples and domain lists at the
    ///   wide and the narrow page expose a lost separator or closer.
    /// - witness: `tests::goldens::the_sugared_form_writes_every_sugar_its_shape_admits`
    #[spec(
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| self.pieces.len() == entry && match *ret {
            | Ok(_) | Err(PresentationError::Build(_)) => true,
            | Err(_) => false,
        },
    )]
    fn listed(
        &mut self,
        items: &[Piece],
    ) -> Result<Doc, PresentationError>
    {
        let opener = self.leaf(Glyphs("("))?;
        let mut docs = Vec::from([opener]);
        for (position, item) in items.iter().enumerate() {
            if position > 0_usize {
                let comma = self.leaf(Glyphs(","))?;
                docs.push(self.space_or_break(comma)?);
            }
            docs.push(item.doc);
        }
        let inner = self.builder.concat_all(&docs)?;
        let inner = self.none_or_break(inner)?;
        let close = self.leaf(Glyphs(")"))?;
        self.builder.concat(inner, close)
    }

    /// `piece`, parenthesized when it binds looser than `loosest`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the piece's document bare when its binding is at most
    ///   `loosest`, else between parentheses.
    /// - provides: the one parenthesization rule of every slot.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bridge and arrow fixtures distinguish wrong
    ///   precedence and missing parentheses. The finite grammar cases do not
    ///   exhaust all possible composite trees.
    /// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `tests::goldens::static_operators_spell_as_the_grammar_writes_them`
    #[spec(
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| self.pieces.len() == entry && match *ret {
            | Ok(doc) => (doc == piece.doc) == (piece.binding <= loosest),
            | Err(PresentationError::Build(_)) => piece.binding > loosest,
            | Err(_) => false,
        },
    )]
    fn bare_up_to(
        &mut self,
        piece: Piece,
        loosest: Binding,
    ) -> Result<Doc, PresentationError>
    {
        if piece.binding <= loosest {
            return Ok(piece.doc);
        }
        self.parenthesized(piece.doc)
    }

    /// `doc` between parentheses.
    ///
    /// # Specification
    /// trivial.
    fn parenthesized(
        &mut self,
        doc: Doc,
    ) -> Result<Doc, PresentationError>
    {
        let open = self.leaf(Glyphs("("))?;
        let close = self.leaf(Glyphs(")"))?;
        self.builder.concat_all(&[open, doc, close])
    }

    /// `head` then a space, or a line break indented two columns.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the inline branch is exactly one space; the broken branch
    ///   starts the continuation two columns in and is the left alternative,
    ///   retained when both alternatives are width-tainted.
    /// - provides: the break after an arrow and a comma.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Build`] when the builder refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — narrow and wide continuations and a zero-column pair
    ///   distinguish missing spaces, wrong indentation and reversed
    ///   width-tainted alternatives. Other widths are not enumerated.
    /// - witness: `tests::goldens::arrow_chain_breaks_before_each_continuation`
    /// - witness: `tests::goldens::doubly_tainted_pair_keeps_the_broken_separator`
    #[spec(
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| self.pieces.len() == entry && match *ret {
            | Ok(doc) => doc != head,
            | Err(PresentationError::Build(_)) => true,
            | Err(_) => false,
        },
    )]
    fn space_or_break(
        &mut self,
        head: Doc,
    ) -> Result<Doc, PresentationError>
    {
        let space = self.leaf(Glyphs(" "))?;
        let line = Doc::HARD_LINE;
        let indented = self.builder.nest(NestAmount::from(CONTINUATION), line)?;
        let choice = self.builder.choice(indented, space)?;
        self.builder.concat(head, choice)
    }

    /// `head` then nothing, or a line break.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the inline branch is empty; the broken branch puts the closer
    ///   on its own line and is the left alternative, retained when both
    ///   alternatives are width-tainted. A composer that settles the choice as
    ///   it composes answers `head` itself for the inline branch.
    /// - provides: the break before a bracket's closer.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Build`] when the builder refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — narrow and wide brackets and the zero-column pair
    ///   distinguish a misplaced closer, a spurious flat space and reversed
    ///   width-tainted alternatives; other widths are not enumerated.
    /// - witness: `tests::goldens::pair_of_injections_pins_sum_notation`
    /// - witness: `tests::goldens::record_value_breaks_fields_at_the_narrow_page`
    /// - witness: `tests::goldens::doubly_tainted_pair_keeps_the_broken_separator`
    #[spec(
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| self.pieces.len() == entry && match *ret {
            | Ok(_) | Err(PresentationError::Build(_)) => true,
            | Err(_) => false,
        },
    )]
    fn none_or_break(
        &mut self,
        head: Doc,
    ) -> Result<Doc, PresentationError>
    {
        let none = Doc::EMPTY;
        let line = Doc::HARD_LINE;
        let choice = self.builder.choice(line, none)?;
        self.builder.concat(head, choice)
    }

    /// `head`, `body` and a closing brace, as one group: on one line, a space
    /// inside each brace, or `body` on its own lines two columns in and the
    /// brace on a line of its own.
    ///
    /// # Specification
    /// - requires: `head` ends with its opening brace.
    /// - ensures: a group whose flat branch is `head body }` with one space
    ///   either side of `body` and whose broken branch breaks after `head`,
    ///   indents `body` two columns and puts the closer on its own line; every
    ///   soft line inside `body` breaks with the group unless a group of its
    ///   own holds it.
    /// - provides: the layout of a lambda's, a thunk's and a bound block's
    ///   body.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Build`] when the builder refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda over a bind at the wide page and at a page
    ///   it overflows distinguishes a missing indent, a closer left inline and
    ///   a statement separator that breaks apart from its block.
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    #[spec(
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| self.pieces.len() == entry && match *ret {
            | Ok(doc) => doc != head && doc != body,
            | Err(PresentationError::Build(_)) => true,
            | Err(_) => false,
        },
    )]
    fn block(
        &mut self,
        head: Doc,
        body: Doc,
    ) -> Result<Doc, PresentationError>
    {
        let line = Doc::LINE;
        let inner = self.builder.concat(line, body)?;
        let inner = self.builder.nest(NestAmount::from(CONTINUATION), inner)?;
        let close = self.leaf(Glyphs("}"))?;
        let doc = self.builder.concat_all(&[head, inner, line, close])?;
        self.builder.group(doc)
    }

    /// `piece` bare when it binds at most as loosely as `loosest`, a block
    /// `{ … }` when it is a bind's statements, and parenthesized otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the piece's document bare when its binding is at most
    ///   `loosest`; between braces, as [`Self::block`] lays them out, when it
    ///   is a [`Binding::Sequence`] the slot does not admit; else between
    ///   parentheses.
    /// - provides: the slots a computation stands in where its body goes on.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bind run by a bind and a returner at a call's head
    ///   distinguish a block from parentheses and from a bare operand.
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `tests::goldens::a_block_body_holds_its_sequence_bare`
    #[spec(
        captures: [entry = self.pieces.len()],
        ensures: |ref ret| self.pieces.len() == entry && match *ret {
            | Ok(doc) => (doc == piece.doc) == (piece.binding <= loosest),
            | Err(PresentationError::Build(_)) => piece.binding > loosest,
            | Err(_) => false,
        },
    )]
    fn bare_or_block(
        &mut self,
        piece: Piece,
        loosest: Binding,
    ) -> Result<Doc, PresentationError>
    {
        if piece.binding == Binding::Sequence && loosest < Binding::Sequence {
            let open = self.leaf(Glyphs("{"))?;
            return self.block(open, piece.doc);
        }
        self.bare_up_to(piece, loosest)
    }

    /// Spells one node, or schedules its children and their join.
    ///
    /// # Specification
    /// - requires: `tasks` is the walk's stack, and `former` is what `source`
    ///   reads at `node`.
    /// - ensures: a value at the depth limit finishes as `<deep>`; a node of a
    ///   sort its position does not admit and an unreadable node finish as `?`;
    ///   a thunk finishes as `<thunk>` where bodies are opaque; a leaf former
    ///   finishes as its spelling, the 0-ary product as `Unit`, the 0-ary sum
    ///   as `Void` and the sum of two 0-ary products as `Bool`; a composite
    ///   former pushes its join below its children's visits, each label
    ///   scheduled just before its entry and each child between the opening and
    ///   the closing of the binders it stands under; a former spelled by parts
    ///   pushes its parts as [`Self::form`] builds them; a static application
    ///   schedules its spine as [`Self::spine`] does and an application its
    ///   call as [`Self::call`] does; a decode, a quote, a returner where the
    ///   body ends, a nested computation and a returned value push their
    ///   child's visit alone, so the child's piece is theirs; a returner
    ///   anywhere else is `pure v` and a run `run c`.
    /// - provides: one step of the walk.
    /// - fails: as [`Self::leaf`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::leaf`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete grammar fixtures, nested binders and deep or
    ///   misplaced nodes distinguish missing work, reversed children, binder
    ///   scope leakage and lost approximation. Mutable-source fixtures bound
    ///   traversal but do not prove name consistency across mutations.
    /// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `tests::goldens::static_operators_spell_as_the_grammar_writes_them`
    /// - witness: `tests::goldens::beyond_the_depth_limit_renders_deep`
    /// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
    /// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `tests::goldens::a_scoped_capability_names_its_scope_400`
    /// - witness: `tests::goldens::a_returner_lists_each_interface_of_its_row_between_commas`
    #[spec(
        captures: [entry = self.pieces.len(), pending = tasks.len(), opened = self.opened.len(), fidelity = self.fidelity],
        ensures: |ref ret| self.opened.len() == opened
            && (fidelity != Fidelity::Approximate || self.fidelity == Fidelity::Approximate)
            && match *ret {
                | Ok(()) => (entry.checked_add(1_usize) == Some(self.pieces.len()) && tasks.len() == pending)
                    || (self.pieces.len() == entry && tasks.len() > pending),
                | Err(PresentationError::Build(_)) => self.pieces.len() == entry && tasks.len() == pending,
                | Err(_) => false,
            },
    )]
    fn visit<S>(
        &mut self,
        source: &S,
        node: S::Node,
        former: Former<'_, S::Node>,
        admits: Admits,
        depth: ValueDepth,
        tasks: &mut Vec<Task<S::Node>>,
    ) -> Result<(), PresentationError>
    where
        S: Source + ?Sized,
    {
        let kind = kind(&former);
        match reach(admits, depth, kind) {
            Reach::Spell => {},
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a node past the depth limit is left out, written `<deep>`"
                )
            )]
            Reach::Deep => {
                return self.approximate(Glyphs("<deep>"), Unspelled::Elided(Elided::Deep));
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a node of a sort its position does not admit: no spelling is both \
                              the node and what the position reads"
                )
            )]
            Reach::Misplaced => return self.unspell(Unspelled::Misplaced),
        }
        // The slots a former read whole in a shape of its own stands over, in
        // place of its child table's.
        let mut shaped = None;
        let join = match former {
            Former::BaseType(BaseType::Integer) => {
                return writes(Production("primitive_type"), self.atom(Glyphs("Integer")));
            },
            Former::BaseType(BaseType::String) => {
                return writes(Production("primitive_type"), self.atom(Glyphs("String")));
            },
            Former::Product(arity) if usize::from(arity) == 0 => {
                return writes(Production("primitive_type"), self.atom(Glyphs("Unit")));
            },
            Former::Sum(arity) if usize::from(arity) == 0 => {
                return writes(Production("primitive_type"), self.atom(Glyphs("Void")));
            },
            // `Bool` is the sum of two units, a fixed name as the lowering
            // reads it.
            Former::Sum(arity)
                if usize::from(arity) == 2
                    && let Some(name) = named_sum(source, node) =>
            {
                return writes(Production("type_identifier"), self.atom(name));
            },
            Former::Unit => {
                return writes(Production("unit.expression"), self.atom(Glyphs("unit")));
            },
            Former::ListNil => {
                return writes(
                    Production("identifier.expression"),
                    self.atom(Glyphs("nil")),
                );
            },
            // A name is written as it stands, a qualified one as its path.
            Former::Abstract(name) => {
                return writes(
                    Production("type_identifier"),
                    writes(Production("type_path"), self.name(name)),
                );
            },
            Former::Constant(name) => {
                return writes(
                    Production("identifier.expression"),
                    writes(
                        Production("constructor.expression"),
                        writes(Production("projection_expression"), self.name(name)),
                    ),
                );
            },
            Former::Literal(value) => {
                let spelled = literal(value);
                let production = match *value {
                    Literal::Integer(_) | Literal::Numeric(_) => Production("number.expression"),
                    Literal::Text(_) => Production("string.expression"),
                };
                return writes(production, self.atom(Glyphs(spelled.0.as_str())));
            },
            Former::Capability {
                authority,
                grade,
                region,
            } => {
                let mut spelled = alloc::string::String::from("Cap");
                if grade == gandr_core_term::effect::capability::CapabilityGrade::Consumable {
                    spelled.push_str("[1]");
                }
                spelled.push_str(" {");
                spelled.push_str(&authority.granted().join(", "));
                spelled.push('}');
                return match region {
                    gandr_core_term::effect::capability::Region::Held => writes(
                        Production("capability_type"),
                        self.atom(Glyphs(spelled.as_str())),
                    ),
                    // A scoped capability names the scope whose region it
                    // lives in, `Cap {…} at c`; past the scopes the source
                    // names, its region goes unwritten.
                    gandr_core_term::effect::capability::Region::Scoped(depth) => {
                        let named = self.region(source, depth).filter(|name| {
                            !name.0.is_empty() && !name.0.contains(char::is_whitespace)
                        });
                        match named {
                            Some(name) => {
                                spelled.push_str(" at ");
                                spelled.push_str(&name.0);
                                writes(
                                    Production("at_type"),
                                    writes(
                                        Production("capability_type"),
                                        self.atom(Glyphs(spelled.as_str())),
                                    ),
                                )
                            },
                            #[cfg_attr(
                                dylint_lib = "quenchant_dylints",
                                expect(
                                    answer_totality,
                                    reason = "a region past the scopes the source names has no \
                                              name to write after `at`"
                                )
                            )]
                            None => self.approximate(
                                Glyphs(spelled.as_str()),
                                Unspelled::Elided(Elided::Region),
                            ),
                        }
                    },
                };
            },
            Former::Universe { sort, level } => {
                return match universe(sort, level) {
                    Maybe::Present(spelled) => writes(
                        Production("universe_type"),
                        self.atom(Glyphs(spelled.0.as_str())),
                    ),
                    #[cfg_attr(
                        dylint_lib = "quenchant_dylints",
                        expect(
                            answer_totality,
                            reason = "a universe over a sort parameter or at a level mentioning a \
                                      variable, which the surface's universe atom, a sort and a \
                                      numeral level, cannot write"
                        )
                    )]
                    Maybe::Absent(_) => self.unspell(Unspelled::Universe),
                };
            },
            // A variable reads as the name of its binder, in a type as a type
            // variable.
            Former::Variable { zone, index } => {
                return writes(
                    Production("identifier.expression"),
                    writes(Production("type_variable"), self.variable(zone, index)),
                );
            },
            Former::Thunk(_) => match self.bodies {
                #[cfg_attr(
                    dylint_lib = "quenchant_dylints",
                    expect(
                        answer_totality,
                        reason = "a thunk presented with its body opaque is written `<thunk>`"
                    )
                )]
                Bodies::Opaque => {
                    return self.approximate(Glyphs("<thunk>"), Unspelled::Elided(Elided::Thunk));
                },
                Bodies::Spelled => Some(writes(Production("thunk_expression"), Join::Thunk)),
            },
            Former::Run(_) => Some(writes(
                Production("run_expression"),
                Join::Prefix(Prefix::Run),
            )),
            Former::Path { .. }
            | Former::Flow { .. }
            | Former::Relation { .. }
            | Former::Data { .. }
            | Former::Codata { .. }
            | Former::Constructor { .. }
            | Former::Recorded { .. }
            | Former::Primitive { .. }
            | Former::Transport(..)
            | Former::PathTransport { .. }
            | Former::Ride { .. }
            | Former::TelescopeTransport { .. }
            | Former::Fixpoint(_)
            | Former::Case { .. }
            | Former::Split { .. }
            | Former::DataCase { .. }
            | Former::RecordProjection(..)
            | Former::TupleProjection(..)
            | Former::ListFold { .. }
            | Former::ListCase { .. }
            | Former::Perform { .. }
            | Former::Handle { .. }
            | Former::Exercise { .. }
            | Former::Scope { .. }
            | Former::Resume(..)
            | Former::Reset(_)
            | Former::Shift(_)
            | Former::Lazy(..)
            | Former::Then(..)
            | Former::Project(..)
            | Former::Send { .. }
            | Former::Receive { .. }
            | Former::Select { .. }
            | Former::Offer { .. }
            | Former::Close(_)
            | Former::Fork { .. }
            | Former::Hold { .. }
            | Former::Access { .. }
            | Former::ResumeView { .. }
            | Former::AbortView(_)
            | Former::Located { .. }
            | Former::Kept { .. }
            | Former::WorldHold(_)
            | Former::Leta { .. }
            | Former::Migrate { .. } => Some(self.form(source, node, &former, admits)),
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a reified stack has no surface spelling: written `<stack>`"
                )
            )]
            Former::Reify => {
                return self.approximate(Glyphs("<stack>"), Unspelled::Elided(Elided::Stack));
            },
            Former::Stack(..) => Some(writes(
                Production("type_application"),
                Join::Bracket(Bracket::Stack),
            )),
            Former::With(arity) if self.form == Form::Sugared && usize::from(arity) >= 2 => {
                Some(writes(Production("lazy_product_type"), Join::Infix {
                    infix: Infix::Lazy,
                    arity: Arity(usize::from(arity)),
                }))
            },
            Former::With(arity) => Some(writes(Production("lazy_record_type"), Join::Braced {
                brace: Brace::Ampersand,
                arity: Arity(usize::from(arity)),
                entries: Entries::Positional,
            })),
            Former::Session {
                protocol,
                state,
                payloads,
            } => {
                let (template, binding, fidelity) = protocol_template(protocol, state);
                if fidelity == Fidelity::Approximate {
                    self.fidelity = Fidelity::Approximate;
                    #[cfg_attr(
                        dylint_lib = "quenchant_dylints",
                        expect(
                            answer_totality,
                            reason = "a session type at a state its protocol does not hold: a \
                                      malformed protocol"
                        )
                    )]
                    let _fresh = self.unspelled.insert(Unspelled::Protocol);
                }
                self.protocols.push(template);
                // The protocol's template writes each session former.
                let join = Join::Session {
                    payloads: Arity(usize::from(payloads)),
                    binding,
                };
                let join = writes(Production("send_session_type"), join);
                let join = writes(Production("receive_session_type"), join);
                let join = writes(Production("end_session_type"), join);
                let join = writes(Production("mu_session_type"), join);
                Some(join)
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "the numeric base atom: the type of a numeric literal, which the \
                              surface grammar has no name for"
                )
            )]
            Former::BaseType(BaseType::Numeric) => {
                return self.unspell(Unspelled::Unreadable(Unreadable::NumericAtom));
            },
            // The unknown type, where a type is read, is the grammar's
            // `unknown_type` atom `?`; the lowering admits no unknown type, so
            // the spelling stays approximate.
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "the unknown type a hole or a mark synthesises: written as the \
                              grammar's `unknown_type`, which the lowering does not admit"
                )
            )]
            Former::Unreadable(Unreadable::UnknownType)
                if matches!(admits, Admits::Type | Admits::ValueType | Admits::CompType) =>
            {
                return writes(
                    Production("unknown_type"),
                    self.unspell(Unspelled::Unreadable(Unreadable::UnknownType)),
                );
            },
            // A hole is the term the author has not written; where a term is
            // read its `?` is the grammar's hole, and it reads back as the same
            // hole: a hole is named by its place among its source's holes, which
            // a printing in its declaration's place keeps.
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a hole, a term the author has not written: the walk writes it as \
                              the grammar's hole `?`"
                )
            )]
            Former::Unreadable(Unreadable::Hole) => {
                return writes(Production("hole"), self.atom(Glyphs("?")));
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "the honest set's other members, a dangling handle, an unnamed \
                              reference, a mark, a lift, a world's capability and the unknown \
                              type where a term is read, have no surface spelling"
                )
            )]
            Former::Unreadable(reason) => return self.unspell(Unspelled::Unreadable(reason)),
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "the universe path has no surface syntax: written in the printer's \
                              notation"
                )
            )]
            Former::PathUniverse(..) => {
                self.note(Unspelled::Notation(Notation::PathUniverse));
                Some(writes(
                    Production("type_application"),
                    Join::Bracket(Bracket::PathUniverse),
                ))
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a universe path's reflexivity has no surface syntax: written in \
                              the printer's notation"
                )
            )]
            Former::PathRefl(_) => {
                self.note(Unspelled::Notation(Notation::PathRefl));
                Some(writes(
                    Production("call_expression"),
                    Join::Bracket(Bracket::PathRefl),
                ))
            },
            Former::Here(_) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::Here),
            )),
            Former::Funext(..) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::Funext),
            )),
            Former::Equiv(..) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::Equiv),
            )),
            Former::Univalence(_) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::Univalence),
            )),
            Former::SessionRelated(SessionRelation::Equivalence, ..) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::Bisim),
            )),
            Former::SessionRelated(SessionRelation::Subtyping, ..) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::Sim),
            )),
            Former::Stay(_) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::Stay),
            )),
            Former::FlowProduct(..) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::FlowProduct),
            )),
            Former::Back(_) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::Back),
            )),
            Former::Cong(..) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::Cong),
            )),
            Former::Forward(_) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::Forward),
            )),
            Former::FunctionFlow(..) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::Arrow),
            )),
            Former::RunType(_) => Some(writes(
                Production("type_application"),
                Join::Bracket(Bracket::Run),
            )),
            Former::Ua {
                stratum,
                source: from,
                target: to,
                ..
            } => {
                let head = alloc::format!(
                    "ua[{}, {}]({}, {},",
                    usize::from(stratum.degree),
                    usize::from(stratum.bound),
                    from.as_ref(),
                    to.as_ref(),
                );
                let head = self.leaf(Glyphs(&head))?;
                // The stratum's two numerals are the instantiation's type
                // residents, each a numeral where a type is read.
                Some(writes(
                    Production("instantiation_expression"),
                    writes(
                        Production("instantiation.type"),
                        writes(
                            Production("number.type"),
                            writes(Production("call_expression"), Join::Ua(head)),
                        ),
                    ),
                ))
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "the path out of an equivalence has no surface syntax: written in \
                              the printer's notation"
                )
            )]
            Former::PathEquiv(..) => {
                self.note(Unspelled::Notation(Notation::PathEquiv));
                Some(writes(
                    Production("call_expression"),
                    Join::Bracket(Bracket::PathEquiv),
                ))
            },
            Former::PathProduct(..) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::PathProduct),
            )),
            Former::Product(arity) if self.form == Form::Sugared && usize::from(arity) >= 2 => {
                Some(writes(Production("product_type"), Join::Infix {
                    infix: Infix::Product,
                    arity: Arity(usize::from(arity)),
                }))
            },
            Former::Sum(arity) if self.form == Form::Sugared && usize::from(arity) >= 2 => {
                Some(writes(Production("sum_type"), Join::Infix {
                    infix: Infix::Sum,
                    arity: Arity(usize::from(arity)),
                }))
            },
            Former::Tuple(arity) if self.form == Form::Sugared && usize::from(arity) >= 2 => {
                Some(writes(
                    Production("parenthesized_expression"),
                    Join::Tuple(Arity(usize::from(arity))),
                ))
            },
            Former::Product(arity) => Some(writes(Production("telescope_type"), Join::Braced {
                brace: Brace::Hash,
                arity: Arity(usize::from(arity)),
                entries: Entries::Positional,
            })),
            Former::Tuple(arity) => {
                Some(writes(Production("telescope_expression"), Join::Braced {
                    brace: Brace::Hash,
                    arity: Arity(usize::from(arity)),
                    entries: Entries::Positional,
                }))
            },
            Former::Sum(arity) => Some(writes(Production("labelled_sum_type"), Join::Braced {
                brace: Brace::Plus,
                arity: Arity(usize::from(arity)),
                entries: Entries::Positional,
            })),
            Former::RecordType(arity) => Some(writes(Production("telescope_type"), Join::Braced {
                brace: Brace::Hash,
                arity: Arity(usize::from(arity)),
                entries: Entries::Labelled(Label::Field),
            })),
            Former::List(_) => Some(writes(
                Production("type_application"),
                Join::Bracket(Bracket::List),
            )),
            Former::ThunkType(body) => {
                if self.form == Form::Sugared
                    && let Some((links, dependent, codomain)) = self.alias(source, body)
                {
                    tasks.push(Task::Join(writes(
                        Production("value_function_type"),
                        writes(
                            Production("parenthesized_type"),
                            Join::ValueFunction(Arity(links.len()), dependent),
                        ),
                    )));
                    for _ in 0_u32 .. dependent.0.count_ones() {
                        tasks.push(Task::Unbind);
                    }
                    tasks.push(match codomain {
                        Codomain::Result(node) => Task::Visit {
                            node,
                            admits: Admits::ValueType,
                            depth,
                        },
                        Codomain::Reduct(node) => Task::Returned { node, depth },
                    });
                    for link in links.into_iter().rev() {
                        if link.opener.is_some() {
                            tasks.push(Task::Bind(Binds::ONE.zone, link.opener));
                        }
                        tasks.push(Task::Visit {
                            node: link.domain,
                            admits: Admits::ValueType,
                            depth,
                        });
                    }
                    return Ok(());
                }
                Some(writes(Production("u_type"), Join::Prefix(Prefix::Thunk)))
            },
            Former::Returner(_) => {
                Some(writes(Production("f_type"), Join::Prefix(Prefix::Returner)))
            },
            Former::EffectfulReturner { effects, .. } => {
                let mut annotation = String::from("-F [");
                for (index, interface) in effects.interfaces().iter().enumerate() {
                    if index != 0 {
                        annotation.push_str(", ");
                    }
                    annotation.push_str(interface.as_ref());
                }
                annotation.push_str("] ");
                let head = self.leaf(Glyphs(&annotation))?;
                Some(writes(Production("f_type.row"), Join::EffectReturner(head)))
            },
            Former::Arrow { .. } | Former::StaticPi { .. } => {
                Some(writes(Production("function_type"), Join::Arrow))
            },
            // A dependent arrow names its binder in a parenthesized domain,
            // `(x : A) -> C`.
            Former::Pi { .. } => Some(writes(
                Production("function_type"),
                writes(Production("parenthesized_type"), Join::Pi),
            )),
            Former::Sigma { .. } => Some(writes(Production("telescope_type"), Join::Sigma)),
            Former::StaticLambda(_) => {
                Some(writes(Production("static_abstraction"), Join::StaticLambda))
            },
            Former::Record(arity) => {
                Some(writes(Production("telescope_expression"), Join::Braced {
                    brace: Brace::Hash,
                    arity: Arity(usize::from(arity)),
                    entries: Entries::Labelled(Label::Assignment),
                }))
            },
            Former::ListCons(..) => Some(writes(
                Production("call_expression"),
                Join::Bracket(Bracket::ListCons),
            )),
            Former::Injection(..) => Some(writes(
                Production("labelled_sum_expression"),
                Join::Braced {
                    brace: Brace::Plus,
                    arity: Arity(1_usize),
                    entries: Entries::Labelled(Label::Summand),
                },
            )),
            Former::StaticApplication(operator, argument) => {
                Self::spine(source, operator, argument, depth, ReductAs::Term, tasks);
                return writes(Production("type_application"), Ok(()));
            },
            Former::Application(function, argument) => {
                Self::call(source, function, argument, depth, tasks);
                return writes(Production("call_expression"), Ok(()));
            },
            // A body that ends answering a type's code keeps its `pure`: the
            // lowering reads a type at a body's end only as a returned value.
            // So does one that ends answering a `run`: bare at a statement's
            // head, `run` opens a bind, `run x <- c ; …`.
            Former::Return(returned) => match admits {
                Admits::Computation(Tail::Ends | Tail::Unstated)
                    if !matches!(
                        source.read(returned),
                        Former::Quote(_) | Former::QuoteComputation(_) | Former::Run(_)
                    ) =>
                {
                    None
                },
                Admits::Computation(Tail::Ends | Tail::Continues | Tail::Unstated)
                | Admits::Type
                | Admits::ValueType
                | Admits::CompType
                | Admits::Value
                | Admits::Stated
                | Admits::Operand => Some(writes(
                    Production("pure_expression"),
                    Join::Prefix(Prefix::Pure),
                )),
            },
            Former::Force(_) => Some(writes(
                Production("force_expression"),
                Join::Prefix(Prefix::Force),
            )),
            Former::Bind(bound, rest) => match self.typed_bind(source, bound) {
                Some((ascribed, result)) => {
                    shaped = Some(Vec::from([
                        Slot::of(ascribed, Admits::Computation(Tail::Continues), Binds::NONE),
                        Slot::of(result, Admits::ValueType, Binds::NONE),
                        Slot::of(rest, admits, Binds::ONE),
                    ]));
                    Some(writes(Production("block"), Join::TypedSequence))
                },
                None => Some(writes(Production("block"), Join::Sequence)),
            },
            // An ascription outside a typed bind has no spelling of its own:
            // it stands as its body, its type unwritten.
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "the surface writes an ascription only in a typed bind: elsewhere \
                              it stands as its body"
                )
            )]
            Former::Ascription { body, .. } => {
                self.note(Unspelled::Elided(Elided::Ascription));
                shaped = Some(Vec::from([Slot::of(body, admits, Binds::NONE)]));
                None
            },
            Former::Lambda(_) => Some(writes(Production("lambda_expression"), Join::Lambda)),
            // A nested call the lowering bound by a run, `x ← f(a); g(x)`,
            // spells as the call it was written as, `g(f(a))`: a type has no
            // run to read back (#676).
            Former::Nested(body) | Former::Returned(body) if bound_call(source, body).is_some() => {
                Self::inlined(source, body, below(depth, kind), tasks);
                return writes(Production("call_expression"), Ok(()));
            },
            // A quoted type whose head no expression reads, standing where an
            // expression is read, is written in the quote's own spelling,
            // `type(T)`; every other one stands bare, as the lowering quotes a
            // type written where a value is read, and a type position reads
            // the type itself.
            Former::Quote(quoted) | Former::QuoteComputation(quoted)
                if self.surface == Surface::Expression
                    && self.unread_as_expression(source, quoted) == Bare::Unread =>
            {
                Some(writes(
                    Production("type_quote_expression"),
                    Join::Bracket(Bracket::TypeQuote),
                ))
            },
            // A quoted type stands where an expression is read, which takes
            // the alias only over one bare domain, `A => C`: a parenthesized
            // domain list there, `(c : U) => el(c)` or `() => C`, reads as a
            // parenthesized expression. Any other alias is written as the
            // thunk it stands for, `+U ((c : U) -> -F el(c))`.
            Former::Quote(quoted)
                if self.form == Form::Sugared
                    && let Former::ThunkType(body) = source.read(quoted)
                    && !self
                        .alias(source, body)
                        .is_some_and(|(links, dependent, _)| {
                            links.len() == 1_usize && dependent.0 == 0_u64
                        }) =>
            {
                shaped = Some(Vec::from([Slot::of(body, Admits::CompType, Binds::NONE)]));
                Some(writes(Production("u_type"), Join::Prefix(Prefix::Thunk)))
            },
            // A computation where a value is read stands bare, its run left
            // to the checker, and so does the computation a returned value
            // stands for; its piece, as a decode's and a quote's, is the
            // node's.
            Former::Element(_)
            | Former::ComputationElement(_)
            | Former::Quote(_)
            | Former::QuoteComputation(_)
            | Former::Nested(_)
            | Former::Returned(_) => None,
        };
        if let Some(join) = join {
            tasks.push(Task::Join(join));
        }
        let below = below(depth, kind);
        let slots = match shaped {
            Some(slots) => slots,
            None => children(source, node, &former, admits, self.bodies),
        };
        for (index, slot) in slots.into_iter().enumerate().rev() {
            for _ in 0_usize .. slot.binds.count {
                tasks.push(Task::Unbind);
            }
            let surface = surface_below(self.surface, &former, slot.admits);
            if surface != self.surface {
                tasks.push(Task::Surface(self.surface));
            }
            tasks.push(slot.node.map_or(Task::Missing, |child| Task::Visit {
                node: child,
                admits: slot.admits,
                depth: below,
            }));
            if surface != self.surface {
                tasks.push(Task::Surface(surface));
            }
            let opener = (slot.binds.count == 1_usize).then_some(node);
            // A capability scope's subject, its first slot, and a hold's scope,
            // its second, stand in the region the scope or the hold opens.
            let scoped = (index == 0_usize && matches!(former, Former::Scope { .. }))
                || (index == 1_usize && matches!(former, Former::Hold { .. }));
            for _ in 0_usize .. slot.binds.count {
                tasks.push(if scoped {
                    Task::BindScope(slot.binds.zone, opener)
                }
                else {
                    Task::Bind(slot.binds.zone, opener)
                });
            }
            if let Some(label) = slot.label {
                tasks.push(Task::Label(label));
            }
        }
        Ok(())
    }

    /// Schedules a static application and the applications under its
    /// operator as one application, `f(a1, …, an)`, or, where the operator is
    /// a static abstraction, as the redex's reduct.
    ///
    /// # Specification
    /// - requires: the application at `depth` applies `operator` to `argument`,
    ///   and `tasks` is the walk's stack.
    /// - ensures: the operator is read down through every static application it
    ///   is, each argument scheduled at the depth the scan reaches it at, until
    ///   an operator that is no application or one at the depth limit. An
    ///   operator that is a static abstraction consumes the first arguments,
    ///   one per binder of its chain: those arguments are visited first, then
    ///   their binders opened standing for them, the abstraction's body walked
    ///   under them and the binders closed; any arguments left apply to that
    ///   reduct as below. Otherwise the operator is scheduled as itself; the
    ///   join over the operator and the arguments, left to right, is pushed
    ///   below their visits, the operator visited first. Read as
    ///   [`ReductAs::Result`], a reduct with no argument left is scheduled as
    ///   the value type it returns, the codomain of an alias.
    /// - provides: the one spelling the surface writes a spine in, which a join
    ///   over one application at a time could not give.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Every turn of the scan deepens the depth it reads at by one, and the
    /// loop stops at [`DEPTH_LIMIT`]; every turn of the abstraction's peel
    /// consumes one argument, and stops when they are spent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one- and three-argument spines observe argument order
    ///   and operator parentheses; the exact depth cutoff observes an unpeeled
    ///   operator scheduled before its argument; a redex of one and of two
    ///   arguments, and one whose abstraction is applied past its chain,
    ///   observe the reduct and the arguments left. Longer stable spines and
    ///   arbitrary changing sources are not enumerated.
    /// - witness: `tests::goldens::static_operators_spell_as_the_grammar_writes_them`
    /// - witness: `tests::goldens::a_static_redex_prints_as_its_reduct_401`
    /// - witness: `walk::tests::spine_schedules_operator_first_at_the_depth_limit`
    #[spec(
        captures: [entry = tasks.len()],
        ensures: |()| tasks.get(entry..).is_some_and(|scheduled| {
            let substituted = scheduled.iter().find_map(|task| if let Task::Substitute(Arity(count)) = *task { Some(count) } else { None });
            if let Some(count) = substituted {
                count > 0_usize
                    && scheduled.iter().filter(|task| matches!(**task, Task::Unbind)).count() == count
            }
            else {
                let Some((&Task::Join(Join::Apply(Arity(arity))), visits)) = scheduled.split_first()
                else { return false; };
                arity > 0_usize && u32::try_from(arity).is_ok_and(|count| count <= DEPTH_LIMIT.0.max(1_u32))
                    && arity.checked_add(1_usize) == Some(visits.len())
                    && visits.iter().all(|task| matches!(*task,
                        Task::Visit { admits: Admits::Value, depth: at, .. }
                            if at.0 >= depth.0.saturating_add(1_u32)
                                && at.0 <= DEPTH_LIMIT.0.max(depth.0.saturating_add(1_u32))))
            }
        }),
    )]
    fn spine<S>(
        source: &S,
        operator: S::Node,
        argument: S::Node,
        depth: ValueDepth,
        reduct_as: ReductAs,
        tasks: &mut Vec<Task<S::Node>>,
    ) where
        S: Source + ?Sized,
    {
        let mut level = below(depth, Kind::Value);
        let mut arguments = Vec::from([(argument, level)]);
        let mut operator = operator;
        while level < DEPTH_LIMIT {
            let Former::StaticApplication(inner, next) = source.read(operator)
            else {
                break;
            };
            level = level.deeper();
            arguments.push((next, level));
            operator = inner;
        }
        // The arguments in the order they are applied, the first outermost.
        arguments.reverse();
        let mut consumed = 0_usize;
        while consumed < arguments.len() {
            let Former::StaticLambda(body) = source.read(operator)
            else {
                break;
            };
            operator = body;
            consumed = consumed.saturating_add(1_usize);
        }
        let left = arguments.split_off(consumed);
        if !left.is_empty() {
            tasks.push(Task::Join(Join::Apply(Arity(left.len()))));
        }
        for &(node, at) in left.iter().rev() {
            tasks.push(Task::Visit {
                node,
                admits: Admits::Value,
                depth: at,
            });
        }
        for _ in 0_usize .. consumed {
            tasks.push(Task::Unbind);
        }
        tasks.push(if reduct_as == ReductAs::Result && left.is_empty() {
            Task::Returned {
                node: operator,
                depth: level,
            }
        }
        else {
            Task::Visit {
                node: operator,
                admits: Admits::Value,
                depth: level,
            }
        });
        if consumed > 0_usize {
            tasks.push(Task::Substitute(Arity(consumed)));
        }
        for &(node, at) in arguments.iter().rev() {
            tasks.push(Task::Visit {
                node,
                admits: Admits::Value,
                depth: at,
            });
            tasks.push(Task::Hold);
        }
    }

    /// Schedules the value type the computation type `node` returns, the
    /// codomain of a value-function alias.
    ///
    /// # Specification
    /// - requires: `node` is a codomain [`Self::alias`] found as a reduct, and
    ///   `tasks` is the walk's stack.
    /// - ensures: a returner's result scheduled as a value type at `depth`; a
    ///   decode's and a quote's child scheduled the same way again; a static
    ///   redex scheduled by [`Self::spine`] with its reduct read as its result;
    ///   any other node, which [`Self::alias`] does not answer with, scheduled
    ///   as the computation type it is.
    /// - provides: the reduct half of the alias's codomain, under the binders
    ///   the redex's spine opens for its arguments.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk over an arrow into a static redex of a
    ///   returner spells as the alias over the reduct's result.
    /// - witness: `tests::goldens::a_static_redex_prints_as_its_reduct_401`
    #[spec(captures: [entry = tasks.len()], ensures: tasks.len() > entry)]
    fn returned<S>(
        source: &S,
        node: S::Node,
        depth: ValueDepth,
        tasks: &mut Vec<Task<S::Node>>,
    ) where
        S: Source + ?Sized,
    {
        let former = source.read(node);
        if let Former::Returner(result) = former {
            tasks.push(Task::Visit {
                node: result,
                admits: Admits::ValueType,
                depth,
            });
        }
        else if let Former::ComputationElement(child) | Former::QuoteComputation(child) = former {
            tasks.push(Task::Returned { node: child, depth });
        }
        else if let Former::StaticApplication(operator, argument) = former {
            Self::spine(source, operator, argument, depth, ReductAs::Result, tasks);
        }
        else {
            tasks.push(Task::Visit {
                node,
                admits: Admits::CompType,
                depth,
            });
        }
    }

    /// Schedules an application and the applications under its function as
    /// one call, `f(a1, …, an)`, or, where the function is a function literal
    /// whose body returns, as the value the call returns.
    ///
    /// # Specification
    /// - requires: the application at `depth` applies `function` to `argument`,
    ///   and `tasks` is the walk's stack.
    /// - ensures: the function is read down through every application it is, at
    ///   most [`DEPTH_LIMIT`] arguments in all, each argument scheduled as a
    ///   value at `depth`; a force at the head of the spine is scheduled as the
    ///   value it forces, the bridge the lowering writes before a value it
    ///   calls, and any other head as a computation where the body goes on; the
    ///   join over the head and the arguments, left to right, is pushed below
    ///   their visits, the head visited first. A forced thunk literal of at
    ///   least as many abstractions as the call has arguments, whose body then
    ///   returns, is scheduled instead as the value it returns, under one
    ///   binder per argument standing for the argument, the first outermost:
    ///   the type grammar has no call of a literal, and the reading back
    ///   compares such a call as what it returns (#675).
    /// - provides: the one spelling the surface writes a call in.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Every turn adds one argument, and the loop stops at [`DEPTH_LIMIT`]
    /// arguments.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call of a forced constant on two arguments and a
    ///   call whose head is a returner observe argument order, the elided force
    ///   and the head's parentheses; a call of a literal identity and of a
    ///   literal projection on two arguments observe the reduct and the binder
    ///   each argument stands for, and a literal whose body does more than
    ///   return stays a call.
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `tests::goldens::a_call_collects_its_arguments_up_to_the_depth_limit`
    /// - witness: `tests::goldens::a_called_function_literal_prints_as_what_it_returns_675`
    #[spec(
        captures: [entry = tasks.len()],
        ensures: |()| tasks.get(entry..).is_some_and(|scheduled| {
            let substituted = scheduled.iter().find_map(|task| if let Task::Substitute(Arity(count)) = *task { Some(count) } else { None });
            if let Some(count) = substituted {
                return count > 0_usize
                    && scheduled.iter().filter(|task| matches!(**task, Task::Unbind)).count() == count
                    && scheduled.iter().filter(|task| matches!(**task, Task::Hold)).count() == count
                    && count.checked_mul(3_usize).and_then(|all| all.checked_add(2_usize)) == Some(scheduled.len());
            }
            let Some((&Task::Join(Join::Apply(Arity(arity))), visits)) = scheduled.split_first()
            else { return false; };
            arity > 0_usize && u32::try_from(arity).is_ok_and(|count| count <= DEPTH_LIMIT.0)
                && arity.checked_add(1_usize) == Some(visits.len())
                && visits.split_last().is_some_and(|(head, arguments)|
                    matches!(*head, Task::Visit { admits: Admits::Value | Admits::Computation(Tail::Continues), depth: at, .. } if at == depth)
                        && arguments.iter().all(|task| matches!(*task, Task::Visit { admits: Admits::Value, depth: at, .. } if at == depth)))
        }),
    )]
    fn call<S>(
        source: &S,
        function: S::Node,
        argument: S::Node,
        depth: ValueDepth,
        tasks: &mut Vec<Task<S::Node>>,
    ) where
        S: Source + ?Sized,
    {
        let limit = usize::try_from(u32::from(DEPTH_LIMIT)).unwrap_or(usize::MAX);
        let mut arguments = Vec::from([argument]);
        let mut head = function;
        while arguments.len() < limit {
            let Former::Application(inner, next) = source.read(head)
            else {
                break;
            };
            arguments.push(next);
            head = inner;
        }
        if let Former::Force(thunk) = source.read(head)
            && let Former::Thunk(body) = source.read(thunk)
        {
            let mut reduct = body;
            let mut consumed = 0_usize;
            while consumed < arguments.len() {
                let Former::Lambda(inner) = source.read(reduct)
                else {
                    break;
                };
                reduct = inner;
                consumed = consumed.saturating_add(1_usize);
            }
            if consumed == arguments.len()
                && let Former::Return(result) = source.read(reduct)
            {
                for _ in 0_usize .. consumed {
                    tasks.push(Task::Unbind);
                }
                tasks.push(Task::Visit {
                    node: result,
                    admits: Admits::Value,
                    depth,
                });
                tasks.push(Task::Substitute(Arity(consumed)));
                for node in arguments {
                    tasks.push(Task::Visit {
                        node,
                        admits: Admits::Value,
                        depth,
                    });
                    tasks.push(Task::Hold);
                }
                return;
            }
        }
        tasks.push(Task::Join(Join::Apply(Arity(arguments.len()))));
        for node in arguments {
            tasks.push(Task::Visit {
                node,
                admits: Admits::Value,
                depth,
            });
        }
        tasks.push(if let Former::Force(thunk) = source.read(head) {
            Task::Visit {
                node: thunk,
                admits: Admits::Value,
                depth,
            }
        }
        else {
            Task::Visit {
                node: head,
                admits: Admits::Computation(Tail::Continues),
                depth,
            }
        });
    }

    /// Schedules a computation whose runs bind calls as its last step with
    /// each run's binder standing for the call it binds, `g(f(a))` for `x ←
    /// f(a); g(x)`.
    ///
    /// # Specification
    /// - requires: `body` is the computation a nested or returned value at
    ///   `depth` stands for, and `tasks` is the walk's stack.
    /// - ensures: every leading bind whose bound is a call ([`bound_call`]) is
    ///   peeled; each bound call is scheduled as a computation where the body
    ///   goes on, in order, each followed by one binder standing for it; the
    ///   rest is scheduled under them all, and every binder is closed after it.
    /// - provides: the nested call a type writes, which the lowering commutes
    ///   into runs and the type grammar cannot read back as runs.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Every turn peels one bind off the computation, a finite term.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one run and two runs, the second's call naming the
    ///   first's binder, observe each call standing for its binder in order.
    /// - witness: `tests::goldens::a_run_bound_call_in_a_type_prints_nested_676`
    #[spec(
        captures: [entry = tasks.len()],
        ensures: |()| tasks.get(entry..).is_some_and(|scheduled| {
            let substitutes = scheduled.iter().filter(|task| matches!(**task, Task::Substitute(Arity(1_usize)))).count();
            substitutes > 0_usize
                && scheduled.iter().filter(|task| matches!(**task, Task::Unbind)).count() == substitutes
                && scheduled.iter().filter(|task| matches!(**task, Task::Hold)).count() == substitutes
                && substitutes.checked_mul(4_usize).and_then(|all| all.checked_add(1_usize)) == Some(scheduled.len())
        }),
    )]
    fn inlined<S>(
        source: &S,
        body: S::Node,
        depth: ValueDepth,
        tasks: &mut Vec<Task<S::Node>>,
    ) where
        S: Source + ?Sized,
    {
        let mut bounds = Vec::new();
        let mut rest = body;
        while let Some((bound, next)) = bound_call(source, rest) {
            bounds.push(bound);
            rest = next;
        }
        for _ in &bounds {
            tasks.push(Task::Unbind);
        }
        tasks.push(Task::Visit {
            node: rest,
            admits: Admits::Computation(Tail::Continues),
            depth,
        });
        for &bound in bounds.iter().rev() {
            tasks.push(Task::Substitute(Arity(1_usize)));
            tasks.push(Task::Visit {
                node: bound,
                admits: Admits::Computation(Tail::Continues),
                depth,
            });
            tasks.push(Task::Hold);
        }
    }

    /// A leaf naming the binder at `offset` among those the join at hand's
    /// children open, `?` and approximate when the names ran out.
    ///
    /// # Specification
    /// - requires: the open count is the join's own, its children's binders
    ///   closed, so position `open + offset` names the binder.
    /// - ensures: the name the binder took when it opened ([`Self::bind`]) is a
    ///   leaf, and a position no binder opened — the last label of a dependent
    ///   record — takes the first generated name no binder below it holds; a
    ///   binder that took none, or no generated name left, yields `?` and marks
    ///   the presentation approximate without adding a piece.
    /// - fails: the builder's refusal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested dependent arrows and static abstractions
    ///   observe the chosen binder and scope, and a split's two binders their
    ///   order. The binder cache witness covers counter exhaustion separately;
    ///   layout refusal at this exact join is outside the finite spelling
    ///   fixtures.
    /// - witness: `tests::goldens::long_dependent_function_type_breaks_at_the_narrow_page`
    /// - witness: `tests::goldens::static_operators_spell_as_the_grammar_writes_them`
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `tests::goldens::an_arrow_binder_spells_as_the_source_names_it`
    #[spec(
        captures: [entry = self.pieces.len(), fidelity = self.fidelity,
            unnamed = matches!(self.names.get(self.opened.len().saturating_add(offset.0)), Some(&None))],
        ensures: |ref ret| self.pieces.len() == entry
            && (fidelity != Fidelity::Approximate || self.fidelity == Fidelity::Approximate)
            && (!unnamed || self.fidelity == Fidelity::Approximate)
            && match *ret {
                | Ok(doc) => doc != Doc::EMPTY,
                | Err(PresentationError::Build(_)) => true,
                | Err(_) => false,
            },
    )]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            answer_totality,
            reason = "a binder the generated names ran out for has no name to write"
        )
    )]
    fn binder(
        &mut self,
        offset: OpenBinders,
    ) -> Result<Doc, PresentationError>
    {
        let position = self.opened.len().saturating_add(offset.0);
        let name = match self.names.get(position) {
            Some(&Some(ref name)) => Some(name.clone()),
            Some(&None) => None,
            None => self.fresh(offset),
        };
        if let Some(name) = name {
            self.leaf(Glyphs(name.0.as_str()))
        }
        else {
            self.fidelity = Fidelity::Approximate;
            let _fresh = self.unspelled.insert(Unspelled::Exhausted);
            self.leaf(Glyphs("?"))
        }
    }

    /// The generated name ([`Binders::name_at`]) of the binder `offset` past
    /// the innermost open binder: the first no binder below it holds, past
    /// one more for each binder between it and the last named one, which
    /// takes the earlier ones in order; none once the names ran out.
    ///
    /// # Specification
    /// trivial.
    fn fresh(
        &mut self,
        offset: OpenBinders,
    ) -> Option<BinderName>
    {
        let position = self.opened.len().saturating_add(offset.0);
        let outer = self
            .names
            .get(.. position.min(self.names.len()))
            .unwrap_or_default();
        let unnamed = position.saturating_sub(self.names.len());
        (0_usize ..)
            .map_while(|at| match self.binders.name_at(OpenBinders(at)) {
                Maybe::Present(name) => Some(name.clone()),
                Maybe::Absent(_) => None,
            })
            .filter(|name| !outer.iter().flatten().any(|held| held.0 == name.0))
            .nth(unnamed)
    }

    /// Open a binder in `zone`, named as the source writes it for `opener`
    /// where that name captures nothing, and by the first generated name no
    /// binder around it holds otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one binder more is open, in `zone`; its position takes the
    ///   name `opener`'s source writes ([`Source::arrow_binder`]) when it is a
    ///   name the walk's spelling writes, the term mentions nowhere else and no
    ///   open binder holds, else the first generated name
    ///   ([`Binders::name_at`]) no open binder holds, else none. With no
    ///   written names, the binder at position `p` takes the `p`-th generated
    ///   name, as it always did.
    /// - provides: the name each occurrence of the binder and its former's join
    ///   read.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declared type spells its parameters' names; a
    ///   written name a constant of the type holds, or an outer binder's, falls
    ///   back to a generated one; generated names skip a written name an outer
    ///   binder took; a primed name in ASCII falls back to a generated one.
    /// - witness: `tests::goldens::an_arrow_binder_spells_as_the_source_names_it`
    /// - witness: `tests::goldens::a_primed_name_has_no_ascii_spelling_782`
    #[spec(
        captures: [opened = self.opened.len()],
        ensures: self.opened.len() == opened.saturating_add(1_usize)
            && self.names.len() > opened,
    )]
    fn bind<S>(
        &mut self,
        source: &S,
        zone: Zone,
        opener: Option<S::Node>,
    ) where
        S: Source + ?Sized,
    {
        let position = self.opened.len();
        self.names.truncate(position);
        let outer = self.names.as_slice();
        let taken = |name: &str| outer.iter().flatten().any(|held| held.0 == name);
        let written = opener
            .and_then(|node| source.arrow_binder(node))
            .filter(|&name| {
                let text: &str = name.as_ref();
                unwritable(name, self.spelling).is_none()
                    && !self.binders.mentioned.contains(text)
                    && !taken(text)
            })
            .map(|name| BinderName(String::from(name.as_ref())));
        let name = written.or_else(|| self.fresh(OpenBinders(0)));
        self.names.resize(position, None);
        self.names.push(name);
        let _named = self.occurring.remove(&OpenBinders(position));
        self.opened.push(zone);
    }

    /// The name of the capability scope or hold whose region is `depth`,
    /// counted from the outermost: the regions the source's roots stand in
    /// first, then the ones the walk is inside.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the name the source writes for an ambient region, or the name
    ///   the walk gave the binder of a scope or hold it is inside; none for
    ///   depth zero, for a depth past every region open around the node, and
    ///   for a region whose binder took no name.
    /// - provides: the region a capability type's and a kept type's `at` names.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ambient scope, a scope the walk enters and a hold
    ///   it enters each name the region they open, counted on from the ambient
    ///   ones; a region past them goes unnamed.
    /// - witness: `tests::goldens::a_scoped_capability_names_its_scope_400`
    /// - witness: `tests::goldens::a_kept_value_names_the_scope_it_is_kept_in`
    /// - witness: `tests::goldens::a_kept_value_names_the_hold_it_is_kept_in`
    #[spec(ensures: |ret| u32::from(depth) != 0_u32 || ret.is_none())]
    fn region<S>(
        &self,
        source: &S,
        depth: RegionDepth,
    ) -> Option<BinderName>
    where
        S: Source + ?Sized,
    {
        let at = usize::try_from(u32::from(depth))
            .ok()?
            .checked_sub(1_usize)?;
        let ambient = source.regions();
        if let Some(named) = ambient.get(at) {
            return named.map(|name| BinderName(String::from(name.as_ref())));
        }
        let position = *self.scopes.get(at.checked_sub(ambient.len())?)?;
        self.names.get(position)?.clone()
    }

    /// `name` as a part's text, or `?` for a name a line or the walk's
    /// spelling cannot hold or the source does not answer, recorded as the
    /// reason it is unwritable or as `missing`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the name itself when it is non-empty, holds no line feed,
    ///   carriage return or tab and, in ASCII, no prime; `?` otherwise, the
    ///   presentation approximate and the reason recorded.
    /// - provides: every name a former spelled by parts writes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a handler's clause names and a data case's
    ///   constructors spell as written; an unnamed constructor spells `?`; a
    ///   primed constructor in ASCII spells `?`.
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `tests::goldens::a_primed_name_has_no_ascii_spelling_782`
    /// - witness: `walk::tests::unprintable_names_are_approximate_atoms`
    #[spec(ensures: |ref ret| !ret.0.contains(['\n', '\r', '\t']) && !ret.0.is_empty())]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            answer_totality,
            reason = "a name the source does not hold or a line or the spelling cannot hold has \
                      no spelling: the caller states which"
        )
    )]
    fn spelled(
        &mut self,
        name: Option<Name<'_>>,
        missing: Unspelled,
    ) -> Written
    {
        let reason = match name {
            Some(name) => match unwritable(name, self.spelling) {
                None => return Written(Cow::Owned(String::from(name.as_ref()))),
                Some(reason) => reason,
            },
            None => missing,
        };
        self.fidelity = Fidelity::Approximate;
        let _fresh = self.unspelled.insert(reason);
        Written(Cow::Borrowed("?"))
    }

    /// Pushes the parts `former`, a former spelled by parts, is written in,
    /// and answers the join that writes them.
    ///
    /// # Specification
    /// - requires: `former` is what `source` reads at `node`, a former
    ///   [`children`] answers child slots for at a position admitting `admits`.
    /// - ensures: one more parts list, whose pieces are the former's children
    ///   in reading order: `Path(A, x, y)`; a family or a constructor as its
    ///   name, applied to its components when it has any, a parameterised
    ///   constructor written against its family as [`children`] reads its
    ///   classifier; a primitive and an operation as a call of their name;
    ///   `transport(…)` over its motive — `\a. M`, or `+U M` for a telescope —
    ///   and operands; `v.l` and `v.i`; `case v { … }` with one arm per branch,
    ///   its pattern `+{.i = a}`, `#{a, b}` or a constructor's applied to its
    ///   field binders, `?` for a constructor the source cannot name; `handle {
    ///   c } with { pure(x) => r, oper op(p, k) => b }`, the scope's head
    ///   `handle c : I`; `c.op(v)`; `send(e, v)`, `recv(e)`, `select(e, l)`,
    ///   `offer(e) { l => c }`, `close(e)` and `fork (a : S) { t } as a ; u`,
    ///   each endpoint named by its binder. The forms the grammar does not
    ///   write — native transport, a fixpoint `rec f { c }`, a fold, `resume(k,
    ///   c)`, `reset { c }`, `shift k { c }`, a lazy product `&{c, …}` and its
    ///   observation `c.0` — make the presentation approximate.
    /// - provides: the spelling of every former without a join of its own.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the computation golden reads every computation
    ///   former, the type golden a path and a family, the value golden a
    ///   constructor; a swapped part or a lost binder changes the golden.
    /// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `tests::goldens::a_parameterised_constructor_is_written_against_its_family_where_source_reads_it`
    /// - witness: `tests::goldens::a_prelude_operator_is_written_as_its_operator`
    #[spec(
        captures: [forms = self.forms.len()],
        ensures: |ret| self.forms.len() == forms.saturating_add(1_usize)
            && matches!(ret, Join::Form { pieces: Arity(count), .. }
                if self.forms.last().is_some_and(|parts| parts.iter().filter(|part| matches!(**part, Part::Piece(_))).count() == count)),
    )]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            answer_totality,
            reason = "a label, a name or an operation the source does not answer, a malformed \
                      source, has no spelling: `spelled` writes `?` under the reason each call \
                      names; a former the grammar has no syntax for is written in the printer's \
                      notation, under that reason"
        )
    )]
    fn form<S>(
        &mut self,
        source: &S,
        node: S::Node,
        former: &Former<'_, S::Node>,
        admits: Admits,
    ) -> Join
    where
        S: Source + ?Sized,
    {
        let mut parts = Parts::default();
        let clauses = |walk: &mut Self, parts: &mut Parts, count: crate::former::Arity| {
            let _ = parts
                .text(" with {")
                .part(Part::Open)
                .text("pure(")
                .part(Part::Binder(0_usize))
                .text(") => ")
                .piece(Binding::Arrow);
            for index in 0_usize .. usize::from(count) {
                let label = source.label(node, Component::from(index));
                let name = walk.spelled(label, Unspelled::Missing);
                let _ = parts
                    .text(",")
                    .part(Part::Line)
                    .text("oper ")
                    .text(name)
                    .text("(")
                    .part(Part::Binder(0_usize))
                    .text(", ")
                    .part(Part::Binder(1_usize))
                    .text(") => ")
                    .piece(Binding::Arrow);
            }
            let _ = parts.part(Part::Close);
        };
        let binding = match *former {
            Former::Path { .. } => {
                let _ = parts.text("Path").arguments(Arity(3_usize));
                writes(Production("path_type"), Binding::Atom)
            },
            Former::Flow { .. } => {
                let _ = parts.text("Flow").arguments(Arity(3_usize));
                writes(Production("type_application"), Binding::Atom)
            },
            Former::Relation { relation, .. } => {
                let spelled = relation_spelled(relation);
                match (self.spelling, spelled.ascii) {
                    (grammar::Spelling::Ascii, grammar::Ascii::Head(head)) => {
                        let _ = parts.text(head.0).arguments(Arity(2_usize));
                        writes(Production("type_application"), Binding::Atom)
                    },
                    (grammar::Spelling::Unicode, _)
                    | (grammar::Spelling::Ascii, grammar::Ascii::Token(_)) => {
                        let _ = parts
                            .piece(Binding::Lazy)
                            .text(" ")
                            .text(spelled.written(self.spelling).0)
                            .part(Part::Space)
                            .piece(Binding::Relation);
                        Binding::Relation
                    },
                }
            },
            Former::Recorded { moves, .. } => {
                let _ = parts.text("recorded(");
                for (index, step) in moves.moves().into_iter().enumerate() {
                    if index > 0_usize {
                        let _ = parts.text(",").part(Part::Space);
                    }
                    let _ = match step.action {
                        ActionKind::Send => parts.text("sent(").piece(Binding::Sequence).text(")"),
                        ActionKind::Receive => {
                            parts.text("received(").piece(Binding::Sequence).text(")")
                        },
                        ActionKind::Select => {
                            let label = self.spelled(step.label, Unspelled::Missing);
                            parts.text("selected(").text(label).text(")")
                        },
                        ActionKind::Offer => {
                            let label = self.spelled(step.label, Unspelled::Missing);
                            parts.text("offered(").text(label).text(")")
                        },
                        ActionKind::Close => parts.text("closed"),
                    };
                }
                let _ = parts.part(Part::Tight).text(")");
                writes(Production("call_expression"), Binding::Atom)
            },
            Former::Constructor {
                name,
                placement: Placement::Consed,
                ..
            } => {
                let name = self.spelled(name, Unspelled::Unreadable(Unreadable::Unnamed));
                let _ = parts
                    .text(name)
                    .text(" ")
                    .text(grammar::CONS.written(self.spelling).0)
                    .text(" ")
                    .piece(Binding::Cons);
                writes(Production("binary_expression.cons"), Binding::Cons)
            },
            Former::Data { name, arity } | Former::Codata { name, arity } => {
                let name = self.spelled(name, Unspelled::Unreadable(Unreadable::Unnamed));
                let _ = parts.text(name);
                if usize::from(arity) > 0_usize {
                    let _ = parts.arguments(Arity(usize::from(arity)));
                    writes(Production("type_application"), Binding::Atom)
                }
                else {
                    writes(Production("type_identifier"), Binding::Atom)
                }
            },
            Former::Constructor {
                name,
                arity,
                placement: Placement::Applied,
                classifier,
            } => {
                // Where the spelling is source a reader reads back, a
                // parameterised constructor is written against its family,
                // `(MkIx : Ix(3))`, which its lowering needs, unless its
                // position states its type.
                let annotated = classifier.is_some()
                    && self.bodies == Bodies::Spelled
                    && admits != Admits::Stated;
                let name = self.spelled(name, Unspelled::Unreadable(Unreadable::Unnamed));
                if annotated {
                    let _ = parts.text("(");
                }
                let _ = parts.text(name);
                if usize::from(arity) > 0_usize {
                    let _ = parts.arguments(Arity(usize::from(arity)));
                }
                if annotated {
                    let _ = parts.text(" : ").piece(Binding::Arrow).text(")");
                }
                let applied = if usize::from(arity) > 0_usize {
                    writes(Production("call_expression"), Binding::Atom)
                }
                else {
                    writes(Production("constructor.expression"), Binding::Atom)
                };
                if annotated {
                    writes(Production("parenthesized_expression"), applied)
                }
                else {
                    applied
                }
            },
            Former::Primitive { name, arity } => {
                // A primitive the surface writes as an operator is written so:
                // its call by name reads back as a call of the prelude
                // constant, not as the primitive itself.
                let operator = gandr_core_term::primitive::PRELUDE
                    .iter()
                    .find(|primitive| <&'static str>::from(primitive.name()) == name.as_ref())
                    .map(|primitive| primitive.operator());
                match (operator, usize::from(arity)) {
                    (Some(gandr_core_term::primitive::Operator::Infix(spelling)), 2_usize) => {
                        let _ = parts
                            .piece(Binding::Atom)
                            .text(format!(" {spelling} "))
                            .piece(Binding::Atom);
                        match spelling {
                            "+" => writes(Production("binary_expression.add.plus"), Binding::Cons),
                            "-" => writes(Production("binary_expression.add.minus"), Binding::Cons),
                            "*" => writes(Production("binary_expression.mul.times"), Binding::Cons),
                            "==" => writes(Production("binary_expression.cmp.eq"), Binding::Cons),
                            "!=" => writes(Production("binary_expression.cmp.ne"), Binding::Cons),
                            "<" => writes(Production("binary_expression.cmp.lt"), Binding::Cons),
                            "<=" => writes(Production("binary_expression.cmp.le"), Binding::Cons),
                            ">" => writes(Production("binary_expression.cmp.gt"), Binding::Cons),
                            ">=" => writes(Production("binary_expression.cmp.ge"), Binding::Cons),
                            "&&" => writes(Production("binary_expression.and"), Binding::Cons),
                            "||" => writes(Production("binary_expression.or"), Binding::Cons),
                            // The prelude's other infix spellings, should it
                            // gain one, name their rule here.
                            _ => Binding::Cons,
                        }
                    },
                    (Some(gandr_core_term::primitive::Operator::Prefix(spelling)), 1_usize) => {
                        // A literal operand is parenthesized: `-(-1)`, never
                        // `--1`.
                        let literal = source
                            .component(node, Component::from(0_usize))
                            .is_some_and(|operand| {
                                matches!(source.read(operand), Former::Literal(_))
                            });
                        let _ = parts.text(spelling).piece(if literal {
                            Binding::Qualified
                        }
                        else {
                            Binding::Atom
                        });
                        writes(Production("unary_expression"), Binding::Prefix)
                    },
                    (
                        Some(
                            gandr_core_term::primitive::Operator::Infix(_)
                            | gandr_core_term::primitive::Operator::Prefix(_)
                            | gandr_core_term::primitive::Operator::Named,
                        )
                        | None,
                        _,
                    ) => {
                        let name =
                            self.spelled(Some(Name::from(name.as_ref())), Unspelled::Missing);
                        let _ = parts.text(name).arguments(Arity(usize::from(arity)));
                        writes(Production("call_expression"), Binding::Atom)
                    },
                }
            },
            Former::Perform { operation, .. } => {
                let name = self.spelled(Some(operation), Unspelled::Missing);
                let _ = parts.text(name).arguments(Arity(1_usize));
                writes(Production("call_expression"), Binding::Atom)
            },
            Former::Transport(..) => {
                self.note(Unspelled::Notation(Notation::Transport));
                let _ = parts.text("transport").arguments(Arity(2_usize));
                writes(Production("call_expression"), Binding::Atom)
            },
            Former::Resume(..) => {
                self.note(Unspelled::Notation(Notation::Resume));
                let _ = parts.text("resume").arguments(Arity(2_usize));
                writes(Production("resume_expression"), Binding::Atom)
            },
            Former::PathTransport { .. } | Former::Ride { .. } => {
                let lead = if matches!(*former, Former::Ride { .. }) {
                    "ride(\\"
                }
                else {
                    "transport(\\"
                };
                let _ = parts
                    .text(lead)
                    .part(Part::Binder(0_usize))
                    .text(".")
                    .part(Part::Space)
                    .piece(Binding::Arrow)
                    .rest(Arity(2_usize));
                writes(Production("call_expression"), Binding::Atom)
            },
            Former::TelescopeTransport { .. } => {
                let _ = parts
                    .text("transport(+U ")
                    .piece(Binding::Atom)
                    .rest(Arity(4_usize));
                writes(Production("call_expression"), Binding::Atom)
            },
            Former::Fixpoint(_) => {
                self.note(Unspelled::Notation(Notation::Fixpoint));
                let _ = parts
                    .text("rec ")
                    .part(Part::Binder(0_usize))
                    .text(" {")
                    .body();
                Binding::Prefix
            },
            Former::Reset(_) => {
                self.note(Unspelled::Notation(Notation::Reset));
                let _ = parts.text("reset {").body();
                Binding::Prefix
            },
            Former::Shift(_) => {
                self.note(Unspelled::Notation(Notation::Shift));
                let _ = parts
                    .text("shift ")
                    .part(Part::Binder(0_usize))
                    .text(" {")
                    .body();
                Binding::Prefix
            },
            Former::Case { arity, .. } => {
                let _ = parts
                    .text("case ")
                    .piece(Binding::Prefix)
                    .text(" {")
                    .part(Part::Open);
                for index in 0_usize .. usize::from(arity) {
                    let _ = parts
                        .separated(Component::from(index))
                        .text(format!("+{{.{index} = "))
                        .part(Part::Binder(0_usize))
                        .text("} => ")
                        .piece(Binding::Arrow);
                }
                let _ = parts.part(Part::Close);
                writes(
                    Production("case_expression"),
                    writes(
                        Production("labelled_sum_pattern"),
                        writes(Production("identifier.pattern"), Binding::Prefix),
                    ),
                )
            },
            Former::Split { arity, .. } => {
                let _ = parts
                    .text("case ")
                    .piece(Binding::Prefix)
                    .text(" {")
                    .part(Part::Open);
                let pattern = if usize::from(arity) == 0_usize {
                    let _ = parts.text("unit");
                    writes(Production("unit.pattern"), Binding::Prefix)
                }
                else {
                    let _ = parts
                        .text("#{")
                        .binders(Arity(usize::from(arity)))
                        .text("}");
                    writes(
                        Production("telescope_pattern"),
                        writes(Production("identifier.pattern"), Binding::Prefix),
                    )
                };
                let _ = parts.text(" => ").piece(Binding::Arrow).part(Part::Close);
                writes(Production("case_expression"), pattern)
            },
            Former::DataCase { motive, arity, .. } => {
                let _ = parts.text("case ").piece(Binding::Prefix);
                if case_motive(source, motive, admits) == Motive::Written {
                    let _ = parts.text(" -> ").piece(Binding::Prefix);
                }
                let _ = parts.text(" {").part(Part::Open);
                for index in 0_usize .. usize::from(arity) {
                    let arm = arm(source, node, Component::from(index));
                    let name = self.spelled(arm.name, Unspelled::Unreadable(Unreadable::Unnamed));
                    let _ = parts.separated(Component::from(index)).text(name);
                    if arm.placement == Placement::Consed {
                        let _ = parts
                            .text(" ")
                            .text(grammar::CONS.written(self.spelling).0)
                            .text(" ")
                            .binders(Arity(arm.fields));
                    }
                    else if arm.fields > 0_usize {
                        let _ = parts.text("(").binders(Arity(arm.fields)).text(")");
                    }
                    let _ = parts.text(" => ").piece(Binding::Arrow);
                }
                let _ = parts.part(Part::Close);
                // An arm's pattern is its constructor, applied to its field
                // binders when it has fields, or a letter of a word before
                // the rest of the word.
                writes(
                    Production("case_expression"),
                    writes(
                        Production("constructor_pattern"),
                        writes(Production("cons_pattern"), Binding::Prefix),
                    ),
                )
            },
            Former::RecordProjection(_, label) => {
                let label = self.spelled(Some(label), Unspelled::Missing);
                let _ = parts.piece(Binding::Atom).text(".").text(label);
                writes(Production("projection_expression"), Binding::Atom)
            },
            Former::TupleProjection(target, index) => {
                // A positional projection off another is parenthesized,
                // `(p.1).0`: unparenthesized, `1.0` would read as a number.
                let loosest = if matches!(source.read(target), Former::TupleProjection(..)) {
                    Binding::Qualified
                }
                else {
                    Binding::Atom
                };
                let _ = parts
                    .piece(loosest)
                    .text(format!(".{}", usize::from(index)));
                writes(Production("projection_expression"), Binding::Atom)
            },
            Former::Project(side, _) => {
                self.note(Unspelled::Notation(Notation::Projection));
                let _ = parts
                    .piece(Binding::Atom)
                    .text(format!(".{}", usize::from(side)));
                writes(Production("projection_expression"), Binding::Atom)
            },
            Former::ListFold { .. } => {
                self.note(Unspelled::Notation(Notation::ListFold));
                let _ = parts
                    .text("fold ")
                    .piece(Binding::Prefix)
                    .text(" {")
                    .part(Part::Open)
                    .text("nil => ")
                    .piece(Binding::Arrow)
                    .text(",")
                    .part(Part::Line)
                    .text("cons(")
                    .binders(Arity(2_usize))
                    .text(") => ")
                    .piece(Binding::Arrow)
                    .part(Part::Close);
                Binding::Prefix
            },
            Former::ListCase { .. } => {
                self.note(Unspelled::Notation(Notation::ListCase));
                let _ = parts
                    .text("case ")
                    .piece(Binding::Prefix)
                    .text(" {")
                    .part(Part::Open)
                    .text("nil => ")
                    .piece(Binding::Arrow)
                    .text(",")
                    .part(Part::Line)
                    .text("cons(")
                    .binders(Arity(2_usize))
                    .text(") => ")
                    .piece(Binding::Arrow)
                    .part(Part::Close);
                Binding::Prefix
            },
            Former::Handle { clauses: count, .. } => {
                let _ = parts.text("handle {").body();
                clauses(self, &mut parts, count);
                writes(Production("handle_expression"), Binding::Prefix)
            },
            Former::Scope {
                interface,
                clauses: count,
                ..
            } => {
                let interface = self.spelled(Some(interface), Unspelled::Missing);
                let _ = parts
                    .text("handle ")
                    .part(Part::Binder(0_usize))
                    .text(" : ")
                    .text(interface)
                    .text(" {")
                    .body();
                clauses(self, &mut parts, count);
                writes(Production("handle_expression"), Binding::Prefix)
            },
            Former::Exercise { operation, .. } => {
                let operation = self.spelled(Some(operation), Unspelled::Missing);
                let _ = parts
                    .piece(Binding::Atom)
                    .text(".")
                    .text(operation)
                    .arguments(Arity(1_usize));
                writes(
                    Production("projection_expression"),
                    writes(Production("call_expression"), Binding::Atom),
                )
            },
            // A lazy product is the positional copattern block, which the
            // lowering reads back as the lazy product of its clauses.
            Former::Lazy(arity) => {
                let _ = parts.text("&{");
                for index in 0_usize .. usize::from(arity) {
                    if index > 0_usize {
                        let _ = parts.text(",").part(Part::Space);
                    }
                    let _ = parts
                        .text(alloc::format!(".{index} => "))
                        .piece(Binding::Arrow);
                }
                let _ = parts.part(Part::Tight).text("}");
                writes(Production("lazy_record_expression"), Binding::Atom)
            },
            // A flow composite is written infix, as the surface writes it and
            // the lowering reads it back where a flow is answered (#631); so
            // is a path composite the sugared form reads off its transport
            // (#754).
            Former::Then(..) => {
                let _ = parts
                    .piece(Binding::Atom)
                    .text(" then ")
                    .piece(Binding::Atom);
                writes(Production("binary_expression.then"), Binding::Cons)
            },
            Former::Send { endpoint, .. } => {
                let _ = parts
                    .text("send(")
                    .part(Part::Endpoint(endpoint))
                    .rest(Arity(1_usize));
                writes(Production("send_expression"), Binding::Atom)
            },
            Former::Close(endpoint) => {
                let _ = parts
                    .text("close(")
                    .part(Part::Endpoint(endpoint))
                    .text(")");
                writes(Production("close_expression"), Binding::Atom)
            },
            Former::Select { endpoint, label } => {
                let label = self.spelled(Some(label), Unspelled::Missing);
                let _ = parts
                    .text("select(")
                    .part(Part::Endpoint(endpoint))
                    .text(", ")
                    .text(label)
                    .text(")");
                writes(Production("select_expression"), Binding::Atom)
            },
            Former::Offer { endpoint, arms } => {
                let _ = parts
                    .text("offer(")
                    .part(Part::Endpoint(endpoint))
                    .text(") {")
                    .part(Part::Open);
                for index in 0_usize .. usize::from(arms) {
                    let label = source.label(node, Component::from(index));
                    let name = self.spelled(label, Unspelled::Missing);
                    let _ = parts
                        .separated(Component::from(index))
                        .text(name)
                        .text(" => ")
                        .piece(Binding::Arrow);
                }
                let _ = parts.part(Part::Close);
                writes(Production("offer_expression"), Binding::Prefix)
            },
            Former::Fork { .. } => {
                let _ = parts
                    .text("fork (")
                    .part(Part::Binder(0_usize))
                    .text(" : ")
                    .piece(Binding::Arrow)
                    .text(") {")
                    .body()
                    .text(" as ")
                    .part(Part::Binder(0_usize))
                    .text(" ;")
                    .part(Part::Line)
                    .piece(Binding::Sequence);
                writes(Production("block"), Binding::Sequence)
            },
            Former::Hold { grade, .. } => {
                let _ = parts
                    .text(match grade {
                        gandr_core_term::memory::HoldGrade::Many => "hold ",
                        gandr_core_term::memory::HoldGrade::One => "hold[1] ",
                    })
                    .part(Part::Binder(0_usize))
                    .text(" = ")
                    .piece(Binding::Arrow)
                    .text(" ;")
                    .part(Part::Line)
                    .piece(Binding::Sequence);
                writes(Production("block"), Binding::Sequence)
            },
            Former::Receive { endpoint, .. } => {
                let _ = parts
                    .text("recv(")
                    .part(Part::Endpoint(endpoint))
                    .text(") as ")
                    .part(Part::Binder(0_usize))
                    .text(" ;")
                    .part(Part::Line)
                    .piece(Binding::Sequence);
                writes(Production("block"), Binding::Sequence)
            },
            Former::Access {
                held, place, mode, ..
            } => {
                let _ = parts.text(match mode {
                    AccessMode::Exclusive { .. } => "access ",
                    AccessMode::Shared => "access shared ",
                });
                let _ = parts.part(Part::Endpoint(held));
                if let gandr_core_term::memory::Place::At { .. } = place {
                    let _ = parts.text("[").piece(Binding::Arrow).text("]");
                }
                let _ = parts
                    .text(" as ")
                    .part(Part::Binder(0_usize))
                    .text(" {")
                    .body();
                if let AccessMode::Exclusive { .. } = mode {
                    let _ = parts.text(" unwind {").body();
                }
                writes(Production("access_expression"), Binding::Prefix)
            },
            Former::ResumeView { view, .. } => {
                let _ = parts
                    .text("resume(")
                    .part(Part::Endpoint(view))
                    .rest(Arity(1_usize));
                writes(Production("resume_expression"), Binding::Atom)
            },
            Former::AbortView(view) => {
                let _ = parts.text("abort(").part(Part::Endpoint(view)).text(")");
                writes(Production("abort_expression"), Binding::Atom)
            },
            // `A at w` binds as loosely as a word's cons, so a bridge over it
            // parenthesizes it and it parenthesizes any operand but an atom.
            Former::Located { world, .. } => {
                let world = self.spelled(world, Unspelled::Unreadable(Unreadable::Unnamed));
                let _ = parts.piece(Binding::Atom).text(" at ").text(world);
                writes(Production("at_type"), Binding::Cons)
            },
            // `A at c` names the capability scope whose region the value is
            // kept in, and binds as `A at w` does.
            Former::Kept { region, .. } => {
                let named = self.region(source, region);
                let scope = self.spelled(
                    named.as_ref().map(|name| Name::from(name.0.as_str())),
                    Unspelled::Elided(Elided::Region),
                );
                let _ = parts.piece(Binding::Atom).text(" at ").text(scope);
                writes(Production("at_type"), Binding::Cons)
            },
            Former::WorldHold(_) => {
                // Parenthesized, as the surface writes it: bare at a block's
                // head, `hold` opens a hold statement, `hold x = v ; …`.
                let _ = parts.text("(hold ").piece(Binding::Prefix).text(")");
                writes(
                    Production("parenthesized_expression"),
                    writes(Production("hold_expression"), Binding::Atom),
                )
            },
            Former::Leta { .. } => {
                let _ = parts
                    .text("leta ")
                    .part(Part::Binder(0_usize))
                    .text(" = ")
                    .piece(Binding::Arrow)
                    .text(" ;")
                    .part(Part::Line)
                    .piece(Binding::Sequence);
                writes(Production("block"), Binding::Sequence)
            },
            Former::Migrate { world, .. } => {
                let world = self.spelled(world, Unspelled::Unreadable(Unreadable::Unnamed));
                let _ = parts.text("migrate [").text(world).text("] {").body();
                writes(Production("migrate_expression"), Binding::Prefix)
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "never reached: `visit` writes these formers itself, and only \
                              formers spelled by parts come here"
                )
            )]
            Former::Reify
            | Former::Stack(..)
            | Former::With(..)
            | Former::Ascription { .. }
            | Former::ListNil
            | Former::ListCons(..)
            | Former::PathUniverse(..)
            | Former::PathRefl(_)
            | Former::PathEquiv(..)
            | Former::PathProduct(..)
            | Former::BaseType(_)
            | Former::Product(_)
            | Former::Sum(_)
            | Former::RecordType(_)
            | Former::ThunkType(_)
            | Former::Universe { .. }
            | Former::Element(_)
            | Former::Abstract(_)
            | Former::StaticPi { .. }
            | Former::Sigma { .. }
            | Former::Capability { .. }
            | Former::Session { .. }
            | Former::Returner(_)
            | Former::EffectfulReturner { .. }
            | Former::Arrow { .. }
            | Former::Pi { .. }
            | Former::ComputationElement(_)
            | Former::List(_)
            | Former::Variable { .. }
            | Former::Constant(_)
            | Former::Unit
            | Former::Literal(_)
            | Former::Tuple(_)
            | Former::Record(_)
            | Former::Injection(..)
            | Former::Thunk(_)
            | Former::Quote(_)
            | Former::QuoteComputation(_)
            | Former::StaticLambda(_)
            | Former::StaticApplication(..)
            | Former::Here(_)
            | Former::Funext(..)
            | Former::Equiv(..)
            | Former::Univalence(_)
            | Former::SessionRelated(..)
            | Former::Stay(_)
            | Former::Back(_)
            | Former::Cong(..)
            | Former::FlowProduct(..)
            | Former::Forward(_)
            | Former::FunctionFlow(..)
            | Former::RunType(_)
            | Former::Return(_)
            | Former::Bind(..)
            | Former::Force(_)
            | Former::Application(..)
            | Former::Lambda(_)
            | Former::Nested(_)
            | Former::Run(_)
            | Former::Ua { .. }
            | Former::Returned(_)
            | Former::Unreadable(_) => {
                self.fidelity = Fidelity::Approximate;
                let _fresh = self.unspelled.insert(Unspelled::Misplaced);
                let _ = parts.text("?");
                Binding::Atom
            },
        };
        let pieces = Arity(parts.pieces);
        self.forms.push(parts.parts);
        Join::Form { pieces, binding }
    }

    /// Combines the finished pieces a join takes into one.
    ///
    /// # Specification
    /// - requires: available operands are the top finished pieces in operand
    ///   order, last on top; application arity comes from a bounded spine.
    /// - ensures: `+U C`, `-F A`, `pure v`, `force v` and `run c` with the
    ///   operand parenthesized unless it is an atom; `#{…}`, `+{…}` and `&{…}`
    ///   around their entries, each bare and after its label when it has one;
    ///   `A -> C` with the domain bare up to a bridge and the codomain bare, a
    ///   break after the arrow; `(x : A) -> C` naming the binder by the binders
    ///   open outside it, a break after the arrow; `#{x : A, y : B}` naming its
    ///   first label so and its second by the next name, a break after the
    ///   comma; `\a. v` naming its binder so, a break after the dot; `f(a1, …,
    ///   an)` with the operator parenthesized unless it is an atom, a block
    ///   when it is a bind; every list with a break after each comma and before
    ///   the closer; `run x <- c ; rest` naming its binder so, the bound
    ///   computation a block when it is itself a bind, a soft line after the
    ///   semicolon; `fn (x) { c }` naming its binder so and `thunk { c }`, each
    ///   a block.
    /// - provides: every composite spelling.
    /// - fails: a missing operand, which the walk's scheduling excludes, or the
    ///   builder's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`PresentationError::Unbalanced`] for a missing operand and
    /// [`PresentationError::Build`] when the builder refuses.
    ///
    /// # Termination
    /// An application's loops run once per argument its arity counts.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite narrow and wide grammar fixtures distinguish
    ///   wrong operators, parentheses, child order and binder scopes. An
    ///   incomplete join exposes missing-operand refusal; arbitrary trees and
    ///   every builder limit are not enumerated.
    /// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `tests::goldens::static_operators_spell_as_the_grammar_writes_them`
    /// - witness: `tests::goldens::pair_of_injections_pins_sum_notation`
    /// - witness: `tests::goldens::records_spell_their_fields_in_label_order`
    /// - witness: `tests::goldens::long_dependent_function_type_breaks_at_the_narrow_page`
    /// - witness: `walk::tests::missing_operands_are_unbalanced_not_layout_failures`
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `tests::goldens::a_dependent_arrow_ignoring_its_binder_spells_as_the_arrow_398`
    /// - witness: `tests::goldens::a_dependent_pair_ignoring_its_binder_spells_as_the_product_771`
    #[spec(
        captures: [entry = self.pieces.len(), taken = match join {
            Join::Prefix(_) | Join::EffectReturner(_) | Join::StaticLambda | Join::Lambda | Join::Thunk
                | Join::Bracket(Bracket::PathRefl | Bracket::Here | Bracket::Univalence | Bracket::List | Bracket::Stay | Bracket::Back | Bracket::Forward | Bracket::Run | Bracket::TypeQuote) => Some(1_usize),
            Join::Braced { arity: Arity(count), entries: Entries::Positional, .. } | Join::Session { payloads: Arity(count), .. }
                | Join::Form { pieces: Arity(count), .. } | Join::Infix { arity: Arity(count), .. } | Join::Tuple(Arity(count)) => Some(count),
            Join::ValueFunction(Arity(domains), _) => domains.checked_add(1_usize),
            Join::Braced { arity: Arity(count), entries: Entries::Labelled(_), .. } => count.checked_mul(2_usize),
            Join::Arrow | Join::Pi | Join::Sigma | Join::Sequence | Join::Ua(_) | Join::Bracket(Bracket::Stack | Bracket::ListCons | Bracket::PathUniverse | Bracket::PathEquiv | Bracket::PathProduct | Bracket::Funext | Bracket::Equiv | Bracket::Bisim | Bracket::Sim | Bracket::FlowProduct | Bracket::Cong | Bracket::Arrow) => Some(2_usize),
            Join::TypedSequence => Some(3_usize),
            Join::Apply(Arity(arguments)) => arguments.checked_add(1_usize),
        }],
        ensures: |ref ret| match *ret {
            | Ok(()) => taken.and_then(|count| entry.checked_sub(count)).and_then(|rest| rest.checked_add(1_usize)) == Some(self.pieces.len())
                && self.pieces.last().is_some_and(|piece| piece.binding == match join {
                    Join::Prefix(_) | Join::EffectReturner(_) | Join::Lambda | Join::Thunk => Binding::Prefix,
                    Join::Arrow | Join::Pi | Join::StaticLambda | Join::ValueFunction(..) => Binding::Arrow,
                    // A dependent pair naming no binder is the product it
                    // reads as.
                    Join::Sigma if piece.binding == Binding::Product => Binding::Product,
                    Join::Sequence | Join::TypedSequence => Binding::Sequence,
                    Join::Infix { infix, .. } => infix.binding(),
                    Join::Apply(_) | Join::Bracket(_) | Join::Braced { .. } | Join::Sigma | Join::Ua(_) | Join::Tuple(_) => Binding::Atom,
                    Join::Session { binding, .. } | Join::Form { binding, .. } => binding,
                }),
            | Err(PresentationError::Build(_) | PresentationError::Unbalanced) => self.pieces.len() <= entry,
            | Err(PresentationError::Render(_)) => false,
        },
    )]
    fn join(
        &mut self,
        join: Join,
    ) -> Result<(), PresentationError>
    {
        let (doc, binding) = match join {
            Join::EffectReturner(head) => {
                let operand = self.pop()?;
                let operand = self.bare_up_to(operand, Binding::Atom)?;
                (self.builder.concat(head, operand)?, Binding::Prefix)
            },
            Join::Session {
                payloads: Arity(count),
                binding,
            } => {
                let mut popped = Vec::with_capacity(count);
                for _ in 0_usize .. count {
                    popped.push(self.pop()?);
                }
                let mut payloads = Vec::with_capacity(count);
                for piece in popped.into_iter().rev() {
                    payloads.push(if piece.binding == Binding::Qualified {
                        self.parenthesized(piece.doc)?
                    }
                    else {
                        self.bare_up_to(piece, Binding::Atom)?
                    });
                }
                let template = self.protocols.pop().ok_or(PresentationError::Unbalanced)?;
                let mut items = Vec::with_capacity(template.len());
                for segment in &template {
                    items.push(match *segment {
                        Segment::Text(ref text) => self.leaf(Glyphs(text))?,
                        Segment::Payload(slot) => payloads
                            .get(usize::from(slot))
                            .copied()
                            .ok_or(PresentationError::Unbalanced)?,
                    });
                }
                (self.builder.concat_all(&items)?, binding)
            },
            Join::Prefix(prefix) => {
                let operand = self.pop()?;
                let operand = self.bare_up_to(operand, Binding::Atom)?;
                let head = self.leaf(match prefix {
                    Prefix::Thunk => Glyphs("+U "),
                    Prefix::Returner => Glyphs("-F "),
                    Prefix::Pure => Glyphs("pure "),
                    Prefix::Force => Glyphs("force "),
                    Prefix::Run => Glyphs("run "),
                })?;
                (self.builder.concat(head, operand)?, Binding::Prefix)
            },
            Join::Braced {
                brace,
                arity: Arity(count),
                entries,
            } => {
                let per_entry = match entries {
                    Entries::Positional => 1_usize,
                    Entries::Labelled(_) => 2_usize,
                };
                let taken = count
                    .checked_mul(per_entry)
                    .ok_or(PresentationError::Unbalanced)?;
                let mut popped = Vec::with_capacity(taken);
                for _ in 0_usize .. taken {
                    popped.push(self.pop()?);
                }
                let opener = self.leaf(brace.opener())?;
                let mut items = Vec::from([opener]);
                for (position, entry) in popped.rchunks(per_entry).enumerate() {
                    if position > 0_usize {
                        let comma = self.leaf(Glyphs(","))?;
                        items.push(self.space_or_break(comma)?);
                    }
                    items.extend(entry.iter().rev().map(|piece| piece.doc));
                }
                let inner = self.builder.concat_all(&items)?;
                let inner = self.none_or_break(inner)?;
                let close = self.leaf(Glyphs("}"))?;
                (self.builder.concat(inner, close)?, Binding::Atom)
            },
            Join::Infix { infix, arity } => {
                let mut joined = None;
                for operand in self.take(arity)? {
                    let operand = self.bare_up_to(operand, infix.operand())?;
                    joined = Some(match joined {
                        None => operand,
                        Some(head) => {
                            let symbol = self.leaf(infix.symbol())?;
                            let head = self.builder.concat(head, symbol)?;
                            let head = self.space_or_break(head)?;
                            self.builder.concat(head, operand)?
                        },
                    });
                }
                (
                    joined.ok_or(PresentationError::Unbalanced)?,
                    infix.binding(),
                )
            },
            Join::Tuple(arity) => {
                let components = self.take(arity)?;
                (self.listed(&components)?, Binding::Atom)
            },
            Join::ValueFunction(arity, dependent) => {
                let codomain = self.pop()?;
                let domains = self.take(arity)?;
                let open = self.opened.len();
                let binders = usize::try_from(dependent.0.count_ones())
                    .ok()
                    .ok_or(PresentationError::Unbalanced)?;
                let named = (open .. open.saturating_add(binders))
                    .any(|position| self.occurring.contains(&OpenBinders(position)));
                if binders > 0_usize && (named || self.fidelity != Fidelity::Faithful) {
                    self.dependent_alias(&domains, dependent, codomain)?
                }
                else {
                    let domain = match *domains.as_slice() {
                        [] => self.leaf(Glyphs("()"))?,
                        [only] => self.bare_up_to(only, Binding::Lazy)?,
                        _ => self.listed(&domains)?,
                    };
                    let arrow = self.leaf(Glyphs(" =>"))?;
                    let head = self.builder.concat(domain, arrow)?;
                    let head = self.space_or_break(head)?;
                    (self.builder.concat(head, codomain.doc)?, Binding::Arrow)
                }
            },
            Join::Arrow => {
                let codomain = self.pop()?;
                let domain = self.pop()?;
                let domain = self.bare_up_to(domain, Binding::Lazy)?;
                let arrow = self.leaf(Glyphs(" ->"))?;
                let head = self.builder.concat(domain, arrow)?;
                let head = self.space_or_break(head)?;
                (self.builder.concat(head, codomain.doc)?, Binding::Arrow)
            },
            // The surface reads `(x : A) -> C` as the plain arrow where `C`
            // does not name `x`, so a dependent arrow whose codomain names
            // no binder — a decode substituting a constant family — has no
            // spelling of its own and is written as the arrow it reads as.
            // A walk that spelled every node so far met every occurrence.
            Join::Pi
                if self.fidelity == Fidelity::Faithful
                    && !self.occurring.contains(&OpenBinders(self.opened.len())) =>
            {
                let codomain = self.pop()?;
                let domain = self.pop()?;
                let domain = self.bare_up_to(domain, Binding::Lazy)?;
                let arrow = self.leaf(Glyphs(" ->"))?;
                let head = self.builder.concat(domain, arrow)?;
                let head = self.space_or_break(head)?;
                (self.builder.concat(head, codomain.doc)?, Binding::Arrow)
            },
            Join::Pi => {
                let codomain = self.pop()?;
                let domain = self.pop()?;
                let binder = self.binder(OpenBinders(0_usize))?;
                let open = self.leaf(Glyphs("("))?;
                let colon = self.leaf(Glyphs(" : "))?;
                let arrow = self.leaf(Glyphs(") ->"))?;
                let head = self
                    .builder
                    .concat_all(&[open, binder, colon, domain.doc, arrow])?;
                let head = self.space_or_break(head)?;
                (self.builder.concat(head, codomain.doc)?, Binding::Arrow)
            },
            // The surface reads a record whose later field names no earlier
            // one as a record of labels, not as a pair, so a dependent pair
            // whose second factor names no binder — a decode the family
            // reduces away (#771) — is written as the product it reads as:
            // `A * B` sugared, each operand tighter than the chain, and
            // `#{A, B}` explicit.
            Join::Sigma
                if self.fidelity == Fidelity::Faithful
                    && !self.occurring.contains(&OpenBinders(self.opened.len())) =>
            {
                let second = self.pop()?;
                let first = self.pop()?;
                if self.form == Form::Sugared {
                    let first = self.bare_up_to(first, Binding::Prefix)?;
                    let second = self.bare_up_to(second, Binding::Prefix)?;
                    let symbol = self.leaf(Infix::Product.symbol())?;
                    let head = self.builder.concat(first, symbol)?;
                    let head = self.space_or_break(head)?;
                    (self.builder.concat(head, second)?, Binding::Product)
                }
                else {
                    let opener = self.leaf(Brace::Hash.opener())?;
                    let comma = self.leaf(Glyphs(","))?;
                    let comma = self.space_or_break(comma)?;
                    let inner = self
                        .builder
                        .concat_all(&[opener, first.doc, comma, second.doc])?;
                    let inner = self.none_or_break(inner)?;
                    let close = self.leaf(Glyphs("}"))?;
                    (self.builder.concat(inner, close)?, Binding::Atom)
                }
            },
            Join::Sigma => {
                let second = self.pop()?;
                let first = self.pop()?;
                let binder = self.binder(OpenBinders(0_usize))?;
                let label = self.binder(OpenBinders(1_usize))?;
                let open = self.leaf(Glyphs("#{"))?;
                let colon = self.leaf(Glyphs(" : "))?;
                let comma = self.leaf(Glyphs(","))?;
                let head = self
                    .builder
                    .concat_all(&[open, binder, colon, first.doc, comma])?;
                let head = self.space_or_break(head)?;
                let colon = self.leaf(Glyphs(" : "))?;
                let inner = self.builder.concat_all(&[head, label, colon, second.doc])?;
                let inner = self.none_or_break(inner)?;
                let close = self.leaf(Glyphs("}"))?;
                (self.builder.concat(inner, close)?, Binding::Atom)
            },
            Join::StaticLambda => {
                let body = self.pop()?;
                let binder = self.binder(OpenBinders(0_usize))?;
                let lead = self.leaf(Glyphs("\\"))?;
                let dot = self.leaf(Glyphs("."))?;
                let head = self.builder.concat_all(&[lead, binder, dot])?;
                let head = self.space_or_break(head)?;
                (self.builder.concat(head, body.doc)?, Binding::Arrow)
            },
            Join::Sequence => {
                let rest = self.pop()?;
                let bound = self.pop()?;
                let bound = self.bare_or_block(bound, Binding::Arrow)?;
                let binder = self.binder(OpenBinders(0_usize))?;
                let run = self.leaf(Glyphs("run "))?;
                let arrow = self.leaf(Glyphs(" <- "))?;
                let semicolon = self.leaf(Glyphs(" ;"))?;
                let line = Doc::LINE;
                (
                    self.builder
                        .concat_all(&[run, binder, arrow, bound, semicolon, line, rest.doc])?,
                    Binding::Sequence,
                )
            },
            Join::TypedSequence => {
                let rest = self.pop()?;
                let result = self.pop()?;
                let bound = self.pop()?;
                let bound = self.bare_or_block(bound, Binding::Arrow)?;
                let binder = self.binder(OpenBinders(0_usize))?;
                let run = self.leaf(Glyphs("run "))?;
                let colon = self.leaf(Glyphs(" : "))?;
                let arrow = self.leaf(Glyphs(" <- "))?;
                let semicolon = self.leaf(Glyphs(" ;"))?;
                let line = Doc::LINE;
                (
                    self.builder.concat_all(&[
                        run, binder, colon, result.doc, arrow, bound, semicolon, line, rest.doc,
                    ])?,
                    Binding::Sequence,
                )
            },
            Join::Lambda => {
                let body = self.pop()?;
                let binder = self.binder(OpenBinders(0_usize))?;
                let open = self.leaf(Glyphs("fn ("))?;
                let close = self.leaf(Glyphs(") {"))?;
                let head = self.builder.concat_all(&[open, binder, close])?;
                (self.block(head, body.doc)?, Binding::Prefix)
            },
            Join::Thunk => {
                let body = self.pop()?;
                let head = self.leaf(Glyphs("thunk {"))?;
                (self.block(head, body.doc)?, Binding::Prefix)
            },
            Join::Apply(Arity(count)) => {
                let mut arguments = Vec::with_capacity(count);
                for _ in 0_usize .. count {
                    arguments.push(self.pop()?);
                }
                let operator = self.pop()?;
                let operator = self.bare_or_block(operator, Binding::Atom)?;
                let opener = self.leaf(Glyphs("("))?;
                let mut items = Vec::from([operator, opener]);
                for (position, argument) in arguments.iter().rev().enumerate() {
                    if position > 0_usize {
                        let comma = self.leaf(Glyphs(","))?;
                        items.push(self.space_or_break(comma)?);
                    }
                    items.push(argument.doc);
                }
                let inner = self.builder.concat_all(&items)?;
                let inner = self.none_or_break(inner)?;
                let close = self.leaf(Glyphs(")"))?;
                (self.builder.concat(inner, close)?, Binding::Atom)
            },
            Join::Bracket(bracket) => {
                let mut items = Vec::new();
                match bracket {
                    Bracket::PathUniverse
                    | Bracket::Stack
                    | Bracket::PathEquiv
                    | Bracket::PathProduct
                    | Bracket::Funext
                    | Bracket::Equiv
                    | Bracket::ListCons
                    | Bracket::Bisim
                    | Bracket::Sim
                    | Bracket::FlowProduct
                    | Bracket::Cong
                    | Bracket::Arrow => {
                        let second = self.pop()?;
                        let first = self.pop()?;
                        let opener = self.leaf(bracket.opener())?;
                        let comma = self.leaf(Glyphs(","))?;
                        let comma = self.space_or_break(comma)?;
                        items.extend([opener, first.doc, comma, second.doc]);
                    },
                    Bracket::Here
                    | Bracket::Univalence
                    | Bracket::PathRefl
                    | Bracket::List
                    | Bracket::Stay
                    | Bracket::Back
                    | Bracket::Forward
                    | Bracket::Run
                    | Bracket::TypeQuote => {
                        let body = self.pop()?;
                        let opener = self.leaf(bracket.opener())?;
                        items.extend([opener, body.doc]);
                    },
                }
                let inner = self.builder.concat_all(&items)?;
                let inner = self.none_or_break(inner)?;
                let close = self.leaf(Glyphs(")"))?;
                (self.builder.concat(inner, close)?, Binding::Atom)
            },
            Join::Ua(head) => {
                let backward = self.pop()?;
                let forward = self.pop()?;
                let head = self.space_or_break(head)?;
                let comma = self.leaf(Glyphs(","))?;
                let comma = self.space_or_break(comma)?;
                let inner = self
                    .builder
                    .concat_all(&[head, forward.doc, comma, backward.doc])?;
                let inner = self.none_or_break(inner)?;
                let close = self.leaf(Glyphs(")"))?;
                (self.builder.concat(inner, close)?, Binding::Atom)
            },
            Join::Form {
                pieces: Arity(count),
                binding,
            } => {
                let mut children = Vec::with_capacity(count);
                for _ in 0_usize .. count {
                    children.push(self.pop()?);
                }
                let parts = self.forms.pop().ok_or(PresentationError::Unbalanced)?;
                let mut current = Vec::new();
                let mut heads = Vec::new();
                for part in parts {
                    match part {
                        Part::Text(text) => current.push(self.leaf(Glyphs(text.as_ref()))?),
                        Part::Piece(loosest) => {
                            let piece = children.pop().ok_or(PresentationError::Unbalanced)?;
                            current.push(self.bare_or_block(piece, loosest)?);
                        },
                        Part::Binder(offset) => current.push(self.binder(OpenBinders(offset))?),
                        Part::Endpoint(index) => {
                            current.push(self.variable_leaf(Zone::Linear, index)?);
                        },
                        Part::Space => {
                            let head = self.builder.concat_all(&core::mem::take(&mut current))?;
                            current.push(self.space_or_break(head)?);
                        },
                        Part::Tight => {
                            let head = self.builder.concat_all(&core::mem::take(&mut current))?;
                            current.push(self.none_or_break(head)?);
                        },
                        Part::Line => current.push(Doc::LINE),
                        Part::Open => heads.push(core::mem::take(&mut current)),
                        Part::Close => {
                            let body = self.builder.concat_all(&core::mem::take(&mut current))?;
                            let head = heads.pop().ok_or(PresentationError::Unbalanced)?;
                            let head = self.builder.concat_all(&head)?;
                            current.push(self.block(head, body)?);
                        },
                    }
                }
                if !heads.is_empty() || !children.is_empty() {
                    return Err(PresentationError::Unbalanced);
                }
                (self.builder.concat_all(&current)?, binding)
            },
        };
        self.pieces.push(Piece { doc, binding });
        Ok(())
    }
}

/// The document of the node `root` of `source`, in a position admitting
/// `admits`, its thunks written as `bodies` says.
///
/// # Specification
/// - requires: `builder` is the builder the document is rendered from.
/// - ensures: the root's document and whether every node was spelled in full;
///   [`Walked::OverBudget`] when either pass exhausts its scheduled-visit
///   budget. A scan refusal builds nothing; a walk refusal may leave partial
///   documents in the builder when the source changes after the scan. A
///   computation's document is one group, so its statements break together.
/// - provides: the document [`crate::present_type`], [`crate::present_value`],
///   [`crate::present_definition`] and [`crate::present_computation`] lay out.
/// - fails: the builder's refusal, or bookkeeping the walk's scheduling
///   excludes.
/// - panics: none.
/// - intension: one scan and one walk, each on an explicit stack, never
///   recursion; linear in the nodes reached.
///
/// # Errors
/// Returns [`PresentationError::Build`] when the builder refuses and
/// [`PresentationError::Unbalanced`] when the walk ends with other than one
/// finished piece.
///
/// # Adequacy
/// - hypothesis: L3 — the finite golden fixtures expose wrong constructors,
///   breaks and depth cutoffs. A scanned leaf that becomes a cycle exposes a
///   missing second-pass budget through the read count and approximation. Other
///   mutations of a source during presentation are not enumerated.
/// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `tests::goldens::beyond_the_depth_limit_renders_deep`
/// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
/// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
#[spec(ensures: |ref ret| match *ret {
    | Ok(Walked::Built { doc, .. }) => doc != Doc::EMPTY,
    | Ok(Walked::OverBudget) | Err(PresentationError::Build(_) | PresentationError::Unbalanced) => true,
    | Err(PresentationError::Render(_)) => false,
})]
pub fn walk<S>(
    source: &S,
    root: S::Node,
    (admits, bodies): (Admits, Bodies),
    style: Style,
    builder: &mut dyn Compose,
) -> Result<Walked, PresentationError>
where
    S: Source + ?Sized,
{
    let Maybe::Present(mut mentioned) = mentioned(source, root, admits, bodies)
    else {
        return Ok(Walked::OverBudget);
    };
    let context = source.context();
    mentioned.extend(context.iter().flatten().copied());
    mentioned.extend(source.regions().iter().flatten().copied());
    let mut walk = Walk {
        builder,
        pieces: Vec::new(),
        binders: Binders::new(mentioned),
        names: Vec::new(),
        opened: Vec::new(),
        scopes: Vec::new(),
        occurring: BTreeSet::new(),
        held: Vec::new(),
        substituted: BTreeMap::new(),
        context,
        recursive: source.recursive(),
        fidelity: Fidelity::Faithful,
        unspelled: BTreeSet::new(),
        bodies,
        protocols: Vec::new(),
        forms: Vec::new(),
        form: style.form,
        spelling: style.spelling,
        remaining: VISIT_BUDGET,
        surface: match admits {
            Admits::Type | Admits::ValueType | Admits::CompType => Surface::Type,
            Admits::Value | Admits::Stated | Admits::Operand | Admits::Computation(_) => {
                Surface::Expression
            },
        },
    };
    let mut tasks = Vec::from([Task::Visit {
        node: root,
        admits,
        depth: ValueDepth::ROOT,
    }]);
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit {
                node,
                admits,
                depth,
            } => {
                let Some(left) = walk.remaining.checked_sub(1_u32)
                else {
                    return Ok(Walked::OverBudget);
                };
                walk.remaining = left;
                walk.visit(
                    source,
                    node,
                    reading(source, node, walk.form, admits),
                    admits,
                    depth,
                    &mut tasks,
                )?;
            },
            Task::Returned { node, depth } => {
                let Some(left) = walk.remaining.checked_sub(1_u32)
                else {
                    return Ok(Walked::OverBudget);
                };
                walk.remaining = left;
                Walk::returned(source, node, depth, &mut tasks);
            },
            Task::Bind(zone, opener) => walk.bind(source, zone, opener),
            Task::BindScope(zone, opener) => {
                walk.bind(source, zone, opener);
                walk.scopes.push(walk.opened.len().saturating_sub(1_usize));
            },
            Task::Unbind => {
                let _closed = walk.opened.pop();
                if walk
                    .scopes
                    .last()
                    .is_some_and(|&scope| scope >= walk.opened.len())
                {
                    let _left = walk.scopes.pop();
                }
                let _argument = walk.substituted.remove(&OpenBinders(walk.opened.len()));
            },
            Task::Hold => walk.held.push(core::mem::take(&mut walk.occurring)),
            Task::Substitute(arity) => walk.substitute(arity)?,
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a component the source does not answer: a malformed source, with no \
                              node to spell"
                )
            )]
            Task::Missing => walk.unspell(Unspelled::Missing)?,
            Task::Label(Labelled { of, index, label }) => walk.label(source, of, index, label)?,
            Task::Join(join) => walk.join(join)?,
            Task::Surface(surface) => walk.surface = surface,
        }
    }
    let root = walk.pop()?;
    if !walk.pieces.is_empty() {
        return Err(PresentationError::Unbalanced);
    }
    // A body's statements break together: on one line when the whole body
    // fits, one statement per line otherwise.
    let doc = match admits {
        Admits::Computation(_) => walk.builder.group(root.doc)?,
        Admits::Type
        | Admits::ValueType
        | Admits::CompType
        | Admits::Value
        | Admits::Stated
        | Admits::Operand => root.doc,
    };
    Ok(Walked::Built {
        doc,
        fidelity: walk.fidelity,
        unspelled: walk.unspelled,
    })
}

#[cfg(test)]
mod tests
{
    use core::cell::Cell;

    use anodized::spec;
    use gandr_surface_layout::units::PageWidth;

    use super::Component;
    use super::Fidelity;
    use super::Former;
    use super::Source;
    use super::VISIT_BUDGET;

    /// The root handle of a deliberately changing source.
    #[derive(Clone, Copy, Debug)]
    struct ChangingNode;

    /// A leaf during the scan and an alternating type cycle during the walk.
    #[repr(transparent)]
    struct ChangingSource
    {
        /// Reads already performed, including the initial naming scan.
        reads: Cell<u32>,
    }

    impl Source for ChangingSource
    {
        type Node = ChangingNode;

        /// Returns a finite changing source without hanging a failing witness.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: the read count advances once, saturating; the first read
        ///   is a unit type, later reads alternate the two type bridges until
        ///   the finite cutoff, after which the handle is unreadable.
        /// - provides: a between-pass change that invalidates the scan's bound.
        /// - fails: never.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the public presentation observes approximation
        ///   and a bounded read count when a scanned leaf becomes a cycle. A
        ///   missing walk budget overruns that count; other source mutations
        ///   are outside this fixture, whose own cutoff keeps the failure
        ///   finite.
        /// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
        #[spec(
            captures: [entry = self.reads.get()],
            ensures: |ret| self.reads.get() == entry.saturating_add(1_u32)
                && (matches!(ret, Former::Product(arity) if usize::from(arity) == 0)
                    || matches!(ret, Former::ThunkType(_) | Former::Returner(_) | Former::Unreadable(_))),
        )]
        fn read(
            &self,
            _node: ChangingNode,
        ) -> Former<'_, ChangingNode>
        {
            let entry = self.reads.get();
            self.reads.set(entry.saturating_add(1_u32));
            if entry == 0_u32 {
                Former::Product(crate::former::Arity::from(0_usize))
            }
            else if entry >= VISIT_BUDGET.saturating_add(4_u32) {
                Former::Unreadable(crate::former::Unreadable::Dangling)
            }
            else if entry & 1_u32 == 1_u32 {
                Former::ThunkType(ChangingNode)
            }
            else {
                Former::Returner(ChangingNode)
            }
        }

        /// No component: the fixture's only n-ary reading is the unit.
        ///
        /// # Specification
        /// trivial.
        fn component(
            &self,
            _node: ChangingNode,
            _index: Component,
        ) -> Option<ChangingNode>
        {
            None
        }

        /// No label: the fixture holds no record.
        ///
        /// # Specification
        /// trivial.
        fn label(
            &self,
            _node: ChangingNode,
            _index: Component,
        ) -> Option<super::Name<'_>>
        {
            None
        }
    }

    /// A source cannot bypass the traversal budget by changing after its scan.
    #[test]
    fn changing_source_is_still_bounded_by_the_walk_budget()
    {
        let source = ChangingSource {
            reads: Cell::new(0_u32),
        };
        let result = crate::present_type(
            &source,
            ChangingNode,
            PageWidth::from(80_u32),
            crate::Form::Sugared.into(),
        );
        assert!(
            source.reads.get() <= VISIT_BUDGET.saturating_add(1_u32),
            "read count escaped the scan plus walk bound: {}",
            source.reads.get()
        );
        let presentation = result.expect("the visit budget refuses before layout construction");
        assert_eq!(presentation.as_ref(), "?");
        assert_eq!(presentation.fidelity(), Fidelity::Approximate);
    }

    /// Depth refusal precedes even an unknown kind and only values deepen.
    #[test]
    fn depth_boundaries_preserve_precedence_and_saturation()
    {
        let before = super::ValueDepth(super::DEPTH_LIMIT.0.saturating_sub(1_u32));
        assert_eq!(
            super::reach(super::Admits::Value, before, super::Kind::Unknown),
            super::Reach::Spell
        );
        assert_eq!(
            super::reach(
                super::Admits::Value,
                super::DEPTH_LIMIT,
                super::Kind::Unknown
            ),
            super::Reach::Deep
        );
        assert_eq!(
            super::reach(super::Admits::Type, super::DEPTH_LIMIT, super::Kind::Value),
            super::Reach::Misplaced
        );
        assert_eq!(
            super::reach(
                super::Admits::Type,
                super::DEPTH_LIMIT,
                super::Kind::Unknown
            ),
            super::Reach::Spell
        );
        let ceiling = super::ValueDepth(u32::MAX);
        assert_eq!(super::below(ceiling, super::Kind::Value), ceiling);
        assert_eq!(super::below(before, super::Kind::CompType), before);
        assert_eq!(super::below(before, super::Kind::Value), super::DEPTH_LIMIT);
    }

    /// Candidate spelling crosses alphabet rounds and represents the last
    /// ordinal.
    #[test]
    fn candidate_names_cross_rounds_without_losing_the_last_ordinal()
    {
        for (ordinal, expected) in [
            (0_u32, "a"),
            (25_u32, "z"),
            (26_u32, "a1"),
            (51_u32, "z1"),
            (52_u32, "a2"),
            (u32::MAX, "v165191049"),
        ] {
            assert!(matches!(super::candidate(super::Ordinal(ordinal)),
                super::Maybe::Present(name) if name.0 == expected));
        }
    }

    /// Avoided names and cached positions survive candidate-counter exhaustion.
    #[test]
    fn binder_exhaustion_preserves_existing_names()
    {
        let mut binders = super::Binders::new(super::BTreeSet::from([super::Name::from("a")]));
        assert!(
            matches!(binders.name_at(super::OpenBinders(0_usize)), super::Maybe::Present(name) if name.0 == "b")
        );
        assert!(
            matches!(binders.name_at(super::OpenBinders(1_usize)), super::Maybe::Present(name) if name.0 == "c")
        );
        binders.next = super::Ordinal(u32::MAX);
        assert!(matches!(
            binders.name_at(super::OpenBinders(2_usize)),
            super::Maybe::Absent(super::binder::Absent::Exhausted)
        ));
        assert!(
            matches!(binders.name_at(super::OpenBinders(0_usize)), super::Maybe::Present(name) if name.0 == "b")
        );
        assert_eq!(binders.generated.len(), 2_usize);
    }

    /// Text-budget refusal must not manufacture a piece or erase approximation.
    #[test]
    fn failed_atoms_do_not_push_pieces_or_restore_fidelity()
    {
        let limits = gandr_surface_layout::limits::BuildLimits {
            max_text_bytes: 0_usize.into(),
            ..gandr_surface_layout::limits::BuildLimits::default()
        };
        let mut meter = gandr_surface_layout::limits::BuildMeter::new(limits);
        let mut builder = gandr_surface_layout::build::DocBuilder::try_new(&mut meter)
            .expect("singleton nodes need no text bytes");
        let mut paged = crate::compose::Paged::new(&mut builder);
        let mut walk = super::Walk {
            builder: &mut paged,
            pieces: super::Vec::new(),
            binders: super::Binders::new(super::BTreeSet::new()),
            names: super::Vec::new(),
            opened: super::Vec::new(),
            scopes: super::Vec::new(),
            occurring: super::BTreeSet::new(),
            held: super::Vec::new(),
            substituted: super::BTreeMap::new(),
            context: &[],
            recursive: None,
            fidelity: Fidelity::Faithful,
            unspelled: super::BTreeSet::new(),
            bodies: super::Bodies::Opaque,
            protocols: super::Vec::new(),
            forms: super::Vec::new(),
            form: crate::Form::Sugared,
            spelling: super::grammar::Spelling::Unicode,
            remaining: super::VISIT_BUDGET,
            surface: super::Surface::Expression,
        };
        let refusal = super::PresentationError::Build(
            gandr_surface_layout::error::BuildError::LimitExceeded {
                kind: gandr_surface_layout::error::BuildLimitKind::TextBytes,
                limit: 0_u64.into(),
            },
        );
        assert_eq!(walk.atom(super::Glyphs("x")), Err(refusal));
        assert!(walk.pieces.is_empty());
        assert_eq!(walk.fidelity, Fidelity::Faithful);
        assert!(matches!(
            walk.approximate(
                super::Glyphs("?"),
                super::Unspelled::Elided(crate::former::Elided::Deep)
            ),
            Err(super::PresentationError::Build(
                gandr_surface_layout::error::BuildError::LimitExceeded {
                    kind: gandr_surface_layout::error::BuildLimitKind::TextBytes,
                    ..
                }
            ))
        ));
        assert!(walk.pieces.is_empty());
        assert_eq!(walk.fidelity, Fidelity::Approximate);
    }

    /// The scan visits as many nodes as its budget and no more: a tree of
    /// exactly `VISIT_BUDGET` nodes is scanned, one of a node more is over
    /// budget.
    #[test]
    fn the_name_scan_visits_exactly_its_budget()
    {
        let budget = usize::try_from(super::VISIT_BUDGET).expect("the budget fits a usize");
        let mut arena = gandr_core_term::CoreArena::new();
        let unit = arena.value_unit();
        let within = arena.value_tuple(&super::Vec::from_iter(core::iter::repeat_n(
            unit,
            budget.saturating_sub(1_usize),
        )));
        let over = arena.value_tuple(&super::Vec::from_iter(core::iter::repeat_n(unit, budget)));
        let source = crate::core_source::CoreSource::new(&arena, &[]);
        let scanned = |root| {
            super::mentioned(
                &source,
                crate::core_source::CoreNode::Value(root),
                super::Admits::Value,
                super::Bodies::Opaque,
            )
        };
        assert!(matches!(scanned(within), super::Maybe::Present(_)));
        assert!(matches!(
            scanned(over),
            super::Maybe::Absent(super::scan::Absent::OverBudget)
        ));
    }

    /// An incomplete join reports bookkeeping, not a fabricated layout refusal.
    #[test]
    fn missing_operands_are_unbalanced_not_layout_failures()
    {
        let mut meter = gandr_surface_layout::limits::BuildMeter::new(
            gandr_surface_layout::limits::BuildLimits::default(),
        );
        let mut builder = gandr_surface_layout::build::DocBuilder::try_new(&mut meter)
            .expect("default limits build");
        let mut paged = crate::compose::Paged::new(&mut builder);
        let mut walk = super::Walk {
            builder: &mut paged,
            pieces: super::Vec::new(),
            binders: super::Binders::new(super::BTreeSet::new()),
            names: super::Vec::new(),
            opened: super::Vec::new(),
            scopes: super::Vec::new(),
            occurring: super::BTreeSet::new(),
            held: super::Vec::new(),
            substituted: super::BTreeMap::new(),
            context: &[],
            recursive: None,
            fidelity: Fidelity::Faithful,
            unspelled: super::BTreeSet::new(),
            bodies: super::Bodies::Opaque,
            protocols: super::Vec::new(),
            forms: super::Vec::new(),
            form: crate::Form::Sugared,
            spelling: super::grammar::Spelling::Unicode,
            remaining: super::VISIT_BUDGET,
            surface: super::Surface::Expression,
        };
        walk.atom(super::Glyphs("x")).expect("one operand builds");
        assert_eq!(
            walk.join(super::Join::Arrow),
            Err(super::PresentationError::Unbalanced)
        );
        assert!(walk.pieces.is_empty());
        assert!(matches!(
            walk.pop(),
            Err(super::PresentationError::Unbalanced)
        ));
        walk.forms.push(super::Vec::from([super::Part::Open]));
        assert_eq!(
            walk.join(super::Join::Form {
                pieces: super::Arity(0_usize),
                binding: super::Binding::Atom,
            }),
            Err(super::PresentationError::Unbalanced),
            "a form that opens a block it never closes"
        );
        walk.atom(super::Glyphs("x")).expect("one piece builds");
        walk.forms.push(super::Vec::new());
        assert_eq!(
            walk.join(super::Join::Form {
                pieces: super::Arity(1_usize),
                binding: super::Binding::Atom,
            }),
            Err(super::PresentationError::Unbalanced),
            "a form that leaves a piece it takes unplaced"
        );
    }

    /// Empty and forbidden-control names cannot masquerade as faithful atoms.
    #[test]
    fn unprintable_names_are_approximate_atoms()
    {
        let mut arena = gandr_core_term::CoreArena::new();
        let constant = arena.value_constant(gandr_kernel_term::ConstantIndex::from(0_usize));
        let family = arena.value_type_data(
            gandr_kernel_term::ConstantIndex::from(0_usize),
            super::Vec::new(),
        );
        for invalid in ["", "\r", "\n", "\t"] {
            let names = [super::Name::from(invalid)];
            let source = crate::core_source::CoreSource::new(&arena, &names);
            let result = crate::present_value(
                &source,
                crate::core_source::CoreNode::Value(constant),
                PageWidth::from(80_u32),
                crate::Form::Sugared.into(),
            )
            .expect("malformed names are approximated");
            assert_eq!(result.as_ref(), "?");
            assert_eq!(result.fidelity(), Fidelity::Approximate);
            let typed = crate::present_type(
                &source,
                crate::core_source::CoreNode::ValueType(family),
                PageWidth::from(80_u32),
                crate::Form::Sugared.into(),
            )
            .expect("malformed names are approximated");
            assert_eq!(typed.as_ref(), "?", "a family named {invalid:?}");
            assert_eq!(typed.fidelity(), Fidelity::Approximate);
        }
    }

    /// At the cutoff the operator remains unpeeled and executes before its
    /// argument.
    #[test]
    fn spine_schedules_operator_first_at_the_depth_limit()
    {
        let mut arena = gandr_core_term::CoreArena::new();
        let inner = arena.value_unit();
        let argument = arena.value_constant(gandr_kernel_term::ConstantIndex::from(0_usize));
        let operator = arena.value_static_application(inner, argument);
        let source = crate::core_source::CoreSource::new(&arena, &[]);
        let operator = crate::core_source::CoreNode::Value(operator);
        let argument = crate::core_source::CoreNode::Value(argument);
        let mut tasks = super::Vec::new();
        super::Walk::spine(
            &source,
            operator,
            argument,
            super::ValueDepth(super::DEPTH_LIMIT.0.saturating_sub(1_u32)),
            super::ReductAs::Term,
            &mut tasks,
        );
        assert!(matches!(tasks.as_slice(), [
            super::Task::Join(super::Join::Apply(super::Arity(1_usize))),
            super::Task::Visit { node: found_argument, admits: super::Admits::Value, depth: argument_depth },
            super::Task::Visit { node: found_operator, admits: super::Admits::Value, depth: operator_depth },
        ] if *found_argument == argument && *found_operator == operator
            && *argument_depth == super::DEPTH_LIMIT && *operator_depth == super::DEPTH_LIMIT));
    }
}
