//! The presentation printer: checked core types, normal-form values and
//! elaborated bodies, laid out at a page width.
//!
//! A caller hands the printer a [`Source`] — a store that answers, for one
//! handle, the [`Former`] the node carries — a root and a [`PageWidth`]. The
//! printer walks the nodes into one layout document, every break point a
//! choice between the byte the one-line spelling carries there and a line
//! break, and the layout engine picks the layout for the page.
//!
//! | item                          | what it is                                               |
//! | ----------------------------- | -------------------------------------------------------- |
//! | [`present_type`]              | a value or computation type at a width                   |
//! | [`present_value`]             | a value at a width, bounded at [`DEPTH_LIMIT`]            |
//! | [`present_computation`]       | an elaborated body at a width, its exits elided           |
//! | [`present_computation_line`]  | the same body on one line, never laid out                |
//! | [`Form`]                      | sugared or explicit: which spelling a former takes       |
//! | [`Spelling`], [`Style`]       | Unicode or ASCII glyphs; a form and a spelling together  |
//! | [`Presentation`]              | the laid-out text and whether it says the whole node     |
//! | [`Source`], [`Former`]        | the one question the printer asks of its input           |
//! | [`CoreSource`]                | the core arena as a source                               |
//! | [`ContentSource`]             | a checkpoint's content table as a source                 |
//! | [`PresentationError`]         | a layout ceiling reached on the way                      |
//!
//! # One walk, two composers
//!
//! The walk writes each leaf and join into a composer. The page faces compose
//! a layout document and let the engine choose its breaks;
//! [`present_computation_line`] composes text directly, taking at each choice
//! the side with fewer breaks, because building the document — not choosing
//! among its layouts — is most of what a value a run prints would cost.
//!
//! - **Alternatives.** Rendering the layout document without a break search
//!   still builds and interns the document for every value.
//! - **Reversal.** A one-line face whose text must follow a cost only the
//!   resolver decides.
//!
//! # Two forms, one walk
//!
//! Every presentation entry point takes a [`Style`]: a [`Form`] and a
//! [`Spelling`]. Both forms write only what the surface grammar parses, so a
//! printed type reads back as the type it names.
//!
//! Every production spells a mold, every mold has a production: each spelling
//! the printer writes is one the grammar molds and the lowering reads back to
//! the node printed, and each node the core holds has a spelling or is the
//! honest `?` below. The dispatcher's corpus census holds the contract over
//! every printed type, run value and normal form the corpus states: a
//! spelling that does not parse, that the lowering refuses or that the
//! printer cannot lay out fails it by name, and so does a spelling whose
//! reading prints otherwise, `print(parse(print(x))) = print(x)` up to
//! layout. A parameterised constructor is written against its family,
//! `(MkIx : Ix(3))`, except where its position states its type — a family's
//! argument, `Vec(MkIx)` — whose parameter the lowering classifies it by.
//!
//! **Explicit** gives every former one spelling: `Integer`, `String`, `Unit`,
//! `Void`, `Bool`, `#{A, B, …}`, `#{l : A, …}`, `+{A, B, …}`, `&{C, D}`,
//! `+U C`, `-F A`, `-F [I, …] A` over a row of interfaces, `A -> C`,
//! `(x : A) -> C`, the static Pi `A -> B` between value types, a
//! continuation's type `Stack(C, D)`, `Type`,
//! `Type[-]`, `Type[+, l]`, `Type[-, l]`, an abstract
//! type and a constant by name, and a decode as the code it reads; values are
//! `unit`, literals with their canonical digits and escapes, `#{a, b, …}`,
//! `#{.l = v, …}`, `+{.i = v}`, `here(a)`, `funext(f, g)`, `equiv(f, g)`,
//! univalence at a stratum `ua[n, k](a, b, f, g)` with its two descriptions
//! by name, the static abstraction `\a. v`, and a static application as its
//! spine, `f(a, b)` for `f` applied to `a` and then to `b` (the type
//! operators of `gandr-surface-grammar`). Every braced former is written
//! between its delimiters at any arity from one, its labels in their declared
//! order.
//!
//! **Sugared** writes, besides, every sugar the grammar parses where the
//! core's shape is exactly the one the sugar stands for: the product `A * B`
//! and the sum `A + B` of two components or more, `A * B * C` one product of
//! three as the lowering flattens the chain; the binary lazy product `C & D`;
//! the tuple `(a, b)` of two components or more; the value-function alias
//! `A => C`, `() => C` and `(A, B) => C` for a thunk over a chain of
//! non-dependent arrows ending in a pure returner; and the path composite
//! `p then q` for the returned transport `transport(\y. Path(A, a, y), q, p)`
//! it derives, the carrier and the fixed endpoint naming no `y` (#754). A
//! dependent arrow, an effectful returner, a record, a sum or product of one
//! component and the empty ones keep their explicit spelling. Sugared is what
//! every reader-facing
//! face shows — a hover, a diagnostic, the REPL, the terminal face and a
//! run's value; explicit is what an editor's `gandr.presentation.form` asks
//! for, and what the golden fixtures of the core's own spellings pin.
//!
//! Binding strength follows the grammar's bands, tightest first: atoms, every
//! braced former among them, then the bridges `+U` and `-F` (built-in
//! spellings in `gandr-surface-grammar`), then `*`, then `+`, then `&`, then
//! the arrows `->` and `=>`; every band associates to the right. A product's
//! operand is bare up to a bridge, a sum's up to a product, `&`'s left
//! operand up to a sum and its right up to `&`, and an arrow's domain up to
//! `&`, its codomain bare. A static abstraction binds as loosely as an arrow,
//! its body running to the right, and an application is an atom whose
//! operator is parenthesized unless it is one. A static redex prints as its
//! reduct, each binder written as the argument it takes, so the type a
//! classifier applied to an abstraction denotes reads as it is written plainly.
//!
//! A node the surface has no spelling for — a lift, the numeric atom, a linear
//! or unbound variable, a term where a type stands — is written `?`, and a
//! thunk value presented alone `<thunk>`; each makes the presentation
//! approximate. Fidelity is recorded by the nodes the walk met, so a name that
//! happens to contain `?` stays faithful. A page the one-line spelling fits
//! selects it unchanged.
//!
//! The recorded design gave every former one spelling and printed none of the
//! sugar, so that the printer wrote what the core holds: a thunked arrow read
//! `+U (Integer -> -F String)` where its source read `Integer => String`, and
//! a pair `#{1, "a"}` where it was written `(1, "a")`. The change keeps that
//! spelling as the explicit form and adds the sugared one as the default,
//! because the reader of a hover or a diagnostic reads the surface they write,
//! and the sugar is no less exact: each sugared spelling lowers to the same
//! core node, which the dispatcher's readback witness checks. The form is one
//! flag on the walk — a former's sugared spelling is one more arm of its
//! visit and join — so the two forms never diverge in what they admit.
//!
//! - **Alternatives.** One spelling with the sugar always, which hides the
//!   formers a reader learning the core needs to see; one without it, the
//!   recorded design, which a hover over a function shows as a thunk of an
//!   arrow of a returner; a notation independent of the grammar, which would
//!   print text the surface cannot read back; parenthesizing every compound
//!   operand, simpler to state but longer at every chain.
//! - **Reversal.** A ruled change to the grammar's spellings or bands; this
//!   crate follows it, never leads it. A sugar the lowering stops reading back
//!   to the shape it prints leaves the sugared form.
//!
//! # Two spellings
//!
//! Every construct has an ASCII spelling and may have a Unicode one
//! (`gandr-surface-grammar` § Spellings). [`Spelling::Unicode`], the default,
//! writes each glyph the grammar holds; [`Spelling::Ascii`] writes what the
//! grammar's table pairs it with: `A <~> B` for `A ≃ B`, `A ~~> B` for `A ⇝
//! B`, the call `Iso(A, B)` for `A ≅ B`, and `g :: p` for `g ∷ p`. A name
//! holding the prime `′`, which has no ASCII spelling, is written `?` and the
//! presentation is approximate, recorded [`Unspelled::Primed`]; a binder the
//! source named so takes a generated name instead, as one that would capture
//! does. The spelling is a second flag on the walk beside the form, read at
//! the arms that write a glyph, so both spellings admit the same nodes.
//!
//! - **Alternatives.** Transliterating the Unicode text afterwards, which
//!   cannot write `≅` as a call and would rewrite a glyph inside a string
//!   literal; a spelling per glyph, which no reader asked for.
//! - **Reversal.** A ruled ASCII spelling for the prime, at which point a
//!   primed name is written with it instead of `?`.
//!
//! # A body prints in its canonical form, its exits elided
//!
//! [`present_computation`] is the canonical printer of an elaborated body: it
//! writes the form the lowering reads back to the same term, with every exit
//! the lowering would infer left out. A returner where a path through the
//! body ends is written as its value, `n`, never `return n`; any other
//! computation there bare, `f(n)`, never `become f(n)`; a returner anywhere
//! else is `pure v`, since a written `return` there would leave the body. A
//! bind is `run x <- c ; rest`, its statements one per line when the body
//! does not fit; a force is `force v`, and a force at a call's head is the
//! value it forces, `f(a, b)`, as the surface writes a call; a lambda is
//! `fn (x) { c }` and, inside a body, a thunk is `thunk { c }`. A value
//! presented alone keeps its thunks opaque. Case analyses, splits,
//! projections, fixpoints, native operations, transports and the effect and
//! control operators are spelled as the surface writes them. What the core
//! holds only by position — a constructor's name by its tag, a field label, an
//! operation — comes from the [`Source`]: a data case's branch is written
//! under the pattern [`Source::constructor`] names, and a source that cannot
//! name it writes `?` there, approximate. A source as written is the
//! formatter's (`gandr-surface-format`): it keeps every token, the exit
//! keywords among them, so a source round-trips as written.
//!
//! - **Alternatives.** Printing every exit keyword, the form the surface
//!   required before exits were inferred, which a module can still ask for
//!   through the `explicit-exits` lint of `gandr-surface-diagnostics`; it is
//!   the longer form for the same term, and a printer that writes it would
//!   disagree with the shortest source the lowering reads back to that term.
//! - **Reversal.** A ruled change that makes the written keywords canonical, or
//!   a source that answers constructor, label and operation names, at which
//!   point the case and projection forms gain their spellings.
//!
//! # Totality
//!
//! Nothing here panics or recurses. The walk drains an explicit task stack, a
//! value deeper than [`DEPTH_LIMIT`] is written `<deep>`, a source that takes
//! more node visits than one presentation makes — a cycle — is written `?`,
//! and every layout failure is a [`PresentationError`].
//!
//! # Answers checked at compile time
//!
//! The corpus census above is the runtime half of the contract; the lint
//! wall holds its static half (quenchant's `answer_totality` group, whose
//! tables the workspace's `check:dylint` task configures):
//!
//! - every `?` the printer can build — a [`Former::Unreadable`], an
//!   [`Unspelled`] reason, the unknown node kind, a `"?"` or a `'?'` — is built
//!   only under an `expect` whose reason says why no spelling exists;
//! - the walk's `visit` and `form` name every [`Former`] variant;
//! - each arm that writes a grammar rule names it, `writes(Production("rule"),
//!   …)`, and the rules named equal the rules the grammar builds, but for those
//!   the configuration lists as unproduced, each with its reason: the
//!   declarations, patterns and shell syntax no core node carries, and the
//!   sugar the lowering elaborates away.
//!
//! The marker is read only by the lint; at run time `writes` is the identity.
//!
//! - **Alternatives.** The census alone, which finds a missing production only
//!   when the corpus happens to print one; a lint level without `expect`'s
//!   reason, which would let a residue stand unexplained; a production table
//!   beside the walk, which would drift from the arms that write.
//! - **Reversal.** A grammar built from data the lint cannot read, at which
//!   point the production set returns to the census alone.
//!
//! # Tests and their limits
//!
//! The golden fixtures cover exact grammar spellings and their narrow and wide
//! layouts; the README's Provided features names their observers. Boundary
//! witnesses cover truncation across all four core-node families,
//! admission-table endpoints, depth saturation, candidate rounds, binder
//! exhaustion, error causes and layout refusals.
//!
//! Run `RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p
//! gandr-surface-pretty` to execute the predicates as well as the independent
//! assertions. Adequacy blocks state the finite input domains and the mutations
//! each witness distinguishes; they do not claim exhaustive coverage.
//!
//! Executable exemptions remain at opaque observation boundaries: the abstract
//! source reader, child-handle provenance without its source, admission-table
//! correspondence to declarations not held by the adapter, and formatting into
//! an opaque destination. Their source contracts name the missing observer;
//! concrete reader, borrowed-key and error-chain obligations retain executable
//! predicates.
//!
//! # References
//!
//! - Sorawee Porncharoenwase, Justin Pombrio, and Emina Torlak. "A Pretty
//!   Expressive Printer." _Proceedings of the ACM on Programming Languages_ 7,
//!   OOPSLA2, October 2023.
//!   [doi:10.1145/3622837](https://doi.org/10.1145/3622837),
//!   [arXiv:2310.01530](https://arxiv.org/abs/2310.01530) — the cost order and
//!   the computation width the documents here are resolved under.
//! - Jean-Philippe Bernardy. "A Pretty But Not Greedy Printer (Functional
//!   Pearl)." _Proceedings of the ACM on Programming Languages_ 1, ICFP,
//!   article 6, September 2017.
//!   [doi:10.1145/3110250](https://doi.org/10.1145/3110250) — choosing a layout
//!   over all candidates rather than the first that fits, which lets each break
//!   point be an independent choice.
//! - Phillip M. Yelland. "A New Approach to Optimal Code Formatting." Technical
//!   report, Google, 2016. [research.google](https://research.google/pubs/a-new-approach-to-optimal-code-formatting/)
//!   — formatting as least cost over alternative layouts with an overflow
//!   penalty, the tradition the break-point choices belong to.
//! - Philip Wadler. "A Prettier Printer." In Jeremy Gibbons and Oege de Moor
//!   (editors), _The Fun of Programming_, Palgrave Macmillan, 2003.
//!   [prettier.pdf](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf)
//!   — the document algebra the documents are written in.

// Module documentation that predates the shape lint: 17 headings outside the
// vocabulary, 16 decision records, 8 issue references and 3 budgets exceeded.
// Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(linear_search_in_loop, reason = "1 cost-shape site; #814 lists it")
)]

extern crate alloc;

mod compose;

mod content_source;

mod core_source;

mod error;

mod former;

mod scope;

mod walk;

use alloc::collections::BTreeSet;
use core::fmt;

use anodized::spec;
pub use gandr_surface_grammar::Spelling;
use gandr_surface_layout::ComputationWidth;
use gandr_surface_layout::LayoutOptions;
pub use gandr_surface_layout::PageWidth;
use gandr_surface_layout::PhysicalLineEnding;
use gandr_surface_layout::RenderError;
use gandr_surface_layout::RenderLimits;
use gandr_surface_layout::RenderMeter;
use gandr_surface_layout::build::DocBuilder;
use gandr_surface_layout::limits::BuildLimits;
use gandr_surface_layout::limits::BuildMeter;
use gandr_surface_layout::render::RenderedText;
use gandr_surface_layout::render::render;

use crate::compose::Compose;
use crate::compose::Glyphs;
use crate::compose::OneLine;
use crate::compose::Paged;
pub use crate::content_source::ContentSource;
pub use crate::core_source::Constructors;
pub use crate::core_source::CoreNode;
pub use crate::core_source::CoreSource;
pub use crate::core_source::Restoration;
pub use crate::error::PresentationError;
pub use crate::former::Arity;
pub use crate::former::Component;
pub use crate::former::Former;
pub use crate::former::Name;
pub use crate::former::Placement;
pub use crate::former::Source;
pub use crate::former::Unreadable;
pub use crate::former::Unspelled;
pub use crate::scope::Binder;
pub use crate::scope::BinderIndex;
pub use crate::scope::ChildSlot;
pub use crate::scope::Scopes;
use crate::walk::Admits;
use crate::walk::Bodies;
use crate::walk::Tail;
use crate::walk::Walked;
use crate::walk::walk;

/// How many value formers enclose a node of a presentation.
///
/// Types do not count: a value nested in a type — the code a decode reads —
/// stands at the depth of the value the type is nested in.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ValueDepth(u32);

impl ValueDepth
{
    /// The depth of a presentation's root.
    const ROOT: Self = Self(0_u32);

    /// The depth one value former further in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the next value depth, saturating at the maximum count.
    /// - provides: bounded descent through value formers.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the root, penultimate count and maximum distinguish
    ///   increment, premature saturation and wraparound; intervening counts are
    ///   governed by the same arithmetic but not enumerated.
    /// - witness: `tests::value_depth_saturates_without_wrapping`
    #[spec(ensures: |ret| if self.0 == u32::MAX {
        ret.0 == u32::MAX
    } else { matches!(ret.0.checked_sub(self.0), Some(1_u32)) })]
    const fn deeper(self) -> Self
    {
        Self(self.0.saturating_add(1_u32))
    }
}

impl From<ValueDepth> for u32
{
    /// The depth as a count of enclosing value formers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: ValueDepth) -> Self
    {
        depth.0
    }
}

/// The value depth at which the printer stops descending and writes `<deep>`.
///
/// A value of the depth a reader reads stays well inside it; a normal form
/// nested deeper is shown as its outer formers around one `<deep>` leaf, so
/// a presentation stays a size a page can hold.
pub const DEPTH_LIMIT: ValueDepth = ValueDepth(32_u32);

/// Whether a presentation says exactly the node it was made from.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Fidelity
{
    /// Every node was written as the surface writes it.
    Faithful,
    /// Some node has no surface spelling or exceeds the depth limit.
    /// Diagnostic notation and placeholders are not round-trippable source.
    Approximate,
}

/// Which of the spellings the grammar parses a presentation writes where the
/// core's shape admits more than one.
///
/// Both read back to the same core term; they differ only where the surface
/// has a sugar for a shape (§ Two forms, one walk).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Form
{
    /// Every sugar the grammar parses where the core's shape is exactly the
    /// sugar's: the value-function alias `(A, B) => C` for `+U (A -> B -> -F
    /// C)`, the infix `A * B`, `A + B` and `C & D`, the tuple `(a, b)`, and
    /// the path composite `p then q` for the transport it derives.
    /// The form every face a person reads takes by default.
    Sugared,
    /// What the core holds, former by former: `+U (A -> B -> -F C)`,
    /// `#{A, B}`, `+{A, B}`, `&{C, D}` and `#{a, b}`.
    Explicit,
}

/// How a presentation is written: which of the grammar's spellings a former
/// takes, and which glyphs.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Style
{
    /// Sugared or explicit (§ Two forms, one walk).
    pub form: Form,
    /// Unicode or ASCII (§ Two spellings).
    pub spelling: Spelling,
}

impl From<Form> for Style
{
    /// `form` in the default spelling, Unicode.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(form: Form) -> Self
    {
        Self {
            form,
            spelling: Spelling::Unicode,
        }
    }
}

/// A node laid out at a page width.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Presentation
{
    /// The laid-out text, line feeds between its lines.
    text: RenderedText,
    /// Whether the text says the whole node.
    fidelity: Fidelity,
    /// Why each `?` the text holds was written.
    unspelled: BTreeSet<Unspelled>,
}

impl Presentation
{
    /// Whether the text says the whole node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fidelity(&self) -> Fidelity
    {
        self.fidelity
    }

    /// Why the printer wrote each `?` the text holds, one entry per reason.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unspelled(&self) -> &BTreeSet<Unspelled>
    {
        &self.unspelled
    }
}

impl AsRef<str> for Presentation
{
    /// The laid-out text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.text.as_ref()
    }
}

impl fmt::Display for Presentation
{
    /// Writes the laid-out text unchanged.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.text, f)
    }
}

/// The type at `root` of `source`, laid out at `page`.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: the root, a value type or a computation type, written in its one
///   spelling; at a page the one-line spelling fits, exactly that line, and
///   otherwise the layout of least overflow, then fewest lines, breaking after
///   an arrow, an infix symbol or a comma with the continuation two columns in.
///   A term at the root, a child of the wrong sort and every former without a
///   surface spelling are written `?`, and the presentation is then
///   approximate. A source taking more visits than one presentation makes is
///   written `?`. Successful output contains neither carriage returns nor tabs;
///   layout-owned line endings are line feeds.
/// - provides: the type a transcript line, a hover or a diagnostic names.
/// - fails: a layout ceiling reached while building or rendering; width
///   ordering is never invalid, including at saturated computation widths.
/// - panics: none.
///
/// # Errors
/// Returns [`PresentationError::Build`] or [`PresentationError::Render`] when
/// the layout engine refuses, and [`PresentationError::Unbalanced`] on a
/// defect in the walk's own bookkeeping.
///
/// # Adequacy
/// - hypothesis: L3 — exact spellings cover every core type former, and
///   dependent arrows and arrow chains distinguish both page widths. These
///   observe wrong formers, grouping and line endings over fixed sources. A
///   scanned leaf that becomes a cycle distinguishes the second-pass budget;
///   other source mutations, page widths and layout ceilings are not exhausted.
/// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `tests::goldens::n_ary_products_and_sums_spell_between_their_braces`
/// - witness: `tests::goldens::records_spell_their_fields_in_label_order`
/// - witness: `tests::goldens::dependent_function_type_breaks_before_codomain`
/// - witness: `tests::goldens::long_dependent_function_type_breaks_at_the_narrow_page`
/// - witness: `tests::goldens::arrow_chain_breaks_before_each_continuation`
/// - witness: `tests::goldens::nullary_declared_data_uses_its_bare_name`
/// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
/// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
#[spec(ensures: |ref ret| match *ret {
    Ok(ref presentation) => !presentation.as_ref().contains(['\r', '\t']),
    Err(PresentationError::Render(RenderError::InvalidWidth)) => false,
    Err(_) => true,
})]
#[inline]
pub fn present_type<S>(
    source: &S,
    root: S::Node,
    page: PageWidth,
    style: Style,
) -> Result<Presentation, PresentationError>
where
    S: Source + ?Sized,
{
    present(
        source,
        root,
        (Admits::Type, Bodies::Spelled),
        style,
        Layout::Page(page),
    )
}

/// The value at `root` of `source`, laid out at `page`.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: the root written as [`present_type`] writes a type, a value's
///   formers spelled `unit`, as their literal, `#{a, b}`, `#{.l = v}` in label
///   order and `+{.i = v}` at any summand, `here(a)`, `funext(f, g)`, `equiv(f,
///   g)`, `ua[n, k](a, b, f, g)`, a constant by its name and the code of a type
///   as the type; a thunk is written `<thunk>`, and a value [`DEPTH_LIMIT`]
///   value formers deep is written `<deep>` inside the formers around it, each
///   making the presentation approximate. Output has the same line-ending and
///   width guarantees as [`present_type`].
/// - provides: the normal form a transcript line or a probe shows.
/// - fails: as [`present_type`].
/// - panics: none.
///
/// # Errors
/// As [`present_type`].
///
/// # Adequacy
/// - hypothesis: L3 — escaped strings, sum and pair notation, a pair broken
///   after its comma, and the depth bound are asserted at both page widths over
///   values read back from evaluation. These distinguish lost escaping,
///   notation and depth boundaries, not every numeric magnitude or layout
///   refusal.
/// - witness: `tests::goldens::string_controls_stay_in_one_escaped_literal`
/// - witness: `tests::goldens::pair_of_injections_pins_sum_notation`
/// - witness: `tests::goldens::n_ary_tuples_and_injections_spell_between_their_braces`
/// - witness: `tests::goldens::record_value_breaks_fields_at_the_narrow_page`
/// - witness: `tests::goldens::beyond_the_depth_limit_renders_deep`
/// - witness: `tests::goldens::fidelity_follows_nodes_not_the_characters_of_a_name`
/// - witness: `tests::goldens::here_witness_pins_identity_notation`
/// - witness: `tests::goldens::univalence_spells_its_stratum_and_descriptions`
#[spec(ensures: |ref ret| match *ret {
    Ok(ref presentation) => !presentation.as_ref().contains(['\r', '\t']),
    Err(PresentationError::Render(RenderError::InvalidWidth)) => false,
    Err(_) => true,
})]
#[inline]
pub fn present_value<S>(
    source: &S,
    root: S::Node,
    page: PageWidth,
    style: Style,
) -> Result<Presentation, PresentationError>
where
    S: Source + ?Sized,
{
    present(
        source,
        root,
        (Admits::Value, Bodies::Opaque),
        style,
        Layout::Page(page),
    )
}

/// The value at `root` of `source`, a definition's body under its stated
/// type, laid out at `page` as source that reads back.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: the root written as [`present_value`] writes a value, but for
///   what a reader reads back: a thunk written `thunk { c }`, its body as
///   [`present_computation`] writes one, and a parameterised constructor below
///   the root written against its family, `(MkIx : Ix(3))`, where the root
///   itself stands bare, its type the definition's. Output has the same
///   line-ending and width guarantees as [`present_type`].
/// - provides: the body of a `def name = …` the lowering reads back to the same
///   term against the definition's stated type.
/// - fails: as [`present_type`].
/// - panics: none.
///
/// # Errors
/// As [`present_type`].
///
/// # Adequacy
/// - hypothesis: L3 — a constructor of a parameterised family, bare at the root
///   and inside a constructor's field, and a thunk below the root, distinguish
///   a lost annotation, an annotation at the root and an opaque thunk.
/// - witness: `tests::goldens::a_definition_writes_its_constructors_against_their_family_815`
#[spec(ensures: |ref ret| match *ret {
    Ok(ref presentation) => !presentation.as_ref().contains(['\r', '\t']),
    Err(PresentationError::Render(RenderError::InvalidWidth)) => false,
    Err(_) => true,
})]
#[inline]
pub fn present_definition<S>(
    source: &S,
    root: S::Node,
    page: PageWidth,
    style: Style,
) -> Result<Presentation, PresentationError>
where
    S: Source + ?Sized,
{
    present(
        source,
        root,
        (Admits::Stated, Bodies::Spelled),
        style,
        Layout::Page(page),
    )
}

/// The computation at `root` of `source`, an elaborated body, laid out at
/// `page` in its canonical form: every exit a path through it ends in elided.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: the root written as the body of a definition: a returner where a
///   path through the body ends written as its value and any other computation
///   there bare, never `return` or `become`; a returner anywhere else `pure v`;
///   a bind `run x <- c ; rest`, the computation it runs a block `{ … }` when
///   it is itself a bind; a force `force v`, a call `f(a, b)` with a forced
///   value at its head written as the value; a lambda `fn (x) { c }` and a
///   thunk `thunk { c }`; binders named as a dependent arrow's are; values and
///   types inside as [`present_value`] and [`present_type`] write them, but for
///   thunks. Every computation without a surface spelling here is `?`,
///   approximate. The body's statements break together: on one line when it
///   fits the page, one per line otherwise, a block's body two columns in.
///   Output has the same line-ending and width guarantees as [`present_type`].
/// - provides: the canonical printer of an elaborated body, which the lowering
///   reads back to the same term.
/// - fails: as [`present_type`].
/// - panics: none.
///
/// # Errors
/// As [`present_type`].
///
/// # Adequacy
/// - hypothesis: L3 — bodies built as the lowering builds them, with their
///   exits written and elided, a bind run by a bind, a call of a forced
///   constant and a call of a returner, at the wide and a narrow page,
///   distinguish a written exit, a lost `pure`, a missing block and binder
///   capture; case analyses are asserted approximate.
/// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
#[spec(ensures: |ref ret| match *ret {
    Ok(ref presentation) => !presentation.as_ref().contains(['\r', '\t']),
    Err(PresentationError::Render(RenderError::InvalidWidth)) => false,
    Err(_) => true,
})]
#[inline]
pub fn present_computation<S>(
    source: &S,
    root: S::Node,
    page: PageWidth,
    style: Style,
) -> Result<Presentation, PresentationError>
where
    S: Source + ?Sized,
{
    present(
        source,
        root,
        (Admits::Computation(Tail::Ends), Bodies::Spelled),
        style,
        Layout::Page(page),
    )
}

/// The computation at `root` of `source` as [`present_computation`] spells
/// it, on as few lines as it admits.
///
/// The layout a page no line overflows selects, written by the same walk
/// straight into text, with no layout document built and no break searched
/// for.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: the text [`present_computation`] writes at a page wider than
///   every line, the same fidelity and the same unspelled reasons; a body's
///   statements on one line, a break only where the document admits no other.
/// - provides: the spelling of a value a run prints, read as one line and never
///   laid out to a page.
/// - fails: as [`present_type`].
/// - panics: none.
///
/// # Errors
/// As [`present_type`].
///
/// # Adequacy
/// - hypothesis: L3 — the elaborated bodies of the golden, with binds, blocks
///   and calls, written on one line equal their layout at a page no line
///   overflows; a choice taken the wrong way or a soft break kept changes the
///   text.
/// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
#[spec(ensures: |ref ret| match *ret {
    Ok(ref presentation) => !presentation.as_ref().contains(['\r', '\t']),
    Err(PresentationError::Render(RenderError::InvalidWidth)) => false,
    Err(_) => true,
})]
#[inline]
pub fn present_computation_line<S>(
    source: &S,
    root: S::Node,
    style: Style,
) -> Result<Presentation, PresentationError>
where
    S: Source + ?Sized,
{
    present(
        source,
        root,
        (Admits::Computation(Tail::Ends), Bodies::Spelled),
        style,
        Layout::Line,
    )
}

/// Where a presentation is written: laid out at a page, or on as few lines
/// as the document admits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Layout
{
    /// Laid out at the page by the resolver.
    Page(PageWidth),
    /// Written straight into text, on as few lines as admitted.
    Line,
}

/// The node at `root` of `source`, at a `position` admitting its [`Admits`]
/// with thunks written as its [`Bodies`] says, written in `style` as `layout`
/// asks.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the walk's document rendered at the page of a [`Layout::Page`],
///   the computation width twice the page, saturating at its maximum, so the
///   resolver can prove which candidates fit; for [`Layout::Line`], the walk
///   written straight into text on as few lines as it admits, no layout
///   document built. Over-budget walks produce `?`, approximate. Successful
///   text has no carriage return or tab; layout-owned endings are line feeds.
///   Computation width is never narrower than the page.
/// - provides: the one path every entry point takes.
/// - fails: as [`present_type`].
/// - panics: none.
///
/// # Errors
/// As [`present_type`].
///
/// # Adequacy
/// - hypothesis: L3 — exact narrow and wide layouts distinguish the chosen
///   breaks and line-ending policy; cyclic and deep sources distinguish
///   approximation. A scanned leaf becoming a cycle observes the independent
///   walk budget; other source mutations and meter refusals are not exhausted.
/// - witness: `tests::goldens::arrow_chain_breaks_before_each_continuation`
/// - witness: `tests::goldens::string_controls_stay_in_one_escaped_literal`
/// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
/// - witness: `tests::goldens::beyond_the_depth_limit_renders_deep`
/// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
#[spec(ensures: |ref ret| match *ret {
    Ok(ref presentation) => !presentation.as_ref().contains(['\r', '\t']),
    Err(PresentationError::Render(RenderError::InvalidWidth)) => false,
    Err(_) => true,
})]
fn present<S>(
    source: &S,
    root: S::Node,
    position: (Admits, Bodies),
    style: Style,
    layout: Layout,
) -> Result<Presentation, PresentationError>
where
    S: Source + ?Sized,
{
    let spelled = |composer: &mut dyn Compose| {
        Ok::<_, PresentationError>(match walk(source, root, position, style, composer)? {
            Walked::Built {
                doc,
                fidelity,
                unspelled,
            } => (doc, fidelity, unspelled),
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a source taking more visits than one presentation makes, a cycle, \
                              has no finite spelling"
                )
            )]
            Walked::OverBudget => (
                composer.text(Glyphs("?"))?,
                Fidelity::Approximate,
                BTreeSet::from([Unspelled::OverBudget]),
            ),
        })
    };
    let (text, fidelity, unspelled) = match layout {
        Layout::Page(page) => {
            let mut meter = BuildMeter::new(BuildLimits::default());
            let mut builder = DocBuilder::try_new(&mut meter)?;
            let mut paged = Paged::new(&mut builder);
            let (doc, fidelity, unspelled) = spelled(&mut paged)?;
            let doc = paged.handle(doc)?;
            let arena = builder.finish()?;
            let computation = ComputationWidth::from(u32::from(page).saturating_mul(2_u32));
            let options = LayoutOptions::try_new(page, computation, PhysicalLineEnding::Lf)?;
            let mut render_meter = RenderMeter::new(RenderLimits::default());
            let rendered = render(&arena, doc, &options, &mut render_meter)?;
            (rendered.text, fidelity, unspelled)
        },
        Layout::Line => {
            let mut line = OneLine::new();
            let (doc, fidelity, unspelled) = spelled(&mut line)?;
            (
                RenderedText::from(line.into_text(doc)?),
                fidelity,
                unspelled,
            )
        },
    };
    Ok(Presentation {
        text,
        fidelity,
        unspelled,
    })
}

#[cfg(test)]
mod tests
{
    use super::ValueDepth;

    #[test]
    fn value_depth_saturates_without_wrapping()
    {
        assert_eq!(ValueDepth::ROOT.deeper(), ValueDepth(1_u32));
        assert_eq!(
            ValueDepth(u32::MAX.saturating_sub(1_u32)).deeper(),
            ValueDepth(u32::MAX)
        );
        assert_eq!(ValueDepth(u32::MAX).deeper(), ValueDepth(u32::MAX));
    }
}
