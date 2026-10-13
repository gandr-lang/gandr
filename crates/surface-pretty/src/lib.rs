//! The presentation printer: checked core types and normal-form values, laid
//! out at a page width.
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
//! | [`Presentation`]              | the laid-out text and whether it says the whole node     |
//! | [`Source`], [`Former`]        | the one question the printer asks of its input           |
//! | [`CoreSource`]                | the core arena as a source                               |
//! | [`ContentSource`]             | a checkpoint's content table as a source                 |
//! | [`PresentationError`]         | a layout ceiling reached on the way                      |
//!
//! # One spelling per former
//!
//! Every former has exactly one spelling, the one the surface grammar parses:
//! `Integer`, `String`, `Unit`, `#{A, B}`, `#{l : A, m : B}`, `+{A, B}`,
//! `&{C, D}`, `+U C`, `-F A`, `A -> C`, `(x : A) -> C`, `Type`, `Type[-]`,
//! `Type[+, l]`, `Type[-, l]`; `unit`, literals, `#{a, b}`, `#{.l = v}`,
//! `+{.i = v}`. Every braced former is written between its delimiters at any
//! arity from one, its labels in their declared order; the binary sugar
//! `A * B`, `A + B`, `C & D` and `(a, b)` parses and is never printed. A former
//! the surface does not write — a lift, the numeric atom, a variable past
//! every binder, the empty record — is written `?`.
//! Effectful returners display their interface names as diagnostic notation.
//! Both are [`Fidelity::Approximate`], not round-trippable source. A page the
//! one-line spelling fits selects it unchanged.
//!
//! Every former has exactly one spelling, the one the surface grammar parses,
//! so a printed type reads back as the type it names: `Integer`, `String`,
//! `Unit`, `Void`, `Bool`, `#{A, B, …}`, `#{l : A, …}`, `+{A, B, …}`,
//! `&{C, D}`, `+U C`, `-F A`, `A -> C`, `(x : A) -> C`, the static Pi `A -> B`
//! between value types, `Type`, `Type[-]`, `Type[+, l]`, `Type[-, l]`, an
//! abstract type and a constant by name, and a decode as the code it reads;
//! values are `unit`, literals with their canonical digits and escapes,
//! `#{a, b, …}`, `#{.l = v, …}`, `+{.i = v}`, the static abstraction `\a. v`,
//! and a static application as its spine, `f(a, b)` for `f` applied to `a` and
//! then to `b` (the type operators of `gandr-surface-grammar`). Binding
//! strength follows the grammar's bands, tightest first: atoms, every braced
//! former among them, then the bridges `+U` and `-F` (built-in spellings in
//! `gandr-surface-grammar`), then arrow; an arrow's domain is bare up to a
//! bridge and its codomain bare. A static abstraction binds as loosely as an
//! arrow, its body running to the right, and an application is an atom whose
//! operator is parenthesized unless it is one, so a redex reads
//! `(\a. a)(Integer)`. The sugar `A * B`, `A + B`, `C & D`, `(a, b)` and the
//! value-function alias `(A, B) => C` parse and are never printed: the printer
//! writes what the core holds, the alias as `+U (A -> B -> -F C)`.
//!
//! A node the surface has no spelling for — a lift, the numeric atom, a linear
//! or unbound variable, a term where a type stands — is written `?`, and a
//! thunk value `<thunk>`; each makes the presentation approximate. Fidelity is
//! recorded by the nodes the walk met, so a name that happens to contain `?`
//! stays faithful.
//!
//! A right-nested arrow chain stays bare because the grammar parses it so. The
//! REPL's corpus witness expects each signature's line to be its source's own
//! text.
//!
//! - **Alternatives.** A notation independent of the grammar would print text
//!   the surface cannot read back. Parenthesizing every compound operand is
//!   simpler to state but lengthens every chain.
//! - **Reversal.** A ruled change to the grammar's spellings or bands; this
//!   crate follows it, never leads it.
//!
//! # Totality
//!
//! Nothing here panics or recurses. The walk drains an explicit task stack, a
//! value deeper than [`DEPTH_LIMIT`] is written `<deep>`, a source that takes
//! more node visits than one presentation makes — a cycle — is written `?`,
//! and every layout failure is a [`PresentationError`].
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

#![no_std]

extern crate alloc;

mod content_source;

mod core_source;

mod error;

mod former;

mod walk;

use core::fmt;

use anodized::spec;
use gandr_surface_layout::ComputationWidth;
use gandr_surface_layout::LayoutOptions;
pub use gandr_surface_layout::PageWidth;
use gandr_surface_layout::PhysicalLineEnding;
use gandr_surface_layout::RenderError;
use gandr_surface_layout::RenderLimits;
use gandr_surface_layout::RenderMeter;
use gandr_surface_layout::arena::TextSource;
use gandr_surface_layout::build::DocBuilder;
use gandr_surface_layout::limits::BuildLimits;
use gandr_surface_layout::limits::BuildMeter;
use gandr_surface_layout::render::RenderedText;
use gandr_surface_layout::render::render;

pub use crate::content_source::ContentSource;
pub use crate::core_source::CoreNode;
pub use crate::core_source::CoreSource;
pub use crate::error::PresentationError;
pub use crate::former::Arity;
pub use crate::former::Component;
pub use crate::former::Former;
pub use crate::former::Name;
pub use crate::former::Source;
use crate::walk::Admits;
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

/// A node laid out at a page width.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Presentation
{
    /// The laid-out text, line feeds between its lines.
    text: RenderedText,
    /// Whether the text says the whole node.
    fidelity: Fidelity,
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
/// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `goldens::tests::n_ary_products_and_sums_spell_between_their_braces`
/// - witness: `goldens::tests::records_spell_their_fields_in_label_order`
/// - witness: `goldens::tests::dependent_function_type_breaks_before_codomain`
/// - witness: `goldens::tests::long_dependent_function_type_breaks_at_the_narrow_page`
/// - witness: `goldens::tests::arrow_chain_breaks_before_each_continuation`
/// - witness: `goldens::tests::nullary_declared_data_uses_its_bare_name`
/// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
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
) -> Result<Presentation, PresentationError>
where
    S: Source + ?Sized,
{
    present(source, root, Admits::Type, page)
}

/// The value at `root` of `source`, laid out at `page`.
///
/// # Specification
/// - requires: nothing; `source` may be malformed.
/// - ensures: the root written as [`present_type`] writes a type, a value's
///   formers spelled `unit`, as their literal, `#{a, b}`, `#{.l = v}` in label
///   order and `+{.i = v}` at any summand, a constant by its name and the code
///   of a type as the type; a thunk is written `<thunk>`, and a value
///   [`DEPTH_LIMIT`] value formers deep is written `<deep>` inside the formers
///   around it, each making the presentation approximate. Output has the same
///   line-ending and width guarantees as [`present_type`].
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
/// - witness: `goldens::tests::string_controls_stay_in_one_escaped_literal`
/// - witness: `goldens::tests::pair_of_injections_pins_sum_notation`
/// - witness: `goldens::tests::n_ary_tuples_and_injections_spell_between_their_braces`
/// - witness: `goldens::tests::record_value_breaks_fields_at_the_narrow_page`
/// - witness: `goldens::tests::beyond_the_depth_limit_renders_deep`
/// - witness: `goldens::tests::fidelity_follows_nodes_not_the_characters_of_a_name`
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
) -> Result<Presentation, PresentationError>
where
    S: Source + ?Sized,
{
    present(source, root, Admits::Value, page)
}

/// The node at `root` of `source`, in a position admitting `admits`, laid out
/// at `page`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the walk's document rendered at `page`, the computation width
///   twice the page, saturating at its maximum, so the resolver can prove which
///   candidates fit. Over-budget walks produce `?`, approximate. Successful
///   text has no carriage return or tab; layout-owned endings are line feeds.
///   Computation width is never narrower than the page.
/// - provides: the one path both entry points take.
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
/// - witness: `goldens::tests::arrow_chain_breaks_before_each_continuation`
/// - witness: `goldens::tests::string_controls_stay_in_one_escaped_literal`
/// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
/// - witness: `goldens::tests::beyond_the_depth_limit_renders_deep`
/// - witness: `walk::tests::changing_source_is_still_bounded_by_the_walk_budget`
#[spec(ensures: |ref ret| match *ret {
    Ok(ref presentation) => !presentation.as_ref().contains(['\r', '\t']),
    Err(PresentationError::Render(RenderError::InvalidWidth)) => false,
    Err(_) => true,
})]
fn present<S>(
    source: &S,
    root: S::Node,
    admits: Admits,
    page: PageWidth,
) -> Result<Presentation, PresentationError>
where
    S: Source + ?Sized,
{
    let mut meter = BuildMeter::new(BuildLimits::default());
    let mut builder = DocBuilder::try_new(&mut meter)?;
    let (doc, fidelity) = match walk(source, root, admits, &mut builder)? {
        | Walked::Built { doc, fidelity } => (doc, fidelity),
        | Walked::OverBudget => (builder.text(TextSource::from("?"))?, Fidelity::Approximate),
    };
    let arena = builder.finish()?;
    let computation = ComputationWidth::from(u32::from(page).saturating_mul(2_u32));
    let options = LayoutOptions::try_new(page, computation, PhysicalLineEnding::Lf)?;
    let mut render_meter = RenderMeter::new(RenderLimits::default());
    let rendered = render(&arena, doc, &options, &mut render_meter)?;
    Ok(Presentation {
        text: rendered.text,
        fidelity,
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
