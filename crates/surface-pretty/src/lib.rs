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
//! | [`PresentationError`]         | a layout ceiling reached on the way                      |
//!
//! # One spelling per former
//!
//! Every former has exactly one spelling, the one the surface grammar parses:
//! `Integer`, `String`, `Unit`, `A * B`, `A + B`, `+U C`, `-F A`, `A -> C`,
//! `(x : A) -> C`, `Type`, `Type[-]`, `Type[+, l]`, `Type[-, l]`; `()`,
//! literals, `(a, b)`, `Inl(v)`, `Inr(v)`. A former the surface does not write
//! — a lift, the numeric atom, a variable past every binder — is written `?`,
//! and the presentation is then [`Fidelity::Approximate`]. A page the
//! one-line spelling fits selects it unchanged.
//!
//! # Totality
//!
//! Nothing here panics or recurses. The walk drains an explicit task stack, a
//! value deeper than [`DEPTH_LIMIT`] is written `<deep>`, a source that takes
//! more node visits than one presentation makes — a cycle — is written `?`,
//! and every layout failure is a [`PresentationError`].

#![no_std]

extern crate alloc;

mod core_source;
mod error;
mod former;
mod walk;

use core::fmt;

use gandr_surface_layout::ComputationWidth;
use gandr_surface_layout::LayoutOptions;
pub use gandr_surface_layout::PageWidth;
use gandr_surface_layout::PhysicalLineEnding;
use gandr_surface_layout::RenderLimits;
use gandr_surface_layout::RenderMeter;
use gandr_surface_layout::arena::TextSource;
use gandr_surface_layout::build::DocBuilder;
use gandr_surface_layout::limits::BuildLimits;
use gandr_surface_layout::limits::BuildMeter;
use gandr_surface_layout::render::RenderedText;
use gandr_surface_layout::render::render;

pub use crate::core_source::CoreNode;
pub use crate::core_source::CoreSource;
pub use crate::error::PresentationError;
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
    /// trivial.
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
///   written `?`.
/// - provides: the type a transcript line, a hover or a diagnostic names.
/// - fails: a layout ceiling reached while building or rendering.
/// - panics: none.
///
/// # Errors
/// Returns [`PresentationError::Build`] or [`PresentationError::Render`] when
/// the layout engine refuses, and [`PresentationError::Unbalanced`] on a
/// defect in the walk's own bookkeeping.
///
/// # Adequacy
/// - hypothesis: L3 — every type former of the core is asserted at its exact
///   spelling, and the dependent arrow and an arrow chain at both page widths.
/// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `goldens::tests::dependent_function_type_breaks_before_codomain`
/// - witness: `goldens::tests::long_dependent_function_type_breaks_at_the_narrow_page`
/// - witness: `goldens::tests::arrow_chain_breaks_before_each_continuation`
/// - witness: `goldens::tests::nullary_declared_data_uses_its_bare_name`
/// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
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
///   formers spelled `()`, as their literal, `(a, b)`, `Inl(v)` and `Inr(v)`, a
///   constant by its name and the code of a type as the type; a thunk is
///   written `<thunk>`, and a value [`DEPTH_LIMIT`] value formers deep is
///   written `<deep>` inside the formers around it, each making the
///   presentation approximate.
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
///   values read back from evaluation.
/// - witness: `goldens::tests::string_controls_stay_in_one_escaped_literal`
/// - witness: `goldens::tests::pair_of_injections_pins_sum_notation`
/// - witness: `goldens::tests::record_value_breaks_fields_at_the_narrow_page`
/// - witness: `goldens::tests::beyond_the_depth_limit_renders_deep`
/// - witness: `goldens::tests::fidelity_follows_nodes_not_the_characters_of_a_name`
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
///   twice the page so the resolver can prove which candidates fit; `?`,
///   approximate, when the walk is over budget.
/// - provides: the one path both entry points take.
/// - fails: as [`present_type`].
/// - panics: none.
///
/// # Errors
/// As [`present_type`].
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
