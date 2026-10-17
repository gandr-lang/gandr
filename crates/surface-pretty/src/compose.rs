//! Where the walk writes its document.
//!
//! The walk spells every former once, through [`Compose`]: a leaf's glyphs,
//! the joins between pieces, and the places a line may break. Two composers
//! receive it.
//!
//! - [`Paged`] writes into the layout engine's builder, so a face that lays a
//!   presentation out at a page — a hover, a diagnostic, the formatter's
//!   operand — gets the resolver's choice of breaks.
//! - [`OneLine`] writes the text itself, for a spelling read as one line — a
//!   value a run prints — that is never laid out: every soft line a space, as
//!   the root's group reads it flat, and each choice by the alternative with
//!   fewer hard breaks, the left on a tie. That is the layout the resolver
//!   selects at a page no line overflows, without building the document or
//!   searching it for breaks.
//!
//! The decision: one walk and two receivers, rather than a second printer for
//! values or a flat render of the built document. A second printer would spell
//! every former twice and drift; a flat render still pays for the document's
//! interning, its flattened images and its validation, which cost a run's
//! value more than the run. Reversal: a one-line face whose output must follow
//! a cost only the resolver decides.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_surface_layout::arena::DocId;
use gandr_surface_layout::arena::TextSource;
use gandr_surface_layout::build::DocBuilder;
use gandr_surface_layout::units::NestAmount;

use crate::PresentationError;

/// One document the walk composed, by the composer's own count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Doc(u32);

impl Doc
{
    /// The document with nothing in it.
    pub const EMPTY: Self = Self(0);
    /// A line break that survives flattening.
    pub const HARD_LINE: Self = Self(2);
    /// A soft line break.
    pub const LINE: Self = Self(1);
}

/// The glyphs of one leaf, never holding a line break.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Glyphs<'text>(pub &'text str);

/// What the walk writes its document into.
///
/// # Specification
/// - requires: every [`Doc`] passed back came from the same composer.
/// - ensures: the composed document is the walk's spelling: [`Paged`] the
///   layout engine's document, [`OneLine`] its text on as few lines as it
///   admits.
/// - panics: none.
/// - executable: none — the trait carries no body of its own; each composer's
///   witnesses compare its output.
///
/// # Adequacy
/// - hypothesis: L3 — as [`OneLine`].
/// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
pub trait Compose
{
    /// The leaf `glyphs`.
    ///
    /// # Specification
    /// trivial.
    fn text(
        &mut self,
        glyphs: Glyphs<'_>,
    ) -> Result<Doc, PresentationError>;

    /// `left`, then `right`.
    ///
    /// # Specification
    /// trivial.
    fn concat(
        &mut self,
        left: Doc,
        right: Doc,
    ) -> Result<Doc, PresentationError>;

    /// Each of `docs` in order.
    ///
    /// # Specification
    /// trivial.
    fn concat_all(
        &mut self,
        docs: &[Doc],
    ) -> Result<Doc, PresentationError>;

    /// `doc`, each of its line breaks indented `amount` further.
    ///
    /// # Specification
    /// trivial.
    fn nest(
        &mut self,
        amount: NestAmount,
        doc: Doc,
    ) -> Result<Doc, PresentationError>;

    /// `left` or `right`, whichever lays out better; `left` on a tie.
    ///
    /// # Specification
    /// trivial.
    fn choice(
        &mut self,
        left: Doc,
        right: Doc,
    ) -> Result<Doc, PresentationError>;

    /// `doc` on one line where it fits, as laid out otherwise.
    ///
    /// # Specification
    /// trivial.
    fn group(
        &mut self,
        doc: Doc,
    ) -> Result<Doc, PresentationError>;
}

/// The document `doc` numbers among `docs`.
///
/// # Specification
/// - requires: `docs` are the composer's documents by position.
/// - ensures: the document at `doc`'s position.
/// - fails: [`PresentationError::Unbalanced`] for a position past the end, a
///   document the composer never numbered.
/// - panics: none.
/// - executable: none — a foreign document is a walk defect, which the walk's
///   own witnesses would show as an unbalanced presentation.
///
/// # Adequacy
/// - hypothesis: L3 — every golden spelling is composed through it.
/// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
fn held<T>(
    docs: &[T],
    doc: Doc,
) -> Result<&T, PresentationError>
{
    usize::try_from(doc.0)
        .ok()
        .and_then(|at| docs.get(at))
        .ok_or(PresentationError::Unbalanced)
}

/// Number `kept` as the next of `docs`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `kept` appended, numbered by its position.
/// - fails: [`PresentationError::Unbalanced`] past `u32::MAX` documents, a
///   ceiling beyond any walk's budget.
/// - panics: none.
/// - executable: none — the ceiling is four billion documents.
///
/// # Adequacy
/// - hypothesis: L3 — every golden spelling is composed through it.
/// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
fn numbered<T>(
    docs: &mut Vec<T>,
    kept: T,
) -> Result<Doc, PresentationError>
{
    let doc = u32::try_from(docs.len())
        .map(Doc)
        .map_err(|_overflow| PresentationError::Unbalanced)?;
    docs.push(kept);
    Ok(doc)
}

/// The layout engine's builder as a composer: every document the walk
/// composes is the builder's, numbered in the order composed.
#[derive(Debug)]
pub struct Paged<'builder, 'meter>
{
    /// The builder every document is written into.
    builder: &'builder mut DocBuilder<'meter>,
    /// The builder's handle of each document, by position.
    docs: Vec<DocId>,
}

impl<'builder, 'meter> Paged<'builder, 'meter>
{
    /// A composer writing into `builder`.
    ///
    /// # Specification
    /// trivial.
    pub fn new(builder: &'builder mut DocBuilder<'meter>) -> Self
    {
        let docs = Vec::from([builder.empty(), builder.line(), builder.hard_line()]);
        Self { builder, docs }
    }

    /// The builder's handle of `doc`.
    ///
    /// # Specification
    /// - requires: `doc` came from this composer.
    /// - ensures: the handle the builder minted for `doc`.
    /// - fails: [`PresentationError::Unbalanced`] for a document this composer
    ///   never numbered.
    /// - panics: none.
    /// - executable: none — a foreign document is a walk defect, which the
    ///   walk's own witnesses would show as an unbalanced presentation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every laid-out golden is rendered from it.
    /// - witness: `goldens::tests::arrow_chain_breaks_before_each_continuation`
    pub fn handle(
        &self,
        doc: Doc,
    ) -> Result<DocId, PresentationError>
    {
        held(&self.docs, doc).copied()
    }

    /// Number `handle` as the next document.
    ///
    /// # Specification
    /// trivial.
    fn keep(
        &mut self,
        handle: DocId,
    ) -> Result<Doc, PresentationError>
    {
        numbered(&mut self.docs, handle)
    }
}

impl Compose for Paged<'_, '_>
{
    /// The builder's leaf `glyphs`.
    ///
    /// # Specification
    /// trivial.
    fn text(
        &mut self,
        glyphs: Glyphs<'_>,
    ) -> Result<Doc, PresentationError>
    {
        let handle = self.builder.text(TextSource::from(glyphs.0))?;
        self.keep(handle)
    }

    /// The builder's concatenation.
    ///
    /// # Specification
    /// trivial.
    fn concat(
        &mut self,
        left: Doc,
        right: Doc,
    ) -> Result<Doc, PresentationError>
    {
        let handle = self
            .builder
            .concat(self.handle(left)?, self.handle(right)?)?;
        self.keep(handle)
    }

    /// The builder's concatenation of every document.
    ///
    /// # Specification
    /// trivial.
    fn concat_all(
        &mut self,
        docs: &[Doc],
    ) -> Result<Doc, PresentationError>
    {
        let handles = docs
            .iter()
            .map(|&doc| self.handle(doc))
            .collect::<Result<Vec<_>, _>>()?;
        let handle = self.builder.concat_all(handles)?;
        self.keep(handle)
    }

    /// The builder's nesting.
    ///
    /// # Specification
    /// trivial.
    fn nest(
        &mut self,
        amount: NestAmount,
        doc: Doc,
    ) -> Result<Doc, PresentationError>
    {
        let handle = self.builder.nest(amount, self.handle(doc)?)?;
        self.keep(handle)
    }

    /// The builder's choice, the resolver's to make.
    ///
    /// # Specification
    /// trivial.
    fn choice(
        &mut self,
        left: Doc,
        right: Doc,
    ) -> Result<Doc, PresentationError>
    {
        let handle = self
            .builder
            .choice(self.handle(left)?, self.handle(right)?)?;
        self.keep(handle)
    }

    /// The builder's group.
    ///
    /// # Specification
    /// trivial.
    fn group(
        &mut self,
        doc: Doc,
    ) -> Result<Doc, PresentationError>
    {
        let handle = self.builder.group(self.handle(doc)?)?;
        self.keep(handle)
    }
}

/// One composed text and the hard line breaks it holds.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Written
{
    /// The text.
    text: String,
    /// How many line breaks it holds.
    breaks: u32,
}

/// The text itself as a composer, on as few lines as the document admits.
///
/// # Specification
/// - requires: the walk's root is a group, so every soft line reads flat.
/// - ensures: every soft line a space; each choice the alternative with fewer
///   line breaks, the left on a tie; a surviving break a line feed and the
///   indentation its nesting adds.
/// - panics: none.
/// - executable: none — the composer is exercised through
///   [`crate::present_computation_line`], whose witness compares its text with
///   the resolver's at a page no line overflows.
///
/// # Adequacy
/// - hypothesis: L3 — elaborated bodies with binds, blocks, calls and case
///   analyses written on one line equal their layout at a page no line
///   overflows; a choice taken the wrong way or a soft line kept as a break
///   changes the text.
/// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OneLine
{
    /// Each document composed, by position.
    docs: Vec<Written>,
}

impl OneLine
{
    /// A composer holding the empty document and the two line breaks.
    ///
    /// # Specification
    /// trivial.
    pub fn new() -> Self
    {
        Self {
            docs: Vec::from([
                Written::default(),
                Written {
                    text: String::from(" "),
                    breaks: 0_u32,
                },
                Written {
                    text: String::from("\n"),
                    breaks: 1_u32,
                },
            ]),
        }
    }

    /// The text of `doc`.
    ///
    /// # Specification
    /// - requires: `doc` came from this composer.
    /// - ensures: the composed text.
    /// - fails: [`PresentationError::Unbalanced`] for a document this composer
    ///   never numbered.
    /// - panics: none.
    /// - executable: none — as [`Paged::handle`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OneLine`].
    /// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
    pub fn into_text(
        mut self,
        doc: Doc,
    ) -> Result<String, PresentationError>
    {
        let at = usize::try_from(doc.0).map_err(|_overflow| PresentationError::Unbalanced)?;
        if at >= self.docs.len() {
            return Err(PresentationError::Unbalanced);
        }
        Ok(self.docs.swap_remove(at).text)
    }

    /// The composed text and breaks of `doc`.
    ///
    /// # Specification
    /// trivial.
    fn written(
        &self,
        doc: Doc,
    ) -> Result<&Written, PresentationError>
    {
        held(&self.docs, doc)
    }

    /// Number `written` as the next document.
    ///
    /// # Specification
    /// trivial.
    fn keep(
        &mut self,
        written: Written,
    ) -> Result<Doc, PresentationError>
    {
        numbered(&mut self.docs, written)
    }
}

impl Compose for OneLine
{
    /// The glyphs as they stand.
    ///
    /// # Specification
    /// trivial.
    fn text(
        &mut self,
        glyphs: Glyphs<'_>,
    ) -> Result<Doc, PresentationError>
    {
        self.keep(Written {
            text: String::from(glyphs.0),
            breaks: 0_u32,
        })
    }

    /// `left` then `right`.
    ///
    /// # Specification
    /// trivial.
    fn concat(
        &mut self,
        left: Doc,
        right: Doc,
    ) -> Result<Doc, PresentationError>
    {
        self.concat_all(&[left, right])
    }

    /// Each document's text in order, the line breaks summed.
    ///
    /// # Specification
    /// trivial.
    fn concat_all(
        &mut self,
        docs: &[Doc],
    ) -> Result<Doc, PresentationError>
    {
        // A concatenation of one written document is that document, uncopied.
        let mut written = docs
            .iter()
            .copied()
            .filter(|&doc| self.written(doc).is_ok_and(|held| !held.text.is_empty()));
        if let (Some(only), None) = (written.next(), written.next()) {
            return Ok(only);
        }
        let mut text = String::new();
        let mut breaks = 0_u32;
        for &doc in docs {
            let held = self.written(doc)?;
            text.push_str(&held.text);
            breaks = breaks.saturating_add(held.breaks);
        }
        if text.is_empty() {
            return Ok(Doc::EMPTY);
        }
        self.keep(Written { text, breaks })
    }

    /// `doc` with each line feed followed by `amount` more spaces.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a flat document is its own nest; a broken one gains
    ///   the indentation after each line feed.
    /// - witness: `compose::tests::a_nest_indents_each_line_feed_and_leaves_a_flat_document_itself`
    fn nest(
        &mut self,
        amount: NestAmount,
        doc: Doc,
    ) -> Result<Doc, PresentationError>
    {
        let written = self.written(doc)?;
        if written.breaks == 0_u32 {
            return Ok(doc);
        }
        let indentation = " ".repeat(usize::try_from(u32::from(amount)).unwrap_or(usize::MAX));
        let text = written
            .text
            .replace('\n', &alloc::format!("\n{indentation}"));
        let breaks = written.breaks;
        self.keep(Written { text, breaks })
    }

    /// The alternative with fewer line breaks, `left` on a tie.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tie and a strictly fewer-broken right.
    /// - witness: `compose::tests::a_choice_takes_fewer_breaks_and_the_left_on_a_tie`
    fn choice(
        &mut self,
        left: Doc,
        right: Doc,
    ) -> Result<Doc, PresentationError>
    {
        let fewer = self.written(right)?.breaks < self.written(left)?.breaks;
        Ok(if fewer { right } else { left })
    }

    /// `doc` itself: every soft line already reads flat.
    ///
    /// # Specification
    /// trivial.
    fn group(
        &mut self,
        doc: Doc,
    ) -> Result<Doc, PresentationError>
    {
        Ok(doc)
    }
}

#[cfg(test)]
mod tests
{
    use gandr_surface_layout::units::NestAmount;

    use super::Compose as _;
    use super::Doc;
    use super::Glyphs;
    use super::OneLine;

    #[test]
    fn a_nest_indents_each_line_feed_and_leaves_a_flat_document_itself()
    {
        let mut one = OneLine::new();
        let flat = one.text(Glyphs("x y")).expect("a leaf composes");
        assert_eq!(
            flat,
            one.nest(NestAmount::from(2_u32), flat)
                .expect("a nest composes"),
            "a document with no break is its own nest"
        );
        let head = one.text(Glyphs("x")).expect("a leaf composes");
        let tail = one.text(Glyphs("y")).expect("a leaf composes");
        let broken = one
            .concat_all(&[head, Doc::HARD_LINE, tail])
            .expect("a concatenation composes");
        let nested = one
            .nest(NestAmount::from(2_u32), broken)
            .expect("a nest composes");
        assert_eq!(
            "x\n  y",
            one.into_text(nested).expect("the nest is numbered")
        );
    }

    #[test]
    fn a_choice_takes_fewer_breaks_and_the_left_on_a_tie()
    {
        let mut one = OneLine::new();
        let left = one.text(Glyphs("left")).expect("a leaf composes");
        let right = one.text(Glyphs("right")).expect("a leaf composes");
        assert_eq!(
            left,
            one.choice(left, right).expect("a choice composes"),
            "a tie"
        );
        let broken = one
            .concat(left, Doc::HARD_LINE)
            .expect("a concatenation composes");
        assert_eq!(
            right,
            one.choice(broken, right).expect("a choice composes"),
            "the alternative with fewer breaks"
        );
    }
}
