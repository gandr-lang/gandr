//! One report — a refusal, an unsettled declaration or a goal — at the source
//! it sits in, and the snippet it renders as.
//!
//! # The class says whose fact the report is
//!
//! A refusal is classed by the [`FailureClass`] its producer's classifier
//! gives it, a declaration unsettled with no refusal produced by what its
//! unsettlement rests on, and a goal as a goal. The class labels the primary
//! locus; the title is the producer's message, and a refusal's vocabulary
//! name is the report's identifier, spelled as a `refuses` payload spells it.

use core::fmt;
use std::path::Path;

use annotate_snippets::AnnotationKind;
use annotate_snippets::Group;
use annotate_snippets::Level;
use annotate_snippets::Origin;
use annotate_snippets::Renderer;
use annotate_snippets::Snippet;
use annotate_snippets::renderer::DecorStyle;
use gandr_core_term::FailureClass;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::Surviving;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::OriginTable;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::locus::Annotation;
use crate::locus::Annotations;
use crate::locus::Checked;
use crate::locus::Label;
use crate::locus::context;
use crate::style::RenderStyle;
use crate::style::Rendered;

quenchant_shape::reason_enum! {
    /// Why a report claims no span.
    pub mod report_span {
        /// The reason a report is unlocated.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The refusal is about the run rather than a position in the
            /// source: an exhausted lowering allowance, or a tree molded under
            /// another grammar.
            Run,
            /// The refusal names a core node the origin table holds nothing
            /// for.
            Unrecorded,
            /// The span the producer recorded lies outside the source's text,
            /// or splits one of its characters.
            OutsideText,
        }
    }
}

/// The name a source with no path is rendered under.
const PATHLESS: &str = "<input>";

/// What a report is about, and whose fact it records.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Class
{
    /// A refusal, by whose fact it records: the refusal an unsettled
    /// declaration produced, or the lowering's refusal of a source as a whole.
    Refusal(FailureClass),
    /// A declaration unsettled with no refusal produced, by what its
    /// unsettlement rests on.
    Unsettled(Unsettlement),
    /// A declaration unsettled by its obligations alone, shown as a goal
    /// under `check --goals`.
    Goal,
}

impl fmt::Display for Class
{
    /// Writes the failure class, the unsettlement, or `goal`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Refusal(class) => fmt::Display::fmt(&class, f),
            | Self::Unsettled(unsettlement) => fmt::Display::fmt(&unsettlement, f),
            | Self::Goal => f.write_str("goal"),
        }
    }
}

/// What the unsettlement of a declaration that produced no refusal rests on.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unsettlement
{
    /// It states *checks* and produced *checks*, owing another count.
    Obligations,
    /// It states a refusal it did not produce.
    Unproduced,
    /// Its expectation states no verdict.
    Malformed,
}

impl fmt::Display for Unsettlement
{
    /// Writes what the unsettlement rests on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Obligations => "surviving obligations",
            | Self::Unproduced => "unproduced refusal",
            | Self::Malformed => "malformed expectation",
        })
    }
}

/// What one report is about.
#[derive(Clone, Copy, Debug)]
pub enum Subject<'step>
{
    /// A declaration unsettled by the refusal it produced.
    Refused
    {
        /// The declaration, as the settle comparison reported it.
        declaration: &'step DeclarationReport<'step>,
        /// The refusal it produced.
        refusal: Refusal<'step>,
        /// The table its core nodes are located through.
        origins: &'step OriginTable,
    },
    /// A declaration unsettled with no refusal produced.
    Unsettled
    {
        /// The declaration, as the settle comparison reported it.
        declaration: &'step DeclarationReport<'step>,
        /// What its unsettlement rests on.
        unsettlement: Unsettlement,
    },
    /// A declaration unsettled by its obligations alone, under
    /// `check --goals`.
    Goal(&'step DeclarationReport<'step>),
    /// A source the lowering refused as a whole, where its root expects
    /// declarations.
    Source(LoweringRefusal<'step>),
}

/// One refusal, unsettled declaration or goal, at the source it sits in.
#[derive(Clone, Copy, Debug)]
pub struct Report<'step>
{
    /// The source's path, as the walk reached it; empty for a source with no
    /// file.
    path: &'step Path,
    /// The source's text, which every span of the subject is measured against.
    text: SourceText<'step>,
    /// What the report is about.
    subject: Subject<'step>,
}

impl<'step> Report<'step>
{
    /// The report on `subject`, a part of the source at `path` whose text is
    /// `text`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(
        path: &'step Path,
        text: SourceText<'step>,
        subject: Subject<'step>,
    ) -> Self
    {
        Self {
            path,
            text,
            subject,
        }
    }

    /// The path of the source the report is about.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn path(&self) -> &'step Path
    {
        self.path
    }

    /// What the report is about, and whose fact it records.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused declaration and a source refused as a whole are
    ///   [`Class::Refusal`] with the class their producer's classifier gives; a
    ///   declaration unsettled with no refusal is [`Class::Unsettled`] with
    ///   what it rests on; a goal is [`Class::Goal`].
    /// - provides: the class a reader sorts reports by, and the label of the
    ///   primary locus.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one report of each subject is asserted at its exact
    ///   class: a lowering refusal and a checker refusal of the malformed
    ///   source class, a corpus refusal, a whole-source refusal of the
    ///   unrepresentable class, an unproduced refusal and a goal.
    /// - witness: `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`
    /// - witness: `diagnostics::diagnostics::an_unsettled_declaration_renders_as_its_golden`
    /// - witness: `diagnostics::diagnostics::a_goal_renders_as_its_golden`
    #[inline]
    #[must_use]
    pub fn class(&self) -> Class
    {
        match self.subject {
            | Subject::Refused { refusal, .. } => Class::Refusal(refusal.classify()),
            | Subject::Unsettled { unsettlement, .. } => Class::Unsettled(unsettlement),
            | Subject::Goal(_) => Class::Goal,
            | Subject::Source(refusal) => Class::Refusal(refusal.classify()),
        }
    }

    /// The bytes the report is about: its primary locus.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the span the producer recorded for the subject — a lowering
    ///   or corpus refusal's own span, the origin of the node a checker refusal
    ///   names, or the declaration's span for an unsettled declaration, a goal,
    ///   or a checker refusal about the declaration as a whole — when it lies
    ///   inside the source's text on character boundaries.
    /// - provides: the position a face marks, read from the producer and never
    ///   from a search of the text.
    /// - fails: never; an unlocated report is the [`report_span::Absent`]
    ///   absence: [`Run`] for a lowering refusal about the run, [`Unrecorded`]
    ///   for a node the origin table holds nothing for, [`OutsideText`] for a
    ///   span the text cannot answer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a checker refusal located through the origin table, a
    ///   lowering refusal at its own span and a declaration-wide report are
    ///   each asserted at their exact span, and a span outside the text is
    ///   asserted unlocated.
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    /// - witness: `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`
    /// - witness: `diagnostics::diagnostics::a_span_outside_the_text_is_unlocated`
    ///
    /// [`Run`]: report_span::Absent::Run
    /// [`Unrecorded`]: report_span::Absent::Unrecorded
    /// [`OutsideText`]: report_span::Absent::OutsideText
    #[inline]
    pub fn span(&self) -> Maybe<ByteSpan, report_span::Absent>
    {
        match self.annotations().primary {
            | Maybe::Present(primary) => Maybe::Present(primary.span),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The report as a source snippet, laid out in `style`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the first line is the level — `error`, or `goal` for a goal —
    ///   with a refusal's vocabulary name as its identifier, and the title: the
    ///   producer's message for a refusal, what the declaration states and
    ///   produced otherwise. A located report then quotes the lines its loci
    ///   cover under the source's path, line and column, the primary locus
    ///   underlined and labelled with the class or the surviving obligations,
    ///   each context locus marked with what it explains; an unlocated report
    ///   names the source's path alone. A refused declaration closes with a
    ///   note naming it and what it states. A source with an empty path is
    ///   named `<input>`. [`RenderStyle::Plain`] writes no escape sequence;
    ///   [`RenderStyle::Styled`] colours the same text.
    /// - provides: the plain text the driver prints and the tests compare.
    /// - fails: never.
    /// - panics: none; every span reaches the snippet backend checked against
    ///   the text.
    /// - intension: the backend chooses the source window and the connector
    ///   layout; the loci it receives are exactly the producer's.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — one pinned golden per kind, a refusal with two loci,
    ///   an unsettled declaration and a goal, compared byte for byte; L3 for
    ///   the residue — a pathless report names `<input>` and keeps its causal
    ///   context, a context locus keeps its own span and label, and styling
    ///   adds escape sequences to the plain text's content.
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    /// - witness: `diagnostics::diagnostics::an_unsettled_declaration_renders_as_its_golden`
    /// - witness: `diagnostics::diagnostics::a_goal_renders_as_its_golden`
    /// - witness: `diagnostics::diagnostics::a_pathless_report_names_input_and_renders_causal_context`
    /// - witness: `diagnostics::diagnostics::a_labeled_context_retains_its_locus_and_cause`
    /// - witness: `diagnostics::diagnostics::forced_styling_colors_actual_facade_annotations`
    #[inline]
    #[must_use]
    pub fn render(
        &self,
        style: RenderStyle,
    ) -> Rendered
    {
        let annotations = self.annotations();
        let title = Title(self.subject).to_string();
        let level = match self.subject {
            | Subject::Goal(_) => Level::INFO.with_name("goal"),
            | Subject::Refused { .. } | Subject::Unsettled { .. } | Subject::Source(_) => {
                Level::ERROR
            },
        };
        let spelling = match self.subject {
            | Subject::Refused { refusal, .. } => Maybe::Present(refusal.name().spelling()),
            | Subject::Source(refusal) => {
                Maybe::Present(Refusal::Lowering(refusal).name().spelling())
            },
            | Subject::Unsettled { .. } | Subject::Goal(_) => {
                Maybe::Absent(unnamed::Absent::Statement)
            },
        };
        let message = match spelling {
            | Maybe::Present(ref spelling) => {
                level.primary_title(title.as_str()).id(spelling.as_ref())
            },
            | Maybe::Absent(unnamed::Absent::Statement) => level.primary_title(title.as_str()),
        };
        let origin = if self.path.as_os_str().is_empty() {
            PATHLESS.to_owned()
        }
        else {
            self.path.display().to_string()
        };
        let [first, second] = annotations.context;
        let primary_label = labelled(annotations.primary);
        let first_label = labelled(first);
        let second_label = labelled(second);
        let range = |annotation: Annotation| {
            usize::from(annotation.span.start()) .. usize::from(annotation.span.end())
        };
        let mut group = Group::with_title(message);
        match annotations.primary {
            | Maybe::Present(primary) => {
                let mut snippet = Snippet::source(self.text.as_ref())
                    .path(origin.as_str())
                    .annotation(
                        AnnotationKind::Primary
                            .span(range(primary))
                            .label(primary_label.as_str()),
                    );
                for (annotation, label) in [(first, &first_label), (second, &second_label)] {
                    if let Maybe::Present(annotation) = annotation {
                        snippet = snippet.annotation(
                            AnnotationKind::Context
                                .span(range(annotation))
                                .label(label.as_str()),
                        );
                    }
                }
                group = group.element(snippet);
            },
            | Maybe::Absent(_) => {
                group = group.element(Origin::path(origin.as_str()));
            },
        }
        let note = match self.subject {
            | Subject::Refused { declaration, .. } => Maybe::Present(Note(declaration).to_string()),
            | Subject::Unsettled { .. } | Subject::Goal(_) | Subject::Source(_) => {
                Maybe::Absent(unnamed::Absent::Statement)
            },
        };
        if let Maybe::Present(ref note) = note {
            group = group.element(Level::NOTE.message(note.as_str()));
        }
        let renderer = match style {
            | RenderStyle::Plain => Renderer::plain(),
            | RenderStyle::Styled => Renderer::styled(),
        };
        Rendered::from(renderer.decor_style(DecorStyle::Unicode).render(&[group]))
    }

    /// Every locus the report marks, each checked against the source's text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the subject's loci as its producer recorded them; a primary
    ///   locus the text cannot answer becomes the
    ///   [`report_span::Absent::OutsideText`] absence, and such a context locus
    ///   is dropped.
    /// - provides: the only loci [`Report::span`] and [`Report::render`] read.
    /// - fails: never.
    /// - panics: none.
    fn annotations(&self) -> Annotations
    {
        let annotations = match self.subject {
            | Subject::Refused {
                declaration,
                refusal,
                origins,
            } => Annotations::refusal(refusal, declaration.span(), origins),
            | Subject::Unsettled {
                declaration,
                unsettlement: Unsettlement::Obligations,
            }
            | Subject::Goal(declaration) => Annotations::at(
                declaration.span(),
                Label::Surviving(declaration.surviving()),
            ),
            | Subject::Unsettled {
                declaration,
                unsettlement: unsettlement @ (Unsettlement::Unproduced | Unsettlement::Malformed),
            } => Annotations::at(
                declaration.span(),
                Label::Class(Class::Unsettled(unsettlement)),
            ),
            | Subject::Source(refusal) => {
                Annotations::lowering(refusal, Class::Refusal(refusal.classify()))
            },
        };
        let inside = |annotation: &Annotation| self.text.fragment(annotation.span).is_ok();
        let primary = match annotations.primary {
            | Maybe::Present(primary) if inside(&primary) => Maybe::Present(primary),
            | Maybe::Present(_) => Maybe::Absent(report_span::Absent::OutsideText),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        let [first, second] = annotations.context.map(|annotation| match annotation {
            | Maybe::Present(annotation) if inside(&annotation) => Maybe::Present(annotation),
            | Maybe::Present(_) => Maybe::Absent(context::Absent::OutsideText),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        });
        Annotations {
            primary,
            context: [first, second],
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a report carries no identifier or note.
    mod unnamed {
        /// The reason a report part is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The report states what a declaration states and produced: it
            /// carries no refusal to name, and its title is its statement.
            Statement,
        }
    }
}

/// The text of an annotation's label, or the empty text for a locus absent.
///
/// # Specification
/// trivial.
fn labelled<Reason>(annotation: Maybe<Annotation, Reason>) -> String
where
    Reason: Copy,
{
    match annotation {
        | Maybe::Present(annotation) => annotation.label.to_string(),
        | Maybe::Absent(_) => String::new(),
    }
}

/// A report's title.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Title<'step>(Subject<'step>);

impl fmt::Display for Title<'_>
{
    /// Writes the producer's message for a refusal, and what the declaration
    /// states and produced otherwise.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
            | Subject::Refused {
                refusal: Refusal::Lowering(refusal),
                ..
            } => fmt::Display::fmt(&refusal, f),
            | Subject::Refused {
                refusal: Refusal::Checking(refusal),
                ..
            } => fmt::Display::fmt(&Checked(refusal), f),
            | Subject::Refused {
                refusal: Refusal::Corpus(refusal),
                ..
            } => fmt::Display::fmt(&refusal, f),
            | Subject::Unsettled { declaration, .. } | Subject::Goal(declaration) => write!(
                f,
                "`{}` states {}; produced {}",
                declaration.name(),
                declaration.stated(),
                declaration.outcome()
            ),
            | Subject::Source(refusal) => {
                write!(f, "the lowering refused the source as a whole: {refusal}")
            },
        }
    }
}

/// The note a refused declaration closes with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Note<'step>(&'step DeclarationReport<'step>);

impl fmt::Display for Note<'_>
{
    /// Writes the declaration's settlement, its name, what it states, and the
    /// obligations that survive when any do.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{} `{}` states {}",
            self.0.settlement(),
            self.0.name(),
            self.0.stated()
        )?;
        let surviving = self.0.surviving();
        if surviving != Surviving::default() {
            write!(f, "; surviving obligations: {surviving}")?;
        }
        Ok(())
    }
}
