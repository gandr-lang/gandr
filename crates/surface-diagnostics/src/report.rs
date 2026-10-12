//! One report — a refusal, an unsettled declaration, a goal or a warning — at
//! the source it sits in, and the snippet it renders as.
//!
//! # The class says whose fact the report is; the label says what the bytes are
//!
//! A refusal is classed by the [`FailureClass`] its producer's classifier
//! gives it, a declaration unsettled with no refusal produced by what its
//! unsettlement rests on, a goal as a goal, and a builtin the source shadowed
//! as a warning. The class sorts reports; the primary locus is labelled with
//! what its bytes are, never with the class. The title is the producer's
//! message, which names no byte offsets, and a refusal's vocabulary name is
//! the report's identifier, spelled as a `refuses` payload spells it.
//!
//! # A shadowed builtin is a warning, named as the refusal it would be
//!
//! Under the warn-and-allow shadow policy, the default, a declaration or a
//! binder over a builtin name wins and the lowering records the shadowing; the
//! report on it is a warning, which settles nothing and fails no run. Its
//! identifier is `ShadowedBuiltin`, the refusal the reject policy files for
//! the same bytes, so one name reads the same fact under either policy.

use core::fmt;
use std::path::Path;

use annotate_snippets::AnnotationKind;
use annotate_snippets::Group;
use annotate_snippets::Level;
use annotate_snippets::Origin;
use annotate_snippets::Renderer;
use annotate_snippets::Snippet;
use annotate_snippets::renderer::DecorStyle;
use anodized::spec;
use gandr_core_checker::Pending;
use gandr_core_term::FailureClass;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::RefusalName;
use gandr_surface_corpus::RefusalSpelling;
use gandr_surface_corpus::Surviving;
use gandr_surface_dispatcher::Spellings;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::OriginTable;
use gandr_surface_lowering::namespace::ShadowedBuiltin;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::culprit::Culprit;
use crate::locus::Annotation;
use crate::locus::Annotations;
use crate::locus::Checked;
use crate::locus::Comparison;
use crate::locus::Label;
use crate::locus::PrimaryLabel;
use crate::locus::Reason;
use crate::locus::report_context;
use crate::message::Plain;
use crate::style::RenderStyle;
use crate::style::Rendered;
use crate::style::Verbosity;

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

quenchant_shape::reason_enum! {
    /// Why a report carries no identifier.
    pub mod report_identifier {
        /// The reason a report names no refusal.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The report states what a declaration states and produced: it
            /// carries no refusal to name, and its title is its statement.
            Statement,
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
    /// A builtin name the source shadowed, which the source's binding won.
    Warning,
}

impl fmt::Display for Class
{
    /// Writes the failure class, the unsettlement, `goal` or `warning`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the producer's failure class, the unsettlement reason
    ///   or the goal label; propagates destination failure.
    /// - provides: the human-readable report class.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither output text nor an
    ///   independent destination-failure observer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the four unsettlement reasons remain distinguishable
    ///   from one refusal class and a goal. Collapsed labels change a finite
    ///   observation; other failure classes and destination errors are
    ///   excluded.
    /// - witness: `report::tests::class_labels_keep_their_decision_surfaces_distinct`
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
            | Self::Warning => f.write_str("warning"),
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
    /// It states a run outcome, and its run produced another.
    RunOutcome,
    /// Its expectation states no verdict.
    Malformed,
}

impl fmt::Display for Unsettlement
{
    /// Writes what the unsettlement rests on.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the reason the declaration did not settle.
    /// - provides: a distinguishable description of each unsettlement kind.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither output text nor an
    ///   independent destination-failure observer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all four unsettlement kinds have distinct public
    ///   class labels. A collapsed reason changes an observation; exact prose
    ///   and destination failures are outside this evidence.
    /// - witness: `report::tests::class_labels_keep_their_decision_surfaces_distinct`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Obligations => "surviving obligations",
            | Self::Unproduced => "unproduced refusal",
            | Self::RunOutcome => "another run outcome",
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
        /// The spellings of the types it compares.
        spellings: &'step Spellings,
        /// The judgements its body was refused inside, outermost first.
        pending: &'step [Pending],
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
    /// A builtin the source's declaration or binder shadowed, under the
    /// warn-and-allow policy.
    Shadowed(&'step ShadowedBuiltin),
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
    ///   what it rests on; a goal is [`Class::Goal`]; a shadowed builtin is
    ///   [`Class::Warning`].
    /// - provides: the class a reader sorts reports by and a face chooses a
    ///   severity from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite real reports expose the producer's exact class
    ///   across refused declarations and whole-source refusal. Unproduced
    ///   expectations and goals distinguish the non-refusal branches; arbitrary
    ///   checker payloads are outside these fixtures.
    /// - witness: `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`
    /// - witness: `diagnostics::diagnostics::an_unsettled_declaration_renders_as_its_golden`
    /// - witness: `diagnostics::diagnostics::a_goal_renders_as_its_golden`
    /// - witness: `diagnostics::diagnostics::each_verb_prints_its_entries`
    /// - witness: `diagnostics::diagnostics::a_shadowed_builtin_renders_as_a_warning`
    #[spec(ensures: |ret| ret == match self.subject {
        Subject::Refused { refusal, .. } => Class::Refusal(refusal.classify()),
        Subject::Unsettled { unsettlement, .. } => Class::Unsettled(unsettlement),
        Subject::Goal(_) => Class::Goal,
        Subject::Source(refusal) => Class::Refusal(refusal.classify()),
        Subject::Shadowed(_) => Class::Warning,
    })]
    #[inline]
    #[must_use]
    pub fn class(&self) -> Class
    {
        match self.subject {
            | Subject::Refused { refusal, .. } => Class::Refusal(refusal.classify()),
            | Subject::Unsettled { unsettlement, .. } => Class::Unsettled(unsettlement),
            | Subject::Goal(_) => Class::Goal,
            | Subject::Source(refusal) => Class::Refusal(refusal.classify()),
            | Subject::Shadowed(_) => Class::Warning,
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
    /// - hypothesis: L3 — real producer spans and finite UTF-8 boundary
    ///   fixtures distinguish exact location from out-of-text metadata. Split
    ///   characters and empty end positions expose accidental clamping. Other
    ///   producer/span combinations are not enumerated.
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    /// - witness: `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`
    /// - witness: `diagnostics::diagnostics::a_span_outside_the_text_is_unlocated`
    /// - witness: `report::tests::utf8_boundaries_are_checked_per_locus_without_clamping`
    ///
    /// [`Run`]: report_span::Absent::Run
    /// [`Unrecorded`]: report_span::Absent::Unrecorded
    /// [`OutsideText`]: report_span::Absent::OutsideText
    #[spec(ensures: |ret| match ret {
        Maybe::Present(span) => self.text.fragment(span).is_ok(),
        Maybe::Absent(_) => true,
    })]
    #[inline]
    pub fn span(&self) -> Maybe<ByteSpan, report_span::Absent>
    {
        match self.annotations().primary {
            | Maybe::Present(primary) => Maybe::Present(primary.span),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The vocabulary name of the refusal the report is about: the identifier
    /// its snippet's first line carries.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused declaration names the refusal it produced, a source
    ///   refused as a whole the lowering's refusal, and a shadowed builtin
    ///   `ShadowedBuiltin`, the refusal the reject policy files for it, each
    ///   spelled as a `refuses` payload spells it.
    /// - provides: the identifier [`Report::render`] writes, for a face that
    ///   carries it beside the message rather than in a snippet.
    /// - fails: never; an unsettled declaration and a goal carry no refusal to
    ///   name, the [`report_identifier::Absent::Statement`] absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — checker and lowering refusals expose stable
    ///   vocabulary identifiers; a goal exposes statement absence. These
    ///   distinguish missing or substituted identifiers on the finite fixture
    ///   subjects, not every refusal vocabulary member.
    /// - witness: `diagnostics::diagnostics::a_report_preserves_refusal_identity_and_title_payloads`
    #[spec(ensures: |ret| match (self.subject, ret) {
        (Subject::Refused { refusal, .. }, Maybe::Present(spelling)) => spelling == refusal.name().spelling(),
        (Subject::Source(refusal), Maybe::Present(spelling)) => spelling == Refusal::Lowering(refusal).name().spelling(),
        (Subject::Shadowed(_), Maybe::Present(spelling)) => spelling == RefusalName::ShadowedBuiltin.spelling(),
        (Subject::Unsettled { .. } | Subject::Goal(_), Maybe::Absent(report_identifier::Absent::Statement)) => true,
        _ => false,
    })]
    #[inline]
    pub fn identifier(&self) -> Maybe<RefusalSpelling, report_identifier::Absent>
    {
        match self.subject {
            | Subject::Refused { refusal, .. } => Maybe::Present(refusal.name().spelling()),
            | Subject::Source(refusal) => {
                Maybe::Present(Refusal::Lowering(refusal).name().spelling())
            },
            | Subject::Shadowed(_) => Maybe::Present(RefusalName::ShadowedBuiltin.spelling()),
            | Subject::Unsettled { .. } | Subject::Goal(_) => {
                Maybe::Absent(report_identifier::Absent::Statement)
            },
        }
    }

    /// The report's title: the producer's own text for what the report is
    /// about.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the producer's message for a refusal, what the declaration
    ///   states and produced for an unsettled declaration or a goal, the
    ///   lowering's refusal for a source refused as a whole, and the path a
    ///   shadowed builtin is bound at.
    /// - provides: the detail a face shows beside the [`Report::message`] it
    ///   leads with, for a reader who wants the producer's own words.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unresolved-name and goal titles preserve source names
    ///   and numeric roles; mismatch titles expose no core addresses. Distinct
    ///   stated/produced counts expose lost or swapped payloads. Other subjects
    ///   and natural-language wording are excluded.
    /// - witness: `diagnostics::diagnostics::a_report_preserves_refusal_identity_and_title_payloads`
    /// - witness: `diagnostics::diagnostics::a_shadowed_builtin_renders_as_a_warning`
    /// - witness: `report::tests::notes_and_titles_preserve_numeric_roles_and_omit_empty_survivors`
    #[spec(ensures: |ret| matches!((self.subject, ret.0),
        (Subject::Refused { .. }, Subject::Refused { .. })
            | (Subject::Unsettled { .. }, Subject::Unsettled { .. })
            | (Subject::Goal(_), Subject::Goal(_)) | (Subject::Source(_), Subject::Source(_))
            | (Subject::Shadowed(_), Subject::Shadowed(_))
    ))]
    #[inline]
    #[must_use]
    pub const fn title(&self) -> Title<'step>
    {
        Title(self.subject)
    }

    /// The report's message: what its snippet's first line says after the
    /// level and the identifier.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the plain message of a refusal, naming no grammar sort, node
    ///   or admission position; the title of every other report.
    /// - provides: the message [`Report::render`] writes and a face shows
    ///   beside the report's span.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type mismatch's message differs from its title, and
    ///   one refusal of every vocabulary name has a plain message.
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    /// - witness: `message::tests::every_refusal_name_has_a_plain_message`
    #[spec(ensures: |ret| matches!((self.subject, ret.0),
        (Subject::Refused { .. }, Subject::Refused { .. })
            | (Subject::Unsettled { .. }, Subject::Unsettled { .. })
            | (Subject::Goal(_), Subject::Goal(_)) | (Subject::Source(_), Subject::Source(_))
            | (Subject::Shadowed(_), Subject::Shadowed(_))
    ))]
    #[inline]
    #[must_use]
    pub const fn message(&self) -> Message<'step>
    {
        Message(self.subject)
    }

    /// The loci that explain the report beside its primary one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the two context slots, in the order the refusal names them:
    ///   the first occurrence a duplicate or a contradicted expectation
    ///   repeats; the declaration a member is named before; the type a term is
    ///   checked against, then the type it synthesises; the type a former met.
    ///   Each locus keeps its producer's span and its own label.
    /// - provides: the context loci [`Report::render`] marks, for a face that
    ///   shows them as related locations.
    /// - fails: never; an empty slot is the [`report_context::Absent`] absence:
    ///   [`Unnamed`] for a slot the refusal names no locus for, [`Unrecorded`]
    ///   for a node the origin table holds nothing for, [`OutsideText`] for a
    ///   span the text cannot answer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mismatch and duplicate fixtures expose causal slot
    ///   order. Finite UTF-8 boundaries distinguish outside-text context from
    ///   unrecorded or unnamed context; a goal has two unnamed slots. Other
    ///   producer payloads are outside these observations.
    /// - witness: `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`
    /// - witness: `report::tests::utf8_boundaries_are_checked_per_locus_without_clamping`
    ///
    /// [`Unnamed`]: report_context::Absent::Unnamed
    /// [`Unrecorded`]: report_context::Absent::Unrecorded
    /// [`OutsideText`]: report_context::Absent::OutsideText
    #[spec(ensures: |ret| ret.iter().all(|slot| match *slot {
        Maybe::Present(annotation) => self.text.fragment(annotation.span).is_ok(),
        Maybe::Absent(_) => true,
    }) && match self.subject {
        Subject::Goal(_) | Subject::Shadowed(_) | Subject::Unsettled { unsettlement: Unsettlement::Obligations | Unsettlement::Unproduced | Unsettlement::RunOutcome, .. } =>
            ret == [Maybe::Absent(report_context::Absent::Unnamed); 2_usize],
        Subject::Refused { .. } | Subject::Source(_) | Subject::Unsettled { unsettlement: Unsettlement::Malformed, .. } => true,
    })]
    #[inline]
    pub fn context(&self) -> [Maybe<Annotation, report_context::Absent>; 2_usize]
    {
        self.annotations().context
    }

    /// What the report's primary locus is, as its underline labels it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the label [`Report::render`] writes under the primary locus:
    ///   what the refused bytes are for a refusal, with the types a checker
    ///   refusal compares, what the unsettlement rests on for a declaration
    ///   unsettled with no refusal, the surviving obligations for a goal;
    ///   absent exactly when [`Report::span`] is.
    /// - provides: the label a face shows beside the title, for a face that
    ///   does not draw the underline.
    /// - fails: never; an unlocated report is the [`report_span::Absent`]
    ///   absence [`Report::span`] gives.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type mismatch and an unresolved type head, both
    ///   malformed source, carry different labels; a mismatch carries its
    ///   types; a run refusal carries none.
    /// - witness: `diagnostics::diagnostics::refusals_of_one_class_label_what_their_locus_is`
    /// - witness: `diagnostics::diagnostics::a_mismatch_label_spells_both_types`
    #[spec(ensures: |ret| matches!((ret, self.span()), (Maybe::Present(_), Maybe::Present(_)) | (Maybe::Absent(_), Maybe::Absent(_)))
        && match ret { Maybe::Present(label) => label.comparison == self.comparison(), Maybe::Absent(_) => true })]
    #[inline]
    pub fn label(&self) -> Maybe<PrimaryLabel<'step>, report_span::Absent>
    {
        match self.annotations().primary {
            | Maybe::Present(primary) => Maybe::Present(PrimaryLabel {
                label: primary.label,
                comparison: self.comparison(),
            }),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The types the report's refusal compares.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused declaration compares what [`Comparison::of`] reads
    ///   for its refusal; every other report compares no types.
    /// - provides: the expected and found types a face spells beside the
    ///   primary locus.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type mismatch compares both of its types; a goal
    ///   compares none.
    /// - witness: `diagnostics::diagnostics::a_mismatch_label_spells_both_types`
    #[spec(ensures: |ret| match self.subject {
        Subject::Refused { refusal, spellings, .. } => ret == Comparison::of(refusal, spellings),
        Subject::Unsettled { .. } | Subject::Goal(_) | Subject::Source(_) | Subject::Shadowed(_) => ret == Comparison::none(),
    })]
    #[inline]
    #[must_use]
    pub fn comparison(&self) -> Comparison<'step>
    {
        match self.subject {
            | Subject::Refused {
                refusal, spellings, ..
            } => Comparison::of(refusal, spellings),
            | Subject::Unsettled { .. }
            | Subject::Goal(_)
            | Subject::Source(_)
            | Subject::Shadowed(_) => Comparison::none(),
        }
    }

    /// The judgements the report's refusal stood inside, located, outermost
    /// first: its nested reasons.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused declaration's reasons are those [`Reason::trail`]
    ///   reads from its judgements against its primary locus, less any whose
    ///   bytes the text cannot answer; every other report has none.
    /// - provides: the reasons [`Report::render`] marks, for a face that shows
    ///   them as related locations.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a force refused inside a thunk names the thunk and
    ///   the force; a goal names nothing.
    /// - witness: `diagnostics::diagnostics::a_refusal_names_the_judgements_it_stood_inside`
    #[spec(ensures: |ret| ret.iter().all(|reason| self.text.fragment(reason.span).is_ok())
        && match self.subject {
            Subject::Refused { .. } => true,
            Subject::Unsettled { .. } | Subject::Goal(_) | Subject::Source(_) | Subject::Shadowed(_) => ret.is_empty(),
        })]
    #[inline]
    #[must_use]
    pub fn reasons(&self) -> Vec<Reason<'step>>
    {
        match self.subject {
            | Subject::Refused {
                origins,
                spellings,
                pending,
                ..
            } => {
                let mut reasons = Reason::trail(pending, origins, spellings, self.span());
                reasons.retain(|reason| self.text.fragment(reason.span).is_ok());
                reasons
            },
            | Subject::Unsettled { .. }
            | Subject::Goal(_)
            | Subject::Source(_)
            | Subject::Shadowed(_) => Vec::new(),
        }
    }

    /// The note the report closes with.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused declaration closes with a note naming it, what it
    ///   states and the obligations that survive; every other report closes
    ///   with none.
    /// - provides: the note [`Report::render`] writes, for a face that carries
    ///   it beside the message.
    /// - fails: never; a report that states what a declaration states and
    ///   produced is the [`report_note::Absent::Statement`] absence, and a
    ///   warning the [`report_note::Absent::Warning`] absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused declaration's note names it; an unsettled
    ///   declaration has none.
    /// - witness: `report::tests::notes_and_titles_preserve_numeric_roles_and_omit_empty_survivors`
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(_)) == matches!(self.subject, Subject::Refused { .. }))]
    #[inline]
    pub const fn note(&self) -> Maybe<Note<'step>, report_note::Absent>
    {
        match self.subject {
            | Subject::Refused { declaration, .. } => Maybe::Present(Note(declaration)),
            | Subject::Unsettled { .. } | Subject::Goal(_) | Subject::Source(_) => {
                Maybe::Absent(report_note::Absent::Statement)
            },
            | Subject::Shadowed(_) => Maybe::Absent(report_note::Absent::Warning),
        }
    }

    /// The report as a source snippet, laid out in `style` at `verbosity`, or
    /// as one line of JSON.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the first line is the level — `error`, `goal` for a goal,
    ///   `warning` for a shadowed builtin — with a refusal's vocabulary name as
    ///   its identifier, and the message: a refusal's plain message, what the
    ///   declaration states and produced for a declaration, the shadowed path
    ///   for a warning. A located report then quotes the lines its loci cover
    ///   under the source's path, line and column, the primary locus underlined
    ///   and labelled with what its bytes are or with the surviving
    ///   obligations, each context locus marked with what it explains, and each
    ///   nested reason marked with the judgement it stands for; an unlocated
    ///   report names the source's path alone. A refused declaration closes
    ///   with a note naming it and what it states. A source with an empty path
    ///   is named `<input>`. Plain adds no styling; styled adds the backend's
    ///   colour sequences. Caller path controls remain literal in both modes.
    ///   No framing terminator is appended, but a trailing path line ending can
    ///   end an unlocated rendering. At [`Verbosity::Detailed`] and above the
    ///   snippet closes with the report's class, the producer's own wording
    ///   where it differs from the message, and the primary locus's source text
    ///   when it is one line; at [`Verbosity::Debug`] then the byte span of
    ///   every locus and the producer's refusal and judgements as their
    ///   implementers print them. At [`Verbosity::Json`] the rendering is one
    ///   line of JSON holding the level, the identifier, the class, the
    ///   message, the title, the path, every locus with its bytes, line, column
    ///   and label, and the note, whatever the style.
    /// - provides: the plain text the driver prints and the tests compare, and
    ///   the structured image a tool reads.
    /// - fails: never.
    /// - panics: none; every span reaches the snippet backend checked against
    ///   the text.
    /// - intension: the backend chooses the source window and the connector
    ///   layout; the loci it receives are exactly the producer's.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — one byte-exact golden for each report kind bounds
    ///   layout evidence to those fixtures. L3 — pathless and causal-context
    ///   observations distinguish lost locations; plain/styled pairs expose
    ///   added colour. Literal path controls and UTF-8 boundary fixtures expose
    ///   false sanitization or location guarantees. Other paths and producer
    ///   payloads are not exhaustively covered.
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    /// - witness: `diagnostics::diagnostics::an_unsettled_declaration_renders_as_its_golden`
    /// - witness: `diagnostics::diagnostics::a_goal_renders_as_its_golden`
    /// - witness: `diagnostics::diagnostics::a_pathless_report_names_input_and_renders_causal_context`
    /// - witness: `diagnostics::diagnostics::a_labeled_context_retains_its_locus_and_cause`
    /// - witness: `diagnostics::diagnostics::forced_styling_colors_actual_facade_annotations`
    /// - witness: `report::tests::literal_path_controls_are_not_styling_or_framing`
    /// - witness: `report::tests::utf8_boundaries_are_checked_per_locus_without_clamping`
    /// - witness: `diagnostics::diagnostics::a_refusal_names_the_judgements_it_stood_inside`
    /// - witness: `diagnostics::diagnostics::a_shadowed_builtin_renders_as_a_warning`
    /// - witness: `diagnostics::diagnostics::one_refusal_renders_at_every_verbosity`
    #[spec(ensures: |ref ret| match verbosity {
        Verbosity::Json => ret.as_ref().starts_with('{') && !ret.as_ref().contains('\n'),
        Verbosity::User | Verbosity::Detailed | Verbosity::Debug => match style {
            RenderStyle::Plain => match self.subject {
                Subject::Goal(_) => ret.as_ref().starts_with("goal: "),
                Subject::Unsettled { .. } => ret.as_ref().starts_with("error: "),
                Subject::Refused { .. } | Subject::Source(_) => ret.as_ref().starts_with("error["),
                Subject::Shadowed(_) => ret.as_ref().starts_with("warning["),
            },
            RenderStyle::Styled => ret.as_ref().contains("\u{1b}["),
        },
    })]
    #[inline]
    #[must_use]
    pub fn render(
        &self,
        style: RenderStyle,
        verbosity: Verbosity,
    ) -> Rendered
    {
        if verbosity == Verbosity::Json {
            return self.json();
        }
        let annotations = self.annotations();
        let reasons: Vec<(ByteSpan, String)> = self
            .reasons()
            .into_iter()
            .map(|reason| (reason.span, reason.to_string()))
            .collect();
        let title = self.message().to_string();
        let level = match self.subject {
            | Subject::Goal(_) => Level::INFO.with_name("goal"),
            | Subject::Shadowed(_) => Level::WARNING,
            | Subject::Refused { .. } | Subject::Unsettled { .. } | Subject::Source(_) => {
                Level::ERROR
            },
        };
        let identifier = self.identifier();
        let message = match identifier {
            | Maybe::Present(ref spelling) => {
                level.primary_title(title.as_str()).id(spelling.as_ref())
            },
            | Maybe::Absent(report_identifier::Absent::Statement) => {
                level.primary_title(title.as_str())
            },
        };
        let origin = if self.path.as_os_str().is_empty() {
            PATHLESS.to_owned()
        }
        else {
            self.path.display().to_string()
        };
        let [first, second] = annotations.context;
        let primary_label = match self.label() {
            | Maybe::Present(label) => label.to_string(),
            | Maybe::Absent(_) => String::new(),
        };
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
                for &(span, ref label) in &reasons {
                    snippet = snippet.annotation(
                        AnnotationKind::Context
                            .span(usize::from(span.start()) .. usize::from(span.end()))
                            .label(label.as_str()),
                    );
                }
                group = group.element(snippet);
            },
            | Maybe::Absent(_) => {
                group = group.element(Origin::path(origin.as_str()));
            },
        }
        let note = match self.note() {
            | Maybe::Present(note) => Maybe::Present(note.to_string()),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        if let Maybe::Present(ref note) = note {
            group = group.element(Level::NOTE.message(note.as_str()));
        }
        let details = self.details(verbosity);
        for detail in &details {
            group = group.element(
                Level::NOTE
                    .with_name(detail.name)
                    .message(detail.text.as_str()),
            );
        }
        let renderer = match style {
            | RenderStyle::Plain => Renderer::plain(),
            | RenderStyle::Styled => Renderer::styled(),
        };
        Rendered::from(renderer.decor_style(DecorStyle::Unicode).render(&[group]))
    }

    /// The lines a rendering at `verbosity` closes with, after the note.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: none below [`Verbosity::Detailed`]; then the class, the
    ///   producer's wording where it differs from the message, and the primary
    ///   locus's text when it is one line; at [`Verbosity::Debug`] then the
    ///   byte spans and, for a refusal, the producer's refusal and the
    ///   judgements it stood inside. Every text is one line.
    /// - provides: the detail [`Report::render`] adds above the user level.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one refusal rendered at each level shows the detail
    ///   lines of its level and none of the next.
    /// - witness: `diagnostics::diagnostics::one_refusal_renders_at_every_verbosity`
    #[spec(ensures: |ref ret| (matches!(verbosity, Verbosity::User | Verbosity::Json) == ret.is_empty())
        && ret.iter().all(|detail| !detail.text.contains('\n')))]
    fn details(
        &self,
        verbosity: Verbosity,
    ) -> Vec<Detail>
    {
        let mut details = Vec::new();
        if matches!(verbosity, Verbosity::User | Verbosity::Json) {
            return details;
        }
        details.push(Detail {
            name: "class",
            text: self.class().to_string(),
        });
        let title = self.title().to_string();
        if title != self.message().to_string() && !title.contains('\n') {
            details.push(Detail {
                name: "detail",
                text: title,
            });
        }
        let annotations = self.annotations();
        if let Maybe::Present(primary) = annotations.primary
            && let Ok(fragment) = self.text.fragment(primary.span)
            && !fragment.as_ref().contains('\n')
        {
            details.push(Detail {
                name: "expression",
                text: format!("`{}`", fragment.as_ref()),
            });
        }
        if verbosity != Verbosity::Debug {
            return details;
        }
        let mut spans = match annotations.primary {
            | Maybe::Present(primary) => format!("primary {}", primary.span),
            | Maybe::Absent(reason) => format!("primary unlocated ({reason:?})"),
        };
        for annotation in annotations.context {
            if let Maybe::Present(annotation) = annotation {
                spans.push_str("; context ");
                spans.push_str(&annotation.span.to_string());
            }
        }
        for reason in self.reasons() {
            spans.push_str("; reason ");
            spans.push_str(&reason.span.to_string());
        }
        details.push(Detail {
            name: "spans",
            text: spans,
        });
        match self.subject {
            | Subject::Refused {
                refusal, pending, ..
            } => {
                details.push(Detail {
                    name: "refusal",
                    text: format!("{refusal:?}"),
                });
                if !pending.is_empty() {
                    details.push(Detail {
                        name: "judgements",
                        text: format!("{pending:?}"),
                    });
                }
            },
            | Subject::Source(refusal) => details.push(Detail {
                name: "refusal",
                text: format!("{refusal:?}"),
            }),
            | Subject::Unsettled { .. } | Subject::Goal(_) | Subject::Shadowed(_) => {},
        }
        details
    }

    /// The report as one line of JSON.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one JSON object on one line: `level`, `name` (the refusal's
    ///   vocabulary name, or null), `class`, `message`, `title`, `path`,
    ///   `primary` (a locus, or null), `context` and `reasons` (loci), and
    ///   `note` (or null); a locus holds its byte `start` and `end`, its
    ///   one-based `line` and `column` in characters, and its `label`.
    /// - provides: the [`Verbosity::Json`] rendering.
    /// - fails: never; the image holds only strings, numbers, nulls and arrays,
    ///   which always encode.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one refusal's image parses back with its name,
    ///   message, primary locus and reasons.
    /// - witness: `diagnostics::diagnostics::one_refusal_renders_at_every_verbosity`
    #[spec(ensures: |ref ret| ret.as_ref().starts_with('{') && !ret.as_ref().contains('\n'))]
    fn json(&self) -> Rendered
    {
        let text = self.text.as_ref();
        let locus = |span: ByteSpan, label: String| {
            let start = usize::from(span.start());
            let before = text.get(.. start).unwrap_or_default();
            let line = before.matches('\n').count().saturating_add(1);
            let column = before
                .rsplit('\n')
                .next()
                .map_or(0, |current| current.chars().count())
                .saturating_add(1);
            JsonLocus {
                start,
                end: usize::from(span.end()),
                line,
                column,
                label,
            }
        };
        let annotations = self.annotations();
        let primary = match (annotations.primary, self.label()) {
            | (Maybe::Present(primary), Maybe::Present(label)) => {
                Some(locus(primary.span, label.to_string()))
            },
            | (Maybe::Present(_) | Maybe::Absent(_), Maybe::Absent(_))
            | (Maybe::Absent(_), Maybe::Present(_)) => None,
        };
        let context = annotations
            .context
            .into_iter()
            .filter_map(|annotation| match annotation {
                | Maybe::Present(annotation) => {
                    Some(locus(annotation.span, annotation.label.to_string()))
                },
                | Maybe::Absent(_) => None,
            })
            .collect();
        let reasons = self
            .reasons()
            .into_iter()
            .map(|reason| locus(reason.span, reason.to_string()))
            .collect();
        let image = JsonReport {
            level: match self.subject {
                | Subject::Goal(_) => "goal",
                | Subject::Shadowed(_) => "warning",
                | Subject::Refused { .. } | Subject::Unsettled { .. } | Subject::Source(_) => {
                    "error"
                },
            },
            name: match self.identifier() {
                | Maybe::Present(spelling) => Some(spelling.as_ref().to_owned()),
                | Maybe::Absent(_) => None,
            },
            class: self.class().to_string(),
            message: self.message().to_string(),
            title: self.title().to_string(),
            path: self.path.display().to_string(),
            primary,
            context,
            reasons,
            note: match self.note() {
                | Maybe::Present(note) => Some(note.to_string()),
                | Maybe::Absent(_) => None,
            },
        };
        Rendered::from(serde_json::to_string(&image).unwrap_or_default())
    }

    /// Every locus the report marks, each checked against the source's text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the subject's loci as its producer recorded them; a primary
    ///   locus the text cannot answer becomes the
    ///   [`report_span::Absent::OutsideText`] absence, and such a context locus
    ///   is marked `OutsideText` in its original context slot.
    /// - provides: the only loci [`Report::span`], [`Report::context`] and
    ///   [`Report::render`] read.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite real producer spans and UTF-8 boundary cases
    ///   expose unvalidated or clamped locations. Independent primary and
    ///   context validation preserves the surviving causal slot. Arbitrary text
    ///   sizes and other producer payloads are outside these fixtures.
    /// - witness: `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`
    /// - witness: `diagnostics::diagnostics::a_span_outside_the_text_is_unlocated`
    /// - witness: `report::tests::utf8_boundaries_are_checked_per_locus_without_clamping`
    #[spec(ensures: |ref ret| {
        let primary = match ret.primary {
            Maybe::Present(annotation) => self.text.fragment(annotation.span).is_ok() && match self.subject {
                Subject::Refused { refusal, .. } => annotation.label == Label::Culprit(Culprit::of(refusal)),
                Subject::Source(refusal) => annotation.label == Label::Culprit(Culprit::of(Refusal::Lowering(refusal))),
                Subject::Unsettled { declaration, unsettlement: Unsettlement::Obligations }
                    | Subject::Goal(declaration) => annotation.label == Label::Surviving(declaration.surviving()),
                Subject::Unsettled { unsettlement, .. } => annotation.label == Label::Unsettled(unsettlement),
                Subject::Shadowed(_) => annotation.label == Label::Shadows,
            },
            Maybe::Absent(_) => true,
        };
        primary && ret.context.iter().all(|slot| match *slot {
            Maybe::Present(annotation) => self.text.fragment(annotation.span).is_ok(),
            Maybe::Absent(_) => true,
        })
    })]
    fn annotations(&self) -> Annotations
    {
        let annotations = match self.subject {
            | Subject::Refused {
                declaration,
                refusal,
                origins,
                ..
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
                unsettlement: Unsettlement::Malformed,
            } => Annotations::malformed(declaration.stated(), declaration.span()),
            | Subject::Unsettled {
                declaration,
                unsettlement: unsettlement @ (Unsettlement::Unproduced | Unsettlement::RunOutcome),
            } => Annotations::at(declaration.span(), Label::Unsettled(unsettlement)),
            | Subject::Source(refusal) => Annotations::lowering(refusal),
            | Subject::Shadowed(shadowed) => Annotations::at(shadowed.span, Label::Shadows),
        };
        let inside = |annotation: &Annotation| self.text.fragment(annotation.span).is_ok();
        let primary = match annotations.primary {
            | Maybe::Present(primary) if inside(&primary) => Maybe::Present(primary),
            | Maybe::Present(_) => Maybe::Absent(report_span::Absent::OutsideText),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        let [first, second] = annotations.context.map(|annotation| match annotation {
            | Maybe::Present(annotation) if inside(&annotation) => Maybe::Present(annotation),
            | Maybe::Present(_) => Maybe::Absent(report_context::Absent::OutsideText),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        });
        Annotations {
            primary,
            context: [first, second],
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a report carries no note.
    pub mod report_note {
        /// The reason a report closes with no note.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The report states what a declaration states and produced: it
            /// carries no refusal to name, and its title is its statement.
            Statement,
            /// The report is a warning: no declaration's settlement rests on
            /// it, so it names none.
            Warning,
        }
    }
}

/// The text of an annotation's label, or the empty text for a locus absent.
///
/// # Specification
/// - requires: nothing.
/// - ensures: absent loci have empty labels; present loci have a nonempty,
///   single-line, unstyled role label.
/// - provides: optional labels for the snippet backend.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — finite mismatch and duplicate snippets expose present
///   role labels alongside absent context. Missing labels or added line/control
///   characters change those renderings; arbitrary formatter failures are
///   outside these infallible string observations.
/// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
/// - witness: `diagnostics::diagnostics::a_labeled_context_retains_its_locus_and_cause`
/// - witness: `diagnostics::diagnostics::a_goal_renders_as_its_golden`
#[spec(ensures: |ref ret| ret.is_empty() == matches!(annotation, Maybe::Absent(_))
    && !ret.contains(['\r', '\n', '\u{1b}'])
)]
fn labelled<Reason>(annotation: Maybe<Annotation, Reason>) -> String
where
    Reason: Copy,
{
    match annotation {
        | Maybe::Present(annotation) => annotation.label.to_string(),
        | Maybe::Absent(_) => String::new(),
    }
}

/// One line a rendering above the user level closes with.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Detail
{
    /// What the line states, written where a note writes `note`.
    name: &'static str,
    /// The line.
    text: String,
}

/// A report's JSON image.
#[derive(Clone, Debug, serde::Serialize)]
struct JsonReport
{
    /// `error`, `warning` or `goal`.
    level: &'static str,
    /// The refusal's vocabulary name, when the report carries a refusal.
    name: Option<String>,
    /// The report's class.
    class: String,
    /// The message the report leads with.
    message: String,
    /// The producer's own wording.
    title: String,
    /// The source's path, as the walk reached it.
    path: String,
    /// The primary locus, when the report is located.
    primary: Option<JsonLocus>,
    /// The context loci.
    context: Vec<JsonLocus>,
    /// The nested reasons, outermost first.
    reasons: Vec<JsonLocus>,
    /// The note a refused declaration closes with.
    note: Option<String>,
}

/// One locus of a report's JSON image.
#[derive(Clone, Debug, serde::Serialize)]
struct JsonLocus
{
    /// The first byte.
    start: usize,
    /// The byte past the last.
    end: usize,
    /// The one-based line of the first byte.
    line: usize,
    /// The one-based column of the first byte, in characters.
    column: usize,
    /// What the locus says.
    label: String,
}

/// A report's title: the producer's message for a refusal, what the
/// declaration states and produced otherwise.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Title<'step>(Subject<'step>);

impl fmt::Display for Title<'_>
{
    /// Writes the producer's message for a refusal, and what the declaration
    /// states and produced otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the refusal's message or the declaration identity with
    ///   its stated and produced outcomes; whole-source refusal keeps its
    ///   scope.
    /// - provides: a report title independent of terminal styling.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer or
    ///   independent destination-failure observer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unresolved-name and goal titles retain source names
    ///   and numeric roles; mismatch titles expose no core addresses. Distinct
    ///   stated/produced counts expose substitution or reversal. Other wording
    ///   and failing destinations are excluded.
    /// - witness: `diagnostics::diagnostics::a_report_preserves_refusal_identity_and_title_payloads`
    /// - witness: `report::tests::notes_and_titles_preserve_numeric_roles_and_omit_empty_survivors`
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
            | Subject::Shadowed(shadowed) => write!(
                f,
                "`{}` shadows a builtin name; the source's binding wins",
                shadowed.path
            ),
        }
    }
}

/// The message a report leads with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Message<'step>(Subject<'step>);

impl fmt::Display for Message<'_>
{
    /// Writes a refusal's plain message, and every other report's title.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused declaration writes its refusal's plain message; a
    ///   source refused as a whole says so, then the plain message; an
    ///   unsettled declaration, a goal and a warning write their title, which
    ///   is already the user's; propagates a write failure.
    /// - provides: the first line of a report and the language server's
    ///   message.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one refusal of every vocabulary name writes a
    ///   nonempty, single-line message that names no grammar sort; a type
    ///   mismatch's message differs from its producer's title.
    /// - witness: `message::tests::every_refusal_name_has_a_plain_message`
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
            | Subject::Refused { refusal, .. } => fmt::Display::fmt(&Plain(refusal), f),
            | Subject::Source(refusal) => write!(
                f,
                "the source is not a list of declarations: {}",
                Plain(Refusal::Lowering(refusal))
            ),
            | Subject::Unsettled { .. } | Subject::Goal(_) | Subject::Shadowed(_) => {
                fmt::Display::fmt(&Title(self.0), f)
            },
        }
    }
}

/// The note a refused declaration closes with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Note<'step>(&'step DeclarationReport<'step>);

impl fmt::Display for Note<'_>
{
    /// Writes the declaration's settlement, its name, what it states, and the
    /// obligations that survive when any do.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes settlement, declaration identity and stated outcome,
    ///   then surviving obligations exactly when the ledger is nonempty.
    /// - provides: the context note after a refused declaration's snippet.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer or
    ///   independent destination-failure observer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — explicit fixture expectations produce empty ledgers
    ///   and each direction of an obligation mismatch. Exact semantic counts
    ///   and declaration names expose omitted or reversed payloads without
    ///   pinning prose. Other statements and destination failures are excluded.
    /// - witness: `report::tests::notes_and_titles_preserve_numeric_roles_and_omit_empty_survivors`
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

/// Report-level validation, framing and semantic payload boundaries.
#[cfg(test)]
mod tests
{
    use std::path::Path;

    use gandr_core_term::FailureClass;
    use gandr_surface_dispatcher::Composed;
    use gandr_surface_dispatcher::Goals;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_dispatcher::Standing;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::Verb;
    use gandr_surface_dispatcher::compose;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Annotation;
    use super::Class;
    use super::Label;
    use super::Note;
    use super::RenderStyle;
    use super::Report;
    use super::Subject;
    use super::Unsettlement;
    use super::Verbosity;
    use super::report_context;
    use super::report_span;
    use crate::Entry;
    use crate::entries;

    #[test]
    fn class_labels_keep_their_decision_surfaces_distinct()
    {
        let classes = [
            Class::Refusal(FailureClass::MalformedSource),
            Class::Unsettled(Unsettlement::Obligations),
            Class::Unsettled(Unsettlement::Unproduced),
            Class::Unsettled(Unsettlement::RunOutcome),
            Class::Unsettled(Unsettlement::Malformed),
            Class::Goal,
            Class::Warning,
        ];
        let labels = classes.map(|class| class.to_string());
        for (index, label) in labels.iter().enumerate() {
            for earlier in &labels[.. index] {
                assert_ne!(earlier, label, "different causes remain distinguishable");
            }
        }
    }

    #[test]
    fn utf8_boundaries_are_checked_per_locus_without_clamping()
    {
        let text = SourceText::from("αβ");
        for (start, end, first_start, first_end, primary_valid, context_valid) in [
            (1_usize, 2_usize, 2_usize, 4_usize, false, true),
            (0_usize, 2_usize, 1_usize, 2_usize, true, false),
            (4_usize, 4_usize, 0_usize, 0_usize, true, true),
            (5_usize, 7_usize, 0_usize, 2_usize, false, true),
        ] {
            let span = ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end))
                .expect("ordered span");
            let first = ByteSpan::new(ByteOffset::from(first_start), ByteOffset::from(first_end))
                .expect("ordered context");
            let report = Report::new(
                Path::new("boundary.gandr"),
                text,
                Subject::Source(LoweringRefusal::DuplicateDefinition {
                    span,
                    first,
                    name: "a".into(),
                }),
            );
            assert_eq!(
                report.span(),
                if primary_valid {
                    Maybe::Present(span)
                }
                else {
                    Maybe::Absent(report_span::Absent::OutsideText)
                }
            );
            assert_eq!(report.context(), [
                if context_valid {
                    Maybe::Present(Annotation {
                        span: first,
                        label: Label::First,
                    })
                }
                else {
                    Maybe::Absent(report_context::Absent::OutsideText)
                },
                Maybe::Absent(report_context::Absent::Unnamed),
            ]);
            let rendered = report.render(RenderStyle::Plain, Verbosity::User);
            if primary_valid {
                let column = if start == 4_usize { 3_usize } else { 1_usize };
                assert!(
                    rendered
                        .as_ref()
                        .contains(&format!("boundary.gandr:1:{column}"))
                );
            }
            else {
                assert!(rendered.as_ref().contains("boundary.gandr"));
                assert!(!rendered.as_ref().contains("boundary.gandr:"));
            }
        }
        let empty = ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(0_usize))
            .expect("empty span");
        let report = Report::new(
            Path::new("empty.gandr"),
            SourceText::from(""),
            Subject::Source(LoweringRefusal::UnresolvedName {
                span: empty,
                name: "empty".into(),
            }),
        );
        assert_eq!(report.span(), Maybe::Present(empty));
        assert!(
            report
                .render(RenderStyle::Plain, Verbosity::User)
                .as_ref()
                .contains("empty.gandr:1:1")
        );
    }

    #[test]
    fn literal_path_controls_are_not_styling_or_framing()
    {
        for path in [
            "plain.gandr",
            "escape\u{1b}[31m.gandr",
            "final\n",
            "final\r",
        ] {
            let report = Report::new(
                Path::new(path),
                SourceText::from(""),
                Subject::Source(LoweringRefusal::BudgetExceeded {
                    budget: 0_usize.into(),
                }),
            );
            let plain = report.render(RenderStyle::Plain, Verbosity::User);
            let styled = report.render(RenderStyle::Styled, Verbosity::User);
            assert!(
                plain.as_ref().ends_with(path),
                "the literal path ends the unlocated report"
            );
            assert!(
                styled.as_ref().contains(path),
                "style preserves the path payload"
            );
        }
    }

    #[test]
    fn notes_and_titles_preserve_numeric_roles_and_omit_empty_survivors()
    {
        let text = SourceText::from(
            "@[ owes(0) ] def quiet = 1 ;\n@[ owes(3) ] def pending : Integer ;\n@[ owes(0) ] def excess : Integer ;\n",
        );
        let grammar = built_in().expect("the grammar builds");
        let step = Step::Source {
            path: Path::new("payload.gandr"),
            root: SourceRoot::Fixture,
            text,
            composed: compose(
                &grammar,
                SourceRoot::Fixture.corpus_root(),
                text,
                &mut LoweringCount::default(),
            )
            .expect("the fixture composes"),
            standing: Standing::Unsettled,
        };
        let Step::Source {
            composed: Composed::Settled { ref report, .. },
            ..
        } = step
        else {
            panic!("the declarations reach the ledger");
        };
        assert_eq!(report.declarations().len(), 3_usize);
        for (declaration, (name, expected)) in report.declarations().iter().zip([
            ("quiet", &[0_usize][..]),
            ("pending", &[3_usize, 0_usize, 2_usize][..]),
            ("excess", &[0_usize, 1_usize, 0_usize][..]),
        ]) {
            let note = Note(declaration).to_string();
            assert!(note.contains(name), "the note retains declaration identity");
            assert!(
                note.split(|character: char| !character.is_ascii_digit())
                    .filter_map(|digits| digits.parse::<usize>().ok())
                    .eq(expected.iter().copied()),
                "only stated and nonempty surviving payloads: {note}"
            );
        }
        let mut stream = entries(&step, Verb::Check(Goals::Gated));
        for (name, expected) in [
            ("pending", [3_usize, 1_usize]),
            ("excess", [0_usize, 1_usize]),
        ] {
            let Some(Entry::Report(report)) = stream.next()
            else {
                panic!("each owed declaration reports");
            };
            let title = report.title().to_string();
            assert!(title.contains(name));
            assert!(
                title
                    .split(|character: char| !character.is_ascii_digit())
                    .filter_map(|digits| digits.parse::<usize>().ok())
                    .eq(expected),
                "stated count precedes the produced count: {title}"
            );
        }
        assert!(stream.next().is_none());
    }
}
