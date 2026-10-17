//! The diagnostic every face projects: what went wrong, where, inside which
//! rules, with which names in scope.
//!
//! # One owned record, read by every face
//!
//! A [`Diagnostic`] holds everything a face shows and nothing a face must look
//! up: the source's path, a [`Severity`], the refusal's vocabulary name, a
//! [`Message`] with its stable key, the [`DiagnosticDetail`] a detailed level
//! adds, the [`DiagnosticAnnotation`]s with their roles and exact byte spans,
//! the [`DiagnosticContext`]s the refusal stood inside, the hypotheses in
//! scope, the note, the offending expression, and the [`Excerpt`] of source
//! lines its annotations cover. The terminal lays the excerpt out with its
//! annotations and contexts; the language server publishes the primary
//! annotation as the diagnostic's range and the rest as related information.
//! Neither re-reads the producer's types, the origin table or the source.
//!
//! The excerpt is the lines the loci touch, not the whole text, so a face that
//! prints one diagnostic of a long source copies those lines once and a
//! diagnostic outlives the text it was built from.
//!
//! # A context is a judgement, a rule and its binders
//!
//! A located context renders as `label; while sentence`: the label says how
//! its term was judged — ``checked against `T` ``, `synthesised`, `formed` —
//! and the sentence what the rule there was doing. The binders the rule
//! opened follow as `; binds x : T`. An unlocated context has no bytes to
//! mark and renders as a note `while sentence` after the snippet.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_checker::FrameRole;
use gandr_surface_corpus::RefusalName;
use gandr_surface_corpus::RefusalSpelling;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::frame::Sentence;
use crate::lint::Lint;
use crate::report::Class;
use crate::report::Unsettlement;
use crate::report::report_identifier;
use crate::report::report_note;
use crate::report::report_span;
use crate::spelled::spelling;
use crate::verbosity::Verbosity;

quenchant_shape::reason_enum! {
    /// Why a span has no locus.
    pub mod located {
        /// The reason a span is not located in the text.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The span lies outside the text, or splits one of its
            /// characters.
            OutsideText,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a context has no locus.
    pub mod context_locus {
        /// The reason a context marks no bytes.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Its node is one the origin table holds nothing for: the checker
            /// minted it.
            Unrecorded,
            /// The span recorded lies outside the text.
            OutsideText,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a binding has no name.
    pub mod binding {
        /// The reason a hypothesis is unnamed.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source wrote no name for the binder, or the origin table
            /// holds none: a split, a discarded statement, an inserted lambda.
            Unnamed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a diagnostic quotes no expression.
    pub mod expression {
        /// The reason no expression is quoted.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The diagnostic marks no bytes.
            Unlocated,
            /// The bytes it marks span more than one line.
            Multiline,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a diagnostic names no producer image.
    pub mod producer {
        /// The reason the producer's own image is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The diagnostic carries no refusal.
            Statement,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a diagnostic proposes no fix.
    pub mod fix {
        /// The reason no edit is proposed.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No single edit settles what it reports.
            Unproposed,
        }
    }
}

/// Where a span lies: its bytes, and the one-based line and column, in
/// characters, of its first byte.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Locus
{
    /// The bytes.
    pub span: ByteSpan,
    /// The one-based line of the first byte.
    pub line: usize,
    /// The one-based column of the first byte, in characters.
    pub column: usize,
}

impl Locus
{
    /// The locus of `span` in `text`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the span with the line and column of its first byte when it
    ///   lies inside `text` on character boundaries; the
    ///   [`located::Absent::OutsideText`] absence otherwise, never clamped.
    /// - provides: the position every annotation and context carries.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a span on the second line reads line 2; a span that
    ///   splits a character is absent.
    /// - witness: `model::tests::a_locus_counts_lines_and_characters`
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(_)) == text.fragment(span).is_ok())]
    #[inline]
    pub fn of(
        text: SourceText<'_>,
        span: ByteSpan,
    ) -> Maybe<Self, located::Absent>
    {
        if text.fragment(span).is_err() {
            return Maybe::Absent(located::Absent::OutsideText);
        }
        let before = text
            .as_ref()
            .get(.. usize::from(span.start()))
            .unwrap_or_default();
        let line = before.matches('\n').count().saturating_add(1);
        let column = before
            .rsplit('\n')
            .next()
            .map_or(0, |current| current.chars().count())
            .saturating_add(1);
        Maybe::Present(Self { span, line, column })
    }
}

/// How serious a diagnostic is, and how a face presents it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Severity
{
    /// A refusal or an unsettled declaration.
    Error,
    /// A warning, which settles nothing: a builtin the source shadowed, or a
    /// lint's finding.
    Warning,
    /// A declaration unsettled by its obligations alone, under
    /// `check --goals`.
    Goal,
    /// A declaration a refusal elsewhere leaves unsettled: what it names was
    /// refused, so its own refusal follows from that one and is reported
    /// beside it rather than as an error of its own.
    Note,
    /// A ledger line: a source's standing, printed as one line.
    Ledger,
}

impl fmt::Display for Severity
{
    /// Writes `error`, `warning`, `goal`, `note` or `line`.
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
            Self::Error => "error",
            Self::Warning => "warning",
            Self::Goal => "goal",
            Self::Note => "note",
            Self::Ledger => "line",
        })
    }
}

/// The stable key of a message: what a translation or a tool matches on.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum MessageKey
{
    /// A refusal, or a warning, by its vocabulary name.
    Refusal(RefusalName),
    /// A lint's finding, by the lint.
    Lint(Lint),
    /// A declaration unsettled with no refusal produced, by what it rests on.
    Unsettled(Unsettlement),
    /// A goal.
    Goal,
    /// A ledger line.
    Ledger,
}

impl fmt::Display for MessageKey
{
    /// Writes the refusal's or the lint's spelling, `unsettled`, `goal` or
    /// `ledger`.
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
            Self::Refusal(name) => f.write_str(name.spelling().as_ref()),
            Self::Lint(lint) => fmt::Display::fmt(&lint, f),
            Self::Unsettled(_) => f.write_str("unsettled"),
            Self::Goal => f.write_str("goal"),
            Self::Ledger => f.write_str("ledger"),
        }
    }
}

/// The message a diagnostic leads with, and its stable key.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Message
{
    /// What a translation of the message is keyed by.
    pub key: MessageKey,
    /// The message, in the words of the language a user writes.
    pub text: String,
}

/// The types a refusal compares, spelled.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Compared
{
    /// The type the rule required.
    pub expected: Maybe<String, spelling::Absent>,
    /// The type the rule met.
    pub found: Maybe<String, spelling::Absent>,
}

impl fmt::Display for Compared
{
    /// Writes ``expected `E`, found `F` ``, either side alone, or nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match (&self.expected, &self.found) {
            (&Maybe::Present(ref expected), &Maybe::Present(ref found)) => {
                write!(f, "expected `{expected}`, found `{found}`")
            },
            (&Maybe::Present(ref expected), &Maybe::Absent(_)) => {
                write!(f, "expected `{expected}`")
            },
            (&Maybe::Absent(_), &Maybe::Present(ref found)) => write!(f, "found `{found}`"),
            (&Maybe::Absent(_), &Maybe::Absent(_)) => Ok(()),
        }
    }
}

/// The typed detail a diagnostic carries beside its message.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DiagnosticDetail
{
    /// Whose fact the diagnostic records.
    pub class: Class,
    /// The producer's own wording.
    pub title: String,
    /// The types its refusal compares.
    pub compared: Compared,
    /// The producer's refusal and the failure it kept, as their implementers
    /// print them, core ids included.
    pub producer: Maybe<String, producer::Absent>,
}

/// What an annotation marks.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AnnotationKind
{
    /// The bytes the diagnostic is about.
    Primary,
    /// Bytes that are part of the cause.
    Context,
}

/// One marked span and what it says.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DiagnosticAnnotation
{
    /// Whether the bytes are the diagnostic's own or part of its cause.
    pub kind: AnnotationKind,
    /// The bytes, and where they lie.
    pub locus: Locus,
    /// What the mark says.
    pub label: String,
}

/// A hypothesis in scope: the name its binder wrote and its type.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Binding
{
    /// The name, where the source wrote one the origin table holds.
    pub name: Maybe<String, binding::Absent>,
    /// The type, spelled.
    pub ty: Maybe<String, spelling::Absent>,
}

impl fmt::Display for Binding
{
    /// Writes `name : type`, `_` for an unnamed binder and `?` for an
    /// unspelled type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let name = match self.name {
            Maybe::Present(ref name) => name.as_str(),
            Maybe::Absent(_) => "_",
        };
        let ty = match self.ty {
            Maybe::Present(ref ty) => ty.as_str(),
            Maybe::Absent(_) => "?",
        };
        write!(f, "{name} : {ty}")
    }
}

/// How a context's term was judged.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Judged
{
    /// Checked against a type, spelled when the composition could spell it.
    Checked(Maybe<String, spelling::Absent>),
    /// Its type was synthesised.
    Synthesised,
    /// It was formed as a type.
    Formed,
}

impl fmt::Display for Judged
{
    /// Writes ``checked against `T` ``, `checked`, `synthesised` or `formed`.
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
            Self::Checked(Maybe::Present(ref expected)) => {
                write!(f, "checked against `{expected}`")
            },
            Self::Checked(Maybe::Absent(_)) => f.write_str("checked"),
            Self::Synthesised => f.write_str("synthesised"),
            Self::Formed => f.write_str("formed"),
        }
    }
}

/// One rule a refusal stood inside, at its term's bytes when they are known.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DiagnosticContext
{
    /// The rule, by its stable name.
    pub role: FrameRole,
    /// What the rule was doing, as a clause after `while`.
    pub sentence: Sentence,
    /// How the term was judged.
    pub judged: Judged,
    /// The binders the rule opened, in order.
    pub binders: Vec<Binding>,
    /// The term's bytes.
    pub locus: Maybe<Locus, context_locus::Absent>,
}

impl DiagnosticContext
{
    /// The context as one label: `judgement; while sentence`, then the
    /// binders it opened after `; binds`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the judgement, `; while `, the sentence, and `; binds ` with
    ///   the binders joined by `, ` when it opened any; one line.
    /// - provides: the label a terminal writes under the context's bytes and an
    ///   editor shows at its related location.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a context under a binder names it after its sentence;
    ///   one opening none does not.
    /// - witness: `diagnostics::diagnostics::a_mismatch_under_a_binder_names_it`
    #[spec(ensures: |ref ret| ret.contains(self.sentence.as_ref()) && !ret.contains('\n'))]
    #[inline]
    #[must_use]
    pub fn label(&self) -> String
    {
        let mut label = alloc::format!("{}; while {}", self.judged, self.sentence);
        self.bound(&mut label);
        label
    }

    /// The context as a note, for one with no bytes to mark: `while
    /// sentence`, then its binders.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `while `, the sentence, and the binders as
    ///   [`DiagnosticContext::label`] writes them.
    /// - provides: the note a terminal closes an unlocated context with and the
    ///   line an editor appends to its message.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unlocated rule reads as its sentence.
    /// - witness: `diagnostics::diagnostics::an_unlocated_rule_becomes_a_note`
    #[spec(ensures: |ref ret| ret.starts_with("while ") && !ret.contains('\n'))]
    #[inline]
    #[must_use]
    pub fn note(&self) -> String
    {
        let mut note = alloc::format!("while {}", self.sentence);
        self.bound(&mut note);
        note
    }

    /// Append the binders to `text`.
    ///
    /// # Specification
    /// trivial.
    fn bound(
        &self,
        text: &mut String,
    )
    {
        for (at, binder) in self.binders.iter().enumerate() {
            text.push_str(if at == 0_usize { "; binds " } else { ", " });
            let _written = fmt::Write::write_fmt(text, format_args!("{binder}"));
        }
    }
}

/// The source lines a diagnostic's loci cover.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Excerpt
{
    /// The lines, whole, from the first locus's line to the last one's.
    pub text: String,
    /// The byte of the source the excerpt starts at.
    pub start: ByteOffset,
    /// The one-based line it starts on.
    pub line: usize,
}

/// One line a rendering above the user level closes with: `name: text`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Detail
{
    /// What the line states, written where a note writes `note`.
    pub name: &'static str,
    /// The line.
    pub text: String,
}

/// The edit a diagnostic proposes: the bytes it replaces and the text written
/// in their place, an empty span for an insertion.
///
/// # Specification
/// - requires: nothing to construct this data; the builder makes it over the
///   text its diagnostic was built from.
/// - ensures: the span lies inside that text on character boundaries.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
///
/// # Adequacy
/// - hypothesis: L3 — a lint finding's fix applied to its source and checked
///   again leaves no finding.
/// - witness: `diagnostics::diagnostics::an_inferred_exit_is_a_finding_whose_fix_writes_its_keyword`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Fix
{
    /// The bytes replaced.
    pub span: ByteSpan,
    /// The text written in their place.
    pub replacement: String,
}

/// The vocabulary name a diagnostic is identified by: a refusal's or a
/// lint's.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Identifier
{
    /// A refusal, or a warning named as the refusal it would be, spelled as a
    /// `refuses` payload spells it.
    Refusal(RefusalSpelling),
    /// A lint's finding, by the lint's spelling.
    Lint(Lint),
}

impl AsRef<str> for Identifier
{
    /// The identifier's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        match *self {
            Self::Refusal(ref spelling) => spelling.as_ref(),
            Self::Lint(ref lint) => lint.as_ref(),
        }
    }
}

impl fmt::Display for Identifier
{
    /// Writes the identifier's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.as_ref())
    }
}

impl fmt::Display for Detail
{
    /// The line as a plain rendering writes it: the name, a colon, the text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}: {}", self.name, self.text)
    }
}

/// Where one source's own text starts in the text a diagnostic was built
/// over: its byte offset and the newlines before it.
///
/// # Specification
/// - requires: constructed by [`SourceStart::of`] or as the default.
/// - ensures: `lines` counts the newlines of the built-over text before `base`.
/// - provides: what [`Diagnostic::rebased`] moves a diagnostic back by.
/// - executable: none — a data type; [`SourceStart::of`] states its check.
///
/// # Adequacy
/// - hypothesis: L3 — an importer laid after its sibling reports its refusal at
///   its own line, column and bytes.
/// - witness: `diagnostics::diagnostics::an_importer_s_refusal_is_located_in_its_own_text`
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SourceStart
{
    /// The offset of the source's first byte.
    base: ByteOffset,
    /// The newlines before `base`.
    lines: usize,
}

impl SourceStart
{
    /// The source starting at `base` in `text`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `base`, with the newlines of `text` before it; none when
    ///   `base` is past the text or splits a character.
    /// - provides: the start a unit's diagnostics are rebased by.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witness of [`SourceStart`].
    /// - witness: `diagnostics::diagnostics::an_importer_s_refusal_is_located_in_its_own_text`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.base == base
        && ret.lines == text.as_ref().get(.. usize::from(base)).map_or(0_usize, |before| before.matches('\n').count()))]
    pub fn of(
        text: SourceText<'_>,
        base: ByteOffset,
    ) -> Self
    {
        let lines = text
            .as_ref()
            .get(.. usize::from(base))
            .map_or(0_usize, |before| before.matches('\n').count());
        Self { base, lines }
    }
}

/// One diagnostic: a refusal, an unsettled declaration, a goal, a warning, a
/// lint's finding or a ledger line, with everything a face shows of it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic
{
    /// The source's path, as the walk reached it; empty for a source with no
    /// file.
    pub path: PathBuf,
    /// How serious it is.
    pub severity: Severity,
    /// The vocabulary name of the refusal or the lint it reports.
    pub identifier: Maybe<Identifier, report_identifier::Absent>,
    /// What it leads with.
    pub message: Message,
    /// What a detailed level adds.
    pub detail: DiagnosticDetail,
    /// Its primary span, or why it marks none.
    pub span: Maybe<ByteSpan, report_span::Absent>,
    /// The marked spans: the primary one first, when located, then the context
    /// annotations its refusal names.
    pub annotations: Vec<DiagnosticAnnotation>,
    /// The rules its refusal stood inside, outermost first.
    pub contexts: Vec<DiagnosticContext>,
    /// The hypotheses in scope where it was refused, outermost first.
    pub hypotheses: Vec<Binding>,
    /// The note it closes with.
    pub note: Maybe<String, report_note::Absent>,
    /// The source text of its primary span, when that is one line.
    pub expression: Maybe<String, expression::Absent>,
    /// The lines its loci cover.
    pub excerpt: Maybe<Excerpt, report_span::Absent>,
    /// The edit that settles it, when it proposes one.
    pub fix: Maybe<Fix, fix::Absent>,
}

impl Diagnostic
{
    /// The primary annotation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the first annotation of kind [`AnnotationKind::Primary`];
    ///   absent, with the reason [`Diagnostic::span`] gives, when the
    ///   diagnostic is unlocated; absent as outside the text when it is located
    ///   but its first annotation is not the primary.
    /// - provides: the lead range an editor publishes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a located refusal's primary annotation is its span;
    ///   an unlocated one has none; a located one whose primary mark was
    ///   removed offers its context mark as none.
    /// - witness: `diagnostics::diagnostics::an_unlocated_report_claims_no_span`
    /// - witness: `report::tests::a_located_diagnostic_without_its_primary_mark_has_no_primary`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(annotation) => self.span == Maybe::Present(annotation.locus.span),
        Maybe::Absent(reason) => match self.span {
            Maybe::Absent(held) => reason == held,
            Maybe::Present(_) => reason == report_span::Absent::OutsideText
                && self.annotations.first().is_none_or(|first| first.kind != AnnotationKind::Primary),
        },
    })]
    #[inline]
    pub fn primary(&self) -> Maybe<&DiagnosticAnnotation, report_span::Absent>
    {
        match (self.span, self.annotations.first()) {
            (Maybe::Present(_), Some(primary)) if primary.kind == AnnotationKind::Primary => {
                Maybe::Present(primary)
            },
            (Maybe::Absent(reason), _) => Maybe::Absent(reason),
            (Maybe::Present(_), _) => Maybe::Absent(report_span::Absent::OutsideText),
        }
    }

    /// This diagnostic as the source that starts at `start` in the text it
    /// was built over shows it: its bytes and its lines measured from there.
    ///
    /// # Specification
    /// - requires: `start` was taken of the text this diagnostic was built
    ///   over, at the start of a line.
    /// - ensures: unchanged at offset zero. Otherwise every span, locus and
    ///   excerpt at or after the start is moved back by its bytes and lines; an
    ///   annotation before it is dropped, a context's locus there is outside
    ///   the text, a primary span there leaves the diagnostic unlocated, a fix
    ///   there is not proposed, and an excerpt is cut to the lines from the
    ///   start on, or dropped when it ends before it.
    /// - provides: the diagnostic of one source of a unit that lays its imports
    ///   before it, located in that source's own file.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an importer's refusal is reported at its own line and
    ///   column.
    /// - witness: `diagnostics::diagnostics::an_importer_s_refusal_is_located_in_its_own_text`
    #[inline]
    #[must_use]
    #[spec(
        captures: [before = self.span],
        ensures: |ret| usize::from(start.base) != 0_usize || ret.span == before,
    )]
    pub fn rebased(
        mut self,
        start: SourceStart,
    ) -> Self
    {
        let SourceStart { base, lines } = start;
        if usize::from(base) == 0_usize {
            return self;
        }
        let shifted = |span: ByteSpan| {
            let start = usize::from(span.start()).checked_sub(usize::from(base))?;
            let end = usize::from(span.end()).checked_sub(usize::from(base))?;
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).ok()
        };
        let moved = |locus: Locus| {
            Some(Locus {
                span: shifted(locus.span)?,
                line: locus.line.checked_sub(lines)?,
                column: locus.column,
            })
        };
        self.span = match self.span {
            Maybe::Present(span) => shifted(span).map_or(
                Maybe::Absent(report_span::Absent::OutsideText),
                Maybe::Present,
            ),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        self.annotations = core::mem::take(&mut self.annotations)
            .into_iter()
            .filter_map(|annotation| {
                Some(DiagnosticAnnotation {
                    locus: moved(annotation.locus)?,
                    ..annotation
                })
            })
            .collect();
        for context in &mut self.contexts {
            if let Maybe::Present(locus) = context.locus {
                context.locus = moved(locus).map_or(
                    Maybe::Absent(context_locus::Absent::OutsideText),
                    Maybe::Present,
                );
            }
        }
        if let Maybe::Present(ref fix) = self.fix
            && let Some(span) = shifted(fix.span)
        {
            let replacement = fix.replacement.clone();
            self.fix = Maybe::Present(Fix { span, replacement });
        }
        else if let Maybe::Present(_) = self.fix {
            self.fix = Maybe::Absent(fix::Absent::Unproposed);
        }
        if let Maybe::Present(excerpt) = core::mem::replace(
            &mut self.excerpt,
            Maybe::Absent(report_span::Absent::OutsideText),
        ) {
            let cut = usize::from(base).saturating_sub(usize::from(excerpt.start));
            let dropped = excerpt
                .text
                .get(.. cut)
                .map_or(0_usize, |prefix| prefix.matches('\n').count());
            if let Some(kept) = excerpt.text.get(cut ..)
                && !kept.is_empty()
                && let Some(start) = usize::from(excerpt.start)
                    .saturating_add(cut)
                    .checked_sub(usize::from(base))
                && let Some(line) = excerpt.line.saturating_add(dropped).checked_sub(lines)
            {
                self.excerpt = Maybe::Present(Excerpt {
                    text: String::from(kept),
                    start: ByteOffset::from(start),
                    line,
                });
            }
        }
        self
    }

    /// The lines a rendering at `verbosity` closes with, after the note.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: none below [`Verbosity::Detailed`] and none at
    ///   [`Verbosity::Json`]; at it and above the class, the producer's wording
    ///   where it differs from the message, the expression, and the hypotheses
    ///   when any are in scope; at [`Verbosity::Debug`] then the byte span of
    ///   every locus, each context's rule, and the producer's image. Every text
    ///   is one line.
    /// - provides: the detail every face adds above the user level.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one refusal shows the lines of its level and none of
    ///   the next.
    /// - witness: `diagnostics::diagnostics::one_refusal_details_each_verbosity`
    /// - witness: `report::tests::a_title_the_message_repeats_is_not_detailed`
    #[spec(ensures: |ref ret| (matches!(verbosity, Verbosity::User | Verbosity::Json) == ret.is_empty()
        || self.severity == Severity::Ledger)
        && ret.iter().all(|detail| !detail.text.contains('\n')))]
    #[inline]
    #[must_use]
    pub fn details(
        &self,
        verbosity: Verbosity,
    ) -> Vec<Detail>
    {
        let mut details = Vec::new();
        if matches!(verbosity, Verbosity::User | Verbosity::Json)
            || self.severity == Severity::Ledger
        {
            return details;
        }
        details.push(Detail {
            name: "class",
            text: alloc::format!("{}", self.detail.class),
        });
        if self.detail.title != self.message.text && !self.detail.title.contains('\n') {
            details.push(Detail {
                name: "detail",
                text: self.detail.title.clone(),
            });
        }
        if let Maybe::Present(ref expression) = self.expression {
            details.push(Detail {
                name: "expression",
                text: alloc::format!("`{expression}`"),
            });
        }
        if !self.hypotheses.is_empty() {
            let hypotheses: Vec<String> = self
                .hypotheses
                .iter()
                .map(|binding| alloc::format!("`{binding}`"))
                .collect();
            details.push(Detail {
                name: "hypotheses",
                text: hypotheses.join(", "),
            });
        }
        if verbosity != Verbosity::Debug {
            return details;
        }
        let mut spans = match self.span {
            Maybe::Present(span) => alloc::format!("primary {span}"),
            Maybe::Absent(reason) => alloc::format!("primary unlocated ({reason:?})"),
        };
        for annotation in self.annotations.iter().skip(1) {
            let _written = fmt::Write::write_fmt(
                &mut spans,
                format_args!("; context {}", annotation.locus.span),
            );
        }
        for context in &self.contexts {
            if let Maybe::Present(locus) = context.locus {
                let _written =
                    fmt::Write::write_fmt(&mut spans, format_args!("; rule {}", locus.span));
            }
        }
        details.push(Detail {
            name: "spans",
            text: spans,
        });
        if !self.contexts.is_empty() {
            let rules: Vec<String> = self
                .contexts
                .iter()
                .map(|context| alloc::format!("{}", context.role))
                .collect();
            details.push(Detail {
                name: "rules",
                text: rules.join(", "),
            });
        }
        if let Maybe::Present(ref producer) = self.detail.producer {
            details.push(Detail {
                name: "refusal",
                text: producer.clone(),
            });
        }
        details
    }

    /// The diagnostic as one line of JSON.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a ledger line is `{"level":"line","path":…,"line":…}`; every
    ///   other diagnostic one object holding `level`, `name` (or null), `key`,
    ///   `class`, `message`, `title`, `path`, `primary` (a locus, or null),
    ///   `annotations` (the context loci), `contexts` (each with its `role`,
    ///   `sentence`, `judged`, `binders` and locus, or null), `hypotheses`,
    ///   `note` (or null) and `fix` (its byte `start` and `end` and its
    ///   `replacement`, or null); a locus holds its byte `start` and `end`, its
    ///   one-based `line` and `column` in characters, and its `label`. One
    ///   line.
    /// - provides: the [`Verbosity::Json`] image every face shares.
    /// - fails: never; the image holds only strings, numbers, nulls and arrays,
    ///   which always encode.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one refusal's image parses back with its name,
    ///   message, primary locus and contexts; a ledger line's with its line; a
    ///   lint finding's with its fix.
    /// - witness: `diagnostics::diagnostics::one_refusal_details_each_verbosity`
    /// - witness: `diagnostics::diagnostics::each_verb_prints_its_entries`
    /// - witness: `diagnostics::diagnostics::an_inferred_exit_is_a_finding_whose_fix_writes_its_keyword`
    /// - witness: `report::tests::the_annotations_of_the_image_are_the_contexts_alone`
    #[spec(ensures: |ref ret| ret.starts_with('{') && !ret.contains('\n'))]
    #[inline]
    #[must_use]
    pub fn json(&self) -> String
    {
        let path = alloc::format!("{}", self.path.display());
        if self.severity == Severity::Ledger {
            return serde_json::to_string(&JsonLine {
                level: "line",
                line: alloc::format!("{path}: {}", self.message.text),
                path,
            })
            .unwrap_or_default();
        }
        let locus = |locus: Locus, label: String| JsonLocus {
            start: usize::from(locus.span.start()),
            end: usize::from(locus.span.end()),
            line: locus.line,
            column: locus.column,
            label,
        };
        let primary = match self.primary() {
            Maybe::Present(annotation) => Some(locus(annotation.locus, annotation.label.clone())),
            Maybe::Absent(_) => None,
        };
        let image = JsonDiagnostic {
            level: alloc::format!("{}", self.severity),
            name: match self.identifier {
                Maybe::Present(ref identifier) => Some(String::from(identifier.as_ref())),
                Maybe::Absent(_) => None,
            },
            key: alloc::format!("{}", self.message.key),
            class: alloc::format!("{}", self.detail.class),
            message: self.message.text.clone(),
            title: self.detail.title.clone(),
            path,
            primary,
            annotations: self
                .annotations
                .iter()
                .filter(|annotation| annotation.kind == AnnotationKind::Context)
                .map(|annotation| locus(annotation.locus, annotation.label.clone()))
                .collect(),
            contexts: self
                .contexts
                .iter()
                .map(|context| JsonContext {
                    role: alloc::format!("{}", context.role),
                    sentence: alloc::format!("{}", context.sentence),
                    judged: alloc::format!("{}", context.judged),
                    binders: context
                        .binders
                        .iter()
                        .map(|binder| alloc::format!("{binder}"))
                        .collect(),
                    locus: match context.locus {
                        Maybe::Present(at) => Some(locus(at, context.label())),
                        Maybe::Absent(_) => None,
                    },
                })
                .collect(),
            hypotheses: self
                .hypotheses
                .iter()
                .map(|binding| alloc::format!("{binding}"))
                .collect(),
            note: match self.note {
                Maybe::Present(ref note) => Some(note.clone()),
                Maybe::Absent(_) => None,
            },
            fix: match self.fix {
                Maybe::Present(ref fix) => Some(JsonFix {
                    start: usize::from(fix.span.start()),
                    end: usize::from(fix.span.end()),
                    replacement: fix.replacement.clone(),
                }),
                Maybe::Absent(_) => None,
            },
        };
        serde_json::to_string(&image).unwrap_or_default()
    }
}

/// A ledger line's JSON image.
#[derive(Clone, Debug, serde::Serialize)]
struct JsonLine
{
    /// Always `line`, where a diagnostic's image writes its level.
    level: &'static str,
    /// The source's path, as the walk reached it.
    path: String,
    /// The line, as it prints below the JSON level.
    line: String,
}

/// A diagnostic's JSON image.
#[derive(Clone, Debug, serde::Serialize)]
struct JsonDiagnostic
{
    /// `error`, `warning` or `goal`.
    level: String,
    /// The refusal's vocabulary name, when the diagnostic carries a refusal.
    name: Option<String>,
    /// The message's stable key.
    key: String,
    /// The diagnostic's class.
    class: String,
    /// The message it leads with.
    message: String,
    /// The producer's own wording.
    title: String,
    /// The source's path, as the walk reached it.
    path: String,
    /// The primary locus, when the diagnostic is located.
    primary: Option<JsonLocus>,
    /// The context annotations.
    annotations: Vec<JsonLocus>,
    /// The rules its refusal stood inside, outermost first.
    contexts: Vec<JsonContext>,
    /// The hypotheses in scope.
    hypotheses: Vec<String>,
    /// The note it closes with.
    note: Option<String>,
    /// The fix it proposes: the bytes it replaces and their replacement.
    fix: Option<JsonFix>,
}

/// The fix of a diagnostic's JSON image.
#[derive(Clone, Debug, serde::Serialize)]
struct JsonFix
{
    /// The first byte replaced.
    start: usize,
    /// The byte past the last replaced; `start` for an insertion.
    end: usize,
    /// The text written in their place.
    replacement: String,
}

/// One context of a diagnostic's JSON image.
#[derive(Clone, Debug, serde::Serialize)]
struct JsonContext
{
    /// The rule's stable name.
    role: String,
    /// What the rule was doing.
    sentence: String,
    /// How the term was judged.
    judged: String,
    /// The binders it opened.
    binders: Vec<String>,
    /// Its term's bytes, when known.
    locus: Option<JsonLocus>,
}

/// One locus of a diagnostic's JSON image.
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

#[cfg(test)]
mod tests
{
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Locus;
    use super::located;

    #[test]
    fn a_locus_counts_lines_and_characters()
    {
        let text = SourceText::from("αβ\nγ x");
        let at = |start: usize, end: usize| {
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("ordered")
        };
        assert_eq!(
            Locus::of(text, at(8_usize, 9_usize)),
            Maybe::Present(Locus {
                span: at(8_usize, 9_usize),
                line: 2_usize,
                column: 3_usize,
            }),
            "the second line's third character"
        );
        assert_eq!(
            Locus::of(text, at(1_usize, 2_usize)),
            Maybe::Absent(located::Absent::OutsideText),
            "a span splitting a character is not located"
        );
    }
}
