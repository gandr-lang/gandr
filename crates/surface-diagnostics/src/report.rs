//! The builder: a refusal, an unsettled declaration, a goal, a warning or a
//! ledger line, at the source it sits in, made into a [`Diagnostic`].
//!
//! # The class says whose fact it is; the label says what the bytes are
//!
//! A refusal is classed by the [`FailureClass`] its producer's classifier
//! gives it, a declaration unsettled with no refusal produced by what its
//! unsettlement rests on, a goal as a goal, a builtin the source shadowed as a
//! warning and a ledger line as a line. The class sorts diagnostics; the
//! primary annotation is labelled with what its bytes are, never with the
//! class. The title is the producer's message, which names no byte offsets,
//! and a refusal's vocabulary name is the diagnostic's identifier, spelled as
//! a `refuses` payload spells it.
//!
//! | Kind | First line | Primary annotation and label | Note |
//! | ---- | ---------- | ---------------------------- | ---- |
//! | refusal | `error[<refusal>]: <message>` | the refusal's span, labelled with what the bytes there are | in words, what the declaration is expected to do and why the refusal leaves it unsettled |
//! | unsettled declaration | ``error: `<name>` states …; produced …`` and, for a suspended declaration, ``; it waits on `<hole>`, …`` | the declaration, labelled with how it is unsettled | none |
//! | goal | ``goal: `<name>` states …; produced …`` and, for a suspended declaration, ``; it waits on `<hole>`, …`` | the declaration, labelled with its surviving obligations | none |
//! | source refused as a whole | `error[<refusal>]: the source is not a list of declarations: …` | the refusal's span | none |
//! | shadowed builtin | ``warning[ShadowedBuiltin]: `<path>` shadows a builtin name; the source's binding wins`` | the shadowing name, labelled `shadows a builtin` | none |
//! | inferred exit | ``warning[explicit-exits]: this path ends without its exit; …`` | the tail, labelled with the exit inferred there; the fix writes that keyword before it | none |
//! | inferred run | ``warning[explicit-runs]: this computation stands where a value is read; …`` | the computation, labelled with the run inferred there and whether it performs an effect; the fix writes `run` before it, parenthesised where it begins a statement | none |
//! | deprecated use | ``warning[deprecated]: `<name>` is deprecated since <version>: <note>`` | the use, labelled `names a deprecated declaration` | none |
//! | ledger line | `<path>: <line>` | the declaration or refusal the line reports, when it has one | none |
//!
//! No message carries a byte range: a face locates the diagnostic by its
//! annotations, and an offset beside them is noise. Labels expose no core node
//! addresses. An empty path renders as `<input>`.
//!
//! # A shadowed builtin is a warning, named as the refusal it would be
//!
//! Under the default warn-and-allow shadow policy, a top-level declaration or a
//! binder named after a builtin wins, and the lowering records the shadowing
//! with the bytes of the name. Under `check` each record is a diagnostic of
//! class [`Class::Warning`], printed before the source's declarations in the
//! order shadowed; `test` prints none, because its ledger records settlements.
//! A warning settles nothing, so `gandr check` still exits zero on a source
//! whose only diagnostics are warnings. Its identifier is `ShadowedBuiltin`,
//! the refusal the reject policy files for the same bytes, so one name reads
//! the same fact under either policy. The alternative was a separate warning
//! code, and a second vocabulary for one fact would have a reader learn two
//! names. Reversal: a warning that is not a would-be refusal gets its own
//! vocabulary. Witness:
//! `tests::diagnostics::a_shadowed_builtin_is_a_warning`.
//!
//! # An inferred exit is a lint's finding, carrying its fix
//!
//! An exit the lowering inferred where a path through a body ends is a
//! [`Class::Lint`] warning of the `explicit-exits` lint, identified by the
//! lint's spelling (the `lint` module says why it is not a refusal's). Its
//! one annotation is the tail's own bytes, and its [`Fix`] inserts the
//! keyword, `return ` or `become `, at the tail's first byte: the edit that
//! writes the exit the lowering would infer, after which the lowering infers
//! nothing there and the lint finds nothing. Witness:
//! `tests::diagnostics::an_inferred_exit_is_a_finding_whose_fix_writes_its_keyword`.
//!
//! # An inferred run is a lint's finding, carrying its fix
//!
//! A computation written where a value is read, which the checker runs, is a
//! [`Class::Lint`] warning of the `explicit-runs` lint, identified by the
//! lint's spelling. Its one annotation is the computation's own bytes,
//! labelled with whether the run performs an effect, and its [`Fix`] inserts
//! `run ` at the computation's first byte, or rewrites it as `(run c)` where
//! it begins a statement or a block's tail, which a block would read as a
//! bind: the edit that writes the run the checker would infer, after which
//! the computation is a written run and the lint finds nothing. Witness:
//! `tests::diagnostics::an_inferred_run_is_a_finding_whose_fix_writes_its_keyword`.
//!
//! # A use of a deprecated declaration is a lint's finding, naming its note
//!
//! A written name that resolves to a declaration a `deprecated` attribute
//! marks is a [`Class::Lint`] warning of the `deprecated` lint at the use,
//! titled with the version and the note the attribute states, each left out
//! when unstated. It proposes no fix. Witness:
//! `tests::diagnostics::a_deprecated_use_is_a_finding_naming_its_note`.
//!
//! # The settle note says what was expected and why it did not happen
//!
//! A refused declaration closes with a note in words: what its source
//! expected of it — to check, to check owing some obligations, to be refused
//! with another refusal, to run to an outcome, or nothing, its expectation
//! being malformed — and that this refusal is why it is unsettled, then the
//! obligations that survive when any do. The alternative was the settle
//! comparison's own ledger spelling (``unsettled `a` states checks owing
//! 0``), which reads as the comparison's record, not as a reason.
//!
//! # Native universe-path diagnostics
//!
//! A checker `PathCode` refusal retains its code-node locus and
//! malformed-source class. Shape diagnostics can name the expected sum or
//! `Path_U` classifier; injection and case remain checking forms, not
//! unsupported language constructs. A missing origin remains an absent
//! annotation rather than an invented source span. The builder projects the
//! same typed refusal and causal roles ordinary checking uses, rather than a
//! second universe-specific pipeline, and certifies neither the candidate
//! path nor its evidence. Reversal: a source notation may supply more precise
//! origins; it must not change the refusal's semantic class or infer
//! certificate equality from its displayed maps.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use std::path::Path;

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::Failure;
use gandr_core_term::FailureClass;
use gandr_core_term::TrackingIssue;
use gandr_core_term::effect::Purity;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::RefusalName;
use gandr_surface_corpus::Stated;
use gandr_surface_corpus::Surviving;
use gandr_surface_lowering::DeprecatedUse;
use gandr_surface_lowering::InferredExit;
use gandr_surface_lowering::InferredRun;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Omitted;
use gandr_surface_lowering::OriginTable;
use gandr_surface_lowering::RunOperand;
use gandr_surface_lowering::RunSpelling;
use gandr_surface_lowering::namespace::ShadowedBuiltin;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::culprit::Culprit;
use crate::frame::contexts;
use crate::lint::Lint;
use crate::locus::Annotation;
use crate::locus::Annotations;
use crate::locus::Checked;
use crate::locus::Comparison;
use crate::locus::Label;
use crate::locus::PrimaryLabel;
use crate::locus::report_context;
use crate::message::Plain;
use crate::message::unsolved;
use crate::model::AnnotationKind;
use crate::model::Compared;
use crate::model::Diagnostic;
use crate::model::DiagnosticAnnotation;
use crate::model::DiagnosticDetail;
use crate::model::Excerpt;
use crate::model::Fix;
use crate::model::Identifier;
use crate::model::Locus;
use crate::model::Message;
use crate::model::MessageKey;
use crate::model::Severity;
use crate::model::expression;
use crate::model::fix;
use crate::model::producer;
use crate::spelled::Spellings;
use crate::spelled::kept;

quenchant_shape::reason_enum! {
    /// Why a diagnostic claims no span.
    pub mod report_span {
        /// The reason a diagnostic is unlocated.
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
            /// The ledger line records a source's standing, not a position in
            /// it.
            Standing,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a diagnostic carries no identifier.
    pub mod report_identifier {
        /// The reason a diagnostic names no refusal.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The diagnostic states what a declaration states and produced,
            /// or a source's standing: it carries no refusal to name.
            Statement,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a diagnostic carries no note.
    pub mod report_note {
        /// The reason a diagnostic closes with no note.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The diagnostic states what a declaration states and produced,
            /// or a source's standing: it carries no refusal to explain.
            Statement,
            /// The diagnostic is a warning: no declaration's settlement rests
            /// on it, so it names none.
            Warning,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a refusal is a declaration's own.
    pub mod upstream {
        /// The reason a refusal follows from no other.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The refusal names no declaration a refusal of its own left
            /// unsettled.
            Own,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a diagnostic names no tracking issue.
    pub mod tracking {
        /// The reason a diagnostic links no issue.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A refusal of what the author owes or wrote wrongly, or the
            /// engine's fault: nothing gandr has not built.
            Untracked,
            /// No refusal: an unsettlement, a goal, a warning, a lint or a
            /// ledger line.
            Unrefused,
        }
    }
}

/// What a diagnostic is about, and whose fact it records.
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
    /// A finding of a lint, by the lint.
    Lint(Lint),
    /// A ledger line: a source's standing.
    Ledger,
}

impl Class
{
    /// The issue tracking what an unimplemented refusal is missing, which
    /// every face of the diagnostic names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the issue an unimplemented refusal's class carries; any other
    ///   refusal is untracked, and every other class unrefused.
    /// - provides: the tracking issue a face writes and links.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unimplemented refusal, a malformed one and a goal
    ///   answer each of the three outcomes.
    /// - witness: `report::tests::only_an_unimplemented_refusal_names_its_issue`
    #[spec(ensures: |ret| match self {
        | Self::Refusal(FailureClass::Unimplemented(issue)) => ret == Maybe::Present(issue),
        | Self::Refusal(
            FailureClass::UserAbsence | FailureClass::MalformedSource | FailureClass::EngineFault,
        ) => ret == Maybe::Absent(tracking::Absent::Untracked),
        | Self::Unsettled(_) | Self::Goal | Self::Warning | Self::Lint(_) | Self::Ledger => {
            ret == Maybe::Absent(tracking::Absent::Unrefused)
        },
    })]
    #[inline]
    pub fn tracking(self) -> Maybe<TrackingIssue, tracking::Absent>
    {
        match self {
            Self::Refusal(class) => match class.tracking() {
                Maybe::Present(issue) => Maybe::Present(issue),
                Maybe::Absent(_) => Maybe::Absent(tracking::Absent::Untracked),
            },
            Self::Unsettled(_) | Self::Goal | Self::Warning | Self::Lint(_) | Self::Ledger => {
                Maybe::Absent(tracking::Absent::Unrefused)
            },
        }
    }
}

impl fmt::Display for Class
{
    /// Writes the failure class, the unsettlement, `goal`, `warning`, the
    /// lint's spelling or `ledger`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the producer's failure class, the unsettlement reason
    ///   or the class's own word; propagates destination failure.
    /// - provides: the human-readable class.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither output text nor an
    ///   independent destination-failure observer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the four unsettlement reasons remain distinguishable
    ///   from one refusal class, a goal, a warning, a lint and a ledger line.
    /// - witness: `report::tests::class_labels_keep_their_decision_surfaces_distinct`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Refusal(class) => fmt::Display::fmt(&class, f),
            Self::Unsettled(unsettlement) => fmt::Display::fmt(&unsettlement, f),
            Self::Goal => f.write_str("goal"),
            Self::Warning => f.write_str("warning"),
            Self::Lint(lint) => write!(f, "lint {lint}"),
            Self::Ledger => f.write_str("ledger"),
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
    /// It states a normal form, and its block's rules read the call to
    /// another, or to none.
    NormalForm,
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
    /// - hypothesis: L3 — all five unsettlement kinds have distinct class
    ///   labels.
    /// - witness: `report::tests::class_labels_keep_their_decision_surfaces_distinct`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Obligations => "surviving obligations",
            Self::Unproduced => "unproduced refusal",
            Self::RunOutcome => "another run outcome",
            Self::NormalForm => "another normal form",
            Self::Malformed => "malformed expectation",
        })
    }
}

/// What one diagnostic is about: the builder's input.
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
        /// The spellings of the types it and its failure name.
        spellings: &'step Spellings,
        /// The failure the checking machine kept, when it refused the body.
        failure: Maybe<&'step Failure, kept::Absent>,
        /// The unsettled declaration the refusal names, when it names one: the
        /// refusal follows from that declaration's and is a note, not an
        /// error of its own.
        upstream: Maybe<&'step DeclarationReport<'step>, upstream::Absent>,
    },
    /// A declaration unsettled with no refusal produced.
    Unsettled
    {
        /// The declaration, as the settle comparison reported it.
        declaration: &'step DeclarationReport<'step>,
        /// What its unsettlement rests on.
        unsettlement: Unsettlement,
        /// A refused declaration of its name, when its source holds one: the
        /// half the lowering could not read, so what the declaration owes
        /// follows from that refusal and is a note, not an error of its own.
        upstream: Maybe<&'step DeclarationReport<'step>, upstream::Absent>,
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
    /// An exit the lowering inferred, where a path through a body ends in a
    /// form that is no exit: a finding of the `explicit-exits` lint.
    InferredExit(&'step InferredExit),
    /// A run the checker inferred, where a computation stands in a position
    /// that reads a value: a finding of the `explicit-runs` lint.
    InferredRun(&'step InferredRun),
    /// A written name resolving to a declaration a `deprecated` attribute
    /// marks: a finding of the `deprecated` lint.
    Deprecated(&'step DeprecatedUse<'step>),
    /// A ledger line: a settled fixture, a pending source's refusal or
    /// declaration, or a pending source the lowering read.
    Ledger
    {
        /// The line, after the path.
        line: &'step str,
        /// The bytes it reports, when it reports a position.
        at: Maybe<ByteSpan, report_span::Absent>,
    },
}

/// The diagnostic `subject`, a part of the source at `path` whose text is
/// `text`, makes.
///
/// # Specification
/// - requires: the subject's spans, origins and spellings were made over
///   `text`.
/// - ensures: a [`Diagnostic`] whose severity, identifier, message, detail,
///   annotations, contexts, hypotheses, note, expression and excerpt are those
///   the module states for the subject; every span it carries lies inside
///   `text` on character boundaries, an unlocatable one left out with its
///   reason, never clamped.
/// - provides: the one builder every face's diagnostics come from.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a refusal, an unsettled declaration, a goal, a source
///   refused whole, a warning and a ledger line each build their kind; finite
///   UTF-8 boundaries expose clamping.
/// - witness: `tests::diagnostics::a_refused_declaration_is_located`
/// - witness: `tests::diagnostics::each_verb_prints_its_entries`
/// - witness: `report::tests::utf8_boundaries_are_checked_per_locus_without_clamping`
#[spec(ensures: |ref ret| ret.annotations.iter().all(|annotation| text.fragment(annotation.locus.span).is_ok())
    && match ret.span { Maybe::Present(span) => text.fragment(span).is_ok(), Maybe::Absent(_) => true })]
#[inline]
#[must_use]
pub fn diagnose(
    path: &Path,
    text: SourceText<'_>,
    subject: Subject<'_>,
) -> Diagnostic
{
    Report {
        path,
        text,
        subject,
    }
    .diagnostic()
}

/// The name a source with no path is rendered under.
pub const PATHLESS: &str = "<input>";

/// One subject at the source it sits in: the view the builder reads.
#[derive(Clone, Copy, Debug)]
struct Report<'step>
{
    /// The source's path, as the walk reached it.
    path: &'step Path,
    /// The source's text, which every span of the subject is measured against.
    text: SourceText<'step>,
    /// What the report is about.
    subject: Subject<'step>,
}

impl Report<'_>
{
    /// The diagnostic.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a term on one line and over two, and a lint finding
    ///   inside the text and past it, observe the expression and fix guards.
    /// - witness: `report::tests::only_a_one_line_term_is_quoted_as_the_expression`
    /// - witness: `report::tests::a_finding_past_the_text_proposes_no_fix`
    fn diagnostic(&self) -> Diagnostic
    {
        let annotations = self.annotations();
        let span = match annotations.primary {
            Maybe::Present(primary) => Maybe::Present(primary.span),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        let mut marked: Vec<DiagnosticAnnotation> = Vec::new();
        if let Maybe::Present(primary) = annotations.primary
            && let Maybe::Present(locus) = Locus::of(self.text, primary.span)
        {
            marked.push(DiagnosticAnnotation {
                kind: AnnotationKind::Primary,
                locus,
                label: alloc::format!("{}", PrimaryLabel {
                    label: primary.label,
                    comparison: self.comparison(),
                }),
            });
        }
        for slot in annotations.context {
            if let Maybe::Present(annotation) = slot
                && let Maybe::Present(locus) = Locus::of(self.text, annotation.span)
            {
                marked.push(DiagnosticAnnotation {
                    kind: AnnotationKind::Context,
                    locus,
                    label: alloc::format!("{}", annotation.label),
                });
            }
        }
        let (contexts, hypotheses) = match self.subject {
            Subject::Refused {
                origins,
                spellings,
                failure: Maybe::Present(failure),
                ..
            } => contexts(failure, origins, spellings, self.text, span),
            Subject::Refused { .. }
            | Subject::Unsettled { .. }
            | Subject::Goal(_)
            | Subject::Source(_)
            | Subject::Shadowed(_)
            | Subject::InferredExit(_)
            | Subject::InferredRun(_)
            | Subject::Deprecated(_)
            | Subject::Ledger { .. } => (Vec::new(), Vec::new()),
        };
        let expression = match span {
            Maybe::Present(span) => match self.text.fragment(span) {
                Ok(fragment) if !fragment.as_ref().contains('\n') => {
                    Maybe::Present(String::from(fragment.as_ref()))
                },
                Ok(_) | Err(_) => Maybe::Absent(expression::Absent::Multiline),
            },
            Maybe::Absent(_) => Maybe::Absent(expression::Absent::Unlocated),
        };
        let covered = marked.iter().map(|annotation| annotation.locus.span).chain(
            contexts.iter().filter_map(|context| match context.locus {
                Maybe::Present(locus) => Some(locus.span),
                Maybe::Absent(_) => None,
            }),
        );
        let excerpt = match excerpt(self.text, covered) {
            Maybe::Present(excerpt) => Maybe::Present(excerpt),
            Maybe::Absent(()) => Maybe::Absent(match span {
                Maybe::Absent(reason) => reason,
                Maybe::Present(_) => report_span::Absent::OutsideText,
            }),
        };
        let comparison = self.comparison();
        let owned = |side: Maybe<&str, crate::spelled::spelling::Absent>| match side {
            Maybe::Present(spelled) => Maybe::Present(String::from(spelled)),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        Diagnostic {
            path: self.path.to_path_buf(),
            severity: match self.subject {
                Subject::Goal(_) => Severity::Goal,
                Subject::Shadowed(_)
                | Subject::InferredExit(_)
                | Subject::InferredRun(_)
                | Subject::Deprecated(_) => Severity::Warning,
                Subject::Ledger { .. } => Severity::Ledger,
                Subject::Refused {
                    upstream: Maybe::Present(_),
                    ..
                }
                | Subject::Unsettled {
                    upstream: Maybe::Present(_),
                    ..
                } => Severity::Note,
                Subject::Refused { .. } | Subject::Unsettled { .. } | Subject::Source(_) => {
                    Severity::Error
                },
            },
            identifier: self.identifier(),
            message: Message {
                key: self.key(),
                text: alloc::format!("{}", MessageText(self.subject)),
            },
            detail: DiagnosticDetail {
                class: self.class(),
                title: alloc::format!("{}", TitleText(self.subject)),
                compared: Compared {
                    expected: owned(comparison.expected),
                    found: owned(comparison.found),
                },
                producer: match self.subject {
                    Subject::Refused {
                        refusal, failure, ..
                    } => Maybe::Present(match failure {
                        Maybe::Present(failure) => alloc::format!("{refusal:?}; {failure:?}"),
                        Maybe::Absent(_) => alloc::format!("{refusal:?}"),
                    }),
                    Subject::Source(refusal) => Maybe::Present(alloc::format!("{refusal:?}")),
                    Subject::Unsettled { .. }
                    | Subject::Goal(_)
                    | Subject::Shadowed(_)
                    | Subject::InferredExit(_)
                    | Subject::InferredRun(_)
                    | Subject::Deprecated(_)
                    | Subject::Ledger { .. } => Maybe::Absent(producer::Absent::Statement),
                },
            },
            span,
            annotations: marked,
            contexts,
            elsewhere: Vec::new(),
            hypotheses,
            note: match self.subject {
                Subject::Refused {
                    declaration,
                    upstream: Maybe::Present(upstream),
                    ..
                } => Maybe::Present(alloc::format!("{}", UpstreamNoteText {
                    declaration,
                    upstream,
                })),
                Subject::Refused { declaration, .. } => {
                    Maybe::Present(alloc::format!("{}", NoteText(declaration)))
                },
                Subject::Unsettled {
                    declaration,
                    upstream: Maybe::Present(upstream),
                    ..
                } => Maybe::Present(alloc::format!("{}", UnreadHalfNoteText {
                    declaration,
                    upstream,
                })),
                Subject::Unsettled { .. }
                | Subject::Goal(_)
                | Subject::Source(_)
                | Subject::Ledger { .. } => Maybe::Absent(report_note::Absent::Statement),
                Subject::Shadowed(_)
                | Subject::InferredExit(_)
                | Subject::InferredRun(_)
                | Subject::Deprecated(_) => Maybe::Absent(report_note::Absent::Warning),
            },
            expression,
            excerpt,
            fix: match self.subject {
                Subject::InferredExit(inferred) => {
                    match ByteSpan::new(inferred.span.start(), inferred.span.start()) {
                        Ok(span) if self.text.fragment(span).is_ok() => Maybe::Present(Fix {
                            span,
                            replacement: alloc::format!("{} ", inferred.exit),
                        }),
                        Ok(_) | Err(_) => Maybe::Absent(fix::Absent::Unproposed),
                    }
                },
                Subject::InferredRun(inferred) => {
                    match (inferred.site.spelling, inferred.site.operand) {
                        (RunSpelling::Bare, RunOperand::Tight) => {
                            match ByteSpan::new(inferred.span.start(), inferred.span.start()) {
                                Ok(span) if self.text.fragment(span).is_ok() => {
                                    Maybe::Present(Fix {
                                        span,
                                        replacement: String::from("run "),
                                    })
                                },
                                Ok(_) | Err(_) => Maybe::Absent(fix::Absent::Unproposed),
                            }
                        },
                        (spelling, operand) => self.text.fragment(inferred.span).map_or(
                            Maybe::Absent(fix::Absent::Unproposed),
                            |written| {
                                let run = match operand {
                                    RunOperand::Tight => {
                                        alloc::format!("run {}", written.as_ref())
                                    },
                                    RunOperand::Grouped => {
                                        alloc::format!("run ({})", written.as_ref())
                                    },
                                };
                                Maybe::Present(Fix {
                                    span: inferred.span,
                                    replacement: match spelling {
                                        RunSpelling::Bare => run,
                                        RunSpelling::Parenthesised => alloc::format!("({run})"),
                                    },
                                })
                            },
                        ),
                    }
                },
                Subject::Refused { .. }
                | Subject::Unsettled { .. }
                | Subject::Goal(_)
                | Subject::Source(_)
                | Subject::Shadowed(_)
                | Subject::Deprecated(_)
                | Subject::Ledger { .. } => Maybe::Absent(fix::Absent::Unproposed),
            },
        }
    }

    /// What the report is about, and whose fact it records.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused declaration and a source refused as a whole are
    ///   [`Class::Refusal`] with the class their producer's classifier gives; a
    ///   declaration unsettled with no refusal is [`Class::Unsettled`] with
    ///   what it rests on; a goal is [`Class::Goal`]; a shadowed builtin is
    ///   [`Class::Warning`]; an inferred exit is [`Class::Lint`] of the
    ///   `explicit-exits` lint, an inferred run of the `explicit-runs` lint, a
    ///   deprecated use of the `deprecated` lint; a ledger line
    ///   [`Class::Ledger`].
    /// - provides: the class a reader sorts diagnostics by.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite real reports expose the producer's exact class
    ///   across refused declarations and whole-source refusal; unproduced
    ///   expectations and goals distinguish the non-refusal branches, and a
    ///   lint finding its lint.
    /// - witness: `tests::diagnostics::a_refused_declaration_is_located`
    /// - witness: `tests::diagnostics::each_verb_prints_its_entries`
    /// - witness: `tests::diagnostics::an_inferred_exit_is_a_finding_whose_fix_writes_its_keyword`
    /// - witness: `tests::diagnostics::an_inferred_run_is_a_finding_whose_fix_writes_its_keyword`
    #[spec(ensures: |ret| ret == match self.subject {
        Subject::Refused { refusal, .. } => Class::Refusal(refusal.classify()),
        Subject::Unsettled { unsettlement, .. } => Class::Unsettled(unsettlement),
        Subject::Goal(_) => Class::Goal,
        Subject::Source(refusal) => Class::Refusal(refusal.classify()),
        Subject::Shadowed(_) => Class::Warning,
        Subject::InferredExit(_) => Class::Lint(Lint::ExplicitExits),
        Subject::InferredRun(_) => Class::Lint(Lint::ExplicitRuns),
        Subject::Deprecated(_) => Class::Lint(Lint::Deprecated),
        Subject::Ledger { .. } => Class::Ledger,
    })]
    fn class(&self) -> Class
    {
        match self.subject {
            Subject::Refused { refusal, .. } => Class::Refusal(refusal.classify()),
            Subject::Unsettled { unsettlement, .. } => Class::Unsettled(unsettlement),
            Subject::Goal(_) => Class::Goal,
            Subject::Source(refusal) => Class::Refusal(refusal.classify()),
            Subject::Shadowed(_) => Class::Warning,
            Subject::InferredExit(_) => Class::Lint(Lint::ExplicitExits),
            Subject::InferredRun(_) => Class::Lint(Lint::ExplicitRuns),
            Subject::Deprecated(_) => Class::Lint(Lint::Deprecated),
            Subject::Ledger { .. } => Class::Ledger,
        }
    }

    /// The message's stable key.
    ///
    /// # Specification
    /// trivial.
    fn key(&self) -> MessageKey
    {
        match self.subject {
            Subject::Refused { refusal, .. } => MessageKey::Refusal(refusal.name()),
            Subject::Source(refusal) => MessageKey::Refusal(Refusal::Lowering(refusal).name()),
            Subject::Shadowed(_) => MessageKey::Refusal(RefusalName::ShadowedBuiltin),
            Subject::InferredExit(_) => MessageKey::Lint(Lint::ExplicitExits),
            Subject::InferredRun(_) => MessageKey::Lint(Lint::ExplicitRuns),
            Subject::Deprecated(_) => MessageKey::Lint(Lint::Deprecated),
            Subject::Unsettled { unsettlement, .. } => MessageKey::Unsettled(unsettlement),
            Subject::Goal(_) => MessageKey::Goal,
            Subject::Ledger { .. } => MessageKey::Ledger,
        }
    }

    /// The vocabulary name of the refusal or the lint the report is about.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused declaration names the refusal it produced, a source
    ///   refused as a whole the lowering's refusal, and a shadowed builtin
    ///   `ShadowedBuiltin`, each spelled as a `refuses` payload spells it; an
    ///   inferred exit names the `explicit-exits` lint, an inferred run the
    ///   `explicit-runs` lint, a deprecated use the `deprecated` lint.
    /// - provides: the identifier a face writes beside the message.
    /// - fails: never; an unsettled declaration, a goal and a ledger line carry
    ///   no refusal to name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — checker and lowering refusals expose their stable
    ///   vocabulary identifiers; a lint finding exposes the lint's; a goal
    ///   exposes statement absence.
    /// - witness: `tests::diagnostics::a_report_preserves_refusal_identity_and_title_payloads`
    /// - witness: `tests::diagnostics::an_inferred_exit_is_a_finding_whose_fix_writes_its_keyword`
    #[spec(ensures: |ret| match (self.subject, ret) {
        (Subject::Refused { refusal, .. }, Maybe::Present(identifier)) => identifier == Identifier::Refusal(refusal.name().spelling()),
        (Subject::Source(refusal), Maybe::Present(identifier)) => identifier == Identifier::Refusal(Refusal::Lowering(refusal).name().spelling()),
        (Subject::Shadowed(_), Maybe::Present(identifier)) => identifier == Identifier::Refusal(RefusalName::ShadowedBuiltin.spelling()),
        (Subject::InferredExit(_), Maybe::Present(identifier)) => identifier == Identifier::Lint(Lint::ExplicitExits),
        (Subject::InferredRun(_), Maybe::Present(identifier)) => identifier == Identifier::Lint(Lint::ExplicitRuns),
        (Subject::Deprecated(_), Maybe::Present(identifier)) => identifier == Identifier::Lint(Lint::Deprecated),
        (Subject::Unsettled { .. } | Subject::Goal(_) | Subject::Ledger { .. }, Maybe::Absent(report_identifier::Absent::Statement)) => true,
        _ => false,
    })]
    fn identifier(&self) -> Maybe<Identifier, report_identifier::Absent>
    {
        match self.subject {
            Subject::Refused { refusal, .. } => {
                Maybe::Present(Identifier::Refusal(refusal.name().spelling()))
            },
            Subject::Source(refusal) => Maybe::Present(Identifier::Refusal(
                Refusal::Lowering(refusal).name().spelling(),
            )),
            Subject::Shadowed(_) => {
                Maybe::Present(Identifier::Refusal(RefusalName::ShadowedBuiltin.spelling()))
            },
            Subject::InferredExit(_) => Maybe::Present(Identifier::Lint(Lint::ExplicitExits)),
            Subject::InferredRun(_) => Maybe::Present(Identifier::Lint(Lint::ExplicitRuns)),
            Subject::Deprecated(_) => Maybe::Present(Identifier::Lint(Lint::Deprecated)),
            Subject::Unsettled { .. } | Subject::Goal(_) | Subject::Ledger { .. } => {
                Maybe::Absent(report_identifier::Absent::Statement)
            },
        }
    }

    /// The types the report's refusal compares.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused declaration compares what [`Comparison::of`] reads
    ///   for its refusal; every other report compares no types.
    /// - provides: the expected and found types a primary label spells.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type mismatch compares both of its types; a goal
    ///   compares none.
    /// - witness: `tests::diagnostics::a_mismatch_label_spells_both_types`
    #[spec(ensures: |ret| match self.subject {
        Subject::Refused { refusal, spellings, .. } => ret == Comparison::of(refusal, spellings),
        Subject::Unsettled { .. } | Subject::Goal(_) | Subject::Source(_) | Subject::Shadowed(_) | Subject::InferredExit(_) | Subject::InferredRun(_) | Subject::Deprecated(_) | Subject::Ledger { .. } => ret == Comparison::none(),
    })]
    fn comparison(&self) -> Comparison<'_>
    {
        match self.subject {
            Subject::Refused {
                refusal, spellings, ..
            } => Comparison::of(refusal, spellings),
            Subject::Unsettled { .. }
            | Subject::Goal(_)
            | Subject::Source(_)
            | Subject::Shadowed(_)
            | Subject::InferredExit(_)
            | Subject::InferredRun(_)
            | Subject::Deprecated(_)
            | Subject::Ledger { .. } => Comparison::none(),
        }
    }

    /// Every locus the report marks, each checked against the source's text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the subject's loci as its producer recorded them; a primary
    ///   locus the text cannot answer becomes the
    ///   [`report_span::Absent::OutsideText`] absence, and such a context locus
    ///   is marked `OutsideText` in its original slot.
    /// - provides: the only loci a diagnostic's annotations come from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite real producer spans and UTF-8 boundary cases
    ///   expose unvalidated or clamped locations; independent primary and
    ///   context validation preserves the surviving causal slot.
    /// - witness: `tests::diagnostics::a_report_exposes_the_context_it_marks`
    /// - witness: `report::tests::utf8_boundaries_are_checked_per_locus_without_clamping`
    #[spec(ensures: |ref ret| {
        let primary = match ret.primary {
            Maybe::Present(annotation) => self.text.fragment(annotation.span).is_ok() && match self.subject {
                Subject::Refused { refusal, .. } => annotation.label == Label::Culprit(Culprit::of(refusal)),
                Subject::Source(refusal) => annotation.label == Label::Culprit(Culprit::of(Refusal::Lowering(refusal))),
                Subject::Unsettled { declaration, unsettlement: Unsettlement::Obligations, .. }
                    | Subject::Goal(declaration) => annotation.label == Label::Surviving(declaration.surviving()),
                Subject::Unsettled { unsettlement, .. } => annotation.label == Label::Unsettled(unsettlement),
                Subject::Shadowed(_) => annotation.label == Label::Shadows,
                Subject::InferredExit(inferred) => annotation.label == Label::Inferred(inferred.exit),
                Subject::InferredRun(inferred) => annotation.label == Label::Ran(inferred.purity),
                Subject::Deprecated(_) => annotation.label == Label::Deprecated,
                Subject::Ledger { .. } => annotation.label == Label::Reported,
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
            Subject::Refused {
                declaration,
                refusal,
                origins,
                ..
            } => Annotations::refusal(refusal, declaration.span(), origins),
            Subject::Unsettled {
                declaration,
                unsettlement: Unsettlement::Obligations,
                ..
            }
            | Subject::Goal(declaration) => Annotations::at(
                declaration.span(),
                Label::Surviving(declaration.surviving()),
            ),
            Subject::Unsettled {
                declaration,
                unsettlement: Unsettlement::Malformed,
                ..
            } => Annotations::malformed(declaration.stated(), declaration.span()),
            Subject::Unsettled {
                declaration,
                unsettlement:
                    unsettlement @ (Unsettlement::Unproduced
                    | Unsettlement::RunOutcome
                    | Unsettlement::NormalForm),
                ..
            } => Annotations::at(declaration.span(), Label::Unsettled(unsettlement)),
            Subject::Source(refusal) => Annotations::lowering(refusal),
            Subject::Shadowed(shadowed) => Annotations::at(shadowed.span, Label::Shadows),
            Subject::InferredExit(inferred) => {
                Annotations::at(inferred.span, Label::Inferred(inferred.exit))
            },
            Subject::InferredRun(inferred) => {
                Annotations::at(inferred.span, Label::Ran(inferred.purity))
            },
            Subject::Deprecated(used) => Annotations::at(used.span, Label::Deprecated),
            Subject::Ledger { at, .. } => match at {
                Maybe::Present(span) => Annotations::at(span, Label::Reported),
                Maybe::Absent(reason) => Annotations {
                    primary: Maybe::Absent(reason),
                    context: [
                        Maybe::Absent(report_context::Absent::Unnamed),
                        Maybe::Absent(report_context::Absent::Unnamed),
                    ],
                },
            },
        };
        let inside = |annotation: &Annotation| self.text.fragment(annotation.span).is_ok();
        let primary = match annotations.primary {
            Maybe::Present(primary) if inside(&primary) => Maybe::Present(primary),
            Maybe::Present(_) => Maybe::Absent(report_span::Absent::OutsideText),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        let [first, second] = annotations.context.map(|annotation| match annotation {
            Maybe::Present(annotation) if inside(&annotation) => Maybe::Present(annotation),
            Maybe::Present(_) => Maybe::Absent(report_context::Absent::OutsideText),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        });
        Annotations {
            primary,
            context: [first, second],
        }
    }
}

/// The whole lines of `text` the spans `covered` touch.
///
/// # Specification
/// - requires: every span lies inside `text` on character boundaries.
/// - ensures: the lines from the one holding the earliest start to the one
///   holding the latest end, without the final line break, with the byte and
///   one-based line they start at; absent when no span is given.
/// - provides: the excerpt a diagnostic carries in place of its source.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two spans on lines two and three excerpt exactly those
///   lines; no span excerpts nothing.
/// - witness: `report::tests::an_excerpt_is_the_lines_its_spans_touch`
#[spec(ensures: |ret| match ret {
    Maybe::Present(ref excerpt) => text.as_ref().get(usize::from(excerpt.start) ..).is_some_and(|rest| rest.starts_with(excerpt.text.as_str())),
    Maybe::Absent(()) => true,
})]
fn excerpt(
    text: SourceText<'_>,
    covered: impl Iterator<Item = ByteSpan>,
) -> Maybe<Excerpt, ()>
{
    let mut bounds: Maybe<(usize, usize), ()> = Maybe::Absent(());
    for span in covered {
        let (start, end) = (usize::from(span.start()), usize::from(span.end()));
        bounds = Maybe::Present(match bounds {
            Maybe::Present((low, high)) => (low.min(start), high.max(end)),
            Maybe::Absent(()) => (start, end),
        });
    }
    let Maybe::Present((low, high)) = bounds
    else {
        return Maybe::Absent(());
    };
    let source = text.as_ref();
    let before = source.get(.. low).unwrap_or_default();
    let start = before
        .rfind('\n')
        .map_or(0_usize, |newline| newline.saturating_add(1));
    let after = source.get(high ..).unwrap_or_default();
    let end = after
        .find('\n')
        .map_or(source.len(), |newline| high.saturating_add(newline));
    Maybe::Present(Excerpt {
        text: String::from(source.get(start .. end).unwrap_or_default()),
        start: ByteOffset::from(start),
        line: before.matches('\n').count().saturating_add(1),
    })
}

/// A report's title: the producer's message for a refusal, what the
/// declaration states and produced otherwise, and what a warning or a lint's
/// finding is about.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct TitleText<'step>(Subject<'step>);

impl fmt::Display for TitleText<'_>
{
    /// Writes the producer's message for a refusal, what the declaration
    /// states and produced otherwise, and a ledger line itself.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the refusal's message or the declaration identity with
    ///   its stated and produced outcomes, and the holes a suspended
    ///   declaration waits on by name; whole-source refusal keeps its scope.
    /// - provides: the producer's own wording, which a detailed level shows.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unresolved-name and goal titles retain source names
    ///   and numeric roles; mismatch titles expose no core addresses; a
    ///   suspended declaration's goal names the hole it waits on.
    /// - witness: `tests::diagnostics::a_report_preserves_refusal_identity_and_title_payloads`
    /// - witness: `tests::diagnostics::a_suspended_goal_names_the_hole_it_waits_on`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
            Subject::Refused {
                refusal: Refusal::Lowering(refusal),
                ..
            } => fmt::Display::fmt(&refusal, f),
            Subject::Refused {
                refusal: Refusal::Checking(refusal),
                ..
            } => fmt::Display::fmt(&Checked(refusal), f),
            Subject::Refused {
                refusal: Refusal::Corpus(refusal),
                ..
            } => fmt::Display::fmt(&refusal, f),
            Subject::Unsettled { declaration, .. } | Subject::Goal(declaration) => {
                write!(
                    f,
                    "`{}` states {}; produced {}",
                    declaration.name(),
                    declaration.stated(),
                    declaration.outcome()
                )?;
                let mut waits = declaration.waits().iter();
                if let Some(first) = waits.next() {
                    write!(f, "; it waits on `{first}`")?;
                    for hole in waits {
                        write!(f, ", `{hole}`")?;
                    }
                }
                Ok(())
            },
            Subject::Source(refusal) => {
                write!(f, "the lowering refused the source as a whole: {refusal}")
            },
            Subject::Shadowed(shadowed) => write!(
                f,
                "`{}` shadows a builtin name; the source's binding wins",
                shadowed.path
            ),
            Subject::InferredExit(inferred) => write!(
                f,
                "this path ends without its exit; the lowering infers `{}`, which the \
                 `{}` lint asks to be written",
                inferred.exit,
                Lint::ExplicitExits
            ),
            Subject::InferredRun(inferred) => write!(
                f,
                "this computation {} where a value is read; the checker infers `run`, which \
                 the `{}` lint asks to be written",
                match inferred.purity {
                    Purity::Pure => "stands",
                    Purity::Effectful => "performs an effect",
                },
                Lint::ExplicitRuns
            ),
            Subject::Deprecated(used) => {
                write!(f, "`{}` is deprecated", used.name)?;
                if let Some(ref since) = used.deprecation.since {
                    write!(f, " since {since}")?;
                }
                if let Some(ref note) = used.deprecation.note {
                    write!(f, ": {note}")?;
                }
                Ok(())
            },
            Subject::Ledger { line, .. } => f.write_str(line),
        }
    }
}

/// The message a report leads with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct MessageText<'step>(Subject<'step>);

impl fmt::Display for MessageText<'_>
{
    /// Writes a refusal's plain message, and every other report's title.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused declaration writes its refusal's plain message, and
    ///   an omitted implicit the solver left unbound names the implicit and the
    ///   function its call wrote, where the origins record them, as does a
    ///   model slot no module or more than one answers, naming every module
    ///   that answers it; a source refused as a whole says so, then the plain
    ///   message; every other report writes its title, which is already the
    ///   user's.
    /// - provides: the first line of a diagnostic.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one refusal of every vocabulary name writes a
    ///   single-line message naming no grammar sort; a type mismatch's message
    ///   differs from its producer's title.
    /// - witness: `message::tests::every_refusal_name_has_a_plain_message`
    /// - witness: `tests::diagnostics::a_mismatch_label_spells_both_types`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
            Subject::Refused {
                refusal: refusal @ Refusal::Checking(CheckRefusal::ImplicitUnsolved { at, reason }),
                origins,
                ..
            } => match origins.omitted(at) {
                Maybe::Present(
                    &Omitted::Implicit {
                        ref function,
                        ref implicit,
                    }
                    | &Omitted::Model {
                        ref function,
                        ref implicit,
                        ..
                    },
                ) => match unsolved(reason) {
                    Maybe::Present(why) => write!(
                        f,
                        "the solver cannot determine the implicit `{implicit}` this call to \
                         `{function}` omits: {why}; supply it as `{function}[{implicit} = \
                         …](…)`"
                    ),
                    Maybe::Absent(()) => write!(
                        f,
                        "the implicit `{implicit}` this call to `{function}` omits is determined \
                         by neither its arguments nor the type it is checked against; supply it \
                         as `{function}[{implicit} = …](…)`"
                    ),
                },
                Maybe::Present(&Omitted::Wildcard) => match unsolved(reason) {
                    Maybe::Present(why) => write!(
                        f,
                        "the solver cannot determine the term this `_` stands for: {why}; write \
                         the term"
                    ),
                    Maybe::Absent(()) => f.write_str(
                        "no equation determines the term this `_` stands for; write the term",
                    ),
                },
                Maybe::Absent(_) => fmt::Display::fmt(&Plain(refusal), f),
            },
            Subject::Refused {
                refusal: refusal @ Refusal::Checking(CheckRefusal::ModelUnanswered { at }),
                origins,
                ..
            } => match origins.omitted(at) {
                Maybe::Present(&Omitted::Model {
                    ref function,
                    ref implicit,
                    ref candidates,
                }) => {
                    write!(
                        f,
                        "no module in scope answers the model implicit `{implicit}` this call to \
                         `{function}` omits"
                    )?;
                    if !candidates.is_empty() {
                        f.write_str(" at the types its arguments force: ")?;
                        named(f, candidates.iter().map(String::as_str))?;
                        f.write_str(if candidates.len() == 1 {
                            " does not"
                        }
                        else {
                            " do not"
                        })?;
                    }
                    write!(f, "; supply one as `{function}[{implicit} = …](…)`")
                },
                Maybe::Present(&(Omitted::Implicit { .. } | Omitted::Wildcard))
                | Maybe::Absent(_) => fmt::Display::fmt(&Plain(refusal), f),
            },
            Subject::Refused {
                refusal: refusal @ Refusal::Checking(CheckRefusal::ModelAmbiguous { at, survivors }),
                origins,
                ..
            } => match origins.omitted(at) {
                Maybe::Present(&Omitted::Model {
                    ref function,
                    ref implicit,
                    ref candidates,
                }) => {
                    write!(
                        f,
                        "more than one module in scope answers the model implicit `{implicit}` \
                         this call to `{function}` omits: "
                    )?;
                    named(
                        f,
                        survivors
                            .places()
                            .filter_map(|place| candidates.get(usize::from(place)))
                            .map(String::as_str),
                    )?;
                    let beyond = u32::from(survivors.beyond());
                    if beyond > 0 {
                        write!(f, ", and {beyond} more")?;
                    }
                    write!(
                        f,
                        "; supply the one meant as `{function}[{implicit} = …](…)`"
                    )
                },
                Maybe::Present(&(Omitted::Implicit { .. } | Omitted::Wildcard))
                | Maybe::Absent(_) => fmt::Display::fmt(&Plain(refusal), f),
            },
            Subject::Refused { refusal, .. } => fmt::Display::fmt(&Plain(refusal), f),
            Subject::Source(refusal) => write!(
                f,
                "the source is not a list of declarations: {}",
                Plain(Refusal::Lowering(refusal))
            ),
            Subject::Unsettled { .. }
            | Subject::Goal(_)
            | Subject::Shadowed(_)
            | Subject::InferredExit(_)
            | Subject::InferredRun(_)
            | Subject::Deprecated(_)
            | Subject::Ledger { .. } => fmt::Display::fmt(&TitleText(self.0), f),
        }
    }
}

/// Write `names` as a list in prose, each in backticks: `` `A` ``,
/// `` `A` and `B` ``, `` `A`, `B` and `C` ``.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every name once, in order, the last two joined by `and` and every
///   earlier pair by a comma; nothing for no name.
/// - fails: if the formatter rejects a write.
/// - panics: none.
/// - executable: none — the formatter exposes no output buffer.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — an ambiguous slot names its two modules.
/// - witness: `tests::diagnostics::an_ambiguous_model_slot_names_every_module_that_answers_it_739`
fn named<'name>(
    f: &mut fmt::Formatter<'_>,
    names: impl Iterator<Item = &'name str>,
) -> fmt::Result
{
    let mut names = names.peekable();
    let mut first = true;
    while let Some(name) = names.next() {
        if !first {
            f.write_str(if names.peek().is_some() {
                ", "
            }
            else {
                " and "
            })?;
        }
        write!(f, "`{name}`")?;
        first = false;
    }
    Ok(())
}

/// The note a refused declaration closes with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct NoteText<'step>(&'step DeclarationReport<'step>);

impl fmt::Display for NoteText<'_>
{
    /// Writes, in words, what the declaration is expected to do and that this
    /// refusal leaves it unsettled, then the obligations that survive when any
    /// do.
    ///
    /// # Specification
    /// - requires: the declaration produced a refusal.
    /// - ensures: names the declaration; says it is expected to check, to check
    ///   owing its stated count, to be refused with its stated refusal, to run
    ///   to its stated outcome, or to be refused and run, or that its
    ///   expectation states nothing and why; says the refusal is what leaves it
    ///   unsettled, or for a refusal and a run what it was refused with and ran
    ///   to; then the surviving obligations exactly when the ledger is
    ///   nonempty.
    /// - provides: the note after a refused declaration's snippet.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration expected to check, one owing three
    ///   obligations and one expecting another refusal each say what they
    ///   expected, with their counts and names.
    /// - witness: `tests::diagnostics::the_settle_note_says_what_was_expected_in_words`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let name = self.0.name();
        match *self.0.stated() {
            Stated::Verdict(Outcome::Checks(owing)) if usize::from(owing) == 0_usize => {
                write!(
                    f,
                    "`{name}` is expected to check, and this refusal leaves it unsettled"
                )?;
            },
            Stated::Verdict(Outcome::Checks(owing)) => write!(
                f,
                "`{name}` is expected to check owing {owing} obligations, and this refusal leaves \
                 it unsettled"
            )?,
            Stated::Verdict(Outcome::Refuses(expected)) => write!(
                f,
                "`{name}` is expected to be refused with {expected}, and this refusal is not \
                 that one"
            )?,
            Stated::Verdict(Outcome::Runs(ref spelled)) => write!(
                f,
                "`{name}` is expected to run to {spelled}, and this refusal leaves it unsettled"
            )?,
            Stated::Verdict(Outcome::Normalizes(ref spelled)) => write!(
                f,
                "`{name}` is expected to read {spelled}, and this refusal leaves it unsettled"
            )?,
            Stated::Verdict(Outcome::Decomposes(ref spelled)) => write!(
                f,
                "`{name}` is expected to decompose to {spelled}, and this refusal leaves it \
                 unsettled"
            )?,
            Stated::Verdict(Outcome::RefusesRunning(expected, ref spelled)) => {
                match self.0.outcome() {
                    Outcome::RefusesRunning(refused, ref ran) => write!(
                        f,
                        "`{name}` is expected to be refused with {expected} and run to {spelled}, and \
                     it is refused with {refused} and runs to {ran}"
                    )?,
                    Outcome::Checks(_)
                    | Outcome::Refuses(_)
                    | Outcome::Runs(_)
                    | Outcome::Normalizes(_)
                    | Outcome::Decomposes(_) => {
                        write!(
                            f,
                            "`{name}` is expected to be refused with {expected} and run to {spelled}, \
                         and this refusal leaves nothing to run"
                        )?;
                    },
                }
            },
            Stated::Malformed(fault) => {
                write!(f, "`{name}` states no verdict to settle against: {fault}")?;
            },
        }
        let surviving = self.0.surviving();
        if surviving != Surviving::default() {
            write!(f, "; surviving obligations: {surviving}")?;
        }
        Ok(())
    }
}

/// The note a declaration left unsettled by another's refusal closes with.
#[derive(Clone, Copy, Debug)]
struct UpstreamNoteText<'step>
{
    /// The declaration the note is about.
    declaration: &'step DeclarationReport<'step>,
    /// The unsettled declaration its refusal names.
    upstream: &'step DeclarationReport<'step>,
}

impl fmt::Display for UpstreamNoteText<'_>
{
    /// Writes that the declaration is expected to do what [`NoteText`] says,
    /// and that the refusal of the declaration it names leaves it unsettled.
    ///
    /// # Specification
    /// - requires: the declaration's refusal names `upstream`.
    /// - ensures: names both declarations; for one expected to check, says so
    ///   and that `upstream`'s refusal leaves it unsettled; for any other
    ///   expectation, the [`NoteText`] of the declaration followed by the name
    ///   of the refused declaration it rests on.
    /// - provides: the note of a declaration a refusal elsewhere leaves
    ///   unsettled, which reads as the cause, not as a second error.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration calling a refused one is noted as left
    ///   unsettled by that refusal, naming both.
    /// - witness: `tests::diagnostics::a_declaration_naming_a_refused_one_is_a_note`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let name = self.declaration.name();
        let upstream = self.upstream.name();
        match *self.declaration.stated() {
            Stated::Verdict(Outcome::Checks(owing))
                if usize::from(owing) == 0_usize
                    && self.declaration.surviving() == Surviving::default() =>
            {
                write!(
                    f,
                    "`{name}` is expected to check, and the refusal of `{upstream}` leaves it \
                     unsettled"
                )
            },
            Stated::Verdict(_) | Stated::Malformed(_) => write!(
                f,
                "{}; it rests on `{upstream}`, which is refused",
                NoteText(self.declaration)
            ),
        }
    }
}

/// The note a declaration closes with when a refused form of its name may be
/// the half it lacks.
#[derive(Clone, Copy, Debug)]
struct UnreadHalfNoteText<'step>
{
    /// The unsettled declaration the note is about.
    declaration: &'step DeclarationReport<'step>,
    /// The refused declaration of its name.
    upstream: &'step DeclarationReport<'step>,
}

impl fmt::Display for UnreadHalfNoteText<'_>
{
    /// Writes what the declaration states and produced, and that a form of
    /// its name the lowering refused leaves it so.
    ///
    /// # Specification
    /// - requires: `upstream` is refused and shares the declaration's name.
    /// - ensures: names the declaration, its stated and produced outcomes and
    ///   the refused form's name.
    /// - provides: the note of a declaration whose other half the lowering
    ///   could not read, which reads as the cause, not as a second error.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a signature whose definition is written with a
    ///   misspelt `def` is noted as left unsettled by the refused form.
    /// - witness: `tests::diagnostics::a_signature_whose_definition_is_refused_is_a_note_2339`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "`{}` states {} and produced {}: a form of `{}` the lowering refused leaves it so",
            self.declaration.name(),
            self.declaration.stated(),
            self.declaration.outcome(),
            self.upstream.name()
        )
    }
}

/// Builder-level validation and semantic payload boundaries.
#[cfg(test)]
mod tests
{
    use std::path::Path;

    use gandr_core_term::FailureClass;
    use gandr_core_term::TrackingIssue;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Class;
    use super::Subject;
    use super::Unsettlement;
    use super::diagnose;
    use super::excerpt;
    use super::report_span;
    use crate::model::AnnotationKind;

    #[test]
    fn class_labels_keep_their_decision_surfaces_distinct()
    {
        let classes = [
            Class::Refusal(FailureClass::MalformedSource),
            Class::Unsettled(Unsettlement::Obligations),
            Class::Unsettled(Unsettlement::Unproduced),
            Class::Unsettled(Unsettlement::RunOutcome),
            Class::Unsettled(Unsettlement::NormalForm),
            Class::Unsettled(Unsettlement::Malformed),
            Class::Goal,
            Class::Warning,
            Class::Ledger,
        ];
        let labels = classes.map(|class| class.to_string());
        for (index, label) in labels.iter().enumerate() {
            for earlier in &labels[.. index] {
                assert_ne!(earlier, label, "different causes remain distinguishable");
            }
        }
    }

    #[test]
    fn only_an_unimplemented_refusal_names_its_issue()
    {
        assert_eq!(
            Class::Refusal(FailureClass::Unimplemented(TrackingIssue::PROJECTION)).tracking(),
            Maybe::Present(TrackingIssue::PROJECTION),
            "an unimplemented refusal names the issue its class carries"
        );
        assert_eq!(
            Class::Refusal(FailureClass::MalformedSource).tracking(),
            Maybe::Absent(super::tracking::Absent::Untracked),
            "a malformed refusal names none"
        );
        assert_eq!(
            Class::Goal.tracking(),
            Maybe::Absent(super::tracking::Absent::Unrefused),
            "a goal is no refusal"
        );
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
            let diagnostic = diagnose(
                Path::new("boundary.gandr"),
                text,
                Subject::Source(LoweringRefusal::DuplicateDefinition {
                    span,
                    first,
                    name: "a".into(),
                }),
            );
            assert_eq!(
                diagnostic.span,
                if primary_valid {
                    Maybe::Present(span)
                }
                else {
                    Maybe::Absent(report_span::Absent::OutsideText)
                }
            );
            let marked: Vec<(AnnotationKind, ByteSpan)> = diagnostic
                .annotations
                .iter()
                .map(|annotation| (annotation.kind, annotation.locus.span))
                .collect();
            let mut expected = Vec::new();
            if primary_valid {
                expected.push((AnnotationKind::Primary, span));
            }
            if context_valid {
                expected.push((AnnotationKind::Context, first));
            }
            assert_eq!(marked, expected, "each locus is kept or dropped on its own");
            if primary_valid {
                let column = if start == 4_usize { 3_usize } else { 1_usize };
                assert_eq!(diagnostic.annotations[0].locus.column, column);
            }
        }
    }

    #[test]
    fn an_excerpt_is_the_lines_its_spans_touch()
    {
        let text = SourceText::from("one\ntwo\nthree\nfour\n");
        let at = |start: usize, end: usize| {
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("ordered")
        };
        let Maybe::Present(lines) = excerpt(text, [at(5, 6), at(9, 11)].into_iter())
        else {
            panic!("two spans excerpt their lines");
        };
        assert_eq!(
            (lines.text.as_str(), usize::from(lines.start), lines.line),
            ("two\nthree", 4_usize, 2_usize)
        );
        assert_eq!(excerpt(text, [].into_iter()), Maybe::Absent(()));
    }

    /// A lint's fix is proposed only at a point of the text it is read over:
    /// a finding whose span lies past the text proposes none.
    #[test]
    fn a_finding_past_the_text_proposes_no_fix()
    {
        use gandr_core_term::effect::Purity;
        use gandr_surface_lowering::AskedRuns;
        use gandr_surface_lowering::Exit;
        use gandr_surface_lowering::Explicitness;
        use gandr_surface_lowering::InferredExit;
        use gandr_surface_lowering::InferredRun;
        use gandr_surface_lowering::NestedSite;
        use gandr_surface_lowering::RunOperand;
        use gandr_surface_lowering::RunSpelling;

        let text = SourceText::from("def x = 1 ;\n");
        let at = |start: usize| {
            ByteSpan::new(
                ByteOffset::from(start),
                ByteOffset::from(start.saturating_add(1)),
            )
            .expect("ordered span")
        };
        for (start, proposed) in [(8_usize, true), (40_usize, false)] {
            let exit = InferredExit {
                span: at(start),
                exit: Exit::Return,
                explicitness: Explicitness::Asked,
            };
            let run = InferredRun {
                span: at(start),
                purity: Purity::Pure,
                site: NestedSite {
                    asked: AskedRuns::Every,
                    spelling: RunSpelling::Bare,
                    operand: RunOperand::Tight,
                },
            };
            for subject in [Subject::InferredExit(&exit), Subject::InferredRun(&run)] {
                let diagnostic = diagnose(Path::new("lint.gandr"), text, subject);
                assert_eq!(
                    matches!(diagnostic.fix, Maybe::Present(_)),
                    proposed,
                    "{subject:?} at byte {start}"
                );
            }
        }
    }

    /// #572: a located diagnostic whose primary mark is gone leads with no
    /// annotation; the context mark left first is not offered as the primary.
    #[test]
    fn a_located_diagnostic_without_its_primary_mark_has_no_primary()
    {
        let at = |start: usize, end: usize| {
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("ordered span")
        };
        let mut diagnostic = diagnose(
            Path::new("twice.gandr"),
            SourceText::from("def a = 1 ;\ndef a = 2 ;\n"),
            Subject::Source(LoweringRefusal::DuplicateDefinition {
                span: at(12, 17),
                first: at(0, 5),
                name: "a".into(),
            }),
        );
        assert_eq!(
            diagnostic.primary().map(|primary| primary.locus.span),
            Maybe::Present(at(12, 17)),
            "a located diagnostic leads with its primary mark"
        );
        let removed = diagnostic.annotations.remove(0);
        assert_eq!(removed.kind, AnnotationKind::Primary);
        assert_eq!(
            diagnostic.primary(),
            Maybe::Absent(report_span::Absent::OutsideText),
            "the context mark left first is not the primary annotation"
        );
    }

    /// A located refusal quotes its term as the expression only when the term
    /// is one line; a term over two lines has none.
    #[test]
    fn only_a_one_line_term_is_quoted_as_the_expression()
    {
        let text = SourceText::from("def a = 1 ;\ndef a =\n  2 ;\n");
        let at = |start: usize, end: usize| {
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("ordered span")
        };
        for (span, expression) in [
            (at(12, 17), Maybe::Present(String::from("def a"))),
            (
                at(12, 23),
                Maybe::Absent(crate::model::expression::Absent::Multiline),
            ),
        ] {
            let diagnostic = diagnose(
                Path::new("twice.gandr"),
                text,
                Subject::Source(LoweringRefusal::DuplicateDefinition {
                    span,
                    first: at(0, 5),
                    name: "a".into(),
                }),
            );
            assert_eq!(diagnostic.expression, expression, "{span:?}");
        }
    }

    /// A lint finding's title is its message, so its details show no title
    /// line repeating it.
    #[test]
    fn a_title_the_message_repeats_is_not_detailed()
    {
        use gandr_surface_lowering::Exit;
        use gandr_surface_lowering::Explicitness;
        use gandr_surface_lowering::InferredExit;

        let exit = InferredExit {
            span: ByteSpan::new(ByteOffset::from(8_usize), ByteOffset::from(9_usize))
                .expect("ordered span"),
            exit: Exit::Return,
            explicitness: Explicitness::Asked,
        };
        let diagnostic = diagnose(
            Path::new("lint.gandr"),
            SourceText::from("def x = 1 ;\n"),
            Subject::InferredExit(&exit),
        );
        assert_eq!(diagnostic.detail.title, diagnostic.message.text);
        assert!(
            diagnostic
                .details(crate::verbosity::Verbosity::Detailed)
                .iter()
                .all(|detail| detail.name != "detail"),
            "{:?}",
            diagnostic.details(crate::verbosity::Verbosity::Detailed)
        );
    }

    /// The JSON image lists a diagnostic's context loci, and not its primary
    /// one, under `annotations`; and a located diagnostic whose first mark is
    /// not its primary one claims no primary annotation.
    #[test]
    fn the_annotations_of_the_image_are_the_contexts_alone()
    {
        let at = |start: usize, end: usize| {
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("ordered span")
        };
        let diagnostic = diagnose(
            Path::new("twice.gandr"),
            SourceText::from("def a = 1 ;\ndef a = 2 ;\n"),
            Subject::Source(LoweringRefusal::DuplicateDefinition {
                span: at(12, 17),
                first: at(0, 5),
                name: "a".into(),
            }),
        );
        let image: serde_json::Value =
            serde_json::from_str(&diagnostic.json()).expect("the JSON image parses");
        let annotations: Vec<(&serde_json::Value, &serde_json::Value)> = image["annotations"]
            .as_array()
            .map(|annotations| {
                annotations
                    .iter()
                    .map(|annotation| (&annotation["start"], &annotation["end"]))
                    .collect()
            })
            .unwrap_or_default();
        assert_eq!(annotations, [(
            &serde_json::json!(0_u64),
            &serde_json::json!(5_u64)
        )]);
    }
}
