//! The transcript encoder: what one submission changed, as a transcript block.
//!
//! # A checked declaration prints what it runs to
//!
//! After a checked declaration's type line, the encoder writes its evaluation:
//! a value, goal blame, or a note for a stuck or unrunnable result. The run
//! stage owns the spelling shared with `gandr run` and `runs` expectations.
//! Goal declarations are not evaluated; probes answer only a type. The
//! declaration is the evaluation unit because the fragment has no top-level
//! expression; see `gandr-surface-session`'s `session` module, § A hole-free
//! item is evaluated.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use std::path::Path;

use anodized::spec;
use gandr_core_incremental::Resume;
use gandr_core_incremental::submitted;
use gandr_surface_corpus::Outcome;
use gandr_surface_diagnostics::Severity;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::entries;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_render_remote::DiagCard;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_render_remote::OutKind;
use gandr_surface_render_remote::TranscriptBlock;
use gandr_surface_render_terminal::RenderStyle;
use gandr_surface_render_terminal::render;
use gandr_surface_session::Submission;
use gandr_surface_session::evaluate;
use gandr_surface_session::spelled;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

use crate::remote::repair_cards;
use crate::render::TRANSCRIPT_WIDTH;

/// What each declaration of the accepted revision produced, by name.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Standings(BTreeMap<String, Outcome>);

impl Standings
{
    /// Whether some declaration of the accepted revision is named `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn names(
        &self,
        name: SourceFragment<'_>,
    ) -> Naming
    {
        if self.0.contains_key(AsRef::<str>::as_ref(&name)) {
            Naming::Taken
        }
        else {
            Naming::Free
        }
    }
}

/// Whether a name is taken by an accepted declaration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Naming
{
    /// An accepted declaration carries the name.
    Taken,
    /// None does.
    Free,
}

/// The text a transcript block echoes, with its highlight spans.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Echo
{
    /// The echoed text: the submitted chunk, or the meta-command that
    /// submitted on the user's behalf.
    source: String,
    /// The highlight spans over [`Self::source`], sorted and disjoint.
    highlights: Vec<HlSpan>,
}

impl Echo
{
    /// The echo of `source`, painted with `highlights`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        source: String,
        highlights: Vec<HlSpan>,
    ) -> Self
    {
        Self { source, highlights }
    }
}

/// What a submission was made for.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Subject<'name>
{
    /// Declarations the user wrote: kept when none of them is refused.
    Declarations,
    /// The probe declaration `:type` wraps an expression in: its type answers
    /// the question, and it is never kept.
    Probe
    {
        /// The probe's name.
        name: &'name str,
    },
}

/// One submission as the encoder reads it: the echo, where the new text sits
/// in the revision, and what it was for.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Offer<'name>
{
    /// The block's echo.
    pub echo: Echo,
    /// Where the new text starts in the submitted revision; everything before
    /// it was accepted earlier.
    pub chunk: ByteOffset,
    /// What the submission was made for.
    pub subject: Subject<'name>,
}

/// Whether the loop keeps the submitted chunk.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Disposition
{
    /// Nothing was refused: the chunk joins the accepted text, and these are
    /// the standings of the accepted revision it makes.
    Kept(Standings),
    /// The revision drew a refusal, or the submission was a probe: the
    /// accepted text stays as it was.
    Dropped,
}

/// A submission's transcript block and the loop's disposition of its chunk.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Encoded
{
    /// The block a face draws.
    pub block: TranscriptBlock,
    /// Whether the chunk is kept.
    pub disposition: Disposition,
}

/// The type the latest checkpoints give the declaration `name`, at the
/// transcript's width: the session's
/// [`type_of`](gandr_surface_session::type_of) at [`TRANSCRIPT_WIDTH`]
/// columns.
///
/// # Specification
/// trivial.
fn type_of(
    resume: Maybe<&Resume, submitted::Absent>,
    name: SourceFragment<'_>,
) -> Maybe<Presentation, spelled::Absent>
{
    gandr_surface_session::type_of(resume, name, PageWidth::from(TRANSCRIPT_WIDTH))
}

/// `name : T`, or the bare name when no type can be spelled.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the name followed by ` : ` and the presentation when available,
///   otherwise the name alone, preserving all presented characters.
/// - provides: type and goal lines without inventing a missing type.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — selected corpus signatures agree with source spelling; L3
///   — owed signatures and dependent types retain their names and syntax.
/// - witness: `loop::tests::corpus_types_spell_as_their_source_writes_them`
/// - witness: `loop::tests::a_hole_encodes_as_a_goal_line`
/// - witness: `loop::tests::a_dependent_function_names_its_type_with_its_binder`
#[spec(ensures: |ret| match *spelling {
    Maybe::Present(ref presentation) => ret.strip_prefix(AsRef::<str>::as_ref(&name))
        .and_then(|rest| rest.strip_prefix(" : ")) == Some(presentation.as_ref()),
    Maybe::Absent(_) => ret == AsRef::<str>::as_ref(&name),
})]
fn typed_line(
    name: SourceFragment<'_>,
    spelling: &Maybe<Presentation, spelled::Absent>,
) -> String
{
    match *spelling {
        | Maybe::Present(ref spelling) => format!("{name} : {spelling}"),
        | Maybe::Absent(_) => name.to_string(),
    }
}

/// A repair card as one diagnostic line.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a warning line with the card's code and unchanged message; a
///   located card appends its exact `start..end` byte range.
/// - provides: repair diagnostics in the transcript.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a repaired end-of-input buffer is reported; the predicate
///   parses the code and byte endpoints without formatting a second copy.
/// - witness: `loop::tests::an_incomplete_buffer_is_submitted_at_end_of_input`
#[spec(ensures: |ret| ret.strip_prefix("warning[")
    .and_then(|rest| rest.split_once("]: ")).is_some_and(|(code, body)|
        code.parse::<gandr_surface_render_remote::DiagnosticCode>().is_ok_and(|parsed| parsed == card.code)
            && card.span.map_or(body == card.message, |span|
                body.strip_prefix(card.message.as_str())
                    .and_then(|rest| rest.strip_prefix(" at "))
                    .and_then(|rest| rest.split_once(".."))
                    .is_some_and(|(start, end)|
                        start.parse::<usize>().is_ok_and(|at| at == usize::from(span.start()))
                            && end.parse::<usize>().is_ok_and(|at| at == usize::from(span.end()))))))]
fn card_line(card: &DiagCard) -> String
{
    match card.span {
        | Some(range) => format!(
            "warning[{}]: {} at {}..{}",
            card.code,
            card.message,
            usize::from(range.start()),
            usize::from(range.end())
        ),
        | None => format!("warning[{}]: {}", card.code, card.message),
    }
}

/// The transcript line of what one run came to: its kind and its text.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a value is a value line, a run blamed on a goal a blame line, and
///   a run that stopped short of a value or never reached the machine a note
///   line; the text is the evaluation's one spelling, the one `gandr run`
///   prints.
/// - provides: the value line's kind and text, so every face marks a run's
///   class the same way.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — value, escaped-string and function results retain their
///   structural spelling; blamed and unrunnable outcomes retain their kinds
///   without pinning explanatory prose.
/// - witness: `render::tests::eval_renders_each_outcome_class`
#[spec(ensures: |ret| ret.0 == match *evaluation {
    Evaluation::Value(_) => OutKind::Value,
    Evaluation::Blamed(_) => OutKind::Blame,
    Evaluation::Stuck(_) | Evaluation::Unfinished(_) | Evaluation::Unrunnable(_) => OutKind::Stuck,
} && !ret.1.is_empty())]
fn evaluation_line(evaluation: &Evaluation<'_>) -> (OutKind, String)
{
    let kind = match *evaluation {
        | Evaluation::Value(_) => OutKind::Value,
        | Evaluation::Blamed(_) => OutKind::Blame,
        | Evaluation::Stuck(_) | Evaluation::Unfinished(_) | Evaluation::Unrunnable(_) => {
            OutKind::Stuck
        },
    };
    (kind, evaluation.to_string())
}

/// The transcript block of `submission`, made for `offer`, and whether its
/// chunk is kept.
///
/// # Specification
/// - requires: `submission` is the session's answer to a revision whose text
///   before `offer.chunk` is the accepted text `prior` was taken from, and
///   `resume` is the session's latest resume, read after that answer.
/// - ensures: the block echoes `offer.echo`. Its lines are, in order: the
///   diagnostics renderer's report, under `style`, for every refusal and every
///   shadowing warning `gandr check --goals` would print for the revision, each
///   its own line, a warning refusing nothing; then, when nothing was refused,
///   one line per declaration the chunk introduced or whose outcome differs
///   from `prior` — `name : T` as a type line when it checks owing nothing, as
///   a goal line when it owes — and, after the type line of a declaration the
///   session evaluates, the line of what its run came to: a value line spelling
///   the value, a blame line naming the goal reached, or a note line for a run
///   that stopped short or never reached the machine; then a warning line per
///   parse repair inside the chunk. A probe answers instead with the one type
///   line `: T`. The disposition keeps the chunk, with the standings of the
///   whole revision, exactly when the subject is declarations and nothing was
///   refused.
/// - provides: the one encoding every face draws, so the batch transcript, the
///   terminal and a later interface show the same lines.
/// - fails: never.
/// - panics: none.
/// - intension: one pass over the report entries and one over the declarations;
///   each named declaration's checkpoint is found by a scan of the resume, and
///   each evaluated declaration runs once on a fresh machine.
///
/// # Adequacy
/// - hypothesis: L2 — a refusal's line equals the diagnostics renderer's own
///   rendering of the same report; a type line equals the renderer's spelling
///   of the checkpoint's type; L3 — a goal, a refusal that drops the chunk, a
///   declaration completed by a later chunk, a probe, and a run of each class
///   the fragment writes are each asserted at their exact lines and
///   disposition.
/// - witness: `loop::tests::an_outcome_only_refusal_is_visible_in_the_repl`
/// - witness: `loop::tests::a_hole_encodes_as_a_goal_line`
/// - witness: `loop::tests::a_definition_is_visible_on_the_next_line`
/// - witness: `loop::tests::a_refused_chunk_is_not_kept`
/// - witness: `loop::tests::a_later_definition_settles_an_earlier_goal`
/// - witness: `loop::tests::the_type_command_answers_without_keeping_the_probe`
/// - witness: `render::tests::eval_renders_each_outcome_class`
#[spec(captures: [
    subject = offer.subject,
    echo_bytes = offer.echo.source.len(),
    highlights = offer.echo.highlights.len(),
    declarations = match *submission.composed() { Composed::Settled { ref report, .. } => report.declarations().len(), Composed::Refused(_) => 0 },
    refused = match *submission.composed() {
        Composed::Settled { ref report, .. } => report.declarations().iter()
            .any(|declaration| matches!(declaration.produced().refusal(), Maybe::Present(_))),
        Composed::Refused(_) => true,
    }
], ensures: |ret| ret.block.source.len() == echo_bytes && ret.block.source_hl.len() == highlights
    && ret.block.lines.iter().all(|row| row.0 != OutKind::Source)
    && match ret.disposition {
        Disposition::Kept(ref standings) => matches!(subject, Subject::Declarations)
            && !refused && standings.0.len() <= declarations,
        Disposition::Dropped => matches!(subject, Subject::Probe { .. })
            || ret.block.lines.iter().any(|row| row.0 == OutKind::Diag),
    }
    && (!matches!(subject, Subject::Probe { .. }) || ret.block.lines.iter().all(|row|
        matches!(row.0, OutKind::Diag | OutKind::Info) || (row.0 == OutKind::Type && row.1.starts_with(':'))))
)]
#[inline]
#[must_use]
pub fn encode_submission(
    offer: Offer<'_>,
    submission: Submission<'_>,
    resume: Maybe<&Resume, submitted::Absent>,
    prior: &Standings,
    style: RenderStyle,
) -> Encoded
{
    let Offer {
        echo,
        chunk,
        subject,
    } = offer;
    let cards = repair_cards(submission.obligations(), chunk);
    let mut step = submission.into_step(Path::new(""));
    let mut lines: Vec<(OutKind, String)> = Vec::new();
    let mut refused = false;
    for diagnostic in entries(&step, Verb::Check(Goals::Reported)) {
        let rendered = render(&diagnostic, style, Verbosity::User).to_string();
        match diagnostic.severity {
            | Severity::Goal => {},
            | Severity::Warning => {
                lines.push((OutKind::Diag, String::from(rendered.trim_end())));
            },
            | Severity::Error => {
                refused = true;
                lines.push((OutKind::Diag, String::from(rendered.trim_end())));
            },
            | Severity::Ledger => lines.push((OutKind::Info, rendered)),
        }
    }
    let mut standings = Standings::default();
    if let Step::Source {
        composed:
            Composed::Settled {
                ref report,
                ref mut program,
                ..
            },
        ..
    } = step
    {
        for declaration in report.declarations() {
            let name = declaration.name().to_string();
            let fragment = SourceFragment::from(name.as_str());
            let outcome = declaration.outcome();
            let introduced = chunk <= declaration.span().start();
            let changed = prior.0.get(&name) != Some(&outcome);
            if !refused && (introduced || changed) {
                match (subject, &outcome) {
                    | (
                        Subject::Probe { name: probe },
                        &(Outcome::Checks(_) | Outcome::Runs(_)),
                    ) if probe == name => {
                        let spelling = type_of(resume, fragment);
                        let line = match spelling {
                            | Maybe::Present(spelling) => format!(": {spelling}"),
                            | Maybe::Absent(_) => String::from(":"),
                        };
                        lines.push((OutKind::Type, line));
                    },
                    | (Subject::Declarations, &Outcome::Checks(owed)) if usize::from(owed) > 0 => {
                        lines.push((
                            OutKind::Goal,
                            typed_line(fragment, &type_of(resume, fragment)),
                        ));
                    },
                    | (Subject::Declarations, &(Outcome::Checks(_) | Outcome::Runs(_))) => {
                        lines.push((
                            OutKind::Type,
                            typed_line(fragment, &type_of(resume, fragment)),
                        ));
                        if let Maybe::Present(evaluation) = evaluate(declaration, program) {
                            lines.push(evaluation_line(&evaluation));
                        }
                    },
                    | (
                        Subject::Probe { .. } | Subject::Declarations,
                        &(Outcome::Checks(_) | Outcome::Refuses(_) | Outcome::Runs(_)),
                    ) => {},
                }
            }
            standings.0.insert(name, outcome);
        }
    }
    lines.extend(cards.iter().map(|card| (OutKind::Diag, card_line(card))));
    let disposition = match (subject, refused) {
        | (Subject::Declarations, false) => Disposition::Kept(standings),
        | (Subject::Declarations, true) | (Subject::Probe { .. }, _) => Disposition::Dropped,
    };
    Encoded {
        block: TranscriptBlock {
            source: echo.source,
            source_hl: echo.highlights,
            lines,
        },
        disposition,
    }
}
