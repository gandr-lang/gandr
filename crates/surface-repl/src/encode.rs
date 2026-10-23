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
use gandr_core_incremental::ContentNode;
use gandr_core_incremental::ItemCheckpoint;
use gandr_core_incremental::Reference;
use gandr_core_incremental::Resume;
use gandr_core_incremental::Typing;
use gandr_core_incremental::submitted;
use gandr_surface_corpus::Outcome;
use gandr_surface_diagnostics::Diagnostic;
use gandr_surface_diagnostics::Excerpt;
use gandr_surface_diagnostics::Fix;
use gandr_surface_diagnostics::Locus;
use gandr_surface_diagnostics::Severity;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_diagnostics::context_locus;
use gandr_surface_diagnostics::report_span;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::entries;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::Spelling;
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
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::remote::line_repair_cards;
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
    /// The probe declaration the prompt wraps an expression or a type in:
    /// its type answers the line, and, where the session evaluates it, its
    /// value answers too — a type answers its sort alone, the session not
    /// evaluating a universe — and it is kept when nothing is refused, so the
    /// next line may use the name.
    Prompt
    {
        /// The probe's name.
        name: &'name str,
        /// The line's offset within the wrapped probe text.
        line_start: ByteOffset,
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
/// - witness: `tests::repl_loop::corpus_types_spell_as_their_source_writes_them`
/// - witness: `tests::repl_loop::a_hole_encodes_as_a_goal_line`
/// - witness: `tests::repl_loop::a_dependent_function_names_its_type_with_its_binder`
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
        Maybe::Present(ref spelling) => format!("{name} : {spelling}"),
        Maybe::Absent(_) => name.to_string(),
    }
}

/// The class of the type the probe synthesized, read off the type value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Synthesis
{
    /// A sort — the probe's type is a universe node, so it answers its
    /// sort alone, unevaluated.
    Sort,
    /// A type the session evaluates.
    Type,
}

/// The class of the type the probe synthesized: a sort the probe answers
/// alone, or a type the session evaluates.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Synthesis::Sort` when the probe's synthesized type is a universe
///   node (`ContentNode::Universe`); `Synthesis::Type` for any other node, or
///   for no checkpoint at all.
/// - provides: the discriminator for skipping evaluation of a type at the
///   prompt.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a universe's node is a `ContentNode::Universe`; a
///   non-universe type's node is not.
/// - witness: `tests::repl_loop::a_type_reports_its_sort`
#[spec(ensures: |ret| ret == match resume {
    Maybe::Absent(_) => Synthesis::Type,
    Maybe::Present(resume) => {
        let wanted = AsRef::<str>::as_ref(&name).as_bytes();
        let named = |checkpoint: &&ItemCheckpoint| {
            matches!(
                checkpoint.content().reference(),
                Reference::Item { key, .. } if key.as_ref() == wanted
            )
        };
        resume
            .checkpoints()
            .items()
            .iter()
            .rfind(named)
            .map_or(Synthesis::Type, |checkpoint| match *checkpoint.typing() {
                Typing::Synthesised { ref produced, .. } => produced
                    .nodes()
                    .first()
                    .map_or(Synthesis::Type, |node| {
                        if matches!(node.former(), ContentNode::Universe { .. }) {
                            Synthesis::Sort
                        } else {
                            Synthesis::Type
                        }
                    }),
                Typing::Data
                | Typing::Checked { .. }
                | Typing::Owed
                | Typing::Suspended
                | Typing::Refused(_) => Synthesis::Type,
            })
    }
})]
fn synthesis(
    resume: Maybe<&Resume, submitted::Absent>,
    name: SourceFragment<'_>,
) -> Synthesis
{
    let Maybe::Present(resume) = resume
    else {
        return Synthesis::Type;
    };
    let wanted = AsRef::<str>::as_ref(&name).as_bytes();
    let named = |checkpoint: &&ItemCheckpoint| {
        matches!(
            checkpoint.content().reference(),
            Reference::Item { key, .. } if key.as_ref() == wanted
        )
    };
    let Some(checkpoint) = resume.checkpoints().items().iter().rfind(named)
    else {
        return Synthesis::Type;
    };
    let Typing::Synthesised { ref produced, .. } = *checkpoint.typing()
    else {
        return Synthesis::Type;
    };
    produced.nodes().first().map_or(Synthesis::Type, |node| {
        if matches!(node.former(), ContentNode::Universe { .. }) {
            Synthesis::Sort
        }
        else {
            Synthesis::Type
        }
    })
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
/// - witness: `tests::repl_loop::an_incomplete_buffer_is_submitted_at_end_of_input`
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
    card.span.map_or_else(
        || format!("warning[{}]: {}", card.code, card.message),
        |range| {
            format!(
                "warning[{}]: {} at {}..{}",
                card.code,
                card.message,
                usize::from(range.start()),
                usize::from(range.end())
            )
        },
    )
}

/// The transcript line of what one run came to: its kind and its text.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a value, a sealed one among them, is a value line, a run blamed
///   on a goal or stopped at a hole a blame line, and a run that stopped short
///   of a value otherwise or never reached the machine a note line; the text is
///   the evaluation's one spelling, the one `gandr run` prints.
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
    Evaluation::Value(_) | Evaluation::Sealed(_) => OutKind::Value,
    Evaluation::Blamed(_) | Evaluation::Holed { .. } => OutKind::Blame,
    Evaluation::Stuck(_) | Evaluation::Unfinished(_) | Evaluation::Unrunnable(_) => OutKind::Stuck,
} && !ret.1.is_empty())]
fn evaluation_line(evaluation: &Evaluation<'_>) -> (OutKind, String)
{
    let kind = match *evaluation {
        Evaluation::Value(_) | Evaluation::Sealed(_) => OutKind::Value,
        Evaluation::Blamed(_) | Evaluation::Holed { .. } => OutKind::Blame,
        Evaluation::Stuck(_) | Evaluation::Unfinished(_) | Evaluation::Unrunnable(_) => {
            OutKind::Stuck
        },
    };
    (kind, evaluation.to_string())
}
/// Re-range `diagnostic` from the probe's revision to the line the prompt
/// offered: every span, annotation, context and fix is clamped to the line's
/// bytes, and the excerpt becomes the line, so the renderer quotes the line
/// and marks the line's bytes.
///
/// # Specification
/// - requires: nothing; the diagnostic is one the session raised over the probe
///   `def {name} = {line} ;`, and `line_start` is the line's offset in that
///   revision.
/// - ensures: the diagnostic's spans, annotations, contexts and fix are clamped
///   to the line's bytes, and its excerpt is the line at `line_start` on line
///   one, so the renderer quotes the line and marks the line's bytes; a span
///   that fell outside the line is left unlocated, and an annotation that fell
///   outside the line is clamped to a zero-width span at the line's start, the
///   same way the primary span and the context locus are unlocated.
/// - provides: the line's coordinates for a probe's refusal.
/// - fails: never.
/// - panics: none.
/// - executable: none — the in-place re-ranging has no return-value observer;
///   the clamped spans are witnessed end to end by
///   `tests::repl_loop::a_malformed_expression_carries_the_line_s_range`, and
///   the annotation's clamp is witnessed by
///   `encode::tests::an_out_of_line_annotation_is_clamped_to_the_line`.
///
/// # Adequacy
/// - hypothesis: L3 — a refusal at the prompt carries the line's range, not the
///   probe's, and an out-of-line annotation is clamped to the line the same way
///   the primary span and the context locus are unlocated.
/// - witness: `tests::repl_loop::a_malformed_expression_carries_the_line_s_range`
/// - witness: `encode::tests::an_out_of_line_annotation_is_clamped_to_the_line`
fn re_range(
    diagnostic: &mut Diagnostic,
    line: SourceText<'_>,
    line_start: ByteOffset,
)
{
    let line_end =
        ByteOffset::from(usize::from(line_start).saturating_add(<&str>::from(line).len()));
    let clamp = |span: ByteSpan| -> Option<ByteSpan> {
        let start = usize::from(span.start()).max(usize::from(line_start));
        let end = usize::from(span.end()).min(usize::from(line_end));
        if start >= usize::from(line_end) {
            return None;
        }
        ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).ok()
    };
    diagnostic.span = match diagnostic.span {
        Maybe::Present(span) => clamp(span).map_or(
            Maybe::Absent(report_span::Absent::OutsideText),
            Maybe::Present,
        ),
        Maybe::Absent(reason) => Maybe::Absent(reason),
    };
    for annotation in &mut diagnostic.annotations {
        annotation.locus.span = clamp(annotation.locus.span).unwrap_or_else(|| {
            ByteSpan::new(line_start, line_start).unwrap_or(annotation.locus.span)
        });
    }
    for context in &mut diagnostic.contexts {
        context.locus = match context.locus {
            Maybe::Present(locus) => clamp(locus.span).map_or(
                Maybe::Absent(context_locus::Absent::OutsideText),
                |span| {
                    Maybe::Present(Locus {
                        span,
                        line: locus.line,
                        column: locus.column,
                    })
                },
            ),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
    }
    diagnostic.excerpt = match diagnostic.excerpt {
        Maybe::Present(_) => Maybe::Present(Excerpt {
            text: <&str>::from(line).to_owned(),
            start: line_start,
            line: 1_usize,
        }),
        Maybe::Absent(reason) => Maybe::Absent(reason),
    };
    let fix = core::mem::replace(
        &mut diagnostic.fix,
        Maybe::Absent(gandr_surface_diagnostics::fix::Absent::Unproposed),
    );
    diagnostic.fix = match fix {
        Maybe::Present(fix) => match clamp(fix.span) {
            Some(span) => Maybe::Present(Fix {
                span,
                replacement: fix.replacement,
            }),
            None => Maybe::Absent(gandr_surface_diagnostics::fix::Absent::Unproposed),
        },
        Maybe::Absent(reason) => Maybe::Absent(reason),
    };
}

/// The transcript block of `submission`, made for `offer`, and whether its
/// chunk is kept.
///
/// # Specification
/// - requires: `submission` is the session's answer to a revision whose text
///   before `offer.chunk` is the accepted text `prior` was taken from, and
///   `resume` is the session's latest resume, read after that answer.
/// - ensures: the block echoes `offer.echo`. Its lines are, in order: the
///   diagnostics renderer's report, under `style` and naming its types in
///   `spelling`, for every refusal and every shadowing warning `gandr check
///   --goals` would print for the revision, each its own line, a warning
///   refusing nothing; then, when nothing was refused, one line per declaration
///   the chunk introduced or whose outcome differs from `prior` — `name : T` as
///   a type line when it checks owing nothing, as a goal line when it owes —
///   and, after the type line of a declaration the session evaluates, the line
///   of what its run came to: a value line spelling the value in `spelling`, a
///   blame line naming the goal reached, or a note line for a run that stopped
///   short or never reached the machine; then a warning line per parse repair
///   inside the chunk, a prompt line's measured on the line as its refusal is.
///   A probe answers instead with the one type line `: T`. A prompt probe
///   answers with the declaration's type line and, where the session evaluates
///   it, its value line, and its refusal is re-ranged to the line; a type at
///   the prompt answers its sort alone — the session does not evaluate a
///   universe, so no stuck note follows. The disposition keeps the chunk, with
///   the standings of the whole revision, exactly when the subject is
///   declarations or a prompt probe and nothing was refused.
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
/// - witness: `tests::repl_loop::an_outcome_only_refusal_is_visible_in_the_repl`
/// - witness: `tests::repl_loop::a_hole_encodes_as_a_goal_line`
/// - witness: `tests::repl_loop::a_definition_is_visible_on_the_next_line`
/// - witness: `tests::repl_loop::a_refused_chunk_is_not_kept`
/// - witness: `tests::repl_loop::a_later_definition_settles_an_earlier_goal`
/// - witness: `tests::repl_loop::the_type_command_answers_without_keeping_the_probe`
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
        Disposition::Kept(ref standings) => matches!(subject, Subject::Declarations | Subject::Prompt { .. })
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
    spelling: Spelling,
) -> Encoded
{
    let Offer {
        echo,
        chunk,
        subject,
    } = offer;
    let cards = match subject {
        Subject::Prompt { line_start, .. } => line_repair_cards(
            submission.obligations(),
            ByteOffset::from(usize::from(chunk).saturating_add(usize::from(line_start))),
            SourceText::from(echo.source.as_str()),
        ),
        Subject::Declarations | Subject::Probe { .. } => {
            repair_cards(submission.obligations(), chunk)
        },
    };
    let mut step = submission.into_step(Path::new(""));
    let mut lines: Vec<(OutKind, String)> = Vec::new();
    let mut refused = false;
    for diagnostic in entries(&step, Verb::Check(Goals::Reported)).spelling(spelling) {
        let mut diagnostic = diagnostic;
        if let Subject::Prompt { line_start, .. } = subject {
            let absolute =
                ByteOffset::from(usize::from(chunk).saturating_add(usize::from(line_start)));
            re_range(
                &mut diagnostic,
                SourceText::from(echo.source.as_str()),
                absolute,
            );
        }
        let rendered = render(&diagnostic, style, Verbosity::User).to_string();
        match diagnostic.severity {
            Severity::Goal => {},
            Severity::Warning => {
                lines.push((OutKind::Diag, String::from(rendered.trim_end())));
            },
            Severity::Error | Severity::Note => {
                refused = true;
                lines.push((OutKind::Diag, String::from(rendered.trim_end())));
            },
            Severity::Ledger => lines.push((OutKind::Info, rendered)),
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
        program.spell_in(spelling);
        for declaration in report.declarations() {
            let name = declaration.name().to_string();
            let fragment = SourceFragment::from(name.as_str());
            let outcome = declaration.outcome();
            let introduced = chunk <= declaration.span().start();
            let changed = prior.0.get(&name) != Some(&outcome);
            if !refused && (introduced || changed) {
                match (subject, &outcome) {
                    (
                        Subject::Probe { name: probe },
                        &(Outcome::Checks(_) | Outcome::Runs(_) | Outcome::Normalizes(_)),
                    ) if probe == name => {
                        let spelling = type_of(resume, fragment);
                        let line = match spelling {
                            Maybe::Present(spelling) => format!(": {spelling}"),
                            Maybe::Absent(_) => String::from(":"),
                        };
                        lines.push((OutKind::Type, line));
                    },
                    (Subject::Declarations, &Outcome::Checks(owed)) if usize::from(owed) > 0 => {
                        lines.push((
                            OutKind::Goal,
                            typed_line(fragment, &type_of(resume, fragment)),
                        ));
                    },
                    (
                        Subject::Declarations,
                        &(Outcome::Checks(_) | Outcome::Runs(_) | Outcome::Normalizes(_)),
                    ) => {
                        lines.push((
                            OutKind::Type,
                            typed_line(fragment, &type_of(resume, fragment)),
                        ));
                        if let Maybe::Present(evaluation) = evaluate(declaration, program) {
                            lines.push(evaluation_line(&evaluation));
                        }
                    },
                    (
                        Subject::Prompt { name: probe, .. },
                        &(Outcome::Checks(_) | Outcome::Runs(_) | Outcome::Normalizes(_)),
                    ) if probe == name => {
                        let spelling = type_of(resume, fragment);
                        lines.push((OutKind::Type, typed_line(fragment, &spelling)));
                        if synthesis(resume, fragment) != Synthesis::Sort
                            && let Maybe::Present(evaluation) = evaluate(declaration, program)
                        {
                            lines.push(evaluation_line(&evaluation));
                        }
                    },
                    (
                        Subject::Probe { .. } | Subject::Declarations | Subject::Prompt { .. },
                        &(Outcome::Checks(_)
                        | Outcome::Refuses(_)
                        | Outcome::Runs(_)
                        | Outcome::Normalizes(_)
                        | Outcome::RefusesRunning(..)),
                    ) => {},
                }
            }
            standings.0.insert(name, outcome);
        }
    }
    lines.extend(cards.iter().map(|card| (OutKind::Diag, card_line(card))));
    let disposition = match (subject, refused) {
        (Subject::Declarations | Subject::Prompt { .. }, false) => Disposition::Kept(standings),
        (Subject::Declarations | Subject::Probe { .. } | Subject::Prompt { .. }, _) => {
            Disposition::Dropped
        },
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

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;
    use std::path::PathBuf;

    use gandr_surface_diagnostics::AnnotationKind;
    use gandr_surface_diagnostics::Class;
    use gandr_surface_diagnostics::Compared;
    use gandr_surface_diagnostics::DiagnosticAnnotation;
    use gandr_surface_diagnostics::DiagnosticDetail;
    use gandr_surface_diagnostics::Message;
    use gandr_surface_diagnostics::MessageKey;
    use gandr_surface_diagnostics::Unsettlement;
    use gandr_surface_diagnostics::fix;
    use gandr_surface_diagnostics::producer;
    use gandr_surface_diagnostics::report_note;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::re_range;

    /// An out-of-line annotation is clamped to the line the same way the
    /// primary span and the context locus are unlocated: the primary span
    /// becomes `OutsideText`, and the annotation's span becomes a zero-width
    /// span at the line's start, not the probe's offset.
    #[test]
    fn an_out_of_line_annotation_is_clamped_to_the_line()
    {
        let line = SourceText::from("nope");
        let line_start = ByteOffset::from(11_usize);
        let mut diagnostic = gandr_surface_diagnostics::Diagnostic {
            path: PathBuf::new(),
            severity: gandr_surface_diagnostics::Severity::Error,
            identifier: Maybe::Absent(
                gandr_surface_diagnostics::report_identifier::Absent::Statement,
            ),
            message: Message {
                key: MessageKey::Unsettled(Unsettlement::Obligations),
                text: String::from("`nope` is not defined"),
            },
            detail: DiagnosticDetail {
                class: Class::Unsettled(Unsettlement::Obligations),
                title: String::from("unsettled"),
                compared: Compared {
                    expected: Maybe::Absent(gandr_surface_diagnostics::spelling::Absent::Unspelled),
                    found: Maybe::Absent(gandr_surface_diagnostics::spelling::Absent::Unspelled),
                },
                producer: Maybe::Absent(producer::Absent::Statement),
            },
            span: Maybe::Present(
                ByteSpan::new(ByteOffset::from(8_usize), ByteOffset::from(9_usize)).unwrap(),
            ),
            annotations: Vec::new(),
            contexts: Vec::new(),
            elsewhere: Vec::new(),
            hypotheses: Vec::new(),
            note: Maybe::Absent(report_note::Absent::Statement),
            expression: Maybe::Absent(gandr_surface_diagnostics::expression::Absent::Unlocated),
            excerpt: Maybe::Absent(gandr_surface_diagnostics::report_span::Absent::OutsideText),
            fix: Maybe::Absent(fix::Absent::Unproposed),
        };
        diagnostic.annotations.push(DiagnosticAnnotation {
            kind: AnnotationKind::Context,
            locus: gandr_surface_diagnostics::Locus {
                span: ByteSpan::new(ByteOffset::from(4_usize), ByteOffset::from(7_usize)).unwrap(),
                line: 1_usize,
                column: 5_usize,
            },
            label: String::from("context"),
        });
        re_range(&mut diagnostic, line, line_start);
        assert!(
            matches!(
                diagnostic.span,
                Maybe::Absent(gandr_surface_diagnostics::report_span::Absent::OutsideText)
            ),
            "the primary span is unlocated: {:?}",
            diagnostic.span
        );
        let annotation = &diagnostic.annotations[0];
        assert_eq!(
            annotation.locus.span,
            ByteSpan::new(ByteOffset::from(11_usize), ByteOffset::from(11_usize)).unwrap(),
            "the annotation is clamped to the line's start, not the probe's offset"
        );
    }
}
