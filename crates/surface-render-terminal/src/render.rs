//! One diagnostic laid out for a terminal.
//!
//! # A projection, never a second reading
//!
//! [`render`] reads a [`Diagnostic`] and nothing else: every span, label,
//! context, hypothesis and note it writes is one the model holds. The snippet
//! is the diagnostic's excerpt — the whole lines its loci cover — with each
//! span rebased onto it and its first line numbered as the source numbers it,
//! so the layout is the one the whole source would give. The primary
//! annotation and the refusal's own context annotations mark their bytes; each
//! located context the refusal stood inside marks its term's bytes with
//! `judgement; while sentence`, and its binders after `; binds`; each unlocated
//! one closes the snippet as a `while …` note. A diagnostic with no annotation
//! names its source's path and quotes no line. An empty path is named
//! `<input>`.
//!
//! A ledger line is its path, a colon and its text, unstyled.
//!
//! The help closes the notes. A proposed fix closes the report as a `help`
//! group: the excerpt with the fix applied and the edit marked.
//!
//! | Level | Adds |
//! | ----- | ---- |
//! | `User`, the default | the message, labels, contexts, note, an unimplemented refusal's `tracked by #N <url>` and the help |
//! | `Detailed` | `class:`, `detail:` where the producer's wording differs from the message, `expression:` when the primary span is one line, `hypotheses:` when any are in scope |
//! | `Debug` | `spans:` every locus's bytes, `rules:` each context's stable name, `refusal:` the producer's refusal and failure as their implementers print them |
//! | `Json` | instead of the snippet, the diagnostic's one-line JSON image |
//!
//! The added lines close the snippet beside the note, so a reader at the
//! detailed level reads the user's diagnostic first. The refusal name stays on
//! the first line at every level: a user copies it into a `refuses`
//! expectation. The alternative was a renderer per level, which would let two
//! levels disagree about what a diagnostic holds. Reversal: a face that needs
//! a fact no level shows adds it to the model, and the level that owns it
//! here.

use alloc::string::String;
use alloc::vec::Vec;

use annotate_snippets::AnnotationKind as Mark;
use annotate_snippets::Group;
use annotate_snippets::Level;
use annotate_snippets::Origin;
use annotate_snippets::Patch;
use annotate_snippets::Renderer;
use annotate_snippets::Snippet;
use annotate_snippets::renderer::DecorStyle;
use anodized::spec;
use gandr_surface_diagnostics::AnnotationKind;
use gandr_surface_diagnostics::Diagnostic;
use gandr_surface_diagnostics::PATHLESS;
use gandr_surface_diagnostics::Severity;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::style::RenderStyle;
use crate::style::Rendered;

/// `diagnostic` as a terminal prints it, in `style` at `verbosity`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: at [`Verbosity::Json`], the diagnostic's JSON image on one line,
///   whatever the style. Otherwise a ledger line is its path, `: ` and its
///   message; every other diagnostic leads with its severity, its identifier in
///   brackets when it has one and its message; quotes its excerpt with each
///   annotation and each located context marked at its bytes, under its path,
///   or names its path alone when it marks nothing; closes with each unlocated
///   context as a note, its note, the issue tracking it as a note when its
///   refusal is unimplemented, its help, and then the details its level adds;
///   and, when it proposes a fix inside its excerpt, a `help` group quoting the
///   excerpt with the fix applied. A source with an empty path is named
///   `<input>`. Plain adds no styling; styled adds the backend's colour
///   sequences. Caller path controls remain literal in both modes. No framing
///   terminator is appended.
/// - provides: the plain text the driver prints and the tests compare.
/// - fails: never.
/// - panics: none; every span reaches the backend inside the excerpt.
/// - intension: the backend chooses the connector layout; the loci it receives
///   are exactly the model's.
///
/// # Adequacy
/// - hypothesis: L1 — one byte-exact golden for each diagnostic kind and each
///   causal shape bounds layout evidence to those fixtures. L3 — pathless and
///   unlocated observations distinguish lost locations; plain/styled pairs
///   expose added colour; literal path controls expose false sanitization.
/// - witness: `tests::render::a_type_mismatch_renders_as_a_located_report`
/// - witness: `tests::render::each_causal_shape_renders_as_its_golden`
/// - witness: `tests::render::one_refusal_renders_at_every_verbosity`
/// - witness: `tests::render::forced_styling_colors_actual_facade_annotations`
/// - witness: `tests::render::an_unimplemented_refusal_closes_with_its_tracking_issue`
/// - witness: `render::tests::literal_path_controls_are_not_styling_or_framing`
#[spec(ensures: |ref ret| match verbosity {
    Verbosity::Json => ret.as_ref().starts_with('{') && !ret.as_ref().contains('\n'),
    Verbosity::User | Verbosity::Detailed | Verbosity::Debug => match (style, diagnostic.severity) {
        (_, Severity::Ledger) => !ret.as_ref().contains('\u{1b}'),
        (RenderStyle::Plain, Severity::Goal) => ret.as_ref().starts_with("goal"),
        (RenderStyle::Plain, Severity::Note) => ret.as_ref().starts_with("note"),
        (RenderStyle::Plain, Severity::Warning) => ret.as_ref().starts_with("warning"),
        (RenderStyle::Plain, Severity::Error) => ret.as_ref().starts_with("error"),
        (RenderStyle::Styled, _) => ret.as_ref().contains("\u{1b}["),
    },
})]
#[inline]
#[must_use]
pub fn render(
    diagnostic: &Diagnostic,
    style: RenderStyle,
    verbosity: Verbosity,
) -> Rendered
{
    if verbosity == Verbosity::Json {
        return Rendered::from(diagnostic.json());
    }
    let origin = if diagnostic.path.as_os_str().is_empty() {
        String::from(PATHLESS)
    }
    else {
        alloc::format!("{}", diagnostic.path.display())
    };
    let level = match diagnostic.severity {
        Severity::Ledger => {
            return Rendered::from(alloc::format!("{origin}: {}", diagnostic.message.text));
        },
        Severity::Goal => Level::INFO.with_name("goal"),
        Severity::Note => Level::NOTE,
        Severity::Warning => Level::WARNING,
        Severity::Error => Level::ERROR,
    };
    let title = level.primary_title(diagnostic.message.text.as_str());
    let title = match diagnostic.identifier {
        Maybe::Present(ref spelling) => title.id(alloc::format!("{spelling}")),
        Maybe::Absent(_) => title,
    };
    let labels: Vec<String> = diagnostic
        .contexts
        .iter()
        .map(gandr_surface_diagnostics::DiagnosticContext::label)
        .collect();
    let mut group = Group::with_title(title);
    let mut help: Vec<Group<'_>> = Vec::new();
    match diagnostic.excerpt {
        Maybe::Present(ref excerpt) => {
            let base = usize::from(excerpt.start);
            let range = |span: ByteSpan| {
                usize::from(span.start()).saturating_sub(base)
                    .. usize::from(span.end()).saturating_sub(base)
            };
            let mut snippet = Snippet::source(excerpt.text.as_str())
                .line_start(excerpt.line)
                .path(origin.as_str());
            for annotation in &diagnostic.annotations {
                let mark = match annotation.kind {
                    AnnotationKind::Primary => Mark::Primary,
                    AnnotationKind::Context => Mark::Context,
                };
                snippet = snippet.annotation(
                    mark.span(range(annotation.locus.span))
                        .label(annotation.label.as_str()),
                );
            }
            for (context, label) in diagnostic.contexts.iter().zip(&labels) {
                if let Maybe::Present(locus) = context.locus {
                    snippet = snippet
                        .annotation(Mark::Context.span(range(locus.span)).label(label.as_str()));
                }
            }
            group = group.element(snippet);
            if let Maybe::Present(ref fix) = diagnostic.fix
                && usize::from(fix.span.start()) >= base
                && usize::from(fix.span.end()) <= base.saturating_add(excerpt.text.len())
            {
                help.push(
                    Level::HELP.secondary_title("apply this edit").element(
                        Snippet::source(excerpt.text.as_str())
                            .line_start(excerpt.line)
                            .path(origin.as_str())
                            .patch(Patch::new(range(fix.span), fix.replacement.as_str())),
                    ),
                );
            }
        },
        Maybe::Absent(_) => {
            group = group.element(Origin::path(origin.as_str()));
        },
    }
    let notes: Vec<String> = diagnostic
        .contexts
        .iter()
        .filter(|context| matches!(context.locus, Maybe::Absent(_)))
        .map(gandr_surface_diagnostics::DiagnosticContext::note)
        .collect();
    for note in &notes {
        group = group.element(Level::NOTE.message(note.as_str()));
    }
    if let Maybe::Present(ref note) = diagnostic.note {
        group = group.element(Level::NOTE.message(note.as_str()));
    }
    let tracked = diagnostic.tracked();
    if let Maybe::Present(ref sentence) = tracked {
        group = group.element(Level::NOTE.message(sentence.as_str()));
    }
    if let Maybe::Present(ref help) = diagnostic.help {
        group = group.element(Level::HELP.message(help.as_str()));
    }
    let details = diagnostic.details(verbosity);
    for detail in &details {
        group = group.element(
            Level::NOTE
                .with_name(detail.name)
                .message(detail.text.as_str()),
        );
    }
    let renderer = match style {
        RenderStyle::Plain => Renderer::plain(),
        RenderStyle::Styled => Renderer::styled(),
    };
    let mut report = Vec::from([group]);
    report.append(&mut help);
    Rendered::from(renderer.decor_style(DecorStyle::Unicode).render(&report))
}

/// Path boundaries the renderer leaves literal.
#[cfg(test)]
mod tests
{
    use std::path::Path;

    use gandr_surface_diagnostics::Subject;
    use gandr_surface_diagnostics::Verbosity;
    use gandr_surface_diagnostics::diagnose;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_syntax::SourceText;

    use super::render;
    use crate::style::RenderStyle;

    #[test]
    fn literal_path_controls_are_not_styling_or_framing()
    {
        for path in [
            "plain.gandr",
            "escape\u{1b}[31m.gandr",
            "final\n",
            "final\r",
        ] {
            let diagnostic = diagnose(
                Path::new(path),
                SourceText::from(""),
                Subject::Source(LoweringRefusal::BudgetExceeded {
                    budget: 0_usize.into(),
                }),
            );
            let plain = render(&diagnostic, RenderStyle::Plain, Verbosity::User);
            let styled = render(&diagnostic, RenderStyle::Styled, Verbosity::User);
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
}
