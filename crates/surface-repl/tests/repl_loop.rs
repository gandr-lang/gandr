//! The loop observed from outside: lines offered, blocks and transcripts read.
//!
//! Every type a case expects is spelled by the renderer or read from a corpus
//! source, and every refusal a case expects is rendered by the diagnostics
//! renderer over the same revision, so no case restates a spelling the
//! surface owns.
//!
//! The loop's cases, in a `cfg(test)` module so the crate's lint wall reads
//! them as test code rather than as shipping code.

use std::io;
use std::path::Path;

use anodized::spec;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::ContentNode;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_core_incremental::NodeIndex;
use gandr_kernel_term::BaseType;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_diagnostics::Severity;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::entries;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Spelling;
use gandr_surface_grammar::built_in;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::OutKind;
use gandr_surface_render_remote::TranscriptBlock;
use gandr_surface_render_terminal::RenderStyle;
use gandr_surface_render_terminal::render;
use gandr_surface_repl::CompletionStatus;
use gandr_surface_repl::Ended;
use gandr_surface_repl::Fault;
use gandr_surface_repl::LineSource;
use gandr_surface_repl::LoopEvent;
use gandr_surface_repl::Prompt;
use gandr_surface_repl::Read;
use gandr_surface_repl::SessionLoop;
use gandr_surface_repl::SpanOrder;
use gandr_surface_repl::completeness;
use gandr_surface_repl::disk_notice;
use gandr_surface_repl::drive;
use gandr_surface_repl::finished;
use gandr_surface_repl::rows;
use gandr_surface_repl::run_batch;
use gandr_surface_repl::span_order;
use gandr_surface_repl::spell;
use gandr_surface_repl::write_block;
use gandr_surface_session::Session;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// Three selected strict corpus sources, by path from this crate.
const CORPUS: [&str; 3] = [
    concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../surface-corpus/strict/values.gandr"
    ),
    concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../surface-corpus/strict/functions.gandr"
    ),
    concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../surface-corpus/strict/classifier/universes.gandr"
    ),
];

/// The built-in grammar.
///
/// # Specification
/// - requires: the built-in grammar is valid.
/// - ensures: a nonempty grammar with one name per rule.
/// - provides: the grammar fixture.
/// - fails: never.
/// - panics: if the built-in grammar does not build.
///
/// # Adequacy
/// - hypothesis: L3 — open, closed and empty buffers distinguish the fixture's
///   completion decisions.
/// - witness: `tests::repl_loop::an_open_form_is_incomplete`
/// - witness: `tests::repl_loop::an_empty_buffer_is_complete`
#[spec(ensures: |ret| !ret.rules().is_empty() && ret.rules().len() == ret.rule_names().len())]
fn grammar() -> Pbg
{
    built_in().expect("the built-in grammar builds")
}

/// A loop rendering refusals plainly.
///
/// # Specification
/// - requires: the built-in grammar and role table are valid.
/// - ensures: a fresh loop rendering plain diagnostics.
/// - provides: the external loop fixture.
/// - fails: never.
/// - panics: if the loop cannot be built.
///
/// # Adequacy
/// - hypothesis: L3 — the first open form changes the fresh prompt, and an
///   empty loop finishes without a transcript.
/// - witness: `tests::repl_loop::an_open_form_continues`
/// - witness: `tests::repl_loop::finishing_an_empty_loop_yields_nothing`
#[spec(ensures: |ret| ret.prompt() == Prompt::Fresh)]
fn repl() -> SessionLoop
{
    SessionLoop::new(RenderStyle::Plain).expect("the loop starts")
}

/// Offer `line` to `repl`.
///
/// # Specification
/// - requires: conversion yields admissible text and the session does not
///   fault.
/// - ensures: the loop event; a completed block or quit leaves a fresh prompt.
/// - provides: the event observer used by the external loop witnesses.
/// - fails: never.
/// - panics: if the session faults.
///
/// # Adequacy
/// - hypothesis: L3 — a continued form, a completed form and quit have distinct
///   events and prompt transitions.
/// - witness: `tests::repl_loop::an_open_form_continues`
/// - witness: `tests::repl_loop::quit_stops_the_loop`
#[spec(ensures: |ret| matches!(ret, LoopEvent::Continue) || repl.prompt() == Prompt::Fresh)]
fn offer<'line, Line>(
    repl: &mut SessionLoop,
    line: Line,
) -> LoopEvent
where
    Line: Into<SourceText<'line>>,
{
    repl.offer(line.into()).expect("the session does not fault")
}

/// The block `line` answers with.
///
/// # Specification
/// - requires: offering the converted text answers a block without a fault.
/// - ensures: that block, with no source-kind result row, and a fresh prompt.
/// - provides: the transcript-block observer.
/// - fails: never.
/// - panics: if the event is not a block or the session faults.
///
/// # Adequacy
/// - hypothesis: L3 — exact echoed multiline text, result kinds and later name
///   resolution observe the completed submission.
/// - witness: `tests::repl_loop::an_open_form_continues`
/// - witness: `tests::repl_loop::a_definition_is_visible_on_the_next_line`
#[spec(ensures: |ret| repl.prompt() == Prompt::Fresh
        && ret.lines.iter().all(|row| row.0 != OutKind::Source))]
fn block<'line, Line>(
    repl: &mut SessionLoop,
    line: Line,
) -> TranscriptBlock
where
    Line: Into<SourceText<'line>>,
{
    let line = line.into();
    match offer(repl, line) {
        LoopEvent::Block(block) => block,
        other @ (LoopEvent::Continue | LoopEvent::Quit) => {
            panic!("`{line}` answers a block, not {other:?}")
        },
    }
}

/// The lines `line` answers with.
///
/// # Specification
/// - requires: offering the converted text answers a block without a fault.
/// - ensures: its result rows, never echo rows.
/// - provides: the result-only transcript observer.
/// - fails: never.
/// - panics: if the event is not a block or the session faults.
///
/// # Adequacy
/// - hypothesis: L3 — type, value and goal rows are compared at their exact
///   kinds and semantic text.
/// - witness: `tests::repl_loop::a_definition_is_visible_on_the_next_line`
/// - witness: `tests::repl_loop::a_hole_encodes_as_a_goal_line`
#[spec(ensures: |ret| repl.prompt() == Prompt::Fresh
        && ret.iter().all(|row| row.0 != OutKind::Source))]
fn lines<'line, Line>(
    repl: &mut SessionLoop,
    line: Line,
) -> Vec<(OutKind, String)>
where
    Line: Into<SourceText<'line>>,
{
    block(repl, line).lines
}

/// The renderer's spelling of the base type `base`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the primitive type's nonempty, single-token presentation.
/// - provides: expected primitive type spelling from the shared renderer.
/// - fails: never.
/// - panics: if the presentation engine rejects the primitive layout.
///
/// # Adequacy
/// - hypothesis: L3 — integer and string signatures, probes and definitions
///   agree with the renderer's type vocabulary.
/// - witness: `tests::repl_loop::a_definition_is_visible_on_the_next_line`
/// - witness: `tests::repl_loop::a_later_definition_settles_an_earlier_goal`
#[spec(ensures: |ret| !ret.is_empty() && !ret.contains(char::is_whitespace))]
fn base(base: BaseType) -> String
{
    spell(&[ContentNode::Base(base)], NodeIndex::from(0))
        .expect("a base type lays out")
        .to_string()
}

/// A fresh session as the loop makes one, over the strict root.
///
/// # Specification
/// - requires: the built-in grammar is valid.
/// - ensures: a strict-root session with no preceding resume.
/// - provides: an independent session for report and checkpoint observers.
/// - fails: never.
/// - panics: if the built-in grammar does not build.
///
/// # Adequacy
/// - hypothesis: L2 — refusals and checked signatures agree across the direct
///   session observer and the loop.
/// - witness: `tests::repl_loop::an_outcome_only_refusal_is_visible_in_the_repl`
#[spec(ensures: |ret| matches!(ret.last(), Maybe::Absent(_)))]
fn session() -> Session<MemoryCheckpointStore, InMemoryBlockStore>
{
    Session::new(
        grammar(),
        SourceRoot::Strict,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        BackendArtifact::from(b"gandr-surface-repl tests".as_slice()),
    )
}

/// The diagnostics renderer's refusal reports over `revision`, under
/// `style`, each as the diagnostic line a block carries.
///
/// # Specification
/// - requires: the grammar builds and submission does not fault.
/// - ensures: only non-goal reports, as diagnostic rows with trailing
///   whitespace removed, in report order.
/// - provides: the independent renderer observer for refused revisions.
/// - fails: never.
/// - panics: if fixture creation or submission fails.
///
/// # Adequacy
/// - hypothesis: L2 — refused chunks and styled refusals agree with the
///   renderer over the same revision, without pinning diagnostic prose.
/// - witness: `tests::repl_loop::an_outcome_only_refusal_is_visible_in_the_repl`
/// - witness: `tests::repl_loop::styled_session_diagnostics_reach_the_repl_transcript`
#[spec(ensures: |ret| ret.iter().all(|row| row.0 == OutKind::Diag && row.1.trim_end() == row.1))]
fn refusals<'revision, Revision>(
    revision: Revision,
    style: RenderStyle,
) -> Vec<(OutKind, String)>
where
    Revision: Into<SourceText<'revision>>,
{
    let mut session = session();
    let step = session
        .submit(revision.into())
        .expect("the session does not fault")
        .into_step(Path::new(""));
    entries(&step, Verb::Check(Goals::Reported))
        .filter_map(|diagnostic| match diagnostic.severity {
            Severity::Error | Severity::Note | Severity::Warning => {
                let mut text = render(&diagnostic, style, Verbosity::User).to_string();
                let kept = text.trim_end().len();
                text.truncate(kept);
                Some((OutKind::Diag, text))
            },
            Severity::Goal | Severity::Ledger => None,
        })
        .collect()
}

/// Whether the parser expects no further token after `buffer`.
///
/// # Specification
/// - requires: the built-in grammar is valid.
/// - ensures: the parser's completeness, including completion of empty input.
/// - provides: the completion observer for text fixtures.
/// - fails: never.
/// - panics: if the grammar does not build.
///
/// # Adequacy
/// - hypothesis: L3 — open forms and unterminated declarations wait; terminated
///   declarations, atoms, holes and empty input submit.
/// - witness: `tests::repl_loop::an_open_form_is_incomplete`
/// - witness: `tests::repl_loop::a_declaration_waits_for_its_terminator`
/// - witness: `tests::repl_loop::an_empty_buffer_is_complete`
#[spec(ensures: |ret| !<&str>::from(buffer).is_empty() || bool::from(ret))]
fn complete(buffer: SourceText<'_>) -> CompletionStatus
{
    completeness(&grammar(), buffer)
}

/// An open group is incomplete, alone or inside a definition.
#[test]
fn an_open_form_is_incomplete()
{
    assert!(!bool::from(complete(SourceText::from("("))));
    assert!(!bool::from(complete(SourceText::from("def a = ("))));
}

/// A bare atom is complete.
#[test]
fn a_bare_atom_is_complete()
{
    assert!(bool::from(complete(SourceText::from("42"))));
}

/// A hole is a complete term: holes are typeable, so a buffer holding one
/// is submitted.
#[test]
fn a_hole_is_complete()
{
    assert!(bool::from(complete(SourceText::from("?"))));
    assert!(bool::from(complete(SourceText::from("def h = ? ;"))));
}

/// A definition waits for its terminator, and submits with it.
#[test]
fn a_declaration_waits_for_its_terminator()
{
    assert!(!bool::from(complete(SourceText::from("def answer ="))));
    assert!(bool::from(complete(SourceText::from("def answer = 42 ;"))));
}

/// An empty buffer expects no further token.
#[test]
fn an_empty_buffer_is_complete()
{
    assert_eq!(
        complete(SourceText::from("")),
        CompletionStatus::from(true),
        "the empty buffer expects no token"
    );
}

/// An open form continues the buffer, and the prompt says so.
#[test]
fn an_open_form_continues()
{
    let mut repl = repl();
    assert_eq!(offer(&mut repl, "def a = ("), LoopEvent::Continue);
    assert_eq!(repl.prompt(), Prompt::Continuing);
    let closed = block(&mut repl, "1) ;");
    assert_eq!(closed.source, "def a = (\n1) ;");
    assert_eq!(repl.prompt(), Prompt::Fresh);
}

/// A complete atom is read as a probe: its type and value are printed, and
/// the probe is kept, so the name is usable on the next line.
#[test]
fn a_complete_atom_submits()
{
    let mut repl = repl();
    let integer = base(BaseType::Integer);
    let block = block(&mut repl, "42");
    assert_eq!(block.source, "42");
    assert_eq!(block.lines, [
        (OutKind::Type, format!("it : {integer}")),
        (OutKind::Value, "42".to_owned())
    ]);
    assert_eq!(lines(&mut repl, "it"), [
        (OutKind::Type, format!("it1 : {integer}")),
        (OutKind::Value, "42".to_owned())
    ]);
}

/// An expression at the prompt is read as a probe: its type and value are
/// printed, and the probe is kept, so the name is usable on the next line.
#[test]
fn an_expression_is_read_as_a_probe()
{
    let mut repl = repl();
    let integer = base(BaseType::Integer);
    assert_eq!(lines(&mut repl, "(1, 2)"), [
        (OutKind::Type, format!("it : {integer} * {integer}")),
        (OutKind::Value, "(1, 2)".to_owned())
    ]);
    assert_eq!(lines(&mut repl, "it"), [
        (OutKind::Type, format!("it1 : {integer} * {integer}")),
        (OutKind::Value, "(1, 2)".to_owned())
    ]);
}

/// A type at the prompt reports its sort alone: a sort literal synthesizes a
/// universe, so its printed type is the sort, and the session does not
/// evaluate a universe — the machine carries no image of a code, and the
/// stuck note is not part of the answer.
#[test]
fn a_type_reports_its_sort()
{
    let mut repl = repl();
    assert_eq!(lines(&mut repl, "Integer"), [(
        OutKind::Type,
        "it : Type".to_owned()
    )]);
}

/// An item at the prompt still declares: a declaration head is read as
/// declarations, not as a probe.
#[test]
fn an_item_still_declares()
{
    let mut repl = repl();
    let integer = base(BaseType::Integer);
    assert_eq!(lines(&mut repl, "def it = 42 ;"), [
        (OutKind::Type, format!("it : {integer}")),
        (OutKind::Value, "42".to_owned())
    ]);
}

/// A malformed expression's diagnostic carries the line's range, not the
/// probe's: the echo is the line the user typed, the refusal quotes the line
/// and marks its bytes, and the refused probe is not kept, so the name stays
/// free.
#[test]
fn a_malformed_expression_carries_the_line_s_range()
{
    let mut repl = repl();
    let block = block(&mut repl, "nope");
    assert_eq!(block.source, "nope");
    assert_eq!(block.lines.len(), 1, "one diagnostic: {:?}", block.lines);
    let diagnostic = &block.lines[0].1;
    assert!(
        block.lines[0].0 == OutKind::Diag
            && diagnostic.contains("`nope` is not defined")
            && diagnostic.contains("<input>:1:1")
            && diagnostic.contains("│ nope")
            && !diagnostic.contains("def it = nope ;")
            && !diagnostic.contains(":1:10"),
        "the refusal carries the line's range, not the probe's: {diagnostic:?}"
    );
    let integer = base(BaseType::Integer);
    assert_eq!(lines(&mut repl, "def it = 1 ;"), [
        (OutKind::Type, format!("it : {integer}")),
        (OutKind::Value, "1".to_owned())
    ]);
}

/// #1467: a repair at the prompt names the bytes of the line the block echoes,
/// as the refusal beside it does, not the bytes of the probe the line is
/// wrapped in.
#[test]
fn a_repair_at_the_prompt_names_the_line_s_bytes_1467()
{
    let mut repl = repl();
    let block = block(&mut repl, "1 )");
    let repairs: Vec<&str> = block
        .lines
        .iter()
        .filter(|row| row.0 == OutKind::Diag && row.1.starts_with("warning[W0012]"))
        .map(|row| row.1.as_str())
        .collect();
    assert_eq!(
        repairs,
        ["warning[W0012]: parse repaired: a missing delimiter at 2..3"],
        "{:?}",
        block.lines
    );
}

/// A definition kept on one line is in scope on the next.
#[test]
fn a_definition_is_visible_on_the_next_line()
{
    let mut repl = repl();
    let integer = base(BaseType::Integer);
    assert_eq!(lines(&mut repl, "def y = 5 ;"), [
        (OutKind::Type, format!("y : {integer}")),
        (OutKind::Value, "5".to_owned())
    ]);
    assert_eq!(lines(&mut repl, "def z = y ;"), [
        (OutKind::Type, format!("z : {integer}")),
        (OutKind::Value, "5".to_owned())
    ]);
}

/// A declaration owing its definition is a goal line naming its type.
#[test]
fn a_hole_encodes_as_a_goal_line()
{
    let mut repl = repl();
    assert_eq!(lines(&mut repl, "def later : Integer ;"), [(
        OutKind::Goal,
        format!("later : {}", base(BaseType::Integer))
    )]);
}

/// A definition supplied later settles the goal, and the declaration's
/// line becomes a type line.
#[test]
fn a_later_definition_settles_an_earlier_goal()
{
    let mut repl = repl();
    let string = base(BaseType::String);
    assert_eq!(lines(&mut repl, "def h : String ;"), [(
        OutKind::Goal,
        format!("h : {string}")
    )]);
    assert_eq!(lines(&mut repl, r#"def h = "now" ;"#), [
        (OutKind::Type, format!("h : {string}")),
        (OutKind::Value, r#""now""#.to_owned())
    ]);
}

/// A checker's refusal reaches the transcript as the diagnostics renderer's
/// own report over the session's revision, and the refused chunk is not
/// kept: the declaration can still be defined.
#[test]
fn an_outcome_only_refusal_is_visible_in_the_repl()
{
    let mut repl = repl();
    let _goal = lines(&mut repl, "def wrong : String ;");
    let refused = lines(&mut repl, "def wrong = 42 ;");
    let expected = refusals("def wrong : String ;\ndef wrong = 42 ;", RenderStyle::Plain);
    assert!(!expected.is_empty(), "the revision is refused");
    assert_eq!(refused, expected);
    assert_eq!(lines(&mut repl, r#"def wrong = "right" ;"#), [
        (OutKind::Type, format!("wrong : {}", base(BaseType::String))),
        (OutKind::Value, r#""right""#.to_owned())
    ]);
}

/// A refused chunk leaves the accepted text as it was: a name it declared
/// stays unresolved, and an earlier name stays in scope.
#[test]
fn a_refused_chunk_is_not_kept()
{
    let mut repl = repl();
    let _kept = lines(&mut repl, "def a = 1 ;");
    let refused = lines(&mut repl, "def b = missing ;");
    assert!(
        refused.iter().all(|&(kind, _)| kind == OutKind::Diag) && !refused.is_empty(),
        "{refused:?}"
    );
    let unresolved = lines(&mut repl, "def c = b ;");
    assert_eq!(
        unresolved,
        refusals("def a = 1 ;\ndef c = b ;", RenderStyle::Plain)
    );
    assert_eq!(lines(&mut repl, "def d = a ;"), [
        (OutKind::Type, format!("d : {}", base(BaseType::Integer))),
        (OutKind::Value, "1".to_owned())
    ]);
}

/// Under the styled rendering a refusal carries the renderer's escapes;
/// under the plain one it carries none.
#[test]
fn styled_session_diagnostics_reach_the_repl_transcript()
{
    let mut styled = SessionLoop::new(RenderStyle::Styled).expect("the loop starts");
    let refused = lines(&mut styled, "def broken = missing ;");
    assert_eq!(
        refused,
        refusals("def broken = missing ;", RenderStyle::Styled)
    );
    assert!(
        refused.iter().any(|row| row.1.contains('\u{1b}')),
        "{refused:?}"
    );
    let plain = lines(&mut repl(), "def broken = missing ;");
    assert!(plain.iter().all(|row| !row.1.contains('\u{1b}')));
}

/// `:quit` and `:q` stop the loop.
#[test]
fn quit_stops_the_loop()
{
    let mut repl = repl();
    assert_eq!(offer(&mut repl, ":quit"), LoopEvent::Quit);
    assert_eq!(offer(&mut repl, ":q"), LoopEvent::Quit);
}

/// `:help` lists every command, `:reset` forgets every declaration, and a
/// command missing its argument or unknown answers with a note.
#[test]
fn the_meta_commands_answer()
{
    let mut repl = repl();
    let help = lines(&mut repl, ":help");

    assert!(help.iter().all(|&(kind, _)| kind == OutKind::Info));
    for command in [":type", ":load", ":reset", ":help", ":quit"] {
        assert!(
            help.iter().any(|row| row.1.starts_with(command)),
            "`{command}` is listed"
        );
    }
    let _kept = lines(&mut repl, "def y = 1 ;");
    assert!(matches!(lines(&mut repl, ":reset").as_slice(), [(
        OutKind::Info,
        _
    )]));
    assert_eq!(
        lines(&mut repl, "def z = y ;"),
        refusals("def z = y ;", RenderStyle::Plain)
    );
    for command in [":load", ":type", ":frob x"] {
        let answer = block(&mut repl, command);
        assert_eq!(answer.source, command);
        assert!(matches!(answer.lines.as_slice(), [(OutKind::Info, _)]));
    }
}

/// `:type` answers its expression's type, keeps nothing, and probes under
/// a name no accepted declaration carries.
#[test]
fn the_type_command_answers_without_keeping_the_probe()
{
    let mut repl = repl();
    let integer = base(BaseType::Integer);
    let typed = block(&mut repl, ":type 42");
    assert_eq!(typed.source, ":type 42");
    assert_eq!(typed.lines, [(OutKind::Type, format!(": {integer}"))]);
    assert_eq!(lines(&mut repl, "def it = 1 ;"), [
        (OutKind::Type, format!("it : {integer}")),
        (OutKind::Value, "1".to_owned())
    ]);
    assert_eq!(lines(&mut repl, ":type it"), [(
        OutKind::Type,
        format!(": {integer}")
    )]);
    assert_eq!(lines(&mut repl, r#"def it1 = "s" ;"#), [
        (OutKind::Type, format!("it1 : {}", base(BaseType::String))),
        (OutKind::Value, r#""s""#.to_owned())
    ]);
}

/// A refused `:type` expression is reported under its probe's name: `it`
/// while nothing accepted is named so, then the first free `it1`.
#[test]
fn a_refused_type_probe_is_reported_under_the_first_free_probe_name()
{
    let mut repl = repl();
    let refused_as = |repl: &mut SessionLoop, probe: &str| {
        let answer = block(repl, ":type nope");
        assert!(
            matches!(answer.lines.as_slice(), [(OutKind::Diag, text)]
                    if text.contains(&format!("def {probe} = nope ;"))
                        && text.contains(&format!("`{probe}` is expected to check"))),
            "{probe}: {:?}",
            answer.lines
        );
    };
    refused_as(&mut repl, "it");
    drop(lines(&mut repl, "def it = 1 ;"));
    refused_as(&mut repl, "it1");
}

/// `:load` submits a file as one chunk, every declaration answering a
/// type line and a value line, and a file that cannot be read answers why.
#[test]
fn a_loaded_file_is_one_chunk()
{
    let mut repl = repl();
    let command = format!(":load {}", CORPUS[0]);
    let loaded = block(&mut repl, command.as_str());
    assert_eq!(loaded.source, command);
    let command = format!(":load {}/Cargo.toml/not-a-file", env!("CARGO_MANIFEST_DIR"));
    let missing = block(&mut repl, command.as_str());
    assert_eq!(missing.source, command);
    assert!(matches!(missing.lines.as_slice(), [(OutKind::Diag, text)]
            if text.contains("Cargo.toml/not-a-file")));
    assert_eq!(lines(&mut repl, "def again = echo ;"), [
        (
            OutKind::Type,
            format!("again : {}", base(BaseType::Integer))
        ),
        (OutKind::Value, "42".to_owned())
    ]);
}

/// `:reload` resubmits a loaded file rewritten on disk in place of its
/// chunk, judging the declarations typed after it again; a rewrite one of
/// them refuses keeps the earlier chunk; an unchanged file is left alone.
#[test]
fn a_reloaded_file_replaces_its_chunk()
{
    let integer = base(BaseType::Integer);
    let path = std::env::temp_dir().join(format!("gandr-reload-{}.gandr", std::process::id()));
    let named = path.display().to_string();
    std::fs::write(&path, "def a = 1 ;\n").expect("the file writes");
    let mut repl = repl();
    drop(lines(&mut repl, format!(":load {named}").as_str()));
    drop(lines(&mut repl, "def g : Integer ;"));
    drop(lines(&mut repl, "def g = a ;"));
    assert_eq!(lines(&mut repl, ":reload"), [(
        OutKind::Info,
        "no loaded file changed on disk".to_owned()
    )]);
    std::fs::write(&path, "def a = 2 ;\n").expect("the file writes");
    assert_eq!(
        lines(&mut repl, ":reload"),
        [
            (OutKind::Info, format!("`{named}` resubmitted")),
            (OutKind::Type, format!("a : {integer}")),
            (OutKind::Value, "2".to_owned()),
            (OutKind::Type, format!("g : {integer}")),
            (OutKind::Value, "2".to_owned()),
        ],
        "the declaration after the file is judged again over its new text"
    );
    std::fs::write(&path, "def a = \"s\" ;\n").expect("the file writes");
    let refused = lines(&mut repl, ":reload");
    assert!(
        matches!(refused.as_slice(), [(OutKind::Diag, text), (OutKind::Info, kept)]
            if text.contains("expected `Integer`, found `String`")
                && *kept == format!("`{named}` keeps its earlier chunk")),
        "{refused:?}"
    );
    assert_eq!(
        lines(&mut repl, "def d = a ;"),
        [
            (OutKind::Type, format!("d : {integer}")),
            (OutKind::Value, "2".to_owned()),
        ],
        "the refused rewrite left the earlier chunk in place"
    );
    drop(std::fs::remove_file(&path));
}

/// Of two loaded files, the first rewritten longer is resubmitted and the
/// second's chunk moves with it: rewriting the second afterwards is
/// resubmitted over its own text alone. A loaded file deleted from disk is
/// reported as unreadable, and the rest of the reload goes on.
#[test]
fn a_longer_reload_moves_the_later_files_and_a_missing_one_is_named()
{
    let integer = base(BaseType::Integer);
    let scratch = |name: &str| {
        std::env::temp_dir().join(format!("gandr-reload-{name}-{}.gandr", std::process::id()))
    };
    let (first, second) = (scratch("first"), scratch("second"));
    let (first_named, second_named) = (first.display().to_string(), second.display().to_string());
    std::fs::write(&first, "def a = 1 ;\n").expect("the file writes");
    std::fs::write(&second, "def b = a ;\n").expect("the file writes");
    let mut repl = repl();
    drop(lines(&mut repl, format!(":load {first_named}").as_str()));
    drop(lines(&mut repl, format!(":load {second_named}").as_str()));
    std::fs::write(&first, "def a = 1 ;\ndef c = 3 ;\n").expect("the file writes");
    assert_eq!(lines(&mut repl, ":reload"), [
        (OutKind::Info, format!("`{first_named}` resubmitted")),
        (OutKind::Type, format!("a : {integer}")),
        (OutKind::Value, "1".to_owned()),
        (OutKind::Type, format!("c : {integer}")),
        (OutKind::Value, "3".to_owned()),
        (OutKind::Type, format!("b : {integer}")),
        (OutKind::Value, "1".to_owned()),
    ]);
    std::fs::write(&second, "def b = c ;\n").expect("the file writes");
    assert_eq!(lines(&mut repl, ":reload"), [
        (OutKind::Info, format!("`{second_named}` resubmitted")),
        (OutKind::Type, format!("b : {integer}")),
        (OutKind::Value, "3".to_owned()),
    ]);
    std::fs::remove_file(&first).expect("the file is removed");
    let missing = lines(&mut repl, ":reload");
    assert!(
        matches!(missing.as_slice(), [(OutKind::Diag, text), ..]
            if text.starts_with(&format!("cannot read `{first_named}`"))),
        "{missing:?}"
    );
    drop(std::fs::remove_file(&second));
}

/// The notice for a loaded file changed on disk is one information line
/// naming the file and the command that resubmits it.
#[test]
fn a_disk_notice_names_the_file_and_the_reload()
{
    let notice = disk_notice(Path::new("/tmp/changed.gandr"));
    assert!(notice.source.is_empty() && notice.source_hl.is_empty());
    assert_eq!(notice.lines, [(
        OutKind::Info,
        "`/tmp/changed.gandr` changed on disk; :reload to resubmit".to_owned()
    )]);
}

/// A function whose later parameter's type reads an earlier type
/// parameter answers a type line in the dependent alias's spelling: the
/// binder named, its universe, and the decodes written as the binder they
/// read; its value line follows.
#[test]
fn a_dependent_function_names_its_type_with_its_binder()
{
    let mut repl = repl();
    assert_eq!(
        lines(&mut repl, "def id(a : Type, x : a) -> -F a { return x }"),
        [
            (OutKind::Type, "id : (a : Type, a) => a".to_owned()),
            (OutKind::Value, "fn (a) { fn (b) { b } }".to_owned())
        ]
    );
}

/// One-line signatures in three selected strict corpus sources retain
/// the type spelling written in those sources.
#[test]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "bounded: the lines one `:load` of a selected corpus source prints"
    )
)]
fn corpus_types_spell_as_their_source_writes_them()
{
    for path in CORPUS {
        let source = std::fs::read_to_string(path).expect("the corpus source reads");
        let mut repl = repl();
        let loaded = lines(&mut repl, format!(":load {path}").as_str());

        for written in source.lines() {
            let Some(signature) = written
                .strip_prefix("def ")
                .and_then(|rest| rest.strip_suffix(" ;"))
                .filter(|rest| rest.contains(" : "))
            else {
                continue;
            };

            assert!(
                loaded.contains(&(OutKind::Type, signature.to_owned())),
                "{path}: `{signature}` among {loaded:?}"
            );
        }
    }
}

/// A submission's echo carries the highlighter's spans, `def` among them
/// as a keyword.
#[test]
fn a_submission_carries_highlight_spans()
{
    let mut repl = repl();
    let block = block(&mut repl, "def one = 1 ;");
    assert!(
        block
            .source_hl
            .iter()
            .any(|span| span.role == HlRole::Keyword && usize::from(span.range.end()) == 3),
        "{:?}",
        block.source_hl
    );
}

/// Over the selected corpus sources, every emitted span is ordered and
/// lies inside its echo on character boundaries.
#[test]
fn transcript_spans_are_sorted_and_disjoint()
{
    for path in CORPUS {
        let source = std::fs::read_to_string(path).expect("the corpus source reads");
        let mut repl = repl();

        for line in source.lines() {
            if let LoopEvent::Block(block) = offer(&mut repl, line) {
                assert_eq!(span_order(&block.source_hl), SpanOrder::SortedAndDisjoint);
                assert!(block.source_hl.iter().all(|span| {
                    block
                        .source
                        .is_char_boundary(usize::from(span.range.start()))
                        && block.source.is_char_boundary(usize::from(span.range.end()))
                }));
            }
        }
    }
}

/// A buffer still open at the end of input is submitted, not dropped, and
/// its repair is a warning line naming the code and the repaired bytes.
#[test]
fn an_incomplete_buffer_is_submitted_at_end_of_input()
{
    let mut repl = repl();
    assert_eq!(offer(&mut repl, "def a = ("), LoopEvent::Continue);
    let Ok(Maybe::Present(block)) = repl.finish()
    else {
        panic!("the open buffer is submitted");
    };
    assert_eq!(block.source, "def a = (");
    assert!(
        block.lines.contains(&(
            OutKind::Diag,
            "warning[W0012]: parse repaired: a missing delimiter at 6..7".to_owned()
        )),
        "{:?}",
        block.lines
    );
}

/// Finishing a loop with nothing waiting submits nothing.
#[test]
fn finishing_an_empty_loop_yields_nothing()
{
    let mut repl = repl();
    assert_eq!(repl.finish(), Ok(Maybe::Absent(finished::Absent::Empty)));
}

/// A waiting buffer is reported by the first finish only.
#[test]
fn finishing_twice_reports_once()
{
    let mut repl = repl();
    assert_eq!(offer(&mut repl, "def a = ("), LoopEvent::Continue);
    assert!(matches!(repl.finish(), Ok(Maybe::Present(_))));
    assert_eq!(repl.finish(), Ok(Maybe::Absent(finished::Absent::Empty)));
}

/// The transcript of `input` piped through the batch face.
///
/// # Specification
/// - requires: the grammar and role table build and submission does not fault.
/// - ensures: the batch ending and UTF-8 transcript; each emitted row ends with
///   a newline and an editor fault is impossible.
/// - provides: the complete batch transcript observer.
/// - fails: never.
/// - panics: if the vector writer or UTF-8 conversion unexpectedly fails.
///
/// # Adequacy
/// - hypothesis: L3 — exact successful output, an incomplete final buffer and
///   an input fault distinguish output and ending mistakes.
/// - witness: `tests::repl_loop::piped_value_prints_a_transcript`
/// - witness: `tests::repl_loop::unreadable_input_ends_the_batch_faulted`
#[spec(ensures: |ret| !matches!(ret.0, Ended::Faulted(Fault::Editor(_)))
        && (ret.1.is_empty() || ret.1.ends_with('\n')))]
fn piped<Input>(input: Input) -> (Ended, String)
where
    Input: std::io::BufRead,
{
    let mut output = Vec::new();
    let ended = run_batch(input, &mut output, RenderStyle::Plain, Spelling::Unicode)
        .expect("the transcript is written");
    (
        ended,
        String::from_utf8(output).expect("the transcript is UTF-8"),
    )
}

/// #782: a loop asked for ASCII writes the value a word runs to, and the
/// types a refusal names, in ASCII.
#[test]
fn a_value_is_written_in_the_spelling_asked_782()
{
    let input = "data Circle : Type { Base : Circle; loop : Base <-> Base; }\ndef once : +U (-F \
                 Path(Circle, Base, Base)) ;\ndef once = thunk { loop } ;\ndef r : Integer ≃ \
                 String ;\ndef r = 1 ;\n";
    let transcript = |spelling| {
        let mut output = Vec::new();
        let _ended = run_batch(input.as_bytes(), &mut output, RenderStyle::Plain, spelling)
            .expect("the transcript is written");
        String::from_utf8(output).expect("the transcript is UTF-8")
    };
    for (spelling, word, relation) in [
        (Spelling::Unicode, "loop ∷ here(Base)", "Integer ≃ String"),
        (Spelling::Ascii, "loop :: here(Base)", "Integer <~> String"),
    ] {
        let written = transcript(spelling);
        assert!(
            written.contains(word) && written.contains(&format!("expected `{relation}`")),
            "the word and the relation in {spelling:?}: {written}"
        );
    }
}

/// A piped session loading a corpus source and asking a type prints the
/// echo, a type line and a value line per declaration, then the answer.
#[test]
fn piped_value_prints_a_transcript()
{
    let input = format!(":load {}\n:type answer\n:q\n", CORPUS[0]);
    let (ended, transcript) = piped(input.as_bytes());
    assert!(matches!(ended, Ended::Completed));
    let integer = base(BaseType::Integer);
    let string = base(BaseType::String);
    let unit = spell(&[ContentNode::Product(Vec::new())], NodeIndex::from(0))
        .expect("the unit type lays out")
        .to_string();
    let expected = [
        format!("▸ :load {}", CORPUS[0]),
        format!("answer : {integer}"),
        "= 42".to_owned(),
        format!("greeting : {string}"),
        r#"= "hello, gandr""#.to_owned(),
        format!("nothing : {unit}"),
        "= unit".to_owned(),
        format!("copy : {integer}"),
        "= 42".to_owned(),
        format!("echo : {integer}"),
        "= 42".to_owned(),
        "▸ :type answer".to_owned(),
        format!(": {integer}"),
    ];
    assert_eq!(transcript.lines().collect::<Vec<_>>(), expected);
}

/// A block's rows: the echo's rows across a `\r\n`, a diagnostic's rows,
/// a note whose empty middle row is bare, and no row for an empty line;
/// each row starts at its byte offset in its own text, and the plain
/// transcript prints exactly these rows.
#[test]
fn a_block_lays_out_as_rows()
{
    let block = TranscriptBlock {
        source: String::from("def a = (\r\n1) ;"),
        source_hl: Vec::new(),
        lines: Vec::from([
            (OutKind::Diag, String::from("error: first\n  --> here\n")),
            (OutKind::Info, String::from("a\n\nb")),
            (OutKind::Goal, String::new()),
        ]),
    };
    let laid: Vec<(OutKind, &str, &str, usize)> = rows(&block)
        .map(|row| {
            (
                row.kind,
                <&str>::from(row.lead),
                row.text,
                usize::from(row.start),
            )
        })
        .collect();
    assert_eq!(laid, [
        (OutKind::Source, "▸ ", "def a = (", 0_usize),
        (OutKind::Source, "  ", "1) ;", 11),
        (OutKind::Diag, "", "error: first", 0),
        (OutKind::Diag, "", "  --> here", 13),
        (OutKind::Info, "· ", "a", 0),
        (OutKind::Info, "", "", 2),
        (OutKind::Info, "  ", "b", 3),
    ]);
    let mut written = Vec::new();
    write_block(&mut written, &block).expect("a vector takes every write");
    assert_eq!(
        String::from_utf8(written).expect("the transcript is UTF-8"),
        "▸ def a = (\n  1) ;\nerror: first\n  --> here\n· a\n\n  b\n"
    );
}

/// Text the grammar cannot read is reported in the transcript.
#[test]
fn an_unparseable_pipe_reports_rather_than_going_quiet()
{
    let (ended, transcript) = piped(b"@@@ !! nonsense\n".as_slice());
    assert!(matches!(ended, Ended::Completed));
    let printed: Vec<&str> = transcript.lines().collect();
    assert_eq!(printed.first().copied(), Some("▸ @@@ !! nonsense"));
    assert!(
        printed
            .iter()
            .skip(1)
            .any(|line| line.starts_with("error[")),
        "{transcript}"
    );
}

/// Input that is not text ends the batch faulted, after what was read.
#[test]
fn unreadable_input_ends_the_batch_faulted()
{
    let (ended, transcript) = piped(b"def a = 1 ;\n\xff\xfe\n".as_slice());
    assert!(
        matches!(ended, Ended::Faulted(Fault::Input(_))),
        "{ended:?}"
    );
    assert_eq!(transcript.lines().next(), Some("▸ def a = 1 ;"));
}

/// A scripted line source standing in for the terminal, recording the
/// prompts it was read under.
struct Script
{
    /// The reads still to answer, last first.
    reads: Vec<Read>,
    /// The prompts asked so far.
    prompts: Vec<Prompt>,
}

impl LineSource for Script
{
    /// The next scripted read, or the end.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one recorded prompt and the last queued read, or end when the
    ///   queue is empty, consuming at most one event.
    /// - provides: the scripted source for the actual interactive driver.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — prompt order, interrupted input and final submission
    ///   are observed through the driver's transcript and source state.
    /// - witness: `tests::repl_loop::the_terminal_face_discards_on_interrupt_and_submits_at_the_end`
    #[spec(captures: [reads = self.reads.len(), prompts = self.prompts.len(),
            kind = self.reads.last().map(core::mem::discriminant)],
            ensures: |ret| self.reads.len() == reads.saturating_sub(1)
                && self.prompts.len() == prompts.saturating_add(1) && self.prompts.last() == Some(&prompt)
                && core::mem::discriminant(&ret) == kind.unwrap_or(core::mem::discriminant(&Read::End)))]
    fn read(
        &mut self,
        prompt: Prompt,
    ) -> Read
    {
        self.prompts.push(prompt);
        self.reads.pop().unwrap_or(Read::End)
    }
}

/// Under the terminal face an interrupt drops the waiting buffer, each
/// read is asked under the loop's prompt, and a buffer open at the end is
/// submitted.
#[test]
fn the_terminal_face_discards_on_interrupt_and_submits_at_the_end()
{
    let mut script = Script {
        reads: Vec::from([
            Read::Line("def c = (".to_owned()),
            Read::Line("def b = 2 ;".to_owned()),
            Read::Interrupted,
            Read::Line("def a = (".to_owned()),
        ]),
        prompts: Vec::new(),
    };
    let mut output = Vec::new();
    let ended = drive(
        &mut script,
        &mut output,
        RenderStyle::Plain,
        Spelling::Unicode,
    )
    .expect("the transcript is written");
    assert!(matches!(ended, Ended::Completed));
    assert_eq!(script.prompts, [
        Prompt::Fresh,
        Prompt::Continuing,
        Prompt::Fresh,
        Prompt::Fresh,
        Prompt::Continuing,
    ]);
    let transcript = String::from_utf8(output).expect("the transcript is UTF-8");
    let echoes: Vec<&str> = transcript
        .lines()
        .filter(|line| line.starts_with("▸ "))
        .collect();
    assert_eq!(echoes, ["▸ def b = 2 ;", "▸ def c = ("]);
}

/// A bounded writer recording observable progress and flushes.
#[derive(Default)]
struct Probe
{
    /// Bytes accepted before the configured refusal.
    bytes: Vec<u8>,
    /// Maximum accepted bytes.
    limit: usize,
    /// Whether flushing is refused.
    flush_error: bool,
    /// Number of write calls.
    writes: usize,
    /// Number of flush calls.
    flushes: usize,
}

impl std::io::Write for Probe
{
    /// Accept the available prefix or report a broken pipe.
    ///
    /// # Specification
    /// - requires: accepted bytes do not exceed the limit.
    /// - ensures: one recorded write, the exact accepted prefix, or a broken
    ///   pipe without progress when the limit has been reached.
    /// - provides: an observable partial-write boundary for the real face.
    /// - fails: broken pipe at the byte limit.
    /// - panics: none under the precondition.
    ///
    /// # Errors
    /// Broken pipe at the configured byte limit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty transcript performs no write; a refused
    ///   partial transcript preserves its prefix and skips the final flush.
    /// - witness: `tests::repl_loop::empty_transcripts_do_not_touch_the_writer`
    /// - witness: `tests::repl_loop::write_and_flush_failures_keep_their_kind`
    #[spec(requires: self.bytes.len() <= self.limit,
            captures: [bytes = self.bytes.len(), writes = self.writes],
            ensures: |ret| self.writes == writes.saturating_add(1) && match ret {
                Ok(count) => count == buf.len().min(self.limit.saturating_sub(bytes))
                    && self.bytes.len() == bytes.saturating_add(count)
                    && self.bytes.get(bytes..) == buf.get(..count),
                Err(ref error) => error.kind() == io::ErrorKind::BrokenPipe
                    && bytes == self.limit && self.bytes.len() == bytes,
            })]
    fn write(
        &mut self,
        buf: &[u8],
    ) -> std::io::Result<usize>
    {
        self.writes = self.writes.saturating_add(1);
        if self.bytes.len() == self.limit {
            return Err(io::ErrorKind::BrokenPipe.into());
        }
        let count = buf.len().min(self.limit.saturating_sub(self.bytes.len()));
        self.bytes
            .extend_from_slice(buf.get(.. count).expect("the accepted prefix fits"));
        Ok(count)
    }

    /// Record the flush and preserve its configured error kind.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly one recorded flush, succeeding unless refused.
    /// - provides: the observer for final-flush ordering and precedence.
    /// - fails: permission denied when flushing is configured to fail.
    /// - panics: none.
    ///
    /// # Errors
    /// Permission denied when flushing is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a flush failure overrides either a completed ending
    ///   or a reported input fault; terminal endings flush once.
    /// - witness: `tests::repl_loop::write_and_flush_failures_keep_their_kind`
    /// - witness: `tests::repl_loop::terminal_endings_stop_reads_and_flush_once`
    #[spec(captures: [flushes = self.flushes], ensures: |ret|
            self.flushes == flushes.saturating_add(1) && if self.flush_error {
                ret.as_ref().is_err_and(|error| error.kind() == io::ErrorKind::PermissionDenied)
            } else { ret.is_ok() })]
    fn flush(&mut self) -> std::io::Result<()>
    {
        self.flushes = self.flushes.saturating_add(1);
        if self.flush_error {
            Err(io::ErrorKind::PermissionDenied.into())
        }
        else {
            Ok(())
        }
    }
}

/// A block without rows never calls even a refusing writer or its flush.
#[test]
fn empty_transcripts_do_not_touch_the_writer()
{
    let block = TranscriptBlock {
        source: String::new(),
        source_hl: Vec::new(),
        lines: Vec::from([
            (OutKind::Goal, String::new()),
            (OutKind::Info, String::new()),
        ]),
    };
    let mut output = Probe {
        flush_error: true,
        ..Probe::default()
    };
    write_block(&mut output, &block).expect("no operation can fail");
    assert_eq!((output.writes, output.flushes), (0, 0));
    assert_eq!(output.bytes, [0_u8; 0]);
}

/// A partial write is not followed by a flush; flush errors take precedence
/// over both normal completion and an input fault.
#[test]
fn write_and_flush_failures_keep_their_kind()
{
    let mut output = Probe {
        limit: 5,
        ..Probe::default()
    };
    let error = run_batch(
        b"def n = 1 ;\n".as_slice(),
        &mut output,
        RenderStyle::Plain,
        Spelling::Unicode,
    )
    .expect_err("the transcript exceeds the writer's limit");
    assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
    assert_eq!(output.bytes, "▸ d".as_bytes());
    assert_eq!(output.flushes, 0);
    for input in [b"".as_slice(), b"\xff\n".as_slice()] {
        let mut output = Probe {
            limit: usize::MAX,
            flush_error: true,
            ..Probe::default()
        };
        let error = run_batch(input, &mut output, RenderStyle::Plain, Spelling::Unicode)
            .expect_err("flush is refused");
        assert_eq!(error.kind(), io::ErrorKind::PermissionDenied);
        assert_eq!(output.flushes, 1);
        assert_eq!(output.bytes, [0_u8; 0]);
    }
}

/// End and failed reads stop the driver before the next event, then flush.
#[test]
fn terminal_endings_stop_reads_and_flush_once()
{
    for ending in [
        Read::End,
        Read::Failed(Fault::Input(io::ErrorKind::InvalidData.into())),
    ] {
        let failed = matches!(ending, Read::Failed(_));
        let mut source = Script {
            reads: Vec::from([Read::Line("not consumed".to_owned()), ending]),
            prompts: Vec::new(),
        };
        let mut output = Probe {
            limit: usize::MAX,
            ..Probe::default()
        };
        let ended = drive(
            &mut source,
            &mut output,
            RenderStyle::Plain,
            Spelling::Unicode,
        )
        .expect("the writer succeeds");
        if failed {
            assert!(matches!(ended, Ended::Faulted(Fault::Input(ref error))
                    if error.kind() == io::ErrorKind::InvalidData));
        }
        else {
            assert!(matches!(ended, Ended::Completed));
        }
        assert!(matches!(source.reads.as_slice(), [Read::Line(text)] if text == "not consumed"));
        assert_eq!(source.prompts, [Prompt::Fresh]);
        assert_eq!(output.bytes, [0_u8; 0]);
        assert_eq!(output.flushes, 1);
    }
}

/// Unicode offsets, lone carriage returns and every output kind retain
/// their exact row boundaries and leads.
#[test]
fn row_kinds_and_unicode_boundaries_keep_their_meaning()
{
    let kinds = [
        (OutKind::Source, "▸ ", "  "),
        (OutKind::Type, "", ""),
        (OutKind::Value, "= ", "  "),
        (OutKind::Goal, "? ", "  "),
        (OutKind::Stuck, "· ", "  "),
        (OutKind::Blame, "! ", "  "),
        (OutKind::Diag, "", ""),
        (OutKind::Info, "· ", "  "),
    ];
    let block = TranscriptBlock {
        source: "é𐍈\r\n\nz\r".to_owned(),
        source_hl: Vec::new(),
        lines: kinds
            .iter()
            .map(|&(kind, ..)| (kind, "x\n\ny".to_owned()))
            .collect(),
    };
    let expected: Vec<_> = [
        (OutKind::Source, "▸ ", "é𐍈", 0_usize),
        (OutKind::Source, "", "", 8),
        (OutKind::Source, "  ", "z\r", 9),
    ]
    .into_iter()
    .chain(kinds.into_iter().flat_map(|(kind, mark, indent)| {
        [
            (kind, mark, "x", 0),
            (kind, "", "", 2),
            (kind, indent, "y", 3),
        ]
    }))
    .collect();
    let actual: Vec<_> = rows(&block)
        .map(|row| {
            (
                row.kind,
                <&str>::from(row.lead),
                row.text,
                usize::from(row.start),
            )
        })
        .collect();
    assert_eq!(actual, expected);
}

/// Pasted line breaks are preserved, blank fresh input is ignored, and
/// interrupting a pending buffer does not forget accepted declarations.
#[test]
fn multiline_and_interrupted_buffers_preserve_accepted_declarations()
{
    let mut repl = repl();
    let _kept = block(&mut repl, "def kept = 7 ;");
    assert_eq!(offer(&mut repl, "\u{2003}\r\n"), LoopEvent::Continue);
    assert_eq!(repl.prompt(), Prompt::Fresh);
    assert_eq!(offer(&mut repl, "def pasted = (\r\n"), LoopEvent::Continue);
    let pasted = block(&mut repl, "kept) ;");
    assert_eq!(pasted.source, "def pasted = (\r\n\nkept) ;");
    assert_eq!(pasted.lines, [
        (
            OutKind::Type,
            format!("pasted : {}", base(BaseType::Integer))
        ),
        (OutKind::Value, "7".to_owned())
    ]);
    assert_eq!(offer(&mut repl, "def abandoned = ("), LoopEvent::Continue);
    assert!(!matches!(offer(&mut repl, ":q"), LoopEvent::Quit));
    repl.discard();
    assert_eq!(repl.prompt(), Prompt::Fresh);
    assert_eq!(lines(&mut repl, "def abandoned = kept ;"), [
        (
            OutKind::Type,
            format!("abandoned : {}", base(BaseType::Integer))
        ),
        (OutKind::Value, "7".to_owned()),
    ]);
    assert_eq!(repl.finish(), Ok(Maybe::Absent(finished::Absent::Empty)));
}
