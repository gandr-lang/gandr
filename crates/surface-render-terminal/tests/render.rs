//! The terminal renderer over the diagnostics of real compositions.
//!
//! Each case composes its source through the dispatcher — a walk over a
//! scratch tree, or the composition itself where a golden needs a fixed path —
//! takes the diagnostics its step yields, and compares their rendered text.
//!
//! The cases, in a `cfg(test)` module so the crate's lint wall reads them as
//! test code rather than as shipping code.

use core::convert::Infallible;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::TermNode;
use gandr_surface_corpus::Refusal;
use gandr_surface_diagnostics::Diagnostic;
use gandr_surface_diagnostics::Severity;
use gandr_surface_diagnostics::Subject;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_diagnostics::diagnose;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Standing;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::compose;
use gandr_surface_dispatcher::entries;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::OriginTable;
use gandr_surface_render_terminal::RenderStyle;
use gandr_surface_render_terminal::Rendered;
use gandr_surface_render_terminal::TerminalCapability;
use gandr_surface_render_terminal::render;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// A declaration whose definition synthesises a type its signature does
/// not convert to.
const MISMATCH: &str = r#"def wrong : Integer ;
def wrong = "text" ;
"#;

/// A force of an integer, inside a thunk.
const FORCE: &str = "def a : +U (-F Integer) ;\ndef a = thunk { become force 1 } ;\n";

/// An application whose head is a return, not a function.
const APPLICATION: &str = "def b : +U (-F Integer) ;\ndef b = thunk { become (pure 1)(2) } \
                               ;\n";

/// A mismatch under a `run` binder.
const BOUND: &str = "def id(x: Integer) -> -F Integer { return x }\ndef f(n: Integer) -> -F \
                         String { run m <- id(n) ; return m }\n";

/// A fresh scratch directory, removed when dropped.
#[repr(transparent)]
struct Scratch(PathBuf);

impl Scratch
{
    /// An empty directory named for `test` and this process.
    ///
    /// # Specification
    /// - requires: `test` is one file-name component, owned by this test.
    /// - ensures: the returned path is an empty directory.
    /// - provides: isolated storage for filesystem witnesses.
    /// - fails: never returns a failure.
    /// - panics: if an existing directory cannot be removed or creation fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh owned directory has no entries; a nested
    ///   source is then read back through a walk. Omitted creation and stale
    ///   entries change those observations; concurrent writers and I/O errors
    ///   are excluded.
    /// - witness: `tests::render::scratch_scope_removal_is_visible_to_a_new_walk`
    #[spec(
            requires: test.file_name() == Some(test.as_os_str()),
            ensures: |ref ret| std::fs::read_dir(&ret.0).is_ok_and(|mut entries| entries.next().is_none()),
        )]
    fn new(test: &Path) -> Self
    {
        let root = std::env::temp_dir().join(format!(
            "gandr-render-terminal-{}-{}",
            test.display(),
            std::process::id()
        ));
        if root.exists() {
            std::fs::remove_dir_all(&root).expect("a stale scratch directory is removed");
        }
        std::fs::create_dir_all(&root).expect("the scratch directory is created");
        Self(root)
    }

    /// Write `text` at `relative`, creating its directories, and return
    /// its path.
    ///
    /// # Specification
    /// - requires: `relative` names a file through normal or current-directory
    ///   components within this exclusively owned scratch directory.
    /// - ensures: returns a path under the scratch root containing `text`.
    /// - provides: a source for a real filesystem walk.
    /// - fails: never returns a failure.
    /// - panics: if the parent directories or the file cannot be written.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one nested source is read back through a real walk.
    ///   Exact bytes and subsequent cleanup expose wrong content or placement;
    ///   concurrent writes and filesystem failures are outside the domain.
    /// - witness: `tests::render::scratch_scope_removal_is_visible_to_a_new_walk`
    #[spec(
            requires: relative.file_name().is_some() && relative.components().all(|component| matches!(component,
                std::path::Component::Normal(_) | std::path::Component::CurDir)),
            ensures: |ref ret| ret.starts_with(&self.0) && std::fs::metadata(ret).is_ok_and(|metadata|
                metadata.is_file() && u64::try_from(text.as_ref().len()).is_ok_and(|length| metadata.len() == length)),
        )]
    fn file(
        &self,
        relative: &Path,
        text: SourceText<'_>,
    ) -> PathBuf
    {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().expect("a file has a parent"))
            .expect("the directories are created");
        std::fs::write(&path, text.as_ref()).expect("the file is written");
        path
    }
}

impl Drop for Scratch
{
    /// Remove the directory and everything under it.
    ///
    /// # Specification
    /// - requires: this test exclusively owns the scratch path.
    /// - ensures: the directory and its descendants no longer exist.
    /// - provides: cleanup at the end of the fixture scope.
    /// - fails: never returns a failure.
    /// - panics: if removal fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dropping a populated nested fixture leaves its root
    ///   absent and a new source walk reports a fault. Omitted or incomplete
    ///   removal changes the observation; concurrent recreation is excluded.
    /// - witness: `tests::render::scratch_scope_removal_is_visible_to_a_new_walk`
    #[spec(ensures: matches!(self.0.try_exists(), Ok(false)))]
    fn drop(&mut self)
    {
        let removed = std::fs::remove_dir_all(&self.0);
        assert!(removed.is_ok(), "the scratch directory is removed");
    }
}

/// The step of a source at `path` under `root` whose text is `text`,
/// standing unsettled.
///
/// # Specification
/// - requires: `text` composes within the built-in limits.
/// - ensures: returns an unsettled source step borrowing `path` and `text`
///   under the supplied root.
/// - provides: a source step for rendering observations.
/// - fails: never returns a failure.
/// - panics: if grammar construction or composition fails.
///
/// # Adequacy
/// - hypothesis: L3 — strict refusal and fixture expectation sources render
///   their own goldens at their own paths. Wrong root, standing or source
///   changes those observations; fault steps are excluded.
/// - witness: `tests::render::a_type_mismatch_renders_as_a_located_report`
/// - witness: `tests::render::each_causal_shape_renders_as_its_golden`
#[spec(ensures: |ref ret| matches!(*ret,
        Step::Source { path: held, root: actual, text: source, standing: Standing::Unsettled, .. }
            if core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(path)) && actual == root && core::ptr::eq(core::ptr::from_ref(source.as_ref()), core::ptr::from_ref(text.as_ref()))
    ))]
fn unsettled<'step>(
    path: &'step Path,
    root: SourceRoot,
    text: SourceText<'step>,
) -> Step<'step>
{
    let grammar = built_in().expect("the built-in grammar builds");
    Step::Source {
        path,
        root,
        text,
        base: gandr_surface_syntax::ByteOffset::from(0_usize),
        composed: compose(
            &grammar,
            root.corpus_root(),
            text,
            &mut LoweringCount::default(),
        )
        .expect("the source composes"),
        standing: Standing::Unsettled,
    }
}

/// The one diagnostic a strict source at `path` with `text` prints under
/// `verb`.
///
/// # Specification
/// - requires: the source prints exactly one diagnostic.
/// - ensures: that diagnostic.
/// - provides: the subject of a golden.
/// - fails: never returns a failure.
/// - panics: if the source prints another number of diagnostics.
///
/// # Adequacy
/// - hypothesis: L3 — every golden source prints one diagnostic; a source
///   printing two fails loudly rather than comparing the wrong one.
/// - witness: `tests::render::each_causal_shape_renders_as_its_golden`
#[spec(ensures: |ref ret| ret.path.as_path() == path)]
fn only(
    path: &Path,
    root: SourceRoot,
    text: SourceText<'_>,
    verb: Verb,
) -> Diagnostic
{
    let step = unsettled(path, root, text);
    let mut printed: Vec<Diagnostic> = entries(&step, verb).collect();
    assert_eq!(printed.len(), 1_usize, "one diagnostic: {printed:?}");
    printed.remove(0)
}

/// `diagnostic` in plain text at `verbosity`, closed with the line ending
/// a golden file ends with.
///
/// # Specification
/// trivial.
fn plain(
    diagnostic: &Diagnostic,
    verbosity: Verbosity,
) -> String
{
    format!("{}\n", render(diagnostic, RenderStyle::Plain, verbosity))
}

/// Remove complete SGR styling from the backend's escape-free input.
///
/// # Specification
/// - requires: every escape starts a complete backend SGR sequence ending in
///   `m`; the source content contains no literal escapes.
/// - ensures: removes those controls while preserving the other characters.
/// - provides: a plain-text observer for forced styling.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a mismatch with primary and causal annotations renders to
///   identical plain text after SGR removal. Dropped glyphs or retained
///   controls change equality; other terminal controls and literal source
///   escapes are excluded.
/// - witness: `tests::render::forced_styling_colors_actual_facade_annotations`
#[spec(ensures: |ref ret| ret.len() <= styled.as_ref().len() && !ret.contains('\u{1b}'))]
fn unstyled(styled: &Rendered) -> String
{
    let text: &str = styled.as_ref();
    let mut plain = String::with_capacity(text.len());
    let mut escaped = false;
    for character in text.chars() {
        match (escaped, character) {
            (false, '\u{1b}') => escaped = true,
            (false, _) => plain.push(character),
            (true, 'm') => escaped = false,
            (true, _) => {},
        }
    }
    plain
}

/// The force refusal, its origin table cut down to the node it refuses:
/// every rule it stood inside then names a node the table records nothing
/// for, as a node the checker minted does.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the refusal's diagnostic, located at its primary node, with every
///   context unlocated.
/// - provides: the subject of the unlocated-rule golden.
/// - fails: never returns a failure.
/// - panics: if the force source does not refuse with a shape mismatch.
///
/// # Adequacy
/// - hypothesis: L3 — the force refusal keeps its primary locus while its two
///   rules lose theirs.
/// - witness: `tests::render::each_causal_shape_renders_as_its_golden`
#[spec(ensures: |ref ret| matches!(ret.span, Maybe::Present(_)))]
fn unlocated_rules() -> Diagnostic
{
    let text = SourceText::from(FORCE);
    let step = unsettled(Path::new("force.gandr"), SourceRoot::Strict, text);
    let Step::Source {
        path,
        composed:
            Composed::Settled {
                ref report,
                ref origins,
                ref spellings,
                ref failures,
                ..
            },
        ..
    } = step
    else {
        panic!("the force source settles");
    };
    let declaration = report
        .declarations()
        .iter()
        .find(|declaration| matches!(declaration.produced().refusal(), Maybe::Present(_)))
        .expect("one declaration refuses");
    let Maybe::Present(refusal @ Refusal::Checking(CheckRefusal::ShapeMismatch { at, .. })) =
        declaration.produced().refusal()
    else {
        panic!("the force refuses its operand's shape");
    };
    let TermNode::Value(value) = at
    else {
        panic!("the operand is a value");
    };
    let mut primary = OriginTable::new();
    let Maybe::Present(origin) = origins.value(value)
    else {
        panic!("the operand is recorded");
    };
    primary.record_value(value, origin);
    diagnose(path, text, Subject::Refused {
        declaration,
        refusal,
        origins: &primary,
        spellings: spellings.spelled(gandr_surface_grammar::Spelling::Unicode),
        failure: failures.get(declaration.constant()),
        upstream: Maybe::Absent(gandr_surface_diagnostics::upstream::Absent::Own),
    })
}

#[test]
fn a_type_mismatch_renders_as_a_located_report()
{
    let diagnostic = only(
        Path::new("mismatch.gandr"),
        SourceRoot::Strict,
        SourceText::from(MISMATCH),
        Verb::Check(Goals::Gated),
    );
    let rendered = plain(&diagnostic, Verbosity::User);
    assert!(
        rendered.contains("mismatch.gandr:2:13"),
        "the diagnostic names its source at the term: {rendered}"
    );
    assert_eq!(
        rendered,
        include_str!("golden/type-mismatch.txt"),
        "the terminal layout is a public surface"
    );
}

#[test]
fn each_causal_shape_renders_as_its_golden()
{
    let check = Verb::Check(Goals::Gated);
    for (diagnostic, golden) in [
        (
            only(
                Path::new("force.gandr"),
                SourceRoot::Strict,
                SourceText::from(FORCE),
                check,
            ),
            include_str!("golden/nested-force.txt"),
        ),
        (
            only(
                Path::new("application.gandr"),
                SourceRoot::Strict,
                SourceText::from(APPLICATION),
                check,
            ),
            include_str!("golden/nested-application.txt"),
        ),
        (
            only(
                Path::new("bound.gandr"),
                SourceRoot::Strict,
                SourceText::from(BOUND),
                check,
            ),
            include_str!("golden/run-binder.txt"),
        ),
        (unlocated_rules(), include_str!("golden/unlocated-rule.txt")),
    ] {
        assert_eq!(
            plain(&diagnostic, Verbosity::User),
            golden,
            "each context reads as its judgement, its rule's sentence and its binders"
        );
    }
}

#[test]
fn an_unended_form_renders_what_is_missing_where()
{
    let check = Verb::Check(Goals::Gated);
    for (path, source, golden) in [
        (
            "semicolon.gandr",
            "def a : Integer ;\ndef a = 1\ndef b : Integer ;\ndef b = 2 ;\n",
            include_str!("golden/missing-semicolon.txt"),
        ),
        (
            "string.gandr",
            "def s : String ;\ndef s = \"abc ;\n",
            include_str!("golden/unclosed-string.txt"),
        ),
    ] {
        let step = unsettled(
            Path::new(path),
            SourceRoot::Strict,
            SourceText::from(source),
        );
        let rendered: String = entries(&step, check)
            .map(|diagnostic| plain(&diagnostic, Verbosity::User))
            .collect();
        assert_eq!(
            rendered, golden,
            "the message names the missing tile; the mark sits where it belongs"
        );
    }
}

#[test]
fn one_refusal_renders_at_every_verbosity()
{
    let diagnostic = only(
        Path::new("force.gandr"),
        SourceRoot::Strict,
        SourceText::from(FORCE),
        Verb::Check(Goals::Gated),
    );
    for (verbosity, golden) in [
        (Verbosity::User, include_str!("golden/nested-force.txt")),
        (
            Verbosity::Detailed,
            include_str!("golden/verbosity-detailed.txt"),
        ),
        (Verbosity::Debug, include_str!("golden/verbosity-debug.txt")),
        (Verbosity::Json, include_str!("golden/verbosity-json.txt")),
    ] {
        assert_eq!(
            plain(&diagnostic, verbosity),
            golden,
            "each level's layout is a public surface: {verbosity:?}"
        );
    }
    let styled = render(&diagnostic, RenderStyle::Styled, Verbosity::Json);
    assert_eq!(
        styled.as_ref(),
        diagnostic.json(),
        "the JSON image ignores the style"
    );
}

#[test]
fn the_other_kinds_render_as_their_goldens()
{
    for (diagnostic, golden) in [
        (
            only(
                Path::new("shadow.gandr"),
                SourceRoot::Strict,
                SourceText::from("def add : Integer ;\ndef add = 1 ;\n"),
                Verb::Check(Goals::Gated),
            ),
            include_str!("golden/shadowed-builtin.txt"),
        ),
        (
            only(
                Path::new("unsettled.gandr"),
                SourceRoot::Fixture,
                SourceText::from("@[ refuses(\"UnresolvedName\") ] def answer = 42 ;\n"),
                Verb::Check(Goals::Gated),
            ),
            include_str!("golden/unsettled.txt"),
        ),
        (
            only(
                Path::new("hole.gandr"),
                SourceRoot::Strict,
                SourceText::from("def hole : Integer ;\n"),
                Verb::Check(Goals::Reported),
            ),
            include_str!("golden/goal.txt"),
        ),
        (
            only(
                Path::new("exits.gandr"),
                SourceRoot::Strict,
                SourceText::from("@[ explicit_exits ]\ndef kept(n: Integer) -> -F Integer { n }\n"),
                Verb::Check(Goals::Gated),
            ),
            include_str!("golden/explicit-exits.txt"),
        ),
    ] {
        assert_eq!(
            plain(&diagnostic, Verbosity::User),
            golden,
            "the terminal layout is a public surface"
        );
    }
}

#[test]
fn a_pathless_diagnostic_names_input()
{
    let diagnostic = only(
        Path::new(""),
        SourceRoot::Strict,
        SourceText::from(MISMATCH),
        Verb::Check(Goals::Gated),
    );
    let rendered = plain(&diagnostic, Verbosity::User);
    assert!(
        rendered.contains("<input>:2:13"),
        "a source with no path is named `<input>`: {rendered}"
    );
    assert!(
        rendered.contains("1 │ def wrong : Integer ;\n  │             ───────"),
        "the signature the term is checked against stands as context: {rendered}"
    );
}

#[test]
fn a_labeled_context_renders_under_its_bytes()
{
    let diagnostic = only(
        Path::new("duplicate.gandr"),
        SourceRoot::Strict,
        SourceText::from("def a : Integer ;\ndef a : Integer ;\ndef a = 1 ;\n"),
        Verb::Check(Goals::Gated),
    );
    let rendered = plain(&diagnostic, Verbosity::User);
    assert!(
        rendered.contains("1 │ def a : Integer ;\n  │ ─────────────────"),
        "the first signature remains secondary context: {rendered}"
    );
    assert!(
        rendered.contains("2 │ def a : Integer ;\n  │ ━━━━━━━━━━━━━━━━━"),
        "the duplicate retains its primary locus: {rendered}"
    );
}

#[test]
fn an_unlocated_diagnostic_names_its_path_and_quotes_no_line()
{
    let composed_text = SourceText::from("def answer = 42 ;\ndef broken = missing ;\n");
    let grammar = built_in().expect("the grammar builds");
    let step = Step::Source {
        path: Path::new("broken.gandr"),
        root: SourceRoot::Strict,
        text: SourceText::from("def"),
        base: gandr_surface_syntax::ByteOffset::from(0_usize),
        composed: compose(
            &grammar,
            SourceRoot::Strict.corpus_root(),
            composed_text,
            &mut LoweringCount::default(),
        )
        .expect("the source composes"),
        standing: Standing::Unsettled,
    };
    let printed: Vec<Diagnostic> = entries(&step, Verb::Check(Goals::Gated)).collect();
    assert_eq!(printed.len(), 1_usize, "one refusal, one diagnostic");
    let rendered = plain(&printed[0], Verbosity::User);
    assert!(
        rendered.contains("broken.gandr") && !rendered.contains('│'),
        "an unlocated diagnostic names its path and quotes no line: {rendered}"
    );
}

#[test]
fn render_style_follows_terminal_capability()
{
    assert_eq!(
        TerminalCapability::from(false),
        TerminalCapability::NonTerminal
    );
    assert_eq!(TerminalCapability::from(true), TerminalCapability::Terminal);
    assert_eq!(
        RenderStyle::for_terminal(TerminalCapability::from(false)),
        RenderStyle::Plain,
        "a pipe or a file is plain"
    );
    assert_eq!(
        RenderStyle::for_terminal(TerminalCapability::from(true)),
        RenderStyle::Styled,
        "a terminal is styled"
    );
}

#[test]
fn forced_styling_colors_actual_facade_annotations()
{
    let diagnostic = only(
        Path::new("mismatch.gandr"),
        SourceRoot::Strict,
        SourceText::from(MISMATCH),
        Verb::Check(Goals::Gated),
    );
    let plain = render(&diagnostic, RenderStyle::Plain, Verbosity::User).to_string();
    let styled = render(&diagnostic, RenderStyle::Styled, Verbosity::User);
    assert!(
        !plain.contains('\u{1b}'),
        "plain rendering is escape-free: {plain}"
    );
    let escaped: &str = styled.as_ref();
    assert!(
        escaped.contains("\u{1b}["),
        "forced styling colours the diagnostic: {escaped:?}"
    );
    assert_eq!(
        unstyled(&styled),
        plain,
        "styling colours the same text the plain form writes"
    );
}

#[test]
fn a_walk_renders_each_refused_declaration_at_its_line()
{
    let scratch = Scratch::new(Path::new("refused"));
    let text = SourceText::from(
        r#"def answer = 42 ;
def broken = missing ;
def wrong : Integer ;
def wrong = "text" ;
@[ owes(1) ] def later : Integer ;
"#,
    );
    let path = scratch.file(Path::new("refused.gandr"), text);
    for verb in [
        Verb::Check(Goals::Gated),
        Verb::Check(Goals::Reported),
        Verb::Test,
    ] {
        let mut rendered = Vec::new();
        let ControlFlow::Continue(_report) =
            Walk::new(vec![path.clone()]).visit(Width::SERIAL, |step| -> ControlFlow<Infallible> {
                rendered.extend(
                    entries(&step, verb).map(|diagnostic| plain(&diagnostic, Verbosity::User)),
                );
                ControlFlow::Continue(())
            });
        assert_eq!(rendered.len(), 3_usize, "three refusals: {rendered:?}");
        for ((line, column), rendered) in [(2_usize, 14_usize), (4, 13), (5, 4)]
            .into_iter()
            .zip(&rendered)
        {
            assert!(
                rendered.contains(&format!("╭▸ {}:{line}:{column}", path.display())),
                "every refused declaration renders its snippet: {rendered}"
            );
        }
    }
}

#[test]
fn a_ledger_line_prints_as_itself()
{
    let scratch = Scratch::new(Path::new("ledger"));
    let path = scratch.file(
        Path::new("fixture/settled.gandr"),
        SourceText::from("@[ owes(1) ] def later : Integer ;\n"),
    );
    let mut lines = Vec::new();
    let ControlFlow::Continue(_report) = Walk::new(vec![scratch.0.clone()]).visit(
        Width::SERIAL,
        |step| -> ControlFlow<Infallible> {
            lines.extend(entries(&step, Verb::Test));
            ControlFlow::Continue(())
        },
    );
    let [ref line] = *lines.as_slice()
    else {
        panic!("one settled fixture, one line: {lines:?}");
    };
    assert_eq!(line.severity, Severity::Ledger);
    let rendered = render(line, RenderStyle::Styled, Verbosity::User).to_string();
    assert_eq!(
        rendered,
        format!("{}: {}", path.display(), line.message.text),
        "a ledger line is its path and its text, unstyled, with no terminator"
    );
    let image: serde_json::Value =
        serde_json::from_str(render(line, RenderStyle::Plain, Verbosity::Json).as_ref())
            .expect("a ledger line's JSON image parses");
    assert_eq!(
        image,
        serde_json::json!({
            "level": "line",
            "path": path.display().to_string(),
            "line": rendered,
        }),
        "the JSON image carries the path and the line"
    );
}

#[test]
fn scratch_scope_removal_is_visible_to_a_new_walk()
{
    let scratch = Scratch::new(Path::new("scope-removal"));
    assert!(
        std::fs::read_dir(&scratch.0)
            .expect("scratch is readable")
            .next()
            .is_none()
    );
    let text = SourceText::from("def answer = 17 ;\n");
    let path = scratch.file(Path::new("strict/nested/source.gandr"), text);
    let mut observed = Vec::new();
    let ControlFlow::Continue(_report) =
        Walk::new(vec![path.clone()]).visit(Width::SERIAL, |step| -> ControlFlow<Infallible> {
            if let Step::Source { text, .. } = step {
                observed.push(<&str>::from(text).to_owned());
            }
            ControlFlow::Continue(())
        });
    assert_eq!(
        observed,
        [<&str>::from(text).to_owned()],
        "the written source is read once"
    );
    let root = scratch.0.clone();
    drop(scratch);
    assert!(matches!(root.try_exists(), Ok(false)));
    let missing = Walk::new(vec![path]).visit(Width::SERIAL, |step| {
        ControlFlow::Break(matches!(step, Step::Fault { .. }))
    });
    assert_eq!(
        missing,
        ControlFlow::Break(true),
        "the removed source faults"
    );
}
