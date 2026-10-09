//! The renderer over the dispatcher's steps.
//!
//! Each case composes its source through the dispatcher — a walk over a
//! scratch tree, or the composition itself where a golden needs a fixed path —
//! and asserts the entries the step prints, their classes, their spans and
//! their rendered text.

/// The cases, in a `cfg(test)` module so the crate's lint wall reads them as
/// test code rather than as shipping code.
#[cfg(test)]
mod diagnostics
{
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_core_term::FailureClass;
    use gandr_surface_diagnostics::Class;
    use gandr_surface_diagnostics::Entry;
    use gandr_surface_diagnostics::RenderStyle;
    use gandr_surface_diagnostics::Rendered;
    use gandr_surface_diagnostics::Report;
    use gandr_surface_diagnostics::TerminalCapability;
    use gandr_surface_diagnostics::Unsettlement;
    use gandr_surface_diagnostics::entries;
    use gandr_surface_diagnostics::report_span;
    use gandr_surface_dispatcher::Composed;
    use gandr_surface_dispatcher::Goals;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_dispatcher::Standing;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::Verb;
    use gandr_surface_dispatcher::Walk;
    use gandr_surface_dispatcher::compose;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    /// A declaration whose definition synthesises a type its signature does
    /// not convert to.
    const MISMATCH: &str = r#"def wrong : Integer ;
def wrong = "text" ;
"#;

    /// The verbs, every one.
    const VERBS: [Verb; 3_usize] = [
        Verb::Check(Goals::Gated),
        Verb::Check(Goals::Reported),
        Verb::Test,
    ];

    /// A fresh scratch directory, removed when dropped.
    #[repr(transparent)]
    struct Scratch(PathBuf);

    impl Scratch
    {
        /// An empty directory named for `test` and this process.
        ///
        /// # Specification
        ///
        /// trivial.
        fn new(test: &Path) -> Self
        {
            let root = std::env::temp_dir().join(format!(
                "gandr-diagnostics-{}-{}",
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
        ///
        /// trivial.
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
        ///
        /// trivial.
        fn drop(&mut self)
        {
            let removed = std::fs::remove_dir_all(&self.0);
            assert!(removed.is_ok(), "the scratch directory is removed");
        }
    }

    /// `text` composed under `root` by the dispatcher's one composition.
    ///
    /// # Specification
    ///
    /// trivial.
    fn composed(
        root: SourceRoot,
        text: SourceText<'_>,
    ) -> Composed<'_>
    {
        let grammar = built_in().expect("the built-in grammar builds");
        compose(
            &grammar,
            root.corpus_root(),
            text,
            &mut LoweringCount::default(),
        )
        .expect("the source composes")
    }

    /// The step of a source at `path` under `root` whose text is `text`,
    /// standing unsettled.
    ///
    /// # Specification
    ///
    /// trivial.
    fn unsettled<'step>(
        path: &'step Path,
        root: SourceRoot,
        text: SourceText<'step>,
    ) -> Step<'step>
    {
        Step::Source {
            path,
            root,
            text,
            composed: composed(root, text),
            standing: Standing::Unsettled,
        }
    }

    /// The reports `step` prints under `verb`, in order.
    ///
    /// # Specification
    ///
    /// trivial.
    fn reports<'step>(
        step: &'step Step<'step>,
        verb: Verb,
    ) -> Vec<Report<'step>>
    {
        entries(step, verb)
            .map(|entry| match entry {
                | Entry::Report(report) => report,
                | Entry::Line(line) => panic!("a report, not the ledger line {line}"),
            })
            .collect()
    }

    /// The bytes of the first occurrence of `needle` in `text`.
    ///
    /// # Specification
    ///
    /// trivial.
    fn span_of(
        text: SourceText<'_>,
        needle: SourceText<'_>,
    ) -> ByteSpan
    {
        let start = text
            .as_ref()
            .find(needle.as_ref())
            .expect("the needle occurs");
        let end = start
            .checked_add(needle.as_ref().len())
            .expect("the end is representable");
        ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("the span is ordered")
    }

    /// `styled` with every ANSI escape sequence removed.
    ///
    /// # Specification
    ///
    /// trivial.
    fn unstyled(styled: &Rendered) -> String
    {
        let text: &str = styled.as_ref();
        let mut plain = String::with_capacity(text.len());
        let mut escaped = false;
        for character in text.chars() {
            match (escaped, character) {
                | (false, '\u{1b}') => escaped = true,
                | (false, _) => plain.push(character),
                | (true, 'm') => escaped = false,
                | (true, _) => {},
            }
        }
        plain
    }

    #[test]
    fn a_type_mismatch_renders_as_a_located_report()
    {
        let path = Path::new("mismatch.gandr");
        let text = SourceText::from(MISMATCH);
        let step = unsettled(path, SourceRoot::Strict, text);
        let reports = reports(&step, Verb::Check(Goals::Gated));
        assert_eq!(reports.len(), 1_usize, "one mismatch, one report");
        let report = reports[0];
        assert_eq!(
            report.class(),
            Class::Refusal(FailureClass::MalformedSource),
            "a type mismatch is malformed source"
        );
        assert_eq!(
            report.span(),
            Maybe::Present(span_of(text, SourceText::from(r#""text""#))),
            "the checker's refusal is located at the mismatched term through the origin table"
        );
        let rendered = report.render(RenderStyle::Plain).to_string();
        assert!(
            rendered.contains("mismatch.gandr:2:13"),
            "the report names its source at the term: {rendered}"
        );
        assert!(
            rendered.contains("the type it is checked against"),
            "the report marks the expected type: {rendered}"
        );
        assert_eq!(
            format!("{rendered}\n"),
            include_str!("golden/type-mismatch.txt"),
            "the terminal layout is a public surface"
        );
    }

    #[test]
    fn a_pathless_report_names_input_and_renders_causal_context()
    {
        let text = SourceText::from(MISMATCH);
        let step = unsettled(Path::new(""), SourceRoot::Strict, text);
        let reports = reports(&step, Verb::Check(Goals::Gated));
        assert_eq!(reports.len(), 1_usize, "one mismatch, one report");
        let rendered = reports[0].render(RenderStyle::Plain).to_string();
        assert!(
            rendered.contains("<input>:2:13"),
            "a source with no path is named `<input>`: {rendered}"
        );
        assert!(
            rendered.contains(
                "1 │ def wrong : Integer ;
  │             ─────── the type it is checked against
"
            ),
            "the signature the term is checked against stands as context: {rendered}"
        );
    }

    #[test]
    fn a_labeled_context_retains_its_locus_and_cause()
    {
        let text = SourceText::from(
            r"def a : Integer ;
def a : Integer ;
def a = 1 ;
",
        );
        let step = unsettled(Path::new("duplicate.gandr"), SourceRoot::Strict, text);
        let reports = reports(&step, Verb::Check(Goals::Gated));
        assert_eq!(reports.len(), 1_usize, "one duplicate, one report");
        let rendered = reports[0].render(RenderStyle::Plain).to_string();
        assert!(
            rendered.contains(
                "1 │ def a : Integer ;
  │ ───────────────── first written here
2 │ def a : Integer ;
  │ ━━━━━━━━━━━━━━━━━ malformed source
"
            ),
            "the first signature keeps its own line, columns and cause beside the primary: \
             {rendered}"
        );
    }

    #[test]
    fn render_style_follows_terminal_capability()
    {
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
        let text = SourceText::from(MISMATCH);
        let step = unsettled(Path::new("mismatch.gandr"), SourceRoot::Strict, text);
        let reports = reports(&step, Verb::Check(Goals::Gated));
        assert_eq!(reports.len(), 1_usize, "one mismatch, one report");
        let plain = reports[0].render(RenderStyle::Plain).to_string();
        let styled = reports[0].render(RenderStyle::Styled);
        assert!(
            !plain.contains('\u{1b}'),
            "plain rendering is escape-free: {plain}"
        );
        let escaped: &str = styled.as_ref();
        assert!(
            escaped.contains("\u{1b}["),
            "forced styling colours the report: {escaped:?}"
        );
        assert_eq!(
            unstyled(&styled),
            plain,
            "styling colours the same text the plain form writes"
        );
    }

    #[test]
    fn a_refused_declaration_renders_its_snippet()
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
        for verb in VERBS {
            let mut walk = Walk::new(vec![path.clone()]);
            let mut seen = Vec::new();
            while let Maybe::Present(step) = walk.step() {
                for report in reports(&step, verb) {
                    seen.push((
                        report.class(),
                        report.span(),
                        report.render(RenderStyle::Plain).to_string(),
                    ));
                }
            }
            let malformed = Class::Refusal(FailureClass::MalformedSource);
            let located = |needle: &str| Maybe::Present(span_of(text, SourceText::from(needle)));
            assert_eq!(
                seen.iter()
                    .map(|&(class, span, _)| (class, span))
                    .collect::<Vec<_>>(),
                vec![
                    (malformed, located("missing")),
                    (malformed, located(r#""text""#)),
                    (malformed, located("owes(1)")),
                ],
                "the lowering's, the checker's and the corpus root's refusals each report at their \
                 own span"
            );
            for ((line, column), seen) in [(2_usize, 14_usize), (4, 13), (5, 4)]
                .into_iter()
                .zip(&seen)
            {
                let rendered = &seen.2;
                assert!(
                    rendered.contains(&format!("╭▸ {}:{line}:{column}", path.display())),
                    "every refused declaration renders its snippet: {rendered}"
                );
            }
        }
    }

    #[test]
    fn an_unsettled_declaration_renders_as_its_golden()
    {
        let text = SourceText::from(
            r#"@[ refuses("UnresolvedName") ] def answer = 42 ;
"#,
        );
        let step = unsettled(Path::new("unsettled.gandr"), SourceRoot::Fixture, text);
        let reports = reports(&step, Verb::Check(Goals::Gated));
        assert_eq!(
            reports.len(),
            1_usize,
            "one unsettled declaration, one report"
        );
        assert_eq!(
            reports[0].class(),
            Class::Unsettled(Unsettlement::Unproduced),
            "the stated refusal was not produced"
        );
        assert_eq!(
            format!("{}\n", reports[0].render(RenderStyle::Plain)),
            include_str!("golden/unsettled.txt"),
            "the terminal layout is a public surface"
        );
    }

    #[test]
    fn a_goal_renders_as_its_golden()
    {
        let text = SourceText::from(
            r"def hole : Integer ;
",
        );
        let step = unsettled(Path::new("hole.gandr"), SourceRoot::Strict, text);
        let gated = reports(&step, Verb::Check(Goals::Gated));
        assert_eq!(
            gated.iter().map(Report::class).collect::<Vec<_>>(),
            vec![Class::Unsettled(Unsettlement::Obligations)],
            "under plain `check` the owed signature is unsettled"
        );
        let reported = reports(&step, Verb::Check(Goals::Reported));
        assert_eq!(
            reported.iter().map(Report::class).collect::<Vec<_>>(),
            vec![Class::Goal],
            "under `check --goals` it is a goal"
        );
        assert_eq!(
            format!("{}\n", reported[0].render(RenderStyle::Plain)),
            include_str!("golden/goal.txt"),
            "the terminal layout is a public surface"
        );
    }

    #[test]
    fn a_span_outside_the_text_is_unlocated()
    {
        let composed_text = SourceText::from(
            r"def answer = 42 ;
def broken = missing ;
",
        );
        let path = Path::new("broken.gandr");
        let step = Step::Source {
            path,
            root: SourceRoot::Strict,
            text: SourceText::from("def"),
            composed: composed(SourceRoot::Strict, composed_text),
            standing: Standing::Unsettled,
        };
        let reports = reports(&step, Verb::Check(Goals::Gated));
        assert_eq!(reports.len(), 1_usize, "one refusal, one report");
        assert_eq!(
            reports[0].span(),
            Maybe::Absent(report_span::Absent::OutsideText),
            "a span the text cannot answer is no locus"
        );
        let rendered = reports[0].render(RenderStyle::Plain).to_string();
        assert!(
            rendered.contains("broken.gandr") && !rendered.contains('│'),
            "an unlocated report names its path and quotes no line: {rendered}"
        );
    }

    #[test]
    fn each_verb_prints_its_entries()
    {
        let scratch = Scratch::new(Path::new("entries"));
        let sources = [
            ("fixture/hole.gandr", "def hole : Integer ;\n"),
            ("fixture/pending/lowered.gandr", "def a = 1 ;\n"),
            ("fixture/pending/whole.gandr", "ret 3\n"),
            (
                "fixture/settled.gandr",
                "@[ owes(1) ] def later : Integer ;\n",
            ),
            (
                "fixture/unproduced.gandr",
                "@[ refuses(\"UnresolvedName\") ] def answer = 42 ;\n",
            ),
            ("strict/whole.gandr", "ret 3\n"),
        ];
        for (relative, text) in sources {
            scratch.file(Path::new(relative), SourceText::from(text));
        }
        let base = format!("{}/", scratch.0.display());
        let printed = |verb: Verb| {
            let mut walk = Walk::new(vec![scratch.0.clone()]);
            let mut printed = Vec::new();
            while let Maybe::Present(step) = walk.step() {
                for entry in entries(&step, verb) {
                    printed.push(match entry {
                        | Entry::Report(report) => format!(
                            "{}: report: {}",
                            report
                                .path()
                                .strip_prefix(&scratch.0)
                                .expect("under the scratch directory")
                                .display(),
                            report.class()
                        ),
                        | Entry::Line(line) => line.to_string().replacen(&base, "", 1_usize),
                    });
                }
            }
            printed
        };
        let lowered = "fixture/pending/lowered.gandr: unsettled: a pending source whose every \
                       expectation can be stated; it belongs under the fixture root";
        let check = |hole: &str| {
            vec![
                format!("fixture/hole.gandr: report: {hole}"),
                lowered.to_owned(),
                "fixture/unproduced.gandr: report: unproduced refusal".to_owned(),
                "strict/whole.gandr: report: unrepresentable".to_owned(),
            ]
        };
        assert_eq!(
            printed(Verb::Check(Goals::Gated)),
            check("surviving obligations"),
            "check prints each unsettled declaration and source, never a ledger line of a \
             settled fixture or a pending refusal"
        );
        assert_eq!(
            printed(Verb::Check(Goals::Reported)),
            check("goal"),
            "check --goals prints an owed declaration as a goal"
        );
        assert_eq!(
            printed(Verb::Test),
            vec![
                "fixture/hole.gandr: report: surviving obligations".to_owned(),
                lowered.to_owned(),
                "fixture/pending/whole.gandr: pending: `ret_expression` at 0..5, read as a \
                 declaration, is not a former of this sort"
                    .to_owned(),
                "fixture/settled.gandr: settled `later` at 0..34: states checks owing 1; produced \
                 checks owing 1"
                    .to_owned(),
                "fixture/unproduced.gandr: report: unproduced refusal".to_owned(),
                "strict/whole.gandr: report: unrepresentable".to_owned(),
            ],
            "test adds the settled fixture and the pending refusal as ledger lines"
        );
    }
}
