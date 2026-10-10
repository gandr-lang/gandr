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

    use anodized::spec;
    use gandr_core_term::FailureClass;
    use gandr_surface_diagnostics::Annotation;
    use gandr_surface_diagnostics::Class;
    use gandr_surface_diagnostics::Entry;
    use gandr_surface_diagnostics::Label;
    use gandr_surface_diagnostics::RenderStyle;
    use gandr_surface_diagnostics::Rendered;
    use gandr_surface_diagnostics::Report;
    use gandr_surface_diagnostics::TerminalCapability;
    use gandr_surface_diagnostics::Unsettlement;
    use gandr_surface_diagnostics::entries;
    use gandr_surface_diagnostics::report_context;
    use gandr_surface_diagnostics::report_identifier;
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
        /// - requires: `test` is one file-name component, owned by this test.
        /// - ensures: the returned path is an empty directory.
        /// - provides: isolated storage for filesystem witnesses.
        /// - fails: never returns a failure.
        /// - panics: if an existing directory cannot be removed or creation
        ///   fails.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a fresh owned directory has no entries; a nested
        ///   source is then read back through a walk. Omitted creation and
        ///   stale entries change those observations; concurrent writers and
        ///   I/O errors are excluded.
        /// - witness: `diagnostics::diagnostics::scratch_scope_removal_is_visible_to_a_new_walk`
        #[spec(
            requires: test.file_name() == Some(test.as_os_str()),
            ensures: |ref ret| std::fs::read_dir(&ret.0).is_ok_and(|mut entries| entries.next().is_none()),
        )]
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
        /// - requires: `relative` names a file through normal or
        ///   current-directory components within this exclusively owned scratch
        ///   directory.
        /// - ensures: returns a path under the scratch root containing `text`.
        /// - provides: a source for a real filesystem walk.
        /// - fails: never returns a failure.
        /// - panics: if the parent directories or the file cannot be written.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — one nested source is read back through a real
        ///   walk. Exact bytes and subsequent cleanup expose wrong content or
        ///   placement; concurrent writes and filesystem failures are outside
        ///   the domain.
        /// - witness: `diagnostics::diagnostics::scratch_scope_removal_is_visible_to_a_new_walk`
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
        /// - hypothesis: L3 — dropping a populated nested fixture leaves its
        ///   root absent and a new source walk reports a fault. Omitted or
        ///   incomplete removal changes the observation; concurrent recreation
        ///   is excluded.
        /// - witness: `diagnostics::diagnostics::scratch_scope_removal_is_visible_to_a_new_walk`
        #[spec(ensures: matches!(self.0.try_exists(), Ok(false)))]
        fn drop(&mut self)
        {
            let removed = std::fs::remove_dir_all(&self.0);
            assert!(removed.is_ok(), "the scratch directory is removed");
        }
    }

    /// `text` composed under `root` by the dispatcher's one composition.
    ///
    /// # Specification
    /// - requires: the source fits the built-in grammar and composition limits.
    /// - ensures: every settled declaration span lies within `text`.
    /// - provides: the dispatcher composition used by rendering witnesses.
    /// - fails: never returns a failure.
    /// - panics: if grammar construction or composition fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mismatch, duplicate-signature and goal sources retain
    ///   their expected spans and classes in the resulting reports.
    ///   Wrong-source composition or shifted spans change those observations;
    ///   run limits and grammar-construction failure are excluded.
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    /// - witness: `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`
    /// - witness: `diagnostics::diagnostics::a_goal_renders_as_its_golden`
    #[spec(ensures: |ref ret| match *ret {
        Composed::Settled { ref report, .. } => report.declarations().iter().all(|declaration| text.fragment(declaration.span()).is_ok()),
        Composed::Refused(_) => true,
    })]
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
    /// - requires: `text` composes within the built-in limits.
    /// - ensures: returns an unsettled source step borrowing `path` and `text`
    ///   under the supplied root.
    /// - provides: a source step for report observations.
    /// - fails: never returns a failure.
    /// - panics: if grammar construction or composition fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — strict mismatch and fixture expectation sources
    ///   produce different refusal and unsettlement reports at their own paths
    ///   and spans. Wrong root, standing or source changes those observations;
    ///   fault steps and composition failure are excluded.
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    /// - witness: `diagnostics::diagnostics::an_unsettled_declaration_renders_as_its_golden`
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
    /// - requires: every visible entry for this source and verb is a report.
    /// - ensures: preserves report order and each report borrows the step path.
    /// - provides: collected reports for semantic and rendering assertions.
    /// - fails: never returns a failure.
    /// - panics: if an entry is a ledger line.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three distinct refusals retain source order and exact
    ///   locations under each verb. Reordering, dropping or misrouting reports
    ///   changes the sequence; mixed ledger streams are excluded.
    /// - witness: `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`
    #[spec(ensures: |ref ret| ret.iter().all(|report| match *step {
        Step::Source { path, .. } | Step::Fault { path, .. } => core::ptr::eq(core::ptr::from_ref(report.path()), core::ptr::from_ref(path)),
    }))]
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
    /// - requires: `needle` occurs in `text`.
    /// - ensures: returns the span of its first occurrence.
    /// - provides: an independent expected source locus.
    /// - fails: never returns a failure.
    /// - panics: if the needle is absent or the end is not representable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unique ASCII needles in mismatch and refusal sources
    ///   are checked against produced spans and rendered line/column locations.
    ///   Shifted bounds or wrong needles change the observation; empty needles
    ///   and repeated occurrences are outside the witnesses.
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`
    /// - witness: `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`
    #[spec(ensures: |ret| text.fragment(ret).is_ok_and(|fragment| fragment.as_ref() == needle.as_ref()))]
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

    /// Remove complete SGR styling from the backend's escape-free input.
    ///
    /// # Specification
    /// - requires: every escape starts a complete backend SGR sequence ending
    ///   in `m`; the source content contains no literal escapes.
    /// - ensures: removes those controls while preserving the other characters.
    /// - provides: a plain-text observer for forced styling.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mismatch with primary and causal annotations
    ///   renders to identical plain text after SGR removal. Dropped glyphs or
    ///   retained controls change equality; other terminal controls and literal
    ///   source escapes are excluded.
    /// - witness: `diagnostics::diagnostics::forced_styling_colors_actual_facade_annotations`
    #[spec(ensures: |ref ret| ret.len() <= styled.as_ref().len() && !ret.contains('\u{1b}'))]
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
            rendered.contains("1 │ def wrong : Integer ;\n  │             ───────"),
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
  │ ─────────────────"
            ),
            "the first signature remains secondary context: {rendered}"
        );
        assert!(
            rendered.contains(
                "2 │ def a : Integer ;
  │ ━━━━━━━━━━━━━━━━━"
            ),
            "the duplicate retains its primary locus: {rendered}"
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
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        enum Observed
        {
            Report(Class),
            Ledger,
        }
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
        let printed = |verb: Verb| {
            let mut walk = Walk::new(vec![scratch.0.clone()]);
            let mut printed = Vec::new();
            while let Maybe::Present(step) = walk.step() {
                let path = match step {
                    | Step::Source { path, .. } | Step::Fault { path, .. } => path,
                };
                for entry in entries(&step, verb) {
                    let observation = match entry {
                        | Entry::Report(report) => Observed::Report(report.class()),
                        | Entry::Line(line) => {
                            let rendered = line.to_string();
                            let prefix = format!("{}: ", path.display());
                            let payload = rendered
                                .strip_prefix(&prefix)
                                .expect("the ledger names its source");
                            assert!(!rendered.ends_with('\n'), "the ledger adds no terminator");
                            if path.ends_with("fixture/pending/whole.gandr") {
                                assert!(payload.contains("ret_expression"));
                                assert!(
                                    payload
                                        .split(|character: char| !character.is_ascii_digit())
                                        .filter_map(|digits| digits.parse::<usize>().ok())
                                        .eq([0_usize, 5_usize])
                                );
                            }
                            if path.ends_with("fixture/settled.gandr") {
                                assert!(payload.contains("later"));
                                assert!(
                                    payload
                                        .split(|character: char| !character.is_ascii_digit())
                                        .filter_map(|digits| digits.parse::<usize>().ok())
                                        .eq([0_usize, 34_usize, 1_usize, 1_usize])
                                );
                            }
                            Observed::Ledger
                        },
                    };
                    printed.push((
                        path.strip_prefix(&scratch.0)
                            .expect("within scratch")
                            .to_path_buf(),
                        observation,
                    ));
                }
            }
            printed
        };
        let check = |hole| {
            vec![
                (PathBuf::from("fixture/hole.gandr"), Observed::Report(hole)),
                (
                    PathBuf::from("fixture/pending/lowered.gandr"),
                    Observed::Ledger,
                ),
                (
                    PathBuf::from("fixture/unproduced.gandr"),
                    Observed::Report(Class::Unsettled(Unsettlement::Unproduced)),
                ),
                (
                    PathBuf::from("strict/whole.gandr"),
                    Observed::Report(Class::Refusal(FailureClass::Unrepresentable)),
                ),
            ]
        };
        assert_eq!(
            printed(Verb::Check(Goals::Gated)),
            check(Class::Unsettled(Unsettlement::Obligations))
        );
        assert_eq!(printed(Verb::Check(Goals::Reported)), check(Class::Goal));
        assert_eq!(printed(Verb::Test), vec![
            (
                PathBuf::from("fixture/hole.gandr"),
                Observed::Report(Class::Unsettled(Unsettlement::Obligations))
            ),
            (
                PathBuf::from("fixture/pending/lowered.gandr"),
                Observed::Ledger
            ),
            (
                PathBuf::from("fixture/pending/whole.gandr"),
                Observed::Ledger
            ),
            (PathBuf::from("fixture/settled.gandr"), Observed::Ledger),
            (
                PathBuf::from("fixture/unproduced.gandr"),
                Observed::Report(Class::Unsettled(Unsettlement::Unproduced))
            ),
            (
                PathBuf::from("strict/whole.gandr"),
                Observed::Report(Class::Refusal(FailureClass::Unrepresentable))
            ),
        ]);
    }

    #[test]
    fn a_report_preserves_refusal_identity_and_title_payloads()
    {
        let cases = [
            (
                MISMATCH,
                Verb::Check(Goals::Gated),
                Maybe::Present("TypeMismatch"),
                &[][..],
                &[][..],
            ),
            (
                "def broken = missing ;
",
                Verb::Check(Goals::Gated),
                Maybe::Present("UnresolvedName"),
                &[13_usize, 20_usize][..],
                &["missing"][..],
            ),
            (
                "@[ owes(0) ] def hole : Integer ;
",
                Verb::Check(Goals::Reported),
                Maybe::Absent(report_identifier::Absent::Statement),
                &[0_usize, 1_usize][..],
                &["hole"][..],
            ),
        ];
        for (source, verb, identifier, numbers, names) in cases {
            let step = unsettled(
                Path::new("named.gandr"),
                SourceRoot::Fixture,
                SourceText::from(source),
            );
            let reports = reports(&step, verb);
            assert_eq!(reports.len(), 1_usize);
            let report = reports[0];
            let named = match report.identifier() {
                | Maybe::Present(spelling) => Maybe::Present(spelling.to_string()),
                | Maybe::Absent(reason) => Maybe::Absent(reason),
            };
            let expected = match identifier {
                | Maybe::Present(spelling) => Maybe::Present(spelling.to_owned()),
                | Maybe::Absent(reason) => Maybe::Absent(reason),
            };
            assert_eq!(named, expected, "stable refusal identity for {source:?}");
            let title = report.title().to_string();
            for name in names {
                assert!(title.contains(name), "source name in {title}");
            }
            assert!(
                title
                    .split(|character: char| !character.is_ascii_digit())
                    .filter_map(|digits| digits.parse::<usize>().ok())
                    .eq(numbers.iter().copied()),
                "title preserves semantic numeric roles without core addresses: {title}"
            );
        }
    }

    #[test]
    fn a_report_exposes_the_context_it_marks()
    {
        let mismatch = SourceText::from(MISMATCH);
        let step = unsettled(Path::new("mismatch.gandr"), SourceRoot::Strict, mismatch);
        let found = reports(&step, Verb::Check(Goals::Gated));
        assert_eq!(found.len(), 1_usize, "one mismatch, one report");
        assert_eq!(
            found[0].context(),
            [
                Maybe::Present(Annotation {
                    span: span_of(mismatch, SourceText::from("Integer")),
                    label: Label::Expected,
                }),
                Maybe::Absent(report_context::Absent::Unrecorded),
            ],
            "the signature stands as the expected type; the synthesised type has no origin"
        );

        let duplicate = SourceText::from(
            r"def a : Integer ;
def a : Integer ;
def a = 1 ;
",
        );
        let step = unsettled(Path::new("duplicate.gandr"), SourceRoot::Strict, duplicate);
        let found = reports(&step, Verb::Check(Goals::Gated));
        assert_eq!(found.len(), 1_usize, "one duplicate, one report");
        assert_eq!(
            found[0].context(),
            [
                Maybe::Present(Annotation {
                    span: ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(17_usize))
                        .expect("the first signature's span is ordered"),
                    label: Label::First,
                }),
                Maybe::Absent(report_context::Absent::Unnamed),
            ],
            "the first signature is the duplicate's one context locus"
        );

        let hole = SourceText::from("def hole : Integer ;\n");
        let step = unsettled(Path::new("hole.gandr"), SourceRoot::Strict, hole);
        let found = reports(&step, Verb::Check(Goals::Reported));
        assert_eq!(found.len(), 1_usize, "one goal, one report");
        assert_eq!(
            found[0].context(),
            [
                Maybe::Absent(report_context::Absent::Unnamed),
                Maybe::Absent(report_context::Absent::Unnamed),
            ],
            "a goal names no context"
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
        let text = SourceText::from(
            "def answer = 17 ;
",
        );
        let path = scratch.file(Path::new("strict/nested/source.gandr"), text);
        {
            let mut walk = Walk::new(vec![path.clone()]);
            let Maybe::Present(Step::Source { text: observed, .. }) = walk.step()
            else {
                panic!("the written source is readable");
            };
            assert_eq!(observed, text);
            assert!(matches!(walk.step(), Maybe::Absent(_)));
        }
        let root = scratch.0.clone();
        drop(scratch);
        assert!(matches!(root.try_exists(), Ok(false)));
        let mut missing = Walk::new(vec![path]);
        assert!(matches!(missing.step(), Maybe::Present(Step::Fault { .. })));
    }
}
