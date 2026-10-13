//! The diagnostics model over real compositions.
//!
//! Each case composes its source through the dispatcher — a walk over a
//! scratch tree, or the composition itself where a case needs a fixed path —
//! and asserts the diagnostics its step yields: their classes, their spans,
//! their annotations, their contexts and their words.

/// The cases, in a `cfg(test)` module so the crate's lint wall reads them as
/// test code rather than as shipping code.
#[cfg(test)]
mod diagnostics
{
    use std::path::Path;
    use std::path::PathBuf;

    use anodized::spec;
    use gandr_core_checker::CheckRefusal;
    use gandr_core_checker::FrameRole;
    use gandr_core_checker::TermNode;
    use gandr_core_term::FailureClass;
    use gandr_surface_corpus::Refusal;
    use gandr_surface_diagnostics::AnnotationKind;
    use gandr_surface_diagnostics::Class;
    use gandr_surface_diagnostics::Diagnostic;
    use gandr_surface_diagnostics::Failures;
    use gandr_surface_diagnostics::Severity;
    use gandr_surface_diagnostics::Subject;
    use gandr_surface_diagnostics::Unsettlement;
    use gandr_surface_diagnostics::Verbosity;
    use gandr_surface_diagnostics::diagnose;
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
    use gandr_surface_dispatcher::entries;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::OriginTable;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    /// A declaration whose definition synthesises a type its signature does
    /// not convert to.
    const MISMATCH: &str = "def wrong : Integer ;\ndef wrong = \"text\" ;\n";

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
        /// - provides: isolated storage for walk witnesses.
        /// - fails: never returns a failure.
        /// - panics: if an existing directory cannot be removed or creation
        ///   fails.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a fresh owned directory holds exactly the sources
        ///   the walk witnesses write; stale entries would add diagnostics.
        /// - witness: `diagnostics::diagnostics::each_verb_prints_its_entries`
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

        /// Write `text` at `relative`, creating its directories.
        ///
        /// # Specification
        /// - requires: `relative` names a file through normal components within
        ///   this exclusively owned scratch directory.
        /// - ensures: the file under the scratch root holds `text`.
        /// - provides: a source for a real filesystem walk.
        /// - fails: never returns a failure.
        /// - panics: if the parent directories or the file cannot be written.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — each written source is read back through a real
        ///   walk and reports at its own path.
        /// - witness: `diagnostics::diagnostics::each_verb_prints_its_entries`
        #[spec(
            requires: relative.file_name().is_some() && relative.components().all(|component|
                matches!(component, std::path::Component::Normal(_))),
            ensures: std::fs::read_to_string(self.0.join(relative)).is_ok_and(|held| held == text.as_ref()),
        )]
        fn file(
            &self,
            relative: &Path,
            text: SourceText<'_>,
        )
        {
            let path = self.0.join(relative);
            std::fs::create_dir_all(path.parent().expect("a file has a parent"))
                .expect("the directories are created");
            std::fs::write(&path, text.as_ref()).expect("the file is written");
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
        /// - hypothesis: L3 — the walk witness leaves no tree behind.
        /// - witness: `diagnostics::diagnostics::each_verb_prints_its_entries`
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
    /// - ensures: an unsettled source step borrowing `path` and `text` under
    ///   `root`.
    /// - provides: a source step for diagnostic observations.
    /// - fails: never returns a failure.
    /// - panics: if grammar construction or composition fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — strict refusals and fixture expectations build
    ///   different diagnostics at their own spans; a wrong root or source
    ///   changes those observations.
    /// - witness: `diagnostics::diagnostics::a_type_mismatch_is_located_at_its_term`
    /// - witness: `diagnostics::diagnostics::the_settle_note_says_what_was_expected_in_words`
    #[spec(ensures: |ref ret| matches!(*ret,
        Step::Source { path: held, root: actual, standing: Standing::Unsettled, .. }
            if core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(path)) && actual == root))]
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

    /// The diagnostics a source at `path` under `root` with `text` prints
    /// under `verb`.
    ///
    /// # Specification
    /// trivial.
    fn printed(
        path: &Path,
        root: SourceRoot,
        text: SourceText<'_>,
        verb: Verb,
    ) -> Vec<Diagnostic>
    {
        let step = unsettled(path, root, text);
        entries(&step, verb).collect()
    }

    /// The one diagnostic a strict source with `text` prints under plain
    /// `check`.
    ///
    /// # Specification
    /// - requires: the source prints exactly one diagnostic.
    /// - ensures: that diagnostic.
    /// - provides: the subject of most cases.
    /// - fails: never returns a failure.
    /// - panics: if the source prints another number of diagnostics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every single-refusal source prints one diagnostic; a
    ///   source printing two fails loudly rather than asserting the wrong one.
    /// - witness: `diagnostics::diagnostics::a_refusal_names_the_rules_it_stood_inside`
    #[spec(ensures: |ref ret| ret.path.as_path() == path)]
    fn only(
        path: &Path,
        text: SourceText<'_>,
    ) -> Diagnostic
    {
        let mut printed = printed(path, SourceRoot::Strict, text, Verb::Check(Goals::Gated));
        assert_eq!(printed.len(), 1_usize, "one diagnostic: {printed:?}");
        printed.remove(0)
    }

    /// The bytes of each appearance of `needle` in `text`, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the span of every occurrence, first to last.
    /// - provides: an independent expected locus, indexed by occurrence.
    /// - fails: never returns a failure.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated equal siblings are told apart by their
    ///   occurrence index.
    /// - witness: `diagnostics::diagnostics::repeated_equal_siblings_point_at_the_right_occurrence`
    #[spec(ensures: |ref ret| ret.iter().all(|&span| text.fragment(span).is_ok_and(|fragment| fragment.as_ref() == needle.as_ref())))]
    fn nth(
        text: SourceText<'_>,
        needle: SourceText<'_>,
    ) -> Vec<ByteSpan>
    {
        text.as_ref()
            .match_indices(needle.as_ref())
            .map(|(start, _)| {
                ByteSpan::new(
                    ByteOffset::from(start),
                    ByteOffset::from(start.saturating_add(needle.as_ref().len())),
                )
                .expect("the span is ordered")
            })
            .collect()
    }

    /// Each context `diagnostic` carries, as the source text of its bytes
    /// (empty when unlocated) and its label.
    ///
    /// # Specification
    /// trivial.
    fn contexts(
        text: SourceText<'_>,
        diagnostic: &Diagnostic,
    ) -> Vec<(String, String)>
    {
        diagnostic
            .contexts
            .iter()
            .map(|context| match context.locus {
                | Maybe::Present(locus) => (
                    String::from(
                        text.fragment(locus.span)
                            .expect("a context lies inside the text")
                            .as_ref(),
                    ),
                    context.label(),
                ),
                | Maybe::Absent(_) => (String::new(), context.note()),
            })
            .collect()
    }

    /// What an origin table cut down for the unlocated cases keeps.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Kept
    {
        /// The primary node alone.
        Primary,
        /// Nothing.
        Nothing,
    }

    /// The force refusal built over an origin table cut down to `kept`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the force refusal's diagnostic, located at its operand when
    ///   the primary node is kept, unlocated otherwise; every rule it stood
    ///   inside names a node the table records nothing for, as a node the
    ///   checker minted does.
    /// - provides: the subject of the unlocated cases.
    /// - fails: never returns a failure.
    /// - panics: if the force source does not refuse with a shape mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one table keeps the primary node alone, the other
    ///   nothing; the rules lose their loci in both.
    /// - witness: `diagnostics::diagnostics::an_unlocated_rule_becomes_a_note`
    /// - witness: `diagnostics::diagnostics::an_unlocated_report_claims_no_span`
    #[spec(ensures: |ref ret| matches!(ret.span, Maybe::Present(_)) == (kept == Kept::Primary))]
    fn force_without_rules(kept: Kept) -> Diagnostic
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
        let mut table = OriginTable::new();
        if kept == Kept::Primary {
            let Maybe::Present(origin) = origins.value(value)
            else {
                panic!("the operand is recorded");
            };
            table.record_value(value, origin);
        }
        diagnose(path, text, Subject::Refused {
            declaration,
            refusal,
            origins: &table,
            spellings,
            failure: failures.get(declaration.constant()),
        })
    }

    #[test]
    fn a_type_mismatch_is_located_at_its_term()
    {
        let diagnostic = only(Path::new("mismatch.gandr"), SourceText::from(MISMATCH));
        assert_eq!(diagnostic.severity, Severity::Error);
        assert_eq!(
            diagnostic.detail.class,
            Class::Refusal(FailureClass::MalformedSource),
            "a type mismatch is malformed source"
        );
        assert_eq!(
            diagnostic.span,
            Maybe::Present(nth(SourceText::from(MISMATCH), SourceText::from("\"text\""))[0]),
            "the checker's refusal is located at the mismatched term through the origin table"
        );
        let primary = match diagnostic.primary() {
            | Maybe::Present(primary) => primary,
            | Maybe::Absent(reason) => panic!("the mismatch is located: {reason:?}"),
        };
        assert_eq!(
            (primary.locus.line, primary.locus.column),
            (2_usize, 13_usize)
        );
        assert_eq!(
            (
                diagnostic.message.text.as_str(),
                diagnostic.detail.title.as_str()
            ),
            (
                "mismatched types",
                "the type this term synthesises does not convert to the type it is checked against"
            ),
            "the message is plain; the checker's own words stay the title"
        );
        assert_eq!(
            diagnostic.expression,
            Maybe::Present(String::from("\"text\""))
        );
    }

    #[test]
    fn a_mismatch_label_spells_both_types()
    {
        let label = |diagnostic: &Diagnostic| match diagnostic.primary() {
            | Maybe::Present(primary) => primary.label.clone(),
            | Maybe::Absent(reason) => panic!("a located refusal carries a label: {reason:?}"),
        };
        let mismatch = only(Path::new("spelled.gandr"), SourceText::from(MISMATCH));
        assert_eq!(
            (
                mismatch.detail.compared.expected.clone(),
                mismatch.detail.compared.found.clone()
            ),
            (
                Maybe::Present(String::from("Integer")),
                Maybe::Present(String::from("String"))
            ),
            "a mismatch expects its signature's type and found its body's"
        );
        assert_eq!(
            label(&mismatch),
            "its type does not convert: expected `Integer`, found `String`"
        );
        assert_eq!(
            label(&only(Path::new("spelled.gandr"), SourceText::from(FORCE))),
            "its type is not of the required shape: found `Integer`",
            "a shape mismatch expects a former, which its title names, and spells what it found"
        );
        let head = label(&only(
            Path::new("spelled.gandr"),
            SourceText::from("def f(xs: Vec(Integer)) -> -F Integer {\n  pure 1\n}\n"),
        ));
        assert!(
            !head.contains(": "),
            "a refusal that compares no types carries none: {head}"
        );
    }

    #[test]
    fn a_refusal_keeps_its_failure_and_spells_its_types()
    {
        let text = SourceText::from(MISMATCH);
        let step = unsettled(Path::new("kept.gandr"), SourceRoot::Strict, text);
        let Step::Source {
            composed:
                Composed::Settled {
                    ref report,
                    ref failures,
                    ..
                },
            ..
        } = step
        else {
            panic!("the source settles");
        };
        let refused = report
            .declarations()
            .iter()
            .find(|declaration| matches!(declaration.produced().refusal(), Maybe::Present(_)))
            .expect("one declaration refuses");
        let Maybe::Present(failure) = failures.get(refused.constant())
        else {
            panic!("the refused body keeps its failure");
        };
        assert!(
            !failure.obligations().is_empty(),
            "the failure keeps the rules it stood inside"
        );
        let clean = unsettled(
            Path::new("clean.gandr"),
            SourceRoot::Strict,
            SourceText::from("def a = 1 ;\n"),
        );
        let Step::Source {
            composed: Composed::Settled { ref failures, .. },
            ..
        } = clean
        else {
            panic!("the clean source settles");
        };
        assert_eq!(
            *failures,
            Failures::default(),
            "a module that refuses nothing keeps no failure"
        );
    }

    #[test]
    fn a_refusal_names_the_rules_it_stood_inside()
    {
        assert_eq!(
            contexts(
                SourceText::from(FORCE),
                &only(Path::new("force.gandr"), SourceText::from(FORCE))
            ),
            [
                (
                    String::from("thunk { become force 1 }"),
                    String::from(
                        "checked against `+U (-F Integer)`; while checking the body of this thunk"
                    )
                ),
                (
                    String::from("force 1"),
                    String::from("checked against `-F Integer`; while forcing this")
                ),
            ],
            "the force of an integer stands inside the thunk, outermost first"
        );
        let application = only(
            Path::new("application.gandr"),
            SourceText::from(APPLICATION),
        );
        assert_eq!(
            contexts(SourceText::from(APPLICATION), &application),
            [
                (
                    String::from("thunk { become (pure 1)(2) }"),
                    String::from(
                        "checked against `+U (-F Integer)`; while checking the body of this thunk"
                    )
                ),
                (
                    String::from("(pure 1)(2)"),
                    String::from(
                        "checked against `-F Integer`; while synthesising the function this \
                         applies"
                    )
                ),
            ],
            "the head that is not a function stands inside the application and the thunk"
        );
        assert_eq!(
            application
                .contexts
                .iter()
                .map(|context| context.role)
                .collect::<Vec<_>>(),
            [FrameRole::ThunkBody, FrameRole::ApplicationHead],
            "each context keeps its rule's stable name"
        );
        assert_eq!(
            contexts(
                SourceText::from(MISMATCH),
                &only(Path::new("mismatch.gandr"), SourceText::from(MISMATCH))
            ),
            Vec::new(),
            "a body refused where it stands has no rule beyond its primary locus"
        );
    }

    #[test]
    fn a_mismatch_under_a_binder_names_it()
    {
        let diagnostic = only(Path::new("bound.gandr"), SourceText::from(BOUND));
        let named = contexts(SourceText::from(BOUND), &diagnostic);
        assert!(
            named.contains(&(
                String::from("run"),
                String::from(
                    "checked against `-F String`; while checking the body under this binding; \
                     binds m : Integer"
                )
            )),
            "the run names the binder it opened and its type: {named:?}"
        );
        assert_eq!(
            diagnostic
                .hypotheses
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            ["n : Integer", "m : Integer"],
            "the hypotheses in scope are the parameter and the run's binder, outermost first"
        );
        assert_eq!(
            diagnostic.span,
            Maybe::Present(nth(SourceText::from(BOUND), SourceText::from("m"))[1]),
            "the mismatch is the returned binder"
        );
    }

    #[test]
    fn an_unlocated_rule_becomes_a_note()
    {
        let diagnostic = force_without_rules(Kept::Primary);
        assert!(
            diagnostic
                .contexts
                .iter()
                .all(|context| matches!(context.locus, Maybe::Absent(_))),
            "a rule whose node the table records nothing for marks no bytes"
        );
        assert_eq!(
            contexts(SourceText::from(FORCE), &diagnostic)
                .into_iter()
                .map(|(_, note)| note)
                .collect::<Vec<_>>(),
            [
                "while checking the body of this thunk",
                "while comparing the type this synthesises with the one it is checked against",
                "while forcing this",
            ],
            "each unlocated rule reads as its sentence, outermost first"
        );
        assert!(
            diagnostic
                .annotations
                .iter()
                .all(|annotation| annotation.kind == AnnotationKind::Primary),
            "an unlocated rule adds no annotation"
        );
    }

    #[test]
    fn an_unlocated_report_claims_no_span()
    {
        let diagnostic = force_without_rules(Kept::Nothing);
        assert_eq!(
            diagnostic.span,
            Maybe::Absent(report_span::Absent::Unrecorded),
            "a node the table records nothing for is no locus"
        );
        assert!(matches!(diagnostic.primary(), Maybe::Absent(_)));
        assert!(
            diagnostic.annotations.is_empty(),
            "an unlocated report marks nothing"
        );
        assert!(
            matches!(diagnostic.excerpt, Maybe::Absent(_)),
            "and quotes no line"
        );
        assert!(
            matches!(diagnostic.expression, Maybe::Absent(_)),
            "and names no expression"
        );
    }

    #[test]
    fn a_return_position_failure_points_at_the_returned_value()
    {
        let text = "def g(v: Integer) -> -F String { return v }\n";
        let diagnostic = only(Path::new("returned.gandr"), SourceText::from(text));
        assert_eq!(
            diagnostic.span,
            Maybe::Present(nth(SourceText::from(text), SourceText::from("v"))[1]),
            "the mismatch is the value returned, not the return or the function"
        );
        assert_eq!(
            diagnostic.contexts.last().map(|context| context.role),
            Some(FrameRole::ReturnValue),
            "the innermost rule is the return's"
        );
    }

    #[test]
    fn repeated_equal_siblings_point_at_the_right_occurrence()
    {
        let text = "def h(a: String, b: Integer) -> -F Integer { return b }\ndef k(u: Integer) \
                    -> -F Integer { become h(\"no\", \"no\") }\n";
        assert_eq!(
            only(Path::new("siblings.gandr"), SourceText::from(text)).span,
            Maybe::Present(nth(SourceText::from(text), SourceText::from("\"no\""))[1]),
            "the second of two equal arguments is the one that mismatches"
        );
    }

    #[test]
    fn a_shadowed_builtin_is_a_warning()
    {
        let text = "def add : Integer ;\ndef add = 1 ;\ndef f(int: Integer) -> -F Integer { return \
                    int }\ndef g : Integer ;\ndef g = missing ;\n";
        let checked = printed(
            Path::new("shadow.gandr"),
            SourceRoot::Strict,
            SourceText::from(text),
            Verb::Check(Goals::Gated),
        );
        assert_eq!(
            checked
                .iter()
                .map(|diagnostic| (
                    diagnostic.severity,
                    diagnostic.detail.class,
                    diagnostic.span
                ))
                .collect::<Vec<_>>(),
            [
                (
                    Severity::Warning,
                    Class::Warning,
                    Maybe::Present(nth(SourceText::from(text), SourceText::from("add"))[0])
                ),
                (
                    Severity::Warning,
                    Class::Warning,
                    Maybe::Present(nth(SourceText::from(text), SourceText::from("int"))[0])
                ),
                (
                    Severity::Error,
                    Class::Refusal(FailureClass::MalformedSource),
                    Maybe::Present(nth(SourceText::from(text), SourceText::from("missing"))[0])
                ),
            ],
            "each shadowed builtin is a warning at its name, printed before the declarations"
        );
        for warning in &checked[.. 2] {
            assert!(
                matches!(warning.identifier, Maybe::Present(ref spelling) if spelling.as_ref() == "ShadowedBuiltin"),
                "a warning is named as the refusal the reject policy files"
            );
            assert_eq!(
                warning
                    .annotations
                    .first()
                    .map(|primary| primary.label.as_str()),
                Some("shadows a builtin")
            );
        }
        assert_eq!(
            checked[1].message.text,
            "`int` shadows a builtin name; the source's binding wins"
        );
        assert!(
            printed(
                Path::new("shadow.gandr"),
                SourceRoot::Strict,
                SourceText::from(text),
                Verb::Test
            )
            .iter()
            .all(|diagnostic| diagnostic.severity != Severity::Warning),
            "`test` prints settlements, never a warning"
        );
        assert!(
            printed(
                Path::new("shadow.gandr"),
                SourceRoot::Strict,
                SourceText::from("def add : Integer ;\ndef add = 1 ;\n"),
                Verb::Check(Goals::Gated),
            )
            .iter()
            .all(|diagnostic| diagnostic.severity == Severity::Warning),
            "a warning unsettles nothing"
        );
    }

    #[test]
    fn refusals_of_one_class_label_what_their_locus_is()
    {
        let mismatch = only(Path::new("mismatch.gandr"), SourceText::from(MISMATCH));
        let head = only(
            Path::new("head.gandr"),
            SourceText::from("def f(xs: Vec(Integer)) -> -F Integer {\n  pure 1\n}\n"),
        );
        assert_eq!(
            (mismatch.detail.class, head.detail.class),
            (
                Class::Refusal(FailureClass::MalformedSource),
                Class::Refusal(FailureClass::MalformedSource)
            ),
            "both refusals are the author's mistake"
        );
        let label = |diagnostic: &Diagnostic| match diagnostic.primary() {
            | Maybe::Present(primary) => primary.label.clone(),
            | Maybe::Absent(reason) => panic!("a located refusal carries a label: {reason:?}"),
        };
        assert_ne!(
            label(&mismatch),
            label(&head),
            "a term whose type does not convert and a head nothing answers are different loci"
        );
        for diagnostic in [&mismatch, &head] {
            assert_ne!(
                label(diagnostic),
                diagnostic.detail.class.to_string(),
                "the underline says what the bytes are, not the class"
            );
            assert!(
                !diagnostic.detail.title.contains(".."),
                "the annotation locates the refusal; the title repeats no byte range"
            );
        }
    }

    #[test]
    fn a_report_exposes_the_context_it_marks()
    {
        let marked = |diagnostic: &Diagnostic| -> Vec<(ByteSpan, String)> {
            diagnostic
                .annotations
                .iter()
                .filter(|annotation| annotation.kind == AnnotationKind::Context)
                .map(|annotation| (annotation.locus.span, annotation.label.clone()))
                .collect()
        };
        assert_eq!(
            marked(&only(
                Path::new("mismatch.gandr"),
                SourceText::from(MISMATCH)
            )),
            [(
                nth(SourceText::from(MISMATCH), SourceText::from("Integer"))[0],
                String::from("the type it is checked against")
            )],
            "the signature stands as the expected type; the synthesised type has no origin"
        );
        let duplicate = "def a : Integer ;\ndef a : Integer ;\ndef a = 1 ;\n";
        assert_eq!(
            marked(&only(
                Path::new("duplicate.gandr"),
                SourceText::from(duplicate)
            )),
            [(
                nth(
                    SourceText::from(duplicate),
                    SourceText::from("def a : Integer ;")
                )[0],
                String::from("first written here")
            )],
            "the first signature is the duplicate's one context locus"
        );
        let goals = printed(
            Path::new("hole.gandr"),
            SourceRoot::Strict,
            SourceText::from("def hole : Integer ;\n"),
            Verb::Check(Goals::Reported),
        );
        let [ref goal] = *goals.as_slice()
        else {
            panic!("one goal");
        };
        assert_eq!(goal.severity, Severity::Goal);
        assert_eq!(marked(goal), Vec::new(), "a goal names no context");
    }

    #[test]
    fn a_labeled_context_retains_its_locus_and_cause()
    {
        let duplicate = "def a : Integer ;\ndef a : Integer ;\ndef a = 1 ;\n";
        let diagnostic = only(Path::new("duplicate.gandr"), SourceText::from(duplicate));
        assert_eq!(
            diagnostic
                .annotations
                .iter()
                .map(|annotation| (annotation.kind, annotation.locus.line))
                .collect::<Vec<_>>(),
            [
                (AnnotationKind::Primary, 2_usize),
                (AnnotationKind::Context, 1_usize)
            ],
            "the duplicate is primary on its own line; the first signature is context on its own"
        );
        assert!(
            diagnostic
                .annotations
                .iter()
                .all(|annotation| !annotation.label.is_empty()),
            "each annotation says what its bytes are"
        );
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
                "def broken = missing ;\n",
                Verb::Check(Goals::Gated),
                Maybe::Present("UnresolvedName"),
                &[][..],
                &["missing"][..],
            ),
            (
                "@[ owes(0) ] def hole : Integer ;\n",
                Verb::Check(Goals::Reported),
                Maybe::Absent(report_identifier::Absent::Statement),
                &[0_usize, 1_usize][..],
                &["hole"][..],
            ),
        ];
        for (source, verb, identifier, numbers, names) in cases {
            let held = printed(
                Path::new("named.gandr"),
                SourceRoot::Fixture,
                SourceText::from(source),
                verb,
            );
            let [ref diagnostic] = *held.as_slice()
            else {
                panic!("one diagnostic for {source:?}");
            };
            let named = match diagnostic.identifier {
                | Maybe::Present(ref spelling) => Maybe::Present(spelling.to_string()),
                | Maybe::Absent(reason) => Maybe::Absent(reason),
            };
            let expected = match identifier {
                | Maybe::Present(spelling) => Maybe::Present(spelling.to_owned()),
                | Maybe::Absent(reason) => Maybe::Absent(reason),
            };
            assert_eq!(named, expected, "stable refusal identity for {source:?}");
            let title = &diagnostic.detail.title;
            for name in names {
                assert!(title.contains(name), "source name in {title}");
            }
            assert!(
                title
                    .split(|character: char| !character.is_ascii_digit())
                    .filter_map(|digits| digits.parse::<usize>().ok())
                    .eq(numbers.iter().copied()),
                "the title keeps its numeric roles without core addresses: {title}"
            );
        }
    }

    #[test]
    fn the_settle_note_says_what_was_expected_in_words()
    {
        for (source, note) in [
            (
                "@[ owes(0) ] def a = missing ;\n",
                "`a` is expected to check, and this refusal leaves it unsettled",
            ),
            (
                "@[ owes(3) ] def b = missing ;\n",
                "`b` is expected to check owing 3 obligations, and this refusal leaves it \
                 unsettled; surviving obligations: 0 undeclared, 3 unproduced",
            ),
            (
                "@[ refuses(\"TypeMismatch\") ] def c = missing ;\n",
                "`c` is expected to be refused with TypeMismatch, and this refusal is not that \
                 one",
            ),
        ] {
            let held = printed(
                Path::new("noted.gandr"),
                SourceRoot::Fixture,
                SourceText::from(source),
                Verb::Check(Goals::Gated),
            );
            let [ref diagnostic] = *held.as_slice()
            else {
                panic!("one refusal for {source:?}");
            };
            assert_eq!(
                diagnostic.note,
                Maybe::Present(String::from(note)),
                "the note says what was expected and why it did not happen"
            );
        }
    }

    #[test]
    fn a_refused_declaration_is_located()
    {
        let text = "def answer = 42 ;\ndef broken = missing ;\ndef wrong : Integer ;\ndef wrong = \
                    \"text\" ;\n@[ owes(1) ] def later : Integer ;\n";
        let malformed = Class::Refusal(FailureClass::MalformedSource);
        for verb in [
            Verb::Check(Goals::Gated),
            Verb::Check(Goals::Reported),
            Verb::Test,
        ] {
            assert_eq!(
                printed(
                    Path::new("refused.gandr"),
                    SourceRoot::Strict,
                    SourceText::from(text),
                    verb
                )
                .iter()
                .map(|diagnostic| (diagnostic.detail.class, diagnostic.span))
                .collect::<Vec<_>>(),
                [
                    (
                        malformed,
                        Maybe::Present(nth(SourceText::from(text), SourceText::from("missing"))[0])
                    ),
                    (
                        malformed,
                        Maybe::Present(
                            nth(SourceText::from(text), SourceText::from("\"text\""))[0]
                        )
                    ),
                    (
                        malformed,
                        Maybe::Present(nth(SourceText::from(text), SourceText::from("owes(1)"))[0])
                    ),
                ],
                "the lowering's, the checker's and the corpus root's refusals each sit at their \
                 own span under {verb:?}"
            );
        }
    }

    #[test]
    fn one_refusal_details_each_verbosity()
    {
        let diagnostic = only(Path::new("force.gandr"), SourceText::from(FORCE));
        let names = |verbosity| {
            diagnostic
                .details(verbosity)
                .into_iter()
                .map(|detail| detail.name)
                .collect::<Vec<_>>()
        };
        assert_eq!(names(Verbosity::User), Vec::<&str>::new());
        assert_eq!(names(Verbosity::Json), Vec::<&str>::new());
        assert_eq!(names(Verbosity::Detailed), [
            "class",
            "detail",
            "expression"
        ]);
        assert_eq!(names(Verbosity::Debug), [
            "class",
            "detail",
            "expression",
            "spans",
            "rules",
            "refusal"
        ]);
        let bound = only(Path::new("bound.gandr"), SourceText::from(BOUND));
        assert!(
            bound
                .details(Verbosity::Detailed)
                .iter()
                .any(|detail| detail.name == "hypotheses"
                    && detail.text == "`n : Integer`, `m : Integer`"),
            "the hypotheses show from the detailed level"
        );
        let image: serde_json::Value =
            serde_json::from_str(&diagnostic.json()).expect("the JSON image parses");
        assert_eq!(image["name"], "ShapeMismatch");
        assert_eq!(image["message"], diagnostic.message.text.as_str());
        assert_eq!(image["title"], diagnostic.detail.title.as_str());
        assert_eq!(
            (&image["primary"]["line"], &image["primary"]["column"]),
            (&serde_json::json!(2_u64), &serde_json::json!(30_u64)),
            "the primary locus is where the terminal points"
        );
        assert_eq!(
            image["contexts"].as_array().map(Vec::len),
            Some(diagnostic.contexts.len()),
            "every context is in the image"
        );
    }

    #[test]
    fn each_verb_prints_its_entries()
    {
        let scratch = Scratch::new(Path::new("entries"));
        for (relative, text) in [
            ("fixture/hole.gandr", "def hole : Integer ;\n"),
            ("fixture/pending/lowered.gandr", "def a = 1 ;\n"),
            ("fixture/pending/whole.gandr", "pure 3\n"),
            (
                "fixture/settled.gandr",
                "@[ owes(1) ] def later : Integer ;\n",
            ),
            (
                "fixture/unproduced.gandr",
                "@[ refuses(\"UnresolvedName\") ] def answer = 42 ;\n",
            ),
            ("strict/whole.gandr", "pure 3\n"),
        ] {
            scratch.file(Path::new(relative), SourceText::from(text));
        }
        let printed = |verb: Verb| {
            let mut walk = Walk::new(vec![scratch.0.clone()]);
            let mut printed = Vec::new();
            while let Maybe::Present(step) = walk.step() {
                for diagnostic in entries(&step, verb) {
                    if diagnostic.severity == Severity::Ledger {
                        let image: serde_json::Value = serde_json::from_str(&diagnostic.json())
                            .expect("a ledger line's JSON image parses");
                        assert_eq!(image["level"], "line");
                        assert_eq!(
                            image["line"],
                            format!("{}: {}", diagnostic.path.display(), diagnostic.message.text)
                                .as_str(),
                            "the JSON image carries the line as the terminal prints it"
                        );
                    }
                    printed.push((
                        diagnostic
                            .path
                            .strip_prefix(&scratch.0)
                            .expect("within scratch")
                            .to_path_buf(),
                        diagnostic.severity,
                        diagnostic.detail.class,
                    ));
                }
            }
            printed
        };
        let check = |hole: Severity, class: Class| {
            vec![
                (PathBuf::from("fixture/hole.gandr"), hole, class),
                (
                    PathBuf::from("fixture/pending/lowered.gandr"),
                    Severity::Ledger,
                    Class::Ledger,
                ),
                (
                    PathBuf::from("fixture/unproduced.gandr"),
                    Severity::Error,
                    Class::Unsettled(Unsettlement::Unproduced),
                ),
                (
                    PathBuf::from("strict/whole.gandr"),
                    Severity::Error,
                    Class::Refusal(FailureClass::Unrepresentable),
                ),
            ]
        };
        assert_eq!(
            printed(Verb::Check(Goals::Gated)),
            check(Severity::Error, Class::Unsettled(Unsettlement::Obligations))
        );
        assert_eq!(
            printed(Verb::Check(Goals::Reported)),
            check(Severity::Goal, Class::Goal)
        );
        assert_eq!(printed(Verb::Test), vec![
            (
                PathBuf::from("fixture/hole.gandr"),
                Severity::Error,
                Class::Unsettled(Unsettlement::Obligations)
            ),
            (
                PathBuf::from("fixture/pending/lowered.gandr"),
                Severity::Ledger,
                Class::Ledger
            ),
            (
                PathBuf::from("fixture/pending/whole.gandr"),
                Severity::Ledger,
                Class::Ledger
            ),
            (
                PathBuf::from("fixture/settled.gandr"),
                Severity::Ledger,
                Class::Ledger
            ),
            (
                PathBuf::from("fixture/unproduced.gandr"),
                Severity::Error,
                Class::Unsettled(Unsettlement::Unproduced)
            ),
            (
                PathBuf::from("strict/whole.gandr"),
                Severity::Error,
                Class::Refusal(FailureClass::Unrepresentable)
            ),
        ]);
    }
}
