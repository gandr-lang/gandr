//! The loop observed from outside: lines offered, blocks and transcripts read.
//!
//! Every type a case expects is spelled by the renderer or read from a corpus
//! source, and every refusal a case expects is rendered by the diagnostics
//! renderer over the same revision, so no case restates a spelling the
//! surface owns.

/// The loop's cases, in a `cfg(test)` module so the crate's lint wall reads
/// them as test code rather than as shipping code.
#[cfg(test)]
mod tests
{
    use std::path::Path;

    use gandr_core_incremental::BackendArtifact;
    use gandr_core_incremental::ContentNode;
    use gandr_core_incremental::MemoryCheckpointStore;
    use gandr_core_incremental::NodeIndex;
    use gandr_core_incremental::Reference;
    use gandr_core_incremental::Typing;
    use gandr_kernel_term::BaseType;
    use gandr_surface_diagnostics::Class;
    use gandr_surface_diagnostics::Entry;
    use gandr_surface_diagnostics::RenderStyle;
    use gandr_surface_diagnostics::entries;
    use gandr_surface_dispatcher::Goals;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_dispatcher::Verb;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_render_remote::HlRole;
    use gandr_surface_render_remote::OutKind;
    use gandr_surface_render_remote::TranscriptBlock;
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
    use gandr_surface_repl::drive;
    use gandr_surface_repl::finished;
    use gandr_surface_repl::run_batch;
    use gandr_surface_repl::span_order;
    use gandr_surface_repl::spell;
    use gandr_surface_session::Session;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    /// The strict corpus sources, by path from this crate.
    const CORPUS: [&str; 2] = [
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../surface-corpus/strict/values.gandr"
        ),
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../surface-corpus/strict/functions.gandr"
        ),
    ];

    /// The built-in grammar.
    ///
    /// # Specification
    /// trivial.
    fn grammar() -> Pbg
    {
        built_in().expect("the built-in grammar builds")
    }

    /// A loop rendering refusals plainly.
    ///
    /// # Specification
    /// trivial.
    fn repl() -> SessionLoop
    {
        SessionLoop::new(RenderStyle::Plain).expect("the loop starts")
    }

    /// Offer `line` to `repl`.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
    fn block<'line, Line>(
        repl: &mut SessionLoop,
        line: Line,
    ) -> TranscriptBlock
    where
        Line: Into<SourceText<'line>>,
    {
        let line = line.into();
        match offer(repl, line) {
            | LoopEvent::Block(block) => block,
            | other => panic!("`{line}` answers a block, not {other:?}"),
        }
    }

    /// The lines `line` answers with.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
    fn base(base: BaseType) -> String
    {
        spell(&[ContentNode::Base(base)], NodeIndex::from(0)).to_string()
    }

    /// A fresh session as the loop makes one, over the strict root.
    ///
    /// # Specification
    /// trivial.
    fn session() -> Session<MemoryCheckpointStore>
    {
        Session::new(
            grammar(),
            SourceRoot::Strict,
            MemoryCheckpointStore::default(),
            BackendArtifact::from(b"gandr-surface-repl tests".as_slice()),
        )
    }

    /// The diagnostics renderer's refusal reports over `revision`, under
    /// `style`, each as the diagnostic line a block carries.
    ///
    /// # Specification
    /// trivial.
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
            .filter_map(|entry| match entry {
                | Entry::Report(report) if report.class() != Class::Goal => Some((
                    OutKind::Diag,
                    report.render(style).to_string().trim_end().to_owned(),
                )),
                | Entry::Report(_) | Entry::Line(_) => None,
            })
            .collect()
    }

    /// Whether the parser expects no further token after `buffer`.
    ///
    /// # Specification
    /// trivial.
    fn complete<'buffer, Buffer>(buffer: Buffer) -> CompletionStatus
    where
        Buffer: Into<SourceText<'buffer>>,
    {
        completeness(&grammar(), buffer.into())
    }

    /// An open group is incomplete, alone or inside a definition.
    #[test]
    fn an_open_form_is_incomplete()
    {
        assert!(!bool::from(complete("(")));
        assert!(!bool::from(complete("def a = (")));
    }

    /// A bare atom is complete.
    #[test]
    fn a_bare_atom_is_complete()
    {
        assert!(bool::from(complete("42")));
    }

    /// A hole is a complete term: holes are typeable, so a buffer holding one
    /// is submitted.
    #[test]
    fn a_hole_is_complete()
    {
        assert!(bool::from(complete("?")));
        assert!(bool::from(complete("def h = ? ;")));
    }

    /// A definition waits for its terminator, and submits with it.
    #[test]
    fn a_declaration_waits_for_its_terminator()
    {
        assert!(!bool::from(complete("def answer =")));
        assert!(bool::from(complete("def answer = 42 ;")));
    }

    /// The gate's answer is named through this crate, and the empty buffer —
    /// the boundary of the gate — expects nothing.
    #[test]
    fn unused_completion_status_name_stays_in_scope()
    {
        assert_eq!(
            completeness(&grammar(), SourceText::from("")),
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

    /// A complete atom is submitted at once. The fragment reads only
    /// declarations, so its line is the lowering's refusal, exactly as the
    /// diagnostics renderer writes it for the same text.
    #[test]
    fn a_complete_atom_submits()
    {
        let mut repl = repl();
        let block = block(&mut repl, "42");
        assert_eq!(block.source, "42");
        assert_eq!(block.lines, refusals("42", RenderStyle::Plain));
        assert_eq!(block.lines.len(), 1, "one refusal: {:?}", block.lines);
    }

    /// A definition kept on one line is in scope on the next.
    #[test]
    fn a_definition_is_visible_on_the_next_line()
    {
        let mut repl = repl();
        let integer = base(BaseType::Integer);
        assert_eq!(lines(&mut repl, "def y = 5 ;"), [(
            OutKind::Type,
            format!("y : {integer}")
        )]);
        assert_eq!(lines(&mut repl, "def z = y ;"), [(
            OutKind::Type,
            format!("z : {integer}")
        )]);
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
        assert_eq!(lines(&mut repl, r#"def h = "now" ;"#), [(
            OutKind::Type,
            format!("h : {string}")
        )]);
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
        assert_eq!(lines(&mut repl, r#"def wrong = "right" ;"#), [(
            OutKind::Type,
            format!("wrong : {}", base(BaseType::String))
        )]);
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
        assert_eq!(lines(&mut repl, "def d = a ;"), [(
            OutKind::Type,
            format!("d : {}", base(BaseType::Integer))
        )]);
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
        assert_eq!(help.len(), 6, "{help:?}");
        assert!(help.iter().all(|&(kind, _)| kind == OutKind::Info));
        for command in [":type", ":load", ":reset", ":help", ":quit"] {
            assert!(
                help.iter().any(|row| row.1.starts_with(command)),
                "`{command}` is listed"
            );
        }
        let _kept = lines(&mut repl, "def y = 1 ;");
        assert_eq!(lines(&mut repl, ":reset"), [(
            OutKind::Info,
            "every declaration is forgotten".to_owned()
        )]);
        assert_eq!(
            lines(&mut repl, "def z = y ;"),
            refusals("def z = y ;", RenderStyle::Plain)
        );
        assert_eq!(lines(&mut repl, ":load"), [(
            OutKind::Info,
            ":load needs a file: :load <file>".to_owned()
        )]);
        assert_eq!(lines(&mut repl, ":frob x"), [(
            OutKind::Info,
            "no command `:frob x`; :help lists them".to_owned()
        )]);
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
        assert_eq!(lines(&mut repl, "def it = 1 ;"), [(
            OutKind::Type,
            format!("it : {integer}")
        )]);
        assert_eq!(lines(&mut repl, ":type it"), [(
            OutKind::Type,
            format!(": {integer}")
        )]);
        assert_eq!(lines(&mut repl, r#"def it1 = "s" ;"#), [(
            OutKind::Type,
            format!("it1 : {}", base(BaseType::String))
        )]);
    }

    /// `:load` submits a file as one chunk, every declaration answering a
    /// line, and a file that cannot be read answers why.
    #[test]
    fn a_loaded_file_is_one_chunk()
    {
        let mut repl = repl();
        let loaded = block(&mut repl, format!(":load {}", CORPUS[0]).as_str());
        assert_eq!(loaded.lines.len(), 5, "{:?}", loaded.lines);
        let missing = lines(&mut repl, ":load does/not/exist.gandr");
        assert!(
            matches!(missing.as_slice(), [(OutKind::Diag, line)] if line.starts_with("cannot read `does/not/exist.gandr`: ")),
            "{missing:?}"
        );
        assert_eq!(lines(&mut repl, "def again = echo ;"), [(
            OutKind::Type,
            format!("again : {}", base(BaseType::Integer))
        )]);
    }

    /// A checked declaration's line names its type exactly as the renderer
    /// spells the signature the session checked, never the content's debug
    /// image.
    #[test]
    fn a_checked_definition_names_its_type_in_the_renderers_spelling()
    {
        let signature = "def identity : U (Integer -> F Integer) ;";
        let definition = "def identity = thunk { fn (x) { ret x } } ;";
        let mut session = session();
        let _submission = session
            .submit(SourceText::from(
                format!("{signature}\n{definition}").as_str(),
            ))
            .expect("the session does not fault");
        let Maybe::Present(resume) = session.last()
        else {
            panic!("the revision is resumed");
        };
        let checkpoint = resume
            .checkpoints()
            .items()
            .iter()
            .find(|checkpoint| {
                matches!(checkpoint.content().reference(), Reference::Item { key, .. } if key.as_ref() == b"identity")
            })
            .expect("identity is checkpointed");
        assert!(matches!(checkpoint.typing(), Typing::Checked { .. }));
        let Maybe::Present(root) = checkpoint.content().signature()
        else {
            panic!("identity is signed");
        };
        let spelling = spell(checkpoint.content().nodes(), root).to_string();
        let mut repl = repl();
        let _goal = lines(&mut repl, signature);
        assert_eq!(lines(&mut repl, definition), [(
            OutKind::Type,
            format!("identity : {spelling}")
        )]);
        let debug = format!("{:?}", checkpoint.content().nodes());
        assert!(
            !spelling.contains("ThunkType") && debug.contains("ThunkType"),
            "{spelling}"
        );
    }

    /// Every signature of the strict corpus, loaded, answers a type line that
    /// spells the type exactly as the source wrote it.
    #[test]
    fn corpus_types_spell_as_their_source_writes_them()
    {
        for path in CORPUS {
            let source = std::fs::read_to_string(path).expect("the corpus source reads");
            let mut repl = repl();
            let loaded = lines(&mut repl, format!(":load {path}").as_str());
            let mut signatures = 0_usize;
            for written in source.lines() {
                let Some(signature) = written
                    .strip_prefix("def ")
                    .and_then(|rest| rest.strip_suffix(" ;"))
                    .filter(|rest| rest.contains(" : "))
                else {
                    continue;
                };
                signatures += 1;
                assert!(
                    loaded.contains(&(OutKind::Type, signature.to_owned())),
                    "{path}: `{signature}` among {loaded:?}"
                );
            }
            assert!(signatures > 2, "{path} states signatures");
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

    /// Over every line of the strict corpus, offered one at a time, every
    /// echo's spans are sorted, disjoint and inside the echo.
    #[test]
    fn transcript_spans_are_sorted_and_disjoint()
    {
        for path in CORPUS {
            let source = std::fs::read_to_string(path).expect("the corpus source reads");
            let mut repl = repl();
            let mut echoed = 0_usize;
            for line in source.lines() {
                if let LoopEvent::Block(block) = offer(&mut repl, line) {
                    assert_eq!(span_order(&block.source_hl), SpanOrder::SortedAndDisjoint);
                    assert!(
                        block
                            .source_hl
                            .iter()
                            .all(|span| usize::from(span.range.end()) <= block.source.len())
                    );
                    echoed += usize::from(!block.source_hl.is_empty());
                }
            }
            assert!(echoed > 4, "{path}: the echoes are highlighted");
        }
    }

    /// A buffer still open at the end of input is submitted, not dropped.
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
            block.lines.iter().any(|&(kind, _)| kind == OutKind::Diag),
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
    /// trivial.
    fn piped<Input>(input: Input) -> (Ended, String)
    where
        Input: std::io::BufRead,
    {
        let mut output = Vec::new();
        let ended =
            run_batch(input, &mut output, RenderStyle::Plain).expect("the transcript is written");
        (
            ended,
            String::from_utf8(output).expect("the transcript is UTF-8"),
        )
    }

    /// A piped session loading a corpus source and asking a type prints the
    /// echo and one line per declaration, then the answer.
    #[test]
    fn piped_value_prints_a_transcript()
    {
        let input = format!(":load {}\n:type answer\n:q\n", CORPUS[0]);
        let (ended, transcript) = piped(input.as_bytes());
        assert!(matches!(ended, Ended::Completed));
        let integer = base(BaseType::Integer);
        let string = base(BaseType::String);
        let unit = spell(&[ContentNode::UnitType], NodeIndex::from(0)).to_string();
        let expected = [
            format!("▸ :load {}", CORPUS[0]),
            format!("answer : {integer}"),
            format!("greeting : {string}"),
            format!("nothing : {unit}"),
            format!("copy : {integer}"),
            format!("echo : {integer}"),
            "▸ :type answer".to_owned(),
            format!(": {integer}"),
        ];
        assert_eq!(transcript.lines().collect::<Vec<_>>(), expected);
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
        /// trivial.
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
        let ended =
            drive(&mut script, &mut output, RenderStyle::Plain).expect("the transcript is written");
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
}
