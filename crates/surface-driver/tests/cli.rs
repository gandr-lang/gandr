//! The driver's exit codes and output, observed by spawning the binary.
//!
//! Each case writes its sources into a scratch directory, runs `gandr` on
//! them, and asserts the exit code and the lines it printed. Output to a pipe
//! whose reader is closed is the unwritable case: the runtime ignores
//! `SIGPIPE`, so the write fails with `EPIPE` rather than ending the process.

/// The process-level cases, in a `cfg(test)` module so the crate's lint wall
/// reads them as test code rather than as shipping code.
#[cfg(test)]
mod cli
{
    use std::io::Write as _;
    use std::path::Path;
    use std::path::PathBuf;
    use std::process::Command;
    use std::process::Output;
    use std::process::Stdio;

    use gandr_surface_lsp::Body;
    use gandr_surface_lsp::read_frame;
    use gandr_surface_lsp::write_frame;
    use quenchant_shape::shape::Maybe;

    /// A fresh scratch directory, removed when dropped.
    #[repr(transparent)]
    struct Scratch(PathBuf);

    /// The text of one scratch source.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct Text<'text>(&'text str);

    impl<'text> From<&'text str> for Text<'text>
    {
        /// Adopt `text` as a source's text.
        ///
        /// # Specification
        ///
        /// trivial.
        fn from(text: &'text str) -> Self
        {
            Self(text)
        }
    }

    /// A process's exit code.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Code(i32);

    impl Scratch
    {
        /// An empty directory named for `test` and this process.
        ///
        /// # Specification
        /// - requires: a unique single-component test name and writable
        ///   temporary storage, without concurrent mutation of this case's
        ///   directory.
        /// - ensures: returns a fresh empty directory owned by this process and
        ///   case.
        /// - provides: isolated source storage.
        /// - fails: never.
        /// - panics: if stale storage cannot be removed or the directory
        ///   created.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — two live cases with the same relative source path
        ///   produce different process verdicts; removing one leaves the other
        ///   usable. Namespace collisions, stale contents and cross-case
        ///   removal change these observations. Concurrent external writers and
        ///   permission failures are excluded.
        /// - witness: `cli::cli::scratch_ownership_keeps_simultaneous_cases_independent`
        #[anodized::spec(
            requires: test.file_name().is_some_and(|name| name == test.as_os_str()),
            ensures: |ref ret| ret.0.is_dir()
                && std::fs::read_dir(&ret.0).is_ok_and(|mut entries| entries.next().is_none()),
        )]
        fn new(test: &Path) -> Self
        {
            let root = std::env::temp_dir().join(format!(
                "gandr-driver-{}-{}",
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
        /// - requires: a nonempty path of normal relative components beneath
        ///   this owned, writable scratch directory, without concurrent
        ///   mutation.
        /// - ensures: creates missing parent directories and writes exactly the
        ///   offered source, returning its path beneath the scratch root.
        /// - provides: nested fixtures for a real driver process.
        /// - fails: never.
        /// - panics: if directories or the file cannot be written.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — simultaneous roots hold different sources under
        ///   the same nested relative name and yield different actual driver
        ///   verdicts. Escaping the root, losing directories or overwriting a
        ///   peer changes the observations; external mutations and failed
        ///   filesystem operations are excluded.
        /// - witness: `cli::cli::scratch_ownership_keeps_simultaneous_cases_independent`
        #[anodized::spec(
            requires: !relative.as_os_str().is_empty() && relative.components()
                .all(|component| matches!(component, std::path::Component::Normal(_))),
            ensures: |ref ret| ret.strip_prefix(&self.0).is_ok_and(|suffix| suffix == relative) && ret.is_file(),
        )]
        fn file(
            &self,
            relative: &Path,
            text: Text<'_>,
        ) -> PathBuf
        {
            let path = self.0.join(relative);
            std::fs::create_dir_all(path.parent().expect("a file has a parent"))
                .expect("the directories are created");
            std::fs::write(&path, text.0).expect("the file is written");
            path
        }
    }

    impl Drop for Scratch
    {
        /// Remove the directory and everything under it.
        ///
        /// # Specification
        /// - requires: this case still owns its removable directory.
        /// - ensures: removes the root and its descendants without removing
        ///   peer roots.
        /// - provides: scoped fixture lifetime.
        /// - fails: never.
        /// - panics: if removal fails.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — one of two live nested fixture roots is dropped;
        ///   its path disappears and the peer still produces its expected
        ///   process verdict. Missing cleanup and overbroad deletion differ;
        ///   concurrent mutation is excluded.
        /// - witness: `cli::cli::scratch_ownership_keeps_simultaneous_cases_independent`
        #[anodized::spec(ensures: !self.0.exists())]
        fn drop(&mut self)
        {
            let removed = std::fs::remove_dir_all(&self.0);
            assert!(removed.is_ok(), "the scratch directory is removed");
        }
    }

    /// The driver, ready to run with `arguments`.
    ///
    /// # Specification
    /// - requires: arguments have stable operating-system string views.
    /// - ensures: selects the built driver and preserves arguments in order.
    /// - provides: a command without starting a process.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — malformed invocations, an extra script operand and
    ///   distinct check/test results expose argument identity and order.
    ///   Dropped, reordered or substituted arguments change statuses or output;
    ///   arbitrary `AsRef` types with stateful views are outside the domain.
    /// - witness: `cli::cli::a_malformed_invocation_exits_two`
    /// - witness: `cli::cli::a_second_operand_is_refused`
    /// - witness: `cli::cli::the_test_verb_prints_every_fixture_and_pending_source`
    #[anodized::spec(ensures: |ref ret| ret.get_program() == std::ffi::OsStr::new(env!("CARGO_BIN_EXE_gandr"))
        && ret.get_args().eq(arguments.iter().map(AsRef::as_ref)))]
    fn gandr<Argument>(arguments: &[Argument]) -> Command
    where
        Argument: AsRef<std::ffi::OsStr>,
    {
        let mut command = Command::new(env!("CARGO_BIN_EXE_gandr"));
        command.args(arguments);
        command
    }

    /// The finished run of `command`, its output captured.
    ///
    /// # Specification
    /// - requires: a spawnable driver command, with no external process
    ///   termination.
    /// - ensures: waits for completion and returns its status and captured
    ///   streams.
    /// - provides: a process-boundary observation.
    /// - fails: never.
    /// - panics: if the driver cannot start or be waited for.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — accepted, refused and unreadable sources plus a
    ///   closed output pipe expose all three process statuses and stream roles.
    ///   Wrong commands, missing waits or lost output change these fixtures;
    ///   external signals and process-creation failures are excluded.
    /// - witness: `cli::cli::a_settled_run_exits_zero`
    /// - witness: `cli::cli::an_unreadable_path_exits_two`
    /// - witness: `cli::cli::unwritable_standard_output_exits_two`
    #[anodized::spec(
        requires: command.get_program() == std::ffi::OsStr::new(env!("CARGO_BIN_EXE_gandr")),
        ensures: |ref ret| matches!(ret.status.code(), Some(0 ..= 2)),
    )]
    fn ran(mut command: Command) -> Output
    {
        command.output().expect("the driver runs")
    }

    /// The exit code of `output`.
    ///
    /// # Specification
    /// - requires: the process exited normally with a numeric code.
    /// - ensures: returns exactly that code.
    /// - provides: a nominal process-status observation.
    /// - fails: never.
    /// - panics: if the process ended without a code.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — accepted, refused and unreadable cases assert
    ///   distinct zero, one and two statuses. Incorrect extraction or collapsed
    ///   statuses changes these observations; signal termination is excluded.
    /// - witness: `cli::cli::a_settled_run_exits_zero`
    /// - witness: `cli::cli::an_unsettled_run_exits_one`
    /// - witness: `cli::cli::an_unreadable_path_exits_two`
    #[anodized::spec(requires: output.status.code().is_some(),
        ensures: |ret| output.status.code() == Some(ret.0))]
    fn code(output: &Output) -> Code
    {
        Code(output.status.code().expect("the driver exits with a code"))
    }

    /// Standard output of `output`, as text.
    ///
    /// # Specification
    /// - requires: captured standard output is UTF-8.
    /// - ensures: returns its bytes unchanged as owned text.
    /// - provides: readable transcript and value observations.
    /// - fails: never.
    /// - panics: if standard output is not UTF-8.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — value multiplicity and piped transcript fixtures
    ///   compare exact visible lines. Lost, duplicated or replaced bytes change
    ///   those observations; non-UTF-8 output is excluded.
    /// - witness: `cli::cli::the_value_of_a_run_is_printed_once`
    /// - witness: `cli::cli::a_piped_repl_session_prints_its_transcript`
    #[anodized::spec(ensures: |ref ret| ret.as_bytes() == output.stdout.as_slice())]
    fn stdout(output: &Output) -> String
    {
        String::from_utf8(output.stdout.clone()).expect("standard output is UTF-8")
    }

    /// Standard error of `output`, as text.
    ///
    /// # Specification
    /// - requires: captured standard error is UTF-8.
    /// - ensures: returns its bytes unchanged as owned text.
    /// - provides: readable fault and refusal observations.
    /// - fails: never.
    /// - panics: if standard error is not UTF-8.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — absent paths, checker refusal and blame identify the
    ///   failed source or goal on the diagnostic stream. Lost bytes or confused
    ///   streams change these observations; non-UTF-8 output is excluded.
    /// - witness: `cli::cli::an_absent_script_is_refused_by_path`
    /// - witness: `cli::cli::an_ill_typed_script_is_refused_by_the_checker`
    /// - witness: `cli::cli::a_script_that_blames_leaves_with_a_failure_status`
    #[anodized::spec(ensures: |ref ret| ret.as_bytes() == output.stderr.as_slice())]
    fn stderr(output: &Output) -> String
    {
        String::from_utf8(output.stderr.clone()).expect("standard error is UTF-8")
    }

    /// The lines of `output`'s standard output that start with `path`, the
    /// prefix removed.
    ///
    /// # Specification
    /// - requires: standard output is UTF-8.
    /// - ensures: retains path-prefixed lines in order, removing the displayed
    ///   path and separator but not their payload.
    /// - provides: path-specific ledger observations.
    /// - fails: never.
    /// - panics: if standard output is not UTF-8.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — settled and pending fixtures share one run but retain
    ///   distinct path-scoped ledger rows under test and none under check.
    ///   Wrong prefix selection or payload loss changes those observations;
    ///   arbitrary path spellings and embedded line terminators are not
    ///   enumerated.
    /// - witness: `cli::cli::the_test_verb_prints_every_fixture_and_pending_source`
    #[anodized::spec(ensures: |ref ret| ret.iter().all(|line| !line.contains('\n')))]
    fn lines_of(
        output: &Output,
        path: &Path,
    ) -> Vec<String>
    {
        let prefix = format!("{}: ", path.display());
        stdout(output)
            .lines()
            .filter_map(|line| line.strip_prefix(prefix.as_str()))
            .map(str::to_owned)
            .collect()
    }

    /// What `output` printed on standard output before the runner's report:
    /// every report and ledger line of the run.
    ///
    /// # Specification
    /// - requires: UTF-8 output whose first sources marker starts the final
    ///   report.
    /// - ensures: returns exactly the prefix before that marker.
    /// - provides: diagnostic and ledger output separated from the run summary.
    /// - fails: never.
    /// - panics: if output is not UTF-8 or no report marker exists.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — settled, refused, owed and unreadable fixtures
    ///   compare the diagnostic prefix independently of final summaries.
    ///   Truncation, summary leakage or wrong boundaries change the
    ///   observations; source text containing an earlier report marker is
    ///   excluded.
    /// - witness: `cli::cli::a_settled_run_exits_zero`
    /// - witness: `cli::cli::an_unsettled_run_exits_one`
    /// - witness: `cli::cli::goals_report_an_obligation_without_failing`
    #[anodized::spec(ensures: |ref ret| output.stdout.starts_with(ret.as_bytes())
        && !ret.contains("sources: ")
        && output.stdout.get(ret.len() ..).is_some_and(|tail| tail.starts_with(b"sources: ")))]
    fn printed(output: &Output) -> String
    {
        let stdout = stdout(output);
        let (printed, _report) = stdout
            .split_once("sources: ")
            .expect("the runner's report closes standard output");
        printed.to_owned()
    }

    #[test]
    fn a_settled_run_exits_zero()
    {
        let scratch = Scratch::new(Path::new("settled"));
        let source = scratch.file(
            Path::new("answer.gandr"),
            Text::from("def answer : Integer ;\ndef answer = 42 ;\ndef copy = answer ;\n"),
        );
        let output = ran(gandr(&[Path::new("check"), &source]));
        assert_eq!(code(&output), Code(0_i32), "{}", stdout(&output));
        assert!(
            printed(&output).is_empty(),
            "a settled declaration prints nothing"
        );
        assert!(
            stdout(&output).ends_with("seal: sealed\nverdict: settled\n"),
            "{}",
            stdout(&output)
        );
    }

    #[test]
    fn an_unsettled_run_exits_one()
    {
        let scratch = Scratch::new(Path::new("unsettled"));
        let source = scratch.file(
            Path::new("broken.gandr"),
            Text::from("def answer = 42 ;\ndef broken = missing ;\n"),
        );
        for verb in ["check", "test"] {
            let output = ran(gandr(&[Path::new(verb), &source]));
            assert_eq!(code(&output), Code(1_i32), "{verb}: {}", stdout(&output));
            let diagnostic = printed(&output);
            assert!(diagnostic.starts_with("error[UnresolvedName]:"));
            assert!(diagnostic.contains(&format!("{}:2:14", source.display())));
            assert!(diagnostic.contains("2 │ def broken = missing ;"));
            assert!(stdout(&output).ends_with("verdict: unsettled\n"), "{verb}");
        }
    }

    #[test]
    fn goals_report_an_obligation_without_failing()
    {
        let scratch = Scratch::new(Path::new("goals"));
        let source = scratch.file(
            Path::new("hole.gandr"),
            Text::from("def hole : Integer ;\n"),
        );
        let gated = ran(gandr(&[Path::new("check"), &source]));
        assert_eq!(code(&gated), Code(1_i32), "an owed signature fails check");
        let reported = ran(gandr(&[Path::new("check"), Path::new("--goals"), &source]));
        assert_eq!(code(&reported), Code(0_i32), "{}", stdout(&reported));
        let goal = printed(&reported);
        assert!(goal.starts_with("goal: `hole`"));
        assert!(goal.contains(&format!("{}:1:1", source.display())));

        let mixed = scratch.file(
            Path::new("mixed.gandr"),
            Text::from("def hole : Integer ;\ndef broken = missing ;\n"),
        );
        let output = ran(gandr(&[Path::new("check"), Path::new("--goals"), &mixed]));
        assert_eq!(
            code(&output),
            Code(1_i32),
            "a refusal still fails check --goals"
        );
    }

    #[test]
    fn the_test_verb_prints_every_fixture_and_pending_source()
    {
        let scratch = Scratch::new(Path::new("fixtures"));
        let owed = Text::from("@[ owes(1) ] def later : Integer ;\n");
        let fixture = scratch.file(Path::new("fixture/later.gandr"), owed);
        let pending = scratch.file(
            Path::new("fixture/pending/whole.gandr"),
            Text::from("ret 3\n"),
        );
        let root = scratch.0.join("fixture");

        let tested = ran(gandr(&[Path::new("test"), &root]));
        assert_eq!(code(&tested), Code(0_i32), "{}", stdout(&tested));
        let fixture_lines = lines_of(&tested, &fixture);
        let pending_lines = lines_of(&tested, &pending);
        assert_eq!(fixture_lines.len(), 1);
        assert!(fixture_lines[0].starts_with("settled `later`"));
        assert_eq!(pending_lines.len(), 1);
        assert!(pending_lines[0].starts_with("pending: "));
        assert!(pending_lines[0].contains("`ret_expression`"));

        let checked = ran(gandr(&[Path::new("check"), &root]));
        assert_eq!(code(&checked), Code(0_i32), "{}", stdout(&checked));
        assert!(
            lines_of(&checked, &fixture).is_empty() && lines_of(&checked, &pending).is_empty(),
            "check prints neither"
        );

        let strict = scratch.file(Path::new("strict/later.gandr"), owed);
        let output = ran(gandr(&[Path::new("check"), &strict]));
        assert_eq!(
            code(&output),
            Code(1_i32),
            "the strict root refuses the expectation"
        );
        let lowered = scratch.file(
            Path::new("fixture/pending/lowered.gandr"),
            Text::from("def a = 1 ;\n"),
        );
        let output = ran(gandr(&[Path::new("test"), &lowered]));
        assert_eq!(
            code(&output),
            Code(1_i32),
            "a pending source the lowering reads is unsettled"
        );
    }

    #[test]
    fn an_unreadable_path_exits_two()
    {
        let scratch = Scratch::new(Path::new("unreadable"));
        let settled = scratch.file(Path::new("answer.gandr"), Text::from("def answer = 42 ;\n"));
        let broken = scratch.file(
            Path::new("broken.gandr"),
            Text::from("def broken = missing ;\n"),
        );
        let absent = scratch.0.join("absent.gandr");
        let empty = scratch.0.join("empty");
        std::fs::create_dir_all(&empty).expect("the empty directory is created");
        let invalid = scratch.0.join("invalid.gandr");
        std::fs::write(&invalid, [0xff_u8, 0xfe_u8]).expect("the file is written");
        for path in [&absent, &empty, &invalid] {
            let output = ran(gandr(&[Path::new("check"), &settled, &broken, path]));
            assert_eq!(
                code(&output),
                Code(2_i32),
                "{}: {}",
                path.display(),
                stderr(&output)
            );
            let fault_prefix = format!("gandr: {}: ", path.display());
            assert!(
                stderr(&output)
                    .lines()
                    .any(|line| line.starts_with(&fault_prefix)),
                "{}",
                stderr(&output)
            );
            assert!(
                stdout(&output).ends_with("verdict: faulted\n"),
                "a fault outranks an unsettled declaration"
            );
            assert_eq!(
                printed(&output)
                    .matches(&format!("╭▸ {}:", broken.display()))
                    .count(),
                1_usize,
                "the walk continued past the fault and read every other path"
            );
        }
    }

    #[test]
    fn a_malformed_invocation_exits_two()
    {
        for arguments in [&["check"][..], &["test"], &["frobnicate"], &[
            "check",
            "--unknown",
            "a.gandr",
        ]] {
            let output = ran(gandr(arguments));
            assert_eq!(code(&output), Code(2_i32), "{arguments:?}");
            assert!(
                output.stdout.is_empty(),
                "{arguments:?}: nothing on standard output"
            );
        }
    }

    #[test]
    fn help_exits_zero()
    {
        for arguments in [&["--help"][..], &["check", "--help"], &["--version"]] {
            let output = ran(gandr(arguments));
            assert_eq!(code(&output), Code(0_i32), "{arguments:?}");
            assert!(
                output.stderr.is_empty(),
                "informational output is not an error"
            );
        }
    }

    #[test]
    fn status_and_version_identify_the_same_build()
    {
        let version = ran(gandr(&["--version"]));
        let status = ran(gandr::<&str>(&[]));
        assert_eq!(code(&version), Code(0));
        assert_eq!(code(&status), Code(0));
        let identity = stdout(&version);
        let report = stdout(&status);
        assert!(report.starts_with(&format!("{} ", identity.trim_end())));
        assert_eq!(report.lines().count(), 1);
        assert!(version.stderr.is_empty() && status.stderr.is_empty());
    }

    #[test]
    fn unwritable_standard_output_exits_two()
    {
        let scratch = Scratch::new(Path::new("unwritable"));
        let source = scratch.file(Path::new("answer.gandr"), Text::from("def answer = 42 ;\n"));
        let program = scratch.file(
            Path::new("program.gandr"),
            Text::from("def main : +U (-F Integer) ; def main = thunk { ret 17 } ;"),
        );
        for arguments in [
            &[][..],
            &[Path::new("check"), source.as_path()],
            &[Path::new("run"), program.as_path()],
            &[Path::new("tui"), Path::new("--smoke")],
            &[Path::new("lsp"), Path::new("--capabilities")],
            &[Path::new("--help")],
            &[Path::new("repl"), Path::new("--batch")],
        ] {
            let (reader, writer) = std::io::pipe().expect("a pipe is made");
            drop(reader);
            let mut command = gandr(arguments);
            command.stdout(writer);
            command.stdin(std::fs::File::open(&source).expect("the input source opens"));
            let output = ran(command);
            assert_eq!(code(&output), Code(2_i32), "{arguments:?}");
        }
    }

    /// One input stream carrying `messages` as frames, in order.
    ///
    /// # Specification
    /// - requires: each offered body is encodable by the transport.
    /// - ensures: concatenates the messages as ordered protocol frames, with no
    ///   extra frame for empty input.
    /// - provides: client input for a real language-server process.
    /// - fails: never.
    /// - panics: if a body cannot be framed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — initialization, shutdown and exit produce two
    ///   response frames and clean completion; initialization alone ends
    ///   abruptly. Missing or reordered input changes cardinality or status.
    ///   Arbitrary bodies and size limits belong to the transport rather than
    ///   this finite session.
    /// - witness: `cli::cli::lsp_serves_a_session_over_the_standard_streams`
    #[anodized::spec(ensures: |ref ret| messages.last().map_or_else(
        || ret.as_ref().is_empty(),
        |last| ret.as_ref().starts_with(b"Content-Length: ") && ret.as_ref().ends_with(last.0.as_bytes()),
    ))]
    fn frames(messages: &[Text<'_>]) -> Body
    {
        let mut stream = Vec::new();
        for message in messages {
            write_frame(&mut stream, &Body::from(message.0.as_bytes().to_vec()))
                .expect("a vector takes every write");
        }
        Body::from(stream)
    }

    /// The finished run of `gandr lsp` with `input` on standard input, its
    /// output captured.
    ///
    /// # Specification
    /// - requires: a finite input whose pipe write completes before server
    ///   exit, with no external process termination.
    /// - ensures: closes client input after sending it, waits for the server
    ///   and captures both output streams and its process status.
    /// - provides: end-of-input and protocol-boundary observations.
    /// - fails: never.
    /// - panics: on process or pipe failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a complete session, premature EOF and truncated frame
    ///   produce distinct zero, one and two statuses. Unclosed input, missing
    ///   writes or lost termination state changes those cases; large
    ///   backpressured sessions and external signals are excluded.
    /// - witness: `cli::cli::lsp_serves_a_session_over_the_standard_streams`
    #[anodized::spec(ensures: |ref ret| matches!(ret.status.code(), Some(0 ..= 2)))]
    fn served(input: &Body) -> Output
    {
        let mut child = gandr(&["lsp"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("the driver starts");
        child
            .stdin
            .take()
            .expect("standard input is piped")
            .write_all(input.as_ref())
            .expect("the session is written");
        child.wait_with_output().expect("the driver runs")
    }

    #[test]
    fn lsp_serves_a_session_over_the_standard_streams()
    {
        let initialize =
            Text::from(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#);
        let shutdown = Text::from(r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#);
        let exit = Text::from(r#"{"jsonrpc":"2.0","method":"exit"}"#);
        let output = served(&frames(&[initialize, shutdown, exit]));
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
        let mut replies = output.stdout.as_slice();
        for _ in 0_u8 .. 2 {
            assert!(matches!(
                read_frame(&mut replies).expect("a response is framed"),
                Maybe::Present(_)
            ));
        }
        assert!(
            matches!(
                read_frame(&mut replies).expect("the response boundary is clean"),
                Maybe::Absent(_)
            ),
            "exit is a notification and receives no reply"
        );

        let output = served(&frames(&[initialize]));
        assert_eq!(
            code(&output),
            Code(1_i32),
            "a session closed before shutdown exits one"
        );

        let output = served(&Body::from(b"Content-Length: 9\r\n\r\n{".to_vec()));
        assert_eq!(code(&output), Code(2_i32), "a broken stream exits two");
        assert!(
            output.stdout.is_empty(),
            "an incomplete first request has no response"
        );
        assert!(
            stderr(&output).starts_with("gandr:"),
            "the stream fault uses standard error"
        );
    }

    /// The finished run of `gandr` with `arguments` and `input` on standard
    /// input, its output captured.
    ///
    /// # Specification
    /// - requires: stable driver arguments and finite input whose pipe write
    ///   completes before the child exits, without external termination.
    /// - ensures: sends the offered bytes, closes input, waits, and captures
    ///   the process status and both streams.
    /// - provides: a plain-stream client for interactive verbs.
    /// - fails: never.
    /// - panics: on process or pipe failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a finite load/query/refusal/quit transcript is
    ///   compared in automatic and explicit batch modes. Dropped input, wrong
    ///   stream selection or reading beyond quit changes exact rows. Large
    ///   backpressured sessions and external signals are outside the domain.
    /// - witness: `cli::cli::a_piped_repl_session_prints_its_transcript`
    #[anodized::spec(ensures: |ref ret| matches!(ret.status.code(), Some(0 ..= 2)))]
    fn piped<Argument>(
        arguments: &[Argument],
        input: Text<'_>,
    ) -> Output
    where
        Argument: AsRef<std::ffi::OsStr>,
    {
        let mut child = gandr(arguments)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("the driver starts");
        child
            .stdin
            .take()
            .expect("standard input is piped")
            .write_all(input.0.as_bytes())
            .expect("the session is written");
        child.wait_with_output().expect("the driver runs")
    }

    /// A piped session prints its plain transcript: each echo, the loaded
    /// declaration's type spelled as its source wrote it, the type a probe
    /// answers, and a refusal as the diagnostics renderer writes it; it exits
    /// zero, and `--batch` prints the same transcript.
    #[test]
    fn a_piped_repl_session_prints_its_transcript()
    {
        let scratch = Scratch::new(Path::new("repl"));
        let source = scratch.file(
            Path::new("answer.gandr"),
            Text::from("def answer : Integer ;\ndef answer = 42 ;\n"),
        );
        let session = format!(
            ":load {}\n:type answer\ndef broken = missing ;\n:q\ndef unread = 1 ;\n",
            source.display()
        );
        let output = piped(&["repl"], Text::from(session.as_str()));
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
        assert_eq!(stderr(&output), "", "a refusal is no fault");
        let transcript = stdout(&output);
        let printed: Vec<&str> = transcript.lines().collect();
        assert_eq!(
            printed.get(.. 6),
            Some(
                &[
                    format!("▸ :load {}", source.display()).as_str(),
                    "answer : Integer",
                    "= 42",
                    "▸ :type answer",
                    ": Integer",
                    "▸ def broken = missing ;",
                ][..]
            ),
            "{transcript}"
        );
        assert!(
            printed
                .get(6)
                .is_some_and(|line| line.starts_with("error[UnresolvedName]: ")),
            "{transcript}"
        );
        assert!(
            !transcript.contains("unread"),
            "nothing after `:q` is read: {transcript}"
        );
        let batch = piped(&["repl", "--batch"], Text::from(session.as_str()));
        assert_eq!(code(&batch), Code(0_i32), "{}", stderr(&batch));
        assert_eq!(
            stdout(&batch),
            transcript,
            "`--batch` prints the same transcript"
        );
    }

    #[test]
    fn smoke_is_terminal_free_but_interactive_tui_refuses_pipes()
    {
        let smoke = ran(gandr(&["tui", "--smoke"]));
        let interactive = ran(gandr(&["tui"]));
        assert_eq!(code(&smoke), Code(0));
        assert!(smoke.stderr.is_empty());
        assert!(
            !smoke.stdout.contains(&0x1b_u8),
            "the headless face emits no terminal commands"
        );
        assert_eq!(code(&interactive), Code(2));
        assert!(
            interactive.stdout.is_empty(),
            "a refused terminal face paints nothing"
        );
        assert!(stderr(&interactive).starts_with("gandr:"));
    }

    /// A script of `text`, written to `name` in `scratch`, run by the driver.
    ///
    /// # Specification
    /// - requires: a valid scratch-relative source name, writable storage and a
    ///   driver that starts and finishes without external termination.
    /// - ensures: writes and runs that source, returning its path and captured
    ///   run.
    /// - provides: source/status pairs for script semantics.
    /// - fails: never.
    /// - panics: on filesystem or process failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — scripts returning a value, reaching blame, carrying a
    ///   checker refusal or declaring nothing expose status and stream
    ///   separation. Wrong paths, arguments or captured outputs change these
    ///   observations; arbitrary scripts and external mutation are excluded.
    /// - witness: `cli::cli::a_script_that_returns_a_value_leaves_successfully`
    /// - witness: `cli::cli::a_script_that_blames_leaves_with_a_failure_status`
    /// - witness: `cli::cli::a_script_with_no_program_is_refused`
    #[anodized::spec(ensures: |ref ret| ret.0.strip_prefix(&scratch.0).is_ok_and(|relative| relative == name)
        && matches!(ret.1.status.code(), Some(0 ..= 2)))]
    fn run_script(
        scratch: &Scratch,
        name: &Path,
        text: Text<'_>,
    ) -> (PathBuf, Output)
    {
        let path = scratch.file(name, text);
        let output = ran(gandr(&[Path::new("run").as_os_str(), path.as_os_str()]));
        (path, output)
    }

    /// A run that returns a value prints it on standard output and exits zero.
    #[test]
    fn a_script_that_returns_a_value_leaves_successfully()
    {
        let scratch = Scratch::new(Path::new("script-value"));
        let (_path, output) = run_script(
            &scratch,
            Path::new("value.gandr"),
            Text::from("def main : +U (-F Integer) ;\ndef main = thunk { ret 42 } ;\n"),
        );
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
        assert_eq!(
            stdout(&output),
            "42\n",
            "the run routes its value to the caller"
        );
        assert_eq!(stderr(&output), "", "a completed run writes no complaint");
    }

    /// The value of a completed run is the whole of standard output, once,
    /// however many declarations the script holds.
    #[test]
    fn the_value_of_a_run_is_printed_once()
    {
        let scratch = Scratch::new(Path::new("script-once"));
        let (_path, output) = run_script(
            &scratch,
            Path::new("once.gandr"),
            Text::from(
                "def answer = 42 ;\ndef copy = answer ;\ndef shown : +U (-F Integer) ;\ndef shown = thunk { ret copy } ;\n",
            ),
        );
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
        assert_eq!(
            stdout(&output).lines().collect::<Vec<_>>(),
            ["42"],
            "one value line, and nothing else on standard output"
        );
    }

    /// A run that reaches a goal is blamed on it, on standard error, and
    /// exits one.
    #[test]
    fn a_script_that_blames_leaves_with_a_failure_status()
    {
        let scratch = Scratch::new(Path::new("script-blame"));
        let (path, output) = run_script(
            &scratch,
            Path::new("blame.gandr"),
            Text::from(
                "def later : +U (-F Integer) ;\ndef main : +U (-F Integer) ;\ndef main = thunk { force later } ;\n",
            ),
        );
        assert_eq!(
            code(&output),
            Code(1_i32),
            "a run that reaches a blame is a failure, not a success"
        );
        assert_eq!(stdout(&output), "", "a blamed run routes no value");
        let prefix = format!("gandr: {}: ", path.display());
        assert!(stderr(&output).lines().any(|line| line.starts_with(&prefix)
            && line.contains("`main`")
            && line.contains("`later`")));
    }

    /// A script the checker refuses never reaches the machine: its refusal is
    /// on standard error, nothing on standard output, and it exits two.
    #[test]
    fn an_ill_typed_script_is_refused_by_the_checker()
    {
        let scratch = Scratch::new(Path::new("script-ill-typed"));
        let (path, output) = run_script(
            &scratch,
            Path::new("ill-typed.gandr"),
            Text::from("def main : Integer ;\ndef main = \"five\" ;\n"),
        );
        assert_eq!(
            code(&output),
            Code(2_i32),
            "an ill-typed script never reaches the machine"
        );
        assert_eq!(stdout(&output), "", "a refused script routes no result");
        let complaint = stderr(&output);
        assert!(
            complaint.starts_with("error[TypeMismatch]: "),
            "the checker's refusal is reported: {complaint}"
        );
        assert!(
            complaint
                .lines()
                .any(|line| line.starts_with(&format!("gandr: {}: ", path.display()))),
            "{complaint}"
        );
        assert!(
            !complaint.contains('\u{1b}'),
            "captured diagnostics stay plain: {complaint}"
        );
    }

    /// A refusal of a declaration the run never reaches still stops the run.
    #[test]
    fn an_outcome_only_refusal_is_visible_in_a_script_run()
    {
        let scratch = Scratch::new(Path::new("script-outcome-only"));
        let (_path, output) = run_script(
            &scratch,
            Path::new("outcome-only.gandr"),
            Text::from("def wrong : Integer ;\ndef wrong = \"one\" ;\ndef main = 0 ;\n"),
        );
        assert_eq!(
            code(&output),
            Code(2_i32),
            "an outcome-only refusal never reaches the machine"
        );
        assert_eq!(stdout(&output), "", "a refused script routes no result");
        assert!(
            stderr(&output).starts_with("error[TypeMismatch]: "),
            "the refusal is reported: {}",
            stderr(&output)
        );
    }

    /// An absent script exits two, naming its path.
    #[test]
    fn an_absent_script_is_refused_by_path()
    {
        let scratch = Scratch::new(Path::new("script-absent"));
        let absent = scratch.0.join("absent.gandr");
        let output = ran(gandr(&[Path::new("run").as_os_str(), absent.as_os_str()]));
        assert_eq!(
            code(&output),
            Code(2_i32),
            "a source that never reached the machine is a refusal, not a run failure"
        );
        assert!(
            stderr(&output).starts_with(&format!("gandr: {}: ", absent.display())),
            "a read refusal names the path: {}",
            stderr(&output)
        );
    }

    /// A script declaring no name has nothing to run and exits two.
    #[test]
    fn a_script_with_no_program_is_refused()
    {
        let scratch = Scratch::new(Path::new("script-no-program"));
        let (path, output) = run_script(
            &scratch,
            Path::new("nothing.gandr"),
            Text::from("// declares nothing\n"),
        );
        assert_eq!(
            code(&output),
            Code(2_i32),
            "a source with no runnable declaration never reaches the machine"
        );
        assert!(output.stdout.is_empty());
        assert!(stderr(&output).starts_with(&format!("gandr: {}: ", path.display())));
    }

    /// `run` takes exactly one operand.
    #[test]
    fn a_second_operand_is_refused()
    {
        let output = ran(gandr(&["run", "one.gandr", "two.gandr"]));
        assert_eq!(
            code(&output),
            Code(2_i32),
            "the script runner takes exactly one operand"
        );
    }

    /// A literal dash selects a path, whether that file is absent or runnable.
    #[test]
    fn a_bare_dash_is_a_path_not_standard_input()
    {
        let scratch = Scratch::new(Path::new("literal-dash"));
        let mut missing = gandr(&["run", "-"]);
        missing.current_dir(&scratch.0);
        let output = ran(missing);
        assert_eq!(code(&output), Code(2));
        assert!(stderr(&output).starts_with("gandr: -: "));
        let _path = scratch.file(
            Path::new("-"),
            Text::from("def main : +U (-F Integer) ; def main = thunk { ret 17 } ;"),
        );
        let mut present = gandr(&["run", "-"]);
        present.current_dir(&scratch.0);
        let output = ran(present);
        assert_eq!(code(&output), Code(0));
        assert_eq!(
            stdout(&output),
            "17\n",
            "a literal file is read instead of closed stdin"
        );
    }

    #[test]
    fn scratch_ownership_keeps_simultaneous_cases_independent()
    {
        let accepted = Scratch::new(Path::new("isolation-accepted"));
        let refused = Scratch::new(Path::new("isolation-refused"));
        let name = Path::new("nested/shared.gandr");
        let accepted_source = accepted.file(name, Text::from("def answer = 17 ;"));
        let refused_source = refused.file(name, Text::from("def broken = missing ;"));
        assert_eq!(
            code(&ran(gandr(&[Path::new("check"), &accepted_source]))),
            Code(0)
        );
        assert_eq!(
            code(&ran(gandr(&[Path::new("check"), &refused_source]))),
            Code(1)
        );
        let removed = accepted_source
            .parent()
            .and_then(Path::parent)
            .expect("the nested source has its scratch root");
        drop(accepted);
        assert!(!removed.exists());
        let surviving = ran(gandr(&[Path::new("check"), &refused_source]));
        assert_eq!(code(&surviving), Code(1));
        assert!(stdout(&surviving).contains("error[UnresolvedName]:"));
    }

    #[test]
    fn a_failed_diagnostic_stream_stops_later_output()
    {
        let scratch = Scratch::new(Path::new("failed-diagnostic-stream"));
        let source = scratch.file(
            Path::new("value.gandr"),
            Text::from(
                "def unused : Integer ; def main : +U (-F Integer) ; def main = thunk { ret 9 } ;",
            ),
        );
        let control = ran(gandr(&[Path::new("run"), &source]));
        assert_eq!(code(&control), Code(0));
        assert_eq!(stdout(&control), "9\n");
        let missing = scratch.0.join("missing.gandr");
        for arguments in [[Path::new("check"), missing.as_path()], [
            Path::new("run"),
            source.as_path(),
        ]] {
            let (reader, writer) = std::io::pipe().expect("a pipe is made");
            drop(reader);
            let mut command = gandr(&arguments);
            command.stderr(writer);
            let output = ran(command);
            assert_eq!(code(&output), Code(2), "{arguments:?}");
            assert!(
                output.stdout.is_empty(),
                "no later summary or value: {arguments:?}"
            );
        }
    }
}
