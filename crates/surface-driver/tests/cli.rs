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
    use gandr_surface_lsp::Capabilities;
    use gandr_surface_lsp::write_frame;

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
        ///
        /// trivial.
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
        ///
        /// trivial.
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
        ///
        /// trivial.
        fn drop(&mut self)
        {
            let removed = std::fs::remove_dir_all(&self.0);
            assert!(removed.is_ok(), "the scratch directory is removed");
        }
    }

    /// The driver, ready to run with `arguments`.
    ///
    /// # Specification
    ///
    /// trivial.
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
    ///
    /// trivial.
    fn ran(mut command: Command) -> Output
    {
        command.output().expect("the driver runs")
    }

    /// The exit code of `output`.
    ///
    /// # Specification
    ///
    /// trivial.
    fn code(output: &Output) -> Code
    {
        Code(output.status.code().expect("the driver exits with a code"))
    }

    /// Standard output of `output`, as text.
    ///
    /// # Specification
    ///
    /// trivial.
    fn stdout(output: &Output) -> String
    {
        String::from_utf8(output.stdout.clone()).expect("standard output is UTF-8")
    }

    /// Standard error of `output`, as text.
    ///
    /// # Specification
    ///
    /// trivial.
    fn stderr(output: &Output) -> String
    {
        String::from_utf8(output.stderr.clone()).expect("standard error is UTF-8")
    }

    /// The lines of `output`'s standard output that start with `path`, the
    /// prefix removed.
    ///
    /// # Specification
    ///
    /// trivial.
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
    ///
    /// trivial.
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
            assert_eq!(
                printed(&output),
                format!(
                    r"error[UnresolvedName]: no declaration or binder answers `missing` at 31..38
  ╭▸ {}:2:14
  │
2 │ def broken = missing ;
  │              ━━━━━━━ malformed source
  │
  ╰ note: unsettled `broken` states checks owing 0

",
                    source.display()
                ),
                "{verb} prints the unsettled declaration alone, as its snippet"
            );
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
        assert_eq!(
            printed(&reported),
            format!(
                r"goal: `hole` states checks owing 0; produced checks owing 1
  ╭▸ {}:1:1
  │
1 │ def hole : Integer ;
  ╰╴━━━━━━━━━━━━━━━━━━━━ surviving obligations: 1 undeclared, 0 unproduced

",
                source.display()
            ),
            "the obligation is printed as a goal"
        );

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
        assert_eq!(
            lines_of(&tested, &fixture),
            vec![
                "settled `later` at 0..34: states checks owing 1; produced checks owing 1"
                    .to_owned()
            ],
            "test prints the settled fixture"
        );
        assert_eq!(
            lines_of(&tested, &pending),
            vec!["pending: `ret_expression` at 0..5, read as a declaration, is not a former of this sort".to_owned()],
            "test prints the pending source"
        );

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
                stderr(&output).contains("Usage: gandr"),
                "{arguments:?}: {}",
                stderr(&output)
            );
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
                !output.stdout.is_empty(),
                "{arguments:?} prints to standard output"
            );
        }
    }

    #[test]
    fn a_bare_invocation_prints_the_status()
    {
        let output = ran(gandr::<&str>(&[]));
        assert_eq!(code(&output), Code(0_i32), "a bare invocation succeeds");
        assert_eq!(
            stdout(&output),
            format!(
                "gandr {} — toolchain management is not yet implemented; see https://github.com/gandr-lang/gandr\n",
                env!("CARGO_PKG_VERSION")
            ),
            "one status line"
        );
    }

    #[test]
    fn unwritable_standard_output_exits_two()
    {
        let scratch = Scratch::new(Path::new("unwritable"));
        let source = scratch.file(Path::new("answer.gandr"), Text::from("def answer = 42 ;\n"));
        for arguments in [vec![], vec![PathBuf::from("check"), source], vec![
            PathBuf::from("tui"),
            PathBuf::from("--smoke"),
        ]] {
            let (reader, writer) = std::io::pipe().expect("a pipe is made");
            drop(reader);
            let mut command = gandr(&arguments);
            command.stdout(writer);
            let output = ran(command);
            assert_eq!(code(&output), Code(2_i32), "{arguments:?}");
            assert!(
                stderr(&output)
                    .lines()
                    .any(|line| line.starts_with("gandr: cannot write the output: ")),
                "{arguments:?}: {}",
                stderr(&output)
            );
        }
    }

    /// One input stream carrying `messages` as frames, in order.
    ///
    /// # Specification
    ///
    /// trivial.
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
    ///
    /// trivial.
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
    fn lsp_capabilities_print_one_line_of_json()
    {
        let output = ran(gandr(&["lsp", "--capabilities"]));
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
        assert_eq!(
            stdout(&output),
            format!("{Capabilities}\n"),
            "the line the server answers `initialize` with"
        );
        assert!(
            stdout(&output).starts_with(r#"{"capabilities":{"positionEncoding":"utf-16","#),
            "positions are counted in UTF-16 code units: {}",
            stdout(&output)
        );
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
        let answer = format!(r#"{{"jsonrpc":"2.0","id":1,"result":{Capabilities}}}"#);
        let expected = frames(&[
            Text::from(answer.as_str()),
            Text::from(r#"{"jsonrpc":"2.0","id":2,"result":null}"#),
        ]);
        assert_eq!(
            output.stdout,
            expected.as_ref().to_vec(),
            "each request is answered in one frame, in order"
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
            stderr(&output).starts_with(
                "gandr: the language server stopped: the stream ended inside a frame\n"
            ),
            "the fault is noted on standard error: {}",
            stderr(&output)
        );
    }

    /// The finished run of `gandr` with `arguments` and `input` on standard
    /// input, its output captured.
    ///
    /// # Specification
    ///
    /// trivial.
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

    /// `gandr tui --smoke` runs the terminal face once off-screen, prints its
    /// one line and exits zero, touching no terminal.
    #[test]
    fn the_tui_smoke_face_prints_ready()
    {
        let output = ran(gandr(&["tui", "--smoke"]));
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
        assert_eq!(stdout(&output), "gandr tui: ready\n", "the smoke line");
        assert_eq!(stderr(&output), "", "the smoke face notes nothing");
    }

    /// `gandr tui` without a terminal draws nothing, says why on standard
    /// error and exits two, rather than painting escapes into a pipe. Standard
    /// input is closed and standard output captured, so neither is a terminal;
    /// nothing is written to the driver, which exits without reading.
    #[test]
    fn the_tui_needs_a_terminal()
    {
        let output = ran(gandr(&["tui"]));
        assert_eq!(code(&output), Code(2_i32), "{}", stderr(&output));
        assert_eq!(stdout(&output), "", "nothing is drawn");
        assert!(
            stderr(&output).starts_with("gandr: the terminal face needs a terminal"),
            "{}",
            stderr(&output)
        );
    }

    /// A script of `text`, written to `name` in `scratch`, run by the driver.
    ///
    /// # Specification
    ///
    /// trivial.
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
        let blame = format!(
            "gandr: {}: `main` blame: `later` is owed its body",
            path.display()
        );
        assert!(
            stderr(&output).lines().any(|line| line == blame),
            "the blame names the goal reached: {}",
            stderr(&output)
        );
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
                .any(|line| line == format!("gandr: {}: refused; nothing ran", path.display())),
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
        assert_eq!(
            stderr(&output),
            format!("gandr: {}: declares no name to run\n", path.display())
        );
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

    /// `-` is a path, not standard input, so it fails as an absent file.
    #[test]
    fn a_bare_dash_is_a_path_not_standard_input()
    {
        let output = ran(gandr(&["run", "-"]));
        assert_eq!(
            code(&output),
            Code(2_i32),
            "a bare dash is a path, so it fails as a missing file"
        );
        assert!(
            stderr(&output).starts_with("gandr: -: "),
            "the refusal names the path it tried: {}",
            stderr(&output)
        );
    }
}
