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
    use std::path::Path;
    use std::path::PathBuf;
    use std::process::Command;
    use std::process::Output;

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
            lines_of(&output, &source).is_empty(),
            "a settled declaration has no line"
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
                lines_of(&output, &source),
                vec![
                    "unsettled `broken` at 18..40: states checks owing 0; produced refuses UnresolvedName \
                     (malformed source)"
                        .to_owned()
                ],
                "{verb} prints the unsettled declaration alone"
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
            lines_of(&reported, &source),
            vec![
                "goal: unsettled `hole` at 0..20: states checks owing 0; produced checks owing 1; surviving \
                 obligations: 1 undeclared, 0 unproduced"
                    .to_owned()
            ],
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
            assert!(
                stderr(&output).starts_with(&format!("gandr: {}: ", path.display())),
                "{}",
                stderr(&output)
            );
            assert!(
                stdout(&output).ends_with("verdict: faulted\n"),
                "a fault outranks an unsettled declaration"
            );
            assert_eq!(
                lines_of(&output, &broken).len(),
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
        for arguments in [vec![], vec![PathBuf::from("check"), source]] {
            let (reader, writer) = std::io::pipe().expect("a pipe is made");
            drop(reader);
            let mut command = gandr(&arguments);
            command.stdout(writer);
            let output = ran(command);
            assert_eq!(code(&output), Code(2_i32), "{arguments:?}");
            assert!(
                stderr(&output).starts_with("gandr: cannot write the output: "),
                "{arguments:?}: {}",
                stderr(&output)
            );
        }
    }
}
