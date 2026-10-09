//! The run verb's source and script faces.
//!
//! [`run_source`] runs source text and [`Script`] the file `gandr run` names.
//! These cases pin what the file face separates — a path it cannot read, a
//! source that never reaches the machine, and a completed run — and the
//! shebang line an executable script opens with, each against the same text
//! run with no file.

/// The run cases, in a `cfg(test)` module so the crate's lint wall reads them
/// as test code rather than as shipping code.
#[cfg(test)]
mod run
{
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_dispatcher::Composed;
    use gandr_surface_dispatcher::Evaluation;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::Ran;
    use gandr_surface_dispatcher::RunStatus;
    use gandr_surface_dispatcher::Script;
    use gandr_surface_dispatcher::ScriptRun;
    use gandr_surface_dispatcher::SourceFault;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::run_source;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::SourceText;

    /// A program whose last declaration returns forty-two.
    const ANSWER: &str = "def main : +U (-F Integer) ;\ndef main = thunk { ret 42 } ;\n";

    /// A scratch source file, removed when dropped.
    #[repr(transparent)]
    struct Scratch(PathBuf);

    impl Scratch
    {
        /// `text` written to a file named for `test` and this process.
        ///
        /// # Specification
        ///
        /// trivial.
        fn write(
            test: &Path,
            text: SourceText<'_>,
        ) -> Self
        {
            let path = std::env::temp_dir().join(format!(
                "gandr-dispatcher-run-{}-{}.gandr",
                test.display(),
                std::process::id()
            ));
            std::fs::write(&path, text.as_ref()).expect("the scratch source is written");
            Self(path)
        }
    }

    impl Drop for Scratch
    {
        /// Remove the file.
        ///
        /// # Specification
        ///
        /// trivial.
        fn drop(&mut self)
        {
            let removed = std::fs::remove_file(&self.0);
            assert!(removed.is_ok(), "the scratch source is removed");
        }
    }

    /// What running `text` with no file comes to.
    ///
    /// # Specification
    ///
    /// trivial.
    fn ran_text(text: SourceText<'_>) -> Ran<'_>
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let mut lowerings = LoweringCount::default();
        let (_composed, ran) =
            run_source(&grammar, text, &mut lowerings).expect("the source composes");
        ran
    }

    /// Assert that the script at `path` composes settled and runs to
    /// `expected`, as the same text run with no file does.
    ///
    /// # Specification
    ///
    /// trivial.
    fn assert_runs_to(
        path: &Path,
        expected: &Ran<'_>,
    )
    {
        let mut script = Script::new(path.to_path_buf());
        match script.run() {
            | ScriptRun::Source {
                step:
                    Step::Source {
                        composed: Composed::Settled { .. },
                        ..
                    },
                ran,
            } => assert_eq!(ran, *expected, "the file face runs as its text does"),
            | other => panic!("the script composes: {other:?}"),
        }
    }

    #[test]
    fn run_source_runs_source_text()
    {
        let ran = ran_text(SourceText::from(ANSWER));
        assert!(
            matches!(
                ran,
                Ran::Evaluated {
                    target,
                    evaluation: Evaluation::Value(ref value),
                } if target.as_ref() == "main" && value.as_ref() == "42"
            ),
            "a completed run returns the computed value: {ran:?}"
        );
    }

    /// A script file runs exactly as its source text does.
    #[test]
    fn run_source_file_runs_a_script_file()
    {
        let script = Scratch::write(Path::new("value"), SourceText::from(ANSWER));
        assert_runs_to(&script.0, &ran_text(SourceText::from(ANSWER)));
    }

    /// A shebang line does not change what a script computes.
    #[test]
    fn run_source_file_accepts_an_executable_shebang_line()
    {
        let shebang = format!("#!/usr/bin/env gandr\n{ANSWER}");
        let script = Scratch::write(Path::new("shebang"), SourceText::from(shebang.as_str()));
        assert_runs_to(&script.0, &ran_text(SourceText::from(ANSWER)));
    }

    #[test]
    fn run_source_file_reports_the_path_of_an_absent_file()
    {
        let absent = std::env::temp_dir().join(format!(
            "gandr-dispatcher-run-absent-{}.gandr",
            std::process::id()
        ));
        drop(std::fs::remove_file(&absent));
        let mut script = Script::new(absent.clone());
        let run = script.run();
        assert_eq!(
            run.status(),
            RunStatus::Unreached,
            "an absent file never reaches the machine"
        );
        assert!(
            matches!(
                run,
                ScriptRun::Fault {
                    path,
                    fault: SourceFault::Unreadable(_),
                } if path == absent
            ),
            "an unreadable file is a read fault naming the path it could not read: {run:?}"
        );
    }

    /// The script face surfaces the source's failure unchanged.
    #[test]
    fn run_source_file_surfaces_a_source_failure_unchanged()
    {
        for (test, text, failure) in [
            ("no-program", "// declares nothing\n", Ran::NoProgram),
            (
                "refused",
                "def only : Integer ;\ndef only = \"one\" ;\n",
                Ran::Refused,
            ),
        ] {
            assert_eq!(
                ran_text(SourceText::from(text)),
                failure,
                "`{text}` fails before the machine"
            );
            let script = Scratch::write(Path::new(test), SourceText::from(text));
            assert_runs_to(&script.0, &failure);
        }
    }
}
