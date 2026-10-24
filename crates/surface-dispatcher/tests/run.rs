//! The run verb's source and script faces.
//!
//! [`run_source`] runs source text and [`Script`] the file `gandr run` names.
//! These cases pin what the file face separates — a path it cannot read, a
//! source that never reaches the machine, and a completed run — and the
//! shebang line an executable script opens with, each against the same text
//! run with no file.
//!
//! The run cases, in a `cfg(test)` module so the crate's lint wall reads them
//! as test code rather than as shipping code.

use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_dispatcher::Captured;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Entered;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Ran;
use gandr_surface_dispatcher::RunStatus;
use gandr_surface_dispatcher::Script;
use gandr_surface_dispatcher::ScriptRun;
use gandr_surface_dispatcher::SourceFault;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::run_source;
use gandr_surface_grammar::Spelling;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;

/// A program whose last declaration returns forty-two.
const ANSWER: &str = "def answer : +U (-F Integer) ;\ndef answer = thunk { return 42 } ;\n";

/// A scratch source file, removed when dropped.
#[repr(transparent)]
struct Scratch(PathBuf);

impl Scratch
{
    /// `text` written to a file named for `test` and this process.
    ///
    /// # Specification
    /// - requires: the derived path has a writable parent and belongs only to
    ///   this fixture for its lifetime.
    /// - ensures: the returned path names a regular file containing `text`.
    /// - fails: never.
    /// - panics: if the file cannot be written.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — isolated value, shebang and refusal files are read
    ///   back through the script's source step and compared byte-for-byte with
    ///   their supplied text. These cases detect truncation or a wrong source,
    ///   not external interference or every filesystem failure.
    /// - witness: `tests::run::run_source_file_runs_a_script_file`
    /// - witness: `tests::run::run_source_file_accepts_an_executable_shebang_line`
    /// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
    #[spec(ensures: |ref ret| ret.0.metadata().is_ok_and(|metadata|
            metadata.is_file() && u64::try_from(text.as_ref().len())
                .is_ok_and(|offered| metadata.len() == offered)))]
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
    /// - requires: the fixture still exclusively owns its removable file.
    /// - ensures: the fixture's path no longer names a file.
    /// - fails: never.
    /// - panics: if the file cannot be removed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the value-file case retains its path across drop and
    ///   independently observes its absence afterward, detecting a skipped
    ///   removal on normal exit. Unwinding and external filesystem changes are
    ///   outside this witness.
    /// - witness: `tests::run::run_source_file_runs_a_script_file`
    #[spec(ensures: self.0.try_exists().is_ok_and(|exists| !exists))]
    fn drop(&mut self)
    {
        let removed = std::fs::remove_file(&self.0);
        assert!(removed.is_ok(), "the scratch source is removed");
    }
}

/// What running `text` with no file comes to.
///
/// # Specification
/// - requires: the built-in grammar builds and the fixture composes.
/// - ensures: returns the source's execution outcome; any evaluated target is
///   named in the supplied source.
/// - fails: never.
/// - panics: if grammar construction or composition fails.
///
/// # Adequacy
/// - hypothesis: L3 — an explicit forty-two program asserts its target and
///   value, while empty and refused sources assert their distinct outcomes.
///   This detects losing the selected target or collapsing those outcomes, not
///   arbitrary evaluation errors or parser recovery.
/// - witness: `tests::run::run_source_runs_source_text`
/// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
#[spec(ensures: |ref ret| match *ret {
        Ran::Evaluated { target, .. } | Ran::Entered { target, .. } => text.as_ref().contains(target.as_ref()),
        Ran::Refused | Ran::NoProgram => true,
    })]
fn ran_text(text: SourceText<'_>) -> Ran<'_>
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    let (_composed, ran) = run_source(&grammar, text, &mut lowerings, &mut Captured::default())
        .expect("the source composes");
    ran
}

/// Assert the file's complete source, path, execution and status.
///
/// # Specification
/// - requires: the fixture file is readable and composes as a module;
///   `expected_status` is the status of `expected`.
/// - ensures: returning establishes that the source step preserves `path` and
///   holds `expected_text` from its base, after the prelude, and its execution
///   equals both expectations.
/// - fails: never.
/// - panics: if the script does not produce that source and execution.
///
/// # Adequacy
/// - hypothesis: L3 literal status and source observations distinguish value,
///   refusal and empty programs and preserve the shebang's bytes; L2 comparison
///   with in-memory execution checks the two entry paths agree. Neither is an
///   independent evaluator for arbitrary programs.
/// - witness: `tests::run::run_source_file_runs_a_script_file`
/// - witness: `tests::run::run_source_file_accepts_an_executable_shebang_line`
/// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
#[spec(requires: expected.status() == expected_status)]
fn assert_runs_to(
    path: &Path,
    expected_text: SourceText<'_>,
    expected: &Ran<'_>,
    expected_status: RunStatus,
)
{
    let mut script = Script::new(path.to_path_buf());
    let actual = script.run(&mut Captured::default());
    assert_eq!(
        actual.status(),
        expected_status,
        "the script's status is preserved"
    );
    match actual {
        ScriptRun::Source {
            step:
                Step::Source {
                    path: observed_path,
                    text,
                    base,
                    composed: Composed::Settled { .. },
                    ..
                },
            ran,
        } => {
            assert_eq!(
                observed_path, path,
                "the source step names the supplied path"
            );
            assert_eq!(
                text.as_ref().get(usize::from(base) ..),
                Some(expected_text.as_ref()),
                "the complete file is retained as source, after the prelude"
            );
            assert_eq!(ran, *expected, "the file face runs as its text does");
        },
        other @ (ScriptRun::Fault { .. } | ScriptRun::Source { .. }) => {
            panic!("the script composes: {other:?}")
        },
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
            } if target.as_ref() == "answer" && value.as_ref() == "42"
        ),
        "a completed run returns the computed value: {ran:?}"
    );
}

/// A script file runs exactly as its source text does.
#[test]
fn run_source_file_runs_a_script_file()
{
    let script = Scratch::write(Path::new("value"), SourceText::from(ANSWER));
    assert_runs_to(
        &script.0,
        SourceText::from(ANSWER),
        &ran_text(SourceText::from(ANSWER)),
        RunStatus::Value,
    );
    let removed_path = script.0.clone();
    drop(script);
    assert!(removed_path.try_exists().is_ok_and(|exists| !exists));
}

/// A shebang line does not change what a script computes.
#[test]
fn run_source_file_accepts_an_executable_shebang_line()
{
    let shebang = format!("#!/usr/bin/env gandr\n{ANSWER}");
    let script = Scratch::write(Path::new("shebang"), SourceText::from(shebang.as_str()));
    assert_runs_to(
        &script.0,
        SourceText::from(shebang.as_str()),
        &ran_text(SourceText::from(ANSWER)),
        RunStatus::Value,
    );
}

/// #782: a script asked for ASCII writes the value it runs to in ASCII.
#[test]
fn a_script_runs_to_its_value_in_the_spelling_asked_782()
{
    let word = "data Circle : Type { Base : Circle; loop : Base <-> Base; }\ndef once : +U (-F \
                Path(Circle, Base, Base)) ;\ndef once = thunk { loop } ;\n";
    let file = Scratch::write(Path::new("spelling"), SourceText::from(word));
    for (spelling, spelled) in [
        (Spelling::Unicode, "loop ∷ here(Base)"),
        (Spelling::Ascii, "loop :: here(Base)"),
    ] {
        let mut script = Script::new(file.0.clone());
        script.spell_in(spelling);
        let run = script.run(&mut Captured::default());
        let ScriptRun::Source {
            ran:
                Ran::Evaluated {
                    evaluation: Evaluation::Value(ref value),
                    ..
                },
            ..
        } = run
        else {
            panic!("the word runs to a value: {run:?}");
        };
        assert_eq!(value.as_ref(), spelled, "the word in {spelling:?}");
    }
}

/// #2302: a script is laid after the prelude, so `==` between two strings
/// resolves the prelude's `EqString` and runs to whether they are the same
/// text; bare, `==` would be the integer primitive and refuse them.
#[test]
fn a_script_compares_through_the_prelude_s_eq_2302()
{
    for (test, compared, spelled) in [
        ("same", r#""types" == "types""#, "+{.0 = unit}"),
        ("different", r#""types" == "machines""#, "+{.1 = unit}"),
    ] {
        let text = format!("def compared() -> Bool {{ {compared} }}\n");
        let file = Scratch::write(
            Path::new(&format!("eq-2302-{test}")),
            SourceText::from(text.as_str()),
        );
        let mut script = Script::new(file.0.clone());
        let run = script.run(&mut Captured::default());
        let ScriptRun::Source {
            ran:
                Ran::Evaluated {
                    evaluation: Evaluation::Value(ref value),
                    ..
                },
            ..
        } = run
        else {
            panic!("`{compared}` runs to a value: {run:?}");
        };
        assert_eq!(value.as_ref(), spelled, "`{compared}`");
    }
}

/// #1881: a script's arguments reach its entry, which exits with their
/// number.
#[test]
fn a_script_passes_its_arguments_to_its_entry_1881()
{
    let counted = "def rec count(xs : List(String)) -> -F Integer {\n  case xs {\n    [] => 0,\n    \
                   [x, ..rest] => { run n <- count[<](rest); n + 1 }\n  }\n}\ndef main(args : \
                   List(String)) -> -F Integer { become count(args) }\n";
    let file = Scratch::write(Path::new("arguments"), SourceText::from(counted));
    for arguments in [vec![], vec![String::from("one"), String::from("two")]] {
        let mut script = Script::new(file.0.clone());
        let count = u8::try_from(arguments.len()).expect("a few arguments");
        script.pass(arguments);
        let run = script.run(&mut Captured::default());
        assert!(
            matches!(
                run,
                ScriptRun::Source {
                    ran: Ran::Entered {
                        entered: Entered::Exited(status),
                        ..
                    },
                    ..
                } if u8::from(status) == count
            ),
            "the entry exits with the number of its arguments: {run:?}"
        );
    }
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
    let run = script.run(&mut Captured::default());
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
        assert_runs_to(
            &script.0,
            SourceText::from(text),
            &failure,
            RunStatus::Unreached,
        );
    }
}
