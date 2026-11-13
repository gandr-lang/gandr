//! The run verb's script: each kind of source runs to its status, a `main`
//! is entered, and the lowering count saturates (#7048 moves these from the
//! `script` module, since each run names the run stage's engine).

use gandr_surface_dispatcher::Captured;
use gandr_surface_dispatcher::Entered;
use gandr_surface_dispatcher::ExitStatus;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Ran;
use gandr_surface_dispatcher::RunStatus;
use gandr_surface_dispatcher::run_source;
use gandr_surface_evaluate::Evaluator;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;

#[test]
fn each_kind_of_source_has_its_status()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let rows = [
        (r#"def main() -> -F Integer { return 0 }"#, RunStatus::Value),
        (
            r#"def later : +U (-F Integer) ; def main : +U (-F Integer) ; def main = thunk { become force later } ;"#,
            RunStatus::Failed,
        ),
        (
            r#"def answer : Integer ; def answer = "forty-two" ;"#,
            RunStatus::Unreached,
        ),
        (r#"// nothing to run"#, RunStatus::Unreached),
        (
            r#"def later : Integer ; def answer : Integer ; def answer = 42 ;"#,
            RunStatus::Unreached,
        ),
    ];
    for (source, status) in rows {
        let mut lowerings = LoweringCount::default();
        let (_composed, ran) = run_source::<Evaluator>(
            &grammar,
            SourceText::from(source),
            &mut lowerings,
            &mut Captured::default(),
        )
        .expect("the source composes");
        assert_eq!(ran.status(), status, "`{source}` runs as pinned: {ran:?}");
    }

    let mut lowerings = LoweringCount::default();
    let (_composed, ran) = run_source::<Evaluator>(
        &grammar,
        SourceText::from(r#"def answer : Integer ; def answer = "forty-two" ;"#),
        &mut lowerings,
        &mut Captured::default(),
    )
    .expect("the source composes");
    assert_eq!(ran, Ran::Refused, "a refused source runs nothing");
    for source in [
        r#"// nothing to run"#,
        r#"def later : Integer ; def answer : Integer ; def answer = 42 ;"#,
    ] {
        let (_composed, ran) = run_source::<Evaluator>(
            &grammar,
            SourceText::from(source),
            &mut lowerings,
            &mut Captured::default(),
        )
        .expect("the source composes");
        assert_eq!(
            ran,
            Ran::NoProgram,
            "a source declaring no `main` runs nothing, not its last declaration: `{source}`"
        );
    }
}

/// A source declaring `main` runs it, not its last declaration, and exits
/// with its integer; an entry reaching a goal ends with the status of its
/// evaluation (#1881).
#[test]
fn a_source_declaring_main_runs_its_entry_1881()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    let (_composed, ran) = run_source::<Evaluator>(
        &grammar,
        SourceText::from(include_str!(
            "script/fixtures/a-source-declaring-main-runs-its-entry-1881.gandr"
        )),
        &mut lowerings,
        &mut Captured::default(),
    )
    .expect("the source composes");
    let Ran::Entered { target, entered } = ran
    else {
        panic!("a source declaring `main` enters it: {ran:?}");
    };
    assert_eq!(
        (target.as_ref(), entered),
        ("main", Entered::Exited(ExitStatus::from(3_u8))),
        "the entry runs and its integer is the status"
    );
    let (_composed, ran) = run_source::<Evaluator>(
        &grammar,
        SourceText::from("def main() -> -F Integer { ? }\n"),
        &mut lowerings,
        &mut Captured::default(),
    )
    .expect("the source composes");
    let Ran::Entered {
        entered: Entered::Ended(ref evaluation),
        ..
    } = ran
    else {
        panic!("an entry at a goal ends short of a status: {ran:?}");
    };
    assert_eq!(ran.status(), evaluation.status());
    assert_ne!(ran.status(), RunStatus::Value);
}

#[test]
fn run_source_counts_lowerings_with_saturation()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::from(usize::MAX.saturating_sub(1));
    for _ in 0_usize .. 2 {
        let (_, ran) = run_source::<Evaluator>(
            &grammar,
            SourceText::from("// nothing to run"),
            &mut lowerings,
            &mut Captured::default(),
        )
        .expect("an empty program composes");
        assert_eq!(Ran::NoProgram, ran);
        assert_eq!(usize::MAX, usize::from(lowerings));
    }
}
