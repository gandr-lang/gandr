//! The run verb: one source read as a program, and its last declaration run.
//!
//! # A script never reaches the machine with a refusal in it
//!
//! A source is composed exactly as `check` composes it, under the root its path
//! sits under, and is run only when no declaration of it was refused — by the
//! lowering, the checker or its root. A declaration owed its body is no
//! refusal: the run goes ahead, and is blamed on the goal if it reaches it.

use std::path::Path;
use std::path::PathBuf;

use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::produced_refusal;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::compose::ComposeFault;
use crate::compose::Composed;
use crate::compose::LoweringCount;
use crate::compose::compose;
use crate::evaluate::Evaluation;
use crate::evaluate::RunStatus;
use crate::evaluate::declaration_name;
use crate::walk::SourceFault;
use crate::walk::Standing;
use crate::walk::Step;
use crate::walk::read_source;

/// What running a composed source came to.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ran<'source>
{
    /// The source carries a refusal, or the lowering refused it as a whole:
    /// it never reached the machine.
    Refused,
    /// The source declares no name, so there is nothing to run.
    NoProgram,
    /// The source's last declared name, and what running it came to.
    Evaluated
    {
        /// The declaration run.
        target: SurfaceName<'source>,
        /// What the run came to.
        evaluation: Evaluation<'source>,
    },
}

impl Ran<'_>
{
    /// How the run went, as `gandr run`'s exit reports it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused source and a source with no program never reached
    ///   the machine, [`RunStatus::Unreached`]; an evaluated one has its
    ///   evaluation's status.
    /// - provides: the status the driver's exit code reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real values, blame, refusal, empty programs and an
    ///   unrunnable type distinguish the three statuses. These fixtures do not
    ///   enumerate every machine or readback failure.
    /// - witness: `script::tests::each_kind_of_source_has_its_status`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| match *self {
        Self::Refused | Self::NoProgram => matches!(ret, RunStatus::Unreached),
        Self::Evaluated { ref evaluation, .. } => matches!((evaluation.status(), ret),
            (RunStatus::Value, RunStatus::Value) | (RunStatus::Failed, RunStatus::Failed)
                | (RunStatus::Unreached, RunStatus::Unreached)),
    })]
    pub const fn status(&self) -> RunStatus
    {
        match *self {
            | Self::Refused | Self::NoProgram => RunStatus::Unreached,
            | Self::Evaluated { ref evaluation, .. } => evaluation.status(),
        }
    }
}

/// Run the program `composed` holds: its last declared name, unless a
/// declaration of it was refused.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a source the lowering refused whole, or holding a declaration
///   whose produced verdict is a refusal, is [`Ran::Refused`] and runs nothing;
///   a source declaring no name is [`Ran::NoProgram`]; otherwise its program's
///   run target is run once and [`Ran::Evaluated`] carries it.
/// - provides: the run step `gandr run` and [`run_source`] share.
/// - fails: never; every failure is a [`Ran`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a refused source, an empty program and a last named
///   target beside an unrelated goal have exact run outcomes. Value and blame
///   fixtures distinguish reaching the machine from refusal; arbitrary programs
///   and resource failures are outside this finite set.
/// - witness: `script::tests::each_kind_of_source_has_its_status`
#[inline]
#[anodized::spec(
    captures: [
        was_refused = match *composed {
            Composed::Refused(_) => true,
            Composed::Settled { ref report, .. } => report.declarations().iter()
                .any(|declaration| !matches!(declaration.produced().refusal(),
                    Maybe::Absent(produced_refusal::Absent::Unrefused))),
        },
        expected_target = match *composed {
            Composed::Settled { ref program, .. } => match program.target() {
                Maybe::Present(target) => match program.name(target) {
                    Maybe::Present(name) => Some(name),
                    Maybe::Absent(_) => None,
                },
                Maybe::Absent(_) => None,
            },
            Composed::Refused(_) => None,
        },
    ],
    ensures: |ref ret| match *ret {
        Ran::Refused => was_refused,
        Ran::NoProgram => !was_refused && expected_target.is_none(),
        Ran::Evaluated { target, .. } => !was_refused && expected_target == Some(target),
    },
)]
pub fn execute<'source>(composed: &mut Composed<'source>) -> Ran<'source>
{
    let Composed::Settled {
        ref report,
        ref mut program,
        ..
    } = *composed
    else {
        return Ran::Refused;
    };
    let refused = report.declarations().iter().any(|declaration| {
        !matches!(
            declaration.produced().refusal(),
            Maybe::Absent(produced_refusal::Absent::Unrefused)
        )
    });
    if refused {
        return Ran::Refused;
    }
    let Maybe::Present(target) = program.target()
    else {
        return Ran::NoProgram;
    };
    match program.name(target) {
        | Maybe::Present(name) => Ran::Evaluated {
            target: name,
            evaluation: program.evaluate(target),
        },
        | Maybe::Absent(declaration_name::Absent::Undeclared) => Ran::NoProgram,
    }
}

/// Compose `source` under the strict root, as a source at no path, and run
/// its program.
///
/// # Specification
/// - requires: `grammar` is the checked grammar the source is parsed under.
/// - ensures: composes under the strict root, then executes the resulting
///   program. Once parsing succeeds, the lowering count increases by one with
///   saturation; a parse refusal leaves it unchanged.
/// - provides: the run of source text, with no file.
/// - fails: as [`compose()`](crate::compose()).
/// - panics: none.
///
/// # Errors
/// The [`ComposeFault`] [`compose()`](crate::compose()) meets.
///
/// # Adequacy
/// - hypothesis: L3 — a real computation runs to its value and successive
///   empty-program compositions reach and remain at the maximum lowering count.
///   The parse-error counter branch is stated by the predicate, not
///   independently triggered by these valid built-in-grammar fixtures.
/// - witness: `run::run::run_source_runs_source_text`
/// - witness: `script::tests::run_source_counts_lowerings_with_saturation`
#[inline]
#[anodized::spec(
    captures: [before = usize::from(*lowerings)],
    ensures: |ref ret| usize::from(*lowerings) == if matches!(*ret, Err(ComposeFault::Parse(_))) {
        before
    } else { before.saturating_add(1_usize) },
)]
pub fn run_source<'source>(
    grammar: &Pbg,
    source: SourceText<'source>,
    lowerings: &mut LoweringCount,
) -> Result<(Composed<'source>, Ran<'source>), ComposeFault<'source>>
{
    let mut composed = compose(grammar, CorpusRoot::Strict, source, lowerings)?;
    let ran = execute(&mut composed);
    Ok((composed, ran))
}

/// What running a script came to.
#[derive(Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "a script yields one run, which the driver consumes in place; boxing the step would allocate to shrink a value that is never stored"
)]
pub enum ScriptRun<'script>
{
    /// The path could not be read as one source: it is absent, a directory or
    /// not UTF-8, or the pipeline faulted on it.
    Fault
    {
        /// The path given.
        path: &'script Path,
        /// Why.
        fault: SourceFault<'script>,
    },
    /// The source, read and composed as a walk step, and its run.
    Source
    {
        /// The step a `check` of the path would yield.
        step: Step<'script>,
        /// What running it came to.
        ran: Ran<'script>,
    },
}

impl ScriptRun<'_>
{
    /// How the run went, as `gandr run`'s exit reports it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fault never reached the machine, [`RunStatus::Unreached`];
    ///   a source has its run's status.
    /// - provides: the status the driver's exit code reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an absent path directly observes the fault status;
    ///   file-backed value and refusal runs observe the source status. These
    ///   are finite examples, not every nested evaluation failure.
    /// - witness: `run::run::run_source_file_reports_the_path_of_an_absent_file`
    /// - witness: `run::run::run_source_file_runs_a_script_file`
    /// - witness: `run::run::run_source_file_surfaces_a_source_failure_unchanged`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| match *self {
        Self::Fault { .. } => matches!(ret, RunStatus::Unreached),
        Self::Source { ref ran, .. } => matches!((ran.status(), ret),
            (RunStatus::Value, RunStatus::Value) | (RunStatus::Failed, RunStatus::Failed)
                | (RunStatus::Unreached, RunStatus::Unreached)),
    })]
    pub const fn status(&self) -> RunStatus
    {
        match *self {
            | Self::Fault { .. } => RunStatus::Unreached,
            | Self::Source { ref ran, .. } => ran.status(),
        }
    }
}

/// One source file to run as a program.
#[derive(Debug)]
pub struct Script
{
    /// The grammar the source is parsed under, built once.
    grammar: Result<Pbg, PbgError>,
    /// The source's path.
    path: PathBuf,
    /// The source's text, once read.
    text: String,
    /// The lowerings the script has run.
    lowerings: LoweringCount,
}

impl Script
{
    /// A script of the source at `path`, nothing yet read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(path: PathBuf) -> Self
    {
        Self {
            grammar: built_in(),
            path,
            text: String::new(),
            lowerings: LoweringCount::default(),
        }
    }

    /// Read the source, compose it as `check` would, and run its program.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the path is classified by its canonical path and read whole;
    ///   a path that cannot be — absent, a directory, not UTF-8 — is a
    ///   [`SourceFault::Unreadable`], a grammar that did not build a
    ///   [`SourceFault::Grammar`], and a pipeline fault a
    ///   [`SourceFault::Compose`], each naming the path given. Otherwise the
    ///   source is composed under its root, its step built as a walk builds it,
    ///   and [`execute`] runs it.
    /// - provides: `gandr run`.
    /// - fails: never; every failure is a [`ScriptRun`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real file, shebang, missing-file and source-refusal
    ///   fixtures assert their paths and outcomes. L2 comparisons with the same
    ///   in-memory source cover pipeline agreement, not an independent oracle
    ///   for arbitrary programs or all filesystem failures.
    /// - witness: `run::run::run_source_file_runs_a_script_file`
    /// - witness: `run::run::run_source_file_accepts_an_executable_shebang_line`
    /// - witness: `run::run::run_source_file_reports_the_path_of_an_absent_file`
    /// - witness: `run::run::run_source_file_surfaces_a_source_failure_unchanged`
    #[inline]
    #[anodized::spec(
        captures: [expected_path = self.path.as_path()],
        ensures: |ref ret| match *ret {
            ScriptRun::Fault { path, .. } => path == expected_path,
            ScriptRun::Source { step: Step::Source { path, root, ref composed, standing, .. }, .. } =>
                path == expected_path && standing == Standing::of(root, composed),
            ScriptRun::Source { step: Step::Fault { .. }, .. } => false,
        },
    )]
    pub fn run(&mut self) -> ScriptRun<'_>
    {
        let root = match read_source(&self.path, &mut self.text) {
            | Ok(root) => root,
            | Err(error) => {
                return ScriptRun::Fault {
                    path: &self.path,
                    fault: SourceFault::Unreadable(error),
                };
            },
        };
        let grammar = match self.grammar {
            | Ok(ref grammar) => grammar,
            | Err(ref error) => {
                return ScriptRun::Fault {
                    path: &self.path,
                    fault: SourceFault::Grammar(error),
                };
            },
        };
        let source = SourceText::from(self.text.as_str());
        match compose(grammar, root.corpus_root(), source, &mut self.lowerings) {
            | Ok(mut composed) => {
                let ran = execute(&mut composed);
                let standing = Standing::of(root, &composed);
                ScriptRun::Source {
                    step: Step::Source {
                        path: &self.path,
                        root,
                        text: source,
                        composed,
                        standing,
                    },
                    ran,
                }
            },
            | Err(fault) => ScriptRun::Fault {
                path: &self.path,
                fault: SourceFault::Compose(fault),
            },
        }
    }
}

#[cfg(test)]
mod tests
{
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::SourceText;

    use super::Ran;
    use super::run_source;
    use crate::compose::LoweringCount;
    use crate::evaluate::Evaluation;
    use crate::evaluate::RunStatus;

    #[test]
    fn each_kind_of_source_has_its_status()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let rows = [
            (
                r#"def later : Integer ; def answer : Integer ; def answer = 42 ;"#,
                RunStatus::Value,
            ),
            (
                r#"def later : +U (-F Integer) ; def main : +U (-F Integer) ; def main = thunk { force later } ;"#,
                RunStatus::Failed,
            ),
            (
                r#"def answer : Integer ; def answer = "forty-two" ;"#,
                RunStatus::Unreached,
            ),
            (r#"// nothing to run"#, RunStatus::Unreached),
            (
                r#"def code : Type ; def code = Integer ;"#,
                RunStatus::Unreached,
            ),
        ];
        for (source, status) in rows {
            let mut lowerings = LoweringCount::default();
            let (_composed, ran) = run_source(&grammar, SourceText::from(source), &mut lowerings)
                .expect("the source composes");
            assert_eq!(ran.status(), status, "`{source}` runs as pinned: {ran:?}");
        }

        let mut lowerings = LoweringCount::default();
        let (_composed, ran) = run_source(
            &grammar,
            SourceText::from(r#"def answer : Integer ; def answer = "forty-two" ;"#),
            &mut lowerings,
        )
        .expect("the source composes");
        assert_eq!(ran, Ran::Refused, "a refused source runs nothing");
        let (_composed, ran) = run_source(
            &grammar,
            SourceText::from(r#"// nothing to run"#),
            &mut lowerings,
        )
        .expect("the source composes");
        assert_eq!(ran, Ran::NoProgram, "a source of no name has no program");
        let (_composed, ran) = run_source(
            &grammar,
            SourceText::from(r#"def later : Integer ; def answer : Integer ; def answer = 42 ;"#),
            &mut lowerings,
        )
        .expect("the source composes");
        let Ran::Evaluated { target, evaluation } = ran
        else {
            panic!("a runnable source is evaluated");
        };
        assert_eq!(
            (target.as_ref(), evaluation.to_string()),
            ("answer", String::from("42")),
            "the last name declared runs, beside a goal it does not reach"
        );
        assert!(
            matches!(evaluation, Evaluation::Value(_)),
            "the run returned a value"
        );
    }

    #[test]
    fn run_source_counts_lowerings_with_saturation()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let mut lowerings = LoweringCount::from(usize::MAX.saturating_sub(1));
        for _ in 0_usize .. 2 {
            let (_, ran) = run_source(
                &grammar,
                SourceText::from("// nothing to run"),
                &mut lowerings,
            )
            .expect("an empty program composes");
            assert_eq!(Ran::NoProgram, ran);
            assert_eq!(usize::MAX, usize::from(lowerings));
        }
    }
}
