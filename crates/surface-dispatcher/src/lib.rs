//! Routes a driver invocation into the gandr surface pipeline, and composes
//! that pipeline: parse, lower, check, settle, and run.
//!
//! The driver (`gandr-lang`) owns the argument surface and the process
//! boundary; this crate owns what happens after an invocation is understood.
//! An invocation enters as an [`Invocation`] and leaves as an [`Outcome`] the
//! driver renders.
//!
//! # Routing performs no I/O; the walk is the verb's
//!
//! [`dispatch`] reads no file and writes nothing. The `check` and `test` verbs
//! route to a [`Walk`] over the paths they were given and the [`Width`] to
//! visit it at, and the walk's I/O — listing a directory, reading a source —
//! happens as the driver advances it with [`Walk::step`] or hands it a
//! visitor with [`Walk::visit`]. The `run` verb routes to a [`Script`], which
//! reads its one source when the driver runs it.
//!
//! # Sources fork; judgement keeps walk order
//!
//! At a width above one, [`Walk::visit`] parses and lowers the sources on a
//! pool of scoped threads, largest source first, and judges, settles and
//! reports them in walk order on the calling thread, so every count, verdict
//! and diagnostic is the serial walk's at every width. [`Width::SERIAL`] is
//! that serial walk, and the reference every wider one is tested against.
//!
//! # One composition serves both verbs
//!
//! [`compose()`] carries one source through the whole pipeline: it parses the
//! source, lowers the tree once, adapts the lowered declarations to the
//! checker's input, judges them, has the kernel re-derive every acceptance,
//! and settles each declaration against what it states. `check` and `test`
//! run that same function over the same walk and differ only in what they
//! print, so a source has one verdict per run whichever verb ran it.
//!
//! Its two halves are public: [`lower_source`] parses and lowers, and
//! [`judge_module`] judges, readmits and settles what the lowering read.
//! [`compose()`] is exactly the one then the other; the halves exist for the
//! session, which keeps the lowered module to hand the incremental checker
//! beside the verdicts.
//!
//! # The run stage follows the check
//!
//! [`judge_module`] also focuses every accepted declaration into the command
//! IL, and the [`Program`] it builds runs any declaration on the L machine and
//! reads its terminal back: the settle comparison runs the declarations that
//! state a `runs` outcome, the session runs what the user entered, and `gandr
//! run` runs the last name a source declares. Nothing runs that no caller
//! asked for, so `check` performs no run beyond the outcomes its sources
//! state.
//!
//! # Membership is location
//!
//! [`classify`] decides from a source's path alone which root it sits under:
//! the strict root, which holds every declaration to *checks, owing nothing*;
//! the fixture root, where expectations are admitted; or the fixture root's
//! pending set, whose sources carry a refusal no expectation can state.
//! A path under no root is strict.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.

extern crate alloc;

mod compose;
mod evaluate;
mod exercised;
mod report;
mod root;
mod script;
mod walk;
mod width;

use std::path::PathBuf;

use anodized::spec;

pub use crate::compose::ComposeFault;
pub use crate::compose::Composed;
pub use crate::compose::Lowered;
pub use crate::compose::Lowering;
pub use crate::compose::LoweringCount;
pub use crate::compose::adapt;
pub use crate::compose::compose;
pub use crate::compose::judge_module;
pub use crate::compose::lower_source;
pub use crate::evaluate::Evaluation;
pub use crate::evaluate::Program;
pub use crate::evaluate::RunStatus;
pub use crate::evaluate::Unfinished;
pub use crate::evaluate::Unrunnable;
pub use crate::evaluate::ValueSpelling;
pub use crate::evaluate::declaration_name;
pub use crate::evaluate::run_target;
pub use crate::exercised::Exercised;
pub use crate::exercised::Row;
pub use crate::report::Goals;
pub use crate::report::RunReport;
pub use crate::report::RunVerdict;
pub use crate::report::Shown;
pub use crate::report::SourceCount;
pub use crate::report::SourceCounts;
pub use crate::report::Verb;
pub use crate::report::shown;
pub use crate::root::SourceRoot;
pub use crate::root::classify;
pub use crate::script::Ran;
pub use crate::script::Script;
pub use crate::script::ScriptRun;
pub use crate::script::execute;
pub use crate::script::run_source;
pub use crate::walk::SourceFault;
pub use crate::walk::Standing;
pub use crate::walk::Step;
pub use crate::walk::Walk;
pub use crate::walk::walk_step;
pub use crate::width::Threads;
pub use crate::width::Width;

/// One understood driver invocation, ready to route.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Invocation
{
    /// A bare invocation: report the toolchain-management status.
    Status,
    /// `check`: settle every declaration of the sources under `paths`.
    Check
    {
        /// Whether an unsettled obligation fails the run or is reported as a
        /// goal.
        goals: Goals,
        /// The sources and directories of sources to check, in order.
        paths: Vec<PathBuf>,
        /// The threads the sources are parsed and lowered on.
        width: Width,
    },
    /// `test`: the same pass as `check`, reporting every fixture.
    Test
    {
        /// The sources and directories of sources to test, in order.
        paths: Vec<PathBuf>,
        /// The threads the sources are parsed and lowered on.
        width: Width,
    },
    /// `run`: run the program the source at `path` holds.
    Run
    {
        /// The source file.
        path: PathBuf,
    },
}

/// What an invocation routed to, for the driver to render.
#[expect(
    clippy::large_enum_variant,
    reason = "one outcome per process, moved once into the driver's renderer; boxing the walk \
              buys nothing"
)]
#[derive(Debug)]
pub enum Outcome
{
    /// The toolchain-management status report.
    Status(StatusReport),
    /// A walk over sources, run by `verb`.
    Run
    {
        /// The verb whose output and gate the walk is rendered under.
        verb: Verb,
        /// The walk, not yet started.
        walk: Walk,
        /// The width to visit the walk at.
        width: Width,
    },
    /// A source file to run as a program, not yet read.
    Script(Script),
}

/// The toolchain-management status, rendered by the driver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StatusReport;

impl core::fmt::Display for StatusReport
{
    /// Render the status line's message body.
    ///
    /// # Specification
    /// - requires: nothing; the report carries no state to render.
    /// - ensures: writes one sentence and no line terminator, so the driver
    ///   owns the line the message sits on.
    /// - provides: the body of the status line the driver prints on a bare
    ///   invocation.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes write status, not emitted
    ///   text, so the absence of a line terminator cannot be checked here.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the parameterless report is rendered without CR or
    ///   LF, distinguishing an extra line break. The wording and arbitrary
    ///   rejecting sinks are outside this observation.
    /// - witness: `tests::status_routes_to_the_status_report`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(
            "toolchain management is not yet implemented; see https://github.com/gandr-lang/gandr",
        )
    }
}

/// Route one invocation to its outcome.
///
/// # Specification
/// - requires: nothing; every [`Invocation`] variant routes.
/// - ensures: each variant maps to exactly one [`Outcome`] variant: a bare
///   invocation to the status report, `check` to a walk run under
///   [`Verb::Check`] with the same goals setting, and `test` to a walk run
///   under [`Verb::Test`], each walk over the invocation's paths in order at
///   the invocation's width; `run` to a [`Script`] of its path. Routing
///   performs no I/O of its own: a walk or a script reads nothing until it is
///   advanced, and building the grammar it parses with is computation. The
///   optional `tracing` feature reports a span to the caller's subscriber.
/// - provides: the outcome the driver renders.
/// - fails: never; routing is total over the invocation vocabulary.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — all four invocation variants and both goals policies have
///   exact outcomes. Missing-path fixtures observe the first routed path and
///   the script path; they do not enumerate arbitrary path lists or prove the
///   complete walk order, which has its own witnesses.
/// - witness: `tests::status_routes_to_the_status_report`
/// - witness: `tests::check_routes_to_a_walk_under_the_check_verb`
/// - witness: `tests::the_test_verb_routes_to_a_walk`
/// - witness: `tests::the_run_verb_routes_to_a_script`
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
#[inline]
#[must_use]
#[spec(
    captures: [
        status = matches!(invocation, Invocation::Status),
        verb = match &invocation {
            &Invocation::Check { goals, width, .. } => Some((Verb::Check(goals), width)),
            &Invocation::Test { width, .. } => Some((Verb::Test, width)),
            &Invocation::Status | &Invocation::Run { .. } => None,
        },
    ],
    ensures: |ref ret| match *ret {
        Outcome::Status(_) => status,
        Outcome::Run { verb: routed, width, .. } => Some((routed, width)) == verb,
        Outcome::Script(_) => !status && verb.is_none(),
    },
)]
pub fn dispatch(invocation: Invocation) -> Outcome
{
    match invocation {
        | Invocation::Status => Outcome::Status(StatusReport),
        | Invocation::Check {
            goals,
            paths,
            width,
        } => Outcome::Run {
            verb: Verb::Check(goals),
            walk: Walk::new(paths),
            width,
        },
        | Invocation::Test { paths, width } => Outcome::Run {
            verb: Verb::Test,
            walk: Walk::new(paths),
            width,
        },
        | Invocation::Run { path } => Outcome::Script(Script::new(path)),
    }
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use anodized::spec;
    use quenchant_shape::shape::Maybe;

    use super::Goals;
    use super::Invocation;
    use super::Outcome;
    use super::ScriptRun;
    use super::StatusReport;
    use super::Step;
    use super::Threads;
    use super::Verb;
    use super::Width;
    use super::dispatch;

    /// The first fault a walk over `paths` reports, which names the first path
    /// it visited when no path exists.
    ///
    /// # Specification
    /// - requires: a run outcome whose first step is a fault.
    /// - ensures: the path carried by that first fault.
    /// - fails: never on the admitted domain.
    /// - panics: a non-run outcome or non-fault first step violates the
    ///   precondition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — missing paths distinguish the first routed path under
    ///   both check policies and test. Other outcomes and successful first
    ///   steps are outside this helper's admitted domain.
    /// - witness: `tests::check_routes_to_a_walk_under_the_check_verb`
    /// - witness: `tests::the_test_verb_routes_to_a_walk`
    #[spec(requires: matches!(outcome, Outcome::Run { .. }))]
    fn first_fault_path(outcome: Outcome) -> PathBuf
    {
        let Outcome::Run { mut walk, .. } = outcome
        else {
            panic!("a verb routes to a walk");
        };
        let Maybe::Present(Step::Fault { path, .. }) = walk.step()
        else {
            panic!("an absent path faults");
        };
        path.to_path_buf()
    }

    /// A bare invocation routes to the status report.
    #[test]
    fn status_routes_to_the_status_report()
    {
        let outcome = dispatch(Invocation::Status);
        assert!(
            matches!(outcome, Outcome::Status(StatusReport)),
            "a bare invocation reports the status"
        );
        let rendered = std::format!("{StatusReport}");
        assert!(!rendered.contains(['\n', '\r']));
    }

    /// `check` keeps its goals setting, its width and its paths' order.
    #[test]
    fn check_routes_to_a_walk_under_the_check_verb()
    {
        let three = Width::Threads(Threads::from(
            core::num::NonZeroUsize::MIN.saturating_add(2),
        ));
        for (goals, width) in [(Goals::Gated, Width::SERIAL), (Goals::Reported, three)] {
            let paths = vec![
                PathBuf::from("no/such/first.gandr"),
                PathBuf::from("no/such/second.gandr"),
            ];
            let outcome = dispatch(Invocation::Check {
                goals,
                paths,
                width,
            });
            assert!(
                matches!(outcome, Outcome::Run { verb: Verb::Check(routed), width: routed_width, .. }
                    if routed == goals && routed_width == width),
                "check routes under its own goals setting and width"
            );
            assert_eq!(
                first_fault_path(outcome),
                PathBuf::from("no/such/first.gandr"),
                "the walk starts at the first path given"
            );
        }
    }

    /// `test` routes to a walk under the test verb, at its width.
    #[test]
    fn the_test_verb_routes_to_a_walk()
    {
        let outcome = dispatch(Invocation::Test {
            paths: vec![PathBuf::from("no/such/only.gandr")],
            width: Width::PerformanceCores,
        });
        assert!(
            matches!(outcome, Outcome::Run {
                verb: Verb::Test,
                width: Width::PerformanceCores,
                ..
            }),
            "test routes under the test verb at its width"
        );
        assert_eq!(
            first_fault_path(outcome),
            PathBuf::from("no/such/only.gandr"),
            "the walk visits the path given"
        );
    }

    /// `run` routes to a script of its one path.
    #[test]
    fn the_run_verb_routes_to_a_script()
    {
        let outcome = dispatch(Invocation::Run {
            path: PathBuf::from("no/such/script.gandr"),
        });
        let Outcome::Script(mut script) = outcome
        else {
            panic!("run routes to a script");
        };
        let ScriptRun::Fault { path, .. } = script.run()
        else {
            panic!("an absent script faults");
        };
        assert_eq!(
            path,
            PathBuf::from("no/such/script.gandr"),
            "the script reads the path given"
        );
    }
}
