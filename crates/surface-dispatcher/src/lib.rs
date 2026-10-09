//! Routes a driver invocation into the gandr surface pipeline, and composes
//! that pipeline: parse, lower, check, settle.
//!
//! The driver (`gandr-lang`) owns the argument surface and the process
//! boundary; this crate owns what happens after an invocation is understood.
//! An invocation enters as an [`Invocation`] and leaves as an [`Outcome`] the
//! driver renders.
//!
//! # Routing performs no I/O; the walk is the verb's
//!
//! [`dispatch`] reads no file and writes nothing. The `check` and `test` verbs
//! route to a [`Walk`] over the paths they were given, and the walk's I/O —
//! listing a directory, reading a source — happens one source at a time, as
//! the driver advances it with [`Walk::step`].
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

mod compose;
mod exercised;
mod report;
mod root;
mod walk;

use std::path::PathBuf;

pub use crate::compose::ComposeFault;
pub use crate::compose::Composed;
pub use crate::compose::LoweringCount;
pub use crate::compose::adapt;
pub use crate::compose::compose;
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
pub use crate::walk::SourceFault;
pub use crate::walk::Standing;
pub use crate::walk::Step;
pub use crate::walk::Walk;
pub use crate::walk::walk_step;

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
    },
    /// `test`: the same pass as `check`, reporting every fixture.
    Test
    {
        /// The sources and directories of sources to test, in order.
        paths: Vec<PathBuf>,
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
    },
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
///   under [`Verb::Test`], each walk over the invocation's paths in order.
///   Routing performs no I/O of its own: a walk reads nothing until it is
///   advanced, and building the grammar it parses with is computation. The
///   optional `tracing` feature reports a span to the caller's subscriber.
/// - provides: the outcome the driver renders.
/// - fails: never; routing is total over the invocation vocabulary.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 only — the decision surface is a three-variant match,
///   enumerated exhaustively with the exact outcome asserted, the walk's paths
///   observed through the order it visits them in.
/// - witness: `tests::status_routes_to_the_status_report`
/// - witness: `tests::check_routes_to_a_walk_under_the_check_verb`
/// - witness: `tests::the_test_verb_routes_to_a_walk`
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all))]
#[inline]
#[must_use]
pub fn dispatch(invocation: Invocation) -> Outcome
{
    match invocation {
        | Invocation::Status => Outcome::Status(StatusReport),
        | Invocation::Check { goals, paths } => Outcome::Run {
            verb: Verb::Check(goals),
            walk: Walk::new(paths),
        },
        | Invocation::Test { paths } => Outcome::Run {
            verb: Verb::Test,
            walk: Walk::new(paths),
        },
    }
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use quenchant_shape::shape::Maybe;

    use super::Goals;
    use super::Invocation;
    use super::Outcome;
    use super::StatusReport;
    use super::Step;
    use super::Verb;
    use super::dispatch;

    /// The first fault a walk over `paths` reports, which names the first path
    /// it visited when no path exists.
    ///
    /// # Specification
    ///
    /// trivial.
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
    }

    /// `check` keeps its goals setting and its paths' order.
    #[test]
    fn check_routes_to_a_walk_under_the_check_verb()
    {
        for goals in [Goals::Gated, Goals::Reported] {
            let paths = vec![
                PathBuf::from("no/such/first.gandr"),
                PathBuf::from("no/such/second.gandr"),
            ];
            let outcome = dispatch(Invocation::Check { goals, paths });
            assert!(
                matches!(outcome, Outcome::Run { verb: Verb::Check(routed), .. } if routed == goals),
                "check routes under its own goals setting"
            );
            assert_eq!(
                first_fault_path(outcome),
                PathBuf::from("no/such/first.gandr"),
                "the walk starts at the first path given"
            );
        }
    }

    /// `test` routes to a walk under the test verb.
    #[test]
    fn the_test_verb_routes_to_a_walk()
    {
        let outcome = dispatch(Invocation::Test {
            paths: vec![PathBuf::from("no/such/only.gandr")],
        });
        assert!(
            matches!(outcome, Outcome::Run {
                verb: Verb::Test,
                ..
            }),
            "test routes under the test verb"
        );
        assert_eq!(
            first_fault_path(outcome),
            PathBuf::from("no/such/only.gandr"),
            "the walk visits the path given"
        );
    }
}
