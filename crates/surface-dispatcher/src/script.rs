//! The run verb: one source read as a program, and its entry run — the `main`
//! it declares at its top level. A source declaring no `main` runs nothing: a
//! source of declarations alone is checked or tested, not run. The host verb
//! reads a source the same way and hosts its worlds: each migration another
//! host ships to a world its bindings bind here runs here.
//!
//! # A script never reaches the machine with a refusal in it
//!
//! A source is composed exactly as `check` composes it — laid after the
//! prelude, under the root its path sits under — and is run only when no
//! declaration of it was refused — by the lowering, the checker or its root. A
//! declaration owed its body is no refusal: the run goes ahead, and is blamed
//! on the goal if it reaches it.

use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_runtime_net::Net;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::produced_refusal;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::HostGrant;
use crate::component::Laid;
use crate::compose::ComposeFault;
use crate::compose::Composed;
use crate::compose::LoweringCount;
use crate::compose::compose;
use crate::compose::judge_lowering;
use crate::compose::lower_unit_source;
use crate::evaluate::Console;
use crate::evaluate::Entered;
use crate::evaluate::Entry;
use crate::evaluate::Hosted;
use crate::evaluate::MigrationCount;
use crate::evaluate::ProgramKey;
use crate::evaluate::RunStatus;
use crate::evaluate::WorldBindings;
use crate::evaluate::Worlds;
use crate::evaluate::declaration_name;
use crate::reader::Reader;
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
    /// The source declares no `main` at its top level, so there is nothing
    /// to run.
    NoProgram,
    /// The source's entry, and what running it came to.
    Entered
    {
        /// The entry run.
        target: SurfaceName<'source>,
        /// What the run came to.
        entered: Entered<'source>,
    },
    /// The source's worlds were hosted, and what hosting them came to.
    Hosted(Hosted),
}

impl Ran<'_>
{
    /// How the run went, as `gandr run`'s exit reports it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused source and a source with no program never reached
    ///   the machine, [`RunStatus::Unreached`]; an entry that exited is
    ///   [`RunStatus::Value`], and one that ended short of a status has its
    ///   evaluation's; hosting that answered every migration asked for is
    ///   [`RunStatus::Value`], and hosting the network ended first
    ///   [`RunStatus::Failed`].
    /// - provides: the status the driver's exit code reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refusal, a source declaring no `main`, an entry
    ///   exiting and an entry reaching a goal distinguish the statuses. These
    ///   fixtures do not enumerate every machine or readback failure.
    /// - witness: `script::tests::each_kind_of_source_has_its_status`
    /// - witness: `script::tests::a_source_declaring_main_runs_its_entry_1881`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match *self {
        Self::Refused | Self::NoProgram => matches!(ret, RunStatus::Unreached),
        Self::Entered { entered: Entered::Exited(_), .. } | Self::Hosted(Hosted::Answered(_)) => matches!(ret, RunStatus::Value),
        Self::Hosted(Hosted::Faulted { .. }) => matches!(ret, RunStatus::Failed),
        Self::Entered { entered: Entered::Ended(ref evaluation), .. } => matches!((evaluation.status(), ret),
            (RunStatus::Value, RunStatus::Value) | (RunStatus::Failed, RunStatus::Failed)
                | (RunStatus::Unreached, RunStatus::Unreached)),
    })]
    pub const fn status(&self) -> RunStatus
    {
        match *self {
            Self::Refused | Self::NoProgram => RunStatus::Unreached,
            Self::Entered {
                entered: Entered::Exited(_),
                ..
            }
            | Self::Hosted(Hosted::Answered(_)) => RunStatus::Value,
            Self::Hosted(Hosted::Faulted { .. }) => RunStatus::Failed,
            Self::Entered {
                entered: Entered::Ended(ref evaluation),
                ..
            } => evaluation.status(),
        }
    }
}

/// Run the program `composed` holds, its entry given `arguments`, unless a
/// declaration of it was refused.
///
/// Each line it prints is handed to `console`, each `Net` operation is
/// served on `net` when it is given, and each migration runs where `worlds`'
/// bindings bind its world when it is given.
///
/// # Specification
/// - requires: `worlds` holds the key of the text `composed` was composed from.
/// - ensures: a source the lowering refused whole, or holding a declaration
///   whose produced verdict is a refusal, is [`Ran::Refused`] and runs nothing;
///   a source declaring no `main` at its top level is [`Ran::NoProgram`] and
///   runs nothing, its last declaration included; a program with an entry
///   enters it once with `arguments`, writing each line it prints to `console`,
///   in order, serving its `Net` operations on `net` and its migrations as
///   `worlds` binds them, and [`Ran::Entered`] carries it.
/// - provides: the run step `gandr run` and [`run_source`] share.
/// - fails: never; every failure is a [`Ran`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a refused source, a source of declarations and no `main`,
///   an empty source and an entry declared before another name have exact run
///   outcomes; arbitrary programs and resource failures are outside this finite
///   set.
/// - witness: `script::tests::each_kind_of_source_has_its_status`
/// - witness: `script::tests::a_source_declaring_main_runs_its_entry_1881`
#[inline]
#[spec(
    captures: [
        was_refused = match *composed {
            Composed::Refused(_) => true,
            Composed::Settled { ref report, .. } => report.declarations().iter()
                .any(|declaration| !matches!(declaration.produced().refusal(),
                    Maybe::Absent(produced_refusal::Absent::Unrefused))),
        },
        expected_entry = match *composed {
            Composed::Settled { ref program, .. } => match program.entry() {
                Maybe::Present(Entry { constant, .. }) => match program.name(constant) {
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
        Ran::NoProgram => !was_refused && expected_entry.is_none(),
        Ran::Entered { target, .. } => !was_refused && expected_entry == Some(target),
        Ran::Hosted(_) => false,
    },
)]
pub fn execute<'source>(
    composed: &mut Composed<'source>,
    arguments: &[String],
    console: &mut dyn Console,
    (net, worlds): (Option<&mut Net>, Option<Worlds<'_>>),
) -> Ran<'source>
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
    let Maybe::Present(entry) = program.entry()
    else {
        return Ran::NoProgram;
    };
    match program.name(entry.constant) {
        Maybe::Present(name) => Ran::Entered {
            target: name,
            entered: program.enter(entry, arguments, console, (net, worlds)),
        },
        Maybe::Absent(declaration_name::Absent::Undeclared) => Ran::NoProgram,
    }
}

/// Host the worlds of the program `composed` holds on `net`, unless a
/// declaration of it was refused.
///
/// It answers `migrations` migrations shipped to it, each as `worlds`'
/// bindings decide, and prints a line for each on `console`.
///
/// # Specification
/// - requires: `worlds` holds the key of the text `composed` was composed from.
/// - ensures: a refused source is [`Ran::Refused`] and hosts nothing; otherwise
///   [`Ran::Hosted`] with what [`Program::host`] came to.
/// - fails: never; every failure is a [`Ran`].
/// - panics: none.
/// - executable: none — the migrations are the askers', across the network.
///
/// # Adequacy
/// - hypothesis: L3 — two hosts in turn each host two migrations of one run and
///   print a line for each.
/// - witness: `tests::run::a_second_migration_of_an_edited_list_fetches_what_changed_3365`
///
/// [`Program::host`]: crate::Program::host
#[inline]
pub fn host<'source>(
    composed: &Composed<'source>,
    (net, worlds): (&mut Net, Worlds<'_>),
    migrations: MigrationCount,
    console: &mut dyn Console,
) -> Ran<'source>
{
    let Composed::Settled {
        ref report,
        ref program,
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
    Ran::Hosted(program.host(worlds, net, migrations, console))
}

/// Compose `source` under the strict root, as a source at no path, and run
/// its program, its entry given no arguments, each line it prints handed to
/// `console`.
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
/// - hypothesis: L3 — an entry runs to its exit status and successive
///   empty-program compositions reach and remain at the maximum lowering count.
///   The parse-error counter branch is stated by the predicate, not
///   independently triggered by these valid built-in-grammar fixtures.
/// - witness: `tests::run::run_source_runs_source_text`
/// - witness: `script::tests::run_source_counts_lowerings_with_saturation`
#[inline]
#[spec(
    captures: [before = usize::from(*lowerings)],
    ensures: |ref ret| usize::from(*lowerings) == if matches!(*ret, Err(ComposeFault::Parse(_))) {
        before
    } else { before.saturating_add(1_usize) },
)]
pub fn run_source<'source>(
    grammar: &Pbg,
    source: SourceText<'source>,
    lowerings: &mut LoweringCount,
    console: &mut dyn Console,
) -> Result<(Composed<'source>, Ran<'source>), ComposeFault<'source>>
{
    let mut composed = compose(grammar, CorpusRoot::Strict, source, lowerings)?;
    let ran = execute(&mut composed, &[], console, (None, None));
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
    /// - witness: `tests::run::run_source_file_reports_the_path_of_an_absent_file`
    /// - witness: `tests::run::run_source_file_runs_a_script_file`
    /// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match *self {
        Self::Fault { .. } => matches!(ret, RunStatus::Unreached),
        Self::Source { ref ran, .. } => matches!((ran.status(), ret),
            (RunStatus::Value, RunStatus::Value) | (RunStatus::Failed, RunStatus::Failed)
                | (RunStatus::Unreached, RunStatus::Unreached)),
    })]
    pub const fn status(&self) -> RunStatus
    {
        match *self {
            Self::Fault { .. } => RunStatus::Unreached,
            Self::Source { ref ran, .. } => ran.status(),
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
    /// The reader the source is read through.
    reader: Reader,
    /// The source's text, once read.
    text: String,
    /// The source laid after the prelude, once read.
    laid: Option<Laid>,
    /// The lowerings the script has run.
    lowerings: LoweringCount,
    /// The arguments its entry is given.
    arguments: Vec<String>,
    /// The network its entry's `Net` operations are served on, when it has
    /// one; boxed, since a network outweighs the rest of a script.
    net: Option<Box<Net>>,
    /// The world bindings its migrations go where they bind them by, when it
    /// has them.
    bindings: Option<WorldBindings>,
    /// How many migrations it hosts instead of running its entry, when it
    /// hosts.
    hosting: Option<MigrationCount>,
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
            reader: Reader::new(),
            text: String::new(),
            laid: None,
            lowerings: LoweringCount::default(),
            arguments: Vec::new(),
            net: None,
            bindings: None,
            hosting: None,
        }
    }

    /// This script, its entry given `arguments`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a later [`Self::run`] gives a program's entry `arguments`, in
    ///   their order; a program with no entry runs as it did.
    /// - provides: the arguments `gandr run` passes after the path.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — what the arguments do is observed by the later run;
    ///   the store itself is a move.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a script whose entry counts its arguments exits with
    ///   their number.
    /// - witness: `tests::run::a_script_passes_its_arguments_to_its_entry_1881`
    #[inline]
    pub fn pass(
        &mut self,
        arguments: Vec<String>,
    )
    {
        self.arguments = arguments;
    }

    /// This script, its entry's `Net` operations served on `net`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a later [`Self::run`] serves each `Net` operation its entry
    ///   performs on `net`; without a network a script declines them.
    /// - provides: the network `gandr run` binds as its flags say.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — what the network serves is observed by the later
    ///   run; the store itself is a move.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the ping exemplar, given its network, dials an
    ///   endpoint on loopback and prints the answer it reads back.
    /// - witness: `tests::run::a_script_pings_over_its_network_3186`
    #[inline]
    pub fn network(
        &mut self,
        net: Net,
    )
    {
        self.net = Some(Box::new(net));
    }

    /// This script, its migrations run where `bindings` bind their worlds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a later [`Self::run`] runs each migration where `bindings`
    ///   bind its world, and refuses an entry that may migrate to a world no
    ///   binding names; without bindings every migration runs here.
    /// - provides: the world bindings `gandr run` and `gandr host` read from
    ///   their `--world` flags.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — what the bindings decide is observed by the later
    ///   run; the store itself is a move.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a script whose bindings bind its world to a hosting
    ///   endpoint answers there; one binding it to itself runs here; one
    ///   binding another world is refused before it runs.
    /// - witness: `tests::run::a_second_migration_of_an_edited_list_fetches_what_changed_3365`
    /// - witness: `tests::run::a_world_bound_to_this_host_runs_here`
    /// - witness: `tests::run::a_world_no_binding_names_is_refused_before_the_run`
    #[inline]
    pub fn bindings(
        &mut self,
        bindings: WorldBindings,
    )
    {
        self.bindings = Some(bindings);
    }

    /// This script, hosting `migrations` migrations of its worlds instead of
    /// running its entry.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a later [`Self::run`] hosts `migrations` migrations on the
    ///   script's network, as its bindings decide each; without a network it
    ///   hosts none.
    /// - provides: `gandr host`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — what hosting answers is observed by the later run;
    ///   the store itself is a move.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two hosts in turn each host two migrations.
    /// - witness: `tests::run::a_second_migration_of_an_edited_list_fetches_what_changed_3365`
    #[inline]
    pub fn hosting(
        &mut self,
        migrations: MigrationCount,
    )
    {
        self.hosting = Some(migrations);
    }

    /// Read the source, compose it as `check` would, and run its program,
    /// each line it prints handed to `console`, each `Net` operation served
    /// on the script's network and each migration sent where its bindings
    /// bind the world; or, for a script that hosts, host its worlds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the path is classified by its canonical path and read whole;
    ///   a path that cannot be — absent, a directory, not UTF-8 — is a
    ///   [`SourceFault::Unreadable`], a grammar that did not build a
    ///   [`SourceFault::Grammar`], and a pipeline fault a
    ///   [`SourceFault::Compose`], each naming the path given. Otherwise the
    ///   source is laid after the prelude alone, composed under its root, its
    ///   step built as a walk builds it, and [`execute`] runs it, its entry
    ///   given the script's arguments, its network and its bindings keyed by
    ///   the laid text; a script that hosts is [`host`]ed instead, and one with
    ///   no network or bindings hosts nothing.
    /// - provides: `gandr run`.
    /// - fails: never; every failure is a [`ScriptRun`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real file, shebang, missing-file and source-refusal
    ///   fixtures assert their paths and outcomes. L2 comparisons with the same
    ///   in-memory source cover pipeline agreement, not an independent oracle
    ///   for arbitrary programs or all filesystem failures.
    /// - witness: `tests::run::run_source_file_runs_a_script_file`
    /// - witness: `tests::run::a_script_compares_through_the_prelude_s_eq_2302`
    /// - witness: `tests::run::run_source_file_accepts_an_executable_shebang_line`
    /// - witness: `tests::run::run_source_file_reports_the_path_of_an_absent_file`
    /// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
    #[inline]
    #[spec(
        captures: [expected_path = self.path.as_path()],
        ensures: |ref ret| match *ret {
            ScriptRun::Fault { path, .. } => path == expected_path,
            ScriptRun::Source { step: Step::Source { path, root, ref composed, standing, .. }, .. } =>
                path == expected_path && standing == Standing::of(root, composed),
            ScriptRun::Source { step: Step::Fault { .. }, .. } => false,
        },
    )]
    pub fn run(
        &mut self,
        console: &mut dyn Console,
    ) -> ScriptRun<'_>
    {
        let root = match read_source(&self.reader, &self.path, &mut self.text) {
            Ok(root) => root,
            Err(error) => {
                return ScriptRun::Fault {
                    path: &self.path,
                    fault: SourceFault::Unreadable(error),
                };
            },
        };
        let grammar = match self.grammar {
            Ok(ref grammar) => grammar,
            Err(ref error) => {
                return ScriptRun::Fault {
                    path: &self.path,
                    fault: SourceFault::Grammar(error),
                };
            },
        };
        let laid = &*self.laid.insert(Laid::alone(
            &self.path,
            SourceText::from(self.text.as_str()),
            (Vec::new(), Vec::new()),
        ));
        let source = SourceText::from(laid.text.as_str());
        let composed = lower_unit_source(grammar, source, &laid.unit, &mut self.lowerings)
            .and_then(|lowering| {
                judge_lowering(
                    root.corpus_root(),
                    (lowering, source),
                    &HostGrant::UNBOUNDED,
                    laid.base,
                )
            });
        match composed {
            Ok(mut composed) => {
                let worlds = self.bindings.as_ref().map(|bindings| Worlds {
                    bindings,
                    program: ProgramKey::of(source),
                });
                let net = self.net.as_deref_mut();
                let ran = match (self.hosting, net, worlds) {
                    (Some(migrations), Some(net), Some(worlds)) => {
                        host(&composed, (net, worlds), migrations, console)
                    },
                    (Some(_), ..) => Ran::Hosted(Hosted::Faulted {
                        answered: MigrationCount::default(),
                    }),
                    (None, net, worlds) => {
                        execute(&mut composed, &self.arguments, console, (net, worlds))
                    },
                };
                let standing = Standing::of(root, &composed);
                ScriptRun::Source {
                    step: Step::Source {
                        path: &self.path,
                        root,
                        text: source,
                        base: laid.base,
                        composed,
                        standing,
                    },
                    ran,
                }
            },
            Err(fault) => ScriptRun::Fault {
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
    use crate::evaluate::Captured;
    use crate::evaluate::Entered;
    use crate::evaluate::ExitStatus;
    use crate::evaluate::RunStatus;

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
            let (_composed, ran) = run_source(
                &grammar,
                SourceText::from(source),
                &mut lowerings,
                &mut Captured::default(),
            )
            .expect("the source composes");
            assert_eq!(ran.status(), status, "`{source}` runs as pinned: {ran:?}");
        }

        let mut lowerings = LoweringCount::default();
        let (_composed, ran) = run_source(
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
            let (_composed, ran) = run_source(
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
        let (_composed, ran) = run_source(
            &grammar,
            SourceText::from("def main() -> -F Integer { return 3 }\ndef later = 1 ;\n"),
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
        let (_composed, ran) = run_source(
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
            let (_, ran) = run_source(
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
}
