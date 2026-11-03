//! The driver's exit codes and output, observed by spawning the binary.
//!
//! Each case writes its sources into a scratch directory, runs `gandr` on
//! them, and asserts the exit code and the lines it printed. Output to a pipe
//! whose reader is closed is the unwritable case: the runtime ignores
//! `SIGPIPE`, so the write fails with `EPIPE` rather than ending the process.
//!
//! The process-level cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;
use std::process::Stdio;

use anodized::spec;
use gandr_storage_store::RootName;
use gandr_storage_store::Store;
use gandr_surface_dispatcher::Export;
use gandr_surface_dispatcher::Lock;
use gandr_surface_dispatcher::Package;
use gandr_surface_lsp::Body;
use gandr_surface_lsp::read_frame;
use gandr_surface_lsp::write_frame;
use quenchant_shape::shape::Maybe;

/// A fresh scratch directory, removed when dropped.
#[repr(transparent)]
pub struct Scratch(PathBuf);

/// The text of one scratch source.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Text<'text>(&'text str);

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
    /// - requires: a unique single-component test name and writable temporary
    ///   storage, without concurrent mutation of this case's directory.
    /// - ensures: returns a fresh empty directory owned by this process and
    ///   case.
    /// - provides: isolated source storage.
    /// - fails: never.
    /// - panics: if stale storage cannot be removed or the directory created.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two live cases with the same relative source path
    ///   produce different process verdicts; removing one leaves the other
    ///   usable. Namespace collisions, stale contents and cross-case removal
    ///   change these observations. Concurrent external writers and permission
    ///   failures are excluded.
    /// - witness: `tests::cli::scratch_ownership_keeps_simultaneous_cases_independent`
    #[spec(
            requires: test.file_name().is_some_and(|name| name == test.as_os_str()),
            ensures: |ref ret| ret.0.is_dir()
                && std::fs::read_dir(&ret.0).is_ok_and(|mut entries| entries.next().is_none()),
        )]
    pub fn new(test: &Path) -> Self
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
    /// - requires: a nonempty path of normal relative components beneath this
    ///   owned, writable scratch directory, without concurrent mutation.
    /// - ensures: creates missing parent directories and writes exactly the
    ///   offered source, returning its path beneath the scratch root.
    /// - provides: nested fixtures for a real driver process.
    /// - fails: never.
    /// - panics: if directories or the file cannot be written.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — simultaneous roots hold different sources under the
    ///   same nested relative name and yield different actual driver verdicts.
    ///   Escaping the root, losing directories or overwriting a peer changes
    ///   the observations; external mutations and failed filesystem operations
    ///   are excluded.
    /// - witness: `tests::cli::scratch_ownership_keeps_simultaneous_cases_independent`
    #[spec(
            requires: !relative.as_os_str().is_empty() && relative.components()
                .all(|component| matches!(component, std::path::Component::Normal(_))),
            ensures: |ref ret| ret.strip_prefix(&self.0).is_ok_and(|suffix| suffix == relative) && ret.is_file(),
        )]
    pub fn file(
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
    /// - ensures: removes the root and its descendants without removing peer
    ///   roots.
    /// - provides: scoped fixture lifetime.
    /// - fails: never.
    /// - panics: if removal fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one of two live nested fixture roots is dropped; its
    ///   path disappears and the peer still produces its expected process
    ///   verdict. Missing cleanup and overbroad deletion differ; concurrent
    ///   mutation is excluded.
    /// - witness: `tests::cli::scratch_ownership_keeps_simultaneous_cases_independent`
    #[spec(ensures: !self.0.exists())]
    fn drop(&mut self)
    {
        let removed = std::fs::remove_dir_all(&self.0);
        assert!(removed.is_ok(), "the scratch directory is removed");
    }
}

/// The directory holding this test's own user directories for the driver:
/// one per test under the target's scratch directory, emptied on the test's
/// first run of the driver, so no earlier run and no other test decides its
/// verdict.
///
/// A test runs on a thread its name names; a thread a test spawns takes the
/// process's directory, which is the test's own under nextest.
///
/// # Specification
/// trivial.
fn homes() -> PathBuf
{
    thread_local! {
        static HOMES: core::cell::OnceCell<PathBuf> = const { core::cell::OnceCell::new() };
    }
    HOMES.with(|homes| {
        homes
            .get_or_init(|| {
                let test = std::thread::current().name().map_or_else(
                    || format!("process-{}", std::process::id()),
                    |name| name.replace("::", "-"),
                );
                let directory = Path::new(env!("CARGO_TARGET_TMPDIR"))
                    .join("cli-homes")
                    .join(test);
                drop(std::fs::remove_dir_all(&directory));
                directory
            })
            .clone()
    })
}

/// The driver, ready to run with `arguments`.
///
/// # Specification
/// - requires: arguments have stable operating-system string views.
/// - ensures: selects the built driver and preserves arguments in order; the
///   user's configuration, cache and data directories are this test's own,
///   under [`homes`], so neither a file on the host nor an earlier run or
///   another test reaches a case through them, and no case writes the host's
///   store. Neither `GANDR_TOOLCHAIN` nor the `CARGO_MANIFEST_DIR` the test
///   runner sets reaches the driver, so it selects as a shell does and, with no
///   toolchain under the test's data directory, runs itself.
/// - provides: a command without starting a process.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — malformed invocations, a program's trailing arguments and
///   distinct check/test results expose argument identity and order. Dropped,
///   reordered or substituted arguments change statuses or output; arbitrary
///   `AsRef` types with stateful views are outside the domain.
/// - witness: `tests::cli::a_malformed_invocation_exits_two`
/// - witness: `tests::cli::a_program_leaves_with_its_entry_s_status_1881`
/// - witness: `tests::cli::the_test_verb_prints_every_fixture_and_pending_source`
#[spec(ensures: |ref ret| ret.get_program() == std::ffi::OsStr::new(env!("CARGO_BIN_EXE_gandr"))
        && ret.get_args().eq(arguments.iter().map(AsRef::as_ref)))]
fn gandr<Argument>(arguments: &[Argument]) -> Command
where
    Argument: AsRef<std::ffi::OsStr>,
{
    let homes = homes();
    let mut command = Command::new(env!("CARGO_BIN_EXE_gandr"));
    command.args(arguments);
    command.env("XDG_CONFIG_HOME", homes.join("config"));
    command.env("XDG_CACHE_HOME", homes.join("cache"));
    command.env("XDG_DATA_HOME", homes.join("data"));
    command.env_remove("GANDR_TOOLCHAIN");
    command.env_remove("CARGO_MANIFEST_DIR");
    command
}

/// The finished run of `command`, its output captured.
///
/// # Specification
/// - requires: a spawnable driver command, with no external process
///   termination.
/// - ensures: waits for completion and returns its status and captured streams.
/// - provides: a process-boundary observation.
/// - fails: never.
/// - panics: if the driver cannot start or be waited for.
///
/// # Adequacy
/// - hypothesis: L2/L3 — accepted, refused and unreadable sources plus a closed
///   output pipe expose all three process statuses and stream roles, and a
///   program its own exit statuses. Wrong commands, missing waits or lost
///   output change these fixtures; external signals and process-creation
///   failures are excluded.
/// - witness: `tests::cli::a_settled_run_exits_zero`
/// - witness: `tests::cli::an_unreadable_path_exits_two`
/// - witness: `tests::cli::unwritable_standard_output_exits_two`
/// - witness: `tests::cli::a_program_leaves_with_its_entry_s_status_1881`
#[spec(
        requires: command.get_program() == std::ffi::OsStr::new(env!("CARGO_BIN_EXE_gandr")),
        ensures: |ref ret| matches!(ret.status.code(), Some(0 ..= 255)),
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
/// - hypothesis: L3 — accepted, refused and unreadable cases assert distinct
///   zero, one and two statuses. Incorrect extraction or collapsed statuses
///   changes these observations; signal termination is excluded.
/// - witness: `tests::cli::a_settled_run_exits_zero`
/// - witness: `tests::cli::an_unsettled_run_exits_one`
/// - witness: `tests::cli::an_unreadable_path_exits_two`
#[spec(requires: output.status.code().is_some(),
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
/// - hypothesis: L2/L3 — a printed line and piped transcript fixtures compare
///   exact visible lines. Lost, duplicated or replaced bytes change those
///   observations; non-UTF-8 output is excluded.
/// - witness: `tests::cli::a_script_that_runs_its_main_leaves_successfully`
/// - witness: `tests::cli::a_piped_repl_session_prints_its_transcript`
#[spec(ensures: |ref ret| ret.as_bytes() == output.stdout.as_slice())]
fn stdout(output: &Output) -> String
{
    String::from_utf8(output.stdout.clone()).expect("standard output is UTF-8")
}

/// The driver's own standard error of `output`, as text.
///
/// A `tracing` build writes its subscriber's diagnostics to the same stream,
/// and the driver's documentation lets them precede its `gandr:` line. Each
/// diagnostic is one line, a UTC timestamp and then a level; under
/// `tracing`, those lines are dropped, so the tests read the driver's own
/// lines in either build.
///
/// # Specification
/// - requires: captured standard error is UTF-8.
/// - ensures: returns its bytes as owned text, unchanged in a default build;
///   under `tracing`, without the lines the subscriber wrote.
/// - provides: readable fault and refusal observations.
/// - fails: never.
/// - panics: if standard error is not UTF-8.
///
/// # Adequacy
/// - hypothesis: L3 — absent paths, checker refusal and blame identify the
///   failed source or goal on the diagnostic stream, in a default and a
///   `tracing` build. Lost bytes or confused streams change these observations;
///   non-UTF-8 output is excluded.
/// - witness: `tests::cli::an_absent_script_is_refused_by_path`
/// - witness: `tests::cli::an_ill_typed_script_is_refused_by_the_checker`
/// - witness: `tests::cli::a_script_that_blames_leaves_with_a_failure_status`
#[spec(ensures: |ref ret| cfg!(feature = "tracing") || ret.as_bytes() == output.stderr.as_slice())]
fn stderr(output: &Output) -> String
{
    let text = String::from_utf8(output.stderr.clone()).expect("standard error is UTF-8");
    #[cfg(feature = "tracing")]
    let text = {
        const LEVELS: [&str; 5] = ["TRACE", "DEBUG", "INFO", "WARN", "ERROR"];
        text.split_inclusive('\n')
            .filter(|line| {
                let mut words = line.split_whitespace();
                let stamped = words.next().is_some_and(|stamp| {
                    stamp.ends_with('Z')
                        && stamp.get(4 .. 5) == Some("-")
                        && stamp.get(10 .. 11) == Some("T")
                });
                !(stamped && words.next().is_some_and(|level| LEVELS.contains(&level)))
            })
            .collect::<String>()
    };
    text
}

/// The lines of `output`'s standard output that start with `path`, the
/// prefix removed.
///
/// # Specification
/// - requires: standard output is UTF-8.
/// - ensures: retains path-prefixed lines in order, removing the displayed path
///   and separator but not their payload.
/// - provides: path-specific ledger observations.
/// - fails: never.
/// - panics: if standard output is not UTF-8.
///
/// # Adequacy
/// - hypothesis: L3 — settled and pending fixtures share one run but retain
///   distinct path-scoped ledger rows under test and none under check. Wrong
///   prefix selection or payload loss changes those observations; arbitrary
///   path spellings and embedded line terminators are not enumerated.
/// - witness: `tests::cli::the_test_verb_prints_every_fixture_and_pending_source`
#[spec(ensures: |ref ret| ret.iter().all(|line| !line.contains('\n')))]
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
/// - requires: UTF-8 output whose first sources marker starts the final report.
/// - ensures: returns exactly the prefix before that marker.
/// - provides: diagnostic and ledger output separated from the run summary.
/// - fails: never.
/// - panics: if output is not UTF-8 or no report marker exists.
///
/// # Adequacy
/// - hypothesis: L2/L3 — settled, refused, owed and unreadable fixtures compare
///   the diagnostic prefix independently of final summaries. Truncation,
///   summary leakage or wrong boundaries change the observations; source text
///   containing an earlier report marker is excluded.
/// - witness: `tests::cli::a_settled_run_exits_zero`
/// - witness: `tests::cli::an_unsettled_run_exits_one`
/// - witness: `tests::cli::goals_report_an_obligation_without_failing`
#[spec(ensures: |ref ret| output.stdout.starts_with(ret.as_bytes())
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

/// Two sources of one run that each declare `P` and share an import settle in
/// either order: each run spells its value by its own `P`'s constructors, not
/// by the first `P` the run declares (#3125).
#[test]
fn a_run_spells_its_value_by_its_own_type_past_a_namesake_3125()
{
    let scratch = Scratch::new(Path::new("namesake"));
    let _shared = scratch.file(
        Path::new("d.gandr"),
        Text::from("pub data U : Type where {\n  | One : U\n}\n"),
    );
    let other = scratch.file(
        Path::new("b.gandr"),
        Text::from(
            "import \"./d.gandr\";\npub data P : Type where {\n  | Deref : P\n  | Field : P\n}\n@[ \
             runs(\"Field\") ]\ndef first() -> P {\n  Field\n}\n",
        ),
    );
    let own = scratch.file(
        Path::new("a.gandr"),
        Text::from(
            "import \"./d.gandr\";\npub data P : Type where {\n  | Inside : P\n  | OnHeap : P\n}\n@[ \
             runs(\"OnHeap\") ]\ndef second() -> P {\n  OnHeap\n}\n",
        ),
    );
    for (before, after) in [(&other, &own), (&own, &other)] {
        let output = ran(gandr(&[Path::new("test"), before, after]));
        assert_eq!(code(&output), Code(0_i32), "{}", stdout(&output));
    }
}

/// A run whose channel plays another web than the one its source states is
/// unsettled as another run outcome, the stated and the played web both
/// printed: a task that speaks before it is asked against the web of one
/// asked first (#3338).
#[test]
fn a_stated_web_the_run_does_not_produce_is_unsettled_3338()
{
    let asked_first = "series(event(right, 0), event(left, 0), event(left, 1), \
                       parallel(event(left, 2), series(event(right, 1), event(right, 2))))";
    let spoke_first = "series(event(left, 0), event(right, 0), event(right, 1), \
                       parallel(series(event(left, 1), event(left, 2)), event(right, 2)))";
    let text = format!(
        "@[ runs(\"unit\"), traces(decomposes(task, {asked_first})) ]\ndef swapped() -> Unit \
         {{\n  let asked = fork (task : !String. ?String. end) {{\n    send(task, \"notes\");\n    \
         let answer = recv(task);\n    close(task)\n  }};\n  let told = recv(asked);\n  \
         send(asked, told);\n  close(asked)\n}}\n"
    );
    let scratch = Scratch::new(Path::new("traced"));
    let source = scratch.file(Path::new("swapped.gandr"), Text::from(text.as_str()));
    let output = ran(gandr(&[Path::new("check"), &source]));
    assert_eq!(code(&output), Code(1_i32), "{}", stdout(&output));
    let diagnostic = printed(&output);
    assert!(
        diagnostic.contains(&format!(
            "states runs to unit tracing task to {asked_first}; produced runs to unit tracing \
             task to {spoke_first}"
        )),
        "{diagnostic}"
    );
    assert!(diagnostic.contains("another run outcome"), "{diagnostic}");
}

#[test]
fn verbosity_chooses_how_much_of_a_report_prints()
{
    let scratch = Scratch::new(Path::new("verbosity"));
    let source = scratch.file(
        Path::new("broken.gandr"),
        Text::from("def answer = 42 ;\ndef broken = missing ;\n"),
    );
    let at = |level: &str| {
        ran(gandr(&[
            Path::new("check"),
            Path::new("--verbosity"),
            Path::new(level),
            &source,
        ]))
    };
    let user = at("user");
    let detailed = at("detailed");
    let debug = at("debug");
    for output in [&user, &detailed, &debug] {
        assert_eq!(code(output), Code(1_i32), "{}", stdout(output));
        assert!(stdout(output).ends_with("verdict: unsettled\n"));
    }
    assert_eq!(
        stdout(&user),
        stdout(&ran(gandr(&[Path::new("check"), &source]))),
        "the user level is the default"
    );
    assert!(!stdout(&user).contains("class: "));
    assert!(stdout(&detailed).contains("class: malformed source"));
    assert!(stdout(&detailed).contains("expression: `missing`"));
    assert!(!stdout(&detailed).contains("spans: "));
    assert!(stdout(&debug).contains("spans: primary 31..38"));
    let json = at("json");
    assert_eq!(code(&json), Code(1_i32), "the level changes no exit");
    let lines: Vec<serde_json::Value> = stdout(&json)
        .lines()
        .map(|line| serde_json::from_str(line).expect("every line is one JSON object"))
        .collect();
    let [ref report, ref summary] = *lines.as_slice()
    else {
        panic!("one report and the summary: {lines:?}");
    };
    assert_eq!(report["name"], "UnresolvedName");
    assert_eq!(report["primary"]["line"], 2_u64);
    assert_eq!(report["primary"]["column"], 14_u64);
    assert_eq!(summary["level"], "summary");
    assert_eq!(summary["verdict"], "unsettled");
}

/// The counts of a detailed `check`'s `kernel:` line as it prints them,
/// recalled, recorded and unwritten, without the signer; absent when it
/// printed none.
///
/// # Specification
/// trivial.
fn kernel_tally(output: &Output) -> Option<String>
{
    stdout(output).lines().find_map(|line| {
        let (counts, _signer) = line.strip_prefix("kernel: ")?.split_once("; signed by ")?;
        Some(counts.to_owned())
    })
}

/// #2799: a second `check` over one verdict cache recalls in the kernel
/// every declaration the first checked, printing what the first printed;
/// `--recheck` installs no cache, a key the policy does not list recalls
/// nothing, and a key `kernel.trusted` lists is believed.
#[test]
fn a_second_check_recalls_what_the_first_recorded_2799()
{
    let scratch = Scratch::new(Path::new("verdict-cache"));
    let source = scratch.file(
        Path::new("answers.gandr"),
        Text::from("def answer = 42 ;\ndef again = answer ;\n"),
    );
    let home = scratch.0.join("configuration");
    let cache = scratch.0.join("cache");
    let check = |flags: &[&str]| {
        let mut command = gandr(&["check", "--verbosity", "detailed"]);
        let _configured = command
            .args(flags)
            .arg(&source)
            .env("XDG_CONFIG_HOME", &home)
            .env("XDG_CACHE_HOME", &cache);
        let output = ran(command);
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
        output
    };
    let rest = |output: &Output| -> Vec<String> {
        stdout(output)
            .lines()
            .filter(|line| !line.starts_with("kernel: "))
            .map(String::from)
            .collect()
    };
    let cold = check(&[]);
    let tally = kernel_tally(&cold).unwrap_or_default();
    let Some(recorded) = tally
        .strip_prefix("0 recalled, ")
        .and_then(|rest| rest.strip_suffix(" recorded, 0 unwritten"))
        .filter(|recorded| *recorded != "0")
    else {
        panic!("a cold check records what it checks: {}", stdout(&cold));
    };
    let recalled = Some(format!("{recorded} recalled, 0 recorded, 0 unwritten"));
    let unbelieved = Some(format!("0 recalled, {recorded} recorded, 0 unwritten"));
    let first = stdout(&cold)
        .lines()
        .find_map(|line| {
            line.split_once("; signed by ")
                .map(|(_, key)| key.to_owned())
        })
        .expect("the tally names the key it signs with");
    let key = home.join("gandr").join("kernel.key");

    let warm = check(&[]);
    assert_eq!(kernel_tally(&warm), recalled);
    assert_eq!(
        rest(&warm),
        rest(&cold),
        "a recalled verdict prints as a checked one"
    );

    let rechecked = check(&["--recheck"]);
    assert_eq!(
        kernel_tally(&rechecked),
        None,
        "`--recheck` installs no cache"
    );
    assert_eq!(rest(&rechecked), rest(&cold));

    std::fs::write(&key, [1_u8; 32]).expect("another key is written");
    assert_eq!(
        kernel_tally(&check(&[])),
        unbelieved,
        "a receipt signed by a key the policy does not list is not believed"
    );

    std::fs::write(&key, [2_u8; 32]).expect("a third key is written");
    std::fs::write(
        home.join("gandr").join("config.toml"),
        format!("[kernel]\ntrusted = [\"{first}\"]\n"),
    )
    .expect("the configuration is written");
    assert_eq!(
        kernel_tally(&check(&[])),
        recalled,
        "a receipt signed by a key `kernel.trusted` lists is believed"
    );
}

/// The counts of a detailed `check`'s `strata:` line as it prints them,
/// without the signer; absent when it printed none.
///
/// # Specification
/// trivial.
fn strata_tally(output: &Output) -> Option<String>
{
    stdout(output).lines().find_map(|line| {
        let (counts, _signer) = line.strip_prefix("strata: ")?.split_once("; signed by ")?;
        Some(counts.to_owned())
    })
}

/// #4034: a second `check` of a `ua` statement reads its stratum from the
/// store the first kept and certifies nothing; `--recheck` asks no store, and
/// a stratum another key signed is not believed and is certified afresh.
#[test]
fn a_second_check_replays_the_strata_the_first_kept_4034()
{
    let scratch = Scratch::new(Path::new("stratum-store"));
    let source = scratch.file(
        Path::new("six.gandr"),
        Text::from(
            "pub theory Magma where {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> (z : M);\n  \
             oper one : () --> (z : M);\n}\n\npub def exchange(b : Bool) -> Bool {\n  match b {\n    \
             true => +{.1 = unit},\n    false => +{.0 = unit}\n  }\n}\n\npub def keep(e : +{Unit}) \
             -> +{Unit} {\n  e\n}\n\ndef six = ua[6, 6](Magma, Magma, #{.mul = exchange, .one = \
             keep}, #{.mul = exchange, .one = keep});\n",
        ),
    );
    let home = scratch.0.join("configuration");
    let cache = scratch.0.join("cache");
    let check = |flags: &[&str]| {
        let mut command = gandr(&["check", "--verbosity", "detailed"]);
        let _configured = command
            .args(flags)
            .arg(&source)
            .env("XDG_CONFIG_HOME", &home)
            .env("XDG_CACHE_HOME", &cache);
        let output = ran(command);
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
        strata_tally(&output)
    };
    let counts = |counts: &str| Some(counts.to_owned());

    assert_eq!(
        check(&[]),
        counts("0 recalled, 1 certified, 0 refused, 0 unattested, 0 unwritten"),
        "a cold check certifies the stratum and keeps it"
    );
    assert_eq!(
        check(&[]),
        counts("1 recalled, 0 certified, 0 refused, 0 unattested, 0 unwritten"),
        "a warm check replays the kept stratum and certifies nothing"
    );
    assert_eq!(check(&["--recheck"]), None, "`--recheck` asks no store");

    std::fs::write(home.join("gandr").join("kernel.key"), [1_u8; 32])
        .expect("another key is written");
    assert_eq!(
        check(&[]),
        counts("0 recalled, 1 certified, 0 refused, 1 unattested, 0 unwritten"),
        "a stratum another key signed is not believed"
    );
}

#[test]
fn a_lint_reports_each_inferred_exit_and_its_fix_settles_it()
{
    let scratch = Scratch::new(Path::new("lint"));
    let elided = "def kept(n: Integer) -> -F Integer { n }\ndef called(n: Integer) -> -F \
                      Integer { kept(n) }\n";
    let source = scratch.file(Path::new("exits.gandr"), Text::from(elided));
    let check = Path::new("check");
    let lint = [check, Path::new("--lint"), Path::new("explicit-exits")];
    let plain = ran(gandr(&[check, &source]));
    assert_eq!(code(&plain), Code(0_i32), "{}", stdout(&plain));
    assert_eq!(
        printed(&plain),
        "",
        "the lint is off without an attribute or a flag"
    );

    let user = ran(gandr(&[lint[0], lint[1], lint[2], &source]));
    assert_eq!(code(&user), Code(0_i32), "a finding settles nothing");
    let findings = printed(&user);
    assert_eq!(
        findings.matches("warning[explicit-exits]").count(),
        2_usize,
        "{findings}"
    );
    assert!(findings.contains("{ return n }"), "{findings}");
    assert!(findings.contains("{ become kept(n) }"), "{findings}");

    let json = ran(gandr(&[
        lint[0],
        lint[1],
        lint[2],
        Path::new("--verbosity"),
        Path::new("json"),
        &source,
    ]));
    let fixes: Vec<(usize, usize, String)> = stdout(&json)
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("one JSON object"))
        .filter(|report| report["level"] == "warning")
        .map(|report| {
            assert_eq!(report["name"], "explicit-exits");
            let fix = &report["fix"];
            (
                usize::try_from(fix["start"].as_u64().expect("a start")).expect("in range"),
                usize::try_from(fix["end"].as_u64().expect("an end")).expect("in range"),
                fix["replacement"]
                    .as_str()
                    .expect("a replacement")
                    .to_owned(),
            )
        })
        .collect();
    let mut fixed = String::from(elided);
    for &(start, end, ref replacement) in fixes.iter().rev() {
        fixed.replace_range(start .. end, replacement);
    }
    assert_eq!(
        fixed,
        "def kept(n: Integer) -> -F Integer { return n }\ndef called(n: Integer) -> -F \
             Integer { become kept(n) }\n"
    );
    std::fs::write(&source, &fixed).expect("the fixed source is written");
    let again = ran(gandr(&[lint[0], lint[1], lint[2], &source]));
    assert_eq!(code(&again), Code(0_i32), "{}", stdout(&again));
    assert_eq!(printed(&again), "", "the fixed source has no finding");
}

/// `gandr check --measure` prints one line per declaration a source writes:
/// its sizes, the goals the kernel's check of it charged and the time its
/// admission took. A check without the flag prints none. A declaration a
/// recorded verdict admits ran no check, and its line says so in place of the
/// counts.
#[test]
fn check_measures_each_declaration_a_source_writes()
{
    let scratch = Scratch::new(Path::new("measure"));
    let _base = scratch.file(
        Path::new("base.gandr"),
        Text::from("pub def one(n: Integer) -> -F Integer { n }\n"),
    );
    let _top = scratch.file(
        Path::new("top.gandr"),
        Text::from("import \"./base.gandr\" ;\ndef two(n: Integer) -> -F Integer { one(n) }\n"),
    );
    // A key and a verdict cache of the test's own: the shared ones hold the
    // receipts other tests leave, so a first run would recall `one`.
    let home = scratch.0.join("configuration");
    let cache = scratch.0.join("cache");
    let check = |flags: &[&Path]| {
        let mut arguments = vec![Path::new("check")];
        arguments.extend_from_slice(flags);
        arguments.push(&scratch.0);
        let mut command = gandr(&arguments);
        let _configured = command
            .env("XDG_CONFIG_HOME", &home)
            .env("XDG_CACHE_HOME", &cache);
        let output = ran(command);
        assert_eq!(
            code(&output),
            Code(0_i32),
            "a measure settles nothing: {}",
            stderr(&output)
        );
        output
    };
    let count = |field: &str, unit: &str| -> u64 {
        field
            .strip_suffix(unit)
            .and_then(|count| count.trim_end().parse().ok())
            .unwrap_or_else(|| panic!("{field:?} spells its {unit}"))
    };
    // Each row's source, its declaration and the fields after its sizes.
    let rows = |output: &Output| -> Vec<(String, String, Vec<String>)> {
        let mut rows: Vec<(String, String, Vec<String>)> = stdout(output)
            .lines()
            .filter_map(|line| line.strip_prefix("measure: "))
            .map(|row| {
                let (path, rest) = row.split_once(": ").expect("a row names its source");
                let (name, fields) = rest.split_once(": ").expect("a row names its declaration");
                let mut fields = fields.split(", ");
                let (Some(bytes), Some(shared), Some(unshared)) =
                    (fields.next(), fields.next(), fields.next())
                else {
                    panic!("{row:?} spells three sizes");
                };
                assert!(count(bytes, "bytes") > 0, "a segment holds bytes: {row}");
                assert!(
                    count(shared, "shared") <= count(unshared, "unshared"),
                    "a segment adds no more entries than its roots' trees hold: {row}"
                );
                let file = Path::new(path)
                    .file_name()
                    .map(|file| file.to_string_lossy().into_owned())
                    .unwrap_or_default();
                (file, name.to_owned(), fields.map(str::to_owned).collect())
            })
            .collect();
        rows.sort();
        rows
    };
    let written = [
        ("base.gandr".to_owned(), "one".to_owned()),
        ("top.gandr".to_owned(), "two".to_owned()),
    ];
    let named = |rows: &[(String, String, Vec<String>)]| -> Vec<(String, String)> {
        rows.iter()
            .map(|&(ref file, ref name, _)| (file.clone(), name.clone()))
            .collect()
    };

    let checked = rows(&check(&[Path::new("--measure")]));
    assert_eq!(
        named(&checked),
        written,
        "each source measures the declaration it writes, and none it imports"
    );
    for &(_, ref name, ref tally) in &checked {
        let [ref expanded, ref recalled, ref kept, ref took] = *tally.as_slice()
        else {
            panic!("{name}'s checked row spells three counts and a time: {tally:?}");
        };
        assert!(
            count(expanded, "expanded")
                .saturating_add(count(recalled, "recalled"))
                .saturating_add(count(kept, "kept"))
                > 0,
            "the kernel's check of {name} charges at least its declared type's formation"
        );
        let _nanoseconds = count(took, "ns");
    }

    let plain = check(&[]);
    assert!(
        !stdout(&plain).contains("measure: "),
        "a check measures nothing unasked"
    );

    let recorded = rows(&check(&[Path::new("--measure")]));
    assert_eq!(
        named(&recorded),
        written,
        "a recorded verdict's admission is measured as a checked one is"
    );
    for &(_, ref name, ref tally) in &recorded {
        let [ref verdict, ref took] = *tally.as_slice()
        else {
            panic!("{name}'s recalled row spells its admission and a time: {tally:?}");
        };
        assert_eq!(
            verdict, "admitted on a recorded verdict",
            "{name} ran no check, and its row says so rather than counting nothing"
        );
        let _nanoseconds = count(took, "ns");
    }
}

/// #4112: `gandr check --report cells` prints one line per law a model omits
/// that the checker discharged, with its source. A law whose sides part is
/// refused and lists no cell, and a check without the flag lists none.
#[test]
fn check_reports_each_cell_a_source_discharges_4112()
{
    let scratch = Scratch::new(Path::new("cells"));
    let source = scratch.file(
        Path::new("laws.gandr"),
        Text::from(
            "theory Same where {\n  sort Carrier : Type;\n  oper same : (a : Carrier, b : Carrier) --> \
             Bool;\n  law refl : (a : Carrier) => Path(Bool, same(a, a), true);\n}\ndata One : \
             Type where {\n  | Only : One\n}\nmodule Converts : Model(Same) with sort Carrier = One where {\n  \
             def same(a : One, b : One) -> Bool { true }\n}\nmodule Parts : Model(Same) with sort \
             Carrier = One where {\n  def same(a : One, b : One) -> Bool { false }\n}\n",
        ),
    );
    let cells = |output: &Output| -> Vec<String> {
        stdout(output)
            .lines()
            .filter_map(|line| line.strip_prefix("cell: "))
            .map(str::to_owned)
            .collect()
    };
    let reported = ran(gandr(&[
        Path::new("check"),
        Path::new("--report"),
        Path::new("cells"),
        &source,
    ]));
    assert_eq!(
        code(&reported),
        Code(1_i32),
        "the law whose sides part is refused: {}",
        stdout(&reported)
    );
    assert_eq!(
        cells(&reported),
        [format!("{}: Converts.refl: Path.here", source.display())],
        "the law whose sides convert is the one cell, discharged `Path.here`"
    );
    let plain = ran(gandr(&[Path::new("check"), &source]));
    assert!(cells(&plain).is_empty(), "a check lists no cell unasked");
}

#[test]
fn the_runs_lint_reaches_a_pure_run_unless_its_effects_option_narrows_it()
{
    let scratch = Scratch::new(Path::new("runs"));
    let source = scratch.file(
        Path::new("runs.gandr"),
        Text::from(
            "def id(n: Integer) -> -F Integer { n }\ndef twice(n: Integer) -> -F Integer { \
                 id(id(n)) }\n",
        ),
    );
    let check = Path::new("check");
    let lint = Path::new("--lint");
    let every = ran(gandr(&[check, lint, Path::new("explicit-runs"), &source]));
    assert_eq!(code(&every), Code(0_i32), "a finding settles nothing");
    let findings = printed(&every);
    assert_eq!(
        findings.matches("warning[explicit-runs]").count(),
        1_usize,
        "{findings}"
    );
    assert!(findings.contains("{ id(run id(n)) }"), "{findings}");
    let effects = ran(gandr(&[
        check,
        lint,
        Path::new("explicit-runs=effects"),
        &source,
    ]));
    assert_eq!(code(&effects), Code(0_i32), "{}", stdout(&effects));
    assert_eq!(
        printed(&effects),
        "",
        "the `effects` option leaves a pure run silent"
    );
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
        Text::from("@[ checks ]\n"),
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
    assert!(pending_lines[0].contains("`attribute_block`"));

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
fn fmt_rewrites_what_check_reports()
{
    let scratch = Scratch::new(Path::new("fmt"));
    let loose = scratch.file(
        Path::new("loose.gandr"),
        Text::from("def  answer =  42 ;\n"),
    );
    let tidy = scratch.file(Path::new("tidy.gandr"), Text::from("def copy = 1;\n"));
    let absent = scratch.0.join("absent.gandr");
    let fmt = Path::new("fmt");
    let check = Path::new("--check");

    let checked = ran(gandr(&[fmt, check, &loose, &tidy]));
    assert_eq!(code(&checked), Code(1_i32), "{}", stderr(&checked));
    assert_eq!(stdout(&checked), format!("{}\n", loose.display()));
    let serial = ran(gandr(&[fmt, check, Path::new("--jobs=1"), &loose, &tidy]));
    assert_eq!(
        (code(&serial), serial.stdout.as_slice()),
        (code(&checked), checked.stdout.as_slice()),
        "one thread prints what the default width prints"
    );
    assert_eq!(
        std::fs::read_to_string(&loose).expect("the source is readable"),
        "def  answer =  42 ;\n",
        "the check writes nothing"
    );

    let faulted = ran(gandr(&[fmt, check, &loose, &absent]));
    assert_eq!(code(&faulted), Code(2_i32), "a fault outranks a change");
    assert!(
        stderr(&faulted).starts_with(&format!("gandr: {}: ", absent.display())),
        "{}",
        stderr(&faulted)
    );

    let rewritten = ran(gandr(&[fmt, &loose, &tidy]));
    assert_eq!(code(&rewritten), Code(0_i32), "{}", stderr(&rewritten));
    assert_eq!(stdout(&rewritten), format!("{}\n", loose.display()));
    assert_eq!(
        std::fs::read_to_string(&loose).expect("the source is readable"),
        "def answer = 42;\n"
    );
    assert_eq!(
        std::fs::read_to_string(&tidy).expect("the source is readable"),
        "def copy = 1;\n"
    );

    let again = ran(gandr(&[fmt, check, &scratch.0]));
    assert_eq!(code(&again), Code(0_i32), "{}", stdout(&again));
    assert!(
        stdout(&again).is_empty(),
        "a formatted tree reports nothing"
    );
}

/// #791: `fmt --form sugared` sugars a declaration whose match reads its
/// parameter's stated sum as it sugars the one beside it, and reports no
/// declaration as keeping its spelling. Before the fix, the match's
/// declaration kept `+{Integer, Integer}` and standard error named it. Its
/// arms' tail `return`s are left out (#1327).
#[test]
fn fmt_sugars_a_match_over_a_stated_sum_791()
{
    let scratch = Scratch::new(Path::new("fmt-kept"));
    let source = scratch.file(
        Path::new("pick.gandr"),
        Text::from(
            "def pair : #{Integer, String} ;\n\ndef pick(t : +{Integer, Integer}) -> -F Integer \
             {\n  match t {\n    +{.1 = x} => return x,\n    _ => return 0\n  }\n}\n",
        ),
    );
    let (fmt, form) = (Path::new("fmt"), Path::new("--form=sugared"));
    let sugared = ran(gandr(&[fmt, form, &source]));
    assert_eq!(code(&sugared), Code(0_i32), "{}", stderr(&sugared));
    assert_eq!(
        (stdout(&sugared), stderr(&sugared)),
        (format!("{}\n", source.display()), String::new())
    );
    assert_eq!(
        std::fs::read_to_string(&source).expect("the source is readable"),
        "def pair : Integer * String;\n\ndef pick(t : Integer + Integer) -> Integer {\n  match t \
         {\n    +{.1 = x} => x,\n    _ => 0\n  }\n}\n",
        "both declarations are sugared"
    );
}

/// `gandr cells` prints each cell of the occurrence-count exemplar on its
/// rule's line, each hole with how many times the cell's right-hand side
/// writes it; a path that names no source is a fault on standard error and
/// exits two once the census has read every other path.
#[test]
fn cells_reports_each_hole_s_count()
{
    let exemplar = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/model/desc/occurrence-count.gandr");
    let scratch = Scratch::new(Path::new("cells"));
    let absent = scratch.0.join("absent.gandr");
    let cells = Path::new("cells");

    let read = ran(gandr(&[cells, &exemplar]));
    assert_eq!(code(&read), Code(0_i32), "{}", stderr(&read));
    let shown = exemplar.display();
    assert_eq!(
        stdout(&read),
        format!(
            "{shown}:12:1: cell 0 frame, strictly linear: v 1, beta 1\n\
             {shown}:12:1: cell 1 frame, strictly linear: v 1, beta 1\n\
             {shown}:19:23: cell 2 rule, strictly linear: $ret 1\n\
             {shown}:20:29: cell 3 rule, strictly linear: l 1, r 1, $ret 1\n\
             {shown}:21:21: cell 4 rule, strictly linear: $ret 1\n\
             {shown}:22:27: cell 5 rule, erasing: l 1, r 0, $ret 1\n\
             {shown}:23:19: cell 6 rule, duplicating 2: t 2, $ret 1\n\
             {shown}:24:20: cell 7 rule, duplicating 3: t 3, $ret 1\n"
        )
    );

    let faulted = ran(gandr(&[cells, &absent, &exemplar]));
    assert_eq!(code(&faulted), Code(2_i32), "{}", stderr(&faulted));
    assert!(
        stderr(&faulted).starts_with(&format!("gandr: {}: ", absent.display())),
        "{}",
        stderr(&faulted)
    );
    assert_eq!(
        stdout(&faulted),
        stdout(&read),
        "the census continued past the fault"
    );
}

#[test]
fn the_syntax_ledger_is_written_and_reproduced()
{
    let scratch = Scratch::new(Path::new("ledger"));
    let directory = scratch.0.join("ledger");
    let committed = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/ledger");
    let (ledger, syntax, write, with) = (
        Path::new("ledger"),
        Path::new("syntax"),
        Path::new("--write"),
        Path::new("--exemplars"),
    );

    let written = ran(gandr(&[
        ledger, syntax, write, &directory, with, &committed,
    ]));
    assert_eq!(code(&written), Code(0_i32), "{}", stderr(&written));
    let markdown = directory.join("syntax.md");
    let json = directory.join("syntax.json");
    assert_eq!(
        stdout(&written),
        format!("{}\n{}\n", markdown.display(), json.display()),
        "each file written is printed, in order"
    );
    let first = (
        std::fs::read(&markdown).expect("the reading form is written"),
        std::fs::read(&json).expect("the machine form is written"),
    );
    assert!(
        String::from_utf8_lossy(&first.0).contains("- Grammar fingerprint: `0x"),
        "the reading form names the fingerprint"
    );

    let again = ran(gandr(&[
        ledger, syntax, write, &directory, with, &committed,
    ]));
    assert_eq!(code(&again), Code(0_i32), "{}", stderr(&again));
    let second = (
        std::fs::read(&markdown).expect("the reading form is written"),
        std::fs::read(&json).expect("the machine form is written"),
    );
    assert_eq!(first, second, "a second run writes the same bytes");

    let blocked = scratch.file(Path::new("file"), Text::from(""));
    let refused = ran(gandr(&[
        ledger,
        syntax,
        write,
        &blocked.join("ledger"),
        with,
        &committed,
    ]));
    assert_eq!(code(&refused), Code(2_i32), "{}", stdout(&refused));
    assert!(
        stderr(&refused).starts_with(&format!("gandr: {}", blocked.join("ledger").display())),
        "{}",
        stderr(&refused)
    );

    let unshown = ran(gandr(&[ledger, syntax, write, &directory]));
    assert_eq!(code(&unshown), Code(2_i32), "{}", stdout(&unshown));
    assert!(
        stderr(&unshown).starts_with(&format!(
            "gandr: {}",
            directory.join("exemplars").join("syntax").display()
        )),
        "without `--exemplars` the admissions are read under the written directory: {}",
        stderr(&unshown)
    );
}

#[test]
fn the_exemplars_verify_and_a_stray_one_is_named()
{
    let committed = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/ledger");
    let (ledger, exemplars) = (Path::new("ledger"), Path::new("exemplars"));

    let clean = ran(gandr(&[ledger, exemplars, &committed]));
    assert_eq!(code(&clean), Code(0_i32), "{}", stdout(&clean));
    assert!(
        stdout(&clean).ends_with(" owed, 0 findings\n"),
        "{}",
        stdout(&clean)
    );

    let scratch = Scratch::new(Path::new("exemplars"));
    for folder in ["syntax", "attributes", "diagnostics"] {
        for entry in std::fs::read_dir(committed.join(folder)).expect("the folder lists") {
            let source = entry.expect("the entry reads").path();
            let name = source.file_name().expect("an exemplar is a file");
            let text = std::fs::read_to_string(&source).expect("the exemplar reads");
            let _path = scratch.file(&Path::new(folder).join(name), Text::from(text.as_str()));
        }
    }
    let stray = scratch.file(
        Path::new("syntax/unknown_rule.gandr"),
        Text::from("/// `unknown_rule`: no such rule.\ndef answer = 42 ;\n"),
    );
    let found = ran(gandr(&[ledger, exemplars, &scratch.0]));
    assert_eq!(code(&found), Code(1_i32), "{}", stderr(&found));
    assert!(
        stdout(&found).starts_with(&format!(
            "{}: names nothing the ledger lists\n",
            stray.display()
        )),
        "{}",
        stdout(&found)
    );
    assert!(stdout(&found).ends_with(" owed, 1 finding\n"));
}

#[test]
fn the_recovery_sweep_reports_its_table_and_count()
{
    let scratch = Scratch::new(Path::new("recovery"));
    let _path = scratch.file(
        Path::new("syntax/def_value.gandr"),
        Text::from("/// `def_value`: a definition.\n@[ checks ]\ndef answer = 42 ;\n"),
    );
    let swept = ran(gandr(&[
        Path::new("ledger"),
        Path::new("recovery"),
        &scratch.0,
    ]));
    assert_eq!(code(&swept), Code(0_i32), "{}", stderr(&swept));
    let printed = stdout(&swept);
    assert!(
        printed
            .lines()
            .any(|line| line == "near miss: `def` → `de`"),
        "the table names what each tile is mistaken for: {printed}"
    );
    assert!(
        printed.ends_with(" accepted, 0 well formed, 0 closed early, 0 marked elsewhere\n"),
        "the count closes the report: {printed}"
    );
}

/// #1827: `gandr ledger list` and `gandr ledger show` read the features ledger
/// as the guide an author writes from.
#[test]
fn the_features_ledger_lists_and_shows_1827()
{
    let scratch = Scratch::new(Path::new("features"));
    let _ledger = scratch.file(
        Path::new("ledger/features.sql"),
        Text::from(
            "PRAGMA foreign_keys=OFF;\nBEGIN TRANSACTION;\nCREATE TABLE feature(\n  id TEXT PRIMARY KEY,\n  \
             area TEXT NOT NULL,\n  name TEXT NOT NULL,\n  parent TEXT,\n  status TEXT NOT NULL,\n  notability \
             TEXT NOT NULL,\n  compared_to TEXT,\n  line TEXT NOT NULL CHECK(line <> ''),\n  crate TEXT,\n  \
             corpus TEXT,\n  exemplar TEXT,\n  issue TEXT,\n  since TEXT\n) WITHOUT ROWID;\n\
             INSERT INTO feature VALUES('answers','syntax','Answers',NULL,'implemented','ordinary',NULL,'A \
             definition''s answer.','surface-parser','tests/answers.rs','ledger/answers.gandr',NULL,'#2');\n\
             INSERT INTO feature VALUES('questions','syntax','Questions',NULL,'planned','ordinary',NULL,'A \
             question.',NULL,NULL,NULL,'#3',NULL);\n\
             INSERT INTO feature VALUES('reels','storage','Reels',NULL,'implemented','ordinary',NULL,'A \
             reel.','storage-records',NULL,'crate-tests',NULL,'#4');\nCOMMIT;\n",
        ),
    );
    let _exemplar = scratch.file(
        Path::new("ledger/answers.gandr"),
        Text::from("/// `answers`: a definition.\n@[ checks ]\ndef answer = 42 ;\n"),
    );
    let (ledger, root) = (Path::new("ledger"), Path::new("--root"));

    let listed = ran(gandr(&[
        ledger,
        Path::new("list"),
        Path::new("--area"),
        Path::new("syntax"),
        root,
        &scratch.0,
    ]));
    assert_eq!(code(&listed), Code(0_i32), "{}", stderr(&listed));
    assert_eq!(
        stdout(&listed),
        "answers [implemented] Answers: A definition's answer.\nquestions [planned] Questions: A question.\n"
    );
    let planned = ran(gandr(&[
        ledger,
        Path::new("list"),
        Path::new("--status"),
        Path::new("planned"),
        root,
        &scratch.0,
    ]));
    assert_eq!(code(&planned), Code(0_i32), "{}", stderr(&planned));
    assert_eq!(
        stdout(&planned),
        "questions [planned] Questions: A question.\n"
    );

    let shown = ran(gandr(&[
        ledger,
        Path::new("show"),
        Path::new("answers"),
        root,
        &scratch.0,
    ]));
    assert_eq!(code(&shown), Code(0_i32), "{}", stderr(&shown));
    assert_eq!(
        stdout(&shown),
        "id: answers\narea: syntax\nname: Answers\nstatus: implemented\nnotability: ordinary\nline: A \
         definition's answer.\ncrate: surface-parser\ncorpus: tests/answers.rs\nexemplar: \
         ledger/answers.gandr\nsince: #2\n--- ledger/answers.gandr\n/// `answers`: a definition.\n@[ checks \
         ]\ndef answer = 42 ;\n--- corpus\ntests/answers.rs\n"
    );

    let elsewhere = ran(gandr(&[
        ledger,
        Path::new("list"),
        Path::new("--area"),
        Path::new("astrology"),
        root,
        &scratch.0,
    ]));
    assert_eq!(code(&elsewhere), Code(2_i32), "{}", stdout(&elsewhere));
    assert_eq!(
        stderr(&elsewhere),
        "gandr: no feature is in the area `astrology`; the areas are storage, syntax\n"
    );
    let unknown = ran(gandr(&[
        ledger,
        Path::new("show"),
        Path::new("answer"),
        root,
        &scratch.0,
    ]));
    assert_eq!(code(&unknown), Code(2_i32), "{}", stdout(&unknown));
    assert_eq!(stderr(&unknown), "gandr: no feature is `answer`\n");

    let committed = ran(gandr(&[
        ledger,
        Path::new("show"),
        Path::new("features-exemplars"),
        root,
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."),
    ]));
    assert_eq!(code(&committed), Code(0_i32), "{}", stderr(&committed));
}

/// A width a run is asked at, by flag, by the environment, or neither.
#[derive(Clone, Copy, Debug)]
enum Width
{
    /// `--jobs 1`: the serial run.
    Serial,
    /// `--jobs 4`.
    FourByFlag,
    /// `GANDR_JOBS=3`.
    ThreeByEnvironment,
    /// No flag and no environment: the host's width.
    Host,
}

/// The finished run of `gandr` on `arguments` at `width`, its output
/// captured.
///
/// # Specification
/// - requires: as [`ran`].
/// - ensures: runs `arguments` with the flag or the environment `width` names,
///   `GANDR_JOBS` removed unless `width` sets it, and returns the run.
/// - fails: never.
/// - panics: as [`ran`].
///
/// # Adequacy
/// - hypothesis: L2 — the corpus and a faulting path list run at each width
///   print byte-identical streams and exits to the serial run.
/// - witness: `tests::cli::every_width_prints_the_serial_run_of_model_share_0_3400`
/// - witness: `tests::cli::every_width_prints_the_serial_check`
#[spec(ensures: |ref ret| matches!(ret.status.code(), Some(0 ..= 255)))]
fn at(
    arguments: &[PathBuf],
    width: Width,
) -> Output
{
    let mut command = gandr(arguments);
    match width {
        Width::Serial => {
            command.args(["--jobs", "1"]).env_remove("GANDR_JOBS");
        },
        Width::FourByFlag => {
            command.args(["--jobs", "4"]).env_remove("GANDR_JOBS");
        },
        Width::ThreeByEnvironment => {
            command.env("GANDR_JOBS", "3");
        },
        Width::Host => {
            command.env_remove("GANDR_JOBS");
        },
    }
    ran(command)
}

/// Assert that `arguments` run at each of `wider` prints the serial run: the
/// same exit and the same bytes on both streams.
///
/// # Specification
/// - requires: `arguments` is a `gandr` verb with operands whose serial run
///   prints a verdict.
/// - ensures: returns only when the serial run printed a verdict and every
///   wider run's exit and streams equal the serial run's.
/// - fails: never.
/// - panics: at the serial run without a verdict, or the first wider run that
///   differs from it.
/// - executable: none — the assertions are the check.
///
/// # Adequacy
/// - hypothesis: L2 — every corpus root runs serially and at one wider width,
///   and the scratch check at three, so a width that reorders, drops or
///   duplicates a source's output, or exits otherwise, fails.
/// - witness: `tests::cli::every_width_prints_the_serial_run_of_model_share_0_3400`
/// - witness: `tests::cli::every_width_prints_the_serial_check`
fn agrees(
    arguments: &[PathBuf],
    wider: &[Width],
)
{
    let serial = at(arguments, Width::Serial);
    assert!(
        stdout(&serial).contains("verdict: "),
        "{arguments:?}: {}",
        stderr(&serial)
    );
    for &width in wider {
        let output = at(arguments, width);
        assert_eq!(
            (code(&output), stdout(&output), stderr(&output)),
            (code(&serial), stdout(&serial), stderr(&serial)),
            "{arguments:?} at {width:?} prints the serial run"
        );
    }
}

/// A `gandr test` over the corpus roots `roots`, each a path from the
/// workspace root.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the verb `test` followed by each root under the workspace
///   root, in order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each share names its roots, and a root that does not
///   resolve faults the serial run, which the assertion reports.
/// - witness: `tests::cli::every_width_prints_the_serial_run_of_model_share_0_3400`
#[spec(ensures: |ref ret| ret.first() == Some(&PathBuf::from("test"))
        && ret.len().checked_sub(1) == Some(roots.len()))]
fn share(roots: &[&Path]) -> Vec<PathBuf>
{
    let corpus = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut run = vec![PathBuf::from("test")];
    run.extend(roots.iter().map(|root| corpus.join(root)));
    run
}

/// How many tests the model corpus shares out over. Whole, its serial run and
/// its run at four outgrew the 30 s each test is held to (#3400); an eighth
/// stays well inside it under load.
const MODEL_SHARES: usize = 8;

/// Every source under `root`, a folder from the workspace root, each a path
/// from the workspace root, in path order.
///
/// # Specification
/// trivial.
fn sources(root: &Path) -> Vec<PathBuf>
{
    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut folders = vec![root.to_path_buf()];
    let mut found = Vec::new();
    while let Some(folder) = folders.pop() {
        for entry in std::fs::read_dir(workspace.join(&folder)).expect("the folder lists") {
            let path = folder.join(entry.expect("the entry reads").file_name());
            if workspace.join(&path).is_dir() {
                folders.push(path);
            }
            else if path
                .extension()
                .is_some_and(|extension| extension == "gandr")
            {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

/// One of the [`MODEL_SHARES`] tests the model corpus shares out over.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct ModelShare(usize);

impl ModelShare
{
    /// A `gandr test` over this share: every [`MODEL_SHARES`]-th source of
    /// the model corpus, starting at the share's own index.
    ///
    /// # Specification
    /// trivial.
    fn run(self) -> Vec<PathBuf>
    {
        let sources = sources(Path::new("corpus/model"));
        let taken: Vec<&Path> = sources
            .iter()
            .skip(self.0)
            .step_by(MODEL_SHARES)
            .map(PathBuf::as_path)
            .collect();
        share(&taken)
    }
}

// The corpus roots share out over the three wider widths, one test each: every
// source runs once serially and once off the serial schedule, and each width
// is observed over enough sources to interleave. Each root settles on its own,
// so a share prints what its roots print within a whole run. The model corpus
// is shared out by source over `MODEL_SHARES` tests, each source a root of its
// own: one source settles alone as it does within its folder.

#[test]
fn every_width_prints_the_serial_run_of_model_share_0_3400()
{
    agrees(&ModelShare(0).run(), &[Width::FourByFlag]);
}

#[test]
fn every_width_prints_the_serial_run_of_model_share_1_3400()
{
    agrees(&ModelShare(1).run(), &[Width::FourByFlag]);
}

#[test]
fn every_width_prints_the_serial_run_of_model_share_2_3400()
{
    agrees(&ModelShare(2).run(), &[Width::FourByFlag]);
}

#[test]
fn every_width_prints_the_serial_run_of_model_share_3_3400()
{
    agrees(&ModelShare(3).run(), &[Width::FourByFlag]);
}

#[test]
fn every_width_prints_the_serial_run_of_model_share_4_3400()
{
    agrees(&ModelShare(4).run(), &[Width::FourByFlag]);
}

#[test]
fn every_width_prints_the_serial_run_of_model_share_5_3400()
{
    agrees(&ModelShare(5).run(), &[Width::FourByFlag]);
}

#[test]
fn every_width_prints_the_serial_run_of_model_share_6_3400()
{
    agrees(&ModelShare(6).run(), &[Width::FourByFlag]);
}

#[test]
fn every_width_prints_the_serial_run_of_model_share_7_3400()
{
    agrees(&ModelShare(7).run(), &[Width::FourByFlag]);
}

#[test]
fn every_width_prints_the_serial_run_of_the_pathological_corpus()
{
    agrees(&share(&[Path::new("corpus/pathological")]), &[
        Width::ThreeByEnvironment,
    ]);
}

#[test]
fn every_width_prints_the_serial_run_of_the_other_roots()
{
    let roots = [
        "crates/surface-corpus/strict",
        "corpus/classifier",
        "corpus/fragment",
        "corpus/pending",
        "corpus/surface",
    ]
    .map(Path::new);
    agrees(&share(&roots), &[Width::Host]);
}

#[test]
fn every_width_prints_the_serial_check()
{
    let scratch = Scratch::new(Path::new("widths"));
    let settled = scratch.file(Path::new("answer.gandr"), Text::from("def answer = 42 ;\n"));
    let broken = scratch.file(
        Path::new("broken.gandr"),
        Text::from("def broken = missing ;\n"),
    );
    let empty = scratch.0.join("empty");
    std::fs::create_dir_all(&empty).expect("the empty directory is created");
    let check = [
        PathBuf::from("check"),
        settled,
        scratch.0.join("absent.gandr"),
        broken,
        empty,
        scratch.0.clone(),
    ];
    agrees(&check, &[
        Width::FourByFlag,
        Width::ThreeByEnvironment,
        Width::Host,
    ]);
}

#[test]
fn every_width_stages_the_serial_run()
{
    let at = |jobs: &[&str], environment: Option<&str>| {
        let mut command = gandr(&["stage", "pow:0..8", "double:0..8", "pow:0..4"]);
        command.args(jobs);
        match environment {
            Some(threads) => command.env("GANDR_JOBS", threads),
            None => command.env_remove("GANDR_JOBS"),
        };
        ran(command)
    };
    let serial = at(&["--jobs", "1"], None);
    assert_eq!(code(&serial), Code(0_i32), "{}", stderr(&serial));
    let printed = stdout(&serial);
    let lines: Vec<&str> = printed.lines().collect();
    assert_eq!(lines.len(), 5, "{printed}");
    assert!(lines[0].starts_with("pow:0..8: 9 of 9 certificates readmitted; "));
    assert!(lines[1].starts_with("double:0..8: 18 of 18 certificates readmitted; "));
    assert!(lines[2].starts_with("pow:0..4: 5 of 5 certificates readmitted; "));
    assert!(lines[3].strip_prefix("digest: ").is_some_and(
        |digest| digest.len() == 16 && digest.bytes().all(|byte| byte.is_ascii_hexdigit())
    ));
    assert_eq!(lines[4], "verdict: readmitted");
    for (label, wider) in [
        ("--jobs 4", at(&["--jobs", "4"], None)),
        ("GANDR_JOBS=3", at(&[], Some("3"))),
        ("the host's width", at(&[], None)),
    ] {
        assert_eq!(
            (code(&wider), stdout(&wider), stderr(&wider)),
            (code(&serial), stdout(&serial), stderr(&serial)),
            "{label} prints the serial run"
        );
    }
}

#[test]
fn a_malformed_invocation_exits_two()
{
    for arguments in [
        &["run"][..],
        &["frobnicate"],
        &["check", "--unknown", "a.gandr"],
        &["check", "--jobs", "0", "a.gandr"],
        &["stage"],
        &["stage", "triple:0..4"],
        &["stage", "pow:5..4"],
        &["stage", "double:0"],
    ] {
        let output = ran(gandr(arguments));
        assert_eq!(code(&output), Code(2_i32), "{arguments:?}");
        assert!(
            output.stdout.is_empty(),
            "{arguments:?}: nothing on standard output"
        );
    }
}

/// The fields of a package's model past its `name` and its `version`, each a
/// line of a model's body.
macro_rules! fields {
    () => {
        "  def authors = \"Ada\";\n  def licence = \"MIT\";\n  def documentation = \
         \"https://d.example\";\n  def endpoint = \"https://e.example\";\n  def gandr = \">= \
         0.0\";\n  def features = \"project-manifest\";\n  def systems = \"\";\n  def spelling = \
         \"\";\n"
    };
}

/// A package's source declaring its model, `name`, `version` and the
/// fields [`fields`] states, after [`STD_PACKAGE`].
const LIBRARY: &str = concat!(
    "/// The package.\npub module Package : Model(Gandr.Package) where {\n  def name = \"hello\";\n  def \
     version = \"0.1.0\";\n",
    fields!(),
    "}\n"
);

/// The import of the manifest theories, `std.build`, by the absolute path
/// to its source in the tree (#2767).
const STD_PACKAGE: &str = concat!(
    "import \"",
    env!("CARGO_MANIFEST_DIR"),
    "/../../library/std/src/build.gandr\";\n"
);

/// #2687: `check`, `test` and `fmt` run with no path work on the package the
/// working directory sits in, whole, from any directory in it; outside every
/// package each is refused before any source is read.
#[test]
fn a_verb_with_no_path_checks_the_package_it_runs_in_2687()
{
    let scratch = Scratch::new(Path::new("no-path"));
    let _library = scratch.file(
        Path::new("hello/src/package.gandr"),
        Text::from(format!("{STD_PACKAGE}{LIBRARY}").as_str()),
    );
    let _leaf = scratch.file(
        Path::new("hello/src/text/greet.gandr"),
        Text::from("/// A greeting.\ndef greeting = \"hello, world\" ;\n"),
    );
    let within = |arguments: &[&str], directory: &str| {
        let mut command = gandr(arguments);
        command.current_dir(scratch.0.join(directory));
        ran(command)
    };
    let checked = within(&["check"], "hello/src/text");
    assert_eq!(code(&checked), Code(0_i32), "{}", stderr(&checked));
    assert!(
        stdout(&checked).contains("sources: 2 read"),
        "the leaf's directory checks the whole package: {}",
        stdout(&checked)
    );
    for (arguments, directory) in [(&["test"][..], "hello"), (&["fmt"], "hello/src")] {
        let output = within(arguments, directory);
        assert_eq!(
            code(&output),
            Code(0_i32),
            "{arguments:?} in `{directory}`: {}",
            stderr(&output)
        );
    }
    for arguments in [&["check"][..], &["test"], &["fmt"]] {
        let output = within(arguments, ".");
        assert_eq!(
            code(&output),
            Code(2_i32),
            "{arguments:?} outside a package"
        );
        assert!(output.stdout.is_empty(), "{arguments:?}: nothing is read");
        assert!(
            stderr(&output).starts_with("gandr: no path given"),
            "{arguments:?}: {}",
            stderr(&output)
        );
    }
}

/// #2687, #3030: `check` writes a package's `gandr.toml` from its model,
/// leaves it unchanged when the model is, rewrites it when the model changes,
/// and refuses a hand edit as drift, leaving it as it stands; a package source
/// that states no `version`, and one that does not settle, write none. Each
/// reconciled manifest's line carries the package's address, which an edit to
/// an inert field leaves and an edit to a module's item moves.
#[test]
fn a_package_s_manifest_is_written_and_drift_refused_2687()
{
    let scratch = Scratch::new(Path::new("manifest"));
    let library = scratch.file(
        Path::new("hello/src/package.gandr"),
        Text::from(format!("{STD_PACKAGE}{LIBRARY}").as_str()),
    );
    let leaf = scratch.file(
        Path::new("hello/src/text/greet.gandr"),
        Text::from("def greeting = \"hello, world\" ;\n"),
    );
    let manifest = scratch.0.join("hello/gandr.toml");
    let checked = || {
        let mut command = gandr(&[Path::new("check"), &leaf]);
        command.current_dir(&scratch.0);
        ran(command)
    };
    let reconciled = |output: &Output| {
        stdout(output)
            .lines()
            .find_map(|line| line.strip_prefix("manifest: "))
            .and_then(|line| line.strip_suffix(')'))
            .and_then(|line| line.split_once(" (address "))
            .map(|(reconciled, address)| (String::from(reconciled), String::from(address)))
    };
    let written = checked();
    assert_eq!(code(&written), Code(0_i32), "{}", stderr(&written));
    let Some((line, address)) = reconciled(&written)
    else {
        panic!("a manifest line with an address: {}", stdout(&written));
    };
    assert_eq!(
        line,
        format!(
            "{}: written",
            manifest.canonicalize().expect("written").display()
        )
    );
    assert!(
        address.len() == 64 && address.bytes().all(|byte| byte.is_ascii_hexdigit()),
        "a BLAKE3 digest in hex: {address}"
    );
    let first = std::fs::read_to_string(&manifest).expect("the manifest is written");
    assert!(
        first.ends_with(
            "\n[package]\nname = \"hello\"\nversion = \"0.1.0\"\nauthors = \"Ada\"\nlicence = \
             \"MIT\"\ndocumentation = \"https://d.example\"\nendpoint = \
             \"https://e.example\"\nmodules = [\n  \"text.greet\",\n]\n\n[toolchain]\ngandr = \">= \
             0.0\"\nfeatures = [\n  \"project-manifest\",\n]\nsystems = []\n"
        ),
        "{first}"
    );
    let again = checked();
    assert_eq!(code(&again), Code(0_i32));
    assert!(
        reconciled(&again)
            .is_some_and(|(line, again)| line.ends_with(": unchanged") && again == address)
    );
    std::fs::write(
        &library,
        format!(
            "{STD_PACKAGE}{}",
            LIBRARY
                .replace("0.1.0", "0.2.0")
                .replace("MIT", "Apache-2.0")
        ),
    )
    .expect("the model changes");
    let rewritten = checked();
    assert_eq!(code(&rewritten), Code(0_i32));
    assert!(
        reconciled(&rewritten)
            .is_some_and(|(line, inert)| line.ends_with(": rewritten") && inert == address),
        "an edit to inert fields leaves the address: {}",
        stdout(&rewritten)
    );
    let second = std::fs::read_to_string(&manifest).expect("the manifest is rewritten");
    assert!(second.contains("version = \"0.2.0\""), "{second}");
    std::fs::write(&leaf, "def greeting = \"hello, there\" ;\n").expect("the module changes");
    let moved = checked();
    assert_eq!(code(&moved), Code(0_i32), "{}", stderr(&moved));
    assert!(
        reconciled(&moved)
            .is_some_and(|(line, moved)| line.ends_with(": unchanged") && moved != address),
        "an edit to a module's item moves the address: {}",
        stdout(&moved)
    );
    let edited = second.replace("hello", "howdy");
    std::fs::write(&manifest, &edited).expect("the hand edit is written");
    let drifted = checked();
    assert_eq!(code(&drifted), Code(1_i32), "a hand edit unsettles the run");
    assert!(
        stderr(&drifted).contains("gandr.toml: drifted"),
        "{}",
        stderr(&drifted)
    );
    assert_eq!(
        std::fs::read_to_string(&manifest).expect("the manifest reads"),
        edited,
        "left as it stands"
    );
    std::fs::remove_file(&manifest).expect("the manifest is removed");
    std::fs::write(
        &library,
        format!(
            "{STD_PACKAGE}pub module Package : Model(Gandr.Package) where {{\n  def name = \"hello\";\n}}\n"
        ),
    )
    .expect("the model loses its version");
    let unstated = checked();
    assert_ne!(code(&unstated), Code(0_i32), "{}", stdout(&unstated));
    assert!(!manifest.exists(), "no manifest is written");
    std::fs::write(&library, "def name : Integer ;\ndef name = \"hello\" ;\n")
        .expect("the library is ill-typed");
    let unsettled = checked();
    assert_eq!(code(&unsettled), Code(1_i32));
    assert!(
        !manifest.exists(),
        "an unsettled library writes no manifest"
    );
}

/// #3135: `check` of a package whose toolchain constraints the running
/// toolchain meets writes its manifest; one asking for a later language
/// version, a feature the toolchain's ledger does not implement or a system
/// it does not run on is refused by that clause, naming the field and both
/// sides, and leaves the manifest as it stands.
#[test]
fn a_package_s_toolchain_is_met_or_refused_by_its_clause_3135()
{
    let scratch = Scratch::new(Path::new("toolchain"));
    let library = scratch.file(
        Path::new("hello/src/package.gandr"),
        Text::from(format!("{STD_PACKAGE}{LIBRARY}").as_str()),
    );
    let manifest = scratch.0.join("hello/gandr.toml");
    let checked = || {
        let mut command = gandr(&[Path::new("check"), &library]);
        command.current_dir(&scratch.0);
        ran(command)
    };
    let met = checked();
    assert_eq!(code(&met), Code(0_i32), "{}", stderr(&met));
    let written = std::fs::read_to_string(&manifest).expect("the manifest is written");
    for (from, to, clause) in [
        (
            "\">= 0.0\"",
            "\">= 99.0\"",
            "ToolchainUnmet.gandr: `Package.gandr` asks for gandr `>= 99.0`, and this toolchain is \
             gandr 0.0.0",
        ),
        (
            "\"project-manifest\"",
            "\"project-manifest, not-a-feature\"",
            "ToolchainUnmet.feature.not-a-feature: `Package.features` asks for `not-a-feature`, \
             which this toolchain's features ledger does not implement",
        ),
        (
            "systems = \"\"",
            "systems = \"none-such\"",
            "ToolchainUnmet.system: `Package.systems` asks for one of `none-such`, and this \
             toolchain runs on `",
        ),
    ] {
        std::fs::write(
            &library,
            format!("{STD_PACKAGE}{}", LIBRARY.replace(from, to)),
        )
        .expect("the constraint changes");
        let unmet = checked();
        assert_eq!(code(&unmet), Code(1_i32), "{to}: {}", stdout(&unmet));
        assert!(
            stderr(&unmet).contains(&format!("package.gandr: {clause}")),
            "{to}: {}",
            stderr(&unmet)
        );
        assert!(
            !stdout(&unmet).contains("manifest: "),
            "{to}: nothing is reconciled"
        );
        assert_eq!(
            std::fs::read_to_string(&manifest).expect("the manifest reads"),
            written,
            "{to}: the manifest is left as it stands"
        );
    }
}

/// #3072, #4527: `check` of a package importing a sibling by its coordinate
/// writes its `gandr.lock` once, through which its source reads the sibling,
/// and its manifest with no dependency table, and leaves the lock unchanged on
/// a second run; a content edit to the sibling is refused as
/// `LockDrift.path:../hello`, the lock left byte for byte, until `gandr lock`
/// rewrites it and `check` settles again.
#[test]
fn check_writes_a_lock_and_refuses_its_drift_3072()
{
    let scratch = Scratch::new(Path::new("lock"));
    let hello = scratch.file(
        Path::new("hello/src/package.gandr"),
        Text::from(format!("{STD_PACKAGE}{LIBRARY}pub def welcome = \"hello\";\n").as_str()),
    );
    let _sibling = scratch.file(
        Path::new("sibling/src/package.gandr"),
        Text::from(
            format!(
                "import \"path:../hello\" as hello;\n{STD_PACKAGE}{}pub def greeting = \
                 hello.welcome;\n",
                LIBRARY.replace("\"hello\"", "\"sibling\"")
            )
            .as_str(),
        ),
    );
    let lock = scratch.0.join("sibling/gandr.lock");
    let verb = |name: &str| {
        let mut command = gandr(&[Path::new(name), Path::new("sibling")]);
        command.current_dir(&scratch.0);
        ran(command)
    };
    let line = |output: &Output| {
        stdout(output)
            .lines()
            .find_map(|line| line.strip_prefix("lock: "))
            .map(String::from)
    };
    let written = verb("check");
    assert_eq!(code(&written), Code(0_i32), "{}", stderr(&written));
    let named = lock.canonicalize().expect("the lock is written");
    assert_eq!(
        line(&written),
        Some(format!("{}: written", named.display())),
        "{}",
        stdout(&written)
    );
    let first = std::fs::read_to_string(&lock).expect("the lock reads");
    let manifest =
        std::fs::read_to_string(scratch.0.join("sibling/gandr.toml")).expect("the manifest reads");
    assert!(
        !manifest.contains("[dependencies]"),
        "the manifest renders no dependency table: {manifest}"
    );
    let again = verb("check");
    assert_eq!(code(&again), Code(0_i32), "{}", stderr(&again));
    assert_eq!(
        line(&again),
        Some(format!("{}: unchanged", named.display()))
    );
    assert_eq!(
        std::fs::read_to_string(&lock).ok().as_ref(),
        Some(&first),
        "a second run leaves the lock byte for byte"
    );
    std::fs::write(
        &hello,
        format!("{STD_PACKAGE}{LIBRARY}pub def welcome = \"howdy\";\n"),
    )
    .expect("hello changes");
    let drifted = verb("check");
    assert_eq!(code(&drifted), Code(1_i32), "drift unsettles the run");
    assert!(
        stderr(&drifted).contains("gandr.lock: LockDrift.path:../hello: "),
        "{}",
        stderr(&drifted)
    );
    assert_eq!(
        std::fs::read_to_string(&lock).ok().as_ref(),
        Some(&first),
        "a drifted lock is left as it stands"
    );
    let relocked = verb("lock");
    assert_eq!(code(&relocked), Code(0_i32), "{}", stderr(&relocked));
    assert_eq!(
        line(&relocked),
        Some(format!("{}: rewritten", named.display()))
    );
    let settled = verb("check");
    assert_eq!(code(&settled), Code(0_i32), "{}", stderr(&settled));
    assert_eq!(
        line(&settled),
        Some(format!("{}: unchanged", named.display()))
    );
}

/// #3157: `check` of a package depending on a sibling opens the store under
/// the XDG data home and locks the sibling by a pointer into it, whose chunk
/// the store holds; removing the store leaves the lock as it stands on the
/// next run, which commits the chunk again; and a run with nowhere to put the
/// store faults before it checks anything.
#[test]
fn a_package_s_lock_points_into_the_store_the_run_opens_3157()
{
    let scratch = Scratch::new(Path::new("store"));
    let _hello = scratch.file(
        Path::new("hello/src/package.gandr"),
        Text::from(format!("{STD_PACKAGE}{LIBRARY}pub def welcome = \"hello\";\n").as_str()),
    );
    let _sibling = scratch.file(
        Path::new("sibling/src/package.gandr"),
        Text::from(
            format!(
                "import \"path:../hello\" as hello;\n{STD_PACKAGE}{}pub def greeting = \
                 hello.welcome;\n",
                LIBRARY.replace("\"hello\"", "\"sibling\"")
            )
            .as_str(),
        ),
    );
    let data = scratch.0.join("data");
    let chunks = data.join("gandr/store/chunks");
    let check = || {
        let mut command = gandr(&[Path::new("check"), Path::new("sibling")]);
        command.current_dir(&scratch.0).env("XDG_DATA_HOME", &data);
        ran(command)
    };
    let first = check();
    assert_eq!(code(&first), Code(0_i32), "{}", stderr(&first));
    let lock =
        std::fs::read_to_string(scratch.0.join("sibling/gandr.lock")).expect("the lock reads");
    let pointer = lock
        .lines()
        .find_map(|line| line.strip_prefix("\"path:../hello\" = { pointer = \""))
        .and_then(|rest| rest.strip_suffix("\" }"))
        .expect("the lock locks hello by a pointer");
    let (digest, offset) = pointer
        .split_once(':')
        .expect("a pointer is a digest and an offset");
    assert_eq!(offset, "0", "an identity is its chunk's root");
    assert!(
        chunks.join(digest).is_file(),
        "the store under the XDG data home holds the pointer's chunk: {}",
        chunks.display()
    );
    std::fs::remove_dir_all(&data).expect("the store is removed");
    let again = check();
    assert_eq!(code(&again), Code(0_i32), "{}", stderr(&again));
    assert_eq!(
        std::fs::read_to_string(scratch.0.join("sibling/gandr.lock"))
            .ok()
            .as_ref(),
        Some(&lock),
        "removing the store leaves the lock as it stands"
    );
    assert!(
        chunks.join(digest).is_file(),
        "the run commits the chunk again"
    );
    let mut homeless = gandr(&[Path::new("check"), Path::new("sibling")]);
    let _unset = homeless
        .current_dir(&scratch.0)
        .env_remove("XDG_DATA_HOME")
        .env_remove("HOME");
    let faulted = ran(homeless);
    assert_eq!(code(&faulted), Code(2_i32), "{}", stderr(&faulted));
    assert_eq!(
        stderr(&faulted),
        "gandr: no directory names the store: set `XDG_DATA_HOME` or `HOME`\n"
    );
}

/// #3225: `check` of a package commits its export into the store the run
/// opens, under the root `export/<address>`, the address its manifest line
/// prints: the export holds the package source's artifact and a module's, which
/// the store reads back, and a second check names the same pointer; a package
/// with an unsettled source names no export.
#[test]
fn a_checked_package_s_export_is_named_by_its_address_3225()
{
    let scratch = Scratch::new(Path::new("export"));
    let _library = scratch.file(
        Path::new("hello/src/package.gandr"),
        Text::from(format!("{STD_PACKAGE}{LIBRARY}pub def welcome = \"hello\";\n").as_str()),
    );
    let _module = scratch.file(
        Path::new("hello/src/text/greet.gandr"),
        Text::from("def greeting = \"hello, world\" ;\n"),
    );
    let data = scratch.0.join("data");
    let check = || {
        let mut command = gandr(&[Path::new("check"), Path::new("hello")]);
        command.current_dir(&scratch.0).env("XDG_DATA_HOME", &data);
        ran(command)
    };
    // The export the root names, after a run that printed `output`.
    let exported = |output: &Output| {
        let Some(address) = stdout(output)
            .lines()
            .find_map(|line| line.strip_prefix("manifest: "))
            .and_then(|line| line.strip_suffix(')'))
            .and_then(|line| line.split_once(" (address "))
            .map(|(_, address)| String::from(address))
        else {
            panic!("a manifest line with an address: {}", stdout(output));
        };
        let store = Store::open(&data.join("gandr/store")).expect("the run's store opens");
        let Maybe::Present(pointer) = store
            .roots()
            .root(&RootName::new(format!("export/{address}")))
        else {
            panic!("the address names an export: {}", stdout(output));
        };
        let export: Export = store.deref(pointer).expect("the export reads back");
        (pointer, export)
    };
    let first = check();
    assert_eq!(code(&first), Code(0_i32), "{}", stderr(&first));
    let (pointer, export) = exported(&first);
    for source in ["src/package.gandr", "src/text/greet.gandr"] {
        assert!(
            matches!(export.artifact(Path::new(source)), Maybe::Present(_)),
            "the export holds {source}'s artifact"
        );
    }
    let again = check();
    assert_eq!(code(&again), Code(0_i32), "{}", stderr(&again));
    assert_eq!(
        exported(&again).0,
        pointer,
        "a second check names the same export"
    );
    std::fs::remove_dir_all(&data).expect("the store is removed");
    let _broken = scratch.file(
        Path::new("hello/src/text/broken.gandr"),
        Text::from("def broken = missing ;\n"),
    );
    let unsettled = check();
    assert_eq!(code(&unsettled), Code(1_i32), "{}", stderr(&unsettled));
    let store = Store::open(&data.join("gandr/store")).expect("the run's store opens");
    assert!(
        store
            .roots()
            .names()
            .all(|name| !name.as_ref().starts_with("export/")),
        "a package with an unsettled source names no export"
    );
}

/// #3285: `check` of a dependent beside its path dependency re-admits the
/// dependency's export through the kernel, read from the store by the root
/// the dependency's address names once every export of the run is committed:
/// the detailed level prints the declarations re-admitted, which are the
/// export's, and the default level prints nothing of it; the dependent
/// checked alone against a fresh store notes the export it finds none of and
/// settles; and a root that names what is no export faults the run.
#[test]
fn a_dependent_re_admits_its_dependency_s_export_3285()
{
    let scratch = Scratch::new(Path::new("readmit"));
    let _hello = scratch.file(
        Path::new("hello/src/package.gandr"),
        Text::from(format!("{STD_PACKAGE}{LIBRARY}pub def welcome = \"hello\";\n").as_str()),
    );
    let _sibling = scratch.file(
        Path::new("sibling/src/package.gandr"),
        Text::from(
            format!(
                "import \"path:../hello\" as hello;\n{STD_PACKAGE}{}pub def greeting = \
                 hello.welcome;\n",
                LIBRARY.replace("\"hello\"", "\"sibling\"")
            )
            .as_str(),
        ),
    );
    let check = |level: &str, data: &Path, packages: &[&str]| {
        let mut command = gandr(&["check", "--verbosity", level]);
        let _configured = command
            .args(packages)
            .current_dir(&scratch.0)
            .env("XDG_DATA_HOME", data);
        ran(command)
    };
    let data = scratch.0.join("data");
    let base = scratch
        .0
        .canonicalize()
        .expect("the scratch directory canonicalizes");
    let (hello, sibling) = (base.join("hello"), base.join("sibling"));
    let both = check("detailed", &data, &["hello", "sibling"]);
    assert_eq!(code(&both), Code(0_i32), "{}", stderr(&both));
    let Some(address) = stdout(&both)
        .lines()
        .filter_map(|line| line.strip_prefix("manifest: "))
        .find(|line| line.starts_with(hello.to_string_lossy().as_ref()))
        .and_then(|line| line.strip_suffix(')'))
        .and_then(|line| line.split_once(" (address "))
        .map(|(_, address)| String::from(address))
    else {
        panic!("hello's manifest line names its address: {}", stdout(&both));
    };
    let root = format!("export/{address}");
    let store = Store::open(&data.join("gandr/store")).expect("the run's store opens");
    let Maybe::Present(pointer) = store.roots().root(&RootName::new(root.clone()))
    else {
        panic!("hello's address names its export: {}", stdout(&both));
    };
    let export: Export = store.deref(pointer).expect("hello's export reads back");
    let declarations = usize::from(export.readmit().expect("hello's export re-admits"));
    let readmitted: Vec<String> = stdout(&both)
        .lines()
        .filter(|line| line.starts_with("export: "))
        .map(String::from)
        .collect();
    assert_eq!(
        readmitted,
        [format!(
            "export: {}: path:../hello: {declarations} declarations re-admitted from {root}",
            sibling.display()
        )],
        "the dependent re-admits each declaration of its dependency's export"
    );
    let quiet = check("user", &data, &["hello", "sibling"]);
    assert_eq!(code(&quiet), Code(0_i32), "{}", stderr(&quiet));
    assert!(
        !stdout(&quiet).contains("re-admitted") && stderr(&quiet).is_empty(),
        "the default level prints nothing of a re-admission: {}{}",
        stdout(&quiet),
        stderr(&quiet)
    );
    let fresh = check("user", &scratch.0.join("fresh"), &["sibling"]);
    assert_eq!(code(&fresh), Code(0_i32), "{}", stderr(&fresh));
    assert_eq!(
        stderr(&fresh),
        format!(
            "gandr: {}: path:../hello: no export at {root}; check {} first\n",
            sibling.display(),
            hello.display()
        ),
        "a dependent checked alone against a fresh store notes the missing export"
    );
    let Maybe::Present(package) = Package::discover(&sibling)
    else {
        panic!("sibling roots a package");
    };
    let Maybe::Present(lock) = Lock::read(&package)
    else {
        panic!("sibling's check wrote its lock");
    };
    let Some(identity) = lock
        .coordinates()
        .find_map(|coordinate| lock.locked(coordinate))
    else {
        panic!("sibling's lock locks hello");
    };
    let mut store = store;
    store
        .set_root(RootName::new(root.clone()), identity)
        .expect("the root is repointed");
    let faulted = check("user", &data, &["sibling"]);
    assert_eq!(code(&faulted), Code(2_i32), "{}", stderr(&faulted));
    assert!(
        stderr(&faulted).starts_with(&format!(
            "gandr: {}: path:../hello: {root}: ",
            sibling.display()
        )),
        "a root naming what is no export faults the run: {}",
        stderr(&faulted)
    );
}

/// #2687: a workspace's `check` with no path, at its root or in a directory
/// of it in no package, checks its source and each member it names and writes
/// each member's `gandr.toml` from that member's own model, though both
/// package sources import the workspace and declare the same paths; a member
/// rooting no package refuses the verb before any source is read.
#[test]
fn a_workspace_checks_each_member_it_names_2687()
{
    let scratch = Scratch::new(Path::new("workspace"));
    let stated = |members: &str| {
        format!(
            "{STD_PACKAGE}pub module Workspace : Model(Gandr.Workspace) where {{\n  def version = \
             \"0.2.0\";\n  def gandr = \"\";\n  def features = \"\";\n  def systems = \
             \"\";\n}}\npub def members : List(String) = {members};\n"
        )
    };
    let workspace = scratch.file(
        Path::new("workspace.gandr"),
        Text::from(stated("[\"hello\", \"tools\"]").as_str()),
    );
    for (library, name, up) in [
        ("hello/src/package.gandr", "hello", "../.."),
        ("tools/package.gandr", "tools", ".."),
    ] {
        let _library = scratch.file(
            Path::new(library),
            Text::from(
                format!(
                    "{STD_PACKAGE}import \"{up}/workspace.gandr\";\npub module Package : \
                     Model(Gandr.Package) where {{\n  def name = \"{name}\";\n  def version = \
                     Workspace.version;\n{}}}\n",
                    fields!()
                )
                .as_str(),
            ),
        );
    }
    let _notes = scratch.file(
        Path::new("docs/notes.gandr"),
        Text::from("def note = 1 ;\n"),
    );
    let within = |directory: &str| {
        let mut command = gandr(&["check"]);
        command.current_dir(scratch.0.join(directory));
        ran(command)
    };
    for directory in [".", "docs"] {
        for member in ["hello", "tools"] {
            let _removed = std::fs::remove_file(scratch.0.join(member).join("gandr.toml"));
        }
        let checked = within(directory);
        assert_eq!(code(&checked), Code(0_i32), "{}", stderr(&checked));
        assert!(
            stdout(&checked).contains("sources: 3 read"),
            "`{directory}` checks the workspace and both members: {}",
            stdout(&checked)
        );
        for (member, name) in [("hello", "hello"), ("tools", "tools")] {
            let manifest = std::fs::read_to_string(scratch.0.join(member).join("gandr.toml"))
                .expect("each member's manifest is written");
            assert!(
                manifest.contains(&format!("name = \"{name}\"\nversion = \"0.2.0\"\n")),
                "`{member}`'s manifest states its own model from `{directory}`: {manifest}"
            );
        }
    }
    std::fs::write(&workspace, stated("[\"hello\", \"docs\"]")).expect("a member is misnamed");
    let refused = within(".");
    assert_eq!(code(&refused), Code(2_i32), "{}", stdout(&refused));
    assert!(refused.stdout.is_empty(), "nothing is read");
    assert!(
        stderr(&refused).contains("the member `docs` of `workspace.gandr` roots no package"),
        "{}",
        stderr(&refused)
    );
}

/// #2687: the witness workspace's committed `gandr.toml` files are the ones
/// its members' models render: checking the workspace leaves each unchanged.
/// #3072: `tools`' committed `gandr.lock` is the one its dependency on
/// `hello` resolves to wherever the tree is checked out, so the check leaves
/// it unchanged too.
#[test]
fn the_witness_project_s_manifest_is_its_model_s_2687()
{
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/projects");
    let output = ran(gandr(&[Path::new("check"), &workspace]));
    assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
    let printed = stdout(&output);
    let reconciled: Vec<&str> = printed
        .lines()
        .filter(|line| line.starts_with("manifest: "))
        .collect();
    assert_eq!(reconciled.len(), 2, "{printed}");
    assert!(
        reconciled
            .iter()
            .all(|line| line.contains("gandr.toml: unchanged (address ")),
        "{printed}"
    );
    let locked: Vec<&str> = printed
        .lines()
        .filter(|line| line.starts_with("lock: "))
        .collect();
    assert!(
        matches!(locked.as_slice(), [line] if line.ends_with("projects/tools/gandr.lock: unchanged")),
        "{printed}"
    );
}

/// #3558: `--admit native-conversion` takes the emitter tier's answer for
/// `fibonacci`'s closed pair without the kernel deriving it, and says so: the
/// report counts the one result taken, and the verdict names the policy and
/// the tier. Without the flag nothing is taken, and the report is as before.
#[test]
fn check_admit_takes_the_tier_s_answer_and_says_so_3558()
{
    let row =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/conversion/fibonacci.gandr");
    let checked = |admit: &[&str]| {
        let mut arguments = vec![
            std::ffi::OsString::from("check"),
            std::ffi::OsString::from("--recheck"),
        ];
        arguments.extend(admit.iter().map(std::ffi::OsString::from));
        arguments.push(row.clone().into_os_string());
        let output = ran(gandr(&arguments));
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
        stdout(&output)
    };
    let admitted = checked(&["--admit", "native-conversion"]);
    assert!(
        admitted
            .lines()
            .any(|line| line == "admitted: 1 taken from the emitter tier"),
        "{admitted}"
    );
    assert!(
        admitted
            .lines()
            .any(|line| line
                == "verdict: settled, admitting native-conversion from the emitter tier"),
        "{admitted}"
    );
    let derived = checked(&[]);
    assert!(!derived.contains("admitted: "), "{derived}");
    assert!(
        derived.lines().any(|line| line == "verdict: settled"),
        "{derived}"
    );
}

#[test]
fn a_grant_bounds_held_capabilities_and_refuses_an_unknown_operation()
{
    let scratch = Scratch::new(Path::new("grant"));
    let source = scratch.file(
        Path::new("held.gandr"),
        Text::from("def fs : Cap {read, write} ;\n"),
    );
    let at = |grant: &[&str]| {
        let mut command = gandr(&["check"]);
        command.args(grant).arg(&source);
        ran(command)
    };
    let narrow = at(&["--grant", "read"]);
    assert_eq!(code(&narrow), Code(1_i32), "{}", stderr(&narrow));
    assert!(
        stdout(&narrow).contains("error[CapabilityUngranted]"),
        "a capability claiming `write` beyond the grant is refused by name: {}",
        stdout(&narrow)
    );
    for grant in [
        &["--grant", "read,write"][..],
        &["--grant", "write", "--grant", "read"],
        &[],
    ] {
        let within = at(grant);
        assert_eq!(code(&within), Code(1_i32), "{grant:?}");
        assert!(
            stdout(&within).contains("`fs` states checks owing 0; produced checks owing 1")
                && !stdout(&within).contains("CapabilityUngranted"),
            "{grant:?}: a capability within the grant, or under none, is owed: {}",
            stdout(&within)
        );
    }
    let unknown = at(&["--grant", "read,delete"]);
    assert_eq!(code(&unknown), Code(2_i32));
    assert!(unknown.stdout.is_empty(), "no source is read");
    assert_eq!(
        stderr(&unknown),
        "gandr: --grant: no host interface offers `delete`\n"
    );
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
    assert!(version.stderr.is_empty() && stderr(&status).is_empty());
}

#[test]
fn unwritable_standard_output_exits_two()
{
    let scratch = Scratch::new(Path::new("unwritable"));
    let source = scratch.file(Path::new("answer.gandr"), Text::from("def answer = 42 ;\n"));
    let program = scratch.file(
        Path::new("program.gandr"),
        Text::from("def answer : +U (-F Integer) ; def answer = thunk { return 17 } ;"),
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
/// - hypothesis: L3 — initialization, shutdown and exit produce two response
///   frames and clean completion; initialization alone ends abruptly. Missing
///   or reordered input changes cardinality or status. Arbitrary bodies and
///   size limits belong to the transport rather than this finite session.
/// - witness: `tests::cli::lsp_serves_a_session_over_the_standard_streams`
#[spec(ensures: |ref ret| messages.last().map_or_else(
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

/// The finished run of `gandr` with `arguments`, and `input` on standard
/// input, its output captured.
///
/// # Specification
/// - requires: a finite input whose pipe write completes before server exit,
///   with no external process termination.
/// - ensures: closes client input after sending it, waits for the server and
///   captures both output streams and its process status.
/// - provides: end-of-input and protocol-boundary observations.
/// - fails: never.
/// - panics: on process or pipe failure.
///
/// # Adequacy
/// - hypothesis: L3 — a complete session, premature EOF and truncated frame
///   produce distinct zero, one and two statuses. Unclosed input, missing
///   writes or lost termination state changes those cases; large backpressured
///   sessions and external signals are excluded.
/// - witness: `tests::cli::lsp_serves_a_session_over_the_standard_streams`
/// - witness: `tests::cli::lsp_clients_share_one_engine_hub`
#[spec(ensures: |ref ret| matches!(ret.status.code(), Some(0 ..= 2)))]
fn served<Argument>(
    arguments: &[Argument],
    input: &Body,
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
        .write_all(input.as_ref())
        .expect("the session is written");
    child.wait_with_output().expect("the driver runs")
}

#[test]
fn lsp_serves_a_session_over_the_standard_streams()
{
    let initialize = Text::from(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#);
    let shutdown = Text::from(r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#);
    let exit = Text::from(r#"{"jsonrpc":"2.0","method":"exit"}"#);
    let standalone = ["lsp", "--standalone"];
    let output = served(&standalone, &frames(&[initialize, shutdown, exit]));
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

    let output = served(&standalone, &frames(&[initialize]));
    assert_eq!(
        code(&output),
        Code(1_i32),
        "a session closed before shutdown exits one"
    );

    let output = served(
        &standalone,
        &Body::from(b"Content-Length: 9\r\n\r\n{".to_vec()),
    );
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

#[test]
fn the_printed_capabilities_are_what_a_session_is_initialized_with()
{
    let printed = ran(gandr(&["lsp", "--capabilities"]));
    assert_eq!(code(&printed), Code(0_i32), "{}", stderr(&printed));
    let printed = stdout(&printed);
    assert_eq!(printed.lines().count(), 1_usize, "one line: {printed}");
    let session = served(
        &["lsp", "--standalone"],
        &frames(&[
            Text::from(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#),
            Text::from(r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#),
            Text::from(r#"{"jsonrpc":"2.0","method":"exit"}"#),
        ]),
    );
    let mut replies = session.stdout.as_slice();
    let Maybe::Present(initialized) = read_frame(&mut replies).expect("a response is framed")
    else {
        panic!("initialize is answered");
    };
    let initialized = String::from_utf8(initialized.as_ref().to_vec()).expect("UTF-8");
    assert!(
        initialized.contains(&format!(r#""result":{}"#, printed.trim_end())),
        "the printed line is the initialize result: {printed} against {initialized}"
    );
}

#[test]
fn lsp_clients_share_one_engine_hub()
{
    use std::ffi::OsStr;

    // The name is short: a socket path must fit the platform's limit.
    let scratch = Scratch::new(Path::new("hub"));
    let socket = scratch.0.join("hub.sock");
    let session = frames(&[
        Text::from(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#),
        Text::from(r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#),
        Text::from(r#"{"jsonrpc":"2.0","method":"exit"}"#),
    ]);
    let client = [
        OsStr::new("lsp"),
        OsStr::new("--socket"),
        socket.as_os_str(),
        OsStr::new("--linger-ms"),
        OsStr::new("2000"),
    ];
    let first = served(&client, &session);
    assert_eq!(code(&first), Code(0_i32), "{}", stderr(&first));
    assert_eq!(
        first.stdout,
        served(&["lsp", "--standalone"], &session).stdout,
        "a relayed session answers as a standalone one does"
    );
    assert!(
        socket.exists(),
        "the hub a client started outlives it by its linger"
    );
    let second = served(&client, &session);
    assert_eq!(code(&second), Code(0_i32), "{}", stderr(&second));
    let another = gandr(&[
        OsStr::new("serve"),
        OsStr::new("--socket"),
        socket.as_os_str(),
    ])
    .output()
    .expect("the driver runs");
    assert_eq!(code(&another), Code(0_i32));
    assert!(
        stderr(&another).starts_with("gandr: a hub already serves"),
        "a second hub on one socket leaves it to the first"
    );
    let broken = served(&client, &Body::from(b"Content-Length: 9\r\n\r\n{".to_vec()));
    assert_eq!(
        code(&broken),
        Code(2_i32),
        "a broken client stream exits two"
    );
    let deadline = std::time::Instant::now() + core::time::Duration::from_secs(20);
    while socket.exists() && std::time::Instant::now() < deadline {
        std::thread::sleep(core::time::Duration::from_millis(50));
    }
    assert!(
        !socket.exists(),
        "the hub exits after its linger, removing its socket"
    );
}

/// Two builds' relays in one workspace each start a hub of their own, and a
/// second relay of one build reaches the hub its first started.
///
/// Linux alone: the other build is the driver with one byte appended, which a
/// platform that checks an executable's signature would refuse to run.
#[cfg(target_os = "linux")]
#[test]
fn a_relay_reaches_only_a_hub_of_its_own_build()
{
    // The name is short: a socket path must fit the platform's limit.
    let scratch = Scratch::new(Path::new("builds"));
    let runtime = scratch.0.join("run");
    let workspace = scratch.0.join("workspace");
    std::fs::create_dir_all(&workspace).expect("the workspace is made");
    let built = PathBuf::from(env!("CARGO_BIN_EXE_gandr"));
    let other = scratch.0.join("gandr");
    let _copied = std::fs::copy(&built, &other).expect("the driver is copied");
    std::fs::OpenOptions::new()
        .append(true)
        .open(&other)
        .and_then(|mut file| file.write_all(&[0_u8]))
        .expect("the copy is made another build");
    let relay = |driver: &Path| {
        let mut command = Command::new(driver);
        for (key, value) in gandr::<&str>(&[]).get_envs() {
            let _set = match value {
                Some(value) => command.env(key, value),
                None => command.env_remove(key),
            };
        }
        let _configured = command
            .args(["mcp", "--linger-ms", "3000"])
            .current_dir(&workspace)
            .env("XDG_RUNTIME_DIR", &runtime)
            .stdin(Stdio::null());
        // A test thread forking while the copy was open for writing holds it
        // until that child execs, and the kernel refuses to run it meanwhile.
        let output = loop {
            match command.output() {
                Err(error) if error.kind() == std::io::ErrorKind::ExecutableFileBusy => {
                    std::thread::sleep(core::time::Duration::from_millis(20));
                },
                ran => break ran.expect("the relay runs"),
            }
        };
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
    };
    let sockets = || {
        std::fs::read_dir(runtime.join("gandr")).map_or(0_usize, |entries| {
            entries
                .filter(|entry| {
                    entry.as_ref().is_ok_and(|entry| {
                        entry
                            .path()
                            .extension()
                            .is_some_and(|extension| extension == "sock")
                    })
                })
                .count()
        })
    };
    relay(&built);
    assert_eq!(sockets(), 1_usize, "the first relay starts a hub");
    relay(&other);
    assert_eq!(
        sockets(),
        2_usize,
        "a relay of another build starts a hub of its own"
    );
    relay(&built);
    assert_eq!(
        sockets(),
        2_usize,
        "a second relay of one build reaches the hub its first started"
    );
    let deadline = std::time::Instant::now() + core::time::Duration::from_secs(20);
    while sockets() != 0_usize && std::time::Instant::now() < deadline {
        std::thread::sleep(core::time::Duration::from_millis(50));
    }
    assert_eq!(
        sockets(),
        0_usize,
        "each hub lingers out once its clients leave"
    );
}

/// Two builds of this driver, one byte apart, linked as the toolchains
/// `first` and `second` under a scratch data directory, `first` the default;
/// a workspace beside them, and a runtime directory for their hubs.
#[cfg(target_os = "linux")]
struct Builds
{
    /// The first build's directory.
    first: PathBuf,
    /// The second build's directory.
    second: PathBuf,
    /// The directory every command runs in.
    workspace: PathBuf,
    /// The data directory holding the toolchains.
    data: PathBuf,
    /// The runtime directory holding the hubs.
    runtime: PathBuf,
}

#[cfg(target_os = "linux")]
impl Builds
{
    /// The two builds under `scratch`, linked.
    ///
    /// # Specification
    /// trivial.
    fn linked(scratch: &Scratch) -> Self
    {
        let built = PathBuf::from(env!("CARGO_BIN_EXE_gandr"));
        let builds = Self {
            first: scratch.0.join("first"),
            second: scratch.0.join("second"),
            workspace: scratch.0.join("workspace"),
            data: scratch.0.join("data"),
            runtime: scratch.0.join("run"),
        };
        std::fs::create_dir_all(&builds.workspace).expect("the workspace is made");
        for (directory, byte) in [&builds.first, &builds.second]
            .into_iter()
            .zip([0_u8, 1_u8])
        {
            std::fs::create_dir_all(directory).expect("the build's directory is made");
            let driver = directory.join("gandr");
            let _copied = std::fs::copy(&built, &driver).expect("the driver is copied");
            std::fs::OpenOptions::new()
                .append(true)
                .open(&driver)
                .and_then(|mut file| file.write_all(&[byte]))
                .expect("each copy is made a build of its own");
        }
        for (name, directory) in [("first", &builds.first), ("second", &builds.second)] {
            builds.toolchain(&[
                std::ffi::OsStr::new("toolchain"),
                std::ffi::OsStr::new("link"),
                std::ffi::OsStr::new(name),
                directory.as_os_str(),
            ]);
        }
        builds
    }

    /// The first build's driver run with `arguments` in the workspace.
    ///
    /// # Specification
    /// trivial.
    fn command(
        &self,
        arguments: &[&std::ffi::OsStr],
    ) -> Command
    {
        let mut command = Command::new(self.first.join("gandr"));
        for (key, value) in gandr::<&str>(&[]).get_envs() {
            let _set = match value {
                Some(value) => command.env(key, value),
                None => command.env_remove(key),
            };
        }
        let _configured = command
            .args(arguments)
            .current_dir(&self.workspace)
            .env("XDG_DATA_HOME", &self.data)
            .env("XDG_RUNTIME_DIR", &self.runtime);
        command
    }

    /// `command` started. A test thread forking while a copy was open for
    /// writing holds it until that child execs, and the kernel refuses to run
    /// it meanwhile, so a busy executable is retried.
    ///
    /// # Specification
    /// trivial.
    fn started(command: &mut Command) -> std::process::Child
    {
        loop {
            match command.spawn() {
                Err(error) if error.kind() == std::io::ErrorKind::ExecutableFileBusy => {
                    std::thread::sleep(core::time::Duration::from_millis(20));
                },
                started => break started.expect("the driver starts"),
            }
        }
    }

    /// Run `arguments` to completion, asserting it exits `0`.
    ///
    /// # Specification
    /// trivial.
    fn toolchain(
        &self,
        arguments: &[&std::ffi::OsStr],
    )
    {
        let output = Self::started(
            self.command(arguments)
                .stdin(Stdio::null())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped()),
        )
        .wait_with_output()
        .expect("the driver runs");
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
    }

    /// The face `face` started with piped standard streams, its hub lingering
    /// 3 s.
    ///
    /// # Specification
    /// trivial.
    fn face(
        &self,
        face: &std::ffi::OsStr,
    ) -> std::process::Child
    {
        let os = std::ffi::OsStr::new;
        Self::started(
            self.command(&[face, os("--linger-ms"), os("3000")])
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped()),
        )
    }

    /// Make `second` the default.
    ///
    /// # Specification
    /// trivial.
    fn switch(&self)
    {
        let os = std::ffi::OsStr::new;
        self.toolchain(&[os("toolchain"), os("default"), os("second")]);
    }

    /// Assert that each build served the session from a hub of its own, and
    /// that the next build removed the handover it read.
    ///
    /// # Specification
    /// trivial.
    fn served_by_both(&self)
    {
        let hubs = std::fs::read_dir(self.runtime.join("gandr"))
            .expect("the runtime directory holds the hubs")
            .filter_map(Result::ok)
            .map(|entry| entry.file_name().to_string_lossy().into_owned())
            .collect::<Vec<String>>();
        assert_eq!(
            hubs.iter()
                .filter(|name| Path::new(name)
                    .extension()
                    .is_some_and(|extension| extension == "sock"))
                .count(),
            2_usize,
            "each build serves the session from a hub of its own: {hubs:?}"
        );
        assert!(
            hubs.iter().all(|name| !name.starts_with("handover-")),
            "the next build removes the handover it read: {hubs:?}"
        );
    }
}

/// The path of the image the process `child` runs.
///
/// # Specification
/// trivial.
#[cfg(target_os = "linux")]
fn image(child: &std::process::Child) -> PathBuf
{
    std::fs::read_link(format!("/proc/{}/exe", child.id())).expect("the image is read")
}

/// One language-server session follows a switch of the default toolchain:
/// the change after the switch reaches the next build's hub, which publishes
/// its diagnostics, and the session ends cleanly in the next build.
///
/// Linux alone, as [`a_relay_reaches_only_a_hub_of_its_own_build`]; the
/// running image is read from `/proc`.
#[cfg(target_os = "linux")]
#[test]
fn a_language_server_follows_a_toolchain_switch()
{
    use std::io::BufReader;

    // The name is short: a socket path must fit the platform's limit.
    let scratch = Scratch::new(Path::new("switch"));
    let builds = Builds::linked(&scratch);
    let mut editor = builds.face(std::ffi::OsStr::new("lsp"));
    let mut to_editor = editor.stdin.take().expect("standard input is piped");
    let mut from_editor = BufReader::new(editor.stdout.take().expect("standard output is piped"));
    let mut answers: Vec<serde_json::Value> = Vec::new();
    let mut published_at = |version: i32, answers: &mut Vec<serde_json::Value>| loop {
        let Maybe::Present(body) = read_frame(&mut from_editor).expect("a frame")
        else {
            panic!("the editor's server ended before publishing version {version}");
        };
        let message: serde_json::Value =
            serde_json::from_slice(body.as_ref()).expect("a frame is JSON");
        if message.get("method").is_none() {
            answers.push(message);
        }
        else if message.pointer("/params/version") == Some(&serde_json::json!(version)) {
            break message;
        }
    };
    to_editor
        .write_all(
            frames(&[
                Text::from(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#),
                Text::from(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#),
                Text::from(
                    r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///tmp/switch.gandr","languageId":"gandr","version":1,"text":"def g = missing ;\n"}}}"#,
                ),
            ])
            .as_ref(),
        )
        .expect("the editor's session is written");
    let before = published_at(1_i32, &mut answers);
    assert!(
        before.to_string().contains("UnresolvedName"),
        "the first build judges the opened text: {before}"
    );
    assert_eq!(
        image(&editor),
        builds.first.join("gandr"),
        "the session starts in the first build"
    );
    builds.switch();
    to_editor
        .write_all(
            frames(&[Text::from(
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///tmp/switch.gandr","version":2},"contentChanges":[{"text":"def h = absent ;\n"}]}}"#,
            )])
            .as_ref(),
        )
        .expect("the change is written");
    let after = published_at(2_i32, &mut answers);
    assert!(
        after.to_string().contains("absent"),
        "the next build judges the changed text: {after}"
    );
    assert_eq!(
        image(&editor),
        builds.second.join("gandr"),
        "the change found the switch, and the session runs in the second build"
    );
    builds.served_by_both();
    to_editor
        .write_all(
            frames(&[
                Text::from(r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#),
                Text::from(r#"{"jsonrpc":"2.0","method":"exit"}"#),
            ])
            .as_ref(),
        )
        .expect("the editor's session is ended");
    drop(to_editor);
    while let Maybe::Present(body) = read_frame(&mut from_editor).expect("a frame") {
        let message: serde_json::Value =
            serde_json::from_slice(body.as_ref()).expect("a frame is JSON");
        if message.get("method").is_none() {
            answers.push(message);
        }
    }
    let ids: Vec<Option<&serde_json::Value>> =
        answers.iter().map(|answer| answer.get("id")).collect();
    assert_eq!(
        ids,
        [
            Some(&serde_json::json!(1_i32)),
            Some(&serde_json::json!(2_i32))
        ],
        "the client sees one answer to each of its requests, and none to the replay"
    );
    let ended = editor.wait_with_output().expect("the editor's server runs");
    assert_eq!(code(&ended), Code(0_i32), "{}", stderr(&ended));
}

/// One model session follows a switch of the default toolchain: the request
/// after the switch reaches the next build's hub, opened by the client's
/// replayed `initialize`, whose answer the client never sees.
///
/// Linux alone, as [`a_language_server_follows_a_toolchain_switch`].
#[cfg(target_os = "linux")]
#[test]
fn a_model_session_follows_a_toolchain_switch()
{
    use std::io::BufRead as _;
    use std::io::BufReader;

    // The name is short: a socket path must fit the platform's limit.
    let scratch = Scratch::new(Path::new("mswitch"));
    let builds = Builds::linked(&scratch);
    let mut model = builds.face(std::ffi::OsStr::new("mcp"));
    let mut to_model = model.stdin.take().expect("standard input is piped");
    let mut from_model = BufReader::new(model.stdout.take().expect("standard output is piped"));
    let mut answered = || {
        let mut line = String::new();
        let _read = from_model.read_line(&mut line).expect("a line");
        serde_json::from_str::<serde_json::Value>(&line).expect("a line is JSON")
    };
    to_model
        .write_all(concat!(
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{}}}"#,
            "\n",
            r#"{"jsonrpc":"2.0","method":"notifications/initialized"}"#,
            "\n",
        ).as_bytes())
        .expect("the opening is written");
    let opened = answered();
    assert_eq!(
        opened.get("id"),
        Some(&serde_json::json!(1_i32)),
        "{opened}"
    );
    assert_eq!(
        image(&model),
        builds.first.join("gandr"),
        "the session starts in the first build"
    );
    builds.switch();
    to_model
        .write_all(concat!(
            r#"{"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"documents","arguments":{}}}"#,
            "\n",
        ).as_bytes())
        .expect("the call is written");
    let called = answered();
    assert_eq!(
        (
            called.get("id"),
            called.pointer("/result/structuredContent/documents")
        ),
        (
            Some(&serde_json::json!(2_i32)),
            Some(&serde_json::json!([]))
        ),
        "the next build answers the call, and the replay's answer is dropped: {called}"
    );
    assert_eq!(
        image(&model),
        builds.second.join("gandr"),
        "the call found the switch, and the session runs in the second build"
    );
    builds.served_by_both();
    drop(to_model);
    let mut rest = String::new();
    std::io::Read::read_to_string(&mut from_model, &mut rest).expect("the model's output ends");
    assert_eq!(rest, "", "nothing follows the last answer");
    let ended = model.wait_with_output().expect("the model's server runs");
    assert_eq!(code(&ended), Code(0_i32), "{}", stderr(&ended));
}

#[test]
fn mcp_reads_what_an_editor_holds_open()
{
    use std::ffi::OsStr;
    use std::io::BufReader;

    // The name is short: a socket path must fit the platform's limit.
    let scratch = Scratch::new(Path::new("mcp"));
    let socket = scratch.0.join("hub.sock");
    let mut editor = gandr(&[
        OsStr::new("lsp"),
        OsStr::new("--socket"),
        socket.as_os_str(),
        OsStr::new("--linger-ms"),
        OsStr::new("200"),
    ])
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .expect("the editor's server starts");
    let mut to_editor = editor.stdin.take().expect("standard input is piped");
    let mut from_editor = BufReader::new(editor.stdout.take().expect("standard output is piped"));
    to_editor
            .write_all(
                frames(&[
                    Text::from(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#),
                    Text::from(
                        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///tmp/held.gandr","languageId":"gandr","version":1,"text":"def g = missing ;\n"}}}"#,
                    ),
                ])
                .as_ref(),
            )
            .expect("the editor's session is written");
    let mut published = String::new();
    for _frame in 0_u8 .. 2_u8 {
        let Maybe::Present(body) = read_frame(&mut from_editor).expect("a frame")
        else {
            panic!("the editor's server ended early");
        };
        published = String::from_utf8(body.as_ref().to_vec()).expect("UTF-8");
    }
    assert!(
        published.contains("UnresolvedName"),
        "the editor sees the refusal first: {published}"
    );
    let model = piped(
        &[
            OsStr::new("mcp"),
            OsStr::new("--socket"),
            socket.as_os_str(),
        ],
        Text::from(concat!(
            r#"{"jsonrpc":"2.0","id":1,"method":"server/discover"}"#,
            "\n",
            r#"{"jsonrpc":"2.0","id":2,"method":"resources/list"}"#,
            "\n",
            r#"{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"diagnostics","arguments":{"uri":"file:///tmp/held.gandr"}}}"#,
            "\n",
        )),
    );
    assert_eq!(code(&model), Code(0_i32), "{}", stderr(&model));
    let transcript = stdout(&model);
    let replies: Vec<&str> = transcript.lines().collect();
    assert_eq!(replies.len(), 3_usize, "one line per request: {transcript}");
    assert!(
        replies[1].contains(r#""uri":"gandr:///tmp/held.gandr/diagnostics""#),
        "the held document is a resource: {transcript}"
    );
    assert!(
        replies[2].contains(r#""code":"UnresolvedName""#) && replies[2].contains(r#""version":1"#),
        "the model reads the editor's refusal at its version: {transcript}"
    );
    to_editor
        .write_all(
            frames(&[
                Text::from(r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#),
                Text::from(r#"{"jsonrpc":"2.0","method":"exit"}"#),
            ])
            .as_ref(),
        )
        .expect("the editor's session is ended");
    drop(to_editor);
    // The shutdown reply is read, so the editor's last write finds a
    // reader.
    let mut rest = Vec::new();
    std::io::Read::read_to_end(&mut from_editor, &mut rest).expect("the editor's output ends");
    assert!(
        String::from_utf8_lossy(&rest).contains(r#""id":2"#),
        "shutdown is answered"
    );
    let ended = editor.wait_with_output().expect("the editor's server runs");
    assert_eq!(code(&ended), Code(0_i32), "{}", stderr(&ended));
    let deadline = std::time::Instant::now() + core::time::Duration::from_secs(20);
    while socket.exists() && std::time::Instant::now() < deadline {
        std::thread::sleep(core::time::Duration::from_millis(50));
    }
    assert!(
        !socket.exists(),
        "the hub exits after its linger, removing its socket"
    );
}

/// A pseudo-terminal pair, or none where this host can allocate none: the test
/// is then skipped, the reason written to standard error.
///
/// # Specification
/// trivial.
#[cfg(unix)]
fn pseudo_terminal() -> Option<nix::pty::OpenptyResult>
{
    match nix::pty::openpty(None, None) {
        Ok(pair) => Some(pair),
        Err(error) => {
            writeln!(
                std::io::stderr(),
                "skipped: no pseudo-terminal can be allocated here: {error}"
            )
            .expect("standard error is writable");
            None
        },
    }
}

/// A piped view prints the report of what an editor holds open, then the next
/// one after the editor's edit.
#[test]
fn a_view_follows_what_an_editor_holds_open()
{
    view_follows_an_editor(Stdio::null(), Path::new("view"));
}

/// A view whose standard input alone is a terminal still prints plain
/// reports: the terminal follower takes both standard streams being
/// terminals, as the terminal face does.
#[cfg(unix)]
#[test]
fn a_terminal_on_standard_input_alone_leaves_the_view_plain()
{
    let Some(terminal) = pseudo_terminal()
    else {
        return;
    };
    view_follows_an_editor(Stdio::from(terminal.slave), Path::new("viewtty"));
    drop(terminal.master);
}

/// An editor holds a refused document open through a hub, and a view started
/// with `input` on standard input and its output piped prints the plain report
/// of it, then the next one after the editor's edit; the hub lingers out once
/// both have left. The scratch directory is named `name`.
///
/// # Specification
/// trivial.
fn view_follows_an_editor(
    input: Stdio,
    name: &Path,
)
{
    use std::ffi::OsStr;
    use std::io::BufRead as _;
    use std::io::BufReader;

    // The name is short: a socket path must fit the platform's limit.
    let scratch = Scratch::new(name);
    let socket = scratch.0.join("hub.sock");
    let mut editor = gandr(&[
        OsStr::new("lsp"),
        OsStr::new("--socket"),
        socket.as_os_str(),
        OsStr::new("--linger-ms"),
        OsStr::new("200"),
    ])
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .expect("the editor's server starts");
    let mut to_editor = editor.stdin.take().expect("standard input is piped");
    let mut from_editor = BufReader::new(editor.stdout.take().expect("standard output is piped"));
    let mut next_from_editor = || {
        let Maybe::Present(body) = read_frame(&mut from_editor).expect("a frame")
        else {
            panic!("the editor's server ended early");
        };
        String::from_utf8(body.as_ref().to_vec()).expect("UTF-8")
    };
    to_editor
            .write_all(
                frames(&[
                    Text::from(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#),
                    Text::from(
                        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///tmp/viewed.gandr","languageId":"gandr","version":1,"text":"def g = missing ;\n"}}}"#,
                    ),
                ])
                .as_ref(),
            )
            .expect("the editor's session is written");
    drop(next_from_editor());
    assert!(
        next_from_editor().contains("UnresolvedName"),
        "the editor sees the refusal first"
    );
    let mut view = gandr(&[
        OsStr::new("view"),
        OsStr::new("--socket"),
        socket.as_os_str(),
    ])
    .stdin(input)
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .expect("the view starts");
    let mut from_view = BufReader::new(view.stdout.take().expect("standard output is piped"));
    let opening = from_view.fill_buf().expect("the view prints");
    assert!(
        !opening.contains(&0x1b_u8),
        "the view prints plain reports, not terminal commands: {opening:?}"
    );
    let mut row = String::new();
    let mut report = || {
        let mut rows = Vec::new();
        loop {
            row.clear();
            assert_ne!(
                from_view.read_line(&mut row).expect("the view prints"),
                0_usize,
                "the view ended early"
            );
            if row == "\n" {
                return rows;
            }
            rows.push(row.trim_end().to_owned());
        }
    };
    let first = report();
    assert_eq!(
        first.first().map(String::as_str),
        Some("file:///tmp/viewed.gandr at version 1: 1 diagnostic, 0 holes"),
        "the view shows what the editor holds: {first:#?}"
    );
    assert!(
        first
            .get(1_usize)
            .is_some_and(|row| row.starts_with("1:9 [UnresolvedName]")),
        "the refusal is placed at its row and column: {first:#?}"
    );
    to_editor
            .write_all(
                frames(&[Text::from(
                    r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///tmp/viewed.gandr","version":2},"contentChanges":[{"text":"def g = 1 ;\n"}]}}"#,
                )])
                .as_ref(),
            )
            .expect("the editor's edit is written");
    drop(next_from_editor());
    assert_eq!(
        report(),
        ["file:///tmp/viewed.gandr at version 2: 0 diagnostics, 0 holes"],
        "the editor's edit reaches the view within one check"
    );
    view.kill().expect("the view stops");
    assert!(
        !view.wait().expect("the view is reaped").success(),
        "the view runs until it is stopped"
    );
    to_editor
        .write_all(
            frames(&[
                Text::from(r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#),
                Text::from(r#"{"jsonrpc":"2.0","method":"exit"}"#),
            ])
            .as_ref(),
        )
        .expect("the editor's session is ended");
    drop(to_editor);
    // The shutdown reply is read, so the editor's last write finds a
    // reader.
    let mut rest = Vec::new();
    std::io::Read::read_to_end(&mut from_editor, &mut rest).expect("the editor's output ends");
    let ended = editor.wait_with_output().expect("the editor's server runs");
    assert_eq!(code(&ended), Code(0_i32), "{}", stderr(&ended));
    let deadline = std::time::Instant::now()
        .checked_add(core::time::Duration::from_secs(20))
        .expect("the deadline is representable");
    while socket.exists() && std::time::Instant::now() < deadline {
        std::thread::sleep(core::time::Duration::from_millis(50));
    }
    assert!(
        !socket.exists(),
        "the hub exits after its linger, removing its socket"
    );
}

#[test]
fn a_view_whose_output_closes_notes_why_and_exits_two()
{
    use std::ffi::OsStr;
    use std::io::BufReader;

    // The name is short: a socket path must fit the platform's limit.
    let scratch = Scratch::new(Path::new("view-closed"));
    let socket = scratch.0.join("hub.sock");
    let mut editor = gandr(&[
        OsStr::new("lsp"),
        OsStr::new("--socket"),
        socket.as_os_str(),
        OsStr::new("--linger-ms"),
        OsStr::new("200"),
    ])
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .expect("the editor's server starts");
    let mut to_editor = editor.stdin.take().expect("standard input is piped");
    let mut from_editor = BufReader::new(editor.stdout.take().expect("standard output is piped"));
    let mut next_from_editor = || {
        let Maybe::Present(body) = read_frame(&mut from_editor).expect("a frame")
        else {
            panic!("the editor's server ended early");
        };
        drop(body);
    };
    to_editor
            .write_all(
                frames(&[
                    Text::from(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#),
                    Text::from(
                        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///tmp/closed.gandr","languageId":"gandr","version":1,"text":"def g = missing ;\n"}}}"#,
                    ),
                ])
                .as_ref(),
            )
            .expect("the editor's session is written");
    next_from_editor();
    next_from_editor();
    let mut view = gandr(&[
        OsStr::new("view"),
        OsStr::new("--socket"),
        socket.as_os_str(),
    ])
    .stdin(Stdio::null())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .expect("the view starts");
    // With its reader gone, the view's next report has nowhere to go; the
    // edit makes one even if the first reached the pipe before it closed.
    drop(view.stdout.take());
    to_editor
            .write_all(
                frames(&[Text::from(
                    r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///tmp/closed.gandr","version":2},"contentChanges":[{"text":"def g = 1 ;\n"}]}}"#,
                )])
                .as_ref(),
            )
            .expect("the editor's edit is written");
    next_from_editor();
    let stopped = view.wait_with_output().expect("the view is reaped");
    assert_eq!(code(&stopped), Code(2_i32), "{}", stderr(&stopped));
    assert!(
        stderr(&stopped).starts_with("gandr: the view: "),
        "the view says why it stopped: {}",
        stderr(&stopped)
    );
    to_editor
        .write_all(
            frames(&[
                Text::from(r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#),
                Text::from(r#"{"jsonrpc":"2.0","method":"exit"}"#),
            ])
            .as_ref(),
        )
        .expect("the editor's session is ended");
    drop(to_editor);
    // The shutdown reply is read, so the editor's last write finds a
    // reader.
    let mut rest = Vec::new();
    std::io::Read::read_to_end(&mut from_editor, &mut rest).expect("the editor's output ends");
    let ended = editor.wait_with_output().expect("the editor's server runs");
    assert_eq!(code(&ended), Code(0_i32), "{}", stderr(&ended));
    let deadline = std::time::Instant::now() + core::time::Duration::from_secs(20);
    while socket.exists() && std::time::Instant::now() < deadline {
        std::thread::sleep(core::time::Duration::from_millis(50));
    }
    assert!(
        !socket.exists(),
        "the hub exits after its linger once the view has gone"
    );
}

#[test]
fn a_view_reaching_no_hub_notes_why_and_exits_two()
{
    use std::ffi::OsStr;

    let scratch = Scratch::new(Path::new("view-unreached"));
    // Longer than any platform's socket path limit: no client connects to it
    // and the hub the view starts cannot bind it.
    let socket = scratch.0.join("h".repeat(200_usize));
    let unreached = ran(gandr(&[
        OsStr::new("view"),
        OsStr::new("--socket"),
        socket.as_os_str(),
    ]));
    assert_eq!(code(&unreached), Code(2_i32), "{}", stderr(&unreached));
    assert!(
        stderr(&unreached).starts_with("gandr: the engine hub: "),
        "the view says the hub was never reached: {}",
        stderr(&unreached)
    );
    assert!(unreached.stdout.is_empty(), "nothing is followed");
    assert!(!socket.exists(), "no hub is left behind");
}

/// The finished run of `gandr` with `arguments` and `input` on standard
/// input, its output captured.
///
/// # Specification
/// - requires: stable driver arguments and finite input whose pipe write
///   completes before the child exits, without external termination.
/// - ensures: sends the offered bytes, closes input, waits, and captures the
///   process status and both streams.
/// - provides: a plain-stream client for interactive verbs.
/// - fails: never.
/// - panics: on process or pipe failure.
///
/// # Adequacy
/// - hypothesis: L3 — a finite load/query/refusal/quit transcript is compared
///   in automatic and explicit batch modes. Dropped input, wrong stream
///   selection or reading beyond quit changes exact rows. Large backpressured
///   sessions and external signals are outside the domain.
/// - witness: `tests::cli::a_piped_repl_session_prints_its_transcript`
#[spec(ensures: |ref ret| matches!(ret.status.code(), Some(0 ..= 2)))]
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
    assert!(stderr(&smoke).is_empty());
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

/// The terminal face takes both standard streams being terminals: with a
/// terminal on standard input alone it is refused as with two pipes, at once,
/// and paints nothing.
#[cfg(unix)]
#[test]
fn a_terminal_on_standard_input_alone_is_refused_the_terminal_face()
{
    let Some(terminal) = pseudo_terminal()
    else {
        return;
    };
    let mut command = gandr(&["tui"]);
    let mut face = command
        .stdin(Stdio::from(terminal.slave))
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the driver starts");
    // A face that took the terminal puts it in raw mode before it waits on
    // its keys, and the pair shares one mode, read here on the master. The
    // wait ends on that or on the driver's exit, never on a clock: a loaded
    // host only slows the refusal, which a deadline of seconds once read as
    // the face holding the terminal (#1590).
    let took = loop {
        if face.try_wait().expect("the driver is polled").is_some() {
            break false;
        }
        let mode =
            nix::sys::termios::tcgetattr(&terminal.master).expect("the terminal's mode is read");
        if !mode
            .local_flags
            .contains(nix::sys::termios::LocalFlags::ICANON)
        {
            face.kill().expect("the face stops");
            break true;
        }
        std::thread::sleep(core::time::Duration::from_millis(20));
    };
    let refused = face.wait_with_output().expect("the driver is reaped");
    drop(terminal.master);
    assert!(!took, "the face took a terminal it was not given whole");
    assert_eq!(code(&refused), Code(2));
    assert!(
        refused.stdout.is_empty(),
        "a refused terminal face paints nothing"
    );
    assert_eq!(
        stderr(&refused),
        stderr(&ran(gandr(&["tui"]))),
        "refused as two pipes are"
    );
}

/// A client whose hub never comes up keeps trying for five seconds before it
/// gives up: the hub it starts cannot bind under a socket directory that is a
/// file, and the client exits `2`, the hub named.
#[cfg(unix)]
#[test]
fn a_client_tries_five_seconds_for_a_hub_that_never_answers()
{
    use std::ffi::OsStr;

    let scratch = Scratch::new(Path::new("unreached"));
    let blocker = scratch.file(Path::new("blocker"), Text::from(""));
    let socket = blocker.join("hub.sock");
    let started = std::time::Instant::now();
    let unreached = ran(gandr(&[
        OsStr::new("view"),
        OsStr::new("--socket"),
        socket.as_os_str(),
    ]));
    let waited = started.elapsed();
    assert_eq!(code(&unreached), Code(2), "{}", stderr(&unreached));
    assert!(
        waited >= core::time::Duration::from_secs(5),
        "the client gave up after {waited:?}"
    );
    assert!(stderr(&unreached).starts_with("gandr:"));
}

/// A script of `text`, written to `name` in `scratch`, run by the driver.
///
/// # Specification
/// - requires: a valid scratch-relative source name, writable storage and a
///   driver that starts and finishes without external termination.
/// - ensures: writes and runs that source, returning its path and captured run.
/// - provides: source/status pairs for script semantics.
/// - fails: never.
/// - panics: on filesystem or process failure.
///
/// # Adequacy
/// - hypothesis: L3 — scripts running their `main`, reaching blame, carrying a
///   checker refusal or declaring no `main` expose status and stream
///   separation. Wrong paths, arguments or captured outputs change these
///   observations; arbitrary scripts and external mutation are excluded.
/// - witness: `tests::cli::a_script_that_runs_its_main_leaves_successfully`
/// - witness: `tests::cli::a_script_that_blames_leaves_with_a_failure_status`
/// - witness: `tests::cli::a_script_with_no_program_is_refused`
#[spec(ensures: |ref ret| ret.0.strip_prefix(&scratch.0).is_ok_and(|relative| relative == name)
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

/// A run of a `main` writes the lines it prints, and nothing else, on standard
/// output and exits zero.
#[test]
fn a_script_that_runs_its_main_leaves_successfully()
{
    let scratch = Scratch::new(Path::new("script-main"));
    let (_path, output) = run_script(
        &scratch,
        Path::new("main.gandr"),
        Text::from(
            "def answer = 42 ;\ndef main() -> [Console] Unit {\n  Console.print(\"42\")\n}\n",
        ),
    );
    assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
    assert_eq!(
        stdout(&output),
        "42\n",
        "the run routes what it prints to the caller, once"
    );
    assert_eq!(stderr(&output), "", "a completed run writes no complaint");
}

/// #1881: a program leaves with the status its `main` returns or exits with,
/// its arguments the operands after the path, and writes no value; a `main`
/// reaching a goal is blamed as any run is.
#[test]
fn a_program_leaves_with_its_entry_s_status_1881()
{
    let scratch = Scratch::new(Path::new("program-entry"));
    let counted = "def rec count(xs : List(String)) -> -F Integer {\n  match xs {\n    [] => 0,\n    \
                   [x, ..rest] => { let n = count[<](rest); n + 1 }\n  }\n}\ndef main(args : \
                   List(String)) -> -F Integer { become count(args) }\n";
    for (name, text, arguments, status) in [
        (
            "returned.gandr",
            "def main() -> -F Integer { return 3 }\ndef later = 1 ;\n",
            &[][..],
            3_i32,
        ),
        (
            "exited.gandr",
            "def proc : Cap {exit} ;\ndef main() -> -F [Proc] Integer { proc.exit(7) ; return 0 }\n",
            &[][..],
            7_i32,
        ),
        (
            "counted.gandr",
            counted,
            &["a", "-b", "--c", "two.gandr"][..],
            4_i32,
        ),
        (
            "wrapped.gandr",
            "def main() -> -F Integer { return 257 }\n",
            &[][..],
            1_i32,
        ),
    ] {
        let path = scratch.file(Path::new(name), Text::from(text));
        let mut command = gandr(&[Path::new("run"), path.as_path()]);
        command.args(arguments);
        let output = ran(command);
        assert_eq!(code(&output), Code(status), "{name}: {}", stderr(&output));
        assert_eq!(stdout(&output), "", "{name}: a program writes no value");
    }
}

/// #2279: `gandr run` of the hello-world exemplar prints its greeting as the
/// whole of standard output and leaves with 0; a program whose row names an
/// effect no host provides, the exemplar's twin without its expectation, is
/// refused by that name and runs nothing.
#[test]
fn a_program_prints_hello_world_2279()
{
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let hello = corpus.join("model/effects/hello.gandr");
    let output = ran(gandr(&[Path::new("run"), hello.as_path()]));
    assert_eq!(
        (code(&output), stdout(&output).as_str()),
        (Code(0), "hello, world!\n"),
        "{}",
        stderr(&output)
    );
    let scratch = Scratch::new(Path::new("program-unprovided"));
    let unprovided = scratch.file(
        Path::new("unprovided.gandr"),
        Text::from("def main() -> -F [Clock] Unit {\n  Clock.print(\"hello, world!\")\n}\n"),
    );
    let output = ran(gandr(&[Path::new("run"), unprovided.as_path()]));
    assert_eq!(
        (code(&output), stdout(&output).as_str()),
        (Code(2), ""),
        "nothing runs"
    );
    assert!(
        stderr(&output).contains("Clock"),
        "the refusal names the effect: {}",
        stderr(&output)
    );
}

/// #2970: `gandr run` hands a program its standard input and its standard
/// error beside standard output. The answering exemplar reads one line and
/// answers `yes` on standard output and anything else, the end of input too,
/// on standard error.
#[test]
fn a_program_reads_and_answers_on_the_standard_streams_2970()
{
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let answer = corpus.join("model/console/answer.gandr");
    for (input, out, err) in [
        ("yes\n", "agreed\n", ""),
        ("no\n", "", "declined\n"),
        ("", "", "declined\n"),
    ] {
        let output = piped(&[Path::new("run"), answer.as_path()], Text::from(input));
        assert_eq!(
            (
                code(&output),
                stdout(&output).as_str(),
                stderr(&output).as_str()
            ),
            (Code(0), out, err),
            "{input:?}"
        );
    }
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
            "def later : +U (-F Integer) ;\ndef main : +U (-F Integer) ;\ndef main = thunk { become force later } ;\n",
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
        Text::from("def five : Integer ;\ndef five = \"five\" ;\n"),
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
    let prefix = format!("gandr: {}: ", path.display());
    assert!(
        complaint.lines().any(|line| line.starts_with(&prefix)),
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
        Text::from("def wrong : Integer ;\ndef wrong = \"one\" ;\ndef zero = 0 ;\n"),
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

/// A script declaring no `main` runs nothing — not its last declaration — and
/// exits two, naming `def main` and pointing at `check` and `test` (#2572).
#[test]
fn a_script_with_no_program_is_refused()
{
    let scratch = Scratch::new(Path::new("script-no-program"));
    for (name, text) in [
        ("nothing.gandr", "// declares nothing\n"),
        (
            "declarations.gandr",
            "def answer : +U (-F Integer) ;\ndef answer = thunk { return 42 } ;\n",
        ),
    ] {
        let (path, output) = run_script(&scratch, Path::new(name), Text::from(text));
        assert_eq!(
            code(&output),
            Code(2_i32),
            "{name}: a source with no `main` never reaches the machine"
        );
        assert!(output.stdout.is_empty(), "{name}: nothing ran");
        let complaint = stderr(&output);
        assert!(
            complaint.starts_with(&format!("gandr: {}: ", path.display()))
                && complaint.contains("`def main() -> Unit { … }`")
                && complaint.contains("`gandr check`")
                && complaint.contains("`gandr test`"),
            "{name}: the refusal names `main` and the verbs for declarations: {complaint}"
        );
    }
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
        Text::from("def main() -> [Console] Unit { Console.print(\"17\") }"),
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
        Text::from("def unused : Integer ; def main() -> [Console] Unit { Console.print(\"9\") }"),
    );
    let control = ran(gandr(&[Path::new("run"), &source]));
    assert_eq!(code(&control), Code(0));
    assert_eq!(stdout(&control), "9\n");
    let missing = scratch.0.join("missing.gandr");
    // A run prints as it runs, before its diagnostics are written, so what it
    // printed stands; nothing is written after the stream fails.
    for (arguments, printed) in [
        ([Path::new("check"), missing.as_path()], ""),
        ([Path::new("run"), source.as_path()], "9\n"),
    ] {
        let (reader, writer) = std::io::pipe().expect("a pipe is made");
        drop(reader);
        let mut command = gandr(&arguments);
        command.stderr(writer);
        let output = ran(command);
        assert_eq!(code(&output), Code(2), "{arguments:?}");
        assert_eq!(stdout(&output), printed, "no later summary: {arguments:?}");
    }
}

/// #782: `presentation.spelling` in the user's configuration file spells
/// what `check` and `run` report, `--spelling` outranks it, and a file naming
/// no spelling stops the driver before any verb runs.
#[test]
fn the_configured_spelling_prints_and_the_flag_outranks_it_782()
{
    let scratch = Scratch::new(Path::new("configured-spelling"));
    let refused = scratch.file(
        Path::new("relation.gandr"),
        Text::from("def r : Integer ≃ String ;\ndef r = 1 ;\n"),
    );
    let home = scratch.0.join("configuration");
    let configured = |text: &str| {
        let _file = scratch.file(
            Path::new("configuration/gandr/config.toml"),
            Text::from(text),
        );
    };
    let under_home = |arguments: &[&std::ffi::OsStr]| {
        let mut command = gandr(arguments);
        command.env("XDG_CONFIG_HOME", &home);
        ran(command)
    };
    let check = |flag: &[&str]| {
        let mut arguments: Vec<&std::ffi::OsStr> = flag.iter().map(std::ffi::OsStr::new).collect();
        arguments.extend([std::ffi::OsStr::new("check"), refused.as_os_str()]);
        stdout(&under_home(&arguments))
    };
    let run = |flag: &[&str]| {
        let mut arguments: Vec<&std::ffi::OsStr> = flag.iter().map(std::ffi::OsStr::new).collect();
        arguments.extend([std::ffi::OsStr::new("run"), refused.as_os_str()]);
        stderr(&under_home(&arguments))
    };
    assert!(
        check(&[]).contains("expected `Integer ≃ String`"),
        "no file prints Unicode"
    );
    assert!(
        check(&["--spelling", "ascii"]).contains("expected `Integer <~> String`"),
        "the flag alone chooses"
    );
    configured("[presentation]\nspelling = \"ascii\"\n");
    assert!(
        check(&[]).contains("expected `Integer <~> String`"),
        "the file's spelling prints"
    );
    assert!(
        run(&[]).contains("expected `Integer <~> String`"),
        "and spells what a run reports"
    );
    assert!(
        check(&["--spelling", "unicode"]).contains("expected `Integer ≃ String`"),
        "the flag outranks the file"
    );
    assert!(
        run(&["--spelling", "unicode"]).contains("expected `Integer ≃ String`"),
        "for a run too"
    );
    configured("[presentation]\nspelling = \"latin\"\n");
    let stopped = under_home(&[std::ffi::OsStr::new("check"), refused.as_os_str()]);
    assert_eq!(code(&stopped), Code(2), "a spelling there is none of");
    assert!(stopped.stdout.is_empty(), "stops before the verb runs");
    assert!(
        stderr(&stopped).contains("`presentation.spelling` is `latin`"),
        "and says why: {}",
        stderr(&stopped)
    );
}

#[test]
fn an_unreadable_or_malformed_configuration_stops_the_run()
{
    let scratch = Scratch::new(Path::new("configuration-faults"));
    let file = Path::new("gandr/config.toml");
    let malformed = scratch.0.join("malformed");
    let _written = scratch.file(
        &Path::new("malformed").join(file),
        Text::from("[presentation\n"),
    );
    let unreadable = scratch.0.join("unreadable");
    std::fs::create_dir_all(unreadable.join(file))
        .expect("a directory stands where the file is read");
    let status_under = |home: &Path| {
        let mut command = gandr::<&str>(&[]);
        command.env("XDG_CONFIG_HOME", home);
        ran(command)
    };
    let mut noted = Vec::new();
    for home in [&malformed, &unreadable] {
        let stopped = status_under(home);
        assert_eq!(code(&stopped), Code(2_i32), "{}", stderr(&stopped));
        assert!(stopped.stdout.is_empty(), "stops before the verb runs");
        let why = stderr(&stopped);
        assert!(
            why.contains(&home.join(file).display().to_string()),
            "names the file: {why}"
        );
        noted.push(why);
    }
    assert_ne!(
        noted[0], noted[1],
        "a malformed file and an unreadable one read apart"
    );
    let mut homeless = gandr::<&str>(&[]);
    let _unset = homeless.env_remove("XDG_CONFIG_HOME").env_remove("HOME");
    let unconfigured = ran(homeless);
    assert_eq!(
        code(&unconfigured),
        Code(0_i32),
        "{}",
        stderr(&unconfigured)
    );
    assert_eq!(
        stdout(&unconfigured),
        stdout(&ran(gandr::<&str>(&[]))),
        "no home at all reads as no configuration"
    );
}

/// `gandr check` of a manifold judges its deployment before any process
/// starts: a site answering each entry its world requires settles with nothing
/// on standard error, and a site file checked beside it is no manifold; a site
/// leaving `Console` out and binding `store` at other sorts is refused at each,
/// and a placement of a world the program lacks by the world's name (#3523).
#[test]
fn a_manifold_s_deployment_is_judged_at_its_check_3523()
{
    let checked = |paths: &[&str]| {
        let mut arguments = vec!["check"];
        arguments.extend_from_slice(paths);
        let mut command = gandr(&arguments);
        command.current_dir(Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."));
        ran(command)
    };
    let offered = checked(&[
        "corpus/model/deployments/offers.manifold.gandr",
        "corpus/model/deployments/offers.site.gandr",
    ]);
    assert_eq!(
        (code(&offered), stderr(&offered)),
        (Code(0_i32), String::new()),
        "a site answering `Console` and `store` takes `far`, and the site's own file is \
         judged as no deployment"
    );
    let refused = checked(&["corpus/pathological/worlds/offers.gandr"]);
    assert_eq!(
        (code(&refused), stderr(&refused)),
        (
            Code(1_i32),
            String::from(concat!(
                "gandr: `far` requires `Console`, and the site ",
                "`corpus/pathological/worlds/offers.gandr` does not answer it: the site's ",
                "offer does not list it\n",
                "gandr: `far` requires `store`, and the site ",
                "`corpus/pathological/worlds/offers.gandr` does not answer it: TypeMismatch: ",
                "the type of this term does not match the type it is checked against; its ",
                "type does not convert: expected `String`, found `Integer`\n",
                "gandr: `corpus/pathological/worlds/offers.gandr` places `nowhere`, a world ",
                "`corpus/pathological/worlds/../../model/deployments/offers.gandr` does not ",
                "declare: place one of its worlds\n",
            ))
        ),
        "each refusal names what the site lacks or the world the program lacks"
    );
}

/// A toolchain directory under `scratch` named `name`, whose `gandr` prints
/// `ran <name> <its arguments>` and exits 0.
///
/// # Specification
/// trivial.
#[cfg(unix)]
fn fake_toolchain(
    scratch: &Scratch,
    name: &Path,
) -> PathBuf
{
    use std::os::unix::fs::PermissionsExt as _;

    let script = format!("#!/bin/sh\necho \"ran {} $*\"\n", name.display());
    let executable = scratch.file(
        &Path::new("builds").join(name).join("gandr"),
        Text::from(&*script),
    );
    std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o755))
        .expect("the fake build is executable");
    executable
        .parent()
        .expect("the build has a directory")
        .to_path_buf()
}

/// `gandr` with `arguments` in `working`, its data directory `data`, and
/// `GANDR_TOOLCHAIN` set to `selecting` when it names one.
///
/// # Specification
/// trivial.
#[cfg(unix)]
fn proxied<Argument>(
    arguments: &[Argument],
    working: &Path,
    data: &Path,
    selecting: Maybe<&std::ffi::OsStr, ()>,
) -> Output
where
    Argument: AsRef<std::ffi::OsStr>,
{
    let mut command = gandr(arguments);
    let _placed = command.current_dir(working).env("XDG_DATA_HOME", data);
    if let Maybe::Present(name) = selecting {
        let _selected = command.env("GANDR_TOOLCHAIN", name);
    }
    ran(command)
}

/// A linked build runs in the driver's place with the driver's arguments and
/// the selection named, and `toolchain list` shows it.
#[cfg(unix)]
#[test]
fn a_linked_toolchain_is_the_one_the_proxy_runs()
{
    let scratch = Scratch::new(Path::new("toolchain-link"));
    let data = scratch.0.join("data");
    let build = fake_toolchain(&scratch, Path::new("fake"));
    let link = proxied(
        &["toolchain", "link", "fake", &build.to_string_lossy()],
        &scratch.0,
        &data,
        Maybe::Absent(()),
    );
    assert_eq!(code(&link), Code(0_i32), "{}", stderr(&link));
    let run = proxied(
        &["check", "--goals", "here.gandr"],
        &scratch.0,
        &data,
        Maybe::Absent(()),
    );
    assert_eq!(code(&run), Code(0_i32), "{}", stderr(&run));
    assert_eq!(
        stdout(&run),
        "ran fake check --goals here.gandr\n",
        "the first build linked is the default, and it runs with the driver's arguments and the selection named"
    );
    let list = proxied(
        &["toolchain", "list"],
        &scratch.0,
        &data,
        Maybe::Present(std::ffi::OsStr::new("fake")),
    );
    assert_eq!(code(&list), Code(0_i32), "{}", stderr(&list));
    assert_eq!(
        stdout(&list),
        format!(
            "fake {} (default, selected)\n",
            build.canonicalize().expect("the build resolves").display()
        ),
        "`toolchain list` runs whatever is selected and names the link"
    );
    let empty = scratch.0.join("empty");
    std::fs::create_dir_all(&empty).expect("an empty directory is made");
    let unbuilt = proxied(
        &["toolchain", "link", "empty", &empty.to_string_lossy()],
        &scratch.0,
        &data,
        Maybe::Absent(()),
    );
    assert_eq!(code(&unbuilt), Code(2_i32));
    assert!(
        stderr(&unbuilt).starts_with("gandr: the toolchain `empty` holds no "),
        "a directory with no `gandr` is refused: {}",
        stderr(&unbuilt)
    );
}

/// #4511: cargo running the driver's own package runs that build, whatever
/// the default names, so a gate in a worktree judges the worktree's driver;
/// `CARGO_MANIFEST_DIR` naming another directory selects as before.
#[cfg(unix)]
#[test]
fn a_cargo_run_of_the_driver_runs_its_own_build_4511()
{
    let scratch = Scratch::new(Path::new("toolchain-cargo-run"));
    let data = scratch.0.join("data");
    let build = fake_toolchain(&scratch, Path::new("fake"));
    let link = proxied(
        &["toolchain", "link", "fake", &build.to_string_lossy()],
        &scratch.0,
        &data,
        Maybe::Absent(()),
    );
    assert_eq!(code(&link), Code(0_i32), "{}", stderr(&link));
    let under = |manifest: &Path| {
        let mut command = gandr(&["--version"]);
        let _placed = command
            .current_dir(&scratch.0)
            .env("XDG_DATA_HOME", &data)
            .env("CARGO_MANIFEST_DIR", manifest);
        let output = ran(command);
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
        stdout(&output)
    };
    assert_eq!(
        under(Path::new(env!("CARGO_MANIFEST_DIR"))),
        format!("gandr {}\n", env!("CARGO_PKG_VERSION")),
        "cargo running the driver's own package runs that build, not the default"
    );
    assert_eq!(
        under(&scratch.0),
        "ran fake --version\n",
        "another package's manifest directory leaves the selection to the default"
    );
}

/// `GANDR_TOOLCHAIN` outranks a pin, a pin outranks the default, and the
/// default answers where nothing else names a toolchain.
#[cfg(unix)]
#[test]
fn the_environment_outranks_the_pin_and_the_pin_the_default()
{
    let scratch = Scratch::new(Path::new("toolchain-rank"));
    let data = scratch.0.join("data");
    for name in ["first", "second", "third"] {
        let build = fake_toolchain(&scratch, Path::new(name));
        let link = proxied(
            &["toolchain", "link", name, &build.to_string_lossy()],
            &scratch.0,
            &data,
            Maybe::Absent(()),
        );
        assert_eq!(code(&link), Code(0_i32), "{}", stderr(&link));
    }
    let default = proxied(
        &["toolchain", "default", "third"],
        &scratch.0,
        &data,
        Maybe::Absent(()),
    );
    assert_eq!(code(&default), Code(0_i32), "{}", stderr(&default));
    let pinned = scratch.0.join("pinned");
    let _pin = scratch.file(Path::new("pinned/gandr-toolchain"), Text::from("second\n"));
    let nested = pinned.join("deeper");
    std::fs::create_dir_all(&nested).expect("a directory below the pin is made");
    let ran_as = |working: &Path, selecting: Maybe<&std::ffi::OsStr, ()>| {
        let output = proxied(&["check"], working, &data, selecting);
        assert_eq!(code(&output), Code(0_i32), "{}", stderr(&output));
        stdout(&output)
    };
    assert_eq!(
        ran_as(&nested, Maybe::Present(std::ffi::OsStr::new("first"))),
        "ran first check\n"
    );
    assert_eq!(
        ran_as(&nested, Maybe::Absent(())),
        "ran second check\n",
        "the nearest pin above the working directory answers"
    );
    assert_eq!(
        ran_as(&scratch.0, Maybe::Absent(())),
        "ran third check\n",
        "the default answers where no pin does"
    );
    let list = proxied(&["toolchain", "list"], &nested, &data, Maybe::Absent(()));
    let listed = stdout(&list);
    let marks: Vec<(&str, &str)> = listed
        .lines()
        .map(|line| {
            let (name, rest) = line.split_once(' ').expect("a line names a toolchain");
            (name, rest.split_once(" (").map_or("", |(_, marks)| marks))
        })
        .collect();
    assert_eq!(
        marks,
        [
            ("first", ""),
            ("second", "selected)"),
            ("third", "default)")
        ],
        "the list marks the default and the pinned selection"
    );
}

/// A name no installed toolchain answers is refused before any verb runs,
/// naming where the name came from, and so is a name that is not one.
#[cfg(unix)]
#[test]
fn a_name_no_toolchain_answers_is_refused_by_its_source()
{
    let scratch = Scratch::new(Path::new("toolchain-unknown"));
    let data = scratch.0.join("data");
    let pin = scratch.file(Path::new("gandr-toolchain"), Text::from("ghost\n"));
    let refused = proxied(&["check"], &scratch.0, &data, Maybe::Absent(()));
    assert_eq!(code(&refused), Code(2_i32));
    assert_eq!(
        stderr(&refused),
        format!(
            "gandr: the pin {} names the toolchain `ghost`, which is not installed: `gandr toolchain link ghost <path>` installs it\n",
            pin.display()
        )
    );
    let misnamed = proxied(
        &["check"],
        &scratch.0,
        &data,
        Maybe::Present(std::ffi::OsStr::new("../escape")),
    );
    assert_eq!(code(&misnamed), Code(2_i32));
    assert!(
        stderr(&misnamed).starts_with("gandr: `../escape` is not a toolchain's name"),
        "{}",
        stderr(&misnamed)
    );
}

/// A fake toolchain's description: its name, its version and the features
/// it meets.
#[cfg(unix)]
#[derive(Clone, Copy)]
struct Fake<'fake>
{
    /// Its name, and its directory's.
    name: &'fake str,
    /// The version it describes.
    version: &'fake str,
    /// The features it describes.
    features: &'fake [&'fake str],
}

/// A toolchain directory under `scratch` named as `fake` is, whose `gandr`
/// describes itself as `fake` does on this host's system, noting each
/// description in `log`, and otherwise prints `ran <name> <its arguments>`.
///
/// # Specification
/// trivial.
#[cfg(unix)]
fn described_toolchain(
    scratch: &Scratch,
    fake: Fake<'_>,
    log: &Path,
) -> PathBuf
{
    use core::fmt::Write as _;
    use std::os::unix::fs::PermissionsExt as _;

    let Fake {
        name,
        version,
        features,
    } = fake;
    let mut description = format!(
        "version {version}\\nsystem {}-{}\\n",
        std::env::consts::ARCH,
        std::env::consts::OS
    );
    for feature in features {
        write!(description, "feature {feature}\\n").expect("a string takes a line");
    }
    let script = format!(
        "#!/bin/sh\nif [ \"$1 $2\" = \"toolchain describe\" ]; then\n  echo {name} >> '{}'\n  printf '{description}'\n  exit 0\nfi\necho \"ran {name} $*\"\n",
        log.display()
    );
    let executable = scratch.file(
        &Path::new("builds").join(name).join("gandr"),
        Text::from(&*script),
    );
    std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o755))
        .expect("the fake build is executable");
    executable
        .parent()
        .expect("the build has a directory")
        .to_path_buf()
}

/// A package's constraint chooses among the installed toolchains: the default
/// when it meets it, else the highest version that does; a pin naming one
/// that does not is refused by its source, and a constraint none meets by
/// each clause. Each toolchain describes itself once per image.
#[cfg(unix)]
#[test]
fn a_package_s_constraint_chooses_among_the_toolchains()
{
    let scratch = Scratch::new(Path::new("toolchain-constrained"));
    let data = scratch.0.join("data");
    let package = scratch.0.join("package");
    std::fs::create_dir_all(&package).expect("the package's directory is made");
    let log = scratch.0.join("described");
    for (name, version, features) in [
        ("old", "0.1.0", &["shared"][..]),
        ("new", "0.3.0", &["shared"][..]),
        ("bare", "0.4.0", &[][..]),
    ] {
        let fake = Fake {
            name,
            version,
            features,
        };
        let build = described_toolchain(&scratch, fake, &log);
        let link = proxied(
            &["toolchain", "link", name, &build.to_string_lossy()],
            &scratch.0,
            &data,
            Maybe::Absent(()),
        );
        assert_eq!(code(&link), Code(0_i32), "{}", stderr(&link));
    }
    let manifest = |gandr: &str| {
        std::fs::write(
            package.join("gandr.toml"),
            format!(
                "[toolchain]\ngandr = \"{gandr}\"\nfeatures = [\n  \"shared\",\n]\nsystems = []\n"
            ),
        )
        .expect("the manifest is written");
    };
    let checked = |working: &Path| {
        let output = proxied(&["check"], working, &data, Maybe::Absent(()));
        (code(&output), stdout(&output), stderr(&output))
    };
    manifest(">= 0.1");
    assert_eq!(
        checked(&package),
        (Code(0_i32), String::from("ran old check\n"), String::new()),
        "the default meets the constraint, and runs"
    );
    manifest(">= 0.2");
    assert_eq!(
        checked(&package),
        (Code(0_i32), String::from("ran new check\n"), String::new()),
        "the highest version that meets the constraint runs; `bare` lacks the feature"
    );
    let described = || std::fs::read_to_string(&log).map_or(0_usize, |lines| lines.lines().count());
    let once = described();
    let _again = checked(&package);
    assert_eq!(
        described(),
        once,
        "each toolchain is described once per image"
    );
    assert_eq!(
        checked(&scratch.0),
        (Code(0_i32), String::from("ran old check\n"), String::new()),
        "outside the package no constraint holds"
    );
    let pin = scratch.file(Path::new("package/gandr-toolchain"), Text::from("old\n"));
    let (pinned, _, refusal) = checked(&package);
    assert_eq!(pinned, Code(2_i32));
    assert!(
        refusal.starts_with(&format!(
            "gandr: the pin {} names the toolchain `old`, which leaves the constraint of {} unmet\n  ToolchainUnmet.gandr:",
            pin.display(),
            package.join("gandr.toml").display()
        )),
        "{refusal}"
    );
    std::fs::remove_file(&pin).expect("the pin is removed");
    manifest(">= 0.5");
    let (unmeetable, _, refusal) = checked(&package);
    assert_eq!(unmeetable, Code(2_i32));
    assert!(
        refusal.starts_with(&format!(
            "gandr: no installed toolchain meets the constraint of {}; the nearest, `old`, leaves it unmet\n  ToolchainUnmet.gandr:",
            package.join("gandr.toml").display()
        )),
        "{refusal}"
    );
    let describe = ran(gandr(&["toolchain", "describe"]));
    assert_eq!(code(&describe), Code(0_i32), "{}", stderr(&describe));
    let description = stdout(&describe);
    assert!(
        description.starts_with("version ")
            && description.contains(&format!(
                "\nsystem {}-{}\n",
                std::env::consts::ARCH,
                std::env::consts::OS
            ))
            && description.contains("\nfeature project-manifest\n"),
        "the build describes its version, its system and the features its ledger meets: {description}"
    );
}
