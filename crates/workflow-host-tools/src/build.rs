//! A job built into its key, under a lock for the key, whole or not at all,
//! and the scratch of the builds removed when no build holds it.
//!
//! The key of a job is the directory `<into>/<target>/<install
//! name>/<version>`. A build takes the lock of its key, builds into a partial
//! directory and renames it into the key at its end. So a key stands whole or
//! not at all, and two builders of one key build it once. The builds of a run
//! share the scratch `<into>/.scratch`: one target directory and the clones.
//! [`prune`] removes it at the end of a run.

use std::fs::File;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;

use crate::error::HostToolsError;
use crate::host::Host;
use crate::jobs::Job;
use crate::names::Placeholder;
use crate::names::ToolKey;
use crate::names::Version;
use crate::steps::Run;
use crate::steps::Step;
use crate::steps::steps;

/// The lock that each build holds shared while it uses the scratch, and that
/// [`prune`] takes whole, under `<into>/.locks`.
const SCRATCH_LOCK: &str = "scratch.lock";

/// What a prune did with the scratch.
///
/// # Specification
/// - provides: whether the prune removed the scratch, found a build that holds
///   it, or found no scratch.
/// - executable: none — a plain record.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Pruned
{
    /// The scratch stood, no build held it, and the prune removed it.
    Removed,
    /// A build holds the scratch, and the prune left it.
    Busy,
    /// No scratch stood.
    Absent,
}

/// What a build did for a job.
///
/// # Specification
/// - provides: whether the job's key stood already or the build wrote it.
/// - executable: none — a plain record.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Built
{
    /// The key stood, and the build ran no step.
    Kept,
    /// The build ran each step and renamed its result into the key.
    Built,
}

/// What runs the commands of a build.
///
/// # Specification
/// - provides: the one effect of a step that runs a command, so a test runs a
///   build with no compiler.
pub trait Runner
{
    /// Run `run` for the tool `key`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the command ran and exited with success.
    /// - provides: the effect of [`Step::Run`].
    /// - fails: [`HostToolsError::Command`] when the command cannot start or
    ///   exits with a failure.
    /// - panics: none.
    /// - executable: none — the outcome is the command's.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a command that exits with success and one that fails,
    ///   each run by [`Processes`].
    /// - witness: `build::tests::a_process_that_fails_names_its_command_and_its_log`
    fn run(
        &mut self,
        key: &ToolKey,
        run: &Run,
    ) -> Result<(), HostToolsError>;
}

/// A runner of real processes, each with its output in one log.
///
/// # Specification
/// - provides: each command spawned with its variables and its directory, its
///   standard output and standard error appended to `log`.
/// - executable: none — a plain record; [`Runner::run`] states the effect.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Processes
{
    /// The log that each command's output goes to.
    pub log: PathBuf,
}

impl Runner for Processes
{
    /// Spawn `run`, wait for it, and refuse a failure with the log's path.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the command ran with its output appended to `self.log`, and
    ///   exited with success.
    /// - provides: the process boundary of a build.
    /// - fails: [`HostToolsError::Io`] when the log cannot be opened;
    ///   [`HostToolsError::Command`] when the command cannot start or exits
    ///   with a failure, naming the log.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `true` runs, and `false` is refused with its status
    ///   and the log.
    /// - witness: `build::tests::a_process_that_fails_names_its_command_and_its_log`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Io { .. } | HostToolsError::Command { .. })))]
    #[inline]
    fn run(
        &mut self,
        key: &ToolKey,
        run: &Run,
    ) -> Result<(), HostToolsError>
    {
        let io = |error: std::io::Error| HostToolsError::Io {
            path: self.log.clone(),
            message: error.to_string(),
        };
        let log = File::options()
            .create(true)
            .append(true)
            .open(&self.log)
            .map_err(io)?;
        let mut command = std::process::Command::new(&run.program);
        command
            .args(&run.args)
            .envs(run.env.iter().map(|&(ref name, ref value)| (name, value)))
            .stdin(std::process::Stdio::null())
            .stdout(log.try_clone().map_err(io)?)
            .stderr(log);
        if let Some(cwd) = run.cwd.as_ref() {
            command.current_dir(cwd);
        }
        let failed = |message: String| HostToolsError::Command {
            key: key.to_string(),
            command: run.line(),
            message,
        };
        let status = command
            .status()
            .map_err(|error| failed(format!("does not start: {error}")))?;
        if status.success() {
            Ok(())
        }
        else {
            Err(failed(format!(
                "exits with {status}; its output is in {}",
                self.log.display()
            )))
        }
    }
}

/// The key of `job` under `into`: `<into>/<target>/<install name>/<version>`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn key(
    into: &Path,
    job: &Job,
) -> PathBuf
{
    into.join(&job.target)
        .join(&job.install_name)
        .join(&job.version)
}

/// Build `job` into its key under `into`, unless the key stands.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the key of `job` stands. When it stood before the lock or after
///   it, nothing ran and the result is [`Built::Kept`]. Otherwise each step of
///   [`steps`] ran into the partial directory
///   `<into>/.partial/<target>/<install name>/<version>`, which then took the
///   key's name, and the result is [`Built::Built`]. A refusal leaves no key
///   and no partial directory.
/// - provides: the one build of a key, whole or not at all, once for each key
///   across the builders that share `into`.
/// - fails: every refusal of [`steps`] and of `runner`; [`HostToolsError::Io`]
///   when a directory, the lock, a stamped file or the rename fails.
/// - panics: none.
/// - executable: none — the outcome is the directory on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a key that stands is kept with no command; a build whose
///   commands succeed renames its result into the key; a build whose command
///   fails leaves no key and no partial directory; a stamp writes the version
///   over each placeholder.
/// - witness: `build::tests::a_key_that_stands_is_kept_and_runs_nothing`
/// - witness: `build::tests::a_build_renames_its_result_into_the_key`
/// - witness: `build::tests::a_failed_build_leaves_no_key`
/// - witness: `build::tests::a_stamp_writes_the_version_over_each_placeholder`
#[inline]
pub fn build<R>(
    job: &Job,
    into: &Path,
    host: &Host,
    runner: &mut R,
) -> Result<Built, HostToolsError>
where
    R: Runner,
{
    let key = key(into, job);
    if key.is_dir() {
        return Ok(Built::Kept);
    }
    let locks = into.join(".locks");
    std::fs::create_dir_all(&locks).map_err(|error| io(&locks, &error))?;
    let lock_path = locks.join(format!(
        "{}.{}.{}.lock",
        job.target, job.install_name, job.version
    ));
    let lock = File::create(&lock_path).map_err(|error| io(&lock_path, &error))?;
    lock.lock().map_err(|error| io(&lock_path, &error))?;
    // A builder that held the lock before this one may have built the key.
    if key.is_dir() {
        return Ok(Built::Kept);
    }
    let partial = into
        .join(".partial")
        .join(&job.target)
        .join(&job.install_name)
        .join(&job.version);
    clear(&partial)?;
    std::fs::create_dir_all(&partial).map_err(|error| io(&partial, &error))?;
    // A prune removes the scratch only while no build holds this lock.
    let scratch_path = locks.join(SCRATCH_LOCK);
    let scratch_lock = File::create(&scratch_path).map_err(|error| io(&scratch_path, &error))?;
    scratch_lock
        .lock_shared()
        .map_err(|error| io(&scratch_path, &error))?;
    let scratch = into.join(".scratch");
    let built = steps(job, &partial, &scratch, host).and_then(|planned| {
        planned.iter().try_for_each(|step| match *step {
            Step::Clear(ref directory) => clear(directory),
            Step::Run(ref run) => runner.run(&job.key, run),
            Step::Stamp {
                ref files,
                ref placeholder,
                ref version,
            } => files
                .iter()
                .try_for_each(|file| stamp(file, placeholder, version)),
        })
    });
    if let Err(error) = built {
        // The refusal is the build's; a partial directory that also cannot
        // be removed is cleared again by the next build of the key.
        let _cleared = clear(&partial);
        return Err(error);
    }
    if let Some(parent) = key.parent() {
        std::fs::create_dir_all(parent).map_err(|error| io(parent, &error))?;
    }
    std::fs::rename(&partial, &key).map_err(|error| io(&key, &error))?;
    Ok(Built::Built)
}

/// Remove the scratch `<into>/.scratch` when no build holds it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: with no scratch, nothing changes and the result is
///   [`Pruned::Absent`]. When a build holds the scratch's lock shared, the
///   scratch stands and the result is [`Pruned::Busy`]: the prune never waits.
///   Otherwise the prune holds the lock whole, the scratch does not stand, and
///   the result is [`Pruned::Removed`].
/// - provides: the bound of the scratch: at rest it holds nothing, and a run
///   that a crash ends leaves a scratch that the next run's prune removes.
/// - fails: [`HostToolsError::Io`] when the lock cannot be made or taken, or
///   the scratch cannot be removed.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a prune leaves a scratch that a build holds, removes it
///   when no build holds it, and finds none after.
/// - witness: `build::tests::a_prune_removes_the_scratch_unless_a_build_holds_it`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Io { .. })))]
#[inline]
pub fn prune(into: &Path) -> Result<Pruned, HostToolsError>
{
    let scratch = into.join(".scratch");
    if !scratch.exists() {
        return Ok(Pruned::Absent);
    }
    let locks = into.join(".locks");
    std::fs::create_dir_all(&locks).map_err(|error| io(&locks, &error))?;
    let lock_path = locks.join(SCRATCH_LOCK);
    let lock = File::create(&lock_path).map_err(|error| io(&lock_path, &error))?;
    match lock.try_lock() {
        Ok(()) => {},
        Err(std::fs::TryLockError::WouldBlock) => return Ok(Pruned::Busy),
        Err(std::fs::TryLockError::Error(error)) => return Err(io(&lock_path, &error)),
    }
    clear(&scratch)?;
    Ok(Pruned::Removed)
}

/// Remove the key of each version of `job`'s tool and target other than the
/// version of `job`, with the markers of its copies.
///
/// # Specification
/// - requires: nothing.
/// - ensures: of the keys under `<into>/<target>/<install name>/` that the call
///   reads, only the key of `job`'s version stands. Each other key goes under
///   its own lock, and each marker `<into>/.pushed/<host>/<target>.<install
///   name>.<version>` of a removed version goes with it. The result names the
///   removed versions in order.
/// - provides: the bound of the keys: the builder holds one key for each tool
///   and target, the version that `mise.lock` locks.
/// - fails: [`HostToolsError::Io`] when a directory cannot be read, a lock
///   cannot be made or taken, or a key or a marker cannot be removed.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — the keys of an older and a newer version go with their
///   markers; the key and the marker of the job's version stay.
/// - witness: `build::tests::a_retire_removes_each_other_version_and_its_markers`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Io { .. })))]
#[inline]
pub fn retire(
    into: &Path,
    job: &Job,
) -> Result<Vec<Version>, HostToolsError>
{
    let tool = into.join(&job.target).join(&job.install_name);
    let mut versions = names(&tool)?
        .into_iter()
        .filter(|name| job.version != *name.as_str())
        .map(|name| Version::from(name.as_str()))
        .collect::<Vec<_>>();
    versions.sort();
    let hosts = names(&into.join(".pushed"))?;
    let locks = into.join(".locks");
    if !versions.is_empty() {
        std::fs::create_dir_all(&locks).map_err(|error| io(&locks, &error))?;
    }
    for version in &versions {
        let lock_path = locks.join(format!(
            "{}.{}.{version}.lock",
            job.target, job.install_name
        ));
        let lock = File::create(&lock_path).map_err(|error| io(&lock_path, &error))?;
        lock.lock().map_err(|error| io(&lock_path, &error))?;
        clear(&tool.join(version))?;
        // The lock is the marker's name with `.lock` after it.
        let marker = lock_path.file_stem().unwrap_or_default();
        for host in &hosts {
            let path = into.join(".pushed").join(host).join(marker);
            match std::fs::remove_file(&path) {
                Ok(()) => {},
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {},
                Err(error) => return Err(io(&path, &error)),
            }
        }
    }
    Ok(versions)
}

/// The names of the entries of `directory`, none when it does not stand.
///
/// # Specification
/// trivial.
#[inline]
fn names(directory: &Path) -> Result<Vec<String>, HostToolsError>
{
    let entries = match std::fs::read_dir(directory) {
        Ok(entries) => entries,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => return Err(io(directory, &error)),
    };
    entries
        .map(|entry| {
            entry
                .map(|entry| entry.file_name().to_string_lossy().into_owned())
                .map_err(|error| io(directory, &error))
        })
        .collect()
}

/// Remove `directory` and what it holds, if it stands.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `directory` does not stand.
/// - provides: the effect of [`Step::Clear`] and the removal of a partial
///   directory.
/// - fails: [`HostToolsError::Io`] when it stands and cannot be removed.
/// - panics: none.
/// - executable: none — the outcome is the directory on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`build`].
/// - witness: `build::tests::a_failed_build_leaves_no_key`
#[inline]
fn clear(directory: &Path) -> Result<(), HostToolsError>
{
    match std::fs::remove_dir_all(directory) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(io(directory, &error)),
    }
}

/// Write `version` over each `placeholder` of `file`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `file` holds `version` where it held `placeholder`.
/// - provides: the effect of [`Step::Stamp`].
/// - fails: [`HostToolsError::Io`] when `file` cannot be read or written.
/// - panics: none.
/// - executable: none — the outcome is the file on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`build`].
/// - witness: `build::tests::a_stamp_writes_the_version_over_each_placeholder`
#[inline]
fn stamp(
    file: &Path,
    placeholder: &Placeholder,
    version: &Version,
) -> Result<(), HostToolsError>
{
    let text = std::fs::read_to_string(file).map_err(|error| io(file, &error))?;
    let placeholder: &str = placeholder.as_ref();
    let version: &str = version.as_ref();
    std::fs::write(file, text.replace(placeholder, version)).map_err(|error| io(file, &error))
}

/// The refusal of an operation on `path`.
///
/// # Specification
/// trivial.
#[inline]
fn io(
    path: &Path,
    error: &std::io::Error,
) -> HostToolsError
{
    HostToolsError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use super::Built;
    use super::Processes;
    use super::Pruned;
    use super::Runner;
    use super::build;
    use super::io;
    use super::key;
    use super::prune;
    use super::retire;
    use crate::error::HostToolsError;
    use crate::host::Host;
    use crate::input::Input;
    use crate::jobs::Job;
    use crate::names::Placeholder;
    use crate::names::Repository;
    use crate::names::Template;
    use crate::names::ToolKey;
    use crate::names::Version;
    use crate::recipe::Recipe;
    use crate::recipe::Stamp;
    use crate::steps::Run;

    /// A runner that records each command and writes the binary that a
    /// `cargo install` would, or fails each command.
    struct Fake
    {
        /// The command lines it ran.
        ran: Vec<String>,
        /// Whether each command fails.
        fails: bool,
    }

    impl Runner for Fake
    {
        /// Record `run`, then refuse it or write the binary of its root.
        ///
        /// # Specification
        /// trivial.
        fn run(
            &mut self,
            key: &ToolKey,
            run: &Run,
        ) -> Result<(), HostToolsError>
        {
            self.ran.push(run.line());
            if self.fails {
                return Err(HostToolsError::Command {
                    key: key.to_string(),
                    command: run.line(),
                    message: "exits with 101".to_owned(),
                });
            }
            if let Some(root) = run.args.iter().skip_while(|arg| *arg != "--root").nth(1) {
                let bin = Path::new(root).join("bin");
                std::fs::create_dir_all(&bin).map_err(|error| io(&bin, &error))?;
                let tool = bin.join("tool");
                std::fs::write(&tool, "binary").map_err(|error| io(&tool, &error))?;
            }
            Ok(())
        }
    }

    /// A runner whose clone writes a manifest with the placeholder, and whose
    /// install reads it back.
    struct Cloning
    {
        /// The clone's directory.
        clone: PathBuf,
        /// The manifest the install read.
        read: Option<String>,
    }

    impl Runner for Cloning
    {
        /// Write the manifest on the clone, or read it back on the install.
        ///
        /// # Specification
        /// trivial.
        fn run(
            &mut self,
            _key: &ToolKey,
            run: &Run,
        ) -> Result<(), HostToolsError>
        {
            let manifest = self.clone.join("Cargo.toml");
            if run.program == "git" {
                std::fs::create_dir_all(&self.clone).map_err(|error| io(&self.clone, &error))?;
                std::fs::write(&manifest, "version = \"0.0.0-dev\"\n")
                    .map_err(|error| io(&manifest, &error))?;
            }
            else {
                self.read = Some(
                    std::fs::read_to_string(&manifest).map_err(|error| io(&manifest, &error))?,
                );
            }
            Ok(())
        }
    }

    /// A scratch directory of the running test, empty: the test's thread
    /// names it.
    ///
    /// # Specification
    /// trivial.
    fn scratch() -> PathBuf
    {
        let test = std::thread::current()
            .name()
            .unwrap_or("test")
            .replace("::", "-");
        let directory =
            std::env::temp_dir().join(format!("host-tools-{}-{test}", std::process::id()));
        let _gone = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).unwrap();
        directory
    }

    /// A host with the riscv64 linker.
    ///
    /// # Specification
    /// trivial.
    fn host() -> Host
    {
        Host::read(&Input {
            path: "host-tools.toml".into(),
            text: "[target.riscv64gc-unknown-linux-gnu]\nlinker = \"rv-gcc\"\n".to_owned(),
        })
        .unwrap()
    }

    /// A job of a crate at 1.2.3 for riscv64.
    ///
    /// # Specification
    /// trivial.
    fn job() -> Job
    {
        Job {
            key: "github:a/tool".into(),
            version: "1.2.3".into(),
            target: "riscv64gc-unknown-linux-gnu".into(),
            install_name: "github-a-tool".into(),
            recipe: Recipe::Crate {
                name: "tool".to_owned(),
                features: Vec::new(),
                default_features: None,
            },
            needs: Vec::new(),
        }
    }

    #[test]
    fn a_key_that_stands_is_kept_and_runs_nothing()
    {
        let into = scratch();
        std::fs::create_dir_all(key(&into, &job())).unwrap();
        let mut runner = Fake {
            ran: Vec::new(),
            fails: false,
        };
        assert_eq!(build(&job(), &into, &host(), &mut runner), Ok(Built::Kept));
        assert!(runner.ran.is_empty());
        std::fs::remove_dir_all(&into).unwrap();
    }

    #[test]
    fn a_build_renames_its_result_into_the_key()
    {
        let into = scratch();
        let mut runner = Fake {
            ran: Vec::new(),
            fails: false,
        };
        assert_eq!(build(&job(), &into, &host(), &mut runner), Ok(Built::Built));
        let key = into.join("riscv64gc-unknown-linux-gnu/github-a-tool/1.2.3");
        assert_eq!(
            std::fs::read_to_string(key.join("bin/tool")).unwrap(),
            "binary"
        );
        assert!(
            !into
                .join(".partial/riscv64gc-unknown-linux-gnu/github-a-tool/1.2.3")
                .exists()
        );
        assert_eq!(runner.ran.len(), 1);
        assert_eq!(build(&job(), &into, &host(), &mut runner), Ok(Built::Kept));
        assert_eq!(runner.ran.len(), 1);
        std::fs::remove_dir_all(&into).unwrap();
    }

    #[test]
    fn a_failed_build_leaves_no_key()
    {
        let into = scratch();
        let mut runner = Fake {
            ran: Vec::new(),
            fails: true,
        };
        let refused = build(&job(), &into, &host(), &mut runner);
        assert!(
            matches!(refused, Err(HostToolsError::Command { ref key, .. }) if key == "github:a/tool")
        );
        assert!(!key(&into, &job()).exists());
        assert!(
            !into
                .join(".partial/riscv64gc-unknown-linux-gnu/github-a-tool/1.2.3")
                .exists()
        );
        std::fs::remove_dir_all(&into).unwrap();
    }

    #[test]
    fn a_stamp_writes_the_version_over_each_placeholder()
    {
        let into = scratch();
        let clone = into.join(".scratch/src/github-a-tool/1.2.3");
        let mut stamped = job();
        stamped.recipe = Recipe::Cargo {
            repository: Repository::from("https://example.org/tool"),
            tag: Template::from("v{version}"),
            path: ".".to_owned(),
            stamp: Some(Stamp {
                files: vec!["Cargo.toml".to_owned()],
                placeholder: Placeholder::from("0.0.0-dev"),
            }),
        };
        let mut runner = Cloning { clone, read: None };
        assert_eq!(
            build(&stamped, &into, &host(), &mut runner),
            Ok(Built::Built)
        );
        assert_eq!(runner.read.as_deref(), Some("version = \"1.2.3\"\n"));
        std::fs::remove_dir_all(&into).unwrap();
    }

    #[test]
    fn a_process_that_fails_names_its_command_and_its_log()
    {
        let directory = scratch();
        let log = directory.join("build.log");
        let mut processes = Processes { log: log.clone() };
        let run = |program: &str| Run {
            program: program.to_owned(),
            args: Vec::new(),
            env: Vec::new(),
            cwd: None,
        };
        let key = ToolKey::from("github:a/tool");
        assert_eq!(processes.run(&key, &run("true")), Ok(()));
        let refused = processes.run(&key, &run("false")).unwrap_err().to_string();
        assert!(
            refused.starts_with("github:a/tool: `false` exits with exit status: 1"),
            "{refused}"
        );
        assert!(
            refused.ends_with(&format!("its output is in {}", log.display())),
            "{refused}"
        );
        std::fs::remove_dir_all(&directory).unwrap();
    }

    #[test]
    fn a_prune_removes_the_scratch_unless_a_build_holds_it()
    {
        let into = scratch();
        std::fs::create_dir_all(into.join(".scratch/target")).unwrap();
        std::fs::create_dir_all(into.join(".locks")).unwrap();
        let held = std::fs::File::create(into.join(".locks/scratch.lock")).unwrap();
        held.lock_shared().unwrap();
        assert_eq!(prune(&into), Ok(Pruned::Busy));
        assert!(into.join(".scratch/target").is_dir());
        drop(held);
        assert_eq!(prune(&into), Ok(Pruned::Removed));
        assert!(!into.join(".scratch").exists());
        assert_eq!(prune(&into), Ok(Pruned::Absent));
        std::fs::remove_dir_all(&into).unwrap();
    }

    #[test]
    fn a_retire_removes_each_other_version_and_its_markers()
    {
        let into = scratch();
        let tool = into.join("riscv64gc-unknown-linux-gnu/github-a-tool");
        for version in ["1.2.2", "1.2.3", "1.2.4"] {
            std::fs::create_dir_all(tool.join(version).join("bin")).unwrap();
        }
        let pushed = into.join(".pushed/rv");
        std::fs::create_dir_all(&pushed).unwrap();
        let marker = |version: &str| {
            pushed.join(format!(
                "riscv64gc-unknown-linux-gnu.github-a-tool.{version}"
            ))
        };
        std::fs::write(marker("1.2.2"), "").unwrap();
        std::fs::write(marker("1.2.3"), "").unwrap();
        assert_eq!(
            retire(&into, &job()),
            Ok(vec![Version::from("1.2.2"), Version::from("1.2.4")])
        );
        assert!(tool.join("1.2.3").is_dir());
        assert!(!tool.join("1.2.2").exists());
        assert!(!tool.join("1.2.4").exists());
        assert!(marker("1.2.3").is_file());
        assert!(!marker("1.2.2").exists());
        std::fs::remove_dir_all(&into).unwrap();
    }
}
