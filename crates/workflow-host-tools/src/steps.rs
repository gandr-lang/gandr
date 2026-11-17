//! The steps that build a job: the commands to run and the files to stamp.

use std::path::Path;
use std::path::PathBuf;

use anodized::spec;

use crate::error::HostToolsError;
use crate::host::Host;
use crate::jobs::Job;
use crate::names::Placeholder;
use crate::names::Repository;
use crate::names::Template;
use crate::names::Version;
use crate::recipe::Recipe;

/// One step of a build.
///
/// # Specification
/// - provides: a command to run, a directory to clear before a clone, or the
///   version to write over a placeholder in some files.
/// - executable: none — a plain record; [`steps`] fills it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Step
{
    /// Remove a directory and what it holds, if it stands.
    Clear(PathBuf),
    /// Run a command.
    Run(Run),
    /// Write `version` over `placeholder` in each of `files`.
    Stamp
    {
        /// The files.
        files: Vec<PathBuf>,
        /// The placeholder each file holds.
        placeholder: Placeholder,
        /// The version.
        version: Version,
    },
}

/// A command to run.
///
/// # Specification
/// - provides: the program, its arguments, the variables it adds to the
///   environment and its working directory.
/// - executable: none — a plain record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Run
{
    /// The program.
    pub program: String,
    /// The arguments.
    pub args: Vec<String>,
    /// The variables it adds to the environment.
    pub env: Vec<(String, String)>,
    /// The working directory, or the caller's.
    pub cwd: Option<PathBuf>,
}

impl Run
{
    /// The command as a line: the program and its arguments, apart by
    /// spaces.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn line(&self) -> String
    {
        core::iter::once(self.program.as_str())
            .chain(self.args.iter().map(String::as_str))
            .collect::<Vec<_>>()
            .join(" ")
    }
}

/// The steps that build `job` into `root`, with its clones and its cargo
/// target directory under `scratch`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a crate, one `cargo install` of the crate at the version for
///   the target into `root`. For a cargo package, the clone's directory
///   cleared, a `git clone` of the tag, the stamp where the recipe has one, and
///   one `cargo install --path` into `root`. For a Go package, the clone's
///   directory cleared, a `git clone` of the tag and one `go build` into
///   `root/bin`. Each cargo command carries the target's linker and C tools,
///   the shared target directory and each program the job needs, by its name in
///   capitals.
/// - provides: the one statement of how a recipe builds.
/// - fails: [`HostToolsError::Host`] when `host` names no tools for the target
///   or no path for a program the job needs; [`HostToolsError::Recipe`] for a
///   Go build of a target that names no known Go architecture.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a crate with features and a needed program, a cargo
///   package with a stamp and a Go package each give their command lines and
///   variables; a missing program and an unknown Go architecture are refused.
/// - witness: `steps::tests::a_crate_installs_for_the_target_with_its_features_and_programs`
/// - witness: `steps::tests::a_cargo_package_clones_stamps_and_installs`
/// - witness: `steps::tests::a_go_package_clones_and_builds_with_its_stamp`
/// - witness: `steps::tests::a_missing_program_and_an_unknown_architecture_are_refused`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|steps| !steps.is_empty()) || matches!(ret, Err(HostToolsError::Host { .. } | HostToolsError::Recipe { .. })))]
#[inline]
pub fn steps(
    job: &Job,
    root: &Path,
    scratch: &Path,
    host: &Host,
) -> Result<Vec<Step>, HostToolsError>
{
    let clone = scratch
        .join("src")
        .join(&job.install_name)
        .join(&job.version);
    match job.recipe {
        Recipe::Crate {
            ref name,
            ref features,
            default_features,
        } => {
            let mut args = install_args(job, root);
            args.extend([
                name.clone(),
                "--version".to_owned(),
                job.version.to_string(),
            ]);
            if default_features == Some(false) {
                args.push("--no-default-features".to_owned());
            }
            if !features.is_empty() {
                args.extend(["--features".to_owned(), features.join(",")]);
            }
            Ok(vec![Step::Run(Run {
                program: "cargo".to_owned(),
                args,
                env: cargo_env(job, scratch, host)?,
                cwd: None,
            })])
        },
        Recipe::Cargo {
            ref repository,
            ref tag,
            ref path,
            ref stamp,
        } => {
            let mut steps = vec![
                Step::Clear(clone.clone()),
                clone_step(job, repository, tag, &clone),
            ];
            if let Some(stamp) = stamp.as_ref() {
                steps.push(Step::Stamp {
                    files: stamp.files.iter().map(|file| clone.join(file)).collect(),
                    placeholder: stamp.placeholder.clone(),
                    version: job.version.clone(),
                });
            }
            let mut args = install_args(job, root);
            args.extend(["--path".to_owned(), clone.join(path).display().to_string()]);
            steps.push(Step::Run(Run {
                program: "cargo".to_owned(),
                args,
                env: cargo_env(job, scratch, host)?,
                cwd: None,
            }));
            Ok(steps)
        },
        Recipe::Go {
            ref repository,
            ref tag,
            ref package,
            ref binary,
            ref ldflags,
        } => {
            let arch = job.target.go_arch().ok_or_else(|| HostToolsError::Recipe {
                key: job.key.to_string(),
                message: format!(
                    "builds with Go, which names no architecture for {}",
                    job.target
                ),
            })?;
            let mut args = vec!["build".to_owned(), "-trimpath".to_owned()];
            if let Some(flags) = ldflags.as_ref() {
                args.extend(["-ldflags".to_owned(), flags.fill(&job.version)]);
            }
            args.extend([
                "-o".to_owned(),
                root.join("bin").join(binary).display().to_string(),
                package.clone(),
            ]);
            let mut env = vec![
                ("GOOS".to_owned(), "linux".to_owned()),
                ("GOARCH".to_owned(), arch.to_string()),
                ("CGO_ENABLED".to_owned(), "0".to_owned()),
            ];
            env.extend(programs(job, host)?);
            Ok(vec![
                Step::Clear(clone.clone()),
                clone_step(job, repository, tag, &clone),
                Step::Run(Run {
                    program: "go".to_owned(),
                    args,
                    env,
                    cwd: Some(clone),
                }),
            ])
        },
    }
}

/// The arguments that open a `cargo install` of `job` into `root`.
///
/// # Specification
/// trivial.
#[inline]
fn install_args(
    job: &Job,
    root: &Path,
) -> Vec<String>
{
    vec![
        "install".to_owned(),
        "--locked".to_owned(),
        "--target".to_owned(),
        job.target.to_string(),
        "--root".to_owned(),
        root.display().to_string(),
    ]
}

/// The variables of a cargo build of `job`: the target's linker and C tools,
/// the target directory under `scratch`, and each program the job needs.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `CARGO_TARGET_<TARGET>_LINKER`, then `CC_`, `CXX_` and `AR_` of
///   the target where `host` names them, then `CARGO_TARGET_DIR`, then each
///   program of [`programs`].
/// - provides: the one environment of a cargo build.
/// - fails: as [`Host::tools`] and [`programs`] fail.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`steps`].
/// - witness: `steps::tests::a_crate_installs_for_the_target_with_its_features_and_programs`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|env| env.len() >= 2) || matches!(ret, Err(HostToolsError::Host { .. })))]
#[inline]
fn cargo_env(
    job: &Job,
    scratch: &Path,
    host: &Host,
) -> Result<Vec<(String, String)>, HostToolsError>
{
    let tools = host.tools(&job.target)?;
    let under = job.target.to_string().replace('-', "_");
    let mut env = vec![(
        format!("CARGO_TARGET_{}_LINKER", under.to_uppercase()),
        tools.linker.clone(),
    )];
    for (prefix, tool) in [("CC", &tools.cc), ("CXX", &tools.cxx), ("AR", &tools.ar)] {
        if let Some(tool) = tool.as_ref() {
            env.push((format!("{prefix}_{under}"), tool.clone()));
        }
    }
    env.push((
        "CARGO_TARGET_DIR".to_owned(),
        scratch.join("target").display().to_string(),
    ));
    env.extend(programs(job, host)?);
    Ok(env)
}

/// Each program that `job` needs, as a variable of its name in capitals and
/// the path that `host` names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one variable for each program of `job.needs`, in its order.
/// - provides: the programs a build script runs, as `cmake` reads `CMAKE`.
/// - fails: as [`Host::program`] fails.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`steps`].
/// - witness: `steps::tests::a_missing_program_and_an_unknown_architecture_are_refused`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|env| env.len() == job.needs.len()) || matches!(ret, Err(HostToolsError::Host { .. })))]
#[inline]
fn programs(
    job: &Job,
    host: &Host,
) -> Result<Vec<(String, String)>, HostToolsError>
{
    job.needs
        .iter()
        .map(|name| {
            let text: &str = name.as_ref();
            Ok((
                text.to_uppercase(),
                host.program(name)?.display().to_string(),
            ))
        })
        .collect()
}

/// The `git clone` of the tag `tag` names at the version of `job`, of
/// `repository`, into `clone`: the tag's commit alone.
///
/// # Specification
/// trivial.
#[inline]
fn clone_step(
    job: &Job,
    repository: &Repository,
    tag: &Template,
    clone: &Path,
) -> Step
{
    Step::Run(Run {
        program: "git".to_owned(),
        args: vec![
            "clone".to_owned(),
            "--quiet".to_owned(),
            "--depth".to_owned(),
            "1".to_owned(),
            "--branch".to_owned(),
            tag.fill(&job.version),
            repository.to_string(),
            clone.display().to_string(),
        ],
        env: Vec::new(),
        cwd: None,
    })
}

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use super::Run;
    use super::Step;
    use super::steps;
    use crate::error::HostToolsError;
    use crate::host::Host;
    use crate::input::Input;
    use crate::jobs::Job;
    use crate::names::Placeholder;
    use crate::names::ProgramName;
    use crate::names::Repository;
    use crate::names::Target;
    use crate::names::Template;
    use crate::names::Version;
    use crate::recipe::Recipe;
    use crate::recipe::Stamp;

    /// The riscv64 target.
    const RISCV64: &str = "riscv64gc-unknown-linux-gnu";

    /// A host with the riscv64 linker and C compiler, and a `cmake`.
    ///
    /// # Specification
    /// trivial.
    fn host() -> Host
    {
        Host::read(&Input {
            path: "host-tools.toml".into(),
            text: "[target.riscv64gc-unknown-linux-gnu]\nlinker = \"rv-gcc\"\ncc = \"rv-gcc\"\n\n[programs]\ncmake = \"/opt/cmake\"\n".to_owned(),
        })
        .unwrap()
    }

    /// A job of `recipe` at version 1.2.3 for `target`, needing `needs`.
    ///
    /// # Specification
    /// trivial.
    fn job(
        recipe: Recipe,
        target: Target,
        needs: Vec<ProgramName>,
    ) -> Job
    {
        Job {
            key: "github:a/tool".into(),
            version: "1.2.3".into(),
            target,
            install_name: "github-a-tool".into(),
            recipe,
            needs,
        }
    }

    #[test]
    fn a_crate_installs_for_the_target_with_its_features_and_programs()
    {
        let job = job(
            Recipe::Crate {
                name: "tool".to_owned(),
                features: vec!["rustls".to_owned(), "lua".to_owned()],
                default_features: Some(false),
            },
            Target::from(RISCV64),
            vec![ProgramName::from("cmake")],
        );
        let built = steps(&job, Path::new("/k"), Path::new("/s"), &host()).unwrap();
        let [Step::Run(ref run)] = built[..]
        else {
            panic!("one command: {built:?}");
        };
        assert_eq!(
            run.line(),
            "cargo install --locked --target riscv64gc-unknown-linux-gnu --root /k tool --version 1.2.3 --no-default-features --features rustls,lua"
        );
        assert_eq!(run.env, [
            (
                "CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_LINKER".to_owned(),
                "rv-gcc".to_owned()
            ),
            (
                "CC_riscv64gc_unknown_linux_gnu".to_owned(),
                "rv-gcc".to_owned()
            ),
            ("CARGO_TARGET_DIR".to_owned(), "/s/target".to_owned()),
            ("CMAKE".to_owned(), "/opt/cmake".to_owned()),
        ]);
        assert_eq!(run.cwd, None);
    }

    #[test]
    fn a_cargo_package_clones_stamps_and_installs()
    {
        let job = job(
            Recipe::Cargo {
                repository: Repository::from("https://example.org/tool"),
                tag: Template::from("v{version}"),
                path: "rust/tool-cli".to_owned(),
                stamp: Some(Stamp {
                    files: vec!["Cargo.toml".to_owned(), "Cargo.lock".to_owned()],
                    placeholder: Placeholder::from("0.0.0-dev"),
                }),
            },
            Target::from(RISCV64),
            Vec::new(),
        );
        let built = steps(&job, Path::new("/k"), Path::new("/s"), &host()).unwrap();
        let clone = PathBuf::from("/s/src/github-a-tool/1.2.3");
        let [
            Step::Clear(ref cleared),
            Step::Run(ref cloned),
            Step::Stamp {
                ref files,
                ref placeholder,
                version: ref stamped,
            },
            Step::Run(ref installed),
        ] = built[..]
        else {
            panic!("clear, clone, stamp and install: {built:?}");
        };
        assert_eq!(cleared, &clone);
        assert_eq!(
            cloned.line(),
            "git clone --quiet --depth 1 --branch v1.2.3 https://example.org/tool /s/src/github-a-tool/1.2.3"
        );
        assert_eq!(files, &[clone.join("Cargo.toml"), clone.join("Cargo.lock")]);
        assert_eq!(
            (placeholder, stamped),
            (&Placeholder::from("0.0.0-dev"), &Version::from("1.2.3"))
        );
        assert_eq!(
            installed.line(),
            "cargo install --locked --target riscv64gc-unknown-linux-gnu --root /k --path /s/src/github-a-tool/1.2.3/rust/tool-cli"
        );
    }

    #[test]
    fn a_go_package_clones_and_builds_with_its_stamp()
    {
        let job = job(
            Recipe::Go {
                repository: Repository::from("https://example.org/tool"),
                tag: Template::from("v{version}"),
                package: "./cmd/tool".to_owned(),
                binary: "tool".to_owned(),
                ldflags: Some(Template::from(
                    "-X example.org/tool/build.Version=v{version}",
                )),
            },
            Target::from(RISCV64),
            Vec::new(),
        );
        let built = steps(&job, Path::new("/k"), Path::new("/s"), &host()).unwrap();
        let [Step::Clear(_), Step::Run(_), Step::Run(ref go)] = built[..]
        else {
            panic!("clear, clone and build: {built:?}");
        };
        let expected = Run {
            program: "go".to_owned(),
            args: vec![
                "build".to_owned(),
                "-trimpath".to_owned(),
                "-ldflags".to_owned(),
                "-X example.org/tool/build.Version=v1.2.3".to_owned(),
                "-o".to_owned(),
                "/k/bin/tool".to_owned(),
                "./cmd/tool".to_owned(),
            ],
            env: vec![
                ("GOOS".to_owned(), "linux".to_owned()),
                ("GOARCH".to_owned(), "riscv64".to_owned()),
                ("CGO_ENABLED".to_owned(), "0".to_owned()),
            ],
            cwd: Some(PathBuf::from("/s/src/github-a-tool/1.2.3")),
        };
        assert_eq!(go, &expected);
    }

    #[test]
    fn a_missing_program_and_an_unknown_architecture_are_refused()
    {
        let crate_job = job(
            Recipe::Crate {
                name: "tool".to_owned(),
                features: Vec::new(),
                default_features: None,
            },
            Target::from(RISCV64),
            vec![ProgramName::from("ninja")],
        );
        assert_eq!(
            steps(&crate_job, Path::new("/k"), Path::new("/s"), &host()),
            Err(HostToolsError::Host {
                message: "names no path of the program `ninja`".to_owned(),
            })
        );
        let go_job = job(
            Recipe::Go {
                repository: Repository::from("https://example.org/tool"),
                tag: Template::from("v{version}"),
                package: ".".to_owned(),
                binary: "tool".to_owned(),
                ldflags: None,
            },
            Target::from("s390x-unknown-linux-gnu"),
            Vec::new(),
        );
        assert!(matches!(
            steps(&go_job, Path::new("/k"), Path::new("/s"), &host()),
            Err(HostToolsError::Recipe { .. })
        ));
    }
}
