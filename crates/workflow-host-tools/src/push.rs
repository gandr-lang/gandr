//! A key copied to each host that receives its target, and mise brought to
//! the pin on each host.
//!
//! A key goes into the receiver's mise install directory as it is: the key
//! holds the layout of a mise install. The key of mise goes to the path of
//! the receiver's mise. A receiver with no such path, and the builder, take
//! `mise self-update` to the pin. A marker under `<into>/.pushed/<host>/`
//! records each push that ends, so a key goes to a host once.

use std::path::Path;

use anodized::spec;

use crate::build::Runner;
use crate::build::key;
use crate::error::HostToolsError;
use crate::host::Receiver;
use crate::jobs::Job;
use crate::jobs::MISE;
use crate::names::ToolKey;
use crate::names::Version;
use crate::steps::Run;

/// The data directory of a receiver's mise, relative to its home, when its
/// configuration names none.
pub const MISE_DATA: &str = ".local/share/mise";

/// The directory of the markers of the builder's own update, beside the
/// markers of each receiver.
const BUILDER: &str = "builder";

/// What a push did for a key or an update.
///
/// # Specification
/// - provides: whether a marker recorded the push already, whether the push
///   ran, or whether the receiver takes nothing of the key.
/// - executable: none — a plain record.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Pushed
{
    /// A marker recorded the push, and nothing ran.
    Standing,
    /// The push ran, and its marker now stands.
    Pushed,
    /// The receiver takes nothing of the key: it is the key of mise, and the
    /// receiver names no path of its mise.
    Skipped,
}

/// Copy the key of `job` under `into` to `receiver`, unless a marker records
/// it.
///
/// # Specification
/// - requires: the key of `job` stands under `into`.
/// - ensures: for a tool, `rsync -a --delete --mkpath` of the key into
///   `<data>/installs/<install name>/<version>/` on the receiver; for mise, an
///   `rsync -a` of the key's `bin/mise` to the receiver's mise path, which
///   rsync replaces whole. Then the marker
///   `<into>/.pushed/<host>/<target>.<install name>.<version>` stands, and the
///   result is [`Pushed::Pushed`]. A marker that stands runs nothing and gives
///   [`Pushed::Standing`]. The key of mise to a receiver with no mise path runs
///   nothing and gives [`Pushed::Skipped`]. A refusal leaves no marker.
/// - provides: the one copy of a key to a host.
/// - fails: every refusal of `runner`; [`HostToolsError::Io`] when the marker
///   cannot be written.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a tool's key and mise's key each give their command line
///   and their marker; a second push runs nothing; mise's key to a receiver
///   with no mise path runs nothing; a refused copy leaves no marker.
/// - witness: `push::tests::a_key_goes_into_the_install_directory_once`
/// - witness: `push::tests::the_key_of_mise_replaces_the_receivers_mise`
/// - witness: `push::tests::a_refused_copy_leaves_no_marker`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Io { .. } | HostToolsError::Command { .. })))]
#[inline]
pub fn push<R>(
    job: &Job,
    into: &Path,
    receiver: &Receiver,
    runner: &mut R,
) -> Result<Pushed, HostToolsError>
where
    R: Runner,
{
    let marker = into.join(".pushed").join(&receiver.host).join(format!(
        "{}.{}.{}",
        job.target, job.install_name, job.version
    ));
    if marker.is_file() {
        return Ok(Pushed::Standing);
    }
    let source = key(into, job);
    let args = if job.key == *MISE {
        let Some(mise) = receiver.mise.as_ref()
        else {
            return Ok(Pushed::Skipped);
        };
        vec![
            "-a".to_owned(),
            source.join("bin").join("mise").display().to_string(),
            format!("{}:{mise}", receiver.host),
        ]
    }
    else {
        let data = receiver
            .data
            .as_ref()
            .map_or_else(|| MISE_DATA.to_owned(), ToString::to_string);
        vec![
            "-a".to_owned(),
            "--delete".to_owned(),
            "--mkpath".to_owned(),
            format!("{}/", source.display()),
            format!(
                "{}:{data}/installs/{}/{}/",
                receiver.host, job.install_name, job.version
            ),
        ]
    };
    runner.run(&job.key, &Run {
        program: "rsync".to_owned(),
        args,
        env: Vec::new(),
        cwd: None,
    })?;
    mark(&marker)?;
    Ok(Pushed::Pushed)
}

/// Bring mise to the pin `pin` on `receiver`, or on the builder for `None`,
/// unless a marker records it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `mise self-update --yes --no-plugins <pin>` ran, over ssh on a
///   receiver, and the marker `<into>/.pushed/<host>/mise.<pin>` stands, the
///   host `builder` for the builder; the result is [`Pushed::Pushed`]. A marker
///   that stands runs nothing and gives [`Pushed::Standing`]. A refusal leaves
///   no marker.
/// - provides: the one update of a host's mise to the pin.
/// - fails: every refusal of `runner`; [`HostToolsError::Io`] when the marker
///   cannot be written.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — the builder's update runs locally and a receiver's over
///   ssh, each once.
/// - witness: `push::tests::an_update_runs_once_on_the_builder_and_once_over_ssh`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Io { .. } | HostToolsError::Command { .. })))]
#[inline]
pub fn update<R>(
    receiver: Option<&Receiver>,
    into: &Path,
    pin: &Version,
    runner: &mut R,
) -> Result<Pushed, HostToolsError>
where
    R: Runner,
{
    let host: &Path =
        receiver.map_or_else(|| Path::new(BUILDER), |receiver| receiver.host.as_ref());
    let marker = into.join(".pushed").join(host).join(format!("mise.{pin}"));
    if marker.is_file() {
        return Ok(Pushed::Standing);
    }
    let mut args = Vec::with_capacity(6);
    let program = receiver.map_or("mise", |receiver| {
        args.extend([receiver.host.to_string(), "mise".to_owned()]);
        "ssh"
    });
    args.extend([
        "self-update".to_owned(),
        "--yes".to_owned(),
        "--no-plugins".to_owned(),
        pin.to_string(),
    ]);
    runner.run(&ToolKey::from(MISE), &Run {
        program: program.to_owned(),
        args,
        env: Vec::new(),
        cwd: None,
    })?;
    mark(&marker)?;
    Ok(Pushed::Pushed)
}

/// Write the marker `marker`, with its directories.
///
/// # Specification
/// trivial.
#[inline]
fn mark(marker: &Path) -> Result<(), HostToolsError>
{
    let io = |error: std::io::Error| HostToolsError::Io {
        path: marker.to_path_buf(),
        message: error.to_string(),
    };
    if let Some(parent) = marker.parent() {
        std::fs::create_dir_all(parent).map_err(io)?;
    }
    std::fs::write(marker, "").map_err(io)
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use super::Pushed;
    use super::push;
    use super::update;
    use crate::build::Runner;
    use crate::error::HostToolsError;
    use crate::host::Receiver;
    use crate::jobs::Job;
    use crate::names::RemotePath;
    use crate::names::ToolKey;
    use crate::names::Version;
    use crate::recipe::Recipe;
    use crate::steps::Run;

    /// A runner that records each command line, or refuses each command.
    struct Recording
    {
        /// The command lines it ran.
        ran: Vec<String>,
        /// Whether each command fails.
        fails: bool,
    }

    impl Runner for Recording
    {
        /// Record `run`, then refuse it when the runner fails.
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
                    message: "exits with 255".to_owned(),
                });
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

    /// A job of the tool `key` at 1.2.3 for riscv64.
    ///
    /// # Specification
    /// trivial.
    fn job(key: ToolKey) -> Job
    {
        Job {
            install_name: key.install_name(),
            key,
            version: "1.2.3".into(),
            target: "riscv64gc-unknown-linux-gnu".into(),
            recipe: Recipe::Crate {
                name: "tool".to_owned(),
                features: Vec::new(),
                default_features: None,
            },
            needs: Vec::new(),
        }
    }

    /// The riscv64 receiver `rv`, with its mise at `.cargo/bin/mise` when
    /// `mise` holds.
    ///
    /// # Specification
    /// trivial.
    fn receiver(mise: Option<RemotePath>) -> Receiver
    {
        Receiver {
            host: "rv".into(),
            target: "riscv64gc-unknown-linux-gnu".into(),
            data: None,
            mise,
        }
    }

    #[test]
    fn a_key_goes_into_the_install_directory_once()
    {
        let into = scratch();
        let tool = job("github:a/tool".into());
        let mut runner = Recording {
            ran: Vec::new(),
            fails: false,
        };
        assert_eq!(
            push(&tool, &into, &receiver(None), &mut runner),
            Ok(Pushed::Pushed)
        );
        assert_eq!(
            push(&tool, &into, &receiver(None), &mut runner),
            Ok(Pushed::Standing)
        );
        assert_eq!(runner.ran, [format!(
            "rsync -a --delete --mkpath {}/riscv64gc-unknown-linux-gnu/github-a-tool/1.2.3/ rv:.local/share/mise/installs/github-a-tool/1.2.3/",
            into.display()
        )]);
        assert!(
            into.join(".pushed/rv/riscv64gc-unknown-linux-gnu.github-a-tool.1.2.3")
                .is_file()
        );
        std::fs::remove_dir_all(&into).unwrap();
    }

    #[test]
    fn the_key_of_mise_replaces_the_receivers_mise()
    {
        let into = scratch();
        let mise = job("mise".into());
        let mut runner = Recording {
            ran: Vec::new(),
            fails: false,
        };
        assert_eq!(
            push(&mise, &into, &receiver(None), &mut runner),
            Ok(Pushed::Skipped)
        );
        assert_eq!(
            push(
                &mise,
                &into,
                &receiver(Some(".cargo/bin/mise".into())),
                &mut runner
            ),
            Ok(Pushed::Pushed)
        );
        assert_eq!(runner.ran, [format!(
            "rsync -a {}/riscv64gc-unknown-linux-gnu/mise/1.2.3/bin/mise rv:.cargo/bin/mise",
            into.display()
        )]);
        std::fs::remove_dir_all(&into).unwrap();
    }

    #[test]
    fn a_refused_copy_leaves_no_marker()
    {
        let into = scratch();
        let mut runner = Recording {
            ran: Vec::new(),
            fails: true,
        };
        let refused = push(
            &job("github:a/tool".into()),
            &into,
            &receiver(None),
            &mut runner,
        );
        assert!(matches!(refused, Err(HostToolsError::Command { .. })));
        assert!(!into.join(".pushed").exists());
        std::fs::remove_dir_all(&into).unwrap();
    }

    #[test]
    fn an_update_runs_once_on_the_builder_and_once_over_ssh()
    {
        let into = scratch();
        let pin = Version::from("2026.11.4");
        let mut runner = Recording {
            ran: Vec::new(),
            fails: false,
        };
        assert_eq!(update(None, &into, &pin, &mut runner), Ok(Pushed::Pushed));
        assert_eq!(update(None, &into, &pin, &mut runner), Ok(Pushed::Standing));
        let rv = receiver(None);
        assert_eq!(
            update(Some(&rv), &into, &pin, &mut runner),
            Ok(Pushed::Pushed)
        );
        assert_eq!(
            update(Some(&rv), &into, &pin, &mut runner),
            Ok(Pushed::Standing)
        );
        assert_eq!(runner.ran, [
            "mise self-update --yes --no-plugins 2026.11.4",
            "ssh rv mise self-update --yes --no-plugins 2026.11.4",
        ]);
        std::fs::remove_dir_all(&into).unwrap();
    }
}
