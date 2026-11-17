//! The jobs of a target: one for each tool that the table builds for it.

use anodized::spec;

use crate::error::HostToolsError;
use crate::lock::Lock;
use crate::names::InstallName;
use crate::names::ProgramName;
use crate::names::Target;
use crate::names::ToolKey;
use crate::names::Version;
use crate::recipe::Builds;
use crate::recipe::Recipe;

/// The key of mise itself in the table, whose version is the pin.
pub const MISE: &str = "mise";

/// One tool to build for one target.
///
/// # Specification
/// - provides: the tool's key, its version, the target, the name of its
///   directory in mise's install directory, how it builds and the programs its
///   build needs.
/// - executable: none — a plain record; [`plan`] fills it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Job
{
    /// The tool's key in `mise.toml`.
    pub key: ToolKey,
    /// The version to build.
    pub version: Version,
    /// The target triple.
    pub target: Target,
    /// The name of the tool's directory in mise's install directory.
    pub install_name: InstallName,
    /// How it builds.
    pub recipe: Recipe,
    /// The programs its build runs.
    pub needs: Vec<ProgramName>,
}

/// The jobs that build each tool of `builds` for `target`, in the table's
/// order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one job for each tool whose targets hold `target`, at the version
///   `lock` locks for its key, or at `mise_version` for mise itself.
/// - provides: the one choice of what a target's build builds.
/// - fails: [`HostToolsError::Unlocked`] when `lock` locks no version for a
///   tool of the target.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a table of a tool of the target, a tool of another target
///   and mise gives two jobs, mise's at the pin; a tool that the lock leaves
///   out is refused by its key.
/// - witness: `jobs::tests::a_targets_jobs_take_the_locked_versions_and_the_pin`
/// - witness: `jobs::tests::a_tool_the_lock_leaves_out_is_refused`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|jobs| jobs.len() <= builds.tool.len()) || matches!(ret, Err(HostToolsError::Unlocked { .. })))]
#[inline]
pub fn plan(
    builds: &Builds,
    lock: &Lock,
    mise_version: &Version,
    target: &Target,
) -> Result<Vec<Job>, HostToolsError>
{
    builds
        .tool
        .iter()
        .filter(|tool| tool.targets.contains(target))
        .map(|tool| {
            let version = if tool.key == *MISE {
                mise_version
            }
            else {
                lock.version(&tool.key)
                    .ok_or_else(|| HostToolsError::Unlocked {
                        key: tool.key.to_string(),
                    })?
            };
            Ok(Job {
                key: tool.key.clone(),
                version: version.clone(),
                target: target.clone(),
                install_name: tool.key.install_name(),
                recipe: tool.recipe.clone(),
                needs: tool.needs.clone(),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests
{
    use super::plan;
    use crate::error::HostToolsError;
    use crate::input::Input;
    use crate::lock::Lock;
    use crate::names::Target;
    use crate::names::Version;
    use crate::recipe::Builds;

    /// A table of a tool of riscv64, a tool of aarch64 and mise.
    const TABLE: &str = "\
[[tool]]
key = \"github:a/one\"
targets = [\"riscv64gc-unknown-linux-gnu\"]
build = \"crate\"
crate = \"one\"

[[tool]]
key = \"github:a/two\"
targets = [\"aarch64-unknown-linux-gnu\"]
build = \"crate\"
crate = \"two\"

[[tool]]
key = \"mise\"
targets = [\"riscv64gc-unknown-linux-gnu\"]
build = \"crate\"
crate = \"mise\"
";

    /// The table above.
    ///
    /// # Specification
    /// trivial.
    fn builds() -> Builds
    {
        Builds::read(&Input {
            path: "builds.toml".into(),
            text: TABLE.to_owned(),
        })
        .unwrap()
    }

    #[test]
    fn a_targets_jobs_take_the_locked_versions_and_the_pin()
    {
        let lock = Lock::read(&Input {
            path: "mise.lock".into(),
            text: "[[tools.\"github:a/one\"]]\nversion = \"1.2.3\"\n\n[[tools.\"github:a/two\"]]\nversion = \"4.5.6\"\n".to_owned(),
        })
        .unwrap();
        let riscv64 = Target::from("riscv64gc-unknown-linux-gnu");
        let jobs = plan(&builds(), &lock, &Version::from("2026.11.4"), &riscv64).unwrap();
        let read: Vec<[String; 3]> = jobs
            .iter()
            .map(|job| {
                [
                    job.key.to_string(),
                    job.version.to_string(),
                    job.install_name.to_string(),
                ]
            })
            .collect();
        assert_eq!(read, [["github:a/one", "1.2.3", "github-a-one"], [
            "mise",
            "2026.11.4",
            "mise"
        ]]);
        assert!(jobs.iter().all(|job| job.target == riscv64));
    }

    #[test]
    fn a_tool_the_lock_leaves_out_is_refused()
    {
        let refused = plan(
            &builds(),
            &Lock::default(),
            &Version::from("2026.11.4"),
            &Target::from("riscv64gc-unknown-linux-gnu"),
        );
        assert_eq!(
            refused,
            Err(HostToolsError::Unlocked {
                key: "github:a/one".to_owned(),
            })
        );
    }
}
