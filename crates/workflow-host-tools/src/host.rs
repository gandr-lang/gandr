//! The builder's configuration: the linker and the C tools of each target it
//! builds for, and the programs a build needs. The configuration is the
//! host's, never the tree's.

extern crate alloc;

use alloc::collections::BTreeMap;
use std::path::Path;

use anodized::spec;
use serde::Deserialize;

use crate::error::HostToolsError;
use crate::input::Input;
use crate::names::ProgramName;
use crate::names::Target;

/// The builder's configuration, `$XDG_CONFIG_HOME/gandr/host-tools.toml`.
///
/// # Specification
/// - provides: for each target, its linker and C tools; for each program a
///   build needs, its path.
/// - executable: none — a plain record; [`Host::read`] fills it.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
pub struct Host
{
    /// The linker and the C tools of each target, by its triple.
    #[serde(default)]
    pub target: BTreeMap<Target, TargetTools>,
    /// The path of each program a build needs, by its name.
    #[serde(default)]
    pub programs: BTreeMap<ProgramName, String>,
}

/// The linker and the C tools of one target.
///
/// # Specification
/// - provides: the linker cargo links with, and the C compiler, the C++
///   compiler and the archiver a build script runs, as cargo's `cc` reads them.
/// - executable: none — a plain record.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct TargetTools
{
    /// The linker.
    pub linker: String,
    /// The C compiler.
    pub cc: Option<String>,
    /// The C++ compiler.
    pub cxx: Option<String>,
    /// The archiver.
    pub ar: Option<String>,
}

impl Host
{
    /// The configuration that `input` states.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the targets and the programs of `input`.
    /// - provides: the one reading of the configuration.
    /// - fails: [`HostToolsError::Toml`] when `input` is not such a
    ///   configuration.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a configuration of one target and one program reads
    ///   both, and a target with no linker is refused.
    /// - witness: `host::tests::a_target_and_a_program_read`
    /// - witness: `host::tests::a_target_with_no_linker_is_refused`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Toml { .. })))]
    #[inline]
    pub fn read(input: &Input) -> Result<Self, HostToolsError>
    {
        input.parse()
    }

    /// The linker and the C tools of `target`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the configuration's tools of `target`.
    /// - provides: the one lookup of a target's tools.
    /// - fails: [`HostToolsError::Host`] when the configuration names no tools
    ///   for `target`.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Host::read`].
    /// - witness: `host::tests::a_target_and_a_program_read`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Host { .. })))]
    #[inline]
    pub fn tools(
        &self,
        target: &Target,
    ) -> Result<&TargetTools, HostToolsError>
    {
        self.target.get(target).ok_or_else(|| HostToolsError::Host {
            message: format!("names no linker for {target}"),
        })
    }

    /// The path of the program `name`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the configuration's path of `name`.
    /// - provides: the one lookup of a program a build needs.
    /// - fails: [`HostToolsError::Host`] when the configuration names no path
    ///   for `name`.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Host::read`].
    /// - witness: `host::tests::a_target_and_a_program_read`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Host { .. })))]
    #[inline]
    pub fn program(
        &self,
        name: &ProgramName,
    ) -> Result<&Path, HostToolsError>
    {
        self.programs
            .get(name)
            .map(Path::new)
            .ok_or_else(|| HostToolsError::Host {
                message: format!("names no path of the program `{name}`"),
            })
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use super::Host;
    use crate::error::HostToolsError;
    use crate::input::Input;
    use crate::names::ProgramName;
    use crate::names::Target;

    #[test]
    fn a_target_and_a_program_read()
    {
        let host = Host::read(&Input {
            path: "host-tools.toml".into(),
            text: "[target.riscv64gc-unknown-linux-gnu]\nlinker = \"riscv64-linux-gnu-gcc\"\ncc = \"riscv64-linux-gnu-gcc\"\n\n[programs]\ncmake = \"/opt/cmake/bin/cmake\"\n".to_owned(),
        })
        .unwrap();
        let tools = host
            .tools(&Target::from("riscv64gc-unknown-linux-gnu"))
            .unwrap();
        assert_eq!(tools.linker, "riscv64-linux-gnu-gcc");
        assert_eq!(tools.cc.as_deref(), Some("riscv64-linux-gnu-gcc"));
        assert_eq!(tools.ar, None);
        assert_eq!(
            host.program(&ProgramName::from("cmake")).unwrap(),
            Path::new("/opt/cmake/bin/cmake")
        );
        assert_eq!(
            host.tools(&Target::from("aarch64-unknown-linux-gnu"))
                .unwrap_err()
                .to_string(),
            "the host's configuration names no linker for aarch64-unknown-linux-gnu"
        );
        assert_eq!(
            host.program(&ProgramName::from("go"))
                .unwrap_err()
                .to_string(),
            "the host's configuration names no path of the program `go`"
        );
    }

    #[test]
    fn a_target_with_no_linker_is_refused()
    {
        let refused = Host::read(&Input {
            path: "host-tools.toml".into(),
            text: "[target.riscv64gc-unknown-linux-gnu]\ncc = \"gcc\"\n".to_owned(),
        });
        assert!(matches!(refused, Err(HostToolsError::Toml { .. })));
    }
}
