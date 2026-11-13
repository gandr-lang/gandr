//! The names that a build reads and writes, each a wrapper of its text.
//!
//! A tool's key, a version, a target triple, an install name, a program's
//! name, a placeholder, a repository and a template of a version.

use core::fmt;
use std::path::Path;

use anodized::spec;
use serde::Deserialize;

/// Declares a wrapper of the text of one name. The table and the
/// configuration state the name as a string, and the build writes it as it is:
/// into a command, into a path, or into a refusal.
macro_rules! name {
    ($(#[$attribute:meta])* $name:ident) => {
        $(#[$attribute])*
        #[repr(transparent)]
        #[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd)]
        #[serde(transparent)]
        pub struct $name(String);

        impl From<&str> for $name
        {
            /// The name of `text`, as written.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(text: &str) -> Self
            {
                Self(text.to_owned())
            }
        }

        impl fmt::Display for $name
        {
            /// Writes the name as it is.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn fmt(
                &self,
                f: &mut fmt::Formatter<'_>,
            ) -> fmt::Result
            {
                f.write_str(&self.0)
            }
        }

        impl PartialEq<str> for $name
        {
            /// Whether the name is `other`.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn eq(
                &self,
                other: &str,
            ) -> bool
            {
                self.0 == other
            }
        }

        impl AsRef<str> for $name
        {
            /// The name's text.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn as_ref(&self) -> &str
            {
                &self.0
            }
        }

        impl AsRef<Path> for $name
        {
            /// The name as a component of a path.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn as_ref(&self) -> &Path
            {
                Path::new(&self.0)
            }
        }
    };
}

name! {
    /// A tool's key in `mise.toml`, as `github:cli/cli`, or `mise` for mise
    /// itself.
    ToolKey
}

name! {
    /// A version of a tool, as `mise.lock` locks it or as the pin states it.
    Version
}

name! {
    /// A target triple, as `riscv64gc-unknown-linux-gnu`.
    Target
}

name! {
    /// The name of a tool's directory in mise's install directory, as
    /// `github-cli-cli`.
    InstallName
}

name! {
    /// The name of a program that a build runs, as `cmake`.
    ProgramName
}

name! {
    /// The text that some files of a clone hold in place of the version, as
    /// `0.0.0-dev`.
    Placeholder
}

name! {
    /// The URL of a git repository.
    Repository
}

name! {
    /// A text in which `{version}` stands for the version: a tag, or the
    /// linker flags of a Go build.
    Template
}

name! {
    /// A host that receives keys, as ssh names it.
    HostName
}

name! {
    /// A path on a receiver, relative to its home directory, as
    /// `.local/share/mise`.
    RemotePath
}

/// Go's name of an architecture that the hosts run.
///
/// # Specification
/// - provides: the architectures of the targets the hosts run, as `GOARCH`
///   names them.
/// - executable: none — a plain enumeration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GoArch
{
    /// `riscv64`.
    Riscv64,
    /// `amd64`.
    Amd64,
    /// `arm64`.
    Arm64,
}

impl fmt::Display for GoArch
{
    /// Writes the architecture as `GOARCH` names it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Riscv64 => "riscv64",
            Self::Amd64 => "amd64",
            Self::Arm64 => "arm64",
        })
    }
}

impl ToolKey
{
    /// The name of the tool's directory in mise's install directory: the key
    /// in kebab case, each `:` and `/` a `-`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the key with each `:` and `/` written `-`, a `-` before each
    ///   capital letter that follows a lower-case letter or a digit, and each
    ///   letter in lower case.
    /// - provides: the name mise gives a tool's directory, so a key of the
    ///   build copies into mise's install directory as it is.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a key of lower-case names, a key with a digit and a
    ///   key with a capitalized owner give mise's names; a dropped `-` or a
    ///   kept capital changes them.
    /// - witness: `names::tests::an_install_name_is_the_key_in_kebab_case`
    #[spec(ensures: |ret| !ret.0.contains(':') && !ret.0.contains('/') && !ret.0.chars().any(char::is_uppercase))]
    #[inline]
    #[must_use]
    pub fn install_name(&self) -> InstallName
    {
        let mut name = String::with_capacity(self.0.len().saturating_add(4));
        let mut before: Option<char> = None;
        for character in self.0.chars() {
            match character {
                ':' | '/' => name.push('-'),
                capital if capital.is_uppercase() => {
                    if before
                        .is_some_and(|earlier| earlier.is_lowercase() || earlier.is_ascii_digit())
                    {
                        name.push('-');
                    }
                    name.extend(capital.to_lowercase());
                },
                other => name.push(other),
            }
            before = Some(character);
        }
        InstallName(name)
    }
}

impl Target
{
    /// Go's architecture of the target, for the architectures the hosts run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn go_arch(&self) -> Option<GoArch>
    {
        match self.0.split('-').next() {
            Some("riscv64gc" | "riscv64") => Some(GoArch::Riscv64),
            Some("x86_64") => Some(GoArch::Amd64),
            Some("aarch64") => Some(GoArch::Arm64),
            Some(_) | None => None,
        }
    }
}

impl Template
{
    /// The template with each `{version}` written `version`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "`{version}` is the table's placeholder, which `replace` writes over, not an argument of a format"
    )]
    pub fn fill(
        &self,
        version: &Version,
    ) -> String
    {
        self.0.replace("{version}", &version.0)
    }
}

#[cfg(test)]
mod tests
{
    use super::Target;
    use super::Template;
    use super::ToolKey;
    use super::Version;

    #[test]
    fn an_install_name_is_the_key_in_kebab_case()
    {
        let named = |key: &str| ToolKey::from(key).install_name().to_string();
        assert_eq!(named("github:crate-ci/typos"), "github-crate-ci-typos");
        assert_eq!(named("github:j178/prek"), "github-j178-prek");
        assert_eq!(
            named("github:WebAssembly/wasi-sdk"),
            "github-web-assembly-wasi-sdk"
        );
    }

    #[test]
    fn a_template_fills_each_version_and_a_target_names_its_go_architecture()
    {
        let template = Template::from("-X a.Version=v{version} -X b.Version={version}");
        assert_eq!(
            template.fill(&Version::from("1.2.3")),
            "-X a.Version=v1.2.3 -X b.Version=1.2.3"
        );
        let arch = |target: &str| Target::from(target).go_arch().map(|arch| arch.to_string());
        assert_eq!(
            arch("riscv64gc-unknown-linux-gnu").as_deref(),
            Some("riscv64")
        );
        assert_eq!(arch("x86_64-unknown-linux-gnu").as_deref(), Some("amd64"));
        assert_eq!(arch("aarch64-unknown-linux-gnu").as_deref(), Some("arm64"));
        assert_eq!(arch("s390x-unknown-linux-gnu"), None);
    }
}
