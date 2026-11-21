//! The refusals of a build of host tools, each naming what it refused.

use core::fmt;
use std::path::PathBuf;

/// Why a tool could not be planned or built.
///
/// # Specification
/// - provides: one variant per refusal; each carries what it refused and the
///   detail, so the message points at what must change. A refusal of a build
///   leaves no key: the partial directory of the build is removed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostToolsError
{
    /// A file or a directory could not be read, written, locked or renamed.
    Io
    {
        /// The path.
        path: PathBuf,
        /// The error the operating system gave.
        message: String,
    },
    /// A file is not the TOML its reader takes.
    Toml
    {
        /// The file.
        path: PathBuf,
        /// The parser's message.
        message: String,
    },
    /// `mise.lock` locks no version for a tool that the table builds.
    Unlocked
    {
        /// The tool's key in `mise.toml`.
        key: String,
    },
    /// A recipe lacks a field that its way of building needs.
    Recipe
    {
        /// The tool's key in `mise.toml`.
        key: String,
        /// What the recipe lacks.
        message: String,
    },
    /// The host's configuration lacks a fact that a build needs.
    Host
    {
        /// What the configuration lacks.
        message: String,
    },
    /// A command of a build could not start or exited with a failure.
    Command
    {
        /// The tool's key in `mise.toml`.
        key: String,
        /// The command line.
        command: String,
        /// The exit status or the error of the start.
        message: String,
    },
    /// Standard output could not be written.
    Output
    {
        /// The error the operating system gave.
        message: String,
    },
    /// mise's listing of a checkout's tools is not the JSON that the check
    /// reads.
    Listing
    {
        /// The error of the reader.
        message: String,
    },
    /// A text states no release of LLVM as `major.minor.patch`.
    Release
    {
        /// What states the release: the pin, a command or a file.
        source: String,
        /// The text that stands in place of the release.
        text: String,
    },
    /// The pinned LLVM and the LLVM of rustc differ in their major release.
    Major
    {
        /// The release of the pin.
        pin: String,
        /// The release of rustc's LLVM.
        rustc: String,
    },
    /// The tree that the host holds states another release than the pin.
    Tree
    {
        /// The file of the tree that states its release.
        path: PathBuf,
        /// The release of the pin.
        pin: String,
        /// The release of the tree.
        tree: String,
    },
    /// mise holds no install of a tool that the host takes.
    Uninstalled
    {
        /// The tool's key in `mise.toml`.
        key: String,
        /// The pinned version.
        version: String,
    },
}

impl fmt::Display for HostToolsError
{
    /// Describes the refusal and names what it refused.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line naming the variant's subject and its detail.
    /// - provides: the line that the binary prints for a failed tool or a
    ///   refused run.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant's line names its subject and its
    ///   detail; a dropped field or a swapped variant changes the asserted
    ///   line.
    /// - witness: `error::tests::every_refusal_names_its_subject`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Io {
                ref path,
                ref message,
            } => write!(f, "{}: {message}", path.display()),
            Self::Toml {
                ref path,
                ref message,
            } => write!(f, "{}: not the TOML it takes: {message}", path.display()),
            Self::Unlocked { ref key } => write!(f, "{key}: mise.lock locks no version of it"),
            Self::Recipe {
                ref key,
                ref message,
            } => write!(f, "{key}: the recipe {message}"),
            Self::Host { ref message } => write!(f, "the host's configuration {message}"),
            Self::Command {
                ref key,
                ref command,
                ref message,
            } => write!(f, "{key}: `{command}` {message}"),
            Self::Output { ref message } => write!(f, "standard output: {message}"),
            Self::Listing { ref message } => {
                write!(
                    f,
                    "mise's listing of the tools is not the JSON it takes: {message}"
                )
            },
            Self::Release {
                ref source,
                ref text,
            } => write!(
                f,
                "{source} states no release of LLVM as major.minor.patch: `{text}`"
            ),
            Self::Major { ref pin, ref rustc } => write!(
                f,
                "the pin holds LLVM {pin}, and rustc holds LLVM {rustc}: a cross-language link needs one major release"
            ),
            Self::Tree {
                ref path,
                ref pin,
                ref tree,
            } => write!(
                f,
                "{}: the tree states LLVM {tree}, and the pin is LLVM {pin}",
                path.display()
            ),
            Self::Uninstalled {
                ref key,
                ref version,
            } => write!(
                f,
                "{key}: mise holds no install of {version}, and `mise install` installs it"
            ),
        }
    }
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use super::HostToolsError;

    #[test]
    fn every_refusal_names_its_subject()
    {
        let cases = [
            (
                HostToolsError::Io {
                    path: PathBuf::from("keys/a"),
                    message: "denied".to_owned(),
                },
                "keys/a: denied",
            ),
            (
                HostToolsError::Toml {
                    path: PathBuf::from("mise.lock"),
                    message: "bad".to_owned(),
                },
                "mise.lock: not the TOML it takes: bad",
            ),
            (
                HostToolsError::Unlocked {
                    key: "github:a/b".to_owned(),
                },
                "github:a/b: mise.lock locks no version of it",
            ),
            (
                HostToolsError::Recipe {
                    key: "github:a/b".to_owned(),
                    message: "lacks `crate`".to_owned(),
                },
                "github:a/b: the recipe lacks `crate`",
            ),
            (
                HostToolsError::Host {
                    message: "names no linker".to_owned(),
                },
                "the host's configuration names no linker",
            ),
            (
                HostToolsError::Command {
                    key: "github:a/b".to_owned(),
                    command: "cargo install".to_owned(),
                    message: "exits with 101".to_owned(),
                },
                "github:a/b: `cargo install` exits with 101",
            ),
            (
                HostToolsError::Output {
                    message: "closed".to_owned(),
                },
                "standard output: closed",
            ),
            (
                HostToolsError::Listing {
                    message: "expected a map".to_owned(),
                },
                "mise's listing of the tools is not the JSON it takes: expected a map",
            ),
            (
                HostToolsError::Release {
                    source: "`rustc -vV`".to_owned(),
                    text: "23.1.x".to_owned(),
                },
                "`rustc -vV` states no release of LLVM as major.minor.patch: `23.1.x`",
            ),
            (
                HostToolsError::Major {
                    pin: "22.1.8".to_owned(),
                    rustc: "23.1.1".to_owned(),
                },
                "the pin holds LLVM 22.1.8, and rustc holds LLVM 23.1.1: a cross-language link needs one major release",
            ),
            (
                HostToolsError::Tree {
                    path: PathBuf::from("tree/lib/cmake/llvm/LLVMConfigVersion.cmake"),
                    pin: "23.1.6".to_owned(),
                    tree: "23.1.5".to_owned(),
                },
                "tree/lib/cmake/llvm/LLVMConfigVersion.cmake: the tree states LLVM 23.1.5, and the pin is LLVM 23.1.6",
            ),
            (
                HostToolsError::Uninstalled {
                    key: "github:a/b".to_owned(),
                    version: "1.0.0".to_owned(),
                },
                "github:a/b: mise holds no install of 1.0.0, and `mise install` installs it",
            ),
        ];
        for (error, line) in cases {
            assert_eq!(error.to_string(), line);
        }
    }
}
