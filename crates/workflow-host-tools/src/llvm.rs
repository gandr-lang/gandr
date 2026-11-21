//! The pinned LLVM toolchain against the LLVM of the pinned rustc and against
//! the tree that a host holds.
//!
//! A reader of LLVM in the tree links the libraries of one release, and a link
//! with cross-language LTO reads the bitcode of rustc's LLVM beside them. That
//! link needs one major release on both sides. So the major release of the pin
//! is the major release of rustc's LLVM, and the tree that a host holds is the
//! release of the pin.

use core::fmt;
use std::path::Path;

use anodized::spec;

use crate::error::HostToolsError;
use crate::input::Input;
use crate::names::Version;

/// The key of the toolchain in `mise.toml`.
pub const KEY: &str = "github:gandr-lang/toolchains-llvm";

/// The file of the tree that states its release, below the root of the tree.
pub const VERSION_FILE: &str = "lib/cmake/llvm/LLVMConfigVersion.cmake";

/// The line of `rustc -vV` that states the release of its LLVM.
const RUSTC_LINE: &str = "LLVM version: ";

/// The command that states the release in [`VERSION_FILE`].
const TREE_LINE: &str = "set(PACKAGE_VERSION \"";

/// A release of LLVM, `major.minor.patch`.
///
/// # Specification
/// - provides: the three numbers of a release, compared whole or by the major
///   release alone.
/// - executable: none — a plain record; [`Release::of_pin`],
///   [`Release::of_rustc`] and [`Release::of_tree`] fill it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Release
{
    /// The major release.
    major: u32,
    /// The minor release.
    minor: u32,
    /// The patch release.
    patch: u32,
}

impl Release
{
    /// The release that `text` spells as `major.minor.patch`, or `None` for
    /// another text.
    ///
    /// # Specification
    /// trivial.
    fn parse(text: &str) -> Option<Self>
    {
        let mut parts = text.split('.').map(|part| {
            if part.is_empty() || !part.bytes().all(|byte| byte.is_ascii_digit()) {
                return None;
            }
            part.parse::<u32>().ok()
        });
        let release = Self {
            major: parts.next()??,
            minor: parts.next()??,
            patch: parts.next()??,
        };
        parts.next().is_none().then_some(release)
    }

    /// The release of LLVM that the pin `version` holds: the text before its
    /// `+`, as `23.1.6` of `23.1.6+rev0`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the release that the text of `version` before its first `+`
    ///   spells, or the whole text when it holds no `+`.
    /// - provides: the release of the pin.
    /// - fails: [`HostToolsError::Release`] when that text is not
    ///   `major.minor.patch`.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pin with a revision and a pin of two numbers each
    ///   give their result.
    /// - witness: `llvm::tests::a_pin_reads_the_release_before_its_revision`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Release { .. })))]
    #[inline]
    pub fn of_pin(version: &Version) -> Result<Self, HostToolsError>
    {
        let text: &str = version.as_ref();
        let release = text.split_once('+').map_or(text, |(release, _)| release);
        Self::parse(release).ok_or_else(|| HostToolsError::Release {
            source: format!("the pin {KEY}"),
            text: text.to_owned(),
        })
    }

    /// The release of LLVM that rustc holds, from the text of `rustc -vV`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the release that the line `LLVM version: <release>` of `text`
    ///   spells.
    /// - provides: the release of rustc's LLVM.
    /// - fails: [`HostToolsError::Release`] when `text` holds no such line, or
    ///   its release is not `major.minor.patch`.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the text of a nightly rustc gives its release, and a
    ///   text with no line of LLVM is refused by name.
    /// - witness: `llvm::tests::rustc_states_the_release_of_its_llvm`
    /// - witness: `llvm::tests::a_text_with_no_release_is_refused_by_its_source`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Release { .. })))]
    #[inline]
    pub fn of_rustc(text: &str) -> Result<Self, HostToolsError>
    {
        let line = text.lines().find_map(|line| line.strip_prefix(RUSTC_LINE));
        line.map(str::trim)
            .and_then(Self::parse)
            .ok_or_else(|| HostToolsError::Release {
                source: "`rustc -vV`".to_owned(),
                text: line.unwrap_or_default().trim().to_owned(),
            })
    }

    /// The release of LLVM that a tree states in [`VERSION_FILE`], whose text
    /// `input` holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the release of the first line `set(PACKAGE_VERSION
    ///   "<release>")` of the text.
    /// - provides: the release of the tree that a host holds.
    /// - fails: [`HostToolsError::Release`], with the file's path, when the
    ///   text holds no such line, or its release is not `major.minor.patch`.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the file that LLVM 23.1.6 installs gives its release.
    /// - witness: `llvm::tests::a_tree_states_its_release_in_its_cmake_package`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Release { .. })))]
    #[inline]
    pub fn of_tree(input: &Input) -> Result<Self, HostToolsError>
    {
        let release = input.text.lines().find_map(|line| {
            line.trim()
                .strip_prefix(TREE_LINE)
                .and_then(|rest| rest.strip_suffix("\")"))
        });
        release
            .and_then(Self::parse)
            .ok_or_else(|| HostToolsError::Release {
                source: input.path.display().to_string(),
                text: release.unwrap_or_default().to_owned(),
            })
    }
}

impl fmt::Display for Release
{
    /// Writes `major.minor.patch`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// Whether the release of the pin and the release of rustc's LLVM share their
/// major release.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok` when the major releases of `pin` and `rustc` are one.
/// - provides: the refusal of a pin that a cross-language link cannot read.
/// - fails: [`HostToolsError::Major`], with both releases, when the major
///   releases differ.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — two patch releases of one major release agree, and a pin
///   of another major release is refused with both releases.
/// - witness: `llvm::tests::one_major_release_agrees_and_another_is_refused`
/// - witness: `tests::cli::a_pin_of_another_major_release_is_refused_by_both_releases`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Major { .. })))]
#[inline]
pub fn agree(
    pin: Release,
    rustc: Release,
) -> Result<(), HostToolsError>
{
    if pin.major == rustc.major {
        Ok(())
    }
    else {
        Err(HostToolsError::Major {
            pin: pin.to_string(),
            rustc: rustc.to_string(),
        })
    }
}

/// Whether the tree at `root` states the release `pin`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the release of the tree when it is `pin`.
/// - provides: the refusal of a tree of another release than the pin.
/// - fails: [`HostToolsError::Io`] when [`VERSION_FILE`] of `root` cannot be
///   read; every refusal of [`Release::of_tree`]; [`HostToolsError::Tree`],
///   with both releases, when the tree states another release.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a tree of the pin's release is kept, and a tree of
///   another patch release is refused with both releases.
/// - witness: `tests::cli::the_check_passes_at_the_pin`
/// - witness: `tests::cli::a_tree_of_another_release_is_refused_by_both_releases`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |tree| *tree == pin))]
#[inline]
pub fn holds(
    root: &Path,
    pin: Release,
) -> Result<Release, HostToolsError>
{
    let input = Input::read(&root.join(VERSION_FILE))?;
    let tree = Release::of_tree(&input)?;
    if tree == pin {
        Ok(tree)
    }
    else {
        Err(HostToolsError::Tree {
            path: input.path,
            pin: pin.to_string(),
            tree: tree.to_string(),
        })
    }
}

#[cfg(test)]
mod tests
{
    use super::Release;
    use super::agree;
    use crate::error::HostToolsError;
    use crate::input::Input;
    use crate::names::Version;

    /// The text of `rustc -vV` of the tree's pinned nightly.
    const RUSTC: &str = "rustc 1.101.0-nightly (21b707e3f 2026-09-30)\nbinary: rustc\ncommit-hash: 21b707e3f97e0b522ebd2f277a862339625ad83f\ncommit-date: 2026-09-30\nhost: aarch64-apple-darwin\nrelease: 1.101.0-nightly\nLLVM version: 23.1.1\n";

    /// The head of [`super::VERSION_FILE`] as LLVM 23.1.6 installs it.
    const TREE: &str = "set(PACKAGE_VERSION \"23.1.6\")\n\n# LLVM is API-compatible only with matching major.minor versions\n# and patch versions not less than that requested.\nif(\"23.1\" VERSION_EQUAL\n    \"${PACKAGE_FIND_VERSION_MAJOR}.${PACKAGE_FIND_VERSION_MINOR}\"\n   AND NOT \"6\" VERSION_LESS \"${PACKAGE_FIND_VERSION_PATCH}\")\n  set(PACKAGE_VERSION_COMPATIBLE 1)\nendif()\n";

    #[test]
    fn a_pin_reads_the_release_before_its_revision()
    {
        assert_eq!(
            Release::of_pin(&Version::from("23.1.6+rev0"))
                .unwrap()
                .to_string(),
            "23.1.6"
        );
        assert_eq!(
            Release::of_pin(&Version::from("23.1+rev0")),
            Err(HostToolsError::Release {
                source: "the pin github:gandr-lang/toolchains-llvm".to_owned(),
                text: "23.1+rev0".to_owned(),
            })
        );
    }

    #[test]
    fn rustc_states_the_release_of_its_llvm()
    {
        assert_eq!(Release::of_rustc(RUSTC).unwrap().to_string(), "23.1.1");
    }

    #[test]
    fn a_text_with_no_release_is_refused_by_its_source()
    {
        assert_eq!(
            Release::of_rustc("rustc 1.101.0-nightly\nLLVM version: 23.1.x\n"),
            Err(HostToolsError::Release {
                source: "`rustc -vV`".to_owned(),
                text: "23.1.x".to_owned(),
            })
        );
        assert_eq!(
            Release::of_tree(&Input {
                path: "tree/lib/cmake/llvm/LLVMConfigVersion.cmake".into(),
                text: "set(PACKAGE_VERSION_COMPATIBLE 1)\n".to_owned(),
            }),
            Err(HostToolsError::Release {
                source: "tree/lib/cmake/llvm/LLVMConfigVersion.cmake".to_owned(),
                text: String::new(),
            })
        );
    }

    #[test]
    fn a_tree_states_its_release_in_its_cmake_package()
    {
        let input = Input {
            path: "tree/lib/cmake/llvm/LLVMConfigVersion.cmake".into(),
            text: TREE.to_owned(),
        };
        assert_eq!(Release::of_tree(&input).unwrap().to_string(), "23.1.6");
    }

    #[test]
    fn one_major_release_agrees_and_another_is_refused()
    {
        let pin = Release::of_pin(&Version::from("23.1.6+rev0")).unwrap();
        assert_eq!(agree(pin, Release::of_rustc(RUSTC).unwrap()), Ok(()));
        let older = Release::of_pin(&Version::from("22.1.8+rev0")).unwrap();
        assert_eq!(
            agree(older, Release::of_rustc(RUSTC).unwrap()),
            Err(HostToolsError::Major {
                pin: "22.1.8".to_owned(),
                rustc: "23.1.1".to_owned(),
            })
        );
    }
}
