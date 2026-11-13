//! The tree's table of the tools to build for a target, and how each one
//! builds: `.config/host-tools/builds.toml`.

use anodized::spec;
use serde::Deserialize;

use crate::error::HostToolsError;
use crate::input::Input;
use crate::names::Placeholder;
use crate::names::ProgramName;
use crate::names::Repository;
use crate::names::Target;
use crate::names::Template;
use crate::names::ToolKey;

/// The tools that the table builds, in the table's order.
///
/// # Specification
/// - provides: each tool of the table once, in the order the table states.
/// - executable: none — a plain record; [`Builds::read`] fills it.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
pub struct Builds
{
    /// The tools, in the table's order.
    #[serde(default)]
    pub tool: Vec<Tool>,
}

/// One tool of the table.
///
/// # Specification
/// - provides: the tool's key in `mise.toml`, the targets it builds for, how it
///   builds, and the programs its build needs.
/// - executable: none — a plain record.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct Tool
{
    /// The tool's key in `mise.toml`, or `mise` for mise itself.
    pub key: ToolKey,
    /// The target triples it builds for.
    pub targets: Vec<Target>,
    /// How it builds.
    #[serde(flatten)]
    pub recipe: Recipe,
    /// The programs its build runs, which the host's configuration supplies.
    #[serde(default)]
    pub needs: Vec<ProgramName>,
}

/// One way to build a tool.
///
/// # Specification
/// - provides: the three ways the table states, each with its fields. In `tag`,
///   `ldflags` and the stamp, `{version}` stands for the version.
/// - executable: none — a plain record.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(tag = "build", rename_all = "lowercase")]
pub enum Recipe
{
    /// `cargo install` of a crate of crates.io at the version.
    Crate
    {
        /// The crate's name.
        #[serde(rename = "crate")]
        name: String,
        /// The features to turn on.
        #[serde(default)]
        features: Vec<String>,
        /// `Some(false)` turns the crate's default features off; with no
        /// value, they stay on.
        #[serde(default, rename = "default-features")]
        default_features: Option<bool>,
    },
    /// A clone of a repository at a tag, then `cargo install --path` of the
    /// package at a path of the clone.
    Cargo
    {
        /// The repository.
        repository: Repository,
        /// The tag.
        tag: Template,
        /// The package's directory in the clone.
        path: String,
        /// The version written over the placeholder of the clone's files.
        stamp: Option<Stamp>,
    },
    /// A clone of a repository at a tag, then `go build` of a package.
    Go
    {
        /// The repository.
        repository: Repository,
        /// The tag.
        tag: Template,
        /// The package, relative to the clone.
        package: String,
        /// The binary's name.
        binary: String,
        /// The linker flags, which stamp the version.
        ldflags: Option<Template>,
    },
}

/// The version written over a placeholder in some files of a clone, as the
/// tool's release does before its build.
///
/// # Specification
/// - provides: the files, relative to the clone, and the placeholder that each
///   holds in place of the version.
/// - executable: none — a plain record.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct Stamp
{
    /// The files, relative to the clone.
    pub files: Vec<String>,
    /// The placeholder each file holds in place of the version.
    pub placeholder: Placeholder,
}

impl Builds
{
    /// The table that `input` states.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the tools of `input` in its order.
    /// - provides: the one reading of the table.
    /// - fails: [`HostToolsError::Toml`] when `input` is not a table of tools
    ///   with a known way to build each.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the tree's table reads whole, and a tool of an
    ///   unknown way to build is refused with the file's path.
    /// - witness: `recipe::tests::the_trees_table_reads_each_tool`
    /// - witness: `recipe::tests::an_unknown_way_to_build_is_refused`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Toml { .. })))]
    #[inline]
    pub fn read(input: &Input) -> Result<Self, HostToolsError>
    {
        input.parse()
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use super::Builds;
    use super::Recipe;
    use crate::error::HostToolsError;
    use crate::input::Input;

    #[test]
    fn the_trees_table_reads_each_tool()
    {
        let path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.config/host-tools/builds.toml");
        let builds = Builds::read(&Input::read(&path).unwrap()).unwrap();
        let keys: Vec<String> = builds
            .tool
            .iter()
            .map(|tool| tool.key.to_string())
            .collect();
        assert_eq!(keys, [
            "github:cli/cli",
            "github:numtide/treefmt",
            "github:crate-ci/typos",
            "github:j178/prek",
            "github:max-sixty/worktrunk",
            "github:orhun/git-cliff",
            "github:rvben/rumdl",
            "github:zizmorcore/zizmor",
            "github:aubepkg/aube",
            "github:tombi-toml/tombi",
            "mise",
        ]);
        let mise = builds.tool.last().unwrap();
        assert_eq!(mise.recipe, Recipe::Crate {
            name: "mise".to_owned(),
            features: vec![
                "rustls".to_owned(),
                "vfox/vendored-lua".to_owned(),
                "self_update".to_owned()
            ],
            default_features: Some(false),
        });
        let typos = builds
            .tool
            .iter()
            .find(|tool| tool.key == *"github:crate-ci/typos")
            .unwrap();
        assert!(matches!(typos.recipe, Recipe::Crate {
            default_features: None,
            ..
        }));
    }

    #[test]
    fn an_unknown_way_to_build_is_refused()
    {
        let refused = Builds::read(&Input {
            path: "builds.toml".into(),
            text: "[[tool]]\nkey = \"a\"\ntargets = []\nbuild = \"make\"\n".to_owned(),
        });
        assert!(
            matches!(refused, Err(HostToolsError::Toml { ref path, .. }) if path == Path::new("builds.toml"))
        );
    }
}
