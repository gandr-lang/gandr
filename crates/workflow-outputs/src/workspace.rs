//! The packages of the workspace that build a package: the package and each
//! workspace package that it depends on, through its normal and its build
//! dependencies.

use alloc::collections::BTreeSet;
use std::path::Path;
use std::process::Command;

use anodized::spec;
use serde_json::Value;

/// The packages of the workspace at `root`, as `cargo metadata --no-deps
/// --format-version 1 --locked` gives them, by the cargo that `CARGO` names
/// or by `cargo`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// One line when cargo cannot run or writes no JSON.
#[inline]
pub fn metadata(root: &Path) -> Result<Value, String>
{
    let output = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
        .args(["metadata", "--no-deps", "--format-version", "1", "--locked"])
        .current_dir(root)
        .output()
        .map_err(|error| format!("cargo metadata: {error}"))?;
    serde_json::from_slice(&output.stdout).map_err(|error| format!("cargo metadata: {error}"))
}

/// The directories below `crates/` of `package` and of each workspace
/// package that it depends on, in name order.
///
/// The packages are read from the output of `cargo metadata --no-deps
/// --format-version 1`. A development dependency does not build the package,
/// so it is not in the closure.
///
/// # Specification
/// - ensures: the directories are in name order, each one time.
///
/// # Adequacy
/// - hypothesis: L3 — a package, its dependency on a second package, the
///   dependency of the second on a third, and a development dependency on a
///   fourth give the first three.
/// - witness: `workspace::tests::the_closure_follows_normal_dependencies_alone`
#[spec(ensures: |ret| ret.is_sorted())]
#[inline]
#[must_use]
pub fn closure(
    metadata: &Value,
    package: &str,
) -> Vec<String>
{
    let packages: Vec<&Value> = metadata["packages"]
        .as_array()
        .map_or_else(Vec::new, |packages| packages.iter().collect());
    let directory = |found: &Value| {
        found["manifest_path"]
            .as_str()
            .and_then(|manifest| manifest.rsplit('/').nth(1))
            .map(str::to_owned)
    };
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut directories: BTreeSet<String> = BTreeSet::new();
    let mut pending = vec![package.to_owned()];
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(&found) = packages.iter().find(|found| found["name"] == name.as_str())
        else {
            continue;
        };
        if let Some(directory) = directory(found) {
            let _inserted = directories.insert(directory);
        }
        for dependency in found["dependencies"].as_array().into_iter().flatten() {
            if dependency["path"].is_string()
                && dependency["kind"].as_str() != Some("dev")
                && let Some(name) = dependency["name"].as_str()
            {
                pending.push(name.to_owned());
            }
        }
    }
    directories.into_iter().collect()
}

/// The directories below `crates/` of `package`, of each workspace package
/// that a test of `package` depends on, and of the closure of each one, in
/// name order.
///
/// A test of `package` builds with its development dependencies, so each one
/// is in this closure. A development dependency of another package does not
/// build the test, so it is not.
///
/// # Specification
/// - ensures: the directories are in name order, each one time, and they hold
///   the [`closure`] of `package`.
///
/// # Adequacy
/// - hypothesis: L3 — a package, its dependency on a second package, the
///   dependency of the second on a third, a development dependency on a fourth,
///   and a development dependency of the second on a fifth give the first four.
/// - witness: `workspace::tests::the_test_closure_holds_the_development_dependencies_of_the_package`
#[spec(ensures: |ret| ret.is_sorted())]
#[inline]
#[must_use]
pub fn test_closure(
    metadata: &Value,
    package: &str,
) -> Vec<String>
{
    let mut directories: BTreeSet<String> = closure(metadata, package).into_iter().collect();
    let found = metadata["packages"]
        .as_array()
        .into_iter()
        .flatten()
        .find(|found| found["name"] == package);
    let development = found
        .and_then(|found| found["dependencies"].as_array())
        .into_iter()
        .flatten()
        .filter(|dependency| {
            dependency["path"].is_string() && dependency["kind"].as_str() == Some("dev")
        })
        .filter_map(|dependency| dependency["name"].as_str());
    for name in development {
        directories.extend(closure(metadata, name));
    }
    directories.into_iter().collect()
}

#[cfg(test)]
mod tests
{
    use serde_json::json;

    use super::closure;
    use super::test_closure;

    /// A package, its dependency on a second package, the dependency of the
    /// second on a third, and a development dependency on a fourth give the
    /// directories of the first three.
    #[test]
    fn the_closure_follows_normal_dependencies_alone()
    {
        let metadata = json!({"packages": [
            {"name": "a", "manifest_path": "/r/crates/dir-a/Cargo.toml", "dependencies": [
                {"name": "b", "path": "/r/crates/dir-b", "kind": null},
                {"name": "d", "path": "/r/crates/dir-d", "kind": "dev"},
                {"name": "serde", "kind": null}
            ]},
            {"name": "b", "manifest_path": "/r/crates/dir-b/Cargo.toml", "dependencies": [
                {"name": "c", "path": "/r/crates/dir-c", "kind": "build"}
            ]},
            {"name": "c", "manifest_path": "/r/crates/dir-c/Cargo.toml", "dependencies": []},
            {"name": "d", "manifest_path": "/r/crates/dir-d/Cargo.toml", "dependencies": []}
        ]});
        assert_eq!(closure(&metadata, "a"), ["dir-a", "dir-b", "dir-c"]);
    }

    /// A package, its dependency on a second package, the dependency of the
    /// second on a third, a development dependency on a fourth, and a
    /// development dependency of the second on a fifth give the directories
    /// of the first four.
    #[test]
    fn the_test_closure_holds_the_development_dependencies_of_the_package()
    {
        let metadata = json!({"packages": [
            {"name": "a", "manifest_path": "/r/crates/dir-a/Cargo.toml", "dependencies": [
                {"name": "b", "path": "/r/crates/dir-b", "kind": null},
                {"name": "d", "path": "/r/crates/dir-d", "kind": "dev"},
                {"name": "serde", "kind": "dev"}
            ]},
            {"name": "b", "manifest_path": "/r/crates/dir-b/Cargo.toml", "dependencies": [
                {"name": "c", "path": "/r/crates/dir-c", "kind": "build"},
                {"name": "e", "path": "/r/crates/dir-e", "kind": "dev"}
            ]},
            {"name": "c", "manifest_path": "/r/crates/dir-c/Cargo.toml", "dependencies": []},
            {"name": "d", "manifest_path": "/r/crates/dir-d/Cargo.toml", "dependencies": []},
            {"name": "e", "manifest_path": "/r/crates/dir-e/Cargo.toml", "dependencies": []}
        ]});
        assert_eq!(test_closure(&metadata, "a"), [
            "dir-a", "dir-b", "dir-c", "dir-d"
        ]);
    }
}
