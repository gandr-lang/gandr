//! The crate is closed in its tier: its normal and build dependencies reach
//! no other crate of the workspace, so every wrapper in its signatures is its
//! own and no dependent can reach a crate through it that its own manifest
//! never named.
//!
//! The rule is checked against the resolver's own answer rather than the
//! manifest's text, so an edge arriving transitively fails it too.

use std::process::Command;

/// This crate's package name.
const PACKAGE: &str = "gandr-theory-levitation";

/// The prefix every package of the workspace carries.
const WORKSPACE_PREFIX: &str = "gandr-";

#[test]
fn the_crate_depends_on_no_other_workspace_crate()
{
    let output = Command::new(env!("CARGO"))
        .arg("tree")
        .arg("--manifest-path")
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/../../Cargo.toml"))
        .args(["--offline", "--locked", "--package", PACKAGE])
        .args([
            "--edges",
            "normal,build",
            "--prefix",
            "none",
            "--format",
            "{p}",
        ])
        .output()
        .expect("cargo runs");
    assert!(
        output.status.success(),
        "cargo resolves the crate's dependency tree: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let tree = String::from_utf8(output.stdout).expect("cargo prints UTF-8");
    let mut packages = tree
        .lines()
        .filter_map(|line| line.split_whitespace().next());
    assert_eq!(
        Some(PACKAGE),
        packages.next(),
        "the tree is rooted at this crate, so the query found it"
    );
    let workspace_dependencies: Vec<&str> = packages
        .filter(|name| name.starts_with(WORKSPACE_PREFIX))
        .collect();
    assert!(
        workspace_dependencies.is_empty(),
        "the crate reaches no other workspace crate through a normal or build edge, found: {}",
        workspace_dependencies.join(", ")
    );
}
