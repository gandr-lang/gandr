//! The crate is closed in its tier: its normal and build dependencies reach
//! no other crate of the workspace but the path orders it decides termination
//! by, whose types its signatures never name, so every wrapper in its
//! signatures is its own.
//!
//! The rule is checked against the resolver's own answer rather than the
//! manifest's text, so an edge arriving transitively fails it too.

use std::process::Command;

/// This crate's package name.
const PACKAGE: &str = "gandr-theory-levitation";

/// The prefix every package of the workspace carries.
const WORKSPACE_PREFIX: &str = "gandr-";

/// The one workspace crate the crate depends on.
const PATH_ORDERS: &str = "gandr-theory-path-orders";

#[test]
fn the_crate_depends_on_no_workspace_crate_but_the_path_orders()
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
        .filter(|name| name.starts_with(WORKSPACE_PREFIX) && *name != PATH_ORDERS)
        .collect();
    assert!(
        workspace_dependencies.is_empty(),
        "the crate reaches no workspace crate but the path orders through a normal or build edge, found: {}",
        workspace_dependencies.join(", ")
    );
}
