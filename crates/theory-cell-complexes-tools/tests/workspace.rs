//! The crate is test-facing by construction: the resolved workspace reaches it
//! through no normal or build dependency.
//!
//! Cargo admits the edge it forbids, since the tools crate depends only on the
//! substrate and no cycle would refuse a production crate depending on it, so
//! the rule is checked against the resolver's own answer.

use std::process::Command;

/// This crate's package name.
const PACKAGE: &str = "gandr-theory-cell-complexes-tools";

#[test]
fn no_production_crate_links_the_tools_crate()
{
    let output = Command::new(env!("CARGO"))
        .arg("tree")
        .arg("--manifest-path")
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/../../Cargo.toml"))
        .args(["--offline", "--locked", "--workspace", "--invert", PACKAGE])
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
        "cargo resolves the workspace's dependency tree: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let tree = String::from_utf8(output.stdout).expect("cargo prints UTF-8");
    let mut packages = tree
        .lines()
        .filter_map(|line| line.split_whitespace().next());
    assert_eq!(
        Some(PACKAGE),
        packages.next(),
        "the inverted tree is rooted at this crate, so the query found it"
    );
    let dependents: Vec<&str> = packages.filter(|name| *name != PACKAGE).collect();
    assert!(
        dependents.is_empty(),
        "no crate depends on the tools crate outside its dev-dependencies, found: {}",
        dependents.join(", ")
    );
}
