//! The crate is closed in its tier: its normal and build dependencies reach
//! exactly the four theory crates it reads, so no edge climbs to the core or
//! surface tiers, and the convexity sweep, which a caller supplies, is not a
//! dependency.
//!
//! The rule is checked against the resolver's own answer rather than the
//! manifest's text, so an edge arriving transitively fails it too.

use alloc::collections::BTreeSet;
use std::process::Command;

/// This crate's package name.
const PACKAGE: &str = "gandr-theory-computads";

/// The prefix every package of the workspace carries.
const WORKSPACE_PREFIX: &str = "gandr-";

/// The workspace crates the crate reads, and no others.
const READS: [&str; 4] = [
    "gandr-theory-cell-complexes",
    "gandr-theory-coherent-resolutions",
    "gandr-theory-deep-inference",
    "gandr-theory-levitation",
];

#[test]
fn the_crate_reaches_only_the_theory_crates_it_reads()
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
    let reached: BTreeSet<&str> = packages
        .filter(|name| name.starts_with(WORKSPACE_PREFIX))
        .collect();
    assert_eq!(
        READS.into_iter().collect::<BTreeSet<_>>(),
        reached,
        "the crate reaches exactly the theory crates it reads through a normal or build edge"
    );
}
