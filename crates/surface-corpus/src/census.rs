//! The census of the rules that the check refuses outside the fragment that
//! the kernel decides: an overlap of second-order rules, an overlap under a
//! condition, a left side that repeats a variable, and a rule of an indexed
//! family.
//!
//! The corpus suite checks that each source is refused as its attribute
//! states, so the census reads the attributes. The record of the pull request
//! that adds this census has, for each block, the form of the overlap and the
//! answer that a unifier gives for it.

use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use std::fs;
use std::path::Path;

/// The refusals that the census holds.
const CODES: [&str; 4] = [
    "RulesOverlapSecondOrder",
    "RulesOverlapCondition",
    "RulesNonLinear",
    "OutOfFragment.Indexed",
];

/// Each source of the corpus with a refusal of [`CODES`], below `corpus/`,
/// with the refusal.
const CENSUS: [(&str, &str); 16] = [
    (
        "ledger/diagnostics/OutOfFragment.Indexed.gandr",
        "OutOfFragment.Indexed",
    ),
    ("ledger/diagnostics/RulesNonLinear.gandr", "RulesNonLinear"),
    (
        "ledger/diagnostics/RulesOverlapCondition.gandr",
        "RulesOverlapCondition",
    ),
    (
        "ledger/diagnostics/RulesOverlapSecondOrder.gandr",
        "RulesOverlapSecondOrder",
    ),
    (
        "pathological/circuit/circuit-repeated-port.gandr",
        "RulesNonLinear",
    ),
    (
        "pathological/data/indexed-family-rule-declined.gandr",
        "OutOfFragment.Indexed",
    ),
    (
        "pathological/desc/atom-occurrence.gandr",
        "RulesOverlapCondition",
    ),
    ("pathological/desc/member-attribute.gandr", "RulesNonLinear"),
    ("pathological/desc/occurrence-count.gandr", "RulesNonLinear"),
    (
        "pathological/desc/relative-monad.gandr",
        "RulesOverlapSecondOrder",
    ),
    ("pathological/desc/rules-nonlinear.gandr", "RulesNonLinear"),
    (
        "pathological/desc/second-order-rules.gandr",
        "RulesOverlapSecondOrder",
    ),
    ("pathological/effects/rows.gandr", "RulesOverlapCondition"),
    ("pathological/effects/state.gandr", "RulesOverlapCondition"),
    (
        "pathological/effects/state.gandr",
        "RulesOverlapSecondOrder",
    ),
    ("surface/circuit-shared-ports.gandr", "RulesNonLinear"),
];

/// Each attribute of a corpus source that states a refusal of [`CODES`], as
/// the source below `root` and the refusal.
///
/// # Specification
/// trivial.
fn stated(root: &Path) -> BTreeSet<(String, String)>
{
    let mut found = BTreeSet::new();
    let mut pending = Vec::from([root.to_path_buf()]);
    while let Some(here) = pending.pop() {
        for entry in fs::read_dir(&here).expect("a corpus directory lists") {
            let path = entry.expect("an entry reads").path();
            if path.is_dir() {
                pending.push(path);
                continue;
            }
            if path
                .extension()
                .is_none_or(|extension| extension != "gandr")
            {
                continue;
            }
            let text = fs::read_to_string(&path).expect("a corpus source reads");
            let below = path
                .strip_prefix(root)
                .expect("a corpus path")
                .to_string_lossy()
                .into_owned();
            for code in CODES {
                if text.contains(&format!("@[refuses(\"{code}\")]")) {
                    let _new = found.insert((below.clone(), String::from(code)));
                }
            }
        }
    }
    found
}

/// The census has each source of the corpus that the check refuses outside
/// the decided fragment, and no other. A source that gains or loses such a
/// refusal changes the census, and the record of its block with it.
#[test]
fn each_refusal_outside_the_decided_fragment_is_in_the_census()
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus");
    let listed: BTreeSet<(String, String)> = CENSUS
        .iter()
        .map(|&(source, code)| (String::from(source), String::from(code)))
        .collect();
    assert_eq!(stated(&root), listed);
}
