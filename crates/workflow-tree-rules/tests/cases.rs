//! The cases of each rule, read against the patterns of the tree.

use std::path::Path;

use gandr_workflow_tree_rules::Rules;

/// The cases of the rule `residue`: a line or a path, and whether it is
/// residue.
const RESIDUE: &str = include_str!("../../../.config/merge-residue/cases.json");

/// The cases of the rule `paths`: a line, and whether the rule refuses it.
const PATHS: &str = include_str!("../../../.config/local-paths/cases.json");

/// The rules of the tree.
///
/// # Specification
/// trivial.
fn rules() -> Rules
{
    Rules::read(&Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")).unwrap()
}

/// The text of a field of a case.
///
/// # Specification
/// trivial.
fn field<'case>(
    case: &'case serde_json::Value,
    key: &str,
) -> Option<&'case str>
{
    case.get(key).and_then(serde_json::Value::as_str)
}

#[test]
fn each_case_of_residue_reads_as_recorded()
{
    let rules = rules();
    let cases: Vec<serde_json::Value> = serde_json::from_str(RESIDUE).unwrap();
    assert!(cases.len() > 20, "{}", cases.len());
    for case in &cases {
        let name = field(case, "name").unwrap();
        let want = case
            .get("residue")
            .and_then(serde_json::Value::as_bool)
            .unwrap();
        let got = match (field(case, "path"), field(case, "line")) {
            (Some(path), None) => rules.residue_name(path),
            (None, Some(line)) => rules.residue_line(line),
            (Some(_), Some(_)) | (None, None) => panic!("{name}: a case has a path or a line"),
        };
        assert_eq!(got, want, "{name}");
    }
}

#[test]
fn each_case_of_paths_reads_as_recorded()
{
    let rules = rules();
    let cases: Vec<serde_json::Value> = serde_json::from_str(PATHS).unwrap();
    assert!(cases.len() > 10, "{}", cases.len());
    for case in &cases {
        let name = field(case, "name").unwrap();
        let line = field(case, "line").unwrap();
        let want = case
            .get("refused")
            .and_then(serde_json::Value::as_bool)
            .unwrap();
        assert_eq!(rules.home_path(line), want, "{name}: {line}");
    }
}

#[test]
fn the_list_of_readmes_holds_each_readme_alone()
{
    let rules = rules();
    for (path, want) in [
        ("README.md", true),
        ("CHANGELOG.md", true),
        ("crates/workflow-tree-rules/README.md", true),
        ("corpus/sketch/effects/handlers.gandr.md", true),
        (".config/issues/templates/unit.md", true),
        ("docs/guide.md", false),
        ("crates/CHANGELOG.md", false),
        ("crates/workflow-tree-rules/docs/README.md", false),
        ("corpus/sketch/effects/deep/handlers.gandr.md", false),
        ("corpus/sketch/effects/handlers.md", false),
    ] {
        assert_eq!(rules.readme(path), want, "{path}");
    }
}
