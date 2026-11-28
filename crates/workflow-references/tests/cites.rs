//! The citations of a source, against the recorded cases of
//! `.config/references/cases.json`, which the awk reader of the mise task
//! reads too.

use gandr_workflow_references::cites::citations;

/// The path of the source of a line: its last column, less its line number.
fn source(line: &str) -> &str
{
    let location = line.rsplit('\t').next().unwrap_or(line);
    location
        .rsplit_once(':')
        .map_or(location, |(path, number)| {
            if number.bytes().all(|byte| byte.is_ascii_digit()) {
                path
            }
            else {
                location
            }
        })
}

/// Each case of `.config/references/cases.json` gives its recorded lines,
/// the lines of each source in their order. The JSON reader orders the
/// sources of a case by path, so both sides are grouped by source.
#[test]
fn each_case_gives_its_lines()
{
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../.config/references/cases.json"
    );
    let text = std::fs::read_to_string(path).expect("the cases read");
    let cases: serde_json::Value = serde_json::from_str(&text).expect("the cases are JSON");
    let cases = cases.as_array().expect("the cases are a list");
    assert!(!cases.is_empty(), "the file has cases");
    for case in cases {
        let name = case["name"].as_str().expect("a case has a name");
        let files = case["files"].as_object().expect("a case has files");
        let mut lines = Vec::new();
        for (path, text) in files {
            let text = text.as_str().expect("a file is text");
            lines.extend(citations(path, text).iter().map(ToString::to_string));
        }
        let mut expected = case["output"]
            .as_array()
            .expect("a case has its output")
            .iter()
            .map(|line| line.as_str().expect("a line is text").to_owned())
            .collect::<Vec<_>>();
        expected.sort_by(|left, right| source(left).cmp(source(right)));
        lines.sort_by(|left, right| source(left).cmp(source(right)));
        assert_eq!(expected, lines, "{name}");
    }
}
