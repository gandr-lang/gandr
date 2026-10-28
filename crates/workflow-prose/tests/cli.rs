//! The findings, the ledger and the exit codes, observed by spawning the
//! binary over a scratch root with the fake interpreter of `tests/fakes`,
//! which prints the parse each case writes to `FAKE_PYTHON_OUTPUT`.

use std::process::Command;

/// No arguments beyond the interpreter and the root.
const NO_ARGS: [&str; 0] = [];

/// The parse of one passage whose one sentence, "The kernel reduced the
/// term.", is in the past tense.
const PAST: &str = r#"[[[["The","the","DET","DT","det",1,0],["kernel","kernel","NOUN","NN","nsubj",2,4],["reduced","reduce","VERB","VBD","ROOT",2,11],["the","the","DET","DT","det",4,19],["term","term","NOUN","NN","dobj",2,23],[".",".","PUNCT",".","punct",2,27]]]]"#;

/// The parse of the same passage in the present tense.
const PRESENT: &str = r#"[[[["The","the","DET","DT","det",1,0],["kernel","kernel","NOUN","NN","nsubj",2,4],["reduces","reduce","VERB","VBZ","ROOT",2,11],["the","the","DET","DT","det",4,19],["term","term","NOUN","NN","dobj",2,23],[".",".","PUNCT",".","punct",2,27]]]]"#;

/// A scratch root for the case `$name` holding one corpus source of the
/// sentence `$sentence`, an empty glossary, the ledger `$ledger`, and the
/// parse `$parse` for the fake to print.
macro_rules! scratch {
    ($name:literal, $sentence:literal, $ledger:expr, $parse:expr) => {{
        let root =
            std::env::temp_dir().join(format!("workflow-prose-{}-{}", std::process::id(), $name));
        if root.exists() {
            std::fs::remove_dir_all(&root).unwrap();
        }
        for dir in ["corpus", "crates/surface-render-terminal/tests/golden"] {
            std::fs::create_dir_all(root.join(dir)).unwrap();
        }
        std::fs::write(
            root.join("corpus/a.gandr"),
            concat!("/// ", $sentence, "\ndef x = 1 ;\n"),
        )
        .unwrap();
        std::fs::write(root.join("corpus/glossary.toml"), "[words]\n").unwrap();
        std::fs::write(root.join("corpus/prose.ledger"), $ledger).unwrap();
        std::fs::write(root.join("parse.json"), $parse).unwrap();
        root
    }};
}

/// Runs the binary over `$root` with `$args`, the fake in `$mode`.
macro_rules! run {
    ($root:expr, $args:expr, $mode:expr) => {{
        let root: &std::path::Path = &$root;
        Command::new(env!("CARGO_BIN_EXE_prose"))
            .arg("--python")
            .arg(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fakes/python"))
            .arg("--root")
            .arg(root)
            .args($args)
            .env("FAKE_PYTHON_OUTPUT", root.join("parse.json"))
            .env("FAKE_PYTHON_MODE", $mode)
            .output()
            .unwrap()
    }};
}

#[test]
fn a_new_finding_is_refused_with_its_fix()
{
    let root = scratch!("new", "The kernel reduced the term.", "", PAST);
    let output = run!(root, NO_ARGS, "");
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert_eq!(output.status.code(), Some(1_i32));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "corpus/a.gandr:1: Tense: \"The kernel reduced the term.\" — state it in the present \
         tense\n"
    );
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_body_is_refused_on_its_findings()
{
    let root = scratch!("body", "The kernel reduced the term.", "", PAST);
    let body = root.join("body.md");
    std::fs::write(
        &body,
        "## Observed\n\nThe kernel reduced the term.\n\n| a | b |\n",
    )
    .unwrap();
    let clean = root.join("clean.md");
    std::fs::write(&clean, "The kernel reduces the term.\n").unwrap();
    let passage = |parse: &str| {
        parse
            .get(1 .. parse.len().saturating_sub(1))
            .unwrap()
            .to_owned()
    };
    std::fs::write(
        root.join("parse.json"),
        format!("[{},{}]", passage(PAST), passage(PRESENT)),
    )
    .unwrap();
    let flag = std::ffi::OsStr::new("--body");
    let output = run!(root, [flag, body.as_os_str(), clean.as_os_str()], "");
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert_eq!(output.status.code(), Some(1_i32));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!(
            "{}:3: Tense: \"The kernel reduced the term.\" — state it in the present tense\n",
            body.display()
        )
    );
    std::fs::write(root.join("parse.json"), PRESENT).unwrap();
    let args = [flag, clean.as_os_str()];
    let output = run!(root, args, "");
    assert_eq!(
        output.status.code(),
        Some(0_i32),
        "the corpus ledger is not read: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "prose: 1 file(s), no body rule broken\n"
    );
    let output = run!(
        root,
        [std::ffi::OsStr::new("--write"), args[0], args[1]],
        ""
    );
    assert_eq!(output.status.code(), Some(2_i32), "a body keeps no ledger");
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_stale_line_is_refused_and_written_away()
{
    let root = scratch!(
        "stale",
        "The kernel reduces the term.",
        "# header\ncorpus/a.gandr Tense 0123456789abcdef\n",
        PRESENT
    );
    let output = run!(root, NO_ARGS, "");
    assert_eq!(output.status.code(), Some(1_i32));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "corpus/prose.ledger: stale line `corpus/a.gandr Tense 0123456789abcdef`: no finding \
         matches it; run `mise run check:prose --write`\n"
    );
    let written = run!(root, ["--write"], "");
    assert!(written.status.success());
    assert_eq!(
        String::from_utf8_lossy(&written.stdout),
        "prose: wrote 0 ledger lines\n"
    );
    let ledger = std::fs::read_to_string(root.join("corpus/prose.ledger")).unwrap();
    assert!(ledger.lines().all(|line| line.starts_with('#')), "{ledger}");
    let again = run!(root, NO_ARGS, "");
    assert!(again.status.success());
    assert_eq!(
        String::from_utf8_lossy(&again.stdout),
        "prose: 0 findings, every one in the ledger\n"
    );
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_written_finding_passes_until_its_sentence_is_fixed()
{
    let root = scratch!("written", "The kernel reduced the term.", "", PAST);
    assert!(run!(root, ["--write"], "").status.success());
    let ledger = std::fs::read_to_string(root.join("corpus/prose.ledger")).unwrap();
    assert_eq!(
        ledger.lines().filter(|line| !line.starts_with('#')).count(),
        1,
        "{ledger}"
    );
    assert!(run!(root, NO_ARGS, "").status.success());
    std::fs::write(root.join("parse.json"), PRESENT).unwrap();
    let fixed = run!(root, NO_ARGS, "");
    assert_eq!(fixed.status.code(), Some(1_i32));
    assert!(
        String::from_utf8_lossy(&fixed.stdout)
            .starts_with("corpus/prose.ledger: stale line `corpus/a.gandr Tense "),
        "{}",
        String::from_utf8_lossy(&fixed.stdout)
    );
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_failing_parse_is_reported_with_its_message()
{
    let root = scratch!("fail", "The kernel reduces the term.", "", PRESENT);
    let output = run!(root, NO_ARGS, "fail");
    assert_eq!(output.status.code(), Some(2_i32));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.starts_with("prose: `") && stderr.ends_with("No module named 'spacy'\n"),
        "{stderr}"
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "");
    std::fs::remove_dir_all(&root).unwrap();
}
