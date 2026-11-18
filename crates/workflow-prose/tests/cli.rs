//! The findings, the ledger and the exit codes, observed by spawning the
//! binary over a scratch root with the fake interpreter of `tests/fakes`,
//! which prints the parse each case writes to `FAKE_PYTHON_OUTPUT`: one line
//! per passage, as the parse script prints it.

use std::process::Command;

/// No arguments beyond the interpreter and the root.
const NO_ARGS: [&str; 0] = [];

/// The parse of one passage whose one sentence, "The kernel reduced the
/// term.", is in the past tense.
const PAST: &str = r#"[[["The","the","DET","DT","det",1,0],["kernel","kernel","NOUN","NN","nsubj",2,4],["reduced","reduce","VERB","VBD","ROOT",2,11],["the","the","DET","DT","det",4,19],["term","term","NOUN","NN","dobj",2,23],[".",".","PUNCT",".","punct",2,27]]]"#;

/// The parse of the same passage in the present tense.
const PRESENT: &str = r#"[[["The","the","DET","DT","det",1,0],["kernel","kernel","NOUN","NN","nsubj",2,4],["reduces","reduce","VERB","VBZ","ROOT",2,11],["the","the","DET","DT","det",4,19],["term","term","NOUN","NN","dobj",2,23],[".",".","PUNCT",".","punct",2,27]]]"#;

/// A scratch root for the case `$name`, a git work tree tracking one corpus
/// source of the sentence `$sentence`, an empty glossary, the ledger
/// `$ledger`, and the parse `$parse` for the fake to print.
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
        for arguments in [&["init", "--quiet"][..], &["add", "corpus/a.gandr"][..]] {
            let status = Command::new("git")
                .arg("-C")
                .arg(&root)
                .args(arguments)
                .status()
                .unwrap();
            assert!(status.success(), "git {arguments:?}");
        }
        root
    }};
}

/// Runs the binary over `$root` with `$args`, the fake in `$mode`; the fake
/// saves the passages it is fed to `input.json`.
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
            .env("FAKE_PYTHON_INPUT", root.join("input.json"))
            .env("FAKE_PYTHON_MODE", $mode)
            .output()
            .unwrap()
    }};
}

/// Runs git under `$root` with `$args`, as a fixed author with no signing
/// and no hooks.
macro_rules! git {
    ($root:expr, $args:expr) => {{
        let status = Command::new("git")
            .arg("-C")
            .arg(&$root)
            .args([
                "-c",
                "user.name=prose",
                "-c",
                "user.email=prose@example.invalid",
                "-c",
                "commit.gpgsign=false",
                "-c",
                "core.hooksPath=/dev/null",
            ])
            .args($args)
            .status()
            .unwrap();
        assert!(status.success(), "git {:?}", $args);
    }};
}

/// Writes `$text` to `$path` under `$root`, its directories made.
macro_rules! put {
    ($root:expr, $path:expr, $text:expr) => {{
        let path = $root.join($path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, $text).unwrap();
    }};
}

/// The parses `$parse`, each of one passage, printed together as the fake
/// prints them: one line each.
macro_rules! joined {
    ($($parse:expr),+) => {
        [$($parse),+].join("\n")
    };
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
        "corpus/a.gandr:1: STE-3.2: \"The kernel reduced the term.\" — state it in the present \
         tense\ncorpus/a.gandr:1: STE-6.4: \"the head is not four paragraphs\" — open the source on \
         four paragraphs: what, why, how and references, with a `Limits:` paragraph after the how \
         paragraph when the source has limits\nprose: parsed 1 passage(s) of 5 word(s) afresh, of \
         1 read; 0 parse(s) not kept in the cache\n"
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
    std::fs::write(root.join("parse.json"), joined!(PAST, PRESENT)).unwrap();
    let flag = std::ffi::OsStr::new("--body");
    let output = run!(root, [flag, body.as_os_str(), clean.as_os_str()], "");
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert_eq!(output.status.code(), Some(1_i32));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!(
            "{}:3: STE-3.2: \"The kernel reduced the term.\" — state it in the present tense\n",
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
fn a_stale_line_is_refused_and_written_away_5007()
{
    let root = scratch!(
        "stale",
        "The kernel reduces the term.",
        "# header\ncorpus/a.gandr STE-3.2 0123456789abcdef\n",
        PRESENT
    );
    let output = run!(root, NO_ARGS, "");
    assert_eq!(output.status.code(), Some(1_i32));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "corpus/a.gandr:1: STE-6.4: \"the head is not four paragraphs\" — open the source on four \
         paragraphs: what, why, how and references, with a `Limits:` paragraph after the how \
         paragraph when the source has limits\ncorpus/prose.ledger: stale line \
         `corpus/a.gandr STE-3.2 0123456789abcdef`: no finding matches it; run `mise run \
         check:prose --write`\nprose: parsed 1 passage(s) of 5 word(s) afresh, of 1 read; 0 \
         parse(s) not kept in the cache\n"
    );
    let written = run!(root, ["--write"], "");
    assert!(written.status.success());
    assert_eq!(
        String::from_utf8_lossy(&written.stdout),
        "prose: wrote 1 ledger lines\n"
    );
    let ledger = std::fs::read_to_string(root.join("corpus/prose.ledger")).unwrap();
    let lines: Vec<_> = ledger
        .lines()
        .filter(|line| !line.starts_with('#'))
        .collect();
    assert_eq!(lines.len(), 1, "{ledger}");
    assert!(lines[0].starts_with("corpus/a.gandr STE-6.4 "), "{ledger}");
    let again = run!(root, NO_ARGS, "");
    assert!(again.status.success());
    assert_eq!(
        String::from_utf8_lossy(&again.stdout),
        "prose: parsed 1 passage(s) of 5 word(s) afresh, of 1 read; 0 parse(s) not kept in the \
         cache\nprose: 1 findings, every one in the ledger\n"
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
        2,
        "{ledger}"
    );
    assert!(run!(root, NO_ARGS, "").status.success());
    std::fs::write(root.join("parse.json"), PRESENT).unwrap();
    let fixed = run!(root, NO_ARGS, "");
    assert_eq!(fixed.status.code(), Some(1_i32));
    assert!(
        String::from_utf8_lossy(&fixed.stdout)
            .starts_with("corpus/prose.ledger: stale line `corpus/a.gandr STE-3.2 "),
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

#[test]
fn a_second_run_reads_every_parse_from_the_cache()
{
    let root = scratch!("cache", "The kernel reduces the term.", "", PRESENT);
    put!(
        root,
        "corpus/b.gandr",
        "/// The kernel reduces the term.\ndef y = 1 ;\n"
    );
    put!(root, "crates/workflow-prose/parse.py", "the parse script");
    git!(root, ["add", "corpus/b.gandr"]);
    let cache = root.join("cache");
    let flags = |model: &str, extra: &[&str]| {
        let mut flags = vec![
            std::ffi::OsString::from("--cache"),
            cache.clone().into_os_string(),
            "--model".into(),
            model.into(),
        ];
        flags.extend(extra.iter().map(std::ffi::OsString::from));
        flags
    };
    assert!(
        run!(root, flags("fake 1", &["--write"]), "")
            .status
            .success()
    );
    assert_eq!(
        std::fs::read_to_string(root.join("input.json")).unwrap(),
        r#"["The kernel reduces the term."]"#,
        "a text two passages share parses once"
    );
    std::fs::remove_file(root.join("input.json")).unwrap();
    let cached = run!(root, flags("fake 1", &[]), "fail");
    assert_eq!(String::from_utf8_lossy(&cached.stderr), "");
    assert_eq!(cached.status.code(), Some(0_i32));
    assert_eq!(
        String::from_utf8_lossy(&cached.stdout),
        "prose: parsed 0 passage(s) of 0 word(s) afresh, of 2 read; 0 parse(s) not kept in the \
         cache\nprose: 2 findings, every one in the ledger\n"
    );
    assert!(
        !root.join("input.json").exists(),
        "a cached run starts no interpreter"
    );
    assert_eq!(
        run!(root, flags("fake 2", &[]), "fail").status.code(),
        Some(2_i32),
        "another model's cache misses"
    );
    let entry = blake3::hash(b"The kernel reduces the term.").to_hex();
    let script = blake3::hash(b"the parse script").to_hex();
    put!(
        cache
            .join("fake_1")
            .join(script.as_str().get(.. 16).unwrap())
            .join(entry.as_str().get(.. 2).unwrap()),
        entry.as_str(),
        "not a parse"
    );
    assert_eq!(
        run!(root, flags("fake 1", &[]), "fail").status.code(),
        Some(2_i32),
        "a damaged entry parses again"
    );
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_prune_keeps_the_head_s_parses_and_removes_the_rest()
{
    let root = scratch!("prune", "The kernel reduces the term.", "", PRESENT);
    put!(root, "crates/workflow-prose/parse.py", "the parse script");
    assert!(run!(root, ["--write"], "").status.success());
    git!(root, ["add", "."]);
    git!(root, ["commit", "--quiet", "-m", "base"]);
    put!(root, "docs/kept.md", "The kept page reads the term.\n");
    put!(
        root,
        "crates/x/README.md",
        "The gone paragraph reads the term.\n"
    );
    put!(root, "parse.json", joined!(PRESENT, PRESENT, PRESENT));
    let cache = root.join("cache");
    let flags = |extra: &[&str]| {
        let mut flags = vec![
            std::ffi::OsString::from("--cache"),
            cache.clone().into_os_string(),
            "--model".into(),
            "fake 1".into(),
        ];
        flags.extend(extra.iter().map(std::ffi::OsString::from));
        flags
    };
    assert!(run!(root, flags(&["--base", "HEAD"]), "").status.success());
    let script = blake3::hash(b"the parse script").to_hex();
    let scripts = cache.join("fake_1");
    let entry = |text: &str| {
        let digest = blake3::hash(text.as_bytes()).to_hex();
        scripts
            .join(script.as_str().get(.. 16).unwrap())
            .join(digest.as_str().get(.. 2).unwrap())
            .join(digest.as_str())
    };
    let kept = [
        entry("The kernel reduces the term."),
        entry("The kept page reads the term."),
    ];
    let gone = entry("The gone paragraph reads the term.");
    assert!(kept.iter().chain([&gone]).all(|path| path.is_file()));
    put!(
        scripts.join("0123456789abcdef/ab"),
        "ab00",
        "a parse of an older script"
    );
    put!(cache, "notes.txt", "not a parse");
    put!(
        root,
        "crates/x/README.md",
        "The new paragraph reads the term.\n"
    );
    let pruned = run!(root, flags(&["--prune"]), "fail");
    assert_eq!(String::from_utf8_lossy(&pruned.stderr), "");
    assert_eq!(pruned.status.code(), Some(0_i32));
    assert!(
        String::from_utf8_lossy(&pruned.stdout).starts_with(
            "prose: the prune kept 2 parse(s) and removed 1, with 1 stale directory(ies); 0 could \
             not be removed\n"
        ),
        "{}",
        String::from_utf8_lossy(&pruned.stdout)
    );
    assert!(
        kept.iter().all(|path| path.is_file()),
        "the head's parses stand"
    );
    assert!(!gone.exists(), "a parse no paragraph holds is removed");
    assert!(
        !scripts.join("0123456789abcdef").exists(),
        "an older script's parses are removed"
    );
    assert!(cache.join("notes.txt").is_file(), "a stray file stands");
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_cold_parse_across_interpreters_judges_in_order()
{
    let root = scratch!("fan-out", "The kernel reduces the term.", "", PRESENT);
    assert!(run!(root, ["--write"], "").status.success());
    git!(root, ["commit", "--quiet", "-m", "base"]);
    let past = [3_usize, 1000, 2099];
    let readme: Vec<String> = (0 .. 2100_usize)
        .map(|at| {
            let verb = if past.contains(&at) {
                "reduced"
            }
            else {
                "reduces"
            };
            format!("The kernel {verb} term {at}.\n")
        })
        .collect();
    put!(root, "crates/x/README.md", readme.join("\n"));
    put!(root, "parse.json", joined!(PAST, PRESENT));
    let judged = |width: &str| {
        for entry in std::fs::read_dir(&root).unwrap() {
            let path = entry.unwrap().path();
            if path.to_string_lossy().contains("input.json.") {
                std::fs::remove_file(path).unwrap();
            }
        }
        let output = run!(root, ["--base", "HEAD", "--width", width], "each");
        assert_eq!(String::from_utf8_lossy(&output.stderr), "");
        assert_eq!(output.status.code(), Some(1_i32));
        let interpreters = std::fs::read_dir(&root)
            .unwrap()
            .filter(|entry| {
                entry
                    .as_ref()
                    .unwrap()
                    .file_name()
                    .to_string_lossy()
                    .starts_with("input.json.")
            })
            .count();
        (
            String::from_utf8_lossy(&output.stdout).into_owned(),
            interpreters,
        )
    };
    let (alone, one) = judged("1");
    let (fanned, three) = judged("3");
    assert_eq!((one, three), (1, 3), "2101 texts take three interpreters");
    assert_eq!(fanned, alone, "the shards judge as one interpreter does");
    let lines: Vec<&str> = fanned
        .lines()
        .filter_map(|line| line.strip_prefix("crates/x/README.md:"))
        .filter_map(|line| line.split(':').next())
        .collect();
    assert_eq!(lines, ["7", "2001", "4199"], "{fanned}");
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_document_answers_for_the_paragraphs_its_change_wrote()
{
    let root = scratch!("documents", "The kernel reduces the term.", "", PRESENT);
    assert!(run!(root, ["--write"], "").status.success());
    put!(
        root,
        "crates/x/README.md",
        "Kept paragraph one.\n\nOld paragraph.\n"
    );
    put!(root, ".config/issues/templates/t.md", "Old template.\n");
    put!(root, "ledger/census.md", "Old census.\n");
    put!(root, "gone.md", "A page the change deletes.\n");
    git!(root, ["add", "."]);
    git!(root, ["commit", "--quiet", "-m", "base"]);
    put!(
        root,
        "crates/x/README.md",
        "Kept paragraph\none.\n\nThe kernel reduced the term.\n"
    );
    put!(
        root,
        ".config/issues/templates/t.md",
        "The template reduced it.\n"
    );
    put!(root, "ledger/census.md", "The census reduced it.\n");
    std::fs::remove_file(root.join("gone.md")).unwrap();
    put!(root, "docs/new.md", "The new page reads the term.\n");
    put!(root, "parse.json", joined!(PAST, PRESENT, PRESENT));
    let written = run!(root, ["--base", "HEAD"], "");
    assert_eq!(String::from_utf8_lossy(&written.stderr), "");
    assert_eq!(written.status.code(), Some(1_i32));
    assert_eq!(
        String::from_utf8_lossy(&written.stdout),
        "crates/x/README.md:4: STE-3.2: \"The kernel reduced the term.\" — state it in the \
         present tense\nprose: parsed 3 passage(s) of 16 word(s) afresh, of 3 read; 0 parse(s) \
         not kept in the cache\nprose: 2 file(s) touched since HEAD: 1 paragraph(s) kept from the \
         base, 2 written and judged; 0 line(s) of commented-out code left out\n"
    );
    assert_eq!(
        std::fs::read_to_string(root.join("input.json")).unwrap(),
        r#"["The kernel reduced the term.","The new page reads the term.","The kernel reduces the term."]"#,
        "the written paragraphs parse first, and the kept and re-wrapped paragraph, the template \
         and the census never parse"
    );
    put!(
        root,
        "crates/x/README.md",
        "Kept paragraph\none.\n\nThe kernel reduces the term.\n"
    );
    put!(root, "parse.json", joined!(PRESENT, PRESENT));
    let fixed = run!(root, ["--base", "HEAD"], "");
    assert_eq!(String::from_utf8_lossy(&fixed.stderr), "");
    assert_eq!(fixed.status.code(), Some(0_i32));
    assert!(
        String::from_utf8_lossy(&fixed.stdout).ends_with(
            "prose: 2 file(s) touched since HEAD: 1 paragraph(s) kept from the base, 2 written \
             and judged; 0 line(s) of commented-out code left out\nprose: 1 findings, every one \
             in the ledger\n"
        ),
        "{}",
        String::from_utf8_lossy(&fixed.stdout)
    );
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_hash_comment_answers_for_the_paragraphs_its_change_wrote()
{
    let root = scratch!("hash", "The kernel reduces the term.", "", PRESENT);
    assert!(run!(root, ["--write"], "").status.success());
    put!(
        root,
        ".config/mise/tasks/t.toml",
        "# Kept paragraph one.\n[tasks.x]\nrun = '''\n# Old comment of the script.\n'''\n"
    );
    put!(
        root,
        "crates/x/proptest-regressions/a.txt",
        "# Seeds that proptest wrote.\n"
    );
    git!(root, ["add", "."]);
    git!(root, ["commit", "--quiet", "-m", "base"]);
    put!(
        root,
        ".config/mise/tasks/t.toml",
        "# Kept paragraph\n# one.\n[tasks.x]\nrun = '''\n# The kernel reduced the term.\ncat \
         <<EOF\n# The data reduced it.\nEOF\n# old_flag = true\n'''\n"
    );
    put!(
        root,
        ".github/workflows/w.yml",
        "# The workflow reads the term.\non: push\n"
    );
    put!(
        root,
        "crates/x/proptest-regressions/a.txt",
        "# The seeds reduced it.\n"
    );
    put!(
        root,
        "scripts/new",
        "#!/usr/bin/env bash\n# shellcheck disable=SC2034\n# The new script reads the term.\nset \
         -e\n"
    );
    put!(root, "parse.json", joined!(PAST, PRESENT, PRESENT, PRESENT));
    let written = run!(root, ["--base", "HEAD"], "");
    assert_eq!(String::from_utf8_lossy(&written.stderr), "");
    assert_eq!(written.status.code(), Some(1_i32));
    assert_eq!(
        String::from_utf8_lossy(&written.stdout),
        ".config/mise/tasks/t.toml:5: STE-3.2: \"The kernel reduced the term.\" — state it in the \
         present tense\nprose: parsed 4 passage(s) of 21 word(s) afresh, of 4 read; 0 parse(s) \
         not kept in the cache\nprose: 3 file(s) touched since HEAD: 1 paragraph(s) kept from the \
         base, 3 written and judged; 1 line(s) of commented-out code left out\n"
    );
    assert_eq!(
        std::fs::read_to_string(root.join("input.json")).unwrap(),
        r#"["The kernel reduced the term.","The workflow reads the term.","The new script reads the term.","The kernel reduces the term."]"#,
        "the written comments parse first; the re-wrapped comment, the heredoc's data, the \
         commented-out key, the shebang, the directive and proptest's seeds never parse"
    );
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn an_override_admits_its_substitution_and_counts_it()
{
    let root = scratch!("override", "The kernel reduces the term.", "", PRESENT);
    assert!(run!(root, ["--write"], "").status.success());
    put!(
        root,
        "crates/x/README.md",
        "The Opener reads the table.\n\nEach Opener keeps its slot.\n"
    );
    git!(root, ["add", "."]);
    git!(root, ["commit", "--quiet", "-m", "base"]);
    put!(
        root,
        "crates/x/README.md",
        "The Opening reads the table.\n\nEach Opening keeps its own slot.\n"
    );
    put!(root, "parse.json", joined!(PRESENT, PRESENT));
    let body = root.join("body.txt");
    let line =
        "prose-override: mechanical `Opener` -> `Opening` (2 paragraphs), reason: the rename";
    put!(
        root,
        "body.txt",
        format!("## Summary\n\nThe rename.\n\n{line}\n")
    );
    let arguments = [
        std::ffi::OsStr::new("--base"),
        std::ffi::OsStr::new("HEAD"),
        std::ffi::OsStr::new("--override"),
        body.as_os_str(),
    ];
    let claimed = run!(root, arguments, "");
    assert_eq!(String::from_utf8_lossy(&claimed.stderr), "");
    assert_eq!(claimed.status.code(), Some(1_i32));
    assert_eq!(
        String::from_utf8_lossy(&claimed.stdout),
        format!(
            "prose: `{line}` admits 1 paragraph(s) of the 2 it claims\nprose: parsed 2 passage(s) \
             of 11 word(s) afresh, of 2 read; 0 parse(s) not kept in the cache\nprose: 2 file(s) \
             touched since HEAD: 0 paragraph(s) kept from the base, 1 written and judged; 0 \
             line(s) of commented-out code left out\n"
        ),
        "the reworded paragraph parses, and the count admitted differs from the count claimed"
    );
    let line = line.replace("(2 paragraphs)", "(1 paragraph)");
    put!(root, "body.txt", format!("{line}\n"));
    let counted = run!(root, arguments, "");
    assert_eq!(counted.status.code(), Some(0_i32));
    assert!(
        String::from_utf8_lossy(&counted.stdout).starts_with(&format!(
            "prose: `{line}` admits 1 paragraph(s) of the 1 it claims\n"
        )),
        "{}",
        String::from_utf8_lossy(&counted.stdout)
    );
    put!(root, "body.txt", "prose-override: mechanical rename\n");
    let malformed = run!(root, arguments, "");
    assert_eq!(malformed.status.code(), Some(2_i32));
    assert!(
        String::from_utf8_lossy(&malformed.stderr)
            .contains("`prose-override: mechanical rename` is not"),
        "{}",
        String::from_utf8_lossy(&malformed.stderr)
    );
    std::fs::remove_dir_all(&root).unwrap();
}
