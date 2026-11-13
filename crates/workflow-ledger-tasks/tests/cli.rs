//! The exit codes and output of `gandr-ledger`, observed by spawning the
//! binary.
//!
//! Each case writes its sources into a scratch directory, runs `gandr-ledger`
//! on them, and asserts the exit code and the lines it printed.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;

/// A fresh scratch directory, removed when dropped.
#[repr(transparent)]
struct Scratch(PathBuf);

/// A process's exit code.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Code(i32);

/// Text that a case names or writes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Text<'text>(&'text str);

impl Scratch
{
    /// An empty directory named for `test` and this process.
    ///
    /// # Specification
    /// trivial.
    fn new(test: Text<'_>) -> Self
    {
        let root =
            std::env::temp_dir().join(format!("gandr-ledger-{}-{}", test.0, std::process::id()));
        if root.exists() {
            std::fs::remove_dir_all(&root).expect("a stale scratch directory is removed");
        }
        std::fs::create_dir_all(&root).expect("the scratch directory is created");
        Self(root)
    }

    /// Write `text` at `relative`, creating its directories, and return its
    /// path.
    ///
    /// # Specification
    /// trivial.
    fn file(
        &self,
        relative: &Path,
        text: Text<'_>,
    ) -> PathBuf
    {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().expect("a file has a parent"))
            .expect("the directories are created");
        std::fs::write(&path, text.0).expect("the file is written");
        path
    }
}

impl Drop for Scratch
{
    /// Remove the directory and everything under it.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        let removed = std::fs::remove_dir_all(&self.0);
        assert!(removed.is_ok(), "the scratch directory is removed");
    }
}

/// The finished run of `gandr-ledger` with `arguments`, its output captured.
///
/// # Specification
/// trivial.
fn ran<Argument>(arguments: &[Argument]) -> Output
where
    Argument: AsRef<std::ffi::OsStr>,
{
    Command::new(env!("CARGO_BIN_EXE_gandr-ledger"))
        .args(arguments)
        .output()
        .expect("the binary runs")
}

/// The exit code of `output`.
///
/// # Specification
/// trivial.
fn code(output: &Output) -> Code
{
    Code(output.status.code().expect("the binary exits with a code"))
}

/// Standard output of `output`, as text.
///
/// # Specification
/// trivial.
fn stdout(output: &Output) -> String
{
    String::from_utf8(output.stdout.clone()).expect("standard output is UTF-8")
}

/// Standard error of `output`, as text.
///
/// # Specification
/// trivial.
fn stderr(output: &Output) -> String
{
    String::from_utf8(output.stderr.clone()).expect("standard error is UTF-8")
}

/// The committed exemplar directory.
///
/// # Specification
/// trivial.
fn committed() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/ledger")
}

#[test]
fn the_syntax_ledger_is_written_and_reproduced()
{
    let scratch = Scratch::new(Text("syntax"));
    let directory = scratch.0.join("ledger");
    let committed = committed();
    let (syntax, write, with) = (
        Path::new("syntax"),
        Path::new("--write"),
        Path::new("--exemplars"),
    );

    let written = ran(&[syntax, write, &directory, with, &committed]);
    assert_eq!(code(&written), Code(0_i32), "{}", stderr(&written));
    let markdown = directory.join("syntax.md");
    let json = directory.join("syntax.json");
    assert_eq!(
        stdout(&written),
        format!("{}\n{}\n", markdown.display(), json.display()),
        "each file written is printed, in order"
    );
    let first = (
        std::fs::read(&markdown).expect("the reading form is written"),
        std::fs::read(&json).expect("the machine form is written"),
    );
    assert!(
        String::from_utf8_lossy(&first.0).contains("- Grammar fingerprint: `0x"),
        "the reading form names the fingerprint"
    );

    let again = ran(&[syntax, write, &directory, with, &committed]);
    assert_eq!(code(&again), Code(0_i32), "{}", stderr(&again));
    let second = (
        std::fs::read(&markdown).expect("the reading form is written"),
        std::fs::read(&json).expect("the machine form is written"),
    );
    assert_eq!(first, second, "a second run writes the same bytes");

    let blocked = scratch.file(Path::new("file"), Text(""));
    let refused = ran(&[syntax, write, &blocked.join("ledger"), with, &committed]);
    assert_eq!(code(&refused), Code(2_i32), "{}", stdout(&refused));
    assert!(
        stderr(&refused).starts_with(&format!(
            "gandr-ledger: {}",
            blocked.join("ledger").display()
        )),
        "{}",
        stderr(&refused)
    );

    let unshown = ran(&[syntax, write, &directory]);
    assert_eq!(code(&unshown), Code(2_i32), "{}", stdout(&unshown));
    assert!(
        stderr(&unshown).starts_with(&format!(
            "gandr-ledger: {}",
            directory.join("exemplars").join("syntax").display()
        )),
        "without `--exemplars` the admissions are read under the written directory: {}",
        stderr(&unshown)
    );
}

#[test]
fn the_exemplars_verify_and_a_stray_one_is_named()
{
    let committed = committed();
    let exemplars = Path::new("exemplars");

    let clean = ran(&[exemplars, &committed]);
    assert_eq!(code(&clean), Code(0_i32), "{}", stdout(&clean));
    assert!(
        stdout(&clean).ends_with(" owed, 0 findings\n"),
        "{}",
        stdout(&clean)
    );

    let scratch = Scratch::new(Text("exemplars"));
    for folder in ["syntax", "attributes", "diagnostics"] {
        for entry in std::fs::read_dir(committed.join(folder)).expect("the folder lists") {
            let source = entry.expect("the entry reads").path();
            let name = source.file_name().expect("an exemplar is a file");
            let text = std::fs::read_to_string(&source).expect("the exemplar reads");
            let _path = scratch.file(&Path::new(folder).join(name), Text(&text));
        }
    }
    let stray = scratch.file(
        Path::new("syntax/unknown_rule.gandr"),
        Text("/// `unknown_rule`: no such rule.\ndef answer = 42 ;\n"),
    );
    let found = ran(&[exemplars, &scratch.0]);
    assert_eq!(code(&found), Code(1_i32), "{}", stderr(&found));
    assert!(
        stdout(&found).starts_with(&format!(
            "{}: names nothing the ledger lists\n",
            stray.display()
        )),
        "{}",
        stdout(&found)
    );
    assert!(stdout(&found).ends_with(" owed, 1 finding\n"));
}

#[test]
fn the_recovery_sweep_reports_its_table_and_count()
{
    let scratch = Scratch::new(Text("recovery"));
    let _path = scratch.file(
        Path::new("syntax/def_value.gandr"),
        Text("/// `def_value`: a definition.\n@[ checks ]\ndef answer = 42 ;\n"),
    );
    let swept = ran(&[Path::new("recovery"), &scratch.0]);
    assert_eq!(code(&swept), Code(0_i32), "{}", stderr(&swept));
    let printed = stdout(&swept);
    assert!(
        printed
            .lines()
            .any(|line| line == "near miss: `def` → `de`"),
        "the table names what each tile is mistaken for: {printed}"
    );
    assert!(
        printed.ends_with(" accepted, 0 well formed, 0 closed early, 0 marked elsewhere\n"),
        "the count closes the report: {printed}"
    );
}

/// #1827: `gandr-ledger list` and `gandr-ledger show` read the features
/// ledger as the guide an author writes from.
#[test]
fn the_features_ledger_lists_and_shows_1827()
{
    let scratch = Scratch::new(Text("features"));
    let _ledger = scratch.file(
        Path::new("ledger/features.sql"),
        Text(
            "PRAGMA foreign_keys=OFF;\nBEGIN TRANSACTION;\nCREATE TABLE feature(\n  id TEXT PRIMARY KEY,\n  area \
         TEXT NOT NULL,\n  name TEXT NOT NULL,\n  parent TEXT,\n  status TEXT NOT NULL,\n  notability TEXT NOT \
         NULL,\n  compared_to TEXT,\n  line TEXT NOT NULL CHECK(line <> ''),\n  crate TEXT,\n  corpus TEXT,\n  \
         exemplar TEXT,\n  issue TEXT,\n  since TEXT\n) WITHOUT ROWID;\n\
         INSERT INTO feature VALUES('answers','syntax','Answers',NULL,'implemented','ordinary',NULL,'A \
         definition''s answer.','surface-parser','tests/answers.rs','ledger/answers.gandr',NULL,'#2');\n\
         INSERT INTO feature VALUES('questions','syntax','Questions',NULL,'planned','ordinary',NULL,'A \
         question.',NULL,NULL,NULL,'#3',NULL);\n\
         INSERT INTO feature VALUES('reels','storage','Reels',NULL,'implemented','ordinary',NULL,'A \
         reel.','storage-records',NULL,'crate-tests',NULL,'#4');\nCOMMIT;\n",
        ),
    );
    let _exemplar = scratch.file(
        Path::new("ledger/answers.gandr"),
        Text("/// `answers`: a definition.\n@[ checks ]\ndef answer = 42 ;\n"),
    );
    let root = Path::new("--root");

    let listed = ran(&[
        Path::new("list"),
        Path::new("--area"),
        Path::new("syntax"),
        root,
        &scratch.0,
    ]);
    assert_eq!(code(&listed), Code(0_i32), "{}", stderr(&listed));
    assert_eq!(
        stdout(&listed),
        "answers [implemented] Answers: A definition's answer.\nquestions [planned] Questions: A question.\n"
    );
    let planned = ran(&[
        Path::new("list"),
        Path::new("--status"),
        Path::new("planned"),
        root,
        &scratch.0,
    ]);
    assert_eq!(code(&planned), Code(0_i32), "{}", stderr(&planned));
    assert_eq!(
        stdout(&planned),
        "questions [planned] Questions: A question.\n"
    );

    let shown = ran(&[Path::new("show"), Path::new("answers"), root, &scratch.0]);
    assert_eq!(code(&shown), Code(0_i32), "{}", stderr(&shown));
    assert_eq!(
        stdout(&shown),
        "id: answers\narea: syntax\nname: Answers\nstatus: implemented\nnotability: ordinary\nline: A \
         definition's answer.\ncrate: surface-parser\ncorpus: tests/answers.rs\nexemplar: \
         ledger/answers.gandr\nsince: #2\n--- ledger/answers.gandr\n/// `answers`: a definition.\n@[ checks \
         ]\ndef answer = 42 ;\n--- corpus\ntests/answers.rs\n"
    );

    let elsewhere = ran(&[
        Path::new("list"),
        Path::new("--area"),
        Path::new("astrology"),
        root,
        &scratch.0,
    ]);
    assert_eq!(code(&elsewhere), Code(2_i32), "{}", stdout(&elsewhere));
    assert_eq!(
        stderr(&elsewhere),
        "gandr-ledger: no feature is in the area `astrology`; the areas are storage, syntax\n"
    );
    let unknown = ran(&[Path::new("show"), Path::new("answer"), root, &scratch.0]);
    assert_eq!(code(&unknown), Code(2_i32), "{}", stdout(&unknown));
    assert_eq!(stderr(&unknown), "gandr-ledger: no feature is `answer`\n");

    let committed = ran(&[
        Path::new("show"),
        Path::new("features-exemplars"),
        root,
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."),
    ]);
    assert_eq!(code(&committed), Code(0_i32), "{}", stderr(&committed));
}
