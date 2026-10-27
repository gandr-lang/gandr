//! `prose`: the sentence rules over the corpus comments, the rendered
//! diagnostics and the crate READMEs, against the committed debt.
//!
//! `prose --python PATH [--root DIR] [--write]` gathers the text under the
//! root, parses it by running `crates/workflow-prose/parse.py` under the given
//! interpreter, judges every sentence and diagnostic, and compares the
//! findings with `corpus/prose.ledger`. With `--write` it writes the ledger
//! instead.
//!
//! # Exit codes
//!
//! - `0`: every finding is in the ledger and every ledger line is a finding; or
//!   the ledger was written; also `--help` and `--version`.
//! - `1`: a finding the ledger lacks, or a ledger line no finding matches.
//! - `2`: a refusal — an unreadable file, a malformed glossary or ledger, a
//!   failed parse, or standard output closed; also a malformed invocation.

extern crate alloc;

use alloc::collections::BTreeSet;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use gandr_workflow_prose::Finding;
use gandr_workflow_prose::Glossary;
use gandr_workflow_prose::Key;
use gandr_workflow_prose::ProseError;
use gandr_workflow_prose::ledger;
use gandr_workflow_prose::parse;
use gandr_workflow_prose::passage;
use gandr_workflow_prose::passage::Advice;
use gandr_workflow_prose::passage::Text;
use gandr_workflow_prose::rules;
use gandr_workflow_prose::rules::Fix;

/// The exit code of findings the ledger does not match.
const FOUND: u8 = 1;

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// The sentence rules against the committed prose debt.
#[derive(Debug, clap::Parser)]
#[command(name = "prose", version, about)]
struct Cli
{
    /// The interpreter of the pinned spaCy venv.
    #[arg(long)]
    python: PathBuf,
    /// The repository root.
    #[arg(long, default_value = ".")]
    root: PathBuf,
    /// Write the ledger from the findings instead of comparing.
    #[arg(long)]
    write: bool,
}

/// What a run concluded.
///
/// # Specification
/// - provides: the exit code's cause.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Outcome
{
    /// The findings and the ledger agree, or the ledger was written.
    Agreed,
    /// A finding or a ledger line has no partner.
    Disagreed,
}

/// Parses the invocation, runs the check and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits `0` when the findings and the ledger agree or the ledger
///   was written, `1` when they disagree, `2` after printing a refusal or a
///   usage message to standard error.
/// - provides: the process boundary.
/// - fails: never; every refusal is an exit code.
/// - panics: none.
/// - executable: none — the outcome is the process's exit code.
///
/// # Adequacy
/// - hypothesis: L3 — a run in agreement, one with a new finding, one with a
///   stale line and one whose parse fails; a swapped exit code changes the
///   observed process result.
/// - witness: `tests::cli::a_new_finding_is_refused_with_its_fix`
/// - witness: `tests::cli::a_stale_line_is_refused_and_written_away`
/// - witness: `tests::cli::a_failing_parse_is_reported_with_its_message`
fn main() -> ExitCode
{
    let cli = match <Cli as clap::Parser>::try_parse() {
        Ok(cli) => cli,
        Err(error) => {
            drop(error.print());
            return if error.use_stderr() {
                ExitCode::from(REFUSED)
            }
            else {
                ExitCode::SUCCESS
            };
        },
    };
    match run(&cli) {
        Ok(Outcome::Agreed) => ExitCode::SUCCESS,
        Ok(Outcome::Disagreed) => ExitCode::from(FOUND),
        Err(error) => {
            drop(writeln!(std::io::stderr(), "prose: {error}"));
            ExitCode::from(REFUSED)
        },
    }
}

/// Gathers, parses, judges and compares with the ledger, or writes it.
///
/// # Specification
/// - requires: `cli.python` can import spaCy and `en_core_web_sm`.
/// - ensures: with `--write`, the ledger holds one line per distinct finding
///   and the outcome is agreed; otherwise each finding the ledger lacks is
///   printed with its line, rule, sentence and fix, each ledger line no finding
///   matches is printed as stale, and the outcome is agreed exactly when
///   neither was printed.
/// - provides: the whole command.
/// - fails: every refusal of [`passage::gather`], [`Glossary::read`],
///   [`parse::parse`] and [`ledger::read`]; [`ProseError::Io`] when the ledger,
///   the glossary or standard output cannot be read or written.
/// - panics: none.
/// - executable: none — the outcome is the bytes printed and the ledger file.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`].
/// - witness: `tests::cli::a_new_finding_is_refused_with_its_fix`
/// - witness: `tests::cli::a_stale_line_is_refused_and_written_away`
fn run(cli: &Cli) -> Result<Outcome, ProseError>
{
    let io = |path: PathBuf| {
        move |error: std::io::Error| ProseError::Io {
            path,
            message: error.to_string(),
        }
    };
    let glossary_path = cli.root.join("corpus/glossary.toml");
    let glossary = Glossary::read(Text(
        &std::fs::read_to_string(&glossary_path).map_err(io(glossary_path))?,
    ))?;
    let gathered = passage::gather(&cli.root)?;
    let mut inputs: Vec<&passage::Passage> = gathered.passages.iter().collect();
    for golden in &gathered.goldens {
        if let Advice::Help(ref help) = golden.advice {
            inputs.push(help);
        }
    }
    let script = cli.root.join("crates/workflow-prose/parse.py");
    let parsed = parse::parse(&cli.python, &script, &inputs)?;
    let mut parses = parsed.iter();
    let mut findings: Vec<Finding> = Vec::new();
    for (passage, sentences) in gathered.passages.iter().zip(parses.by_ref()) {
        findings.extend(rules::sentences(passage, sentences, &glossary));
    }
    for golden in &gathered.goldens {
        let help = match golden.advice {
            Advice::Help(_) => parses.next().map_or(&[][..], Vec::as_slice),
            Advice::Tracked | Advice::Missing => &[],
        };
        findings.extend(rules::procedure(golden, help));
    }
    let keys: BTreeSet<Key> = findings.iter().map(Key::of).collect();
    let ledger_path = cli.root.join("corpus/prose.ledger");
    let mut out = std::io::stdout().lock();
    let output = |error: std::io::Error| ProseError::Io {
        path: PathBuf::from("<stdout>"),
        message: error.to_string(),
    };
    if cli.write {
        std::fs::write(&ledger_path, ledger::write(&keys)).map_err(io(ledger_path))?;
        writeln!(out, "prose: wrote {} ledger lines", keys.len()).map_err(output)?;
        return Ok(Outcome::Agreed);
    }
    let committed = ledger::read(Text(
        &std::fs::read_to_string(&ledger_path).map_err(io(ledger_path))?,
    ))?;
    let mut disagreed = false;
    let mut told = BTreeSet::new();
    for finding in &findings {
        let key = Key::of(finding);
        if committed.contains(&key) || !told.insert(key) {
            continue;
        }
        disagreed = true;
        writeln!(
            out,
            "{}:{}: {}: \"{}\" — {}",
            finding.path,
            finding.line,
            finding.rule,
            finding.sentence,
            Fix(finding.rule)
        )
        .map_err(output)?;
    }
    for stale in committed.difference(&keys) {
        disagreed = true;
        writeln!(
            out,
            "corpus/prose.ledger: stale line `{stale}`: no finding matches it; run `mise run \
             check:prose --write`"
        )
        .map_err(output)?;
    }
    if disagreed {
        return Ok(Outcome::Disagreed);
    }
    writeln!(
        out,
        "prose: {} findings, every one in the ledger",
        findings.len()
    )
    .map_err(output)?;
    Ok(Outcome::Agreed)
}
