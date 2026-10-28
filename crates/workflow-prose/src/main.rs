//! `prose`: the sentence rules over the corpus comments, the rendered
//! diagnostics and the crate READMEs, against the committed debt, and over a
//! pull request's or an issue's body.
//!
//! `prose --python PATH [--root DIR] [--write]` gathers the text under the
//! root, parses it by running `crates/workflow-prose/parse.py` under the given
//! interpreter, judges every sentence and diagnostic, and compares the
//! findings with `corpus/prose.ledger`. With `--write` it writes the ledger
//! instead. `prose --python PATH --body FILE` judges the one body in `FILE`
//! under the body rules, with no ledger.
//!
//! # Exit codes
//!
//! - `0`: every finding is in the ledger and every ledger line is a finding; or
//!   the ledger was written; or the body breaks no rule; also `--help` and
//!   `--version`.
//! - `1`: a finding the ledger lacks, a ledger line no finding matches, or a
//!   finding in the body.
//! - `2`: a refusal — an unreadable file, a malformed glossary or ledger, a
//!   failed parse, or standard output closed; also a malformed invocation.

use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use gandr_workflow_ledger::Ledger;
use gandr_workflow_ledger::LedgerError;
use gandr_workflow_ledger::Standing;
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
    #[arg(long, conflicts_with = "body")]
    write: bool,
    /// Judge the pull request or issue bodies in these files instead, with no
    /// ledger.
    #[arg(long, num_args = 1..)]
    body: Vec<PathBuf>,
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
/// - ensures: exits `0` when the findings and the ledger agree, the ledger was
///   written or the body breaks no rule, `1` when they disagree or the body
///   breaks a rule, `2` after printing a refusal or a usage message to standard
///   error.
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
/// - witness: `tests::cli::a_body_is_refused_on_its_findings`
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
    let outcome = if cli.body.is_empty() {
        run(&cli)
    }
    else {
        judge(&cli, &cli.body)
    };
    match outcome {
        Ok(Outcome::Agreed) => ExitCode::SUCCESS,
        Ok(Outcome::Disagreed) => ExitCode::from(FOUND),
        Err(error) => {
            drop(writeln!(std::io::stderr(), "prose: {error}"));
            ExitCode::from(REFUSED)
        },
    }
}

/// Writes `finding` with its fix to `out`.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — the check and the body mode print each finding's file,
///   line, rule, sentence and fix; a lost part changes the printed line.
/// - witness: `tests::cli::a_new_finding_is_refused_with_its_fix`
/// - witness: `tests::cli::a_body_is_refused_on_its_findings`
fn print(
    out: &mut impl std::io::Write,
    finding: &Finding,
) -> Result<(), ProseError>
{
    writeln!(
        out,
        "{}:{}: {}: \"{}\" — {}",
        finding.path,
        finding.line,
        finding.rule,
        finding.sentence,
        Fix(finding.rule)
    )
    .map_err(|error| ProseError::Io {
        path: PathBuf::from("<stdout>"),
        message: error.to_string(),
    })
}

/// Parses and judges the bodies in `paths` under the body rules, in one
/// parse.
///
/// # Specification
/// - requires: `cli.python` can import spaCy and `en_core_web_sm`.
/// - ensures: each finding of [`passage::body`]'s passages of each file is
///   printed with its file, line, rule, sentence and fix, and the outcome is
///   agreed exactly when none was printed.
/// - provides: the body mode `pr:open`, `issue:file` and the nightly sweep run.
/// - fails: [`ProseError::Io`] when a body cannot be read or standard output
///   cannot be written; every refusal of [`parse::parse`].
/// - panics: none.
/// - executable: none — the outcome is the bytes printed.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a body with a finding beside one with none, and a clean
///   body alone; a finding unprinted, misattributed to the other file, or a
///   clean body refused changes the observed output and exit code.
/// - witness: `tests::cli::a_body_is_refused_on_its_findings`
fn judge(
    cli: &Cli,
    paths: &[PathBuf],
) -> Result<Outcome, ProseError>
{
    let mut passages = Vec::new();
    let mut name = String::new();
    let mut text = String::new();
    for path in paths {
        let unread = |error: std::io::Error| ProseError::Io {
            path: path.clone(),
            message: error.to_string(),
        };
        text.clear();
        std::io::Read::read_to_string(&mut std::fs::File::open(path).map_err(unread)?, &mut text)
            .map_err(unread)?;
        name.clear();
        core::fmt::Write::write_fmt(&mut name, format_args!("{}", path.display())).map_err(
            |error| ProseError::Io {
                path: path.clone(),
                message: error.to_string(),
            },
        )?;
        passages.extend(passage::body(Text(&name), Text(&text)));
    }
    let inputs: Vec<&passage::Passage> = passages.iter().collect();
    let script = cli.root.join("crates/workflow-prose/parse.py");
    let parsed = parse::parse(&cli.python, &script, &inputs)?;
    let glossary = Glossary::default();
    let mut out = std::io::stdout().lock();
    let mut found = false;
    for (passage, sentences) in passages.iter().zip(&parsed) {
        for finding in rules::sentences(passage, sentences, &glossary) {
            print(&mut out, &finding)?;
            found = true;
        }
    }
    if found {
        return Ok(Outcome::Disagreed);
    }
    writeln!(out, "prose: {} file(s), no body rule broken", paths.len()).map_err(|error| {
        ProseError::Io {
            path: PathBuf::from("<stdout>"),
            message: error.to_string(),
        }
    })?;
    Ok(Outcome::Agreed)
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
/// - fails: every refusal of [`passage::gather`], [`Glossary::read`] and
///   [`parse::parse`]; [`ProseError::Ledger`] for a ledger line
///   [`Ledger::read`] refuses; [`ProseError::Io`] when the ledger, the glossary
///   or standard output cannot be read or written.
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
    let ledger_path = cli.root.join("corpus/prose.ledger");
    let mut out = std::io::stdout().lock();
    let output = |error: std::io::Error| ProseError::Io {
        path: PathBuf::from("<stdout>"),
        message: error.to_string(),
    };
    if cli.write {
        let text = gandr_workflow_ledger::write(ledger::HEADER, findings.iter().map(Key::of));
        let lines = text.lines().filter(|line| !line.starts_with('#')).count();
        std::fs::write(&ledger_path, text).map_err(io(ledger_path))?;
        writeln!(out, "prose: wrote {lines} ledger lines").map_err(output)?;
        return Ok(Outcome::Agreed);
    }
    let committed = Ledger::<Key>::read(gandr_workflow_ledger::Text(
        &std::fs::read_to_string(&ledger_path).map_err(io(ledger_path))?,
    ))
    .map_err(|LedgerError::Unread { line }| ProseError::Ledger { line })?;
    let verdict = committed.check(&findings, Key::of);
    for finding in &verdict.new {
        print(&mut out, finding)?;
    }
    for stale in &verdict.stale {
        writeln!(
            out,
            "corpus/prose.ledger: stale line `{stale}`: no finding matches it; run `mise run \
             check:prose --write`"
        )
        .map_err(output)?;
    }
    if verdict.standing() == Standing::Disagreed {
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
