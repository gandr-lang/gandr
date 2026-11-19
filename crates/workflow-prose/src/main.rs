//! `prose`: the sentence rules over the corpus comments and the rendered
//! diagnostics against the committed debt, over the paragraphs a change wrote
//! in the markdown documents and the `#` comments, and over a pull request's
//! or an issue's body.
//!
//! `prose --python PATH [--root DIR] [--write]` gathers the text under the
//! root, parses it by running `crates/workflow-prose/parse.py` under the given
//! interpreter, judges every sentence and diagnostic, and compares the
//! findings with `corpus/prose.ledger`. With `--write` it writes the ledger
//! instead. With `--base REV` it also reads each markdown document and each
//! file of `#` comments that the change touched since `REV`, and each
//! paragraph whose digest `REV` does not hold meets every sentence rule with
//! no ledger. `--override FILE` reads the `prose-override:` lines of a pull
//! request body, which admit the paragraphs of a mechanical change. `--cache
//! DIR --model NAME` keeps each parse by its passage's digest, so a passage
//! parses once. `prose --python PATH --body FILE` judges the one body in
//! `FILE` under the body rules, with no ledger.
//!
//! # Exit codes
//!
//! - `0`: every finding is in the ledger, every ledger line is a finding, no
//!   written paragraph breaks a rule and each override admits the count it
//!   claims; or the ledger was written; or the body breaks no rule; also
//!   `--help` and `--version`.
//! - `1`: a finding the ledger lacks, a ledger line no finding matches, a
//!   finding in a written paragraph, an override whose count differs, or a
//!   finding in the body.
//! - `2`: a refusal — an unreadable file, a malformed glossary, ledger or
//!   override, a failed parse or git read, or standard output closed; also a
//!   malformed invocation.

use core::num::NonZeroUsize;
use std::collections::HashSet;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;

use gandr_workflow_debt_ledger::Ledger;
use gandr_workflow_debt_ledger::LedgerError;
use gandr_workflow_debt_ledger::Standing;
use gandr_workflow_prose::Finding;
use gandr_workflow_prose::Glossary;
use gandr_workflow_prose::Key;
use gandr_workflow_prose::ProseError;
use gandr_workflow_prose::cache::Cache;
use gandr_workflow_prose::cache::Model;
use gandr_workflow_prose::cache::Pruned;
use gandr_workflow_prose::cache::Script;
use gandr_workflow_prose::digest::Digest;
use gandr_workflow_prose::documents;
use gandr_workflow_prose::documents::Base;
use gandr_workflow_prose::ledger;
use gandr_workflow_prose::mechanical;
use gandr_workflow_prose::mechanical::Override;
use gandr_workflow_prose::mechanical::Unread;
use gandr_workflow_prose::parse;
use gandr_workflow_prose::parse::Fresh;
use gandr_workflow_prose::parse::Width;
use gandr_workflow_prose::passage;
use gandr_workflow_prose::passage::Advice;
use gandr_workflow_prose::passage::Debt;
use gandr_workflow_prose::passage::Passage;
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
    /// Write the ledger instead of comparing.
    #[arg(long, conflicts_with = "body")]
    write: bool,
    /// Judge the pull request or issue bodies in these files instead, with no
    /// ledger.
    #[arg(long, num_args = 1..)]
    body: Vec<PathBuf>,
    /// The merge base: each paragraph a change wrote since it in a markdown
    /// document or a `#` comment meets every sentence rule.
    #[arg(long, conflicts_with_all = ["body", "write"])]
    base: Option<String>,
    /// The pull request bodies whose `prose-override:` lines admit the
    /// paragraphs of a mechanical change.
    #[arg(long = "override", num_args = 1.., requires = "base")]
    overrides: Vec<PathBuf>,
    /// Keep each parse under this directory, by its passage's digest.
    #[arg(long, requires = "model")]
    cache: Option<PathBuf>,
    /// The parser's and the model's versions, which name the cache.
    #[arg(long, requires = "cache")]
    model: Option<String>,
    /// After the run, remove each kept parse whose passage the head does not
    /// hold, and the cache's directories of another script or model.
    #[arg(long, requires = "cache", conflicts_with = "body")]
    prune: bool,
    /// The most interpreters a cold parse runs at once: the host's parallelism
    /// when it is not given.
    #[arg(long)]
    width: Option<NonZeroUsize>,
}

/// The paragraphs a change wrote in the markdown documents and the `#`
/// comments.
///
/// # Specification
/// - provides: what the documents reader hands the parse, and the counts the
///   run reports.
#[derive(Debug, Default)]
struct Written
{
    /// The files the change touched.
    touched: usize,
    /// Their paragraphs whose digest the base holds.
    held: usize,
    /// The lines of commented-out code that the `#` reader left out of them.
    code: usize,
    /// The paragraphs that parse: written, and admitted by no override.
    passages: Vec<Passage>,
    /// The body's overrides, each with the count it admitted.
    overrides: Vec<Override>,
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
/// - witness: `tests::cli::a_stale_line_is_refused_and_written_away_5007`
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
///
/// # Cost
/// - allocation: the path and the message of a failed write, error path
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
/// parse, the cache read first.
///
/// # Specification
/// - requires: `cli.python` can import spaCy and `en_core_web_sm` when a
///   passage misses the cache.
/// - ensures: each finding of [`passage::body`]'s passages of each file is
///   printed with its file, line, rule, sentence and fix, and the outcome is
///   agreed exactly when none was printed.
/// - provides: the body mode `pr:open`, `issue:file` and the nightly sweep run.
/// - fails: [`ProseError::Io`] when a body or the parse script cannot be read
///   or standard output cannot be written; every refusal of [`parse::parse`].
/// - panics: none.
/// - executable: none — the outcome is the bytes printed.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the bodies' texts, passages and findings, growth within paths
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
    let glossary = Glossary::default();
    let mut out = std::io::stdout().lock();
    let mut found = false;
    parse::parse(
        &cli.python,
        &script,
        &inputs,
        &cache(cli, &script)?,
        width(cli),
        |passage, sentences| {
            for finding in rules::sentences(passage, sentences, &glossary) {
                print(&mut out, &finding)?;
                found = true;
            }
            Ok(())
        },
    )?;
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

/// The cache the invocation names, under the parse script's text.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Cache::under`] the named directory for the named model and the
///   text of `script`; [`Cache::none`] when the invocation names no cache.
/// - provides: the cache both modes read.
/// - fails: [`ProseError::Io`] when the script cannot be read.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the parse script's text, setup
///
/// # Adequacy
/// - hypothesis: L3 — as [`parse::parse`].
/// - witness: `tests::cli::a_second_run_reads_every_parse_from_the_cache`
fn cache(
    cli: &Cli,
    script: &Path,
) -> Result<Cache, ProseError>
{
    match (&cli.cache, &cli.model) {
        (&Some(ref dir), &Some(ref model)) => {
            let text = std::fs::read(script).map_err(|error| ProseError::Io {
                path: script.to_owned(),
                message: error.to_string(),
            })?;
            Ok(Cache::under(dir, Model(model), Script(&text)))
        },
        _ => Ok(Cache::none()),
    }
}

/// The most interpreters a cold parse runs at once: `--width`, or the host's
/// parallelism.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the error of a host that reads no parallelism, error path
fn width(cli: &Cli) -> Width
{
    Width(
        cli.width
            .unwrap_or_else(|| std::thread::available_parallelism().unwrap_or(NonZeroUsize::MIN)),
    )
}

/// The digest of each passage of the head: the passages a run read, and each
/// paragraph of every file that [`documents::every`] lists.
///
/// # Specification
/// - requires: `cli.root` is a repository checkout.
/// - ensures: the digests of `inputs`, with those of the paragraphs that
///   [`documents::at_head`] reads from each file [`documents::every`] lists; no
///   paragraph parses.
/// - provides: what a prune keeps.
/// - fails: every refusal of [`documents::every`] and [`documents::at_head`].
/// - panics: none.
/// - executable: none — the outcome is git's and the file system's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: each file's text, paragraphs and digest, growth within the
///   tree
///
/// # Adequacy
/// - hypothesis: L3 — a run whose cache holds a parse of the head, a parse of
///   an untouched document and a parse no paragraph holds; the first two
///   removed or the third kept changes the next run's fresh count.
/// - witness: `tests::cli::a_prune_keeps_the_head_s_parses_and_removes_the_rest`
fn head(
    cli: &Cli,
    inputs: &[&Passage],
) -> Result<HashSet<Digest>, ProseError>
{
    let mut held: HashSet<Digest> = inputs
        .iter()
        .map(|passage| Digest::of(Text(&passage.text)))
        .collect();
    for file in documents::every(&cli.root)? {
        held.extend(
            documents::at_head(&cli.root, &file)?
                .passages
                .iter()
                .map(|passage| Digest::of(Text(&passage.text))),
        );
    }
    Ok(held)
}

/// The paragraphs a change wrote since `base` in the files it touched, the
/// overrides of `cli.overrides` applied.
///
/// # Specification
/// - requires: `cli.root` is a repository checkout that holds `base`.
/// - ensures: the files [`documents::touched`] lists, each read at the head by
///   [`documents::at_head`]; the paragraphs whose digest no paragraph of
///   [`documents::held`] shares, less those [`mechanical::admit`] admits; each
///   override with its admitted count; the lines of commented-out code that the
///   head's `#` comments hold.
/// - provides: the paragraphs [`run`] parses and judges with no ledger.
/// - fails: every refusal of [`documents::touched`], [`documents::at_head`] and
///   [`documents::held`]; [`ProseError::Io`] for a body that cannot be read;
///   [`ProseError::Override`] for a body's line [`mechanical::read`] refuses.
/// - panics: none.
/// - executable: none — the outcome is git's and the file system's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the head's and the base's paragraphs of the touched files and
///   the held digests, growth within the change
///
/// # Adequacy
/// - hypothesis: L3 — a change that keeps a paragraph, re-wraps one, writes one
///   with a finding and renames a word through two under an override; the kept
///   or re-wrapped one judged, the written one passed, or the renamed ones
///   refused changes the output.
/// - witness: `tests::cli::a_document_answers_for_the_paragraphs_its_change_wrote`
/// - witness: `tests::cli::an_override_admits_its_substitution_and_counts_it`
/// - witness: `tests::cli::a_hash_comment_answers_for_the_paragraphs_its_change_wrote`
fn written(
    cli: &Cli,
    base: Base<'_>,
) -> Result<Written, ProseError>
{
    let touched = documents::touched(&cli.root, base)?;
    let mut head = Vec::new();
    let mut code: usize = 0;
    for file in &touched {
        let read = documents::at_head(&cli.root, file)?;
        code = code.saturating_add(read.code);
        head.extend(read.passages);
    }
    let base_passages = documents::held(&cli.root, base, &touched)?;
    let held: HashSet<Digest> = base_passages
        .iter()
        .map(|passage| Digest::of(Text(&passage.text)))
        .collect();
    let mut overrides = Vec::new();
    for body in &cli.overrides {
        let text = std::fs::read_to_string(body).map_err(|error| ProseError::Io {
            path: body.clone(),
            message: error.to_string(),
        })?;
        overrides.extend(mechanical::read(Text(&text)).map_err(|Unread(line)| {
            ProseError::Override {
                path: body.clone(),
                line,
            }
        })?);
    }
    let fresh: Vec<&Passage> = head
        .iter()
        .filter(|passage| !held.contains(&Digest::of(Text(&passage.text))))
        .collect();
    let held_count = head.len().saturating_sub(fresh.len());
    let passages = mechanical::admit(&mut overrides, &base_passages, fresh)
        .into_iter()
        .cloned()
        .collect();
    Ok(Written {
        touched: touched.len(),
        held: held_count,
        code,
        passages,
        overrides,
    })
}

/// Gathers, parses, judges and compares with the ledger, or writes it; with
/// a base, judges the paragraphs a change wrote in the markdown documents and
/// the `#` comments.
///
/// # Specification
/// - requires: `cli.python` can import spaCy and `en_core_web_sm` when a
///   passage misses the cache.
/// - ensures: with `--write`, the ledger holds one line per distinct finding
///   and the outcome is agreed. Otherwise each finding the ledger lacks is
///   printed with its line, rule, sentence and fix, and each ledger line no
///   finding matches is printed as stale. With `--base`, each finding of a
///   written paragraph is printed as its parse arrives, before the ledger's
///   verdict, and each override is printed with the count it admits beside the
///   count it claims. The run prints the passages and words it parsed afresh,
///   and the outcome is agreed exactly when no finding, stale line or differing
///   count was printed. The written paragraphs, the ledger's passages and the
///   diagnostics' advice parse in one [`parse::parse`], in that order. With
///   `--prune`, the cache keeps only the parses of [`head`] after the parse,
///   and the run prints what the prune kept and removed.
/// - provides: the whole command.
/// - fails: every refusal of [`passage::gather`], [`Glossary::read`],
///   [`written`], [`parse::parse`] and [`head`]; [`ProseError::Ledger`] for a
///   ledger line [`Ledger::read`] refuses; [`ProseError::Io`] when the ledger,
///   the glossary, the parse script or standard output cannot be read or
///   written.
/// - panics: none.
/// - executable: none — the outcome is the bytes printed and the ledger file.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the gathered passages, the parse and the findings, growth
///   within the tree
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`].
/// - witness: `tests::cli::a_new_finding_is_refused_with_its_fix`
/// - witness: `tests::cli::a_stale_line_is_refused_and_written_away_5007`
/// - witness: `tests::cli::a_document_answers_for_the_paragraphs_its_change_wrote`
/// - witness: `tests::cli::a_prune_keeps_the_head_s_parses_and_removes_the_rest`
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
    let written = match cli.base {
        Some(ref base) => Some(written(cli, Base(base))?),
        None => None,
    };
    let mut inputs: Vec<&passage::Passage> = Vec::new();
    if let Some(ref written) = written {
        inputs.extend(written.passages.iter());
    }
    let documents = inputs.len();
    inputs.extend(gathered.passages.iter());
    for golden in &gathered.goldens {
        if let Advice::Help(ref help) = golden.advice {
            inputs.push(help);
        }
    }
    let script = cli.root.join("crates/workflow-prose/parse.py");
    let mut out = std::io::stdout().lock();
    let output = |error: std::io::Error| ProseError::Io {
        path: PathBuf::from("<stdout>"),
        message: error.to_string(),
    };
    let mut refused = false;
    let cache = cache(cli, &script)?;
    let parsed = parse::parse(
        &cli.python,
        &script,
        &inputs,
        &cache,
        width(cli),
        |passage, sentences| {
            if passage.source.debt() == Debt::Base {
                for finding in rules::sentences(passage, sentences, &glossary) {
                    print(&mut out, &finding)?;
                    refused = true;
                }
            }
            Ok(())
        },
    )?;
    if cli.prune {
        let Pruned {
            kept,
            removed,
            stale,
            stuck,
        } = cache.prune(&head(cli, &inputs)?);
        writeln!(
            out,
            "prose: the prune kept {kept} parse(s) and removed {removed}, with {stale} stale \
             directory(ies); {stuck} could not be removed"
        )
        .map_err(output)?;
    }
    let mut parses = parsed.sentences.iter().skip(documents);
    let mut findings: Vec<Finding> = Vec::new();
    let mut passage_parses = Vec::new();
    for (passage, sentences) in gathered.passages.iter().zip(parses.by_ref()) {
        findings.extend(rules::sentences(passage, sentences, &glossary));
        passage_parses.push(sentences.as_slice());
    }
    findings.extend(rules::shaped(
        &gathered.shapes,
        &gathered.passages,
        &passage_parses,
    ));
    for golden in &gathered.goldens {
        let help = match golden.advice {
            Advice::Help(_) => parses.next().map_or(&[][..], Vec::as_slice),
            Advice::Tracked | Advice::Missing => &[],
        };
        findings.extend(rules::procedure(golden, help));
    }
    let ledger_path = cli.root.join("corpus/prose.ledger");
    if cli.write {
        let text = gandr_workflow_debt_ledger::write(ledger::HEADER, findings.iter().map(Key::of));
        let lines = text.lines().filter(|line| !line.starts_with('#')).count();
        std::fs::write(&ledger_path, text).map_err(io(ledger_path))?;
        writeln!(out, "prose: wrote {lines} ledger lines").map_err(output)?;
        return Ok(Outcome::Agreed);
    }
    let committed = Ledger::<Key>::read(gandr_workflow_debt_ledger::Text(
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
        refused = true;
    }
    if let Some(ref written) = written {
        for stated in &written.overrides {
            writeln!(
                out,
                "prose: `{}` admits {} paragraph(s) of the {} it claims",
                stated.line, stated.admitted, stated.claimed
            )
            .map_err(output)?;
            if stated.admitted != stated.claimed {
                refused = true;
            }
        }
    }
    let Fresh {
        passages,
        words,
        unkept,
    } = parsed.fresh;
    writeln!(
        out,
        "prose: parsed {passages} passage(s) of {words} word(s) afresh, of {} read; {unkept} \
         parse(s) not kept in the cache",
        inputs.len()
    )
    .map_err(output)?;
    if let (&Some(ref base), &Some(ref written)) = (&cli.base, &written) {
        writeln!(
            out,
            "prose: {} file(s) touched since {base}: {} paragraph(s) kept from the base, {} \
             written and judged; {} line(s) of commented-out code left out",
            written.touched,
            written.held,
            written.passages.len(),
            written.code
        )
        .map_err(output)?;
    }
    if refused {
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
