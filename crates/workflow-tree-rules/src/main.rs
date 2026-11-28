//! `tree-rules`: holds each tracked file of the tree to its rules.
//!
//! `tree-rules [--root <dir>] [--rule <rule>]... [--cost]` lists the tracked
//! files with one run of `git ls-files`, judges each name, and reads each
//! file that is not binary one time for the rules of its lines. With no
//! `--rule`, it runs each rule: `residue`, `paths` and `markdown`. With
//! `--cost`, it prints each part of the run on standard error, with its count
//! and its time.
//!
//! The binary exits with one of three codes:
//!
//! - `0`: no finding; also `--help` and `--version`.
//! - `1`: a finding.
//! - `2`: a file of the rules that cannot be read, a git that fails, a file of
//!   the tree that cannot be read, output that cannot be written, or a
//!   malformed invocation.

extern crate alloc;

use alloc::collections::BTreeSet;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use anodized::spec;
use gandr_workflow_tree_rules::Rule;
use gandr_workflow_tree_rules::Rules;
use gandr_workflow_tree_rules::binary;

/// The exit code of a finding.
const FOUND: u8 = 1;

/// The exit code of a fault or a malformed invocation.
const FAULTED: u8 = 2;

/// Holds each tracked file of the tree to its rules.
#[derive(Debug, clap::Parser)]
#[command(name = "tree-rules", version, about)]
struct Cli
{
    /// The root of the tree.
    #[arg(long, value_name = "DIR", default_value = ".")]
    root: PathBuf,
    /// A rule to run: `residue`, `paths` or `markdown`; each rule when none
    /// is named.
    #[arg(long = "rule", value_name = "RULE", value_parser = rule)]
    rules: Vec<Rule>,
    /// Print each part of the run with its count and its time.
    #[arg(long)]
    cost: bool,
}

/// The rule that a name of `--rule` names.
///
/// # Specification
/// trivial.
///
/// # Errors
/// A message that lists the rules, for a name of no rule.
fn rule(name: &str) -> Result<Rule, String>
{
    Rule::ALL
        .into_iter()
        .find(|rule| rule.name() == name)
        .ok_or_else(|| format!("no rule `{name}`: the rules are `residue`, `paths` and `markdown`"))
}

/// The standard output of `git ls-files -z` in `root`, or the fault on
/// `stderr`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`std::io::Error`] of a write to `stderr` that failed.
fn tracked(
    root: &Path,
    stderr: &mut impl std::io::Write,
) -> std::io::Result<Option<Vec<u8>>>
{
    match std::process::Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["ls-files", "-z"])
        .output()
    {
        Ok(output) if output.status.success() => Ok(Some(output.stdout)),
        Ok(output) => {
            writeln!(
                stderr,
                "tree-rules: git ls-files: {}",
                String::from_utf8_lossy(&output.stderr).trim_end()
            )?;
            Ok(None)
        },
        Err(error) => {
            writeln!(stderr, "tree-rules: git: cannot start: {error}")?;
            Ok(None)
        },
    }
}

/// Runs the rules over the tree at `root`, prints each finding on `stderr`,
/// and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits `0` after an `OK` line on `stdout` when no tracked file
///   breaks a rule of `rules`; exits `1` after each finding and a count on
///   `stderr`; exits `2` after a fault on `stderr`. A symbolic link and a
///   binary file get no read of their lines.
/// - provides: the whole command.
/// - fails: the [`std::io::Error`] of the first write to a stream that failed.
/// - panics: none.
/// - executable: none — the outcome is the bytes written.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a clean tree, a tree with a finding of each rule, and a
///   pattern that does not compile.
/// - witness: `tests::cli::a_clean_tree_passes`
/// - witness: `tests::cli::the_gate_names_each_finding_and_exits_one`
/// - witness: `tests::cli::a_pattern_that_does_not_compile_is_a_fault`
///
/// # Cost
/// - allocation: the paths of the tracked files, the text of one file at a
///   time, each finding
/// - io: one run of `git ls-files`, one read of each file of the rules, one
///   read of each tracked file that a rule of lines reads
fn run(
    root: &Path,
    rules: &BTreeSet<Rule>,
    cost: bool,
    stdout: &mut impl std::io::Write,
    stderr: &mut impl std::io::Write,
) -> std::io::Result<ExitCode>
{
    let start = Instant::now();
    let read = match Rules::read(root) {
        Ok(read) => read,
        Err(fault) => {
            writeln!(stderr, "tree-rules: {fault}")?;
            return Ok(ExitCode::from(FAULTED));
        },
    };
    let Some(listed) = tracked(root, stderr)?
    else {
        return Ok(ExitCode::from(FAULTED));
    };
    let lines = rules.iter().any(|rule| rule.reads_lines());
    let mut findings = Vec::new();
    let mut files = 0_usize;
    let mut texts = 0_usize;
    for name in listed
        .split(|&byte| byte == 0)
        .filter(|name| !name.is_empty())
    {
        let path = String::from_utf8_lossy(name);
        files = files.saturating_add(1);
        read.judge_name(rules, &path, &mut findings);
        if !lines {
            continue;
        }
        let file = root.join(&*path);
        let readable = std::fs::symlink_metadata(&file).is_ok_and(|meta| {
            let kind = meta.file_type();
            !kind.is_dir() && !kind.is_symlink()
        });
        if !readable {
            continue;
        }
        let bytes = match std::fs::read(&file) {
            Ok(bytes) => bytes,
            Err(error) => {
                writeln!(stderr, "tree-rules: `{path}`: {error}")?;
                return Ok(ExitCode::from(FAULTED));
            },
        };
        if binary(&bytes) {
            continue;
        }
        texts = texts.saturating_add(1);
        read.judge_text(
            rules,
            &path,
            &String::from_utf8_lossy(&bytes),
            &mut findings,
        );
    }
    if cost {
        writeln!(
            stderr,
            "tree-rules: cost: {files} names judged, {texts} files read, in {} ms",
            start.elapsed().as_millis()
        )?;
    }
    let names = rules
        .iter()
        .map(|rule| rule.name())
        .collect::<Vec<_>>()
        .join(", ");
    if findings.is_empty() {
        writeln!(
            stdout,
            "tree rules OK: {files} tracked files keep the rules {names}"
        )?;
        return Ok(ExitCode::SUCCESS);
    }
    for finding in &findings {
        writeln!(stderr, "{finding}")?;
    }
    writeln!(
        stderr,
        "tree rules FAILED: {} findings of the rules {names}",
        findings.len()
    )?;
    Ok(ExitCode::from(FOUND))
}

/// Parses the invocation, runs it and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits as [`run`] chooses; exits `2` when a stream cannot be
///   written, and after a usage message on standard error; exits `0` after
///   `--help` or `--version`.
/// - provides: the process boundary.
/// - fails: never; every fault is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a clean tree exits zero, a finding exits one and names
///   its path, a fault exits two.
/// - witness: `tests::cli::the_gate_names_each_finding_and_exits_one`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FOUND) || ret == ExitCode::from(FAULTED))]
fn main() -> ExitCode
{
    let cli = match <Cli as clap::Parser>::try_parse() {
        Ok(cli) => cli,
        Err(error) => {
            let code = if error.use_stderr() {
                ExitCode::from(FAULTED)
            }
            else {
                ExitCode::SUCCESS
            };
            return match error.print() {
                Ok(()) => code,
                Err(_unwritten) => ExitCode::from(FAULTED),
            };
        },
    };
    let rules: BTreeSet<Rule> = if cli.rules.is_empty() {
        Rule::ALL.into_iter().collect()
    }
    else {
        cli.rules.into_iter().collect()
    };
    let stdout = &mut std::io::stdout().lock();
    let stderr = &mut std::io::stderr().lock();
    run(&cli.root, &rules, cli.cost, stdout, stderr)
        .unwrap_or_else(|_unwritten| ExitCode::from(FAULTED))
}
