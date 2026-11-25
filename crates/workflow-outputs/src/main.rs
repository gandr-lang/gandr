//! `outputs`: the values of one kind of output for a tree, read from the store
//! or computed into it.
//!
//! ```text
//! outputs compute recovery [--revision <revision>] [--print] [--cost]
//! ```
//!
//! With no revision, the tree is the work tree with its changes. The store is
//! the directory that `GANDR_OUTPUT_STORE` names, or `target/outputs`.
//! `--print` prints each source with its value on standard output: the name,
//! a tab and the value. The count of the values goes to standard error, and
//! `--cost` adds each part of the run with its count and its time.

use core::fmt::Write as _;
use std::io::Write as _;
use std::path::Path;
use std::process::Command;
use std::process::ExitCode;
use std::time::Instant;

use gandr_surface_grammar::built_in;
use gandr_workflow_outputs::compute;
use gandr_workflow_outputs::compute::Part;
use gandr_workflow_outputs::recovery::Recorder;
use gandr_workflow_outputs::store::Store;
use gandr_workflow_outputs::tree::Tree;
use gandr_workflow_outputs::workspace;

/// The workspace root: two directories above this package.
const WORKSPACE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");

/// What the command line asks.
#[derive(Debug, Default)]
struct Asked
{
    /// The commit whose tree the run reads, or none for the work tree.
    revision: Option<String>,
    /// Whether the run prints each source with its value.
    print: bool,
    /// Whether the run prints the cost of each part.
    cost: bool,
}

/// Reads the command line: `compute recovery`, then the flags.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The usage line, when the command line is not one that the binary takes.
fn asked(arguments: &[String]) -> Result<Asked, String>
{
    let usage =
        String::from("usage: outputs compute recovery [--revision <revision>] [--print] [--cost]");
    let mut rest = arguments.iter();
    if rest.next().map(String::as_str) != Some("compute")
        || rest.next().map(String::as_str) != Some("recovery")
    {
        return Err(usage);
    }
    let mut asked = Asked::default();
    while let Some(flag) = rest.next() {
        match flag.as_str() {
            "--revision" => {
                asked.revision = Some(rest.next().ok_or_else(|| usage.clone())?.clone());
            },
            "--print" => asked.print = true,
            "--cost" => asked.cost = true,
            _ => return Err(usage),
        }
    }
    Ok(asked)
}

/// Runs the command line, and writes a refusal as one line.
///
/// # Specification
/// trivial.
fn main() -> ExitCode
{
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    match run(&arguments) {
        Ok(()) => ExitCode::SUCCESS,
        Err(refusal) => {
            let _written = writeln!(std::io::stderr().lock(), "outputs: {refusal}");
            ExitCode::FAILURE
        },
    }
}

/// The run of the command line `arguments`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The refusal of the command line, of the workspace, of the grammar, of the
/// tree or of the store, as one line.
fn run(arguments: &[String]) -> Result<(), String>
{
    let asked = asked(arguments)?;
    let root = Path::new(WORKSPACE)
        .canonicalize()
        .map_err(|error| format!("the workspace root: {error}"))?;
    let store = Store::asked(&root);
    let scratch = root.join("target");
    let started = Instant::now();
    let tree = asked
        .revision
        .as_deref()
        .map_or_else(
            || Tree::of_work_tree(&root, &scratch),
            |revision| Tree::of_revision(&root, revision),
        )
        .map_err(|error| error.to_string())?;
    let mut parts = vec![Part {
        name: "read the tree",
        count: 1,
        time: started.elapsed(),
    }];
    let started = Instant::now();
    let metadata = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
        .args(["metadata", "--no-deps", "--format-version", "1", "--locked"])
        .current_dir(&root)
        .output()
        .map_err(|error| format!("cargo metadata: {error}"))?;
    let metadata: serde_json::Value = serde_json::from_slice(&metadata.stdout)
        .map_err(|error| format!("cargo metadata: {error}"))?;
    let packages = workspace::closure(&metadata, compute::RECOVERY_PACKAGE);
    let packages: Vec<&str> = packages.iter().map(String::as_str).collect();
    let tool = tree.tool(&packages).map_err(|error| error.to_string())?;
    parts.push(Part {
        name: "digest the tool",
        count: packages.len(),
        time: started.elapsed(),
    });
    let started = Instant::now();
    let pbg = built_in().map_err(|error| format!("the built-in grammar: {error}"))?;
    let recorder = Recorder::new(&pbg).map_err(|error| error.to_string())?;
    parts.push(Part {
        name: "build the grammar",
        count: 1,
        time: started.elapsed(),
    });
    let values =
        compute::recovery(&store, &tree, &tool, &recorder).map_err(|error| error.to_string())?;
    parts.extend(values.parts.iter().copied());
    let mut out = String::new();
    if asked.print {
        for &(ref source, ref value) in &values.values {
            let _written = write!(out, "{}\t{}", source.name, String::from_utf8_lossy(value));
        }
    }
    let mut summary = String::new();
    let _written = writeln!(
        summary,
        "recovery: {} sources, {} from the store, {} computed, in {}",
        values.values.len(),
        values.values.len().saturating_sub(values.computed),
        values.computed,
        store.root().display()
    );
    if asked.cost {
        for part in &parts {
            let _written = writeln!(
                summary,
                "  {:<20} {:>6} {:>10.3} s",
                part.name,
                part.count,
                part.time.as_secs_f64()
            );
        }
    }
    let _summarised = std::io::stderr().lock().write_all(summary.as_bytes());
    std::io::stdout()
        .lock()
        .write_all(out.as_bytes())
        .map_err(|error| format!("the output: {error}"))
}
