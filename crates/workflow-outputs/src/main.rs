//! `outputs`: the values of one kind of output for a tree, read from the store
//! or computed into it, and the difference of two trees.
//!
//! ```text
//! outputs compute <kind> [--revision <revision>] [--print] [--cost]
//! outputs difference <kind> --base <revision> [--head <revision>] [--lines <count>] [--cost]
//! ```
//!
//! A kind is `recovery`, the recovery record of a source, or `roles`, the
//! roles that the highlight gives a source.
//!
//! With no revision, the tree is the work tree with its changes. The store is
//! the directory that `GANDR_OUTPUT_STORE` names, or `target/outputs`.
//!
//! `compute --print` prints each source with its value on standard output.
//! A value of one line follows the name and a tab. A value of more lines
//! follows a line with the name, and each of its lines starts with a tab.
//! The count of the values goes to standard error.
//!
//! `difference` prints the count of the sources whose values differ between
//! the base and the head, then the first changes, one on each line. A tree
//! whose tool is the tool of this binary is computed in this run. A tree with
//! another tool is computed by the binary of its commit, in a checkout below
//! the target directory, unless the store holds each of its values.
//!
//! `difference` exits with 1 when values differ and no commit between the
//! base and the head names the kind in a trailer `Changes-output: <kind>`.
//! With no `--head`, the commits end at `HEAD`.
//!
//! `--cost` adds each part of the run with its count and its time.

use core::fmt::Write as _;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::ExitCode;
use std::time::Instant;

use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_workflow_outputs::checkout;
use gandr_workflow_outputs::compute;
use gandr_workflow_outputs::compute::Part;
use gandr_workflow_outputs::compute::Writer;
use gandr_workflow_outputs::difference;
use gandr_workflow_outputs::gauge;
use gandr_workflow_outputs::gauge::Gauge;
use gandr_workflow_outputs::recovery::Recorder;
use gandr_workflow_outputs::roles::Roles;
use gandr_workflow_outputs::store::Digest;
use gandr_workflow_outputs::store::Kind;
use gandr_workflow_outputs::store::Store;
use gandr_workflow_outputs::tree::Source;
use gandr_workflow_outputs::tree::Tree;
use gandr_workflow_outputs::word;
use gandr_workflow_outputs::workspace;

/// The workspace root: two directories above this package.
const WORKSPACE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");

/// The usage of the binary.
const USAGE: &str = "usage: outputs compute <kind> [--revision <revision>] [--print] [--cost]\n       outputs difference <kind> --base <revision> [--head <revision>] [--lines <count>] [--cost]\n       a kind is recovery or roles";

/// How many changes `difference` prints when the command line names no
/// count.
const LINES: usize = 16;

/// The values of a tree: each source with its value, in name order.
type Valued = Vec<(Source, Vec<u8>)>;

/// What the command line asks.
#[derive(Debug)]
struct Asked
{
    /// The kind of the values.
    kind: Kind,
    /// Whether the command is `difference`; else it is `compute`.
    difference: bool,
    /// The commit of `compute`, or the head of `difference`; none for the
    /// work tree.
    revision: Option<String>,
    /// The base of `difference`.
    base: Option<String>,
    /// How many changes `difference` prints.
    lines: Option<usize>,
    /// Whether `compute` prints each source with its value.
    print: bool,
    /// Whether the run prints the cost of each part.
    cost: bool,
}

/// Reads the command line: the command, the kind, then the flags.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The usage, when the command line is not one that the binary takes.
fn asked(arguments: &[String]) -> Result<Asked, String>
{
    let usage = || String::from(USAGE);
    let mut rest = arguments.iter();
    let difference = match rest.next().map(String::as_str) {
        Some("compute") => false,
        Some("difference") => true,
        _ => return Err(usage()),
    };
    let named = rest.next().ok_or_else(usage)?;
    let kind = compute::KINDS
        .into_iter()
        .find(|kind| kind.0 == named.as_str())
        .ok_or_else(usage)?;
    let mut asked = Asked {
        kind,
        difference,
        revision: None,
        base: None,
        lines: None,
        print: false,
        cost: false,
    };
    while let Some(flag) = rest.next() {
        let mut value = || rest.next().cloned().ok_or_else(usage);
        match (asked.difference, flag.as_str()) {
            (false, "--revision") | (true, "--head") => asked.revision = Some(value()?),
            (true, "--base") => asked.base = Some(value()?),
            (true, "--lines") => {
                asked.lines = Some(
                    value()?
                        .parse()
                        .map_err(|error| format!("--lines: {error}\n{USAGE}"))?,
                );
            },
            (false, "--print") => asked.print = true,
            (_, "--cost") => asked.cost = true,
            _ => return Err(usage()),
        }
    }
    if asked.difference && asked.base.is_none() {
        return Err(usage());
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

/// What every command reads: the workspace, the store, the packages of the
/// tool, and the parts of the run so far.
struct Run
{
    /// The workspace root.
    root: PathBuf,
    /// The store.
    store: Store,
    /// The directories of the packages that build the tool of the kind.
    packages: Vec<String>,
    /// The grammar, built when the run first computes a value.
    pbg: Option<Pbg>,
    /// The work tree and its tool, when the run has read them.
    work: Option<(Tree, Digest)>,
    /// The parts of the run, in their order.
    parts: Vec<Part>,
}

impl Run
{
    /// Reads the workspace root, the store and the packages of the tool.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The refusal of the workspace or of `cargo metadata`.
    fn start() -> Result<Self, String>
    {
        let root = Path::new(WORKSPACE)
            .canonicalize()
            .map_err(|error| format!("the workspace root: {error}"))?;
        let started = Instant::now();
        let metadata = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
            .args(["metadata", "--no-deps", "--format-version", "1", "--locked"])
            .current_dir(&root)
            .output()
            .map_err(|error| format!("cargo metadata: {error}"))?;
        let metadata: serde_json::Value = serde_json::from_slice(&metadata.stdout)
            .map_err(|error| format!("cargo metadata: {error}"))?;
        let packages = workspace::closure(&metadata, compute::TOOL_PACKAGE);
        let parts = vec![Part {
            name: "read the workspace",
            count: packages.len(),
            time: started.elapsed(),
        }];
        Ok(Self {
            store: Store::asked(&root),
            root,
            packages,
            pbg: None,
            work: None,
            parts,
        })
    }

    /// The tree of `revision`, or of the work tree, and its tool. A run reads
    /// the work tree one time.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The refusal of git.
    fn tree(
        &mut self,
        revision: Option<&str>,
    ) -> Result<(Tree, Digest), String>
    {
        if revision.is_none()
            && let Some(ref work) = self.work
        {
            return Ok(work.clone());
        }
        let started = Instant::now();
        let tree = revision
            .map_or_else(
                || Tree::of_work_tree(&self.root, &self.root.join("target")),
                |revision| Tree::of_revision(&self.root, revision),
            )
            .map_err(|error| error.to_string())?;
        let packages: Vec<&str> = self.packages.iter().map(String::as_str).collect();
        let tool = tree.tool(&packages).map_err(|error| error.to_string())?;
        self.parts.push(Part {
            name: "read a tree",
            count: 1,
            time: started.elapsed(),
        });
        if revision.is_none() {
            self.work = Some((tree.clone(), tool));
        }
        Ok((tree, tool))
    }

    /// The values of the kind `kind` of `tree` under `tool`, computed in this
    /// run.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The refusal of the grammar, of the tree or of the store.
    fn compute(
        &mut self,
        tree: &Tree,
        tool: &Digest,
        kind: Kind,
    ) -> Result<compute::Values, String>
    {
        if self.pbg.is_none() {
            let started = Instant::now();
            self.pbg = Some(built_in().map_err(|error| format!("the built-in grammar: {error}"))?);
            self.parts.push(Part {
                name: "build the grammar",
                count: 1,
                time: started.elapsed(),
            });
        }
        let pbg = self
            .pbg
            .as_ref()
            .ok_or_else(|| String::from("the grammar is not built"))?;
        let writer = if kind == compute::ROLES {
            Writer::Roles(Roles::new(pbg).map_err(|error| error.to_string())?)
        }
        else {
            Writer::Recovery(Recorder::new(pbg).map_err(|error| error.to_string())?)
        };
        let values =
            compute::values(&self.store, tree, tool, &writer).map_err(|error| error.to_string())?;
        self.parts.extend(values.parts.iter().copied());
        Ok(values)
    }

    /// The values of the kind `kind` of the side `revision`, from the store,
    /// from this run when its tool is `own`, or from the binary of its
    /// commit; and how many values the run computed.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The refusal of a tree, of the store, or of the binary of the commit.
    fn side(
        &mut self,
        revision: Option<&str>,
        own: &Digest,
        kind: Kind,
    ) -> Result<(Valued, usize), String>
    {
        let (tree, tool) = self.tree(revision)?;
        let held =
            compute::held(&self.store, &tree, &tool, kind).map_err(|error| error.to_string())?;
        let missing = held.missing();
        if missing == 0 {
            return Ok((held_values(held), 0));
        }
        if revision.is_none() || *own == tool {
            let values = self.compute(&tree, &tool, kind)?;
            return Ok((values.values, values.computed));
        }
        let commit = revision.unwrap_or("HEAD");
        let started = Instant::now();
        checkout::compute(&self.root, &self.store, kind, commit)?;
        self.parts.push(Part {
            name: "run the other tool",
            count: missing,
            time: started.elapsed(),
        });
        let held =
            compute::held(&self.store, &tree, &tool, kind).map_err(|error| error.to_string())?;
        let left = held.missing();
        if left > 0 {
            return Err(format!(
                "the tool of {commit} wrote {left} values fewer than its tree has"
            ));
        }
        Ok((held_values(held), missing))
    }
}

/// The values of `held`, each source with its value.
///
/// # Specification
/// trivial.
fn held_values(held: compute::Held) -> Vec<(Source, Vec<u8>)>
{
    held.sources
        .into_iter()
        .zip(held.values)
        .map(|(source, value)| (source, value.unwrap_or_default()))
        .collect()
}

/// The run of the command line `arguments`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The refusal of the command line, of the workspace, of the grammar, of a
/// tree or of the store, as one line; and a difference that no commit names.
fn run(arguments: &[String]) -> Result<(), String>
{
    let asked = asked(arguments)?;
    let kind = asked.kind;
    let name = kind.0;
    let mut run = Run::start()?;
    let mut out = String::new();
    let mut summary = String::new();
    let mut recomputed = None;
    let mut refusal = None;
    if asked.difference {
        let base = asked.base.as_deref().unwrap_or("HEAD");
        let head = asked.revision.as_deref();
        let own = run.tree(None)?.1;
        let (head_values, head_computed) = run.side(head, &own, kind)?;
        let (base_values, base_computed) = run.side(Some(base), &own, kind)?;
        let changes = difference::changes(&base_values, &head_values);
        let lines = asked.lines.unwrap_or(LINES);
        let _written = writeln!(
            out,
            "{name}: {} of {} sources differ between {base} and {}",
            changes.len(),
            head_values.len(),
            head.unwrap_or("the work tree")
        );
        for change in changes.iter().take(lines) {
            let _written = writeln!(out, "  {}", change.line());
        }
        if changes.len() > lines {
            let _written = writeln!(out, "  … {} more", changes.len().saturating_sub(lines));
        }
        let _written = writeln!(
            summary,
            "{name}: the head computed {head_computed} values, the base {base_computed}, in {}",
            run.store.root().display()
        );
        recomputed = Some(base_computed);
        if !changes.is_empty() && !word::named(&run.root, base, head, kind)? {
            refusal = Some(format!(
                "{name}: {} of {} sources differ, and no commit of {base}..{} has the trailer `{}: {name}`",
                changes.len(),
                head_values.len(),
                head.unwrap_or("HEAD"),
                word::TRAILER
            ));
        }
    }
    else {
        let (tree, tool) = run.tree(asked.revision.as_deref())?;
        let values = run.compute(&tree, &tool, kind)?;
        if asked.print {
            for &(ref source, ref value) in &values.values {
                let value = String::from_utf8_lossy(value);
                if value.lines().count() <= 1 {
                    let _written =
                        writeln!(out, "{}\t{}", source.name, value.trim_end_matches('\n'));
                }
                else {
                    let _written = writeln!(out, "{}", source.name);
                    for line in value.lines() {
                        let _written = writeln!(out, "\t{line}");
                    }
                }
            }
        }
        let _written = writeln!(
            summary,
            "{name}: {} sources, {} from the store, {} computed, in {}",
            values.values.len(),
            values.values.len().saturating_sub(values.computed),
            values.computed,
            run.store.root().display()
        );
    }
    let started = Instant::now();
    let mut gauges = vec![Gauge {
        name: "store size in bytes",
        value: gauge::size(&run.store).map_err(|error| format!("the store: {error}"))?,
        bound: gauge::bound("GANDR_OUTPUT_STORE_BOUND", gauge::STORE_BOUND),
    }];
    if let Some(count) = recomputed {
        gauges.push(Gauge {
            name: "recomputed base values",
            value: u64::try_from(count).unwrap_or(u64::MAX),
            bound: gauge::bound("GANDR_OUTPUT_RECOMPUTED_BOUND", gauge::RECOMPUTED_BOUND),
        });
    }
    for complaint in gauge::complain(&gauges) {
        let _written = writeln!(summary, "{complaint}");
    }
    run.parts.push(Part {
        name: "read the gauges",
        count: gauges.len(),
        time: started.elapsed(),
    });
    if asked.cost {
        for watched in &gauges {
            let _written = writeln!(
                summary,
                "  gauge {:<26} {:>12} of {}",
                watched.name, watched.value, watched.bound
            );
        }
        for part in &run.parts {
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
        .map_err(|error| format!("the output: {error}"))?;
    refusal.map_or(Ok(()), Err)
}
