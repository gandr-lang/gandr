//! `outputs`: the values of each asked kind of output for a tree, read from
//! the store or computed into it, and the difference of two trees.
//!
//! ```text
//! outputs compute <kinds> [--revision <revision>] [--print] [--cost]
//! outputs difference <kinds> --base <revision> [--head <revision>] [--lines <count>] [--cost]
//! ```
//!
//! A kind is `recovery`, the recovery record of a source, `refusals`, the
//! refusals that `gandr check` prints for a refusing source, or `roles`, the
//! roles that the highlight gives a source. `<kinds>` is one kind, two or
//! more kinds with a comma between them, or `all`. One run answers each kind
//! that it names, and reads each tree one time. `--print` takes one kind.
//!
//! One walk computes the refusals of each source of a tree, and it reads the
//! files of a checkout. The run walks its own work tree. The binary of a
//! commit walks any other tree, in the checkout below the target directory.
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
//! another tool is read from the list that the store holds for the tree. If
//! the store holds no list of it, the binary of its commit computes it, in a
//! checkout below the target directory. A commit whose binary does not have
//! the kind has no value of the kind, so each value of the head is a change.
//!
//! `difference` exits with 1 when values of a kind differ and no commit
//! between the base and the head names that kind in a trailer
//! `Changes-output: <kind>`. It prints one refusal for each such kind. With no
//! `--head`, the commits end at `HEAD`.
//!
//! `--cost` adds each part of the run with its count and its time.
//!
//! The binary exits with 2 when it refuses its command line: a command or a
//! kind that it does not have.

use core::fmt::Write as _;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_workflow_output_store::Digest;
use gandr_workflow_output_store::Kind;
use gandr_workflow_output_store::Store;
use gandr_workflow_outputs::checkout;
use gandr_workflow_outputs::compute;
use gandr_workflow_outputs::compute::Part;
use gandr_workflow_outputs::compute::Valued;
use gandr_workflow_outputs::compute::Writer;
use gandr_workflow_outputs::difference;
use gandr_workflow_outputs::gauge;
use gandr_workflow_outputs::gauge::Gauge;
use gandr_workflow_outputs::recovery::Recorder;
use gandr_workflow_outputs::roles::Roles;
use gandr_workflow_outputs::tree::Tree;
use gandr_workflow_outputs::word;
use gandr_workflow_outputs::workspace;

/// The workspace root: two directories above this package.
const WORKSPACE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");

/// The usage of the binary.
const USAGE: &str = "usage: outputs compute <kinds> [--revision <revision>] [--print] [--cost]\n       outputs difference <kinds> --base <revision> [--head <revision>] [--lines <count>] [--cost]\n       a kind is recovery, refusals or roles; <kinds> is one kind, kinds with a comma between them, or all\n       --print takes one kind";

/// How many changes `difference` prints when the command line names no
/// count.
const LINES: usize = 16;

/// What the command line asks.
#[derive(Debug)]
struct Asked
{
    /// The kinds of the values, each one time, in the order of the command
    /// line.
    kinds: Vec<Kind>,
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

/// Reads the command line: the command, the kinds, then the flags.
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
    let mut kinds: Vec<Kind> = Vec::new();
    for word in named.split(',') {
        let found: Vec<Kind> = compute::KINDS
            .into_iter()
            .filter(|kind| word == "all" || kind.0 == word)
            .collect();
        if found.is_empty() {
            return Err(usage());
        }
        for kind in found {
            if !kinds.contains(&kind) {
                kinds.push(kind);
            }
        }
    }
    let mut asked = Asked {
        kinds,
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
    if asked.print && asked.kinds.len() > 1 {
        return Err(usage());
    }
    Ok(asked)
}

/// Runs the command line, and writes a refusal as one line. A command line
/// that the binary does not take exits with
/// [`checkout::COMMAND_LINE_REFUSED`], so a run of a later binary can tell
/// that this one does not have a kind.
///
/// # Specification
/// trivial.
fn main() -> ExitCode
{
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let asked = match asked(&arguments) {
        Ok(asked) => asked,
        Err(usage) => {
            let _written = writeln!(std::io::stderr().lock(), "outputs: {usage}");
            return ExitCode::from(checkout::COMMAND_LINE_REFUSED);
        },
    };
    match run(&asked) {
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
    /// For each kind, the directories of the packages that compute it.
    packages: Vec<(Kind, Vec<String>)>,
    /// The directories of the packages that build the binary.
    manifests: Vec<String>,
    /// The grammar, built when the run first computes a value.
    pbg: Option<Pbg>,
    /// Each tree that the run has read, with its revision. The work tree has
    /// no revision.
    trees: Vec<(Option<String>, Tree)>,
    /// The tool of each kind in each tree that the run has asked for, by the
    /// git tree identifier.
    tools: Vec<(String, Kind, Digest)>,
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
        let metadata = workspace::metadata(&root)?;
        let manifests = workspace::closure(&metadata, compute::TOOL_PACKAGE);
        let packages = compute::KINDS
            .iter()
            .map(|&kind| (kind, compute::tool_packages(&metadata, kind)))
            .collect();
        let parts = vec![Part {
            name: "read the workspace",
            count: manifests.len(),
            time: started.elapsed(),
        }];
        Ok(Self {
            store: Store::asked(&root),
            root,
            packages,
            manifests,
            pbg: None,
            trees: Vec::new(),
            tools: Vec::new(),
            parts,
        })
    }

    /// The tree of `revision`, or of the work tree. A run reads each tree one
    /// time.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The refusal of git.
    fn tree(
        &mut self,
        revision: Option<&str>,
    ) -> Result<Tree, String>
    {
        if let Some(&(_, ref tree)) = self
            .trees
            .iter()
            .find(|&&(ref read, _)| read.as_deref() == revision)
        {
            return Ok(tree.clone());
        }
        let started = Instant::now();
        let tree = revision
            .map_or_else(
                || Tree::of_work_tree(&self.root, &self.root.join("target")),
                |revision| Tree::of_revision(&self.root, revision),
            )
            .map_err(|error| error.to_string())?;
        self.parts.push(Part {
            name: "read a tree",
            count: 1,
            time: started.elapsed(),
        });
        self.trees.push((revision.map(str::to_owned), tree.clone()));
        Ok(tree)
    }

    /// The tool of the kind `kind` in `tree`. A run reads each tool one time.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The refusal of git.
    fn tool(
        &mut self,
        tree: &Tree,
        kind: Kind,
    ) -> Result<Digest, String>
    {
        if let Some(&(_, _, tool)) = self
            .tools
            .iter()
            .find(|&&(ref id, held, _)| id == tree.id() && held == kind)
        {
            return Ok(tool);
        }
        let started = Instant::now();
        let packages: Vec<&str> = self
            .packages
            .iter()
            .find(|&&(held, _)| held == kind)
            .map_or_else(Vec::new, |&(_, ref directories)| {
                directories.iter().map(String::as_str).collect()
            });
        let manifests: Vec<&str> = self.manifests.iter().map(String::as_str).collect();
        let tool = tree
            .tool(&packages, &manifests)
            .map_err(|error| error.to_string())?;
        self.parts.push(Part {
            name: "read a tool",
            count: packages.len(),
            time: started.elapsed(),
        });
        self.tools.push((tree.id().to_owned(), kind, tool));
        Ok(tool)
    }

    /// The values of the kind `kind` of `tree` under `tool`, computed in this
    /// run, or `None` when the kind needs the files of the tree and the work
    /// tree does not hold them.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The refusal of the grammar, of the tree, of the walk or of the store.
    fn compute(
        &mut self,
        tree: &Tree,
        tool: &Digest,
        kind: Kind,
    ) -> Result<Option<compute::Values>, String>
    {
        if kind == compute::REFUSALS {
            let work = self.tree(None)?;
            let checkout = (work.id() == tree.id()).then(|| self.root.clone());
            let values = compute::refusals(&self.store, tree, tool, checkout.as_deref())
                .map_err(|error| error.to_string())?;
            if let Some(ref values) = values {
                self.parts.extend(values.parts.iter().copied());
            }
            return Ok(values);
        }
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
        Ok(Some(values))
    }

    /// The values of the kind `kind` of the side `revision`, and how many
    /// values the run computed. This run computes the work tree and a tree
    /// whose tool is `own`. It reads another tree from the list of the
    /// tree, or lets the binary of its commit compute it. A commit whose
    /// binary does not have the kind gives no value.
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
        let tree = self.tree(revision)?;
        let tool = self.tool(&tree, kind)?;
        if (revision.is_none() || *own == tool)
            && let Some(values) = self.compute(&tree, &tool, kind)?
        {
            return Ok((values.values, values.computed));
        }
        let started = Instant::now();
        let listed =
            compute::listed(&self.store, &tree, kind).map_err(|error| error.to_string())?;
        self.parts.push(Part {
            name: "read the list",
            count: listed.as_ref().map_or(0, Vec::len),
            time: started.elapsed(),
        });
        if let Some(values) = listed {
            return Ok((values, 0));
        }
        let commit = revision.unwrap_or("HEAD");
        let started = Instant::now();
        let values = if checkout::compute(&self.root, &self.store, kind, commit)? {
            compute::listed(&self.store, &tree, kind)
                .map_err(|error| error.to_string())?
                .ok_or_else(|| format!("the tool of {commit} wrote no list of its tree"))?
        }
        else {
            Vec::new()
        };
        let count = values.len();
        self.parts.push(Part {
            name: "run the other tool",
            count,
            time: started.elapsed(),
        });
        Ok((values, count))
    }
}

/// The difference of the kind `kind` between the base and the head of
/// `asked`: its lines go to `out` and its cost line to `summary`. Gives how
/// many values of the base the run computed, and the refusal when values
/// differ and no commit names the kind.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The refusal of a tree, of the store, of the binary of a commit or of git.
fn differ(
    run: &mut Run,
    asked: &Asked,
    kind: Kind,
    out: &mut String,
    summary: &mut String,
) -> Result<(usize, Option<String>), String>
{
    let name = kind.0;
    let base = asked.base.as_deref().unwrap_or("HEAD");
    let head = asked.revision.as_deref();
    let work = run.tree(None)?;
    let own = run.tool(&work, kind)?;
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
    let refusal = (!changes.is_empty() && !word::named(&run.root, base, head, kind)?).then(|| {
        format!(
            "{name}: {} of {} sources differ, and no commit of {base}..{} has the trailer `{}: {name}`",
            changes.len(),
            head_values.len(),
            head.unwrap_or("HEAD"),
            word::TRAILER
        )
    });
    Ok((base_computed, refusal))
}

/// The values of the kind `kind` of the tree of `asked`: each source with its
/// value goes to `out` when the command line asks, and the count line to
/// `summary`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The refusal of the grammar, of the tree or of the store.
fn computed(
    run: &mut Run,
    asked: &Asked,
    kind: Kind,
    out: &mut String,
    summary: &mut String,
) -> Result<(), String>
{
    let name = kind.0;
    let tree = run.tree(asked.revision.as_deref())?;
    let tool = run.tool(&tree, kind)?;
    let values = run.compute(&tree, &tool, kind)?.ok_or_else(|| {
        format!(
            "{name}: the work tree does not hold the files of {}, and the store has no list of them",
            asked.revision.as_deref().unwrap_or("the tree")
        )
    })?;
    if asked.print {
        for &(ref source, ref value) in &values.values {
            let value = String::from_utf8_lossy(value);
            if value.lines().count() <= 1 {
                let _written = writeln!(out, "{}\t{}", source.name, value.trim_end_matches('\n'));
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
    Ok(())
}

/// The run of the command line `asked`: each kind in its order, then the
/// gauges.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The refusal of the workspace, of the grammar, of a tree or of the store,
/// as one line; and one line for each kind with a difference that no commit
/// names.
fn run(asked: &Asked) -> Result<(), String>
{
    let mut run = Run::start()?;
    let mut out = String::new();
    let mut summary = String::new();
    let mut recomputed: Option<usize> = None;
    let mut refusals: Vec<String> = Vec::new();
    for &kind in &asked.kinds {
        if asked.difference {
            let (base_computed, refusal) = differ(&mut run, asked, kind, &mut out, &mut summary)?;
            recomputed = Some(recomputed.map_or(base_computed, |most| most.max(base_computed)));
            refusals.extend(refusal);
        }
        else {
            computed(&mut run, asked, kind, &mut out, &mut summary)?;
        }
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
    if refusals.is_empty() {
        Ok(())
    }
    else {
        Err(refusals.join("\noutputs: "))
    }
}

#[cfg(test)]
mod tests
{
    use super::asked;
    use super::compute;

    /// A command line names one kind, kinds with a comma between them, or
    /// `all`. Each kind goes into the run one time, in the order of the
    /// command line. A word that is no kind is refused, and so is `--print`
    /// with two kinds.
    #[test]
    fn a_command_line_names_its_kinds()
    {
        let kinds = |word: &str| {
            asked(&[String::from("compute"), String::from(word)]).map(|asked| asked.kinds)
        };
        assert_eq!(kinds("roles"), Ok(vec![compute::ROLES]));
        assert_eq!(
            kinds("roles,recovery,roles"),
            Ok(vec![compute::ROLES, compute::RECOVERY])
        );
        assert_eq!(kinds("all"), Ok(compute::KINDS.to_vec()));
        assert!(kinds("roles,molds").is_err(), "`molds` is no kind");
        let printed = asked(&[
            String::from("compute"),
            String::from("all"),
            String::from("--print"),
        ]);
        assert!(printed.is_err(), "`--print` takes one kind");
    }
}
