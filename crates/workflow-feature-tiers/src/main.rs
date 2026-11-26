//! `feature-tiers`: a spike that measures the seams of the workspace against
//! the features ledger and the corpus.
//!
//! | Table | What it answers |
//! | --- | --- |
//! | layers | how many crates and tests a build needs below each root |
//! | seams | what leaves the build of the driver when one crate is optional |
//! | ledger | how many rows name a crate, a source, or both |
//! | corpus | how many sources a row of the ledger names |
//! | rules | how many sources use each grammar rule, and how many fit a rule set |
//!
//! A run starts `cargo metadata` one time, reads each row of the features
//! ledger one time, and parses each source of `corpus/` and `library/` one
//! time. It prints each part with its count and its time to standard error.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::time::Instant;

use gandr_surface_features::FeatureLedger;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use serde_json::Value;

/// The roots of the layers table, each a package of the workspace.
const ROOTS: [&str; 8] = [
    "gandr-kernel-core",
    "gandr-core-term",
    "gandr-core-checker",
    "gandr-surface-parser",
    "gandr-surface-lowering",
    "gandr-surface-dispatcher",
    "gandr-surface-evaluate",
    "gandr-lang",
];

/// The package that each seam is measured against.
const DRIVER: &str = "gandr-lang";

/// The crates of the workspace and the dependencies between them.
struct Workspace
{
    /// The name of each package, in the order of the names.
    names: Vec<String>,
    /// For each package, the packages of the workspace that it depends on
    /// outside its tests and its build script.
    depends: Vec<Vec<usize>>,
    /// For each package, the count of `#[test]` lines below its directory.
    tests: Vec<usize>,
}

impl Workspace
{
    /// The workspace at `root`, from one run of `cargo metadata`.
    fn read(root: &Path) -> Result<Self, String>
    {
        let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
        let output = Command::new(cargo)
            .args(["metadata", "--format-version", "1", "--no-deps", "--offline"])
            .current_dir(root)
            .output()
            .map_err(|error| format!("`cargo metadata` did not run: {error}"))?;
        if !output.status.success() {
            return Err(format!(
                "`cargo metadata` failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        let metadata: Value = serde_json::from_slice(&output.stdout)
            .map_err(|error| format!("the metadata does not read: {error}"))?;
        let packages = metadata
            .get("packages")
            .and_then(Value::as_array)
            .ok_or("the metadata has no packages")?;
        let mut rows: Vec<(String, PathBuf, Vec<String>)> = Vec::new();
        for package in packages {
            let name = package
                .get("name")
                .and_then(Value::as_str)
                .ok_or("a package has no name")?;
            let manifest = package
                .get("manifest_path")
                .and_then(Value::as_str)
                .ok_or("a package has no manifest")?;
            let directory = Path::new(manifest)
                .parent()
                .ok_or("a manifest has no directory")?
                .to_path_buf();
            let depends = package
                .get("dependencies")
                .and_then(Value::as_array)
                .map(|dependencies| {
                    dependencies
                        .iter()
                        .filter(|dependency| dependency.get("kind").is_some_and(Value::is_null))
                        .filter_map(|dependency| dependency.get("name").and_then(Value::as_str))
                        .map(String::from)
                        .collect()
                })
                .unwrap_or_default();
            rows.push((String::from(name), directory, depends));
        }
        rows.sort();
        let index: BTreeMap<&str, usize> = rows
            .iter()
            .enumerate()
            .map(|(position, row)| (row.0.as_str(), position))
            .collect();
        let depends = rows
            .iter()
            .map(|row| {
                row.2
                    .iter()
                    .filter_map(|name| index.get(name.as_str()).copied())
                    .collect()
            })
            .collect();
        let tests = rows.iter().map(|row| test_lines(&row.1)).collect();
        Ok(Self {
            names: rows.iter().map(|row| row.0.clone()).collect(),
            depends,
            tests,
        })
    }

    /// The position of the package `name`.
    fn position(
        &self,
        name: &str,
    ) -> Option<usize>
    {
        self.names.iter().position(|known| known == name)
    }

    /// Each package that `root` reaches, `root` too, on a walk that does not
    /// enter `without`.
    fn closure(
        &self,
        root: usize,
        without: Option<usize>,
    ) -> Vec<bool>
    {
        let mut reached = vec![false; self.names.len()];
        let mut work = vec![root];
        while let Some(package) = work.pop() {
            if Some(package) == without || reached[package] {
                continue;
            }
            reached[package] = true;
            work.extend(self.depends[package].iter().copied());
        }
        reached
    }

    /// The count of the tests of the packages that `set` marks.
    fn tests_of(
        &self,
        set: &[bool],
    ) -> usize
    {
        set.iter()
            .zip(&self.tests)
            .filter_map(|(&marked, &tests)| marked.then_some(tests))
            .sum()
    }

    /// The name of a package with no `gandr-` at its head, as the ledger
    /// writes it.
    fn short(
        &self,
        package: usize,
    ) -> &str
    {
        let name = self.names[package].as_str();
        name.strip_prefix("gandr-").unwrap_or(name)
    }
}

/// The count of `#[test]` lines of the Rust sources below `directory`.
fn test_lines(directory: &Path) -> usize
{
    let mut count = 0;
    walk(directory, "rs", &mut |path| {
        if let Ok(text) = std::fs::read_to_string(path) {
            count += text
                .lines()
                .filter(|line| line.trim_start().starts_with("#[test]"))
                .count();
        }
    });
    count
}

/// Give `visit` each file below `directory` whose extension is `extension`,
/// in the order of the paths. A directory `target` is not entered.
fn walk(
    directory: &Path,
    extension: &str,
    visit: &mut dyn FnMut(&Path),
)
{
    let Ok(entries) = std::fs::read_dir(directory)
    else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .collect();
    paths.sort();
    for path in paths {
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name != "target") {
                walk(&path, extension, visit);
            }
        } else if path.extension().is_some_and(|found| found == extension) {
            visit(&path);
        }
    }
}

/// One row of the features ledger, as the tables read it.
struct Row
{
    /// `area`.
    area: String,
    /// `status`.
    status: String,
    /// The crates of `crate`.
    crates: Vec<String>,
    /// Each path of `corpus` and of `exemplar` that ends in `.gandr`.
    sources: Vec<String>,
}

/// The rows of the features ledger under `root`.
fn rows(root: &Path) -> Result<Vec<Row>, String>
{
    let ledger = FeatureLedger::read(root).map_err(|fault| fault.to_string())?;
    let listed = ledger
        .listed(None, None)
        .map_err(|fault| fault.to_string())?;
    Ok(listed
        .iter()
        .map(|feature| {
            let json = feature.json();
            let text = |column: &str| {
                json.get(column)
                    .and_then(Value::as_str)
                    .unwrap_or_default()
                    .to_owned()
            };
            let mut sources: Vec<String> = text("corpus")
                .split_whitespace()
                .chain(text("exemplar").split_whitespace())
                .filter(|path| path.ends_with(".gandr"))
                .map(String::from)
                .collect();
            sources.sort();
            sources.dedup();
            Row {
                area: text("area"),
                status: text("status"),
                crates: text("crate").split_whitespace().map(String::from).collect(),
                sources,
            }
        })
        .collect())
}

/// A percentage of `part` in `whole`, as a whole number.
fn share(
    part: usize,
    whole: usize,
) -> usize
{
    if whole == 0 { 0 } else { (part * 100 + whole / 2) / whole }
}

/// The run: read the three records, then print the five tables.
fn run(
    root: &Path,
    tier0: &[PathBuf],
) -> Result<(), String>
{
    let start = Instant::now();
    let workspace = Workspace::read(root)?;
    eprintln!(
        "metadata: {} packages, {} ms",
        workspace.names.len(),
        start.elapsed().as_millis()
    );
    let start = Instant::now();
    let rows = rows(root)?;
    eprintln!("ledger: {} rows, {} ms", rows.len(), start.elapsed().as_millis());

    let driver = workspace
        .position(DRIVER)
        .ok_or("the workspace has no driver")?;
    let all_tests: usize = workspace.tests.iter().sum();
    let whole = workspace.closure(driver, None);
    let whole_count = whole.iter().filter(|&&marked| marked).count();

    println!("## layers\n");
    println!("| Root | Crates below it | Tests in them | Share of the {all_tests} tests |");
    println!("| ---- | --------------- | ------------- | ----- |");
    for name in ROOTS {
        let Some(package) = workspace.position(name)
        else {
            continue;
        };
        let reached = workspace.closure(package, None);
        let tests = workspace.tests_of(&reached);
        println!(
            "| `{}` | {} | {} | {} % |",
            workspace.short(package),
            reached.iter().filter(|&&marked| marked).count(),
            tests,
            share(tests, all_tests)
        );
    }

    let mut named: BTreeMap<&str, usize> = BTreeMap::new();
    for row in &rows {
        for name in &row.crates {
            *named.entry(name.as_str()).or_default() += 1;
        }
    }

    println!("\n## seams\n");
    println!(
        "The driver reaches {whole_count} crates. A row is one crate as an optional dependency of \
         each crate that names it.\n"
    );
    println!(
        "| Crate | Manifests that name it | Crates that leave with it | Tests that leave | Rows of \
         the ledger that name it |"
    );
    println!("| ----- | ---------------------- | ------------------------- | ---------------- | --- |");
    let mut seams: Vec<(usize, usize, usize, usize)> = Vec::new();
    for package in 0..workspace.names.len() {
        if package == driver || !whole[package] {
            continue;
        }
        let kept = workspace.closure(driver, Some(package));
        let left: Vec<bool> = whole
            .iter()
            .zip(&kept)
            .map(|(&before, &after)| before && !after)
            .collect();
        let dependents = (0..workspace.names.len())
            .filter(|&other| whole[other] && workspace.depends[other].contains(&package))
            .count();
        seams.push((
            package,
            dependents,
            left.iter().filter(|&&marked| marked).count(),
            workspace.tests_of(&left),
        ));
    }
    seams.sort_by_key(|&(package, dependents, _, tests)| {
        (dependents, core::cmp::Reverse(tests), package)
    });
    for (package, dependents, left, tests) in seams {
        println!(
            "| `{}` | {} | {} | {} | {} |",
            workspace.short(package),
            dependents,
            left,
            tests,
            named.get(workspace.short(package)).copied().unwrap_or(0)
        );
    }

    println!("\n## ledger\n");
    println!("| Area | Rows | Implemented or partial | Name a crate | Name a source | Name both |");
    println!("| ---- | ---- | ---------------------- | ------------ | ------------- | --------- |");
    let mut areas: BTreeMap<&str, [usize; 5]> = BTreeMap::new();
    for row in &rows {
        let counts = areas.entry(row.area.as_str()).or_default();
        let met = matches!(row.status.as_str(), "implemented" | "partial");
        let crates = !row.crates.is_empty();
        let sources = !row.sources.is_empty();
        counts[0] += 1;
        counts[1] += usize::from(met);
        counts[2] += usize::from(crates);
        counts[3] += usize::from(sources);
        counts[4] += usize::from(crates && sources);
    }
    let mut total = [0_usize; 5];
    for (area, counts) in &areas {
        println!(
            "| {area} | {} | {} | {} | {} | {} |",
            counts[0], counts[1], counts[2], counts[3], counts[4]
        );
        for (sum, count) in total.iter_mut().zip(counts) {
            *sum += count;
        }
    }
    println!(
        "| all | {} | {} | {} | {} | {} |",
        total[0], total[1], total[2], total[3], total[4]
    );
    let unnamed: Vec<&str> = (0..workspace.names.len())
        .filter(|&package| whole[package] && !named.contains_key(workspace.short(package)))
        .map(|package| workspace.short(package))
        .collect();
    println!(
        "\nNo row names {} of the {whole_count} crates: {}.",
        unnamed.len(),
        unnamed.join(", ")
    );

    let start = Instant::now();
    let pbg = built_in().map_err(|error| format!("the grammar does not build: {error}"))?;
    let mut sources: Vec<PathBuf> = Vec::new();
    for folder in ["corpus", "library"] {
        walk(&root.join(folder), "gandr", &mut |path| sources.push(path.to_path_buf()));
    }
    let mut uses: Vec<Option<BTreeSet<&'static str>>> = Vec::with_capacity(sources.len());
    for path in &sources {
        let used = std::fs::read_to_string(path).ok().and_then(|text| {
            let parsed = parse(&pbg, SourceText::from(text.as_str())).ok()?;
            let tree = parsed.tree();
            let mut used = BTreeSet::new();
            for position in tree.positions() {
                if let Some(node) = tree.node(position)
                    && let NodeLabel::Meld(mold) | NodeLabel::Tile(mold) = node.label()
                    && let Ok(rule) = pbg.rule_of(mold)
                {
                    let _new = used.insert(rule.name);
                }
            }
            Some(used)
        });
        uses.push(used);
    }
    eprintln!(
        "corpus: {} sources, {} ms",
        sources.len(),
        start.elapsed().as_millis()
    );

    let mut witnesses: BTreeMap<&str, usize> = BTreeMap::new();
    for row in &rows {
        for source in &row.sources {
            *witnesses.entry(source.as_str()).or_default() += 1;
        }
    }
    println!("\n## corpus\n");
    println!("| Folder | Sources | A row names it | It does not parse |");
    println!("| ------ | ------- | -------------- | ----------------- |");
    let mut folders: BTreeMap<String, [usize; 3]> = BTreeMap::new();
    for (path, used) in sources.iter().zip(&uses) {
        let relative = path.strip_prefix(root).unwrap_or(path);
        let folder: PathBuf = relative.components().take(2).collect();
        let counts = folders.entry(folder.display().to_string()).or_default();
        counts[0] += 1;
        counts[1] += usize::from(witnesses.contains_key(relative.to_string_lossy().as_ref()));
        counts[2] += usize::from(used.is_none());
    }
    let mut total = [0_usize; 3];
    for (folder, counts) in &folders {
        println!("| `{folder}` | {} | {} | {} |", counts[0], counts[1], counts[2]);
        for (sum, count) in total.iter_mut().zip(counts) {
            *sum += count;
        }
    }
    println!("| all | {} | {} | {} |", total[0], total[1], total[2]);

    let parsed: Vec<&BTreeSet<&'static str>> = uses.iter().flatten().collect();
    let mut frequency: BTreeMap<&'static str, usize> = BTreeMap::new();
    for used in &parsed {
        for &rule in *used {
            *frequency.entry(rule).or_default() += 1;
        }
    }
    let mut ranked: Vec<(&'static str, usize)> = frequency.into_iter().collect();
    ranked.sort_by_key(|&(rule, count)| (core::cmp::Reverse(count), rule));
    println!("\n## rules\n");
    println!(
        "The grammar has {} rules. The {} sources that parse use {} of them.\n",
        pbg.rules().len(),
        parsed.len(),
        ranked.len()
    );
    println!("| The rules that most sources use | Sources that use no other rule | Share |");
    println!("| ------------------------------- | ------------------------------ | ----- |");
    for count in [10, 15, 20, 25, 30, 40, 50, 60, 80, 100, ranked.len()] {
        if count > ranked.len() {
            continue;
        }
        let permitted: BTreeSet<&str> = ranked.iter().take(count).map(|&(rule, _)| rule).collect();
        let fit = parsed
            .iter()
            .filter(|used| used.iter().all(|rule| permitted.contains(rule)))
            .count();
        println!("| the first {count} | {fit} | {} % |", share(fit, parsed.len()));
    }
    println!("\n| Rule | Sources that use it |");
    println!("| ---- | ------------------- |");
    for (rule, count) in &ranked {
        println!("| `{rule}` | {count} |");
    }

    if !tier0.is_empty() {
        let mut permitted: BTreeSet<&'static str> = BTreeSet::new();
        for path in tier0 {
            let position = sources
                .iter()
                .position(|source| source == &root.join(path))
                .ok_or_else(|| format!("`{}` is no source of the corpus", path.display()))?;
            let used = uses[position]
                .as_ref()
                .ok_or_else(|| format!("`{}` does not parse", path.display()))?;
            permitted.extend(used.iter().copied());
        }
        let fit = parsed
            .iter()
            .filter(|used| used.iter().all(|rule| permitted.contains(rule)))
            .count();
        println!("\n## the candidate rule set\n");
        println!(
            "The {} named sources use {} rules: {}.\n",
            tier0.len(),
            permitted.len(),
            permitted
                .iter()
                .map(|rule| format!("`{rule}`"))
                .collect::<Vec<_>>()
                .join(", ")
        );
        println!(
            "{fit} of the {} sources that parse use no other rule: {} %.",
            parsed.len(),
            share(fit, parsed.len())
        );
    }
    Ok(())
}

fn main() -> std::process::ExitCode
{
    let mut root = PathBuf::from(".");
    let mut tier0 = Vec::new();
    let mut arguments = std::env::args_os().skip(1);
    while let Some(argument) = arguments.next() {
        let value = arguments.next().map(PathBuf::from);
        match (argument.to_str(), value) {
            (Some("--root"), Some(value)) => root = value,
            (Some("--tier0"), Some(value)) => tier0.push(value),
            _ => {
                eprintln!("usage: feature-tiers [--root <directory>] [--tier0 <source>]...");
                return std::process::ExitCode::from(2);
            },
        }
    }
    match run(&root, &tier0) {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(fault) => {
            eprintln!("feature-tiers: {fault}");
            std::process::ExitCode::FAILURE
        },
    }
}
