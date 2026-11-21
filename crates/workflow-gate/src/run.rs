//! One run: what it reads of the worktree, what it asks git, and the lists
//! that it gives.

use alloc::collections::BTreeMap;
use core::fmt::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::time::Instant;

use crate::call::Answer;
use crate::call::Part;
use crate::call::Parts;
use crate::call::Program;
use crate::error::GateError;
use crate::list::Digest;
use crate::list::List;
use crate::list::Listed;
use crate::name::Check;
use crate::name::Commit;
use crate::name::Scope;
use crate::tables::CheckRow;
use crate::tables::Table;
use crate::tables::Tables;
use crate::tables::Tasks;
use crate::tables::Workspace;

/// The path of the gate's table in a commit.
const TABLE: &str = ".config/gate-scope/table.json";

/// What a caller asks of one run: each check at each commit, over one scope.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Request
{
    /// Each commit, or tree, of the run.
    pub commits: Vec<Commit>,
    /// Each check of the run.
    pub checks: Vec<Check>,
    /// The scope of each check.
    pub scope: Scope,
    /// The directory of `inputs.json` and `verdicts.json`. With none, the
    /// run reads `.config/gate-scope` of the worktree.
    pub tables: Option<PathBuf>,
}

/// The table of each commit, from what one `git cat-file --batch` printed.
///
/// # Specification
/// - requires: `answer` is what git printed for one name of each commit, in the
///   order of the commits.
/// - ensures: one table for each commit, in that order. A commit that holds no
///   table has the empty table.
/// - provides: the rows of the checks of the table at each commit, from one
///   start of git.
/// - fails: [`GateError::Read`] when git printed fewer tables than commits.
/// - panics: none.
/// - executable: none — the reference is the script before this crate, whose
///   digests the cases pin.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: one table for each commit, growth within the commits of the
///   request
///
/// # Adequacy
/// - hypothesis: L2 — the digests of the script for a check of the table at two
///   trees with different files of `docs/`, and at a tree whose table the
///   fixture holds; the table of the first commit for each commit reads one row
///   two times and still gives two digests, so the witness of the order is the
///   pair of digests in the order of the commits.
/// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
/// - witness: `tests::cli::a_table_check_reads_its_row_at_the_commit_and_starts_no_cargo`
#[inline]
fn landing(
    answer: &Answer,
    commits: &[Commit],
) -> Result<Vec<Table>, GateError>
{
    let short = || GateError::Read {
        what: "git cat-file --batch".to_owned(),
        reason: "fewer tables than commits".to_owned(),
    };
    let text = String::from_utf8_lossy(answer.as_ref());
    let mut rest: &str = &text;
    let mut out = Vec::with_capacity(commits.len());
    for _commit in commits {
        // An object is its header line, its bytes and a newline. A name that
        // the commit does not hold is one line that ends in ` missing`.
        let (header, after) = rest.split_once('\n').ok_or_else(short)?;
        let size = header
            .rsplit(' ')
            .next()
            .and_then(|word| word.parse::<usize>().ok());
        if let (false, Some(size)) = (header.ends_with(" missing"), size) {
            out.push(Table::from(after.get(.. size).ok_or_else(short)?));
            rest = after.get(size.saturating_add(1) ..).unwrap_or_default();
        }
        else {
            out.push(Table::default());
            rest = after;
        }
    }
    Ok(out)
}

/// What one run holds of the worktree.
#[derive(Debug)]
struct World
{
    /// The root of the worktree.
    root: PathBuf,
    /// The crates of the workspace, or none when no check reads them.
    workspace: Workspace,
    /// The tables of the worktree.
    tables: Tables,
    /// The definition of each task.
    tasks: Tasks,
    /// The table of each commit, in the order of the commits.
    landing: Vec<Table>,
}

impl World
{
    /// Reads the root and the tables of the worktree. Then it starts Cargo,
    /// mise and git, and it takes their answers.
    ///
    /// # Specification
    /// - requires: the working directory is in a worktree of git.
    /// - ensures: the tables of `request.tables`, or of `.config/gate-scope` of
    ///   the worktree; `GATE_INPUTS_TABLE` names another `inputs.json`. The
    ///   crates of the workspace when a check of the request is no check of the
    ///   table. The task of each check from `GATE_INPUTS_TASK`, or from mise
    ///   when the variable is not set.
    /// - provides: each fact of the worktree that the lists of one run read,
    ///   read one time.
    /// - fails: [`GateError::Command`] when a program fails, and
    ///   [`GateError::Read`] when a table or an answer does not read.
    /// - panics: none.
    /// - intension: one start of Cargo when a check reads the crates and none
    ///   otherwise; one start of mise when `GATE_INPUTS_TASK` is not set and
    ///   none otherwise. The three programs run at the same time. The parts of
    ///   the run show each count.
    /// - executable: none — the outcome is the external processes'.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: the tables, the crates, the tasks and the arguments of
    ///   three programs, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a check of the table with a Cargo that fails, a
    ///   scoped check with that Cargo, and a run with no fixed task; a start of
    ///   Cargo for a check of the table refuses its run, and a start of mise
    ///   for each check changes the count of the part.
    /// - witness: `tests::cli::a_table_check_reads_its_row_at_the_commit_and_starts_no_cargo`
    /// - witness: `tests::cli::a_failed_cargo_is_refused_by_its_command`
    /// - witness: `tests::cli::the_task_that_mise_lists_is_an_input`
    #[inline]
    fn read(
        request: &Request,
        parts: &Parts,
    ) -> Result<Self, GateError>
    {
        let unread = |what: &Path, error: &std::io::Error| GateError::Read {
            what: what.display().to_string(),
            reason: error.to_string(),
        };
        let here = std::env::current_dir()
            .map_err(|error| unread(Path::new("the working directory"), &error))?;
        let top = Program {
            part: Part::from("git rev-parse"),
            name: "git",
            arguments: &["rev-parse", "--show-toplevel"],
            input: "",
        }
        .start(&here)?
        .finish(parts)?;
        let root = PathBuf::from(String::from_utf8_lossy(top.as_ref()).trim());
        let config = request
            .tables
            .clone()
            .unwrap_or_else(|| root.join(".config/gate-scope"));
        let inputs = std::env::var_os("GATE_INPUTS_TABLE")
            .map_or_else(|| config.join("inputs.json"), PathBuf::from);
        let verdicts = config.join("verdicts.json");
        let tables = Tables::read(
            &Answer::from(std::fs::read(&inputs).map_err(|error| unread(&inputs, &error))?),
            &Answer::from(std::fs::read(&verdicts).map_err(|error| unread(&verdicts, &error))?),
        )?;
        let fixed = std::env::var("GATE_INPUTS_TASK").ok();
        let manifest = root.join("Cargo.toml");
        let manifest = manifest.to_string_lossy();
        // economy: the crates are those of the worktree for each commit, as
        // Cargo reads them there. ceiling: a commit whose crate list differs
        // from the worktree's needs a read of its manifests from git (#8274).
        let metadata = [
            "metadata",
            "--format-version",
            "1",
            "--no-deps",
            "--locked",
            "--manifest-path",
            manifest.as_ref(),
        ];
        let mut names = String::new();
        for commit in &request.commits {
            let _written = writeln!(names, "{commit}:{TABLE}");
        }
        // Each program starts before the run takes an answer, so the three
        // run at the same time.
        let cargo = request
            .checks
            .iter()
            .any(|check| !tables.row(check).table)
            .then(|| {
                Program {
                    part: Part::from("cargo metadata"),
                    name: "cargo",
                    arguments: &metadata,
                    input: "",
                }
                .start(&root)
            })
            .transpose()?;
        let mise = fixed
            .is_none()
            .then(|| {
                Program {
                    part: Part::from("mise tasks ls"),
                    name: "mise",
                    arguments: &["tasks", "ls", "--json", "--hidden"],
                    input: "",
                }
                .start(&root)
            })
            .transpose()?;
        let git = Program {
            part: Part::from("git cat-file --batch (tables)"),
            name: "git",
            arguments: &["cat-file", "--batch"],
            input: &names,
        }
        .start(&root)?;
        let landing = landing(&git.finish(parts)?, &request.commits)?;
        let workspace = cargo.map_or_else(
            || Ok(Workspace::default()),
            |running| Workspace::read(&running.finish(parts)?, &root),
        )?;
        let tasks = mise.map_or_else(
            || {
                Ok(Tasks::fixed(
                    &request.checks,
                    &Answer::from(fixed.clone().unwrap_or_default().into_bytes()),
                ))
            },
            |running| Tasks::read(&running.finish(parts)?),
        )?;
        Ok(Self {
            root,
            workspace,
            tables,
            tasks,
            landing,
        })
    }
}

/// One pair of a run: a check at a commit, with what the run asks git for
/// it.
#[derive(Debug)]
struct Pair<'run>
{
    /// The commit.
    commit: &'run Commit,
    /// The check.
    check: &'run Check,
    /// The paths of the check's inputs.
    paths: Vec<String>,
    /// The check's row of `verdicts.json`.
    row: CheckRow,
    /// The table of the commit.
    table: &'run Table,
    /// For each path, then for the path of each grep, the place of its
    /// object in the answer of git.
    places: Vec<usize>,
}

/// What a run asks git: each pair, and each name one time.
#[derive(Debug)]
struct Plan<'run>
{
    /// Each pair, in the order of the commits and then of the checks.
    pairs: Vec<Pair<'run>>,
    /// The names for `git cat-file --batch-check`, one per line.
    names: String,
    /// The count of the names.
    asked: usize,
}

impl<'run> Plan<'run>
{
    /// The pairs of `request` and the names that they ask git.
    ///
    /// # Specification
    /// - requires: `world.landing` holds one table for each commit of
    ///   `request`, in their order.
    /// - ensures: one pair for each commit and each check. `names` holds each
    ///   `<commit>:<path>` of a pair one time, with no last `/` in the path,
    ///   and `places` of a pair names the line of each of its paths.
    /// - provides: one batch for git, whichever pairs share a path.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one line of the batch for each distinct name.
    /// - executable: none — the reference is the script before this crate,
    ///   whose digests the cases pin.
    ///
    /// # Cost
    /// - allocation: the paths and the places of each pair, and each distinct
    ///   name one time, growth within the pairs of the request
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the digests of the script for two checks at two
    ///   commits that share most paths; a place of another name gives a path
    ///   the object of another path and changes each pinned digest.
    /// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
    #[inline]
    #[must_use]
    fn new(
        world: &'run World,
        request: &'run Request,
    ) -> Self
    {
        let mut pairs = Vec::new();
        let mut names = String::new();
        let mut name = String::new();
        let mut asked: BTreeMap<String, usize> = BTreeMap::new();
        for (commit, table) in request.commits.iter().zip(&world.landing) {
            for check in &request.checks {
                let paths = world
                    .tables
                    .paths(&request.scope, check, &world.workspace, table);
                let row = world.tables.row(check);
                let mut places = Vec::with_capacity(paths.len().saturating_add(row.greps.len()));
                for path in paths
                    .iter()
                    .map(String::as_str)
                    .chain(row.greps.iter().map(|grep| grep.within.as_str()))
                {
                    name.clear();
                    name.push_str(commit.as_ref());
                    name.push(':');
                    name.push_str(path.strip_suffix('/').unwrap_or(path));
                    let known = asked.get(name.as_str()).copied();
                    places.push(known.unwrap_or_else(|| {
                        let fresh = asked.len();
                        names.push_str(&name);
                        names.push('\n');
                        let _new = asked.insert(name.clone(), fresh);
                        fresh
                    }));
                }
                pairs.push(Pair {
                    commit,
                    check,
                    paths,
                    row,
                    table,
                    places,
                });
            }
        }
        Self {
            pairs,
            names,
            asked: asked.len(),
        }
    }
}

/// The answer of git for each name of a plan, in the order of the names: an
/// object and its type, or a line that ends in ` missing`.
#[repr(transparent)]
#[derive(Debug)]
struct Objects<'answer>(Vec<&'answer str>);

/// One grep that a run owes: a pattern in the files of a tree.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Search
{
    /// The pattern.
    pattern: String,
    /// The path that the check greps.
    within: String,
    /// The object of that path when it is a tree at the commit. The commit
    /// otherwise.
    tree: String,
    /// Whether `tree` is the object of the path.
    shared: bool,
}

/// The arguments of one grep for `git`.
#[repr(transparent)]
#[derive(Debug)]
struct Words<'search>(Vec<&'search str>);

/// Where the digest of a search goes: a pair of the run and a line of its
/// list.
#[derive(Clone, Copy, Debug)]
struct Place
{
    /// The pair's place in the run.
    pair: usize,
    /// The line's place in the list.
    line: usize,
}

/// The lines of one pair before the digests of its searches.
#[derive(Debug)]
struct Draft
{
    /// The commit.
    commit: Commit,
    /// The check.
    check: Check,
    /// The lines. The line of a grep ends at its tab.
    lines: Vec<String>,
}

/// The lists of a run before the digests of its searches, and the searches.
#[derive(Debug)]
struct Filled
{
    /// The lines of each pair.
    drafts: Vec<Draft>,
    /// Each distinct search, with each line that takes its digest.
    wanted: BTreeMap<Search, Vec<Place>>,
}

impl Filled
{
    /// The lines of `plan` from the objects that git gave.
    ///
    /// # Specification
    /// - requires: `objects` holds the answer of git for each name of `plan`,
    ///   in the order of the names.
    /// - ensures: for each pair, one line for each path with its object, or
    ///   `absent` for a path that the commit does not hold; then the line of
    ///   the table for a check of the table; then the line of the task; then
    ///   one line for each grep. Two greps with one pattern, one path and one
    ///   tree at their commits are one search.
    /// - provides: the lists of a run, with each grep named by what it reads.
    /// - fails: [`GateError::Unlisted`] when a check has no task, and
    ///   [`GateError::Read`] when a path has no answer.
    /// - panics: none.
    /// - intension: one search for each distinct tree that a grep reads.
    /// - executable: none — the reference is the script before this crate,
    ///   whose lists the cases pin.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Cost
    /// - allocation: one line for each path of each pair and one search for
    ///   each distinct tree, growth within the names of the plan
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the list of the script with a path that the tree does
    ///   not hold, and two runs whose commits share or do not share the tree of
    ///   `crates`; one search for each commit changes the count of the part,
    ///   and one search for all commits gives tree three the digest of tree
    ///   one.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    /// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
    /// - witness: `tests::cli::a_changed_crate_changes_its_digest_and_runs_its_own_grep`
    #[inline]
    fn new(
        world: &World,
        plan: Plan<'_>,
        objects: &Objects<'_>,
    ) -> Result<Self, GateError>
    {
        let lost = || GateError::Read {
            what: "git cat-file --batch-check".to_owned(),
            reason: "a path with no object".to_owned(),
        };
        let mut drafts = Vec::with_capacity(plan.pairs.len());
        let mut wanted: BTreeMap<Search, Vec<Place>> = BTreeMap::new();
        for pair in plan.pairs {
            let mut places = pair.places.iter();
            let mut lines = Vec::with_capacity(pair.places.len().saturating_add(2));
            for path in &pair.paths {
                let object = places
                    .next()
                    .and_then(|place| objects.0.get(*place))
                    .copied()
                    .ok_or_else(lost)?;
                let object = if object.ends_with(" missing") {
                    "absent"
                }
                else {
                    object.split(' ').next().unwrap_or(object)
                };
                lines.push(format!("{path}\t{object}"));
            }
            if pair.row.table {
                lines.push(pair.table.line(pair.check));
            }
            lines.push(world.tasks.line(pair.check)?);
            for grep in &pair.row.greps {
                let object = places
                    .next()
                    .and_then(|place| objects.0.get(*place))
                    .copied()
                    .ok_or_else(lost)?;
                // A path that is a tree at the commit names the answer of
                // its grep by that tree. Each other path has no object to
                // share, so its grep runs for its commit alone.
                let shared = object.strip_suffix(" tree");
                let search = Search {
                    pattern: grep.pattern.clone(),
                    within: grep.within.clone(),
                    tree: shared.map_or_else(|| pair.commit.to_string(), ToOwned::to_owned),
                    shared: shared.is_some(),
                };
                wanted.entry(search).or_default().push(Place {
                    pair: drafts.len(),
                    line: lines.len(),
                });
                lines.push(format!("grep:{}:{}\t", grep.within, grep.pattern));
            }
            drafts.push(Draft {
                commit: pair.commit.clone(),
                check: pair.check.clone(),
                lines,
            });
        }
        Ok(Self { drafts, wanted })
    }
}

impl Search
{
    /// The arguments of the grep for `git`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `grep -l -e <pattern> <tree>`, and then `-- <path>` when the
    ///   tree is a commit and not the object of the path.
    /// - provides: one form for the grep of a shared tree and of a commit.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the reference is the script before this crate,
    ///   whose line the cases pin.
    ///
    /// # Cost
    /// - allocation: the list of five or seven arguments, setup
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the line of the script for a grep of `crates`; a grep
    ///   of the tree of `crates` with the path after it finds no file and
    ///   changes the pinned line.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    #[inline]
    #[must_use]
    fn arguments(&self) -> Words<'_>
    {
        let mut arguments = vec![
            "grep",
            "-l",
            "-e",
            self.pattern.as_str(),
            self.tree.as_str(),
        ];
        if !self.shared {
            arguments.extend(["--", self.within.as_str()]);
        }
        Words(arguments)
    }

    /// The digest of the files that `answer` names, as git printed them for
    /// this grep.
    ///
    /// # Specification
    /// - requires: `answer` is what `git grep -l` printed for the arguments of
    ///   this search.
    /// - ensures: the SHA-256 of the files that hold the pattern, each as its
    ///   path from the root with a newline, in the order of git.
    /// - provides: the list of the files that a grep of a check reads, as an
    ///   input of the check.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the reference is the script before this crate,
    ///   whose line the cases pin.
    ///
    /// # Cost
    /// - allocation: the paths of the files that hold the pattern, growth
    ///   within the answer of git
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the line of the script for a grep of `crates` at tree
    ///   one, and its digest at tree three; a file named from its tree in place
    ///   of the root changes the pinned line.
    /// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
    /// - witness: `tests::cli::a_changed_crate_changes_its_digest_and_runs_its_own_grep`
    #[inline]
    #[must_use]
    fn digest(
        &self,
        answer: &Answer,
    ) -> Digest
    {
        let listed = String::from_utf8_lossy(answer.as_ref());
        let mut files = String::with_capacity(listed.len());
        for line in listed.lines() {
            // git prints each file after the tree's name and a colon. The
            // files of a shared tree are relative to the path of the grep.
            let file = line
                .strip_prefix(self.tree.as_str())
                .and_then(|rest| rest.strip_prefix(':'))
                .unwrap_or(line);
            if self.shared {
                files.push_str(self.within.trim_end_matches('/'));
                files.push('/');
            }
            files.push_str(file);
            files.push('\n');
        }
        Digest::from(files.as_bytes())
    }
}

/// The list of the inputs of each check of `request` at each of its commits.
///
/// # Specification
/// - requires: the working directory is in a worktree of git, and `git`,
///   `cargo` and `mise` are on the path.
/// - ensures: one list for each commit and each check, in the order of the
///   commits and then of the checks. A list is what the script before this
///   crate printed for its pair.
/// - provides: the inputs of each check of a gate in one run.
/// - fails: [`GateError::Command`] when a program fails, [`GateError::Read`]
///   when a table or an answer does not read, [`GateError::Unlisted`] when a
///   check has no task, and [`GateError::Thread`] when the thread of a
///   program's input does not start.
/// - panics: none.
/// - intension: one batch of git for the objects of all pairs, and one grep for
///   each distinct tree. The greps run at the same time. `parts` holds one row
///   for each call.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the plan, the lines of each list and the arguments of each
///   grep, growth within the pairs of the request
///
/// # Adequacy
/// - hypothesis: L2 — the lists and the digests of the script on three trees,
///   with the count of each part; a run for each pair changes the count of the
///   batch.
/// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
/// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
/// - witness: `tests::cli::a_changed_crate_changes_its_digest_and_runs_its_own_grep`
/// - witness: `tests::cli::a_check_that_mise_does_not_list_is_refused`
#[inline]
pub fn lists(
    request: &Request,
    parts: &Parts,
) -> Result<Vec<Listed>, GateError>
{
    let world = World::read(request, parts)?;
    let start = Instant::now();
    let plan = Plan::new(&world, request);
    parts.add(Part::from("the paths of each pair"), start.elapsed());
    let batch = Program {
        part: Part::from("git cat-file --batch-check"),
        name: "git",
        arguments: &["cat-file", "--batch-check=%(objectname) %(objecttype)"],
        input: &plan.names,
    };
    let answer = batch.start(&world.root)?.finish(parts)?;
    let answer = String::from_utf8_lossy(answer.as_ref());
    let objects = Objects(answer.lines().collect());
    if objects.0.len() != plan.asked {
        return Err(GateError::Read {
            what: "git cat-file --batch-check".to_owned(),
            reason: format!("{} objects for {} names", objects.0.len(), plan.asked),
        });
    }
    let Filled { mut drafts, wanted } = Filled::new(&world, plan, &objects)?;
    // Each grep starts before the run takes an answer, so the greps run at
    // the same time.
    let mut arguments = Vec::with_capacity(wanted.len());
    for search in wanted.keys() {
        arguments.push(search.arguments());
    }
    let mut running = Vec::with_capacity(wanted.len());
    for words in &arguments {
        running.push(
            Program {
                part: Part::from("git grep"),
                name: "git",
                arguments: &words.0,
                input: "",
            }
            .start(&world.root)?,
        );
    }
    for ((search, places), grep) in wanted.iter().zip(running) {
        let digest = search.digest(&grep.finish(parts)?);
        for place in places {
            if let Some(line) = drafts
                .get_mut(place.pair)
                .and_then(|draft| draft.lines.get_mut(place.line))
            {
                let _written = write!(line, "{digest}");
            }
        }
    }
    let mut listed = Vec::with_capacity(drafts.len());
    for draft in drafts {
        listed.push(Listed::new(
            draft.commit,
            draft.check,
            List::from(draft.lines),
        ));
    }
    Ok(listed)
}
