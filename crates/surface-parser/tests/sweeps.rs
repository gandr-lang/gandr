//! The parser's sweeps: the corpus cut short and with each token dropped,
//! against the recovery records and through the molder's two procedures.
//!
//! Each visits its stated sample under every pull-request profile, the whole
//! corpus under the `sweeps` profile, and the night's slice of it under the
//! `nightly` profile (`gandr-workflow-sweep`): each source costs its length
//! squared, and the whole corpus is visited every few nights. A sample is a
//! hashed slice of the corpus at a fixed size, salted by the sweep's name, at
//! least one source of each class — `strict` and each directory below
//! `fixture`, the pending set among them — and every source the change adds
//! or modifies. A sampled source longer than [`SAMPLED_SPAN`] steps through
//! its rows by its multiple of the span, so it costs about its length times
//! the span rather than its length squared.

use core::error::Error;
use core::num::NonZeroUsize;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::collections::HashSet;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_parser::DisagreementCount;
use gandr_surface_parser::FormSplit;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::MeldState;
use gandr_surface_parser::MoldVerdicts;
use gandr_surface_parser::Molder;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use gandr_workflow_sweep::Changed;
use gandr_workflow_sweep::Coverage;
use gandr_workflow_sweep::Nights;
use gandr_workflow_sweep::Rotation;
use gandr_workflow_sweep::Sample;
use gandr_workflow_sweep::SampleName;
use gandr_workflow_sweep::SampleSize;
use gandr_workflow_sweep::Sweep;
use gandr_workflow_sweep::corpus;

use crate::common::built;
use crate::common::label_of;
use crate::common::text;

/// The recovery sweep's sample: forty-eight sources, and the rows of every
/// sixteenth significant token of each, widened past [`SAMPLED_SPAN`].
const RECOVERY: Sample = Sample {
    name: SampleName("dropped_tokens_recover_no_worse_than_the_record"),
    size: SampleSize(48),
};

/// The step between the token rows the recovery sample checks.
const RECOVERY_STRIDE: usize = 16;

/// The nights the nightly recovery sweep takes to visit the corpus: a
/// thirty-second a night. A quarter took 179 s and 410 s with specifications
/// enforced on the nightly runner, and a sixteenth 128 s, past its share of
/// the nightly budget alone.
const RECOVERY_NIGHTS: Nights = Nights(32);

/// The most tab-separated fields a recovery record row holds, with room
/// to spare: a row with more is read as its first this many.
const ROW_FIELDS: usize = 8;

/// The table sweep's sample: twelve sources, the rows of every sixteenth
/// significant token of each, every sixty-fourth under `anodized_panic`. A
/// change that touches more sources widens the step in proportion, so the
/// sample molds about as many rows however many sources it visits, and a
/// source past [`SAMPLED_SPAN`] widens it again.
const TABLES: Sample = Sample {
    name: SampleName("table_verdicts_equal_dry_run_verdicts"),
    size: SampleSize(12),
};

/// The nights the nightly table sweep takes to visit the corpus: a sixteenth
/// a night. A quarter took 102 s and 196 s with specifications enforced on
/// the nightly runner, and an eighth 95 s.
const TABLES_NIGHTS: Nights = Nights(16);

/// The step between the token rows the table sample molds over its stated
/// size.
const TABLES_STRIDE: usize = if cfg!(anodized_panic) { 64 } else { 16 };

/// The step between the token rows the whole table sweep molds: every row
/// plain, every sixteenth under `anodized_panic`, where every clause of both
/// procedures runs at every decision.
const TABLES_WHOLE_STRIDE: usize = if cfg!(anodized_panic) { 16 } else { 1 };

/// The significant tokens a sampled source holds at its sweep's own step.
///
/// A row parses or molds the source once more, so a source at a fixed step
/// costs its length squared. At the recovery sample's step with
/// specifications enforced, a source of 4729 tokens took 16.5 s on one core,
/// past half the 30 s bound alone, where one of this many takes under one.
const SAMPLED_SPAN: usize = 1024;

/// The step between the token rows a sweep visits in one source.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct RowStep(usize);

/// The significant tokens one source holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct TokenCount(usize);

/// Every corpus source, whole and cut short after each significant token,
/// keeps its recorded tree, and dropping each significant token recovers no
/// worse than the record.
///
/// Each source of the fixture and strict roots has a record under
/// `tests/recovery/` at its path in the corpus, with the extension `recovery`.
/// Its first row is the whole parse's obligation count, node count and
/// fingerprint; then comes one row per significant token: the parse cut short
/// after it (obligations, nodes and the fingerprint's first eight hex digits)
/// and the parse with it dropped (obligations and nodes). A whole or cut-short
/// row must match exactly. A dropped row is worse when either count grows; the
/// failure names the worst. A source with no record, a record whose rows do not
/// match its source's tokens and a record with no source are stale; the
/// failure names each, with the command that re-records it.
///
/// The fingerprint hashes the tree's significant nodes in preorder, as the
/// tree's own digest does, but names each mold by its rule, its label and its
/// rank among that rule's molds of the label rather than by its [`MoldId`].
/// The tree digest moves under any grammar change that renumbers molds; the
/// fingerprint moves only where a tree does, so a grammar change re-records
/// exactly the sources whose parses it changes.
///
/// A corpus change re-records the sources it touches:
/// `UPDATE_EXPECT=1 GANDR_RECOVERY_SOURCE=<source> mise run ci:recovery`
/// rewrites that source's record alone, `<source>` being its path in the
/// corpus, and `UPDATE_EXPECT=1 mise run ci:recovery` rewrites every record and
/// deletes those whose source is gone. The rewrite is a reviewed diff, never a
/// blind re-pin: a dropped row whose counts grew is a recovery regression, and
/// a whole or cut-short row that moved is a tree change, each answered by the
/// change that causes it.
///
/// The whole matrix is some two hundred thousand parses, two for each of the
/// corpus's hundred thousand significant tokens (`mise run ci:recovery`, and
/// the `sweeps` profile), and the rewrite always runs it; the `nightly`
/// profile parses the night's slice of it. A queue entry that changes the
/// parser, its grammar or its syntax tree (`crates/surface-parser/`,
/// `crates/surface-grammar/`, `crates/surface-syntax/`) reaches every record,
/// and the plain lane runs the whole matrix for it; the enforcing shards keep
/// the sample, where the whole matrix would take half an hour. The sources
/// are independent, so they are parsed on every available core, the longest
/// first ([`observed_in_parallel`]): run one after another, the whole matrix
/// took 127 s of the plain lane's critical path (#2148). The sample,
/// [`RECOVERY`], parses forty-eight sources, those the change touches first:
/// each one's whole row and the rows of every sixteenth significant token, a
/// source past [`SAMPLED_SPAN`] tokens at that step times its multiple of the
/// span ([`sampled_step`]).
/// Every source's record is still required to exist, and every record to have
/// a source, under every profile.
#[test]
fn dropped_tokens_recover_no_worse_than_the_record() -> Result<(), Box<dyn Error>>
{
    use core::fmt::Write as _;

    /// How many moved or worse rows a failure lists.
    const LISTED: usize = 16;

    let pbg = built();
    let mut spellings: Vec<String> = Vec::new();
    let mut ranks: Vec<(&str, &str, usize)> = Vec::new();
    for (id, def) in pbg.iter_molds() {
        let rule = pbg.rule_of(id)?.name;
        let rank = if let Some(entry) = ranks
            .iter_mut()
            .find(|&&mut (name, label, _)| name == rule && label == def.label)
        {
            entry.2 = entry.2.saturating_add(1);
            entry.2
        }
        else {
            ranks.push((rule, def.label, 0));
            0
        };
        let index = usize::try_from(u32::from(id))?;
        if spellings.len() <= index {
            spellings.resize(index.saturating_add(1), String::new());
        }
        if let Some(slot) = spellings.get_mut(index) {
            *slot = format!("{rule} {} {rank}", def.label);
        }
    }
    let fingerprint = |tree: &SyntaxTree<'_>| {
        let spelled = |mold: MoldId| {
            usize::try_from(u32::from(mold))
                .ok()
                .and_then(|index| spellings.get(index))
                .map_or("", String::as_str)
        };
        let mut preimage: Vec<u8> = Vec::new();
        let mut pending = vec![tree.root()];
        while let Some(at) = pending.pop() {
            let Some(node) = label_of(tree, at)
            else {
                continue;
            };
            let below: Vec<NodeIndex> = tree
                .children(at)
                .filter(|&child| {
                    label_of(tree, child).is_some_and(|child| bool::from(child.significance()))
                })
                .collect();
            let name = match node {
                NodeLabel::Tile(mold) => format!("tile {}", spelled(mold)),
                NodeLabel::Meld(mold) => format!("meld {}", spelled(mold)),
                other @ (NodeLabel::Wald
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. }
                | NodeLabel::Space
                | NodeLabel::Doc) => format!("{other:?}"),
            };
            preimage.extend_from_slice(name.as_bytes());
            preimage.push(0);
            preimage
                .extend_from_slice(&u64::try_from(below.len()).unwrap_or(u64::MAX).to_le_bytes());
            if bool::from(node.carries_text()) {
                let written = text(tree, at);
                preimage.extend_from_slice(
                    &u64::try_from(written.len())
                        .unwrap_or(u64::MAX)
                        .to_le_bytes(),
                );
                preimage.extend_from_slice(written.as_bytes());
            }
            pending.extend(below.into_iter().rev());
        }
        blake3::hash(&preimage).to_hex().to_string()
    };
    let records = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/recovery");
    let update = std::env::var_os("UPDATE_EXPECT").is_some();
    let only = std::env::var("GANDR_RECOVERY_SOURCE").ok();
    let sweep = if update {
        Sweep::new(Coverage::Full, Changed::default(), Rotation::Whole)
    }
    else {
        Sweep::asked()?
    };
    eprintln!("{}", sweep.rotation());
    let coverage = sweep.coverage();
    let stride = match coverage {
        Coverage::Full => 1,
        Coverage::Sampled => RECOVERY_STRIDE,
    };
    let rerecord = |rel: &str| {
        format!(
            "re-record it with `UPDATE_EXPECT=1 GANDR_RECOVERY_SOURCE={rel} mise run ci:recovery`"
        )
    };
    let sources = corpus::sources()?;
    let visited: HashSet<PathBuf> = sweep
        .visit_rotating(RECOVERY, RECOVERY_NIGHTS, &sources)
        .into_iter()
        .map(|source| source.path)
        .collect();
    let mut sourced: HashSet<PathBuf> = HashSet::new();
    let mut stale = Vec::new();
    let mut moved = Vec::new();
    let mut worse: Vec<(usize, usize, String)> = Vec::new();
    let mut jobs: Vec<(&str, PathBuf, &Path)> = Vec::new();
    for source in &sources {
        let rel = source.name.as_ref();
        let record = records.join(rel).with_extension("recovery");
        let _sourced = sourced.insert(record.clone());
        if only.as_deref().is_some_and(|only| only != rel) {
            continue;
        }
        if !update && !record.is_file() {
            stale.push(format!("{rel} has no record; {}", rerecord(rel)));
            continue;
        }
        if only.is_none() && !visited.contains(&source.path) {
            continue;
        }
        jobs.push((rel, record, source.path.as_path()));
    }
    let observations = observed_in_parallel(
        &jobs,
        |&(_, _, path)| path,
        |&(_, _, path)| {
            let src = std::fs::read_to_string(path)
                .map_err(|error| format!("{}: {error}", path.display()))?;
            let mut observed = String::new();
            let mut dropped = String::new();
            let whole =
                parse(pbg, SourceText::from(src.as_str())).map_err(|error| error.to_string())?;
            let digest = fingerprint(whole.tree());
            writeln!(
                observed,
                "W\t{}\t{}\t{digest}",
                whole.obligations().len(),
                whole.tree().positions().count()
            )
            .map_err(|error| error.to_string())?;
            let labelled = label(SourceFragment::from(src.as_str()));
            let significant = || {
                labelled
                    .iter()
                    .filter(|token| token.lexeme != Lexeme::Space)
            };
            let RowStep(step) =
                sampled_step(coverage, RowStep(stride), TokenCount(significant().count()));
            for (index, token) in significant().enumerate() {
                if !index.is_multiple_of(step) {
                    writeln!(observed, "T").map_err(|error| error.to_string())?;
                    continue;
                }
                let start = usize::try_from(token.start).map_err(|error| error.to_string())?;
                let end = usize::try_from(token.end).map_err(|error| error.to_string())?;
                let cut = parse(pbg, SourceText::from(src.get(.. end).unwrap_or_default()))
                    .map_err(|error| error.to_string())?;
                let cut_digest = fingerprint(cut.tree());
                dropped.clear();
                dropped.push_str(src.get(.. start).unwrap_or_default());
                dropped.push_str(src.get(end ..).unwrap_or_default());
                let variant = parse(pbg, SourceText::from(dropped.as_str()))
                    .map_err(|error| error.to_string())?;
                writeln!(
                    observed,
                    "T\t{}\t{}\t{}\t{}\t{}",
                    cut.obligations().len(),
                    cut.tree().positions().count(),
                    cut_digest.get(.. 8).unwrap_or_default(),
                    variant.obligations().len(),
                    variant.tree().positions().count()
                )
                .map_err(|error| error.to_string())?;
            }
            Ok(observed)
        },
    )?;
    for (&(rel, ref record, _), observed) in jobs.iter().zip(&observations) {
        if update {
            if let Some(parent) = record.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(record, observed)?;
            continue;
        }
        let recorded = std::fs::read_to_string(record)?;
        let (rows, recorded_rows) = (observed.lines().count(), recorded.lines().count());
        if rows != recorded_rows {
            stale.push(format!(
                "{rel} has {rows} rows and its record {recorded_rows}; {}",
                rerecord(rel)
            ));
            continue;
        }
        for (row, (got, want)) in observed.lines().zip(recorded.lines()).enumerate() {
            let token = row.saturating_sub(1);
            // Each row's fields, the observed then the recorded, split into
            // fixed slots rather than a fresh vector per row.
            let mut slots = [[""; ROW_FIELDS]; 2];
            let mut counts = [0_usize; 2];
            for ((row_slots, count), text) in slots.iter_mut().zip(&mut counts).zip([got, want]) {
                for (slot, field) in row_slots.iter_mut().zip(text.split('\t')) {
                    *slot = field;
                    *count = count.saturating_add(1);
                }
            }
            let ([ref observed_slots, ref recorded_slots], [count, recorded_count]) =
                (slots, counts);
            let fields = observed_slots.get(.. count).unwrap_or(&[]);
            let recorded_fields = recorded_slots.get(.. recorded_count).unwrap_or(&[]);
            match (fields, recorded_fields) {
                (&["T"], &["T", ..]) => {},
                (&["W", ..], &["W", ..]) => {
                    if got != want {
                        moved.push(format!("{rel} whole"));
                    }
                },
                (
                    &["T", ref cut @ .., obligations, nodes],
                    &["T", ref recorded_cut @ .., old_obligations, old_nodes],
                ) if cut.len() == 3 && recorded_cut.len() == 3 => {
                    if cut != recorded_cut {
                        moved.push(format!("{rel} cut after token {token}"));
                    }
                    let obligations: usize = obligations.parse()?;
                    let nodes: usize = nodes.parse()?;
                    let old_obligations: usize = old_obligations.parse()?;
                    let old_nodes: usize = old_nodes.parse()?;
                    if obligations > old_obligations || nodes > old_nodes {
                        worse.push((
                            obligations.saturating_sub(old_obligations),
                            nodes.saturating_sub(old_nodes),
                            format!(
                                "{rel} drop {token}: obligations {old_obligations} -> {obligations}, nodes {old_nodes} -> {nodes}"
                            ),
                        ));
                    }
                },
                _ => {
                    stale.push(format!("{rel} row {row} is malformed; {}", rerecord(rel)));
                    break;
                },
            }
        }
    }
    let mut orphans = Vec::new();
    if only.is_none() {
        let mut pending = vec![records.clone()];
        while let Some(dir) = pending.pop() {
            let Ok(entries) = std::fs::read_dir(&dir)
            else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    pending.push(path);
                }
                else if !sourced.contains(&path) {
                    orphans.push(path);
                }
            }
        }
        orphans.sort();
    }
    if update {
        for orphan in &orphans {
            std::fs::remove_file(orphan)?;
        }
        return Ok(());
    }
    let orphaned: Vec<&Path> = orphans
        .iter()
        .filter_map(|orphan| orphan.strip_prefix(&records).ok())
        .collect();
    assert!(
        stale.is_empty() && orphans.is_empty(),
        "stale recovery records: {stale:?}; records under tests/recovery with no corpus source, which `UPDATE_EXPECT=1 mise run ci:recovery` deletes: {orphaned:?}"
    );
    assert!(
        moved.is_empty(),
        "{} whole or cut-short trees moved from the record: {:?}",
        moved.len(),
        moved.iter().take(LISTED).collect::<Vec<_>>()
    );
    let worst = worse
        .iter()
        .max_by_key(|&&(obligations, nodes, _)| (obligations, nodes));
    assert!(
        worse.is_empty(),
        "{} dropped tokens recover worse than the record; worst {:?}; first {:?}",
        worse.len(),
        worst.map(|entry| &entry.2),
        worse
            .iter()
            .take(LISTED)
            .map(|entry| &entry.2)
            .collect::<Vec<_>>()
    );
    Ok(())
}

/// `observe` applied to every job on every available core, the results in
/// the jobs' order.
///
/// A worker takes the next job the shared cursor names until none is left.
/// The jobs are taken largest file first, since a source costs its length
/// squared, so the last job a worker takes is a short one.
///
/// # Specification
/// - ensures: one result per job, in the jobs' order, each `observe` of that
///   job; at most as many workers as jobs, and at least one.
/// - fails: with the error of the first job, in the jobs' order, whose
///   observation failed.
/// - panics: resumes a worker's panic on the caller's thread.
///
/// # Adequacy
/// - hypothesis: L3 — the whole recovery sweep compares every observed row with
///   the record kept at the job's own source; a result out of the jobs' order,
///   or one missing, moves every row after it and fails the sweep.
/// - witness: `tests::sweeps::dropped_tokens_recover_no_worse_than_the_record`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |observed| observed.len() == jobs.len()))]
fn observed_in_parallel<T, J>(
    jobs: &[T],
    path: impl Fn(&T) -> &Path,
    observe: impl Fn(&T) -> Result<J, String> + Sync,
) -> Result<Vec<J>, Box<dyn Error>>
where
    T: Sync,
    J: Send,
{
    let mut order: Vec<(u64, usize)> = jobs
        .iter()
        .enumerate()
        .map(|(at, job)| {
            (
                std::fs::metadata(path(job)).map_or(0, |meta| meta.len()),
                at,
            )
        })
        .collect();
    order.sort_unstable_by(|left, right| right.cmp(left));
    let workers = std::thread::available_parallelism()
        .map_or(1, NonZeroUsize::get)
        .min(jobs.len())
        .max(1);
    let cursor = AtomicUsize::new(0);
    let mut done: Vec<(usize, Result<J, String>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = core::iter::repeat_n((), workers)
            .map(|()| {
                scope.spawn(|| {
                    let mut taken = Vec::new();
                    while let Some(&(_, at)) = order.get(cursor.fetch_add(1, Ordering::Relaxed)) {
                        if let Some(job) = jobs.get(at) {
                            taken.push((at, observe(job)));
                        }
                    }
                    taken
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|handle| match handle.join() {
                Ok(taken) => taken,
                Err(panic) => std::panic::resume_unwind(panic),
            })
            .collect()
    });
    done.sort_unstable_by_key(|&(at, _)| at);
    done.into_iter()
        .map(|(_, observed)| observed.map_err(Box::<dyn Error>::from))
        .collect()
}

/// The step a sweep takes through a source's token rows: `stride`, widened
/// under the sample by the multiple of [`SAMPLED_SPAN`] the source's `tokens`
/// reach.
///
/// A sampled source of any length then visits at most as many rows as one
/// of the span, so its cost grows with its length, not its length squared,
/// and no one source takes the 30 s bound alone. The whole sweep keeps
/// `stride` at every length, since it owes every row.
///
/// # Specification
/// - ensures: at least `stride`; exactly `stride` under [`Coverage::Full`];
///   under [`Coverage::Sampled`], at most as many rows of `tokens` as of the
///   span at `stride`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the sampled sweeps visit a source of 4729 tokens beside
///   sources under the span; a step that never widened would take the bound,
///   and one that widened under the whole sweep would skip rows it owes.
/// - witness: `tests::sweeps::dropped_tokens_recover_no_worse_than_the_record`
/// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
#[spec(ensures: |ret| ret.0 >= stride.0 && match coverage {
    Coverage::Full => ret.0 == stride.0,
    Coverage::Sampled => stride.0 == 0 || tokens.0.div_ceil(ret.0) <= SAMPLED_SPAN.div_ceil(stride.0),
})]
fn sampled_step(
    coverage: Coverage,
    stride: RowStep,
    tokens: TokenCount,
) -> RowStep
{
    match coverage {
        Coverage::Full => stride,
        Coverage::Sampled => RowStep(
            stride
                .0
                .saturating_mul(tokens.0.div_ceil(SAMPLED_SPAN).max(1)),
        ),
    }
}

/// The molder's tables reach the dry runs' verdict at every decision the
/// corpus and its one-token drops produce, in both modes.
///
/// A molder in [`MoldVerdicts::Differential`] runs the dry runs and the tables
/// at every decision and counts each where their admitted menus, their
/// eligible menus or their choices differ; the count must stay zero. Each
/// visited corpus source is molded whole, cut short after each significant
/// token and with each dropped — the drop harness's matrix. Each text is
/// molded as one stream, as [`parse`] does, and form run by form run, as an
/// editing session does. The stray cases the molder's cost was measured on
/// come first: their windows are the ones the window classes share most.
///
/// The sample, [`TABLES`], molds twelve sources and every source the change
/// touches, each whole and at every sixteenth significant token's rows, every
/// sixty-fourth under `anodized_panic`. When the change brings it past twelve
/// sources, the step widens by the multiple of twelve it visits, so a change
/// over a hundred fixtures molds each whole and the same budget of rows spread
/// over them, inside the test limit; a source past [`SAMPLED_SPAN`] tokens
/// widens the step again by its multiple of the span ([`sampled_step`]). The
/// whole sweep molds every source at every row, every sixteenth under
/// `anodized_panic`.
#[test]
fn table_verdicts_equal_dry_run_verdicts() -> Result<(), Box<dyn Error>>
{
    /// The strays the molder's cost was measured on, each a one-token edit of
    /// a corpus-shaped definition.
    const STRAYS: [&str; 6] = [
        "def f(x : In[: Nat]) -> Nat { pure x }",
        "def g(b : Unit) -> Unit { run c <- not b); become not(c) }",
        "too_big = Type ;\ndef wrong_sort : Type ;",
        "def : Integer ;\ndef y = 1 ;",
        "def h(x : List[Nat) -> Nat { pure x }",
        "def k(a : Unit) -> Unit { run r go(a); pure r }",
    ];

    let pbg = built();
    let sweep = Sweep::asked()?;
    eprintln!("{}", sweep.rotation());
    let visited = sweep.visit_rotating(TABLES, TABLES_NIGHTS, &corpus::sources()?);
    let stride = match sweep.coverage() {
        Coverage::Full => TABLES_WHOLE_STRIDE,
        Coverage::Sampled => {
            TABLES_STRIDE.saturating_mul(visited.len().div_ceil(TABLES.size.0).max(1))
        },
    };
    let mut molder = Molder::with_verdicts(pbg, MoldVerdicts::Differential);
    let mut molded = 0_usize;
    let mut disagreeing: Vec<String> = Vec::new();
    let mut differential = |name: &dyn Fn() -> String, text: &str| {
        let before = molder.disagreements();
        let source = SourceText::from(text);
        let mut state = MeldState::new(pbg);
        molder.mold_stream(&mut state, &label(SourceFragment::from(text)), source);
        let split = FormSplit::new(&molder, source);
        for &run in split.runs() {
            let _unit = split.mold(&mut molder, run);
        }
        molded = molded.saturating_add(1);
        if molder.disagreements() != before {
            disagreeing.push(name());
        }
    };
    for stray in STRAYS {
        differential(&|| format!("stray {stray:?}"), stray);
    }
    let mut dropped = String::new();
    for source in visited {
        let rel = source.name.as_ref();
        let src = std::fs::read_to_string(&source.path)
            .map_err(|error| format!("{}: {error}", source.path.display()))?;
        differential(&|| format!("{rel} whole"), &src);
        let labelled = label(SourceFragment::from(src.as_str()));
        let significant = || {
            labelled
                .iter()
                .filter(|token| token.lexeme != Lexeme::Space)
        };
        let RowStep(step) = sampled_step(
            sweep.coverage(),
            RowStep(stride),
            TokenCount(significant().count()),
        );
        for (index, token) in significant().enumerate() {
            if !index.is_multiple_of(step) {
                continue;
            }
            let start = usize::try_from(token.start)?;
            let end = usize::try_from(token.end)?;
            differential(
                &|| format!("{rel} cut after token {index}"),
                src.get(.. end).unwrap_or_default(),
            );
            dropped.clear();
            dropped.push_str(src.get(.. start).unwrap_or_default());
            dropped.push_str(src.get(end ..).unwrap_or_default());
            differential(&|| format!("{rel} drop {index}"), &dropped);
        }
    }
    assert!(molded > STRAYS.len(), "the corpus sources are present");
    assert_eq!(
        DisagreementCount(0),
        molder.disagreements(),
        "{} of {molded} texts mold differently by the tables and the dry runs; first {:?}",
        disagreeing.len(),
        disagreeing.iter().take(16).collect::<Vec<_>>()
    );
    Ok(())
}
