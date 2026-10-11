//! Research scratch: the corpus as one program — every source parsed,
//! lowered, checked, readmitted and committed as records — serial and
//! forked. Re-cut from the whole-system scaffold without its kernel probes
//! (the per-declaration snapshot re-check and the speculation probe need
//! kernel APIs absent on `main`). `PROGRAM` forks by source; with
//! `GANDR_FORMS=1` the program also forks by top-level form: every form
//! unit of every source molded longest first, then each source joined and
//! carried through the rest of the check, longest first.
#![allow(
    warnings,
    unused,
    let_underscore,
    clippy::all,
    clippy::pedantic,
    clippy::restriction,
    clippy::nursery,
    clippy::cargo
)]

use std::fs;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::time::Duration;
use std::time::Instant;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::bridge;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_storage_artifact::ArtifactRecordSet;
use gandr_storage_artifact::build;
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::TreeParams;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::MeldState;
use gandr_surface_parser::Molder;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

/// `suseconds_t`: 32 bits on Darwin, 64 on Linux.
#[cfg(target_os = "macos")]
type Usec = i32;
#[cfg(not(target_os = "macos"))]
type Usec = i64;

#[repr(C)]
#[derive(Default)]
struct Timeval
{
    sec: i64,
    usec: Usec,
}

#[repr(C)]
#[derive(Default)]
struct Rusage
{
    utime: Timeval,
    stime: Timeval,
    rest: [i64; 14],
}

unsafe extern "C" {
    fn getrusage(
        who: i32,
        usage: *mut Rusage,
    ) -> i32;
}

fn cpu_time() -> Duration
{
    let mut usage = Rusage::default();
    unsafe { getrusage(0, &mut usage) };
    let user = Duration::new(usage.utime.sec as u64, usage.utime.usec as u32 * 1000);
    let system = Duration::new(usage.stime.sec as u64, usage.stime.usec as u32 * 1000);
    user + system
}

/// The 1, 5 and 15 minute load averages, slash-separated.
fn load_average() -> String
{
    if let Ok(text) = fs::read_to_string("/proc/loadavg") {
        return text
            .split_whitespace()
            .take(3)
            .collect::<Vec<_>>()
            .join("/");
    }
    std::process::Command::new("sysctl")
        .args(["-n", "vm.loadavg"])
        .output()
        .map(|o| {
            String::from_utf8_lossy(&o.stdout)
                .trim()
                .trim_matches(|c| c == '{' || c == '}')
                .trim()
                .replace(' ', "/")
        })
        .unwrap_or_default()
}

fn sources() -> Vec<PathBuf>
{
    let mut found = Vec::new();
    for root in ["strict", "fixture"] {
        let mut pending = vec![PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/")).join(root)];
        while let Some(directory) = pending.pop() {
            for entry in fs::read_dir(&directory).unwrap() {
                let entry = entry.unwrap();
                let kind = entry.file_type().unwrap();
                let path = entry.path();
                if kind.is_dir() {
                    pending.push(path);
                }
                else if !kind.is_symlink() && path.extension().is_some_and(|e| e == "gandr") {
                    found.push(path);
                }
            }
        }
    }
    found.sort();
    found
}

fn declarations(module: &LoweredModule<'_>) -> Vec<Declaration>
{
    module
        .declarations()
        .iter()
        .filter_map(|lowered| {
            let (declared, defined) = match lowered.outcome() {
                | DeclarationOutcome::Completed {
                    declared_type,
                    body,
                } => (Maybe::Present(declared_type), Maybe::Present(body)),
                | DeclarationOutcome::Uncompleted { declared_type } => (
                    Maybe::Present(declared_type),
                    Maybe::Absent(body::Absent::Hole),
                ),
                | DeclarationOutcome::Bodied { body } => (
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(body),
                ),
                | DeclarationOutcome::Refused(_) => return None,
            };
            Some(Declaration::new(
                lowered.constant(),
                declared,
                defined,
                OriginToken::from(usize::from(lowered.origin())),
            ))
        })
        .collect()
}

/// One source through the whole pipeline; stage times and a verdict digest.
#[derive(Clone, Default)]
struct Swept
{
    stages: [Duration; 5],
    declarations: usize,
    digest: String,
}

/// Everything after the parse.
fn check_tree(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    out: &mut Swept,
)
{
    let start = Instant::now();
    let mut arena = CoreArena::new();
    let module = match lower_module(
        pbg,
        tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    ) {
        | Ok(module) => module,
        | Err(_) => {
            out.digest = "lowering-refused".into();
            return;
        },
    };
    let declarations = declarations(&module);
    out.declarations = declarations.len();
    out.stages[1] = start.elapsed();
    let start = Instant::now();
    let verdicts = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &declarations,
    );
    out.stages[2] = start.elapsed();
    let start = Instant::now();
    let readmission = bridge::readmit(&mut arena, &verdicts);
    out.stages[3] = start.elapsed();
    let start = Instant::now();
    let artifact = readmission.export(module.structured_names());
    let mut store = InMemoryBlockStore::default();
    if let Ok(records) = ArtifactRecordSet::from_artifact(artifact.as_image()) {
        let _ = build(&records, TreeParams::current(), &mut store);
    }
    out.stages[4] = start.elapsed();
    out.digest = format!(
        "{}|{:?}",
        verdicts.judged().len(),
        readmission
            .readmitted()
            .iter()
            .map(|r| format!("{:?}", r.outcome()))
            .collect::<Vec<_>>()
    );
}

fn sweep(
    pbg: &Pbg,
    text: &str,
) -> Swept
{
    let mut out = Swept::default();
    let start = Instant::now();
    let tree = match parse(pbg, SourceText::from(text)) {
        | Ok(tree) => tree.into_tree(),
        | Err(_) => {
            out.digest = "parse-refused".into();
            return out;
        },
    };
    out.stages[0] = start.elapsed();
    check_tree(pbg, &tree, &mut out);
    out
}

/// The corpus checked forked by form: label and predict every source, mold
/// every unit longest first, then join and check each source, longest
/// first. Returns the digests in file order.
fn by_form(
    pbg: &Pbg,
    texts: &[(PathBuf, String)],
    by_bytes: &[usize],
) -> Vec<String>
{
    use gandr_surface_parser::FormSplit;
    use gandr_surface_parser::FormUnit;
    let next = AtomicUsize::new(0);
    let splits: Vec<Mutex<Option<FormSplit<'_>>>> =
        texts.iter().map(|_| Mutex::new(None)).collect();
    rayon::broadcast(|_| {
        let molder = Molder::new(pbg);
        loop {
            let k = next.fetch_add(1, Ordering::Relaxed);
            let Some(&i) = by_bytes.get(k)
            else {
                break;
            };
            *splits[i].lock().unwrap() = Some(FormSplit::new(
                &molder,
                SourceText::from(texts[i].1.as_str()),
            ));
        }
    });
    let splits: Vec<FormSplit<'_>> = splits
        .into_iter()
        .map(|s| s.into_inner().unwrap().unwrap())
        .collect();
    let mut units: Vec<(usize, usize, usize)> = Vec::new();
    for (i, split) in splits.iter().enumerate() {
        for (j, run) in split.runs().iter().enumerate() {
            units.push((usize::from(run.end()) - usize::from(run.start()), i, j));
        }
    }
    units.sort_by(|a, b| b.cmp(a));
    let slots: Vec<Vec<Mutex<Option<FormUnit<'_>>>>> = splits
        .iter()
        .map(|split| split.runs().iter().map(|_| Mutex::new(None)).collect())
        .collect();
    let next = AtomicUsize::new(0);
    rayon::broadcast(|_| {
        let mut molder = Molder::new(pbg);
        loop {
            let k = next.fetch_add(1, Ordering::Relaxed);
            let Some(&(_, i, j)) = units.get(k)
            else {
                break;
            };
            let run = splits[i].runs()[j];
            *slots[i][j].lock().unwrap() = Some(splits[i].mold(&mut molder, run));
        }
    });
    let slots: Vec<Mutex<Vec<Mutex<Option<FormUnit<'_>>>>>> =
        slots.into_iter().map(Mutex::new).collect();
    let digests: Vec<Mutex<String>> = texts.iter().map(|_| Mutex::new(String::new())).collect();
    let next = AtomicUsize::new(0);
    rayon::broadcast(|_| {
        let mut molder = Molder::new(pbg);
        loop {
            let k = next.fetch_add(1, Ordering::Relaxed);
            let Some(&i) = by_bytes.get(k)
            else {
                break;
            };
            let units: Vec<FormUnit<'_>> = std::mem::take(&mut *slots[i].lock().unwrap())
                .into_iter()
                .map(|slot| slot.into_inner().unwrap().unwrap())
                .collect();
            let mut out = Swept::default();
            match splits[i].join(&mut molder, units) {
                | Ok(joined) => {
                    let tree = joined.into_result().into_tree();
                    check_tree(pbg, &tree, &mut out);
                },
                | Err(_) => out.digest = "parse-refused".into(),
            }
            *digests[i].lock().unwrap() = out.digest;
        }
    });
    digests
        .into_iter()
        .map(|d| d.into_inner().unwrap())
        .collect()
}

fn median(samples: &mut Vec<Duration>) -> Duration
{
    samples.sort();
    samples[samples.len() / 2]
}

fn main()
{
    println!("# load {}", load_average());
    let pbg = built_in().expect("the built-in grammar");
    let texts: Vec<(PathBuf, String)> = sources()
        .into_iter()
        .map(|p| {
            let text = fs::read_to_string(&p).unwrap();
            (p, text)
        })
        .collect();
    let total_bytes: usize = texts.iter().map(|(_, t)| t.len()).sum();
    // Serial detail pass, best of three per source.
    let detail: Vec<Swept> = texts
        .iter()
        .map(|(_, text)| {
            let mut best = sweep(&pbg, text);
            for _ in 0 .. 2 {
                let again = sweep(&pbg, text);
                if again.stages.iter().sum::<Duration>() < best.stages.iter().sum::<Duration>() {
                    best = again;
                }
            }
            best
        })
        .collect();
    let mut stage_sum = [Duration::ZERO; 5];
    for ((path, text), swept) in texts.iter().zip(&detail) {
        for (sum, t) in stage_sum.iter_mut().zip(swept.stages) {
            *sum += t;
        }
        let name = path
            .strip_prefix(env!("CARGO_MANIFEST_DIR"))
            .unwrap()
            .display();
        println!(
            "SOURCE,{name},bytes={},declarations={},parse_ns={},lower_ns={},check_ns={},readmit_ns={},commit_ns={},total_ns={}",
            text.len(),
            swept.declarations,
            swept.stages[0].as_nanos(),
            swept.stages[1].as_nanos(),
            swept.stages[2].as_nanos(),
            swept.stages[3].as_nanos(),
            swept.stages[4].as_nanos(),
            swept.stages.iter().sum::<Duration>().as_nanos()
        );
    }
    let names = ["parse", "lower", "check", "readmit", "commit"];
    let stages: Vec<String> = names
        .iter()
        .zip(stage_sum)
        .map(|(n, t)| format!("{n}_us={:.1}", t.as_secs_f64() * 1.0e6))
        .collect();
    println!(
        "CORPUS,sources={},bytes={total_bytes},{}",
        texts.len(),
        stages.join(",")
    );
    let totals: Vec<Duration> = detail.iter().map(|s| s.stages.iter().sum()).collect();
    let longest = totals.iter().max().copied().unwrap_or_default();
    let work: Duration = totals.iter().sum();
    println!(
        "SPAN,longest_source_us={:.1},work_us={:.1},speedup_bound={:.2}",
        longest.as_secs_f64() * 1.0e6,
        work.as_secs_f64() * 1.0e6,
        work.as_secs_f64() / longest.as_secs_f64()
    );
    let by_bytes = {
        let mut order: Vec<usize> = (0 .. texts.len()).collect();
        order.sort_by_key(|&i| std::cmp::Reverse(texts[i].1.len()));
        order
    };
    let by_cost = {
        let mut order: Vec<usize> = (0 .. texts.len()).collect();
        order.sort_by_key(|&i| std::cmp::Reverse(totals[i]));
        order
    };
    let by_file: Vec<usize> = (0 .. texts.len()).collect();
    // Inside one source: label, mold-and-meld fold, commit, for the six
    // most expensive sources, best of five.
    for &i in by_cost.iter().take(6) {
        let text = &texts[i].1;
        let source = SourceText::from(text.as_str());
        let mut best = [Duration::MAX; 3];
        let mut tokens = 0;
        for _ in 0 .. 5 {
            let t0 = Instant::now();
            let labelled = label(SourceFragment::from(text.as_str()));
            let t1 = Instant::now();
            let mut molder = Molder::new(&pbg);
            let mut state = MeldState::new(&pbg);
            molder.mold_stream(&mut state, &labelled, source);
            let t2 = Instant::now();
            let _ = state.commit_with_obligations(source);
            let t3 = Instant::now();
            tokens = labelled.len();
            for (b, x) in best.iter_mut().zip([t1 - t0, t2 - t1, t3 - t2]) {
                *b = (*b).min(x);
            }
        }
        let name = texts[i]
            .0
            .strip_prefix(env!("CARGO_MANIFEST_DIR"))
            .unwrap()
            .display();
        println!(
            "PARSEPHASE,{name},bytes={},tokens={tokens},label_ns={},mold_meld_ns={},commit_ns={},ns_per_token={:.0}",
            text.len(),
            best[0].as_nanos(),
            best[1].as_nanos(),
            best[2].as_nanos(),
            (best[0] + best[1] + best[2]).as_nanos() as f64 / tokens.max(1) as f64
        );
    }
    let serial_digest: Vec<String> = detail.iter().map(|s| s.digest.clone()).collect();
    let widths: Vec<usize> = std::env::var("GANDR_WIDTHS")
        .ok()
        .map(|s| s.split(',').filter_map(|w| w.parse().ok()).collect())
        .unwrap_or_else(|| vec![0, 1, 2, 4, 6, 8, 12, 16]);
    let reps: usize = std::env::var("GANDR_REPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(12);
    let forms = std::env::var("GANDR_FORMS").is_ok();
    for width in widths {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(width.max(1))
            .build()
            .unwrap();
        let mut orders: Vec<(&str, &Vec<usize>)> = if width == 0 {
            vec![("serial", &by_file)]
        }
        else {
            vec![("queue-bytes", &by_bytes), ("queue-cost", &by_cost)]
        };
        if forms && width > 0 {
            orders.push(("forms", &by_bytes));
        }
        for (order_name, order) in orders {
            let mut walls = Vec::new();
            let mut cpus = Duration::ZERO;
            let mut wall_sum = Duration::ZERO;
            let mut same = true;
            pool.install(|| {
                for rep in 0 .. reps + 2 {
                    let cpu0 = cpu_time();
                    let start = Instant::now();
                    let digests: Vec<String> = if width == 0 {
                        texts
                            .iter()
                            .map(|(_, text)| sweep(&pbg, text).digest)
                            .collect()
                    }
                    else if order_name == "forms" {
                        by_form(&pbg, &texts, order)
                    }
                    else {
                        let next = AtomicUsize::new(0);
                        let parts: Vec<Vec<(usize, String)>> = rayon::broadcast(|_| {
                            let mut mine = Vec::new();
                            loop {
                                let k = next.fetch_add(1, Ordering::Relaxed);
                                let Some(&i) = order.get(k)
                                else {
                                    break;
                                };
                                mine.push((i, sweep(&pbg, &texts[i].1).digest));
                            }
                            mine
                        });
                        let mut out: Vec<(usize, String)> = parts.into_iter().flatten().collect();
                        out.sort_by_key(|(i, _)| *i);
                        out.into_iter().map(|(_, s)| s).collect()
                    };
                    let wall = start.elapsed();
                    let cpu = cpu_time() - cpu0;
                    if rep >= 2 {
                        walls.push(wall);
                        wall_sum += wall;
                        cpus += cpu;
                    }
                    same &= digests == serial_digest;
                }
            });
            println!(
                "PROGRAM,corpus,width={width},order={order_name},samples={},median_wall_us={:.1},busy_cores={:.2},utilization16={:.3},same_as_serial={same},load={}",
                walls.len(),
                median(&mut walls).as_secs_f64() * 1.0e6,
                cpus.as_secs_f64() / wall_sum.as_secs_f64(),
                cpus.as_secs_f64() / wall_sum.as_secs_f64() / 16.0,
                load_average()
            );
        }
    }
}
