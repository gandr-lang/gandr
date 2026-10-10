//! Throwaway research scaffold on `research-whole-system`: the program and
//! declaration levels over the real corpus — every source parsed, lowered,
//! checked, readmitted and committed as records — serial and forked, plus
//! each declaration's kernel check re-run against a snapshot of its prefix.
//! Nothing here lands.
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
use gandr_kernel_core::LevelContext;
use gandr_kernel_core::check_declaration;
use gandr_storage_artifact::ArtifactRecordSet;
use gandr_storage_artifact::build;
use gandr_storage_records::BlockStore;
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::NodeHash;
use gandr_storage_records::RecordTreeError;
use gandr_storage_records::StoredNode;
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
use quenchant_shape::shape::Maybe;
use rayon::prelude::*;

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
    Duration::new(usage.utime.sec as u64, usage.utime.usec as u32 * 1000)
        + Duration::new(usage.stime.sec as u64, usage.stime.usec as u32 * 1000)
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

/// A block store that records every node size it admits.
#[derive(Default)]
struct Recording
{
    inner: InMemoryBlockStore,
    sizes: Vec<usize>,
}

impl BlockStore for Recording
{
    fn insert(
        &mut self,
        node: StoredNode<'_>,
    ) -> Result<(), RecordTreeError>
    {
        self.sizes.push(node.bytes().as_ref().len());
        self.inner.insert(node)
    }

    fn load(
        &self,
        hash: NodeHash,
    ) -> Result<StoredNode<'_>, RecordTreeError>
    {
        self.inner.load(hash)
    }
}

/// One source through the whole pipeline; stage times and a verdict digest.
#[derive(Clone, Default)]
struct Swept
{
    stages: [Duration; 5],
    declarations: usize,
    crossed: usize,
    digest: String,
    node_sizes: Vec<usize>,
    image_bytes: usize,
    kernel_decl_ns: Vec<u128>,
    core_decl_ns: Vec<u128>,
    snapshot_ok: bool,
}

fn sweep(
    pbg: &Pbg,
    text: &str,
    detail: bool,
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
    let start = Instant::now();
    let mut arena = CoreArena::new();
    let module = match lower_module(
        pbg,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    ) {
        | Ok(module) => module,
        | Err(_) => {
            out.digest = "lowering-refused".into();
            return out;
        },
    };
    let declarations = declarations(&module);
    out.declarations = declarations.len();
    out.stages[1] = start.elapsed();
    if detail {
        // Per-declaration core check cost, in order, on a copy.
        let mut copy = arena.clone();
        let mut context = CheckingContext::new(&mut copy, CheckBudget::DEFAULT);
        for declaration in &declarations {
            let start = Instant::now();
            let _ = gandr_core_checker::check_declaration(&mut context, declaration);
            out.core_decl_ns.push(start.elapsed().as_nanos());
        }
    }
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
    let names = module.structured_names();
    let artifact = readmission.export(names);
    out.image_bytes = artifact.as_image().as_ref().len();
    let mut store = Recording::default();
    if let Ok(records) = ArtifactRecordSet::from_artifact(artifact.as_image()) {
        let _ = build(&records, TreeParams::current(), &mut store);
    }
    out.stages[4] = start.elapsed();
    out.node_sizes = store.sizes;
    let environment = readmission.environment();
    out.crossed = environment.entries().len();
    out.digest = format!(
        "{:?}",
        verdicts
            .judged()
            .iter()
            .map(|j| format!("{:?}", j.verdict()))
            .collect::<Vec<_>>()
            .len()
    ) + &format!(
        "|{:?}",
        readmission
            .readmitted()
            .iter()
            .map(|r| format!("{:?}", r.outcome()))
            .collect::<Vec<_>>()
    );
    if detail {
        // Each admitted declaration's kernel check, re-run against a snapshot
        // of the final environment restricted to its prefix.
        let admitted = readmission.admitted();
        let entries = environment.entries();
        let mut scratch = environment.arena().clone();
        let floor = scratch.watermark();
        let mut ok = true;
        for (position, declaration) in admitted.iter().enumerate() {
            let levels = LevelContext::admit(
                declaration.levels().params(),
                declaration.levels().constraints().to_vec(),
            );
            let start = Instant::now();
            let verdict = levels.and_then(|levels| {
                check_declaration(&mut scratch, &entries[.. position], &levels, declaration)
            });
            out.kernel_decl_ns.push(start.elapsed().as_nanos());
            scratch.truncate_to(floor);
            ok &= verdict.is_ok();
        }
        // The same checks forked, one snapshot per worker.
        let forked: Vec<bool> = (0 .. admitted.len())
            .into_par_iter()
            .map_init(
                || environment.arena().clone(),
                |arena, position| {
                    let declaration = &admitted[position];
                    let verdict = LevelContext::admit(
                        declaration.levels().params(),
                        declaration.levels().constraints().to_vec(),
                    )
                    .and_then(|levels| {
                        check_declaration(arena, &entries[.. position], &levels, declaration)
                    });
                    arena.truncate_to(floor);
                    verdict.is_ok()
                },
            )
            .collect();
        out.snapshot_ok = ok && forked.iter().all(|&v| v) && forked.len() == admitted.len();
    }
    out
}

fn median(samples: &mut Vec<Duration>) -> Duration
{
    samples.sort_unstable();
    samples[samples.len() / 2]
}

fn main()
{
    let load = load_average();
    println!("# load {load}");
    let pbg = built_in().expect("the built-in grammar");
    let paths = sources();
    let texts: Vec<(PathBuf, String)> = paths
        .iter()
        .map(|p| (p.clone(), fs::read_to_string(p).unwrap()))
        .collect();
    let total_bytes: usize = texts.iter().map(|(_, t)| t.len()).sum();
    // Detail pass: per-source, per-stage, per-declaration.
    let detail: Vec<Swept> = texts
        .iter()
        .map(|(_, text)| sweep(&pbg, text, true))
        .collect();
    let mut stage_sum = [Duration::ZERO; 5];
    let mut all_nodes = Vec::new();
    let mut kernel_ns = Vec::new();
    let mut core_ns = Vec::new();
    for ((path, text), swept) in texts.iter().zip(&detail) {
        for (sum, t) in stage_sum.iter_mut().zip(swept.stages) {
            *sum += t;
        }
        all_nodes.extend(&swept.node_sizes);
        kernel_ns.extend(&swept.kernel_decl_ns);
        core_ns.extend(&swept.core_decl_ns);
        let name = path
            .strip_prefix(env!("CARGO_MANIFEST_DIR"))
            .unwrap()
            .display();
        let total: Duration = swept.stages.iter().sum();
        println!(
            "SOURCE,{name},bytes={},declarations={},crossed={},parse_ns={},lower_ns={},check_ns={},readmit_ns={},commit_ns={},total_ns={},image_bytes={},nodes={},kernel_decl_max_ns={},snapshot_recheck_ok={}",
            text.len(),
            swept.declarations,
            swept.crossed,
            swept.stages[0].as_nanos(),
            swept.stages[1].as_nanos(),
            swept.stages[2].as_nanos(),
            swept.stages[3].as_nanos(),
            swept.stages[4].as_nanos(),
            total.as_nanos(),
            swept.image_bytes,
            swept.node_sizes.len(),
            swept.kernel_decl_ns.iter().max().copied().unwrap_or(0),
            swept.snapshot_ok
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
    all_nodes.sort_unstable();
    kernel_ns.sort_unstable();
    core_ns.sort_unstable();
    let pct = |v: &Vec<usize>, p: usize| {
        v.get(v.len().saturating_sub(1) * p / 100)
            .copied()
            .unwrap_or(0)
    };
    let pctu = |v: &Vec<u128>, p: usize| {
        v.get(v.len().saturating_sub(1) * p / 100)
            .copied()
            .unwrap_or(0)
    };
    println!(
        "NODES,count={},p0={},p50={},p90={},p99={},p100={},total_bytes={}",
        all_nodes.len(),
        pct(&all_nodes, 0),
        pct(&all_nodes, 50),
        pct(&all_nodes, 90),
        pct(&all_nodes, 99),
        pct(&all_nodes, 100),
        all_nodes.iter().sum::<usize>()
    );
    println!(
        "KERNELDECL,count={},p50_ns={},p90_ns={},p99_ns={},max_ns={},sum_ns={}",
        kernel_ns.len(),
        pctu(&kernel_ns, 50),
        pctu(&kernel_ns, 90),
        pctu(&kernel_ns, 99),
        pctu(&kernel_ns, 100),
        kernel_ns.iter().sum::<u128>()
    );
    println!(
        "COREDECL,count={},p50_ns={},p90_ns={},p99_ns={},max_ns={},sum_ns={}",
        core_ns.len(),
        pctu(&core_ns, 50),
        pctu(&core_ns, 90),
        pctu(&core_ns, 99),
        pctu(&core_ns, 100),
        core_ns.iter().sum::<u128>()
    );
    if let Ok(path) = std::env::var("GANDR_NODE_SIZES") {
        fs::write(
            path,
            all_nodes
                .iter()
                .map(|n| n.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
        )
        .unwrap();
    }
    // Whole corpus as one program: sources independent, forked across widths.
    let serial_digest: Vec<String> = detail.iter().map(|s| s.digest.clone()).collect();
    let widths: Vec<usize> = std::env::var("GANDR_WIDTHS")
        .ok()
        .map(|s| s.split(',').filter_map(|w| w.parse().ok()).collect())
        .unwrap_or_else(|| vec![0, 1, 2, 4, 6, 8, 12, 16]);
    let reps: usize = std::env::var("GANDR_REPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(12);
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
    // Inside one source: where the parse goes (label, mold+meld fold,
    // commit), and whether its cost grows with length (the source repeated).
    let phases = |text: &str| -> (usize, [Duration; 3]) {
        let source = SourceText::from(text);
        let t0 = Instant::now();
        let tokens = label(SourceFragment::from(text));
        let t1 = Instant::now();
        let mut molder = Molder::new(&pbg);
        let mut state = MeldState::new(&pbg);
        molder.mold_stream(&mut state, &tokens, source);
        let t2 = Instant::now();
        let _ = state.commit_with_obligations(source);
        let t3 = Instant::now();
        (tokens.len(), [t1 - t0, t2 - t1, t3 - t2])
    };
    for &i in by_cost.iter().take(6) {
        let text = &texts[i].1;
        let mut best = [Duration::MAX; 3];
        let mut tokens = 0;
        for _ in 0 .. 5 {
            let (n, t) = phases(text);
            tokens = n;
            for (b, x) in best.iter_mut().zip(t) {
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
        for repeat in [1_usize, 2, 4, 8] {
            let long = text.repeat(repeat);
            let mut fastest = Duration::MAX;
            for _ in 0 .. 3 {
                let start = Instant::now();
                let _ = parse(&pbg, SourceText::from(long.as_str()));
                fastest = fastest.min(start.elapsed());
            }
            println!(
                "PARSESCALE,{name},repeat={repeat},bytes={},ns={},ns_per_byte={:.1}",
                long.len(),
                fastest.as_nanos(),
                fastest.as_nanos() as f64 / long.len() as f64
            );
        }
    }
    for width in widths {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(width.max(1))
            .build()
            .unwrap();
        let orders: Vec<(&str, &Vec<usize>)> = if width == 0 {
            vec![("serial", &by_file)]
        }
        else {
            vec![
                ("rayon", &by_file),
                ("queue-file", &by_file),
                ("queue-bytes", &by_bytes),
                ("queue-cost", &by_cost),
            ]
        };
        for (order_name, order) in orders {
            let mut walls = Vec::new();
            let mut cpus = Duration::ZERO;
            let mut wall_sum = Duration::ZERO;
            let mut same = true;
            pool.install(|| {
                for rep in 0 .. reps {
                    let cpu0 = cpu_time();
                    let start = Instant::now();
                    let swept: Vec<Swept> = if width == 0 {
                        texts
                            .iter()
                            .map(|(_, text)| sweep(&pbg, text, false))
                            .collect()
                    }
                    else if order_name == "rayon" {
                        // Recursive halving over file order; results stay in file order.
                        order
                            .par_iter()
                            .map(|&i| sweep(&pbg, &texts[i].1, false))
                            .collect()
                    }
                    else {
                        // One shared cursor over the order: each worker takes
                        // the next source, so a cost order is longest-first.
                        let next = std::sync::atomic::AtomicUsize::new(0);
                        let parts: Vec<Vec<(usize, Swept)>> = rayon::broadcast(|_| {
                            let mut mine = Vec::new();
                            loop {
                                let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                let Some(&i) = order.get(k)
                                else {
                                    break;
                                };
                                mine.push((i, sweep(&pbg, &texts[i].1, false)));
                            }
                            mine
                        });
                        let mut out: Vec<(usize, Swept)> = parts.into_iter().flatten().collect();
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
                    same &=
                        swept.iter().map(|s| s.digest.clone()).collect::<Vec<_>>() == serial_digest;
                }
            });
            let median = median(&mut walls);
            let load = load_average();
            println!(
                "PROGRAM,corpus,width={width},order={order_name},samples={},median_wall_us={:.1},busy_cores={:.2},utilization16={:.3},same_as_serial={same},load={load}",
                walls.len(),
                median.as_secs_f64() * 1.0e6,
                cpus.as_secs_f64() / wall_sum.as_secs_f64(),
                cpus.as_secs_f64() / wall_sum.as_secs_f64() / 16.0
            );
        }
    }
}
