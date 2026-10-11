//! Research scratch: one source below the file — its top-level forms.
//!
//! For each corpus source: parse it whole; parse it by form through the
//! parser's form-boundary contract (`FormSplit`: label once, mold each form
//! run from the boundary checkpoint, join); check the two agree; time the
//! whole parse, every unit, and the join. Then the corpus parsed forked by
//! `source` (whole parses, longest first), by `segment` (the sibling
//! scaffold's text split: each top-level form's text parsed alone, the cuts
//! read off a whole parse beforehand and not timed) and by `form` (every
//! unit of every source molded longest first, then each source's units
//! joined, sources longest first).
#![allow(
    warnings,
    unused,
    let_underscore,
    clippy::all,
    clippy::pedantic,
    clippy::restriction,
    clippy::nursery
)]

use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::time::Duration;
use std::time::Instant;

use gandr_surface_grammar::built_in;
use gandr_surface_parser::FormSplit;
use gandr_surface_parser::FormUnit;
use gandr_surface_parser::Molder;
use gandr_surface_parser::UnitSeam;
use gandr_surface_parser::parse;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;

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

fn walk(
    dir: &Path,
    out: &mut Vec<PathBuf>,
)
{
    let Ok(entries) = fs::read_dir(dir)
    else {
        return;
    };
    let mut entries: Vec<_> = entries.filter_map(Result::ok).map(|e| e.path()).collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            walk(&path, out);
        }
        else if path.extension().is_some_and(|e| e == "gandr") {
            out.push(path);
        }
    }
}

fn median(v: &mut Vec<Duration>) -> Duration
{
    v.sort();
    v[v.len() / 2]
}

/// Parse every source by form: label and predict per source, mold every
/// unit longest first on the pool, then join each source's units, sources
/// longest first. Returns how many sources' joins commit.
fn by_form(
    pbg: &gandr_surface_grammar::Pbg,
    texts: &[String],
    by_bytes: &[usize],
) -> usize
{
    // Label and predict, longest source first.
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
            *splits[i].lock().unwrap() =
                Some(FormSplit::new(&molder, SourceText::from(texts[i].as_str())));
        }
    });
    let splits: Vec<FormSplit<'_>> = splits
        .into_iter()
        .map(|s| s.into_inner().unwrap().unwrap())
        .collect();
    // Every unit, most tokens first.
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
    // Join, longest source first.
    let next = AtomicUsize::new(0);
    let slots: Vec<Mutex<Vec<Mutex<Option<FormUnit<'_>>>>>> =
        slots.into_iter().map(Mutex::new).collect();
    let joined = AtomicUsize::new(0);
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
            if splits[i].join(&mut molder, units).is_ok() {
                joined.fetch_add(1, Ordering::Relaxed);
            }
        }
    });
    joined.into_inner()
}

fn main()
{
    println!("# load {}", load_average());
    let pbg = built_in().expect("the built-in grammar");
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut paths = Vec::new();
    walk(&root.join("strict"), &mut paths);
    walk(&root.join("fixture"), &mut paths);
    let texts: Vec<String> = paths
        .iter()
        .map(|p| fs::read_to_string(p).unwrap())
        .collect();
    let reps = 7;
    let mut agree = 0;
    let mut whole_sum = Duration::ZERO;
    let mut unit_sum = Duration::ZERO;
    let mut join_sum = Duration::ZERO;
    let mut longest_source = Duration::ZERO;
    let mut longest_unit = Duration::ZERO;
    let mut held = 0;
    let mut broken = 0;
    let mut whole_times = Vec::new();
    let mut segments: Vec<Vec<(usize, usize)>> = Vec::new();
    for (path, text) in paths.iter().zip(&texts) {
        let source = SourceText::from(text.as_str());
        let whole = parse(&pbg, source).expect("parse is total");
        let mut molder = Molder::new(&pbg);
        let split = FormSplit::new(&molder, source);
        let units: Vec<FormUnit<'_>> = split
            .runs()
            .iter()
            .map(|&run| split.mold(&mut molder, run))
            .collect();
        let joined = split.join(&mut molder, units).expect("join commits");
        let agrees = *joined.result() == whole;
        agree += usize::from(agrees);
        let seams_held = joined
            .seams()
            .iter()
            .filter(|s| **s == UnitSeam::Joined)
            .count();
        held += seams_held;
        broken += joined.seams().len() - seams_held;
        // The sibling's text cuts, read off the whole tree.
        let tree = whole.tree();
        let mut cuts: Vec<usize> = tree
            .children(tree.root())
            .filter_map(|c| tree.node(c))
            .filter(|n| n.label() != NodeLabel::Space)
            .map(|n| usize::from(n.span().start()))
            .collect();
        if cuts.first() != Some(&0) {
            cuts.insert(0, 0);
        }
        cuts.push(text.len());
        cuts.dedup();
        segments.push(cuts.windows(2).map(|w| (w[0], w[1])).collect());
        // Times: whole, each unit (median of reps), the join.
        let mut whole_t = Vec::new();
        for _ in 0 .. reps {
            let s = Instant::now();
            let _ = parse(&pbg, source);
            whole_t.push(s.elapsed());
        }
        let whole_t = median(&mut whole_t);
        let mut unit_t = Vec::new();
        for &run in split.runs() {
            let mut ts = Vec::new();
            for _ in 0 .. reps {
                let s = Instant::now();
                let _ = split.mold(&mut molder, run);
                ts.push(s.elapsed());
            }
            unit_t.push(median(&mut ts));
        }
        let mut join_t = Vec::new();
        for _ in 0 .. reps {
            let units: Vec<FormUnit<'_>> = split
                .runs()
                .iter()
                .map(|&run| split.mold(&mut molder, run))
                .collect();
            let s = Instant::now();
            let _ = split.join(&mut molder, units);
            join_t.push(s.elapsed());
        }
        let join_t = median(&mut join_t);
        let sum: Duration = unit_t.iter().sum();
        let max = unit_t.iter().max().copied().unwrap_or_default();
        whole_sum += whole_t;
        unit_sum += sum;
        join_sum += join_t;
        longest_source = longest_source.max(whole_t);
        longest_unit = longest_unit.max(max);
        whole_times.push(whole_t);
        println!(
            "SPLIT,{},bytes={},runs={},held={seams_held},whole_ns={},units_sum_ns={},longest_unit_ns={},join_ns={},agrees={agrees}",
            path.strip_prefix(root).unwrap().display(),
            text.len(),
            split.runs().len(),
            whole_t.as_nanos(),
            sum.as_nanos(),
            max.as_nanos(),
            join_t.as_nanos()
        );
    }
    println!(
        "SPLITSUM,sources={},agree={agree},seams_held={held},seams_broken={broken},whole_sum_us={:.1},units_sum_us={:.1},join_sum_us={:.1},longest_source_us={:.1},longest_unit_us={:.1},bound_by_source={:.2},bound_by_unit={:.2}",
        texts.len(),
        whole_sum.as_secs_f64() * 1.0e6,
        unit_sum.as_secs_f64() * 1.0e6,
        join_sum.as_secs_f64() * 1.0e6,
        longest_source.as_secs_f64() * 1.0e6,
        longest_unit.as_secs_f64() * 1.0e6,
        whole_sum.as_secs_f64() / longest_source.as_secs_f64(),
        (unit_sum + join_sum).as_secs_f64() / longest_unit.as_secs_f64()
    );
    let by_bytes: Vec<usize> = {
        let mut v: Vec<usize> = (0 .. texts.len()).collect();
        v.sort_by_key(|&i| std::cmp::Reverse(texts[i].len()));
        v
    };
    let by_cost: Vec<usize> = {
        let mut v: Vec<usize> = (0 .. texts.len()).collect();
        v.sort_by_key(|&i| std::cmp::Reverse(whole_times[i]));
        v
    };
    let mut text_units: Vec<(usize, usize, usize)> = Vec::new();
    for (i, segs) in segments.iter().enumerate() {
        for &(a, b) in segs {
            text_units.push((i, a, b));
        }
    }
    text_units.sort_by_key(|&(_, a, b)| std::cmp::Reverse(b - a));
    let widths: Vec<usize> = std::env::var("GANDR_WIDTHS")
        .ok()
        .map(|s| s.split(',').filter_map(|w| w.parse().ok()).collect())
        .unwrap_or_else(|| vec![1, 2, 4, 6, 8, 12, 16]);
    let samples: usize = std::env::var("GANDR_REPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(12);
    for width in widths {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(width)
            .build()
            .unwrap();
        for unit in ["source", "segment", "form"] {
            let mut walls = Vec::new();
            let mut cpu = Duration::ZERO;
            let mut wall_sum = Duration::ZERO;
            let mut all_joined = true;
            pool.install(|| {
                for rep in 0 .. samples + 2 {
                    let c0 = cpu_time();
                    let s = Instant::now();
                    match unit {
                        | "source" => {
                            let next = AtomicUsize::new(0);
                            rayon::broadcast(|_| {
                                loop {
                                    let k = next.fetch_add(1, Ordering::Relaxed);
                                    let Some(&i) = by_cost.get(k)
                                    else {
                                        break;
                                    };
                                    let _ = parse(&pbg, SourceText::from(texts[i].as_str()));
                                }
                            });
                        },
                        | "segment" => {
                            let next = AtomicUsize::new(0);
                            rayon::broadcast(|_| {
                                loop {
                                    let k = next.fetch_add(1, Ordering::Relaxed);
                                    let Some(&(i, a, b)) = text_units.get(k)
                                    else {
                                        break;
                                    };
                                    let _ = parse(&pbg, SourceText::from(&texts[i][a .. b]));
                                }
                            });
                        },
                        | _ => {
                            all_joined &= by_form(&pbg, &texts, &by_bytes) == texts.len();
                        },
                    }
                    let wall = s.elapsed();
                    let c = cpu_time() - c0;
                    if rep >= 2 {
                        walls.push(wall);
                        wall_sum += wall;
                        cpu += c;
                    }
                }
            });
            println!(
                "PARSEPROGRAM,width={width},unit={unit},order=cost,samples={},median_wall_us={:.1},busy_cores={:.2},utilization16={:.3},all_committed={all_joined},load={}",
                walls.len(),
                median(&mut walls).as_secs_f64() * 1.0e6,
                cpu.as_secs_f64() / wall_sum.as_secs_f64(),
                cpu.as_secs_f64() / wall_sum.as_secs_f64() / 16.0,
                load_average()
            );
        }
    }
}
