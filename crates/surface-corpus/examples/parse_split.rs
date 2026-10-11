//! Research scratch: one source below the file — its top-level forms. The
//! variant for the parser before the form split.
//!
//! For each corpus source: parse it whole, then each top-level form's text
//! alone (the sibling scaffold's text split, the cuts read off the whole
//! parse); time both. Then the corpus parsed forked by `source` (whole
//! parses, costliest first) and by `segment` (every form's text, longest
//! first).
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
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::time::Duration;
use std::time::Instant;

use gandr_surface_grammar::built_in;
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
    let mut whole_sum = Duration::ZERO;
    let mut segment_sum = Duration::ZERO;
    let mut longest_source = Duration::ZERO;
    let mut longest_segment = Duration::ZERO;
    let mut whole_times = Vec::new();
    let mut segments: Vec<Vec<(usize, usize)>> = Vec::new();
    for (path, text) in paths.iter().zip(&texts) {
        let source = SourceText::from(text.as_str());
        let whole = parse(&pbg, source).expect("parse is total");
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
        let segs: Vec<(usize, usize)> = cuts.windows(2).map(|w| (w[0], w[1])).collect();
        let mut whole_t = Vec::new();
        for _ in 0 .. reps {
            let s = Instant::now();
            let _ = parse(&pbg, source);
            whole_t.push(s.elapsed());
        }
        let whole_t = median(&mut whole_t);
        let mut seg_t = Vec::new();
        for &(a, b) in &segs {
            let mut ts = Vec::new();
            for _ in 0 .. reps {
                let s = Instant::now();
                let _ = parse(&pbg, SourceText::from(&text[a .. b]));
                ts.push(s.elapsed());
            }
            seg_t.push(median(&mut ts));
        }
        let sum: Duration = seg_t.iter().sum();
        let max = seg_t.iter().max().copied().unwrap_or_default();
        whole_sum += whole_t;
        segment_sum += sum;
        longest_source = longest_source.max(whole_t);
        longest_segment = longest_segment.max(max);
        whole_times.push(whole_t);
        println!(
            "SPLIT,{},bytes={},segments={},whole_ns={},segments_sum_ns={},longest_segment_ns={}",
            path.strip_prefix(root).unwrap().display(),
            text.len(),
            segs.len(),
            whole_t.as_nanos(),
            sum.as_nanos(),
            max.as_nanos()
        );
        segments.push(segs);
    }
    println!(
        "SPLITSUM,sources={},whole_sum_us={:.1},segments_sum_us={:.1},longest_source_us={:.1},longest_segment_us={:.1},bound_by_source={:.2},bound_by_segment={:.2}",
        texts.len(),
        whole_sum.as_secs_f64() * 1.0e6,
        segment_sum.as_secs_f64() * 1.0e6,
        longest_source.as_secs_f64() * 1.0e6,
        longest_segment.as_secs_f64() * 1.0e6,
        whole_sum.as_secs_f64() / longest_source.as_secs_f64(),
        segment_sum.as_secs_f64() / longest_segment.as_secs_f64()
    );
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
        for unit in ["source", "segment"] {
            let mut walls = Vec::new();
            let mut cpu = Duration::ZERO;
            let mut wall_sum = Duration::ZERO;
            let all_joined = true;
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
                        | _ => unreachable!(),
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
