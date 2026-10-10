//! Research scratch: the level below one source — its top-level forms.
//!
//! For each corpus source: parse it whole; cut the text at the start of
//! every top-level form (the root `Wald`'s non-layout children); parse each
//! segment alone; compare the segment trees, shifted, with the whole tree's
//! forms; time whole, segments serial, the longest segment, and segments
//! forked at each width.
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
use std::time::Duration;
use std::time::Instant;

use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
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

/// Every node under `at`, depth-first, as (label, start, end, depth) with
/// spans shifted by `shift`.
fn shape(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
    shift: usize,
    depth: usize,
    out: &mut Vec<(NodeLabel, usize, usize, usize)>,
)
{
    let Some(node) = tree.node(at)
    else {
        return;
    };
    let span = node.span();
    out.push((
        node.label(),
        usize::from(span.start()) + shift,
        usize::from(span.end()) + shift,
        depth,
    ));
    for child in tree.children(at) {
        shape(tree, child, shift, depth + 1, out);
    }
}

/// The root's children, shapes concatenated.
fn forms(
    tree: &SyntaxTree<'_>,
    shift: usize,
    out: &mut Vec<(NodeLabel, usize, usize, usize)>,
)
{
    for child in tree.children(tree.root()) {
        shape(tree, child, shift, 0, out);
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
    let reps = 7;
    let mut rows: Vec<(
        String,
        Duration,
        Vec<Duration>,
        Vec<(usize, usize)>,
        bool,
        String,
    )> = Vec::new();
    for path in &paths {
        let text = fs::read_to_string(path).unwrap();
        let whole = parse(&pbg, SourceText::from(text.as_str())).expect("parse is total");
        let tree = whole.tree();
        let starts: Vec<usize> = tree
            .children(tree.root())
            .filter_map(|c| tree.node(c))
            .filter(|n| n.label() != NodeLabel::Space)
            .map(|n| usize::from(n.span().start()))
            .collect();
        let mut cuts: Vec<usize> = starts.clone();
        if cuts.first() != Some(&0) {
            cuts.insert(0, 0);
        }
        cuts.push(text.len());
        cuts.dedup();
        let segments: Vec<(usize, usize)> = cuts.windows(2).map(|w| (w[0], w[1])).collect();
        // Agreement: forms of the whole tree versus the segments' forms,
        // shifted; obligations counted.
        let mut want = Vec::new();
        forms(tree, 0, &mut want);
        let mut got = Vec::new();
        let mut obligations = 0;
        for &(a, b) in &segments {
            let part = parse(&pbg, SourceText::from(&text[a .. b])).expect("parse is total");
            obligations += part.obligations().len();
            forms(part.tree(), a, &mut got);
        }
        let agrees = want == got && obligations == whole.obligations().len();
        let detail = if agrees {
            String::new()
        }
        else {
            let first = want
                .iter()
                .zip(&got)
                .position(|(x, y)| x != y)
                .unwrap_or(want.len().min(got.len()));
            format!(
                "first_difference={first}/{}/{},obligations={}/{}",
                want.len(),
                got.len(),
                whole.obligations().len(),
                obligations
            )
        };
        let mut whole_t = Vec::new();
        for _ in 0 .. reps {
            let s = Instant::now();
            let _ = parse(&pbg, SourceText::from(text.as_str()));
            whole_t.push(s.elapsed());
        }
        let mut seg_t = Vec::new();
        for &(a, b) in &segments {
            let mut ts = Vec::new();
            for _ in 0 .. reps {
                let s = Instant::now();
                let _ = parse(&pbg, SourceText::from(&text[a .. b]));
                ts.push(s.elapsed());
            }
            seg_t.push(median(&mut ts));
        }
        let name = path.strip_prefix(root).unwrap().display().to_string();
        rows.push((name, median(&mut whole_t), seg_t, segments, agrees, detail));
    }
    let mut agree_count = 0;
    let mut whole_sum = Duration::ZERO;
    let mut seg_sum = Duration::ZERO;
    let mut longest_source = Duration::ZERO;
    let mut longest_segment = Duration::ZERO;
    for (name, whole, segs, segments, agrees, detail) in &rows {
        let sum: Duration = segs.iter().sum();
        let max = segs.iter().max().copied().unwrap_or_default();
        agree_count += usize::from(*agrees);
        whole_sum += *whole;
        seg_sum += sum;
        longest_source = longest_source.max(*whole);
        longest_segment = longest_segment.max(max);
        println!(
            "SPLIT,{name},segments={},whole_ns={},segments_sum_ns={},longest_segment_ns={},agrees={agrees}{}{detail}",
            segments.len(),
            whole.as_nanos(),
            sum.as_nanos(),
            max.as_nanos(),
            if detail.is_empty() { "" } else { "," }
        );
    }
    println!(
        "SPLITSUM,sources={},agree={agree_count},whole_sum_us={:.1},segments_sum_us={:.1},longest_source_us={:.1},longest_segment_us={:.1},bound_by_source={:.2},bound_by_segment={:.2}",
        rows.len(),
        whole_sum.as_secs_f64() * 1.0e6,
        seg_sum.as_secs_f64() * 1.0e6,
        longest_source.as_secs_f64() * 1.0e6,
        longest_segment.as_secs_f64() * 1.0e6,
        whole_sum.as_secs_f64() / longest_source.as_secs_f64(),
        seg_sum.as_secs_f64() / longest_segment.as_secs_f64()
    );
    // The corpus parsed as segments, longest first, one shared cursor.
    let texts: Vec<String> = paths
        .iter()
        .map(|p| fs::read_to_string(p).unwrap())
        .collect();
    let mut units: Vec<(usize, usize, usize, Duration)> = Vec::new();
    for (i, (_, _, segs, segments, ..)) in rows.iter().enumerate() {
        for (&(a, b), &t) in segments.iter().zip(segs) {
            units.push((i, a, b, t));
        }
    }
    units.sort_by_key(|u| std::cmp::Reverse(u.3));
    let sources: Vec<(usize, Duration)> = {
        let mut v: Vec<(usize, Duration)> =
            rows.iter().enumerate().map(|(i, r)| (i, r.1)).collect();
        v.sort_by_key(|u| std::cmp::Reverse(u.1));
        v
    };
    let widths: Vec<usize> = std::env::var("GANDR_WIDTHS")
        .ok()
        .map(|s| s.split(',').filter_map(|w| w.parse().ok()).collect())
        .unwrap_or_else(|| vec![1, 2, 4, 6, 8, 12, 16]);
    for width in widths {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(width)
            .build()
            .unwrap();
        for unit in ["source", "segment"] {
            let mut walls = Vec::new();
            let mut cpu = Duration::ZERO;
            let mut wall_sum = Duration::ZERO;
            pool.install(|| {
                for rep in 0 .. 12 {
                    let c0 = cpu_time();
                    let s = Instant::now();
                    let next = std::sync::atomic::AtomicUsize::new(0);
                    rayon::broadcast(|_| {
                        loop {
                            let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            if unit == "source" {
                                let Some(&(i, _)) = sources.get(k)
                                else {
                                    break;
                                };
                                let _ = parse(&pbg, SourceText::from(texts[i].as_str()));
                            }
                            else {
                                let Some(&(i, a, b, _)) = units.get(k)
                                else {
                                    break;
                                };
                                let _ = parse(&pbg, SourceText::from(&texts[i][a .. b]));
                            }
                        }
                    });
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
                "PARSEPROGRAM,width={width},unit={unit},order=cost,samples={},median_wall_us={:.1},busy_cores={:.2},utilization16={:.3},load={}",
                walls.len(),
                median(&mut walls).as_secs_f64() * 1.0e6,
                cpu.as_secs_f64() / wall_sum.as_secs_f64(),
                cpu.as_secs_f64() / wall_sum.as_secs_f64() / 16.0,
                load_average()
            );
        }
    }
}
