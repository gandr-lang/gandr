//! Research scratch: the molder's per-token cost.
//!
//! `mold_profile loop FILE N` parses FILE N times (for a sampling profiler).
//! `mold_profile tokens [REPS]` prints, per source, the fold's best-of-REPS
//! cost per significant token, then the corpus summary.
//! `mold_profile allocs` counts the fold's allocations; only that mode turns
//! the counting allocator on, so the timed modes pay one relaxed load per
//! allocation.

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

use gandr_surface_grammar::built_in;
use gandr_surface_parser::MeldState;
use gandr_surface_parser::Molder;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;

struct Counting;

static ALLOCS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static ALLOC_BYTES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static COUNTING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

unsafe impl std::alloc::GlobalAlloc for Counting
{
    unsafe fn alloc(
        &self,
        layout: std::alloc::Layout,
    ) -> *mut u8
    {
        if COUNTING.load(std::sync::atomic::Ordering::Relaxed) {
            ALLOCS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            ALLOC_BYTES.fetch_add(layout.size() as u64, std::sync::atomic::Ordering::Relaxed);
        }
        unsafe { std::alloc::System.alloc(layout) }
    }

    unsafe fn dealloc(
        &self,
        ptr: *mut u8,
        layout: std::alloc::Layout,
    )
    {
        unsafe { std::alloc::System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(
        &self,
        ptr: *mut u8,
        layout: std::alloc::Layout,
        new_size: usize,
    ) -> *mut u8
    {
        if COUNTING.load(std::sync::atomic::Ordering::Relaxed) {
            ALLOCS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            ALLOC_BYTES.fetch_add(new_size as u64, std::sync::atomic::Ordering::Relaxed);
        }
        unsafe { std::alloc::System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

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

fn main()
{
    let args: Vec<String> = std::env::args().collect();
    let pbg = built_in().expect("the built-in grammar");
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    match args.get(1).map(String::as_str) {
        | Some("loop") => {
            let text = fs::read_to_string(&args[2]).unwrap();
            let n: usize = args[3].parse().unwrap();
            for _ in 0 .. n {
                let _ = std::hint::black_box(parse(&pbg, SourceText::from(text.as_str())));
            }
        },
        | Some("oracle") => {
            // Every node (label, span, digest) and every obligation of every
            // corpus source, then of malformed variants: each source cut at
            // eight token boundaries and with one significant token dropped at
            // eight positions.
            use std::fmt::Write as _;
            let mut paths = Vec::new();
            walk(&root.join("strict"), &mut paths);
            walk(&root.join("fixture"), &mut paths);
            walk(&root.join("../surface-parser/tests/fixtures"), &mut paths);
            let mut out = String::new();
            let mut dump = |name: &str, text: &str, out: &mut String| {
                let parsed = parse(&pbg, SourceText::from(text)).expect("parse is total");
                let tree = parsed.tree();
                writeln!(out, "SOURCE {name} bytes={}", text.len()).unwrap();
                for position in tree.positions() {
                    let node = tree.node(position).unwrap();
                    let children: Vec<String> =
                        tree.children(position).map(|c| format!("{c:?}")).collect();
                    writeln!(
                        out,
                        "  {position:?} {:?} {:?} {:?} [{}]",
                        node.label(),
                        node.span(),
                        node.digest(),
                        children.join(",")
                    )
                    .unwrap();
                }
                for obligation in parsed.obligations() {
                    writeln!(out, "  OBLIGATION {obligation:?}").unwrap();
                }
            };
            for path in &paths {
                let text = fs::read_to_string(path).unwrap();
                let name = path
                    .strip_prefix(root)
                    .unwrap_or(path)
                    .display()
                    .to_string();
                dump(&name, &text, &mut out);
                let tokens = label(SourceFragment::from(text.as_str()));
                let significant: Vec<_> = tokens
                    .iter()
                    .filter(|t| !matches!(t.lexeme, gandr_surface_parser::Lexeme::Space))
                    .copied()
                    .collect();
                for k in 1 ..= 8 {
                    let Some(token) = significant.get(significant.len() * k / 9)
                    else {
                        continue;
                    };
                    let cut = &text[.. token.start as usize];
                    dump(&format!("{name}#cut{k}"), cut, &mut out);
                    let dropped = format!(
                        "{}{}",
                        &text[.. token.start as usize],
                        &text[token.end as usize ..]
                    );
                    dump(&format!("{name}#drop{k}"), &dropped, &mut out);
                }
            }
            fs::write(&args[2], out).unwrap();
        },
        | Some("allocs") => {
            COUNTING.store(true, std::sync::atomic::Ordering::Relaxed);
            let mut paths = Vec::new();
            walk(&root.join("strict"), &mut paths);
            walk(&root.join("fixture"), &mut paths);
            let mut rows: Vec<(usize, usize, u64, u64)> = Vec::new();
            for path in &paths {
                let text = fs::read_to_string(path).unwrap();
                let source = SourceText::from(text.as_str());
                let tokens = label(SourceFragment::from(text.as_str()));
                let significant = tokens
                    .iter()
                    .filter(|t| !matches!(t.lexeme, gandr_surface_parser::Lexeme::Space))
                    .count();
                let mut molder = Molder::new(&pbg);
                let mut state = MeldState::new(&pbg);
                let a0 = ALLOCS.load(std::sync::atomic::Ordering::Relaxed);
                let b0 = ALLOC_BYTES.load(std::sync::atomic::Ordering::Relaxed);
                molder.mold_stream(&mut state, &tokens, source);
                let a1 = ALLOCS.load(std::sync::atomic::Ordering::Relaxed);
                let b1 = ALLOC_BYTES.load(std::sync::atomic::Ordering::Relaxed);
                rows.push((text.len(), significant, a1 - a0, b1 - b0));
            }
            let mut order: Vec<usize> = (0 .. rows.len()).collect();
            order.sort_by_key(|&i| std::cmp::Reverse(rows[i].0));
            for (label, set) in [
                ("six-longest", order[.. 6].to_vec()),
                ("corpus", (0 .. rows.len()).collect::<Vec<_>>()),
            ] {
                let tokens: usize = set.iter().map(|&i| rows[i].1).sum();
                let allocs: u64 = set.iter().map(|&i| rows[i].2).sum();
                let bytes: u64 = set.iter().map(|&i| rows[i].3).sum();
                println!(
                    "ALLOCSUM,{label},tokens={tokens},allocs_per_token={:.2},alloc_bytes_per_token={:.1}",
                    allocs as f64 / tokens as f64,
                    bytes as f64 / tokens as f64
                );
            }
        },
        | _ => {
            let reps: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(25);
            let mut paths = Vec::new();
            walk(&root.join("strict"), &mut paths);
            walk(&root.join("fixture"), &mut paths);
            let mut per_token = Vec::new();
            let mut weighted: Vec<(f64, usize)> = Vec::new();
            let mut total_ns = 0_u128;
            let mut total_tokens = 0_usize;
            for path in &paths {
                let text = fs::read_to_string(path).unwrap();
                let source = SourceText::from(text.as_str());
                let tokens = label(SourceFragment::from(text.as_str()));
                let significant = tokens
                    .iter()
                    .filter(|t| !matches!(t.lexeme, gandr_surface_parser::Lexeme::Space))
                    .count();
                let mut best = Duration::MAX;
                for _ in 0 .. reps {
                    let mut molder = Molder::new(&pbg);
                    let mut state = MeldState::new(&pbg);
                    let start = Instant::now();
                    molder.mold_stream(&mut state, &tokens, source);
                    best = best.min(start.elapsed());
                    std::hint::black_box(&state);
                }
                let ns = best.as_nanos() as f64 / significant.max(1) as f64;
                per_token.push(ns);
                weighted.push((ns, significant));
                total_ns += best.as_nanos();
                total_tokens += significant;
                println!(
                    "TOKEN,{},bytes={},tokens={},significant={},mold_ns={},ns_per_token={:.0}",
                    path.strip_prefix(root).unwrap().display(),
                    text.len(),
                    tokens.len(),
                    significant,
                    best.as_nanos(),
                    ns
                );
            }
            per_token.sort_by(f64::total_cmp);
            // The median token: sources ordered by cost per token, each
            // weighted by its significant tokens.
            weighted.sort_by(|a, b| a.0.total_cmp(&b.0));
            let mut seen = 0_usize;
            let median_token = weighted
                .iter()
                .find(|&&(_, n)| {
                    seen += n;
                    seen * 2 >= total_tokens
                })
                .map_or(0.0, |&(ns, _)| ns);
            println!(
                "TOKENSUM,sources={},tokens={total_tokens},mold_us={:.1},mean_ns_per_token={:.0},median_token_ns={median_token:.0},median_source_ns_per_token={:.0},p90={:.0},max={:.0}",
                paths.len(),
                total_ns as f64 / 1.0e3,
                total_ns as f64 / total_tokens as f64,
                per_token[per_token.len() / 2],
                per_token[per_token.len() * 9 / 10],
                per_token[per_token.len() - 1]
            );
        },
    }
}
