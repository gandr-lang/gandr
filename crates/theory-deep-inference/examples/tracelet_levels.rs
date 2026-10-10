//! Throwaway research scaffold on `research-whole-system`: what one replay
//! level costs against the barrier a fork-join would add, on a plan built by
//! the crate's own certified normalization. Nothing here lands.
//!
//! The peak is a balanced `add` tree with `W` leaves `succ(zero)`; level `l`
//! fires `grow` (even) or `shrink` (odd) at every leaf, so each level is an
//! antichain of width `W`.

#![allow(
    warnings,
    unused,
    clippy::all,
    clippy::pedantic,
    clippy::restriction,
    clippy::nursery,
    clippy::cargo
)]

use std::time::Duration;
use std::time::Instant;

use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::rewrite_at;
use gandr_theory_deep_inference::normalize_certified;
use quenchant_shape::shape::Maybe;

type Cmd = Toy;

fn tree(width: usize) -> Cmd
{
    if width == 1 {
        return Toy::succ(Toy::zero());
    }
    Toy::add(tree(width / 2), tree(width - width / 2))
}

/// Leaf paths of `tree(width)`, left to right.
fn leaves(
    width: usize,
    prefix: &mut Vec<usize>,
    out: &mut Vec<Vec<usize>>,
)
{
    if width == 1 {
        out.push(prefix.clone());
        return;
    }
    prefix.push(0);
    leaves(width / 2, prefix, out);
    prefix.pop();
    prefix.push(1);
    leaves(width - width / 2, prefix, out);
    prefix.pop();
}

fn pos(path: &[usize]) -> <ToyAlphabet as gandr_theory_cell_complexes::CellAlphabet>::Pos
{
    let steps: Vec<PositionStep> = path.iter().map(|&s| PositionStep::from(s)).collect();
    ToyAlphabet::position_at_path(&steps)
}

/// Serial: one whole-term rewrite per step, as `run_schedule` does.
fn fire_serial(
    store: &CellStore<ToyAlphabet>,
    start: &Cmd,
    steps: &[(CellId, Vec<usize>)],
) -> Cmd
{
    let mut current = start.clone();
    for (cell, path) in steps {
        let Maybe::Present(cell) = store.get(*cell)
        else {
            panic!("cell")
        };
        let Maybe::Present(next) = rewrite_at(cell, &current, &pos(path))
        else {
            panic!("fires")
        };
        current = next;
    }
    current
}

/// A level fired by recursive descent: steps partitioned by their next path
/// step, subterms rewritten independently (in parallel when `fork`), and
/// spliced back once per node.
fn fire_split(
    store: &CellStore<ToyAlphabet>,
    term: &Cmd,
    steps: &[(CellId, Vec<usize>)],
    depth: usize,
    fork: bool,
    grain: usize,
) -> Cmd
{
    if steps.is_empty() {
        return term.clone();
    }
    if steps.iter().any(|(_, path)| path.len() == depth) || steps.len() <= grain {
        let relative: Vec<(CellId, Vec<usize>)> = steps
            .iter()
            .map(|(c, p)| (*c, p[depth ..].to_vec()))
            .collect();
        return fire_serial(store, term, &relative);
    }
    let (left, right): (Vec<_>, Vec<_>) = steps
        .iter()
        .cloned()
        .partition(|(_, path)| path[depth] == 0);
    let child = |index: usize| {
        let Maybe::Present(sub) = ToyAlphabet::subterm_cmd_at(term, &pos(&[index]))
        else {
            panic!("child")
        };
        sub
    };
    let (l, r) = if fork && left.len() + right.len() > grain {
        rayon::join(
            || fire_split(store, &child(0), &left, depth + 1, fork, grain),
            || fire_split(store, &child(1), &right, depth + 1, fork, grain),
        )
    }
    else {
        (
            fire_split(store, &child(0), &left, depth + 1, fork, grain),
            fire_split(store, &child(1), &right, depth + 1, fork, grain),
        )
    };
    let with_left = ToyAlphabet::splice_cmd_at(term, &pos(&[0]), l).expect("splice");
    ToyAlphabet::splice_cmd_at(&with_left, &pos(&[1]), r).expect("splice")
}

fn median(samples: &mut Vec<Duration>) -> u128
{
    samples.sort_unstable();
    samples[samples.len() / 2].as_nanos()
}

fn main()
{
    let load = std::fs::read_to_string("/proc/loadavg")
        .map(|text| {
            text.split_whitespace()
                .take(3)
                .collect::<Vec<_>>()
                .join("/")
        })
        .unwrap_or_else(|_| {
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
        });
    println!("# load {load}");
    let widths: Vec<usize> = std::env::var("GANDR_WIDTHS")
        .ok()
        .map(|s| s.split(',').filter_map(|w| w.parse().ok()).collect())
        .unwrap_or_else(|| vec![1, 2, 4, 6, 8, 12, 16]);
    let mut store = CellStore::new();
    let grow = store.insert(toy_cell(
        Toy::succ(Toy::zero()),
        Toy::add(Toy::zero(), Toy::zero()),
    ));
    let shrink = store.insert(toy_cell(
        Toy::add(Toy::zero(), Toy::zero()),
        Toy::succ(Toy::zero()),
    ));
    let levels_count = 4;
    for width in [4_usize, 16, 64, 256, 1024] {
        let peak = tree(width);
        let mut paths = Vec::new();
        leaves(width, &mut Vec::new(), &mut paths);
        let mut path: Vec<CellApp<ToyAlphabet>> = Vec::new();
        let mut levels: Vec<Vec<(CellId, Vec<usize>)>> = Vec::new();
        for level in 0 .. levels_count {
            let cell = if level % 2 == 0 { grow } else { shrink };
            let steps: Vec<(CellId, Vec<usize>)> =
                paths.iter().map(|p| (cell, p.clone())).collect();
            path.extend(steps.iter().map(|(c, p)| CellApp {
                cell: *c,
                at: pos(p),
            }));
            levels.push(steps);
        }
        // The crate's own plan, built by certified normalization.
        let start = Instant::now();
        let witness = if width <= 256 {
            normalize_certified(&store, &peak, &peak, &path).ok()
        }
        else {
            None
        };
        let plan_ns = start.elapsed().as_nanos();
        let plan_widths: Vec<usize> = witness
            .as_ref()
            .map(|w| w.replay_plan().levels().iter().map(Vec::len).collect())
            .unwrap_or_default();
        let reps = if width >= 256 { 9 } else { 25 };
        // Serial, as run_schedule fires a level: one whole-term rewrite per step.
        let mut serial = Vec::new();
        let mut reached = peak.clone();
        for _ in 0 .. reps {
            let start = Instant::now();
            let mut current = peak.clone();
            for level in &levels {
                current = fire_serial(&store, &current, level);
            }
            serial.push(start.elapsed());
            reached = current;
        }
        assert_eq!(reached, peak, "four levels return to the peak");
        if let Some(witness) = &witness {
            let plan = witness.replay_plan();
            let mut planned = Vec::new();
            for _ in 0 .. reps {
                let start = Instant::now();
                let out = plan.replay_with_fuel(&store, plan.critical_path());
                planned.push(start.elapsed());
                assert!(matches!(out, Ok(Maybe::Present(_))));
            }
            println!(
                "PLAN,width={width},levels={},plan_widths={:?},plan_build_ns={plan_ns},replay_with_fuel_ns={}",
                plan_widths.len(),
                plan_widths,
                median(&mut planned)
            );
        }
        let serial_ns = median(&mut serial);
        let size = usize::from(ToyAlphabet::cmd_size(&peak));
        println!(
            "SERIAL,width={width},size={size},levels={levels_count},ns={serial_ns},per_level_ns={}",
            serial_ns / levels_count as u128
        );
        for (label, fork, grain) in [
            ("descent", false, 1_usize),
            ("descent_fork", true, 1),
            ("descent_fork", true, 8),
            ("descent_fork", true, 32),
        ] {
            for threads in widths.iter().copied() {
                if !fork && threads > 1 {
                    continue;
                }
                let pool = rayon::ThreadPoolBuilder::new()
                    .num_threads(threads)
                    .build()
                    .unwrap();
                let mut samples = Vec::new();
                pool.install(|| {
                    for _ in 0 .. reps {
                        let start = Instant::now();
                        let mut current = peak.clone();
                        for level in &levels {
                            current = fire_split(&store, &current, level, 0, fork, grain);
                        }
                        samples.push(start.elapsed());
                        assert_eq!(current, peak, "the split levels reach the same term");
                    }
                });
                println!(
                    "LEVEL,width={width},mode={label},grain={grain},threads={threads},ns={},serial_ns={serial_ns}",
                    median(&mut samples)
                );
            }
        }
        // Barrier floor: an empty fork-join per level.
        for threads in widths.iter().copied().filter(|&t| t > 1) {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap();
            let mut samples = Vec::new();
            pool.install(|| {
                for _ in 0 .. 1000 {
                    let start = Instant::now();
                    rayon::scope(|s| {
                        for _ in 0 .. threads {
                            s.spawn(|_| {});
                        }
                    });
                    samples.push(start.elapsed());
                }
            });
            println!(
                "BARRIER,width={width},threads={threads},empty_scope_ns={}",
                median(&mut samples)
            );
        }
        // Interleaving: P independent plans (declarations), each serial, run
        // together with no barrier between them.
        let plans = 16;
        for threads in widths.iter().copied() {
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap();
            let mut samples = Vec::new();
            pool.install(|| {
                use rayon::prelude::*;
                for _ in 0 .. reps.min(9) {
                    let start = Instant::now();
                    let out: Vec<Cmd> = (0 .. plans)
                        .into_par_iter()
                        .map(|_| {
                            let mut current = peak.clone();
                            for level in &levels {
                                current = fire_split(&store, &current, level, 0, false, 1);
                            }
                            current
                        })
                        .collect();
                    samples.push(start.elapsed());
                    assert!(out.iter().all(|t| *t == peak));
                }
            });
            println!(
                "INTERLEAVE,width={width},plans={plans},threads={threads},ns={}",
                median(&mut samples)
            );
        }
    }
}
