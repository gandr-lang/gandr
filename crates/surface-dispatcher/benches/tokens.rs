//! The measurement of the host's tokens: a free take and its give, on the
//! hub's counter and on the jobserver's FIFO, at each width that the run
//! names.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `counter` | one take with no wait and its give on the host's counter: atomic operations alone |
//! | `FIFO` | one read with no wait and its write on the jobserver's FIFO: two system calls |
//!
//! Each source holds 64 tokens, more than the threads, so no take waits. One
//! thread times its pairs while the other threads of the width take and give
//! on the same source, so each figure is the time of one pair under the
//! contention of that width.
//!
//! `cargo bench --bench tokens -- <threads>...` runs the full measurement at
//! each width that it names, or at one thread and at the host's width when it
//! names none, and prints one table. Under any other runner the binary runs one
//! short pass and prints nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

#[path = "../../theory-exact-reals/benches/support.rs"]
mod support;

use core::hint::black_box;
use core::num::NonZeroUsize;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering;
use std::io::Write as _;
use std::os::unix::fs::OpenOptionsExt as _;

use gandr_surface_dispatcher::Grant;
use gandr_surface_dispatcher::HostCounter;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Tokens;
use quenchant_shape::shape::Maybe;

use crate::support::Count;
use crate::support::Figures;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The tokens that each source holds.
const TOKENS: usize = 64;

/// The pairs of one timed batch.
const BATCH: Count = Count(1_000);

/// A width that the run measures, in threads.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Measured(NonZeroUsize);

/// One take with no wait and its give, when the take finds a token.
///
/// # Specification
/// trivial.
fn pair(tokens: &Tokens)
{
    if let Maybe::Present(token) = tokens.take_now() {
        tokens.give(black_box(token));
    }
}

/// The time of one pair on `tokens` while the other threads of `width` take
/// and give on the same source.
///
/// # Specification
/// trivial.
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "benchmark: the row measures a take under a fixed count of contending threads, so it starts the threads it counts"
    )
)]
fn pairs(
    tokens: &Tokens,
    width: Measured,
    samples: Count,
) -> Figures
{
    let stop = AtomicBool::new(false);
    std::thread::scope(|scope| {
        for _ in 1 .. width.0.get() {
            scope.spawn(|| {
                while !stop.load(Ordering::Relaxed) {
                    pair(tokens);
                }
            });
        }
        let figures = measure(BATCH, samples, || pair(tokens));
        stop.store(true, Ordering::Relaxed);
        figures
    })
}

/// The widths that the run names after `--bench`, or one thread and the
/// host's width when it names none.
///
/// # Specification
/// trivial.
fn widths() -> Vec<Measured>
{
    let named: Vec<Measured> = std::env::args()
        .skip(1)
        .filter_map(|argument| argument.parse::<NonZeroUsize>().ok().map(Measured))
        .collect();
    if !named.is_empty() {
        return named;
    }
    let host = std::thread::available_parallelism().unwrap_or(NonZeroUsize::MIN);
    if host == NonZeroUsize::MIN {
        vec![Measured(NonZeroUsize::MIN)]
    }
    else {
        vec![Measured(NonZeroUsize::MIN), Measured(host)]
    }
}

/// Run the measurement, or the short pass outside `cargo bench`.
///
/// # Specification
/// trivial.
fn main()
{
    let output = Output::of_run();
    let samples = match output {
        Output::Table => Count(200),
        Output::Silent => Count(1),
    };
    let directory = std::env::temp_dir().join(format!("gandr-bench-tokens-{}", std::process::id()));
    drop(std::fs::remove_dir_all(&directory));
    std::fs::create_dir_all(&directory).expect("the scratch directory is made");
    let path = directory.join("jobs");
    nix::unistd::mkfifo(
        &path,
        nix::sys::stat::Mode::S_IRUSR | nix::sys::stat::Mode::S_IWUSR,
    )
    .expect("the FIFO is made");
    // A FIFO keeps its bytes while one of its ends is open, as this one is.
    let mut parent = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .custom_flags(libc::O_NONBLOCK)
        .open(&path)
        .expect("the FIFO opens");
    parent
        .write_all(&[b'+'; TOKENS])
        .expect("the FIFO takes its tokens");
    let counter = HostCounter::with(
        &directory,
        Threads::from(NonZeroUsize::new(TOKENS).expect("a nonzero count")),
    )
    .expect("the counter opens");
    let sources = [
        ("counter", Grant::hosted(&directory).into_tokens()),
        (
            "FIFO",
            Grant::fifo(&path).expect("the FIFO opens").into_tokens(),
        ),
    ];
    let table = matches!(output, Output::Table);
    if table {
        println!("Each figure is the time of one take with no wait and its give.");
        println!();
        println!("| Tokens | Threads | p50 ns | p99 ns | Allocations |");
        println!("| ------ | ------- | ------ | ------ | ----------- |");
    }
    for Measured(width) in widths() {
        for &(name, ref tokens) in &sources {
            let Maybe::Present(ref tokens) = *tokens
            else {
                continue;
            };
            let figures = pairs(tokens, Measured(width), samples);
            if table {
                print_row(format_args!("{name} | {width}"), &figures);
            }
        }
    }
    drop(sources);
    drop(counter);
    drop(parent);
    drop(std::fs::remove_dir_all(&directory));
}
