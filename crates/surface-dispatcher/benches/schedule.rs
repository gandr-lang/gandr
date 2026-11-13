//! The measurement of the pool's hand-offs: one fork of 4,096 items on the
//! driver's pool, called from a thread outside the pool, at each width that the
//! run names.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `schedule, <graph>, <budget>` | one dependence schedule: each release and each commit on the calling thread, and each job on a worker or on the calling thread; under `park` a waiting party stops at once, and under `spin 10000` it polls 10,000 times first |
//! | `each` | one `Fork::each`: each item's job on a worker or on the calling thread |
//! | `each by an atomic cursor` | the hand-written fallback of `each`: one task for each thread of a `rayon` pool of the same width, each taking the next item from one shared atomic counter |
//!
//! Each job spins for its time. Each figure is the time of the whole fork,
//! given for each item, apart from the first commit: the median time from a
//! schedule's call to its first commit. The graphs of the schedule:
//!
//! | Graph | The edges |
//! | ----- | --------- |
//! | `none` | no edge, so every job may run at once |
//! | `stride 64` | each item waits on the item 64 places before it: 64 chains side by side |
//! | `chain` | each item waits on the item before it, so one job runs at a time |
//!
//! `cargo bench --bench schedule -- <threads>...` runs the full measurement at
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

use core::fmt;
use core::hint::black_box;
use core::num::NonZeroUsize;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use core::time::Duration;
use std::time::Instant;

use gandr_core_fork::Dependence;
use gandr_core_fork::Dependences;
use gandr_core_fork::Fork as _;
use gandr_core_fork::Releasing;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Spin;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Width;

use crate::support::Count;
use crate::support::Figures;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The items of one fork.
const ITEMS: usize = 4_096;

/// The distance of each edge of the `stride 64` graph.
const STRIDE: usize = 64;

/// The time each job spins for.
const JOBS: [JobNanos; 3] = [JobNanos(0), JobNanos(1_000), JobNanos(10_000)];

/// The time that one job spins for, in nanoseconds.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct JobNanos(u64);

/// The median time from a schedule's call to its first commit, in
/// nanoseconds.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct FirstCommit(u128);

/// A width that the run measures, in threads.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Measured(NonZeroUsize);

/// The edges of one graph of the schedule's rows.
#[derive(Clone, Copy)]
enum Graph
{
    /// No edge.
    None,
    /// Each item waits on the item [`STRIDE`] places before it.
    Stride,
    /// Each item waits on the item before it.
    Chain,
}

impl Graph
{
    /// Every graph, in the order of the table.
    const ALL: [Self; 3] = [Self::None, Self::Stride, Self::Chain];

    /// The dependences of the graph over [`ITEMS`] items.
    ///
    /// # Specification
    /// trivial.
    fn dependences(self) -> Dependences
    {
        let distance = match self {
            Self::None => return Dependences::default(),
            Self::Stride => STRIDE,
            Self::Chain => 1,
        };
        Dependences::new((distance .. ITEMS).map(|after| Dependence {
            before: after.saturating_sub(distance),
            after,
        }))
        .expect("each edge waits on an earlier item")
    }
}

impl fmt::Display for Graph
{
    /// The name of the graph's row in the table.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::None => "schedule, none",
            Self::Stride => "schedule, stride 64",
            Self::Chain => "schedule, chain",
        })
    }
}

/// Spin for the time of `job`.
///
/// # Specification
/// trivial.
fn spin(job: JobNanos)
{
    let JobNanos(nanos) = job;
    if nanos == 0 {
        return;
    }
    let until = Instant::now()
        .checked_add(Duration::from_nanos(nanos))
        .expect("the end of a spin fits");
    while Instant::now() < until {
        core::hint::spin_loop();
    }
}

/// The figures of one whole fork of [`ITEMS`] items, given for each item.
///
/// # Specification
/// trivial.
fn per_item(whole: &Figures) -> Figures
{
    let items = u128::try_from(ITEMS).expect("the count of items fits");
    Figures {
        median: whole.median.checked_div(items).expect("a nonzero count"),
        tail: whole.tail.checked_div(items).expect("a nonzero count"),
        allocations: whole.allocations,
    }
}

/// The time of one schedule of [`ITEMS`] jobs that each spin for `job` under
/// `after` on `pool`, given for each item, and the median time from the call
/// to its first commit.
///
/// # Specification
/// trivial.
fn scheduled(
    pool: &Pool,
    after: &Dependences,
    job: JobNanos,
    samples: Count,
) -> (Figures, FirstCommit)
{
    let mut items = vec![(); ITEMS];
    // The measurement runs each sample twice, and the room is kept before it,
    // so no push allocates inside it.
    let mut firsts: Vec<u128> = Vec::with_capacity(samples.0.saturating_mul(2));
    let whole = measure(Count(1), samples, || {
        let start = Instant::now();
        let mut first = None;
        pool.schedule(
            black_box(items.as_mut_slice()),
            after,
            |_position, _item| Releasing::<JobNanos, ()>::Run(job),
            |job| spin(black_box(job)),
            |_position, _item, ()| {
                first.get_or_insert_with(|| start.elapsed());
            },
        );
        if let Some(first) = first
            && firsts.len() < firsts.capacity()
        {
            firsts.push(first.as_nanos());
        }
    });
    firsts.sort_unstable();
    let middle = firsts.len().checked_div(2).unwrap_or_default();
    (
        per_item(&whole),
        FirstCommit(firsts.get(middle).copied().unwrap_or_default()),
    )
}

/// The time of one `each` over [`ITEMS`] items whose jobs each spin for `job`
/// on `pool`, given for each item.
///
/// # Specification
/// trivial.
fn each(
    pool: &Pool,
    job: JobNanos,
    samples: Count,
) -> Figures
{
    let mut items = vec![(); ITEMS];
    per_item(&measure(Count(1), samples, || {
        pool.each(
            black_box(items.as_mut_slice()),
            || (),
            |_state: &mut (), _item: &mut ()| spin(black_box(job)),
        );
    }))
}

/// The time of the hand-written fallback of `each` over [`ITEMS`] items whose
/// jobs each spin for `job`: one task for each thread of `threads`, each
/// taking the next item from one atomic counter, given for each item.
///
/// # Specification
/// trivial.
fn cursor(
    threads: &rayon::ThreadPool,
    job: JobNanos,
    samples: Count,
) -> Figures
{
    let next = AtomicUsize::new(0);
    per_item(&measure(Count(1), samples, || {
        next.store(0, Ordering::Relaxed);
        threads.in_place_scope(|scope| {
            for _ in 0 .. threads.current_num_threads() {
                scope.spawn(|_scope| {
                    while next.fetch_add(1, Ordering::Relaxed) < ITEMS {
                        spin(black_box(job));
                    }
                });
            }
        });
    }))
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
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "benchmark: the fallback's row builds one rayon pool per measured width"
    )
)]
fn main()
{
    let output = Output::of_run();
    let samples = match output {
        Output::Table => Count(20),
        Output::Silent => Count(1),
    };
    let table = matches!(output, Output::Table);
    if table {
        println!("Each figure is the time of one fork of {ITEMS} items, given for each item.");
        println!("The allocations are those of one fork.");
        println!();
        println!("| Fork | Job ns | Threads | First commit ns | p50 ns | p99 ns | Allocations |");
        println!("| ---- | ------ | ------- | --------------- | ------ | ------ | ----------- |");
    }
    let print = |lead: fmt::Arguments<'_>, figures: &Figures| {
        if table {
            print_row(lead, figures);
        }
    };
    for Measured(width) in widths() {
        let pools = [
            ("park", Pool::new(Width::Threads(Threads::from(width)))),
            (
                "spin 10000",
                Pool::new(Width::Threads(Threads::from(width))).spinning(Spin::from(10_000)),
            ),
        ];
        let threads = rayon::ThreadPoolBuilder::new()
            .num_threads(width.get())
            .build()
            .expect("the fallback's pool starts");
        for graph in Graph::ALL {
            let after = graph.dependences();
            for &(budget, ref pool) in &pools {
                for job in JOBS {
                    let (figures, FirstCommit(first)) = scheduled(pool, &after, job, samples);
                    print(
                        format_args!("{graph}, {budget} | {} | {width} | {first}", job.0),
                        &figures,
                    );
                }
            }
        }
        let [(_, ref pool), _] = pools;
        for job in JOBS {
            print(
                format_args!("each | {} | {width} | -", job.0),
                &each(pool, job, samples),
            );
            print(
                format_args!("each by an atomic cursor | {} | {width} | -", job.0),
                &cursor(&threads, job, samples),
            );
        }
    }
}
