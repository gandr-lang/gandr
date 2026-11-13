//! The measurement of the pool's hand-offs: one fork of 4,096 items on the
//! driver's pool, called from a thread outside the pool, at each width that the
//! run names.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `schedule, <graph>` | one dependence schedule: each release and each commit on the calling thread, and each job on a worker or on the calling thread |
//! | `each` | one `Fork::each`: each item's job on a worker or on the calling thread |
//! | `each by an atomic cursor` | the hand-written fallback of `each`: one task for each thread of a `rayon` pool of the same width, each taking the next item from one shared atomic counter |
//!
//! Each job spins for its time. Each figure is the time of the whole fork,
//! given for each item. The graphs of the schedule:
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

/// The time each job spins for, in nanoseconds.
const JOBS: [u64; 3] = [0, 1_000, 10_000];

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

    /// The name of the graph's row in the table.
    ///
    /// # Specification
    /// trivial.
    const fn row(self) -> &'static str
    {
        match self {
            Self::None => "schedule, none",
            Self::Stride => "schedule, stride 64",
            Self::Chain => "schedule, chain",
        }
    }

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

/// Spin for `nanos` nanoseconds.
///
/// # Specification
/// trivial.
fn spin(nanos: u64)
{
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

/// The time of one schedule of [`ITEMS`] jobs that each spin for `job`
/// nanoseconds under `after` on `pool`, given for each item.
///
/// # Specification
/// trivial.
fn scheduled(
    pool: &Pool,
    after: &Dependences,
    job: u64,
    samples: Count,
) -> Figures
{
    let mut items = vec![(); ITEMS];
    per_item(&measure(Count(1), samples, || {
        pool.schedule(
            black_box(items.as_mut_slice()),
            after,
            |_position, _item| Releasing::<u64, ()>::Run(job),
            |nanos| spin(black_box(nanos)),
            |_position, _item, ()| {},
        );
    }))
}

/// The time of one `each` over [`ITEMS`] items whose jobs each spin for `job`
/// nanoseconds on `pool`, given for each item.
///
/// # Specification
/// trivial.
fn each(
    pool: &Pool,
    job: u64,
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
/// jobs each spin for `job` nanoseconds: one task for each thread of
/// `threads`, each taking the next item from one atomic counter, given for
/// each item.
///
/// # Specification
/// trivial.
fn cursor(
    threads: &rayon::ThreadPool,
    job: u64,
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
fn widths() -> Vec<NonZeroUsize>
{
    let named: Vec<NonZeroUsize> = std::env::args()
        .skip(1)
        .filter_map(|argument| argument.parse().ok())
        .collect();
    if !named.is_empty() {
        return named;
    }
    let host = std::thread::available_parallelism().unwrap_or(NonZeroUsize::MIN);
    if host == NonZeroUsize::MIN {
        vec![NonZeroUsize::MIN]
    }
    else {
        vec![NonZeroUsize::MIN, host]
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
        Output::Table => Count(20),
        Output::Silent => Count(1),
    };
    if matches!(output, Output::Table) {
        println!("Each figure is the time of one fork of {ITEMS} items, given for each item.");
        println!("The allocations are those of one fork.");
        println!();
        println!("| Fork | Job ns | Threads | p50 ns | p99 ns | Allocations |");
        println!("| ---- | ------ | ------- | ------ | ------ | ----------- |");
    }
    let print = |row: &str, job: u64, width: NonZeroUsize, figures: &Figures| {
        if matches!(output, Output::Table) {
            print_row(format_args!("{row} | {job} | {width}"), figures);
        }
    };
    for width in widths() {
        let pool = Pool::new(Width::Threads(Threads::from(width)));
        let threads = rayon::ThreadPoolBuilder::new()
            .num_threads(width.get())
            .build()
            .expect("the fallback's pool starts");
        for graph in Graph::ALL {
            let after = graph.dependences();
            for job in JOBS {
                print(
                    graph.row(),
                    job,
                    width,
                    &scheduled(&pool, &after, job, samples),
                );
            }
        }
        for job in JOBS {
            print("each", job, width, &each(&pool, job, samples));
            print(
                "each by an atomic cursor",
                job,
                width,
                &cursor(&threads, job, samples),
            );
        }
    }
}
