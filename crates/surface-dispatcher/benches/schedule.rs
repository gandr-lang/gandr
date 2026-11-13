//! The measurement of the pool's dependence schedule: one schedule of 4,096
//! items on the driver's pool, called from a thread outside the pool, at each
//! width that the run names.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `<graph>, <job> ns, <threads> threads` | one schedule of 4,096 items, given for each item: each release and each commit on the calling thread, and each job on a worker or on the calling thread |
//!
//! Each job spins for its time and returns nothing. The graphs:
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

/// The items of one schedule.
const ITEMS: usize = 4_096;

/// The distance of each edge of the `stride 64` graph.
const STRIDE: usize = 64;

/// The time each job spins for, in nanoseconds.
const JOBS: [u64; 3] = [0, 1_000, 10_000];

/// The edges of one graph of the measurement.
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

    /// The name of the graph in the table.
    ///
    /// # Specification
    /// trivial.
    const fn name(self) -> &'static str
    {
        match self {
            Self::None => "none",
            Self::Stride => "stride 64",
            Self::Chain => "chain",
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
    let whole = measure(Count(1), samples, || {
        pool.schedule(
            black_box(items.as_mut_slice()),
            after,
            |_position, _item| Releasing::<u64, ()>::Run(job),
            |nanos| spin(black_box(nanos)),
            |_position, _item, ()| {},
        );
    });
    let items = u128::try_from(ITEMS).expect("the count of items fits");
    Figures {
        median: whole.median.checked_div(items).expect("a nonzero count"),
        tail: whole.tail.checked_div(items).expect("a nonzero count"),
        allocations: whole.allocations,
    }
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
        println!("Each figure is the time of one schedule of {ITEMS} items, given for each item.");
        println!("The allocations are those of one schedule.");
        println!();
        println!("| Graph | Job ns | Threads | p50 ns | p99 ns | Allocations |");
        println!("| ----- | ------ | ------- | ------ | ------ | ----------- |");
    }
    for width in widths() {
        let pool = Pool::new(Width::Threads(Threads::from(width)));
        for graph in Graph::ALL {
            let after = graph.dependences();
            for job in JOBS {
                let figures = scheduled(&pool, &after, job, samples);
                if matches!(output, Output::Table) {
                    print_row(format_args!("{} | {job} | {width}", graph.name()), &figures);
                }
            }
        }
    }
}
