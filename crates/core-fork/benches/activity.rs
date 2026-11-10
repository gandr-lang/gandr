//! The measurement of the activity ring: the write of one mark, alone and
//! beside other producers, and the fold of one tick.
//!
//! | Row | What it times |
//! | --- | ------------- |
//! | `record, room` | the write of one mark into a ring with room |
//! | `record, full` | the write of one mark into a full ring, which drops its oldest mark |
//! | `record, 8 producers` | the write of one mark while eight threads each write their own ring; each sample is one thread's mean |
//! | `record and one shared increment, 8 producers` | as above, with one increment of a counter that the eight threads share: the write of a ring whose producers number the events |
//! | `tick, 8 × 4096, per event` | the fold of eight full rings, 32768 marks: the drain, the merge by the clock, the numbering and the rows |
//!
//! `cargo bench` runs the full measurement and prints one table. Under any
//! other runner the binary runs one short pass of every row and prints
//! nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

#[path = "../../theory-exact-reals/benches/support.rs"]
mod support;

use core::hint::black_box;
use core::num::NonZeroU16;
use core::num::NonZeroUsize;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::Ordering;
use std::time::Instant;

use gandr_core_fork::activity::Activity;
use gandr_core_fork::activity::Core;
use gandr_core_fork::activity::Cores;
use gandr_core_fork::activity::Declaration;
use gandr_core_fork::activity::Edge;
use gandr_core_fork::activity::Event;
use gandr_core_fork::activity::Fold;
use gandr_core_fork::activity::Mark;
use gandr_core_fork::activity::Nanos;
use gandr_core_fork::activity::Slots;
use gandr_core_fork::activity::Task;
use gandr_core_fork::activity::World;

use crate::support::Count;
use crate::support::Figures;
use crate::support::Output;
use crate::support::measure;
use crate::support::print_row;

/// The producers of the contended rows and the cores of the fold's row.
const PRODUCERS: u16 = 8;

/// The slots of each ring in the contended rows and in the fold's row.
const SLOTS: usize = 4_096;

/// The mark of a fork job's start on declaration zero at `clock`.
///
/// # Specification
/// trivial.
fn mark(clock: Nanos) -> Mark
{
    Mark {
        task: Task::Fork,
        edge: Edge::Start,
        declaration: Declaration::from(0),
        world: World::from(0),
        clock,
    }
}

/// The cores of the contended rows and of the fold's row.
///
/// # Specification
/// trivial.
fn producers() -> Cores
{
    Cores::from(NonZeroU16::new(PRODUCERS).expect("eight producers"))
}

/// The slots of each ring of the contended rows and of the fold's row.
///
/// # Specification
/// trivial.
fn slots() -> Slots
{
    Slots::from(NonZeroUsize::new(SLOTS).expect("a ring of slots"))
}

/// Samples in nanoseconds, in no order.
#[repr(transparent)]
struct Samples(Vec<u128>);

/// The median and the 99th percentile of `samples`, with no allocation.
///
/// # Specification
/// trivial.
fn figures(samples: Samples) -> Figures
{
    let Samples(mut samples) = samples;
    samples.sort_unstable();
    let percentile = |hundredths: usize| {
        let index = samples
            .len()
            .saturating_sub(1)
            .saturating_mul(hundredths)
            .checked_div(100)
            .expect("a nonzero divisor");
        samples.get(index).copied().unwrap_or_default()
    };
    Figures {
        median: percentile(50),
        tail: percentile(99),
        allocations: 0,
    }
}

/// Whether the producers of a contended row also share a counter.
#[derive(Clone, Copy)]
enum Counter
{
    /// Each write is one push: the hub numbers the events.
    None,
    /// Each write is one push and one increment of a shared counter: the
    /// producers number the events.
    Shared,
}

/// The mean time of one write on each of eight threads, each writing its own
/// ring `writes` times at once.
///
/// # Specification
/// trivial.
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "benchmark: the row measures eight producers at once, so it starts the threads it compares"
    )
)]
fn contended(
    writes: Count,
    counter: Counter,
) -> Figures
{
    let activity = Activity::new(producers(), slots());
    let shared = AtomicU64::new(0);
    let means = std::thread::scope(|scope| {
        let running: Vec<_> = (0 .. PRODUCERS)
            .map(|index| {
                let producer = activity.producer(Core::from(index)).expect("a free ring");
                let shared = &shared;
                scope.spawn(move || {
                    let start = Instant::now();
                    for write in 0 .. writes.0 {
                        let clock = Nanos::from(u64::try_from(write).expect("a small count"));
                        if matches!(counter, Counter::Shared) {
                            black_box(shared.fetch_add(1, Ordering::Relaxed));
                        }
                        producer.record(black_box(mark(clock)));
                    }
                    start
                        .elapsed()
                        .as_nanos()
                        .checked_div(u128::try_from(writes.0).expect("a count fits"))
                        .expect("a nonempty count")
                })
            })
            .collect();
        running
            .into_iter()
            .map(|thread| thread.join().expect("a producer ends"))
            .collect::<Vec<_>>()
    });
    figures(Samples(means))
}

/// The time of one tick over eight full rings, for each event, in `samples`
/// samples.
///
/// # Specification
/// trivial.
fn ticks(samples: Count) -> Figures
{
    let activity = Activity::new(producers(), slots());
    let mut fold = Fold::new(&activity);
    let events = u128::from(PRODUCERS).saturating_mul(u128::try_from(SLOTS).expect("a count fits"));
    let mut times = Vec::with_capacity(samples.0);
    for sample in 0 .. samples.0 {
        for index in 0 .. PRODUCERS {
            let producer = activity.producer(Core::from(index)).expect("a free ring");
            for slot in 0 .. SLOTS {
                let clock = sample.saturating_mul(SLOTS).saturating_add(slot);
                producer.record(mark(Nanos::from(
                    u64::try_from(clock).expect("a small clock"),
                )));
            }
        }
        let now = Nanos::from(
            u64::try_from(sample.saturating_add(1).saturating_mul(SLOTS)).expect("a small clock"),
        );
        let start = Instant::now();
        black_box(fold.tick(&activity, now).events.len());
        times.push(
            start
                .elapsed()
                .as_nanos()
                .checked_div(events)
                .expect("a nonempty tick"),
        );
    }
    figures(Samples(times))
}

/// Run the measurement, or the short pass outside `cargo bench`.
///
/// # Specification
/// trivial.
fn main()
{
    let output = Output::of_run();
    let (batch, samples, writes) = match output {
        Output::Table => (Count(1_000), Count(200), Count(1_000_000)),
        Output::Silent => (Count(1), Count(1), Count(1)),
    };
    let room = Activity::new(
        Cores::from(NonZeroU16::MIN),
        Slots::from(
            NonZeroUsize::new(
                batch
                    .0
                    .saturating_mul(samples.0)
                    .saturating_mul(2)
                    .saturating_add(batch.0),
            )
            .expect("a ring of slots"),
        ),
    );
    let room_producer = room.producer(Core::from(0)).expect("a free ring");
    let recorded_with_room = measure(batch, samples, || {
        room_producer.record(black_box(mark(Nanos::from(0))));
    });
    let full = Activity::new(
        Cores::from(NonZeroU16::MIN),
        Slots::from(NonZeroUsize::new(64).expect("a ring of slots")),
    );
    let full_producer = full.producer(Core::from(0)).expect("a free ring");
    for _ in 0_u32 .. 64 {
        full_producer.record(mark(Nanos::from(0)));
    }
    let recorded_full = measure(batch, samples, || {
        full_producer.record(black_box(mark(Nanos::from(0))));
    });
    let recorded_beside = contended(writes, Counter::None);
    let recorded_counted = contended(writes, Counter::Shared);
    let ticked = ticks(Count(samples.0.min(50)));
    if matches!(output, Output::Table) {
        println!(
            "A mark is {} bytes, and an event {} bytes.",
            size_of::<Mark>(),
            size_of::<Event>()
        );
        println!();
        println!("| Row | p50 ns | p99 ns | Allocations |");
        println!("| --- | ------ | ------ | ----------- |");
        for (row, figures) in [
            ("record, room", &recorded_with_room),
            ("record, full", &recorded_full),
            ("record, 8 producers", &recorded_beside),
            (
                "record and one shared increment, 8 producers",
                &recorded_counted,
            ),
            ("tick, 8 × 4096, per event", &ticked),
        ] {
            print_row(format_args!("{row}"), figures);
        }
    }
}
