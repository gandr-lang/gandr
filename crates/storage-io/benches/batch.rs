//! The packed write of a whole batch at a width: each of `shards` segments
//! folds one batch in each round, and all the shards fold at one time.
//!
//! A batch is one buffer of its records, appended to its shard's segment
//! and synced. The blocking form is the store's segment as it lands: a
//! thread for each shard, which writes its batch by one positioned write,
//! then blocks in one `fdatasync`. The ring runs `workers` threads, each the
//! one submitter of its share of the shards. Each worker stages a write
//! linked to its sync for each of its shards, so one entry into the kernel
//! carries the whole round of its share, from buffers that its ring
//! registers once.
//!
//! A fold's time runs from the start of its round to the completion of its
//! shard's sync, under each form.
//!
//! # Examples
//!
//! `cargo bench -p gandr-storage-io --bench batch -- --bench --directory
//! <path> --shards 1,16,64 --workers 1,4 --rounds 100` prints one row for
//! the blocking form and one for each count of ring workers, at each count
//! of shards. `--records` and `--size` set a batch: 64 records of 4096
//! bytes by default. Under `cargo test`, the bench runs two rounds of each
//! form at two shards and prints nothing.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

extern crate alloc;

use alloc::alloc::Global;
use core::time::Duration;
use std::fs;
use std::fs::OpenOptions;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Barrier;
use std::time::Instant;

use gandr_storage_io::Buffer;
use gandr_storage_io::Chain;
use gandr_storage_io::Count;
use gandr_storage_io::Errno;
use gandr_storage_io::Fill;
use gandr_storage_io::Handle;
use gandr_storage_io::Io;
use gandr_storage_io::Moved;
use gandr_storage_io::Pinning;
use gandr_storage_io::Position;
use gandr_storage_io::Registered;
use gandr_storage_io::Segment;

/// A count of shards, workers, rounds, records or bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Number(u32);

/// What the command line asks of a run.
struct Arguments
{
    /// A full run, which prints its rows; otherwise one short pass.
    full: bool,
    /// The directory on the device that the run measures.
    directory: PathBuf,
    /// Each count of shards that fold at one time.
    shards: Vec<Number>,
    /// Each count of ring workers.
    workers: Vec<Number>,
    /// The rounds of folds at each count.
    rounds: Number,
    /// The records of each batch.
    records: Number,
    /// The bytes of each record.
    size: Number,
}

impl Arguments
{
    /// The bytes of one batch.
    ///
    /// # Specification
    /// trivial.
    fn batch(&self) -> Moved
    {
        Moved::from(
            self.records
                .0
                .checked_mul(self.size.0)
                .expect("a batch fits a u32"),
        )
    }
}

/// The arguments of the process: `--bench`, `--directory <path>`, `--shards
/// <n,…>`, `--workers <n,…>`, `--rounds <n>`, `--records <n>` and `--size
/// <bytes>`.
///
/// # Specification
/// trivial.
fn arguments() -> Arguments
{
    let mut parsed = Arguments {
        full: false,
        directory: std::env::temp_dir(),
        shards: vec![Number(2)],
        workers: vec![Number(1)],
        rounds: Number(2),
        records: Number(64),
        size: Number(4_096),
    };
    let mut words = std::env::args().skip(1);
    let counts = |word: Option<String>| -> Vec<Number> {
        word.expect("a list of counts follows its flag")
            .split(',')
            .map(|count| {
                Number(
                    count
                        .parse()
                        .ok()
                        .filter(|&count| count > 0)
                        .expect("each count is a number above zero"),
                )
            })
            .collect()
    };
    let count = |word: Option<String>| -> Number {
        counts(word)
            .first()
            .copied()
            .expect("a count follows its flag")
    };
    while let Some(word) = words.next() {
        match word.as_str() {
            "--bench" => parsed.full = true,
            "--directory" => {
                parsed.directory = words
                    .next()
                    .map(PathBuf::from)
                    .expect("--directory names a path");
            },
            "--shards" => parsed.shards = counts(words.next()),
            "--workers" => parsed.workers = counts(words.next()),
            "--rounds" => parsed.rounds = count(words.next()),
            "--records" => parsed.records = count(words.next()),
            "--size" => parsed.size = count(words.next()),
            _ => {},
        }
    }
    parsed
}

/// A fresh segment for shard `shard` under `directory`.
///
/// # Specification
/// trivial.
fn segment(
    directory: &Path,
    shard: Number,
) -> (PathBuf, Segment)
{
    let path = directory.join(format!(
        "gandr-storage-io-batch-{}-{}",
        std::process::id(),
        shard.0
    ));
    let file = OpenOptions::new()
        .create(true)
        .truncate(true)
        .read(true)
        .write(true)
        .open(&path)
        .expect("the bench file opens");
    (
        path,
        Segment::new(Handle::from(file), Position::from(0_u64)),
    )
}

/// The folds of one thread: `io` folds a batch into each of `shards` in each
/// round, all linked writes and syncs staged at once, and waits for the
/// round. Each fold's time is pushed into `folds`. The thread's buffers
/// register within the limit of locked memory, and the rest run
/// unregistered; the answer says how many the ring fixes.
///
/// # Specification
/// trivial.
fn folds(
    mut io: Io<Global>,
    shards: &[Number],
    asked: &Arguments,
    barrier: &Barrier,
    folds: &mut Vec<(Number, Duration)>,
) -> Pinning
{
    let width = Count::from(u32::try_from(shards.len()).expect("the shards fit a u32"));
    let Registered {
        mut buffers,
        pinning,
    } = io
        .register(width, asked.batch(), Global)
        .expect("the global allocator holds the batches");
    for buffer in &mut buffers {
        buffer.fill(Fill(0xa5_u8));
    }
    let (paths, mut segments): (Vec<PathBuf>, Vec<Segment>) = shards
        .iter()
        .map(|&shard| segment(&asked.directory, shard))
        .unzip();
    let mut back: Vec<Buffer<Global>> = Vec::with_capacity(shards.len());
    for round in 0 .. asked.rounds.0 {
        barrier.wait();
        let started = Instant::now();
        for shard in &mut segments {
            let buffer = buffers.pop().expect("each shard's buffer is back");
            let _append = io
                .append(shard, buffer, Chain::Linked)
                .expect("the append stages");
            let _sync = io.sync(shard, Chain::Alone).expect("the sync stages");
        }
        while let Some(done) = io.wait().expect("the wait answers") {
            let _moved = done.outcome.expect("the write and its sync succeed");
            // A write gives its buffer back, and a sync holds none.
            match done.buffer {
                Some(buffer) => back.push(buffer),
                None => folds.push((Number(round), started.elapsed())),
            }
        }
        buffers.append(&mut back);
    }
    drop(io);
    for path in paths {
        fs::remove_file(path).expect("the bench file is removed");
    }
    pinning
}

/// The form a thread of a row opens on its own thread: an `Io` stays on the
/// thread that opens it.
#[derive(Clone, Copy)]
enum Kind
{
    /// The ring.
    Ring,
    /// The blocking form.
    Blocking,
}

/// One row's figures: each fold's time in increasing order, the first and
/// the last fold of each round in increasing order, the wall time of the
/// row, the buffers that its rings fix, and the error number of a
/// registration that the kernel refused.
struct Row
{
    /// Each fold's time, in increasing order.
    times: Vec<Duration>,
    /// The time of each round's first fold, in increasing order.
    firsts: Vec<Duration>,
    /// The time of each round's last fold, in increasing order.
    lasts: Vec<Duration>,
    /// The wall time of the whole row.
    wall: Duration,
    /// The buffers that the row's rings fix.
    fixed: Number,
    /// The error number of a refused registration, if one was refused.
    refused: Option<Errno>,
}

/// The figures of one row: each element of `plan` is one thread, the form
/// it opens and the shards it folds.
///
/// # Specification
/// trivial.
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "benchmark: the measure is a blocked thread for each fold against a ring for each worker, so it starts the threads it counts"
    )
)]
fn row(
    plan: Vec<(Kind, Vec<Number>)>,
    asked: &Arguments,
) -> Row
{
    let barrier = Barrier::new(plan.len());
    let started = Instant::now();
    let rounds = usize::try_from(asked.rounds.0).unwrap_or(usize::MAX);
    let mut row = Row {
        times: Vec::new(),
        firsts: vec![Duration::MAX; rounds],
        lasts: vec![Duration::ZERO; rounds],
        wall: Duration::ZERO,
        fixed: Number(0),
        refused: None,
    };
    std::thread::scope(|scope| {
        let threads: Vec<_> = plan
            .into_iter()
            .map(|(kind, shards)| {
                let barrier = &barrier;
                scope.spawn(move || {
                    let width = usize::try_from(asked.rounds.0)
                        .unwrap_or(usize::MAX)
                        .saturating_mul(shards.len());
                    let depth = Count::from(
                        u32::try_from(shards.len())
                            .expect("the shards fit a u32")
                            .saturating_mul(2),
                    );
                    let io = match kind {
                        Kind::Ring => Io::open(depth).expect("an io opens"),
                        Kind::Blocking => Io::blocking(depth).expect("the blocking form opens"),
                    };
                    let mut times = Vec::with_capacity(width);
                    let pinning = folds(io, &shards, asked, barrier, &mut times);
                    (
                        times,
                        pinning,
                        Number(u32::try_from(shards.len()).unwrap_or(u32::MAX)),
                    )
                })
            })
            .collect();
        for thread in threads {
            let (times, pinning, shards) = thread.join().expect("a thread of the row ends");
            for (round, time) in times {
                let at = usize::try_from(round.0).unwrap_or(usize::MAX);
                if let Some(first) = row.firsts.get_mut(at) {
                    *first = (*first).min(time);
                }
                if let Some(last) = row.lasts.get_mut(at) {
                    *last = (*last).max(time);
                }
                row.times.push(time);
            }
            let fixed = match pinning {
                Pinning::Whole => shards.0,
                Pinning::Within(count) => u32::from(count),
                Pinning::Refused(errno) => {
                    row.refused = Some(errno);
                    0
                },
                Pinning::Blocking => 0,
            };
            row.fixed = Number(row.fixed.0.saturating_add(fixed));
        }
    });
    row.wall = started.elapsed();
    row.times.sort_unstable();
    row.firsts.sort_unstable();
    row.lasts.sort_unstable();
    row
}

/// A share of the folds, in hundredths.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Percent(usize);

/// The fold time below which `percent` of `times` end.
///
/// # Specification
/// trivial.
fn percentile(
    times: &[Duration],
    percent: Percent,
) -> Duration
{
    let at = times
        .len()
        .saturating_mul(percent.0)
        .checked_div(100)
        .unwrap_or_default();
    times
        .get(at)
        .or_else(|| times.last())
        .copied()
        .unwrap_or_default()
}

/// The shards of `worker` among `workers`: every `workers`-th shard from
/// the worker's own.
///
/// # Specification
/// trivial.
fn share(
    shards: Number,
    workers: Number,
    worker: Number,
) -> Vec<Number>
{
    (worker.0 .. shards.0)
        .step_by(usize::try_from(workers.0).unwrap_or(usize::MAX))
        .map(Number)
        .collect()
}

/// Run each row and print it.
///
/// # Specification
/// trivial.
fn main()
{
    let asked = arguments();
    if asked.full {
        println!(
            "batches of {} records of {} bytes under {}, {} rounds; a fold is a write and its sync",
            asked.records.0,
            asked.size.0,
            asked.directory.display(),
            asked.rounds.0
        );
        println!(
            "the rings fix the buffers that the process's limit of locked memory holds; the rest run unregistered"
        );
        println!(
            "| shards | form | threads | fixed buffers | fold p50 (µs) | fold p99 (µs) | first fold p50 (µs) | last fold p50 (µs) | wall (s) | MiB per second |"
        );
        println!("| ---: | --- | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |");
    }
    for &shards in &asked.shards {
        let blocking: Vec<(Kind, Vec<Number>)> = (0 .. shards.0)
            .map(|shard| (Kind::Blocking, vec![Number(shard)]))
            .collect();
        let mut rows = vec![("blocking", shards, row(blocking, &asked))];
        for &workers in asked.workers.iter().filter(|workers| workers.0 <= shards.0) {
            let ring: Vec<(Kind, Vec<Number>)> = (0 .. workers.0)
                .map(|worker| (Kind::Ring, share(shards, workers, Number(worker))))
                .collect();
            rows.push(("ring", workers, row(ring, &asked)));
        }
        if asked.full {
            let bytes = u128::from(u32::from(asked.batch()))
                .saturating_mul(u128::from(shards.0))
                .saturating_mul(u128::from(asked.rounds.0));
            for (form, threads, figures) in rows {
                let rate = bytes
                    .saturating_mul(1_000_000)
                    .checked_div(figures.wall.as_micros().max(1))
                    .unwrap_or_default()
                    .checked_shr(20_u32)
                    .unwrap_or_default();
                let fixed = match (form, figures.refused) {
                    ("blocking", _) => String::from("none: the blocking form"),
                    (_, Some(errno)) => format!(
                        "{} of {}, refused with errno {}",
                        figures.fixed.0,
                        shards.0,
                        u16::from(errno)
                    ),
                    (_, None) => format!("{} of {}", figures.fixed.0, shards.0),
                };
                println!(
                    "| {} | {form} | {} | {fixed} | {} | {} | {} | {} | {:.2} | {rate} |",
                    shards.0,
                    threads.0,
                    percentile(&figures.times, Percent(50)).as_micros(),
                    percentile(&figures.times, Percent(99)).as_micros(),
                    percentile(&figures.firsts, Percent(50)).as_micros(),
                    percentile(&figures.lasts, Percent(50)).as_micros(),
                    figures.wall.as_secs_f64(),
                );
            }
        }
    }
}
