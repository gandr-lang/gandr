//! The store's load: many files read into one store at once, the rate and the
//! latency of its puts, the naming that makes them durable, and the wall of
//! the scan that opens the store after.
//!
//! The bench first makes a source tree of 20,000 files of 4 KiB. The BLAKE3
//! output of the index of a file fills it, so no two files share a piece. A
//! file of 4 KiB is no longer than the least cut of the byte profile, so it
//! reads as one piece. For each width, a fresh store opens, and that many
//! threads load the tree into it with `Store::read_in`. Each thread loads
//! every width-th file and times each call.
//!
//! # Examples
//!
//! `cargo bench -p gandr-storage-store --bench load` measures the widths 1, 16
//! and 64 under the temporary directory of the host, and prints one row for
//! each width. `-- --directory <path>` puts the source tree and the stores
//! under that directory. `-- --widths 1,8,96` measures the widths that it
//! names, and `-- --files <n>` loads that many files. Under `cargo test`, the
//! bench loads 64 files at widths 1 and 2 and prints nothing, so the gates run
//! it and do not time it.
//!
//! # Items
//!
//! The put rate is the count of records in the two planes after the load,
//! over the wall time of the load. The latency is the 50th and the 99th
//! percentile of the calls. A call makes one batch on each plane and syncs
//! nothing, since no root names what it put. After the load, one naming
//! commits an output and names it, and the bench times it. That naming syncs
//! every segment the load wrote to, so its wall is the durable cost the whole
//! load shares.
//!
//! After the load the bench opens the store again and times the open. The
//! open scans each segment's headers into the index, so its wall grows with
//! the records the store holds. Once the root carries the index, the open
//! reads the root and no segment.
//!
//! # Boundaries
//!
//! The full run omits a width above the parallelism of the host, and
//! `--widths` does not. Each row names the filesystem and the device that
//! hold the directory: on Linux, from the mount table of the process; on
//! macOS, from `statfs` and the node of the device under `/dev`. A row on
//! tmpfs states that it measures the locks of the kernel and no device. The
//! bench refuses a run whose directory names no filesystem or no device.
//! Beside each row stand the user CPU, the system CPU and the voluntary
//! context switches of the process during the load.
//!
//! # References
//!
//! - `vault:01a1cf3f-b730-7152-9d64-050e5c00b32a` — anchor: the store's single
//!   writer plan (§ The topology of one host) — the producers append to their
//!   own shards, and no single writer folds them.
//! - `vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583` — anchor: the performance
//!   programme (§ performance-figures) — a row names what it measures: the
//!   filesystem, the device, the CPU and the voluntary switches.
//! - `vault:01a1d90b-b64a-7248-8f6e-e792b6e8cb9f` — anchor: the IO layer's
//!   probe (§ the grid) — the rows of a segment that this bench measures the
//!   store against.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

use core::time::Duration;
use std::fs;
#[cfg(target_os = "macos")]
use std::os::unix::fs::FileTypeExt as _;
#[cfg(target_os = "macos")]
use std::os::unix::fs::MetadataExt as _;
use std::path::Path;
use std::path::PathBuf;
use std::time::Instant;

use gandr_storage_store::Output;
use gandr_storage_store::RootName;
use gandr_storage_store::Store;
use nix::sys::resource::UsageWho;
use nix::sys::resource::getrusage;
use nix::sys::time::TimeVal;

/// How many files a full run loads unless `--files` says otherwise.
const FULL: Count = Count(20_000);

/// How many files a test-mode pass loads.
const SMOKE: Count = Count(64);

/// The bytes of each file: no more than the least cut of the byte profile, so
/// each file is one piece.
const FILE_BYTES: usize = 4_096;

/// The widths a full run measures, when no `--widths` names others.
const FULL_WIDTHS: [Count; 3] = [Count(1), Count(16), Count(64)];

/// The widths a test-mode pass loads at.
const SMOKE_WIDTHS: [Count; 2] = [Count(1), Count(2)];

/// The directories of the two planes under the root of a store.
const PLANES: [&str; 2] = ["chunks", "nodes"];

/// The magic each segment record's header opens with.
const MAGIC: &[u8; 4] = b"gsg1";

/// The bytes of a segment record's header after its magic and its length.
const HEADER_REST: usize = 56;

/// A count of files, threads or records.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Count(usize);

/// A count of records over each second of a wall time.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Rate(u128);

/// The CPU and the voluntary context switches of the process, up to a moment
/// or over a pass.
#[derive(Clone, Copy)]
struct Spent
{
    /// The CPU time in user mode.
    user: Duration,
    /// The CPU time in the kernel.
    system: Duration,
    /// The context switches that the threads of the process gave up.
    switches: nix::libc::c_long,
}

impl Spent
{
    /// What the process spent from its start to now.
    ///
    /// # Specification
    /// trivial.
    fn now() -> Self
    {
        let usage = getrusage(UsageWho::RUSAGE_SELF).expect("the process reads its usage");
        Self {
            user: duration(usage.user_time()),
            system: duration(usage.system_time()),
            switches: usage.voluntary_context_switches(),
        }
    }

    /// What the process spent from `before` to `self`.
    ///
    /// # Specification
    /// trivial.
    fn since(
        self,
        before: Self,
    ) -> Self
    {
        Self {
            user: self.user.saturating_sub(before.user),
            system: self.system.saturating_sub(before.system),
            switches: self.switches.saturating_sub(before.switches),
        }
    }
}

/// The duration that `time` holds.
///
/// # Specification
/// trivial.
fn duration(time: TimeVal) -> Duration
{
    let seconds = u64::try_from(time.tv_sec()).unwrap_or_default();
    let micros = u64::try_from(time.tv_usec()).unwrap_or_default();
    Duration::from_secs(seconds).saturating_add(Duration::from_micros(micros))
}

/// The records that one load puts, its wall time, each call's latency, its
/// naming, and what the process spent during it.
struct Pass
{
    /// The records that the planes gain.
    records: Count,
    /// The wall time of the load.
    wall: Duration,
    /// The latency of each call, in increasing order.
    calls: Vec<Duration>,
    /// The wall of one naming after the load, which syncs what it wrote.
    naming: Duration,
    /// The CPU and the voluntary switches of the process during the load.
    spent: Spent,
}

impl Pass
{
    /// The records of the pass over each second of its wall time.
    ///
    /// # Specification
    /// trivial.
    fn rate(&self) -> Rate
    {
        let records = u128::try_from(self.records.0).expect("a count fits in 128 bits");
        Rate(
            records
                .saturating_mul(1_000_000)
                .checked_div(self.wall.as_micros().max(1))
                .unwrap_or_default(),
        )
    }

    /// The latency below which `percent` of the calls end.
    ///
    /// # Specification
    /// trivial.
    fn percentile(
        &self,
        percent: Count,
    ) -> Duration
    {
        let at = self
            .calls
            .len()
            .saturating_mul(percent.0)
            .checked_div(100)
            .unwrap_or_default();
        self.calls
            .get(at)
            .or_else(|| self.calls.last())
            .copied()
            .unwrap_or_default()
    }
}

/// A fresh, empty directory for the run under `base`, removed first if a run
/// left it.
///
/// # Specification
/// trivial.
fn scratch(base: &Path) -> PathBuf
{
    let directory = base.join(format!("gandr-storage-load-{}", std::process::id()));
    if directory.exists() {
        fs::remove_dir_all(&directory).expect("a stale scratch directory is removed");
    }
    fs::create_dir_all(&directory).expect("the scratch directory is made");
    directory
}

/// A source tree of `files` files under `root`, each filled by the BLAKE3
/// output of its index.
///
/// # Specification
/// trivial.
fn source(
    root: &Path,
    files: Count,
) -> Vec<PathBuf>
{
    let directory = root.join("source");
    fs::create_dir_all(&directory).expect("the source directory is made");
    let mut bytes = vec![0_u8; FILE_BYTES];
    (0 .. files.0)
        .map(|index| {
            let seed = u64::try_from(index).expect("an index fits in 64 bits");
            blake3::Hasher::new()
                .update(&seed.to_le_bytes())
                .finalize_xof()
                .fill(&mut bytes);
            let path = directory.join(format!("{index:05}"));
            fs::write(&path, &bytes).expect("a source file is written");
            path
        })
        .collect()
}

/// The records the segments of the two planes of `store` hold, counted by
/// their headers up to each segment's first bytes that open none.
///
/// # Specification
/// trivial.
fn records(store: &Path) -> Count
{
    let mut count = 0_usize;
    for plane in PLANES {
        for entry in fs::read_dir(store.join(plane)).expect("a plane lists") {
            let bytes =
                fs::read(entry.expect("a plane entry reads").path()).expect("a segment reads");
            let mut rest = bytes.as_slice();
            while let Some((magic, after)) = rest.split_first_chunk::<4>()
                && magic == MAGIC
                && let Some((length, after)) = after.split_first_chunk::<4>()
                && let Ok(length) = usize::try_from(u32::from_le_bytes(*length))
                && let Some(next) = after.get(HEADER_REST.saturating_add(length) ..)
            {
                count = count.saturating_add(1);
                rest = next;
            }
        }
    }
    Count(count)
}

/// Read every file of `files` into a fresh store at `store`, `width` threads
/// at once, each call timed.
///
/// # Specification
/// trivial.
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "benchmark: each row measures the store at a fixed count of producers, so it starts the threads it counts"
    )
)]
fn load(
    store: &Path,
    files: &[PathBuf],
    width: Count,
) -> Pass
{
    let (opened, mut register) = Store::open(store).expect("a fresh store opens");
    let before = Spent::now();
    let started = Instant::now();
    let mut calls: Vec<Duration> = std::thread::scope(|scope| {
        // Every loader starts before the first join, so they run at once.
        let mut threads = Vec::with_capacity(width.0);
        for first in 0 .. width.0 {
            let opened = &opened;
            threads.push(scope.spawn(move || {
                files
                    .iter()
                    .skip(first)
                    .step_by(width.0)
                    .map(|path| {
                        let call = Instant::now();
                        opened.read_in(path).expect("a source file reads in");
                        call.elapsed()
                    })
                    .collect::<Vec<Duration>>()
            }));
        }
        threads
            .into_iter()
            .flat_map(|thread| thread.join().expect("a loader runs to its end"))
            .collect()
    });
    let wall = started.elapsed();
    let spent = Spent::now().since(before);
    calls.sort_unstable();
    // One naming after the load syncs every segment the load wrote to.
    let first = files.first().expect("a load reads a file");
    let entry = opened.read_in(first).expect("a loaded file reads in again");
    let named = Instant::now();
    let pointer = opened
        .commit(&Output::new(entry, Vec::new()))
        .expect("an output commits");
    register
        .name(RootName::new(String::from("bench/load")), pointer)
        .expect("the output is named");
    let naming = named.elapsed();
    Pass {
        records: records(store),
        wall,
        calls,
        naming,
        spent,
    }
}

/// The wall of the open of the store at `store`, which scans its segments.
///
/// # Specification
/// trivial.
fn reopened(store: &Path) -> Duration
{
    let started = Instant::now();
    let opened = Store::open(store).expect("the loaded store opens again");
    let wall = started.elapsed();
    drop(opened);
    wall
}

/// The filesystem and the device that hold a directory.
struct Substrate
{
    /// The type of the filesystem, as the kernel names it.
    filesystem: String,
    /// The device that holds the filesystem, or what the mount names in its
    /// place.
    device: String,
}

impl Substrate
{
    /// The filesystem and the device of `directory`: the mount of the process
    /// whose mount point is the longest prefix of the canonical directory.
    ///
    /// # Specification
    /// trivial.
    #[cfg(target_os = "linux")]
    fn of(directory: &Path) -> Self
    {
        let directory = directory.canonicalize().expect("the directory resolves");
        let table = fs::read_to_string("/proc/self/mountinfo").expect("the mount table reads");
        let mut found = None;
        let mut longest = 0_usize;
        for line in table.lines() {
            let Some((left, right)) = line.split_once(" - ")
            else {
                continue;
            };
            let (Some(point), mut kinds) = (left.split(' ').nth(4), right.split(' '))
            else {
                continue;
            };
            // The mount table writes a space, a tab, a newline and a backslash
            // in a mount point as three octal digits.
            let point = PathBuf::from(
                point
                    .replace("\\040", " ")
                    .replace("\\011", "\t")
                    .replace("\\012", "\n")
                    .replace("\\134", "\\"),
            );
            let depth = point.components().count();
            if directory.starts_with(&point) && depth >= longest {
                longest = depth;
                found = kinds
                    .next()
                    .zip(kinds.next())
                    .map(|(filesystem, device)| Self {
                        filesystem: String::from(filesystem),
                        device: String::from(device),
                    });
            }
        }
        found.unwrap_or(Self {
            filesystem: String::new(),
            device: String::new(),
        })
    }

    /// The filesystem and the device of `directory`: the type name that
    /// `statfs` gives, and the node under `/dev` whose device number is the
    /// directory's.
    ///
    /// # Specification
    /// trivial.
    #[cfg(target_os = "macos")]
    fn of(directory: &Path) -> Self
    {
        let filesystem = nix::sys::statfs::statfs(directory)
            .map_or_default(|stat| String::from(stat.filesystem_type_name()));
        let held = fs::metadata(directory).expect("the directory reads").dev();
        let device = fs::read_dir("/dev")
            .expect("the devices list")
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .find(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with("disk"))
                    && fs::metadata(path)
                        .is_ok_and(|node| node.file_type().is_block_device() && node.rdev() == held)
            })
            .map_or_default(|path| path.display().to_string());
        Self { filesystem, device }
    }

    /// No filesystem and no device: the bench names them on Linux and on
    /// macOS alone, and refuses the run elsewhere.
    ///
    /// # Specification
    /// trivial.
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    fn of(_directory: &Path) -> Self
    {
        Self {
            filesystem: String::new(),
            device: String::new(),
        }
    }

    /// The device as a row names it: on tmpfs, the locks of the kernel, since
    /// no device holds the filesystem.
    ///
    /// # Specification
    /// trivial.
    fn named(&self) -> String
    {
        if self.filesystem == "tmpfs" {
            String::from("none — the locks of the kernel")
        }
        else {
            self.device.clone()
        }
    }
}

/// Print one row: `width`, the records and the wall of `pass`, its put rate,
/// its latencies, its naming, the wall of the `open` after it, what the
/// process spent during the load, and the filesystem and the device of
/// `substrate`.
///
/// # Specification
/// trivial.
fn row(
    width: Count,
    pass: &Pass,
    open: Duration,
    substrate: &Substrate,
)
{
    println!(
        "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
        width.0,
        pass.records.0,
        pass.wall.as_millis(),
        pass.rate().0,
        pass.percentile(Count(50)).as_micros(),
        pass.percentile(Count(99)).as_micros(),
        pass.naming.as_micros(),
        open.as_millis(),
        pass.spent.user.as_millis(),
        pass.spent.system.as_millis(),
        pass.spent.switches,
        substrate.filesystem,
        substrate.named()
    );
}

/// What the command line asks of a run.
struct Arguments
{
    /// A full run, which times and prints; otherwise one short pass.
    full: bool,
    /// How many files a full run loads.
    files: Count,
    /// The directory that holds the run, or the temporary one.
    directory: PathBuf,
    /// The widths that `--widths` names, if it names any.
    widths: Option<Vec<Count>>,
}

/// The arguments of the process: `--bench`, `--files <n>`, `--directory
/// <path>` and `--widths <list>`, each width of the list a count above zero.
///
/// # Specification
/// trivial.
fn arguments() -> Arguments
{
    let mut parsed = Arguments {
        full: false,
        files: FULL,
        directory: std::env::temp_dir(),
        widths: None,
    };
    let mut words = std::env::args().skip(1);
    while let Some(word) = words.next() {
        match word.as_str() {
            "--bench" => parsed.full = true,
            "--files" => {
                parsed.files = Count(
                    words
                        .next()
                        .and_then(|count| count.parse().ok())
                        .expect("--files names a count"),
                );
            },
            "--directory" => {
                parsed.directory = words
                    .next()
                    .map(PathBuf::from)
                    .expect("--directory names a path");
            },
            "--widths" => {
                let list = words.next().expect("--widths names a list");
                parsed.widths = Some(
                    list.split(',')
                        .map(|width| {
                            Count(
                                width
                                    .trim()
                                    .parse::<usize>()
                                    .ok()
                                    .filter(|&width| width > 0)
                                    .expect("each width is a count above zero"),
                            )
                        })
                        .collect(),
                );
            },
            _ => {},
        }
    }
    parsed
}

/// Load the source tree at each width and print a row for each, after a line
/// that names the substrate.
///
/// # Specification
/// trivial.
fn main()
{
    let asked = arguments();
    let full = asked.full;
    let parallelism = std::thread::available_parallelism().map_or(1, usize::from);
    let (files, widths): (Count, Vec<Count>) = match (full, asked.widths) {
        (true, Some(named)) => (asked.files, named),
        (true, None) => (
            asked.files,
            FULL_WIDTHS
                .into_iter()
                .filter(|width| width.0 <= parallelism)
                .collect(),
        ),
        (false, _) => (
            SMOKE,
            SMOKE_WIDTHS
                .into_iter()
                .filter(|width| width.0 <= parallelism)
                .collect(),
        ),
    };
    let substrate = Substrate::of(&asked.directory);
    assert!(
        !substrate.filesystem.is_empty() && !substrate.device.is_empty(),
        "each row names the filesystem and the device of {}",
        asked.directory.display()
    );
    let root = scratch(&asked.directory);
    let sources = source(&root, files);
    if full {
        println!(
            "store load of {} files of {FILE_BYTES} bytes under {}, filesystem {}, device {}",
            files.0,
            asked.directory.display(),
            substrate.filesystem,
            substrate.named()
        );
        println!(
            "| width | records | wall (ms) | puts per second | p50 call (µs) | p99 call (µs) | \
             naming (µs) | open (ms) | user CPU (ms) | system CPU (ms) | voluntary switches | \
             filesystem | device |"
        );
        println!(
            "| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |"
        );
    }
    for width in widths {
        let store = root.join(format!("store-{}", width.0));
        let pass = load(&store, &sources, width);
        assert!(
            pass.records.0 >= files.0,
            "each file puts at least its one piece"
        );
        let open = reopened(&store);
        if full {
            row(width, &pass, open, &substrate);
        }
        fs::remove_dir_all(&store).expect("the store of a width is removed");
    }
    fs::remove_dir_all(&root).expect("the scratch directory is removed");
}
