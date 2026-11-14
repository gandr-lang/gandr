//! The store's load: many files read into one store at once, the rate of its
//! puts beside the rate of the fold of one writer.
//!
//! The bench first makes a source tree of 20,000 files of 4 KiB. The BLAKE3
//! output of the index of a file fills it, so no two files share a piece. A
//! file of 4 KiB is no longer than the least cut of the byte profile, so it
//! reads as one piece. For each width, a fresh store opens, and that many
//! threads load the tree into it with `Store::read_in`. Each thread loads
//! every width-th file. The put rate is the count of objects in the two planes
//! after the load, over the wall time of the load.
//!
//! The fold is the work of the single writer of a sharded store. One thread
//! renames each object of the width-1 store into a fresh plane directory,
//! then syncs that directory once. The fold rate is the count of objects that
//! it renames, over the wall time of the renames and the sync. A width whose
//! put rate is above the fold rate outruns one writer.
//!
//! # Examples
//!
//! `cargo bench -p gandr-storage-store --bench load` measures the widths 1, 16
//! and 64 under the temporary directory of the host, and prints one row for
//! each width. `-- --directory <path>` puts the source tree and the stores
//! under that directory. `-- --widths 1,8,96` measures the widths that it
//! names. Under `cargo test`, the bench loads 64 files at widths 1 and 2 and
//! prints nothing, so the gates run it and do not time it.
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
//!   writer plan (§ The topology of one host) — the fold of the writer beside
//!   the sum of the rates of the producers is the measure of the shards.
//! - `vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583` — anchor: the performance
//!   programme (§ performance-figures) — a row names what it measures: the
//!   filesystem, the device, the CPU and the voluntary switches.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

use core::time::Duration;
use std::fs;
use std::fs::File;
#[cfg(target_os = "macos")]
use std::os::unix::fs::FileTypeExt as _;
#[cfg(target_os = "macos")]
use std::os::unix::fs::MetadataExt as _;
use std::path::Path;
use std::path::PathBuf;
use std::time::Instant;

use gandr_storage_store::Store;
use nix::sys::resource::UsageWho;
use nix::sys::resource::getrusage;
use nix::sys::time::TimeVal;

/// How many files a full run loads.
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

/// A count of files, threads or objects.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Count(usize);

/// A count of objects over each second of a wall time.
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

/// The objects that one pass moves, its wall time, and what the process spent
/// during it.
#[derive(Clone, Copy)]
struct Pass
{
    /// The objects that the planes gain.
    objects: Count,
    /// The wall time of the pass.
    wall: Duration,
    /// The CPU and the voluntary switches of the process during the pass.
    spent: Spent,
}

impl Pass
{
    /// The objects of the pass over each second of its wall time.
    ///
    /// # Specification
    /// trivial.
    fn rate(self) -> Rate
    {
        let objects = u128::try_from(self.objects.0).expect("a count fits in 128 bits");
        Rate(
            objects
                .saturating_mul(1_000_000)
                .checked_div(self.wall.as_micros().max(1))
                .unwrap_or_default(),
        )
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

/// The objects under the plane directories of `store`: each file named by 64
/// lowercase hexadecimal digits.
///
/// # Specification
/// trivial.
fn objects(store: &Path) -> Vec<PathBuf>
{
    PLANES
        .iter()
        .flat_map(|plane| fs::read_dir(store.join(plane)).expect("a plane lists"))
        .map(|entry| entry.expect("a plane entry reads").path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| {
                    name.len() == 64
                        && name
                            .bytes()
                            .all(|byte| byte.is_ascii_digit() || (b'a' ..= b'f').contains(&byte))
                })
        })
        .collect()
}

/// Read every file of `files` into a fresh store at `store`, `width` threads
/// at once.
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
    let (opened, _register) = Store::open(store).expect("a fresh store opens");
    let before = Spent::now();
    let started = Instant::now();
    std::thread::scope(|scope| {
        for first in 0 .. width.0 {
            let opened = &opened;
            scope.spawn(move || {
                for path in files.iter().skip(first).step_by(width.0) {
                    opened.read_in(path).expect("a source file reads in");
                }
            });
        }
    });
    let wall = started.elapsed();
    let spent = Spent::now().since(before);
    Pass {
        objects: Count(objects(store).len()),
        wall,
        spent,
    }
}

/// Rename every object of the store at `store` into a fresh plane directory
/// under `root`, then sync that directory once.
///
/// # Specification
/// trivial.
fn fold(
    store: &Path,
    root: &Path,
) -> Pass
{
    let shard = objects(store);
    let plane = root.join("plane");
    fs::create_dir_all(&plane).expect("the plane directory is made");
    let before = Spent::now();
    let started = Instant::now();
    for object in &shard {
        let name = object.file_name().expect("an object has a name");
        fs::rename(object, plane.join(name)).expect("an object renames into the plane");
    }
    File::open(&plane)
        .and_then(|directory| directory.sync_all())
        .expect("the plane directory syncs");
    let wall = started.elapsed();
    Pass {
        objects: Count(shard.len()),
        wall,
        spent: Spent::now().since(before),
    }
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
            .map(|stat| String::from(stat.filesystem_type_name()))
            .unwrap_or_default();
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
            .map(|path| path.display().to_string())
            .unwrap_or_default();
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

/// Print one row: `width`, the objects and the wall of `pass`, its put rate,
/// that rate over `fold`, what the process spent during the pass, and the
/// filesystem and the device of `substrate`.
///
/// # Specification
/// trivial.
fn row(
    width: Count,
    pass: Pass,
    fold: Rate,
    substrate: &Substrate,
)
{
    let put = pass.rate();
    println!(
        "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
        width.0,
        pass.objects.0,
        pass.wall.as_millis(),
        put.0,
        put.0
            .saturating_mul(100)
            .checked_div(fold.0.max(1))
            .unwrap_or_default(),
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
    /// The directory that holds the run, or the temporary one.
    directory: PathBuf,
    /// The widths that `--widths` names, if it names any.
    widths: Option<Vec<Count>>,
}

/// The arguments of the process: `--bench`, `--directory <path>` and
/// `--widths <list>`, each width of the list a count above zero.
///
/// # Specification
/// trivial.
fn arguments() -> Arguments
{
    let mut parsed = Arguments {
        full: false,
        directory: std::env::temp_dir(),
        widths: None,
    };
    let mut words = std::env::args().skip(1);
    while let Some(word) = words.next() {
        match word.as_str() {
            "--bench" => parsed.full = true,
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

/// Load the source tree at each width and print a row for each, beside the
/// fold of one writer, after a line that names the substrate.
///
/// # Specification
/// trivial.
fn main()
{
    let asked = arguments();
    let full = asked.full;
    let parallelism = std::thread::available_parallelism().map_or(1, usize::from);
    let (files, widths): (Count, Vec<Count>) = match (full, asked.widths) {
        (true, Some(named)) => (FULL, named),
        (true, None) => (
            FULL,
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

    // Width 1 loads first and folds, so each row after it can state its rate
    // beside the fold as its threads end.
    let single = root.join("store-1");
    let first = load(&single, &sources, Count(1));
    let folded = fold(&single, &root);
    let fold_rate = folded.rate();
    if full {
        println!(
            "store load of {} files of {FILE_BYTES} bytes under {}, filesystem {}, device {}; \
             the fold of one writer renames {} objects in {} ms, {} objects per second",
            files.0,
            asked.directory.display(),
            substrate.filesystem,
            substrate.named(),
            folded.objects.0,
            folded.wall.as_millis(),
            fold_rate.0
        );
        println!(
            "| width | objects | wall (ms) | puts per second | puts over the fold (%) | user CPU \
             (ms) | system CPU (ms) | voluntary switches | filesystem | device |"
        );
        println!("| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |");
        row(Count(1), first, fold_rate, &substrate);
    }
    fs::remove_dir_all(&single).expect("the store of width 1 is removed");
    fs::remove_dir_all(root.join("plane")).expect("the folded plane is removed");

    for width in widths.into_iter().filter(|width| width.0 > 1) {
        let store = root.join(format!("store-{}", width.0));
        let pass = load(&store, &sources, width);
        assert!(
            pass.objects.0 >= files.0,
            "each file puts at least its one piece"
        );
        if full {
            row(width, pass, fold_rate, &substrate);
        }
        fs::remove_dir_all(&store).expect("the store of a width is removed");
    }
    assert!(
        first.objects.0 >= files.0 && folded.objects.0 == first.objects.0,
        "each file puts at least its one piece, and the fold renames each object"
    );
    fs::remove_dir_all(&root).expect("the scratch directory is removed");
}
