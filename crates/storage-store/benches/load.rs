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
//! `cargo bench` runs the full measurement and prints one row for each width.
//! The bench omits a width above the parallelism of the host. Under `cargo
//! test`, the bench loads 64 files at widths 1 and 2 and prints nothing. So
//! the gates run it, and they do not time it.
//!
//! # References
//!
//! - `vault:01a1cf3f-b730-7152-9d64-050e5c00b32a` — anchor: the store's single
//!   writer plan (§ The topology of one host) — the fold of the writer beside
//!   the sum of the rates of the producers is the measure of the shards.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

use core::time::Duration;
use std::fs;
use std::fs::File;
use std::path::Path;
use std::path::PathBuf;
use std::time::Instant;

use gandr_storage_store::Store;

/// How many files a full run loads.
const FULL: Count = Count(20_000);

/// How many files a test-mode pass loads.
const SMOKE: Count = Count(64);

/// The bytes of each file: no more than the least cut of the byte profile, so
/// each file is one piece.
const FILE_BYTES: usize = 4_096;

/// The widths a full run measures.
const FULL_WIDTHS: [Count; 5] = [Count(1), Count(8), Count(16), Count(32), Count(64)];

/// The widths a test-mode pass loads at.
const SMOKE_WIDTHS: [Count; 2] = [Count(1), Count(2)];

/// The directories of the two planes under the root of a store.
const PLANES: [&str; 2] = ["chunks", "nodes"];

/// A count of files, threads or objects.
#[derive(Clone, Copy)]
struct Count(usize);

/// The objects that one pass moves, and the wall time it takes.
#[derive(Clone, Copy)]
struct Pass
{
    /// The objects that the planes gain.
    objects: Count,
    /// The wall time of the pass.
    wall: Duration,
}

impl Pass
{
    /// The objects of the pass over each second of its wall time.
    ///
    /// # Specification
    /// trivial.
    fn rate(self) -> u128
    {
        let objects = u128::try_from(self.objects.0).expect("a count fits in 128 bits");
        objects
            .saturating_mul(1_000_000)
            .checked_div(self.wall.as_micros().max(1))
            .unwrap_or_default()
    }
}

/// A fresh, empty directory for the run, removed first if a run left it.
///
/// # Specification
/// trivial.
fn scratch() -> PathBuf
{
    let directory = std::env::temp_dir().join(format!("gandr-storage-load-{}", std::process::id()));
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
fn load(
    store: &Path,
    files: &[PathBuf],
    width: Count,
) -> Pass
{
    let (opened, _register) = Store::open(store).expect("a fresh store opens");
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
    Pass {
        objects: Count(objects(store).len()),
        wall,
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
    }
}

/// Print one row: `width`, the objects and the wall of `pass`, its put rate,
/// and that rate over `fold_rate`.
///
/// # Specification
/// trivial.
fn row(
    width: Count,
    pass: Pass,
    fold_rate: u128,
)
{
    let put_rate = pass.rate();
    println!(
        "| {} | {} | {} | {put_rate} | {} |",
        width.0,
        pass.objects.0,
        pass.wall.as_millis(),
        put_rate
            .saturating_mul(100)
            .checked_div(fold_rate.max(1))
            .unwrap_or_default()
    );
}

fn main()
{
    let full = std::env::args().any(|argument| argument == "--bench");
    let (files, widths) = if full {
        (FULL, FULL_WIDTHS.as_slice())
    }
    else {
        (SMOKE, SMOKE_WIDTHS.as_slice())
    };
    let parallelism = std::thread::available_parallelism().map_or(1, usize::from);
    let root = scratch();
    let sources = source(&root, files);

    // Width 1 loads first and folds, so each row after it can state its rate
    // beside the fold as its threads end.
    let single = root.join("store-1");
    let first = load(&single, &sources, Count(1));
    let folded = fold(&single, &root);
    let fold_rate = folded.rate();
    if full {
        println!(
            "store load of {} files of {FILE_BYTES} bytes; the fold of one writer renames {} \
             objects in {} ms, {fold_rate} objects per second",
            files.0,
            folded.objects.0,
            folded.wall.as_millis()
        );
        println!("| width | objects | wall (ms) | puts per second | puts over the fold (%) |");
        println!("| ---: | ---: | ---: | ---: | ---: |");
        row(Count(1), first, fold_rate);
    }
    fs::remove_dir_all(&single).expect("the store of width 1 is removed");
    fs::remove_dir_all(root.join("plane")).expect("the folded plane is removed");

    for &width in widths
        .iter()
        .filter(|width| width.0 > 1 && width.0 <= parallelism)
    {
        let store = root.join(format!("store-{}", width.0));
        let pass = load(&store, &sources, width);
        assert!(
            pass.objects.0 >= files.0,
            "each file puts at least its one piece"
        );
        if full {
            row(width, pass, fold_rate);
        }
        fs::remove_dir_all(&store).expect("the store of a width is removed");
    }
    assert!(
        first.objects.0 >= files.0 && folded.objects.0 == first.objects.0,
        "each file puts at least its one piece, and the fold renames each object"
    );
    fs::remove_dir_all(&root).expect("the scratch directory is removed");
}
