//! The extent size of a device: the smallest extent whose appends, each with
//! one data sync, write bytes at the device's full rate.
//!
//! A store's shards seal each segment at this size, so the size is what a
//! sealed segment holds: large enough that its sync costs the device's rate,
//! and no larger, so the open segments that a crash leaves to the scan stay
//! small.
//!
//! # Examples
//!
//! `cargo bench -p gandr-storage-store --bench profile -- --directory <path>`
//! appends extents of 64 KiB, doubling to 64 MiB, to a file under that
//! directory, and prints one row for each size and then the line
//! `seal_bytes = <n>`. `mise run store:profile <path>` writes that line into
//! the `[store]` table of the user's configuration. Under `cargo test`, the
//! bench appends two small extents and prints nothing.
//!
//! # Items
//!
//! Each size writes at least 64 MiB, and at least four extents, each in one
//! positioned write followed by one `fdatasync`. Its rate is the bytes over
//! the wall time. The extent size is the smallest size whose rate is nine
//! tenths of the best rate or more.
//!
//! # References
//!
//! - `vault:01a1d90b-b64a-7248-8f6e-e792b6e8cb9f` — anchor: the IO layer's
//!   probe (§ the grid) — a segment's appends with one sync each, whose rate at
//!   each size this bench reads again on the host.

#![expect(
    clippy::expect_used,
    clippy::print_stdout,
    reason = "a measurement binary: a failed setup ends the run, and the figures are its output"
)]

use core::time::Duration;
use std::fs;
use std::fs::File;
use std::os::unix::fs::FileExt as _;
use std::path::Path;
use std::path::PathBuf;
use std::time::Instant;

/// The smallest extent a full run writes.
const LEAST: Bytes = Bytes(64 << 10);

/// The largest extent a full run writes.
const MOST: Bytes = Bytes(64 << 20);

/// The bytes each size writes at least.
const TOTAL: Bytes = Bytes(64 << 20);

/// The extents each size writes at least.
const EXTENTS: u64 = 4;

/// The sizes a test-mode pass writes, and the bytes of each.
const SMOKE: [Bytes; 2] = [Bytes(4 << 10), Bytes(8 << 10)];

/// A count of bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Bytes(u64);

/// A count of bytes over each second of a wall time.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Rate(u128);

/// One size the run measured, and the rate its appends wrote at.
#[derive(Clone, Copy, Debug)]
struct Row
{
    /// The extent size.
    size: Bytes,
    /// The appends' rate.
    rate: Rate,
    /// The wall time of the size's appends.
    wall: Duration,
}

/// The rate of the appends of `size`, each synced, into a fresh file at
/// `path`, and their wall time.
///
/// # Specification
/// trivial.
fn appended(
    path: &Path,
    size: Bytes,
    total: Bytes,
) -> Row
{
    let file = File::options()
        .read(true)
        .write(true)
        .create(true)
        .truncate(true)
        .open(path)
        .expect("the profile file opens");
    let extent = vec![0xA5_u8; usize::try_from(size.0).expect("an extent fits in memory")];
    let extents = total.0.div_ceil(size.0).max(EXTENTS);
    let started = Instant::now();
    let mut at = 0_u64;
    for _extent in 0 .. extents {
        file.write_all_at(&extent, at)
            .expect("an extent is written");
        file.sync_data().expect("an extent syncs");
        at = at.saturating_add(size.0);
    }
    let wall = started.elapsed();
    drop(file);
    fs::remove_file(path).expect("the profile file is removed");
    Row {
        size,
        rate: Rate(
            u128::from(at)
                .saturating_mul(1_000_000)
                .checked_div(wall.as_micros().max(1))
                .unwrap_or_default(),
        ),
        wall,
    }
}

/// The smallest size of `rows` whose rate is nine tenths of the best or more.
///
/// # Specification
/// trivial.
fn chosen(rows: &[Row]) -> Option<Bytes>
{
    let best = rows.iter().map(|row| row.rate).max()?;
    rows.iter()
        .find(|row| row.rate.0.saturating_mul(10) >= best.0.saturating_mul(9))
        .map(|row| row.size)
}

/// What the command line asks of a run.
struct Arguments
{
    /// A full run, which measures each size and prints; otherwise one short
    /// pass.
    full: bool,
    /// The directory on the device that the run measures.
    directory: PathBuf,
}

/// The arguments of the process: `--bench`, and `--directory <path>`.
///
/// # Specification
/// trivial.
fn arguments() -> Arguments
{
    let mut parsed = Arguments {
        full: false,
        directory: std::env::temp_dir(),
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
            _ => {},
        }
    }
    parsed
}

/// Measure each size and print its row and the extent size.
///
/// # Specification
/// trivial.
fn main()
{
    let Arguments { full, directory } = arguments();
    let path = directory.join(format!("gandr-storage-profile-{}", std::process::id()));
    let sizes: Vec<Bytes> = if full {
        core::iter::successors(Some(LEAST), |size| {
            Some(Bytes(size.0.saturating_mul(2))).filter(|next| *next <= MOST)
        })
        .collect()
    }
    else {
        SMOKE.to_vec()
    };
    let total = if full { TOTAL } else { Bytes(16 << 10) };
    let rows: Vec<Row> = sizes
        .iter()
        .map(|&size| appended(&path, size, total))
        .collect();
    let size = chosen(&rows).expect("a run measures a size");
    if full {
        println!("extents under {}, each synced", directory.display());
        println!("| extent (KiB) | wall (ms) | MiB per second |");
        println!("| ---: | ---: | ---: |");
        for row in &rows {
            println!(
                "| {} | {} | {} |",
                row.size.0 >> 10_u32,
                row.wall.as_millis(),
                row.rate.0 >> 20_u32
            );
        }
        println!("seal_bytes = {}", size.0);
    }
}
