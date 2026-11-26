//! The features ledger that the binary carries: the schema of the tree's
//! ledger, then each row of it in the order of its id, then the schema of the
//! needs and each file of needs, as one text in the build directory.

use std::env;
use std::io;
use std::path::Path;
use std::path::PathBuf;

/// Writes `features.sql` in `OUT_DIR`: `ledger/features-schema.sql`, then the
/// file of each row of `ledger/features/`, in the order of the file names,
/// then `ledger/requires-schema.sql` and each file of `ledger/requires/`, in
/// the same order.
///
/// # Specification
/// - ensures: the text is the two schemas, each row file and each file of needs
///   of the tree, whole, in the order of their ids; Cargo runs the script again
///   when a file of the ledger changes.
/// - executable: none — the output is a file that the crate includes.
///
/// # Errors
/// An I/O error when `OUT_DIR` is unset, or when a file of the ledger does
/// not read or the text does not write.
///
/// # Adequacy
/// - hypothesis: L3 — the ledger that the binary carries reads as the tree's
///   ledger, row for row.
/// - witness: `tests::the_built_in_ledger_is_the_committed_one`
fn main() -> io::Result<()>
{
    let ledger = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../ledger");
    let mut text = String::new();
    for (schema, rows) in [
        ("features-schema.sql", "features"),
        ("requires-schema.sql", "requires"),
    ] {
        let schema = ledger.join(schema);
        let rows = ledger.join(rows);
        println!("cargo::rerun-if-changed={}", schema.display());
        println!("cargo::rerun-if-changed={}", rows.display());
        let mut paths: Vec<PathBuf> = std::fs::read_dir(&rows)?
            .map(|entry| entry.map(|entry| entry.path()))
            .collect::<io::Result<_>>()?;
        paths.retain(|path| path.extension().is_some_and(|extension| extension == "sql"));
        paths.sort_by(|left, right| left.file_stem().cmp(&right.file_stem()));
        text.push_str(&std::fs::read_to_string(&schema)?);
        for path in paths {
            text.push_str(&std::fs::read_to_string(path)?);
        }
    }
    let out = env::var_os("OUT_DIR").ok_or_else(|| io::Error::other("Cargo sets OUT_DIR"))?;
    std::fs::write(Path::new(&out).join("features.sql"), text)
}
