//! The digest of a corpus walk, shared by the tests of one nextest run
//! (#5256).
//!
//! nextest runs each test in a process of its own, so two tests that walk the
//! same roots compose them twice. A test that reads a shared walk asks for its
//! digest by name: the first test of the run to ask builds it under a file
//! lock and writes it; each later test reads it. The digest lives under the
//! run's own directory (`NEXTEST_RUN_ID`, a UUID) in the host's temporary
//! directory, so no run reads another's, and the library's own tests reach it
//! as the integration tests do. Outside nextest each test builds its own.

use core::time::Duration;
use std::fs;
use std::fs::File;
use std::path::Path;

use serde::Serialize;
use serde::de::DeserializeOwned;

/// How old another run's directory must be before a new run removes it.
const STALE: Duration = Duration::from_hours(24);

/// The value `build` gives, built once in this nextest run under the file
/// stem `name` and read back by every later test of the run that asks for it.
///
/// # Specification
/// - requires: `name` is a file stem; every caller passing `name` in one run
///   passes a `build` that gives the same value.
/// - ensures: the value `build` gives, or the value an earlier test of this run
///   wrote for `name`. Outside nextest, `build`'s value.
/// - fails: never; a digest a killed writer leaves is never read, because the
///   writer renames it into place only once it is whole.
/// - panics: when the run's directory, the lock or the digest cannot be written
///   or read.
/// - executable: none — the digest is a file that other processes write, which
///   no predicate over the arguments and the value reads.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus tests read one digest each run; a test that
///   finds it reads the same verdicts the builder asserted.
/// - witness: `tests::corpus::focusing_is_total_on_the_model_corpus`
/// - witness: `tests::corpus::every_corpus_source_is_registered`
pub fn shared<T>(
    name: &Path,
    build: impl FnOnce() -> T,
) -> T
where
    T: Serialize + DeserializeOwned,
{
    let Some(run) = std::env::var_os("NEXTEST_RUN_ID")
    else {
        return build();
    };
    let digests = std::env::temp_dir().join("gandr-walk-digest");
    let directory = digests.join(run);
    let fresh = !directory.exists();
    fs::create_dir_all(&directory).expect("the run's digest directory is made");
    if fresh {
        sweep(&digests, &directory);
    }
    let stem = directory.join(name);
    let lock = File::create(stem.with_extension("lock")).expect("the digest's lock opens");
    lock.lock().expect("the digest's lock is taken");
    let path = stem.with_extension("json");
    if let Ok(text) = fs::read_to_string(&path) {
        return serde_json::from_str(&text).expect("the digest reads back");
    }
    let value = build();
    let partial = stem.with_extension("json.partial");
    fs::write(
        &partial,
        serde_json::to_string(&value).expect("the digest writes"),
    )
    .expect("the digest is written");
    fs::rename(&partial, &path).expect("the digest moves into place");
    value
}

/// Remove each directory under `digests` but `own` that is older than
/// [`STALE`]: a run that ended long ago.
///
/// # Specification
/// trivial.
fn sweep(
    digests: &Path,
    own: &Path,
)
{
    let Ok(entries) = fs::read_dir(digests)
    else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let old = entry
            .metadata()
            .and_then(|metadata| metadata.modified())
            .ok()
            .and_then(|modified| modified.elapsed().ok())
            .is_some_and(|age| age > STALE);
        if path != own && old {
            drop(fs::remove_dir_all(path));
        }
    }
}
