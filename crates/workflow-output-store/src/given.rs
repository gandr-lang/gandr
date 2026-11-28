//! The values that a test gives the store: the values of a kind that only a
//! test can compute, such as a text that a test builds from inputs in Rust.
//!
//! The run of the tests of such a kind names the store in [`STORE`] and the
//! directory of the run in [`RUN`]. A test writes its value to the store at
//! the digest of its kind and its bytes. It writes an entry with the key and
//! the name of the value to the directory of the run. The run reads each
//! entry of its directory into the list of its tree. With either variable
//! unset, a test gives nothing and checks the properties of its value alone.

use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use crate::Digest;
use crate::Kind;
use crate::Listed;
use crate::Store;
use crate::write_whole;

/// The variable that names the store of a run of the tests.
pub const STORE: &str = "GANDR_OUTPUT_STORE";

/// The variable that names the directory of a run of the tests.
pub const RUN: &str = "GANDR_OUTPUT_RUN";

/// The end of the name of a file that a writer has not renamed into its
/// place yet.
const PARTIAL: &str = ".partial";

/// The store and the directory of the run that the environment names, or
/// `None` when [`STORE`] or [`RUN`] is unset.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn asked() -> Option<(Store, PathBuf)>
{
    let store = std::env::var_os(STORE)?;
    let run = std::env::var_os(RUN)?;
    Some((Store::at(PathBuf::from(store)), PathBuf::from(run)))
}

/// Gives the value `value` of the kind `kind` at the name `name` to the run
/// that the environment names, and gives whether the environment names one.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`put`].
#[inline]
pub fn give(
    kind: Kind,
    name: &str,
    value: &[u8],
) -> io::Result<bool>
{
    let Some((store, run)) = asked()
    else {
        return Ok(false);
    };
    put(&store, &run, kind, name, value)?;
    Ok(true)
}

/// Writes `value` to `store` as a value of `kind`, at the digest of the kind
/// and the bytes, and writes the entry of `name` to the directory `run`. A
/// second value at the same name replaces the entry of the first.
///
/// # Specification
/// - requires: `name` holds no tab and no line break.
/// - ensures: [`entries`] of `run` and `kind` has one entry named `name`, whose
///   key gives `value` in `store`.
///
/// # Errors
/// [`io::ErrorKind::InvalidInput`] for a name with a tab or a line break, and
/// a directory or a file of the store or of the run that cannot be written.
///
/// # Adequacy
/// - hypothesis: L3 — two values read back as their entries in name order, a
///   second value at one name replaces the first, and a name with a tab is
///   refused.
/// - witness: `given::tests::a_given_value_is_an_entry_of_its_run`
#[inline]
pub fn put(
    store: &Store,
    run: &Path,
    kind: Kind,
    name: &str,
    value: &[u8],
) -> io::Result<()>
{
    if name.contains(['\t', '\n', '\r']) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("the name of a given value holds a tab or a line break: {name:?}"),
        ));
    }
    let key = Digest::of_parts([b"given".as_slice(), kind.0.as_bytes(), value]);
    store.put(kind, &key, value)?;
    let entry = Digest::of_parts([name.as_bytes()]).hex();
    write_whole(
        &run.join(kind.0).join(entry),
        format!("{}\t{name}", key.hex()).as_bytes(),
    )
}

/// The entries that the tests of the run at `run` gave of `kind`, in name
/// order: each with its key, an empty input and its name. A value that a
/// test gives has no one source, so it has no git object.
///
/// # Specification
/// trivial.
///
/// # Errors
/// A directory or a file of the run that cannot be read, and
/// [`io::ErrorKind::InvalidData`] for an entry that is not a key, a tab and a
/// name.
///
/// # Adequacy
/// - hypothesis: L3 — as [`put`].
/// - witness: `given::tests::a_given_value_is_an_entry_of_its_run`
#[inline]
pub fn entries(
    run: &Path,
    kind: Kind,
) -> io::Result<Vec<Listed>>
{
    let directory = match fs::read_dir(run.join(kind.0)) {
        Ok(directory) => directory,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => return Err(error),
    };
    let mut listed = Vec::new();
    for entry in directory {
        let path = entry?.path();
        if path
            .file_name()
            .and_then(|name| name.to_str())
            .is_none_or(|name| name.ends_with(PARTIAL))
        {
            continue;
        }
        let text = fs::read_to_string(&path)?;
        let malformed = || {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{} is no key, tab and name", path.display()),
            )
        };
        let (key, name) = text.split_once('\t').ok_or_else(malformed)?;
        listed.push(Listed {
            key: Digest::of_hex(key).ok_or_else(malformed)?,
            object: String::new(),
            name: name.to_owned(),
        });
    }
    listed.sort_by(|left, right| left.name.cmp(&right.name));
    Ok(listed)
}

#[cfg(test)]
mod tests
{
    use super::Kind;
    use super::Store;
    use super::entries;
    use super::put;

    /// Two values read back as their entries in name order, each key gives
    /// its value, a second value at one name replaces the first, another
    /// kind has no entry, and a name with a tab is refused.
    #[test]
    fn a_given_value_is_an_entry_of_its_run()
    {
        let root = std::env::temp_dir().join(format!("gandr-given-{}", std::process::id()));
        let store = Store::at(root.join("store"));
        let run = root.join("run");
        let kind = Kind("hovers");
        put(&store, &run, kind, "b.gandr", b"second\n").expect("the value is given");
        put(&store, &run, kind, "a.gandr", b"stale\n").expect("the value is given");
        put(&store, &run, kind, "a.gandr", b"first\n").expect("the value is given");
        let given = entries(&run, kind).expect("the run reads");
        let read: Vec<(&str, Option<Vec<u8>>)> = given
            .iter()
            .map(|entry| {
                (
                    entry.name.as_str(),
                    store.get(kind, &entry.key).expect("the store reads"),
                )
            })
            .collect();
        assert_eq!(read, [
            ("a.gandr", Some(b"first\n".to_vec())),
            ("b.gandr", Some(b"second\n".to_vec()))
        ]);
        assert!(
            given.iter().all(|entry| entry.object.is_empty()),
            "a given value has no git object"
        );
        assert!(
            entries(&run, Kind("captures"))
                .expect("the run reads")
                .is_empty(),
            "another kind has no entry"
        );
        assert!(
            put(&store, &run, kind, "a\tb", b"x").is_err(),
            "a name with a tab is refused"
        );
        std::fs::remove_dir_all(root).expect("the scratch is removed");
    }
}
