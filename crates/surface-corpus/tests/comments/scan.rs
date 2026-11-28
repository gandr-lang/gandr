//! The fixture walk: every `.gandr` source, links not followed.

use std::fs;
use std::path::Path;

use anodized::spec;
use gandr_surface_grammar::Pbg;

use crate::comments::error::CommentError;
use crate::comments::judge::Finding;
use crate::comments::judge::findings_of;

/// Every uncommented item under `fixture`, keys relative to it.
///
/// Symbolic links are not followed. Only files whose name ends in `.gandr`
/// are judged. The keys use `/` separators, so a key found on one host
/// matches a key found on another. The shape of a doc comment is
/// `check:prose`'s.
///
/// # Specification
/// - requires: `fixture` is a directory.
/// - ensures: the uncommented findings of every `.gandr` file under `fixture`,
///   each keyed by its path relative to `fixture`.
/// - provides: the findings that the gate gives as the kind `uncommented`.
/// - fails: a directory entry cannot be read, a source cannot be read, a path
///   is not Unicode, or a source does not commit a tree.
/// - panics: none.
///
/// # Errors
/// [`CommentError::Read`] when a directory or a source cannot be read.
/// [`CommentError::File`] when a path is not Unicode or contains a colon.
/// [`CommentError::Parse`] and [`CommentError::Mold`] as [`findings_of`].
///
/// # Adequacy
/// - hypothesis: L3 — a directory of one uncommented source and one commented
///   source yields only the uncommented line; a symbolic link is not walked.
///   The witnesses construct that directory.
/// - witness: `tests::comments::scan::tests::a_walk_names_the_uncommented_source_and_skips_a_link`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|found| found.iter().zip(found.iter().skip(1)).all(|(left, right)| left.line() <= right.line())))]
#[inline]
pub fn collect(
    pbg: &Pbg,
    fixture: &Path,
) -> Result<Vec<Finding>, CommentError>
{
    let mut files = Vec::new();
    let mut pending = Vec::from([fixture.to_owned()]);
    while let Some(directory) = pending.pop() {
        let entries = fs::read_dir(&directory).map_err(|error| CommentError::Read {
            path: directory.clone(),
            detail: error.to_string(),
        })?;
        for entry in entries {
            let entry = entry.map_err(|error| CommentError::Read {
                path: directory.clone(),
                detail: error.to_string(),
            })?;
            let file_type = entry.file_type().map_err(|error| CommentError::Read {
                path: entry.path(),
                detail: error.to_string(),
            })?;
            if file_type.is_symlink() {
                continue;
            }
            if file_type.is_dir() {
                pending.push(entry.path());
                continue;
            }
            if is_gandr(&entry.path()).0 {
                files.push(entry.path());
            }
        }
    }
    files.sort();
    let mut found = Vec::new();
    for path in files {
        let key = file_key(fixture, &path)?;
        let text = fs::read_to_string(&path).map_err(|error| CommentError::Read {
            path: path.clone(),
            detail: error.to_string(),
        })?;
        found.extend(findings_of(
            pbg,
            crate::comments::shape::Text(&key),
            crate::comments::shape::Text(&text),
        )?);
    }
    found.sort_by(|left, right| left.line().cmp(&right.line()));
    Ok(found)
}

/// Whether `path`'s name ends in `.gandr`.
///
/// # Specification
/// trivial.
fn is_gandr(path: &Path) -> crate::comments::shape::Yes
{
    crate::comments::shape::Yes(
        path.extension()
            .is_some_and(|extension| extension == "gandr"),
    )
}

/// `path` relative to `fixture`, with `/` separators.
///
/// # Specification
/// - requires: `path` is under `fixture`.
/// - ensures: the relative path with `/` separators, or a refusal naming `path`
///   when it is not under `fixture`, not Unicode, or contains a colon.
/// - provides: the file half of a finding.
/// - fails: as ensures.
/// - panics: none.
/// - executable: none — the key is a path the predicate would rebuild, and a
///   missing parent is a filesystem fact, not a value the predicate can read.
///
/// # Adequacy
/// - hypothesis: L3 — a walked source is keyed under the fixture, and a colon
///   in that key is refused.
/// - witness: `tests::comments::scan::tests::a_walk_names_the_uncommented_source_and_skips_a_link`
///
/// # Errors
/// [`CommentError::File`] when the relative path cannot be a key.
fn file_key(
    fixture: &Path,
    path: &Path,
) -> Result<String, CommentError>
{
    let relative = path
        .strip_prefix(fixture)
        .map_err(|_error| CommentError::File {
            path: path.to_owned(),
            detail: "the source is not under the fixture root".to_owned(),
        })?;
    let mut key = String::new();
    for (index, component) in relative.components().enumerate() {
        if index > 0 {
            key.push('/');
        }
        let Some(text) = component.as_os_str().to_str()
        else {
            return Err(CommentError::File {
                path: path.to_owned(),
                detail: "the source path is not Unicode".to_owned(),
            });
        };
        key.push_str(text);
    }
    if key.contains(':') {
        return Err(CommentError::File {
            path: path.to_owned(),
            detail: "a file key cannot contain ':'".to_owned(),
        });
    }
    Ok(key)
}

#[cfg(test)]
mod tests
{
    use std::fs;

    use super::collect;
    use crate::comments::judge::grammar;

    #[test]
    fn a_walk_names_the_uncommented_source_and_skips_a_link()
    {
        let root = std::env::temp_dir().join(format!("corpus-comments-{}", std::process::id()));
        drop(fs::remove_dir_all(&root));
        fs::create_dir_all(root.join("kept")).expect("the scratch directory creates");
        fs::write(root.join("kept/bare.gandr"), "def bare = 1;\n").expect("the source writes");
        fs::write(root.join("kept/shown.gandr"), "// shown\ndef shown = 1;\n")
            .expect("the source writes");
        #[cfg(unix)]
        {
            let outside = std::env::temp_dir()
                .join(format!("corpus-comments-link-{}.gandr", std::process::id()));
            fs::write(&outside, "def linked = 1;\n").expect("the link target writes");
            std::os::unix::fs::symlink(&outside, root.join("kept/linked.gandr"))
                .expect("the link creates");
        }

        let pbg = grammar().expect("the built-in grammar builds");
        let found = collect(&pbg, &root).expect("the walk reads the scratch directory");
        let lines: Vec<&str> = found.iter().map(|finding| finding.line().0).collect();
        assert!(
            lines
                .iter()
                .any(|line| line.starts_with("kept/bare.gandr:bare:")),
            "the uncommented item is named"
        );
        assert!(
            lines.contains(&"kept/bare.gandr:<file> uncommented"),
            "the uncommented file is named"
        );
        assert!(
            !lines
                .iter()
                .any(|line| line.contains("shown") && !line.contains("<file>")),
            "a commented item is not debt"
        );
        #[cfg(unix)]
        assert!(
            !lines.iter().any(|line| line.contains("linked")),
            "a symbolic link is not walked"
        );
        fs::remove_dir_all(&root).expect("the scratch directory removes");
    }
}
