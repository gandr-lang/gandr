//! The references of the tree: the citations of the crates and the corpus,
//! and the citation window over them.
//!
//! [`cites::citations`] reads the citations of one source. [`sources`] lists
//! the sources of a tree: each `README.md` of a crate, each module source of
//! a crate, and each corpus source. [`window::findings`] judges the citations
//! against the policy of the window and the years of the works.
//!
//! The `references` binary runs the window over a tree. The landing runs it,
//! so a new citation of a work older than the cutoff year is refused at its
//! site.

extern crate alloc;

pub mod cites;
pub mod window;

use alloc::string::String;
use alloc::vec::Vec;
use std::path::Path;

use anodized::spec;

/// Appends to `out` each file below `directory` whose name ends with
/// `suffix`, as a path that starts with `prefix`.
///
/// # Specification
/// - ensures: each file of the directory tree, by its path from the root with
///   `/` between the parts, in the order of the names.
/// - fails: a directory that cannot be read.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of the first directory that cannot be read.
fn walk(
    directory: &Path,
    prefix: &str,
    suffix: &str,
    out: &mut Vec<String>,
) -> std::io::Result<()>
{
    let mut entries = std::fs::read_dir(directory)?
        .map(|entry| entry.map(|entry| (entry.file_name(), entry.path())))
        .collect::<std::io::Result<Vec<_>>>()?;
    entries.sort();
    for (name, path) in entries {
        let Some(name) = name.to_str()
        else {
            continue;
        };
        let shown = format!("{prefix}/{name}");
        if path.is_dir() {
            walk(&path, &shown, suffix, out)?;
        }
        else if name.ends_with(suffix) {
            out.push(shown);
        }
    }
    Ok(())
}

/// The sources of the tree at `root` whose citations the window reads, by
/// their paths from the root.
///
/// # Specification
/// - ensures: for each directory of `crates/`, its `README.md` and each `.rs`
///   file below its `src/`, but the files below `src/bin/` and `src/main.rs`
///   beside a `src/lib.rs`; then each `.gandr` file below `corpus/`.
/// - fails: a directory that cannot be read.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of the first directory that cannot be read.
///
/// # Cost
/// - allocation: the paths, setup
/// - io: one read of each directory
///
/// # Adequacy
/// - hypothesis: L3 — a tree with a library crate, a binary crate and a corpus
///   source lists each source the window reads, and leaves out the binary
///   targets of the library crate.
/// - witness: `tests::cli::the_window_reads_the_sources_of_a_tree`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|paths| paths.iter().all(|path| path.starts_with("crates/") || path.starts_with("corpus/"))) || ret.is_err())]
#[inline]
pub fn sources(root: &Path) -> std::io::Result<Vec<String>>
{
    let mut paths = Vec::new();
    let crates = root.join("crates");
    let mut names = std::fs::read_dir(&crates)?
        .map(|entry| entry.map(|entry| entry.file_name()))
        .collect::<std::io::Result<Vec<_>>>()?;
    names.sort();
    for name in names {
        let Some(name) = name.to_str()
        else {
            continue;
        };
        let directory = crates.join(name);
        if directory.join("README.md").is_file() {
            paths.push(format!("crates/{name}/README.md"));
        }
        let source = directory.join("src");
        if !source.is_dir() {
            continue;
        }
        let library = source.join("lib.rs").is_file();
        let mut modules = Vec::new();
        walk(&source, &format!("crates/{name}/src"), ".rs", &mut modules)?;
        let bin = format!("crates/{name}/src/bin/");
        let main = format!("crates/{name}/src/main.rs");
        paths.extend(
            modules
                .into_iter()
                .filter(|path| !path.starts_with(&bin) && (!library || *path != main)),
        );
    }
    let corpus = root.join("corpus");
    if corpus.is_dir() {
        walk(&corpus, "corpus", ".gandr", &mut paths)?;
    }
    Ok(paths)
}
