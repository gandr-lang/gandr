//! The built-in mold table as a file of the user's cache, named by the digest
//! of the rules.
//!
//! A process reads the file and thaws the table while the rules digest to the
//! name of the file. With no file, or a file that does not read or thaw, it
//! builds the rules through every gate and writes the file for the next
//! process. The file goes to a name of its own first and then moves to its
//! place, so a reader never sees half of a file.
//!
//! The directory is `gandr/grammar` under `$XDG_CACHE_HOME` when it is an
//! absolute path, else under `$HOME/.cache`, the rule of the cache of the
//! driver. With neither, each process builds the rules.

extern crate std;

use alloc::format;
use std::path::Path;
use std::path::PathBuf;

use crate::model::Pbg;
use crate::model::PbgError;
use crate::model::PrecTable;
use crate::model::Rule;
use crate::model::RulesDigest;
use crate::model::tile_labels;
use crate::mold::FrozenTable;

/// The built-in grammar of `rules` over `precs`: thawed from the baked file of
/// their digest in `directory`, or built through every gate and baked there.
///
/// # Specification
/// - requires: `precs` and `rules` are the built-in table and rules.
/// - ensures: the grammar [`Pbg::build_table`] gives for them. A file of the
///   digest that reads and thaws gives it; else the gated build gives it, and
///   the file is written when `directory` takes it.
/// - fails: as [`Pbg::build_table`].
/// - panics: none.
///
/// # Errors
/// A [`PbgError`] of the gated build.
///
/// # Cost
/// - allocation: the bytes of the file and the frozen columns, setup
/// - io: one read of the file; with no file, one write and one rename
///
/// # Adequacy
/// - hypothesis: L3 — a process with an empty directory builds and writes the
///   file, and a second call thaws it to the same grammar, whole; a file that
///   does not read is written again.
/// - witness: `surface::tests::a_baked_file_thaws_to_the_built_grammar`
pub(super) fn built_in(
    precs: PrecTable,
    rules: alloc::vec::Vec<Rule>,
    directory: Option<&Path>,
) -> Result<Pbg, PbgError>
{
    let digest = RulesDigest::of(&rules);
    let labels = tile_labels(&rules);
    let path = directory.map(|directory| directory.join(format!("{:016x}.molds", digest.0)));
    let frozen = path
        .as_ref()
        .and_then(|path| std::fs::read(path).ok())
        .and_then(|bytes| FrozenTable::read(&bytes, &labels))
        .filter(|frozen| frozen.rules == digest);
    let (precs, rules) = match frozen {
        None => (precs, rules),
        Some(frozen) => match Pbg::thawed(precs, rules, &frozen) {
            Ok(grammar) => return Ok(grammar),
            Err(_refused) => {
                let precs = super::built_in_prec_table()?;
                let rules = super::built_in_rules(&precs)?;
                (precs, rules)
            },
        },
    };
    let grammar = Pbg::build_table(precs, rules)?;
    if let Some(path) = path {
        write(&path, &grammar.frozen().bytes(&labels));
    }
    Ok(grammar)
}

/// The directory of the baked tables: `gandr/grammar` under the cache
/// directory of the user.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `$XDG_CACHE_HOME/gandr/grammar` when `$XDG_CACHE_HOME` is an
///   absolute path, else `$HOME/.cache/gandr/grammar` when `$HOME` is set, else
///   absent.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — the rule of the cache of the driver, read from the
///   environment of the process; the witness of the file passes a directory of
///   its own, so it does not depend on the cache of the user.
pub(super) fn directory() -> Option<PathBuf>
{
    let home = std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .filter(|home| home.is_absolute())
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cache")))?;
    Some(home.join("gandr").join("grammar"))
}

/// Writes `bytes` to `path` through a name of this process, then moves them
/// to `path`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `path` holds `bytes` when each step succeeds; a step that fails
///   leaves `path` as it was, and the next process builds again.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the witness reads the written file back.
/// - witness: `surface::tests::a_baked_file_thaws_to_the_built_grammar`
fn write(
    path: &std::path::Path,
    bytes: &[u8],
)
{
    let part = path.with_extension(format!("{}.part", std::process::id()));
    let written = path
        .parent()
        .map_or(Ok(()), std::fs::create_dir_all)
        .and_then(|()| std::fs::write(&part, bytes))
        .and_then(|()| std::fs::rename(&part, path));
    if written.is_err() {
        drop(std::fs::remove_file(&part));
    }
}
