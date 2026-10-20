//! Files moving: where a rename of files and folders takes each path, and the
//! address each path import writes once the file it names, or the source
//! writing it, has moved.
//!
//! An import's address is relative to the directory of the source writing it,
//! so a move rewrites two kinds of import: those naming a file that moves, in
//! every source importing it, and every import of a source that moves to
//! another directory. A rewritten address is the moved file's path relative to
//! the importer's new directory, `./` before it when it does not climb, as the
//! corpus writes them; its backslashes, quotes and control characters are
//! escaped as an address decodes them.

use alloc::vec::Vec;
use std::path::Component;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_dispatcher::named_path;
use gandr_surface_syntax::ByteSpan;

use crate::protocol::FileRename;

/// A path import a read text writes: where its address is written and the
/// address, its escapes decoded.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathImport
{
    /// The bytes between the address's quotes.
    pub addressed: ByteSpan,
    /// The address.
    pub address: String,
}

/// An address a move rewrites: the bytes between its quotes and what to write
/// there, escaped.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Readdressed
{
    /// The bytes between the address's quotes.
    pub addressed: ByteSpan,
    /// The address to write in their place, escaped.
    pub written: String,
}

/// One file or folder moving: where it is and where it goes, each named as
/// [`named_path`] names it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Move
{
    /// Where the file or folder is.
    from: PathBuf,
    /// Where it goes.
    to: PathBuf,
}

/// The files and folders a rename moves.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Moves(Vec<Move>);

impl Moves
{
    /// The moves `renames` names, each path a `file` URI's, named as
    /// [`named_path`] names it; a rename whose URIs name no path moves
    /// nothing.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn of(renames: &[FileRename]) -> Self
    {
        Self(
            renames
                .iter()
                .map(|rename| Move {
                    from: named_path(&rename.old_uri.path()),
                    to: named_path(&rename.new_uri.path()),
                })
                .filter(|moving| moving.from != moving.to)
                .collect(),
        )
    }

    /// Where the moves take `path`: the first move whose source is `path`
    /// or a folder holding it, with the rest of `path` under its destination.
    ///
    /// # Specification
    /// - requires: `path` is named as [`named_path`] names it.
    /// - ensures: none when no move's source is `path` or holds it; otherwise
    ///   the first such move's destination joined with what of `path` lies
    ///   under its source.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a file moved, a file under a folder moved, and a file
    ///   beside a moved one each land where stated.
    /// - witness: `relocate::tests::an_import_is_readdressed_as_its_file_and_its_source_move`
    #[spec(ensures: |ret| ret.is_none() || !self.0.is_empty())]
    #[must_use]
    pub fn moved(
        &self,
        path: &Path,
    ) -> Option<PathBuf>
    {
        self.0.iter().find_map(|moving| {
            path.strip_prefix(&moving.from).ok().map(|rest| {
                if rest.as_os_str().is_empty() {
                    moving.to.clone()
                }
                else {
                    moving.to.join(rest)
                }
            })
        })
    }

    /// The addresses the moves rewrite among `imports`, the path imports the
    /// source at `importer` writes.
    ///
    /// # Specification
    /// - requires: `importer` is named as [`named_path`] names it.
    /// - ensures: one entry per import whose file or whose importer moves and
    ///   whose address, relative to the importer's directory once moved, reads
    ///   otherwise than it does now, in the order `imports` lists them; none
    ///   for an import whose file and importer stay, or whose new address is
    ///   not a path in Unicode.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an import of a moved file, an import written by a
    ///   source moving to another directory, an import of a file moving with
    ///   its importer, an import of a file that stays and an address needing
    ///   escapes each answer as stated.
    /// - witness: `relocate::tests::an_import_is_readdressed_as_its_file_and_its_source_move`
    #[spec(ensures: |ret| ret.len() <= imports.len())]
    #[must_use]
    pub fn readdressed(
        &self,
        importer: &Path,
        imports: &[PathImport],
    ) -> Vec<Readdressed>
    {
        let directory = importer.parent().unwrap_or(importer);
        let moved_importer = self.moved(importer);
        let new_directory = moved_importer
            .as_deref()
            .and_then(Path::parent)
            .unwrap_or(directory);
        imports
            .iter()
            .filter_map(|import| {
                let target = named_path(&directory.join(&import.address));
                let moved_target = self.moved(&target);
                if moved_importer.is_none() && moved_target.is_none() {
                    return None;
                }
                let target = moved_target.unwrap_or(target);
                let address = relative(
                    new_directory,
                    &target,
                    Dotted(import.address.starts_with('.')),
                )?;
                (address != import.address).then(|| Readdressed {
                    addressed: import.addressed,
                    written: escaped(Unescaped(&address)),
                })
            })
            .collect()
    }
}

/// Whether an address is written with its leading `./` or `../`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Dotted(bool);

/// The address of `target` from `directory`: its path relative to the
/// directory, its components separated by `/`, `./` before it when it does not
/// climb and `dotted` says the address it replaces had one; none when no
/// relative path joins them or a component is not Unicode.
///
/// # Specification
/// trivial.
fn relative(
    directory: &Path,
    target: &Path,
    dotted: Dotted,
) -> Option<String>
{
    let path = pathdiff::diff_paths(target, directory)?;
    let mut parts: Vec<&str> = Vec::new();
    for component in path.components() {
        match component {
            Component::Normal(part) => parts.push(part.to_str()?),
            Component::ParentDir => parts.push(".."),
            Component::CurDir => {},
            Component::RootDir | Component::Prefix(_) => return None,
        }
    }
    let climbs = parts.first().is_some_and(|first| *first == "..");
    let joined = parts.join("/");
    Some(if dotted.0 && !climbs {
        format!("./{joined}")
    }
    else {
        joined
    })
}

/// An address as it reads, before escaping.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Unescaped<'address>(&'address str);

/// `address` as written between an import's quotes: each backslash, quote and
/// control character an address decodes escaped.
///
/// # Specification
/// trivial.
fn escaped(address: Unescaped<'_>) -> String
{
    let mut written = String::with_capacity(address.0.len());
    for character in address.0.chars() {
        match character {
            '\\' => written.push_str("\\\\"),
            '"' => written.push_str("\\\""),
            '\n' => written.push_str("\\n"),
            '\t' => written.push_str("\\t"),
            '\r' => written.push_str("\\r"),
            '\0' => written.push_str("\\0"),
            other => written.push(other),
        }
    }
    written
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;

    use super::Moves;
    use super::PathImport;
    use super::Readdressed;
    use crate::protocol::DocumentUri;
    use crate::protocol::FileRename;

    #[test]
    fn an_import_is_readdressed_as_its_file_and_its_source_move()
    {
        let directory = std::env::temp_dir().join(format!("gandr-relocate-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(directory.join("deeper")).expect("the scratch tree is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        for file in [
            "base.gandr",
            "stays.gandr",
            "deeper/mid.gandr",
            "deeper/beside.gandr",
        ] {
            std::fs::write(directory.join(file), "").expect("the source is written");
        }
        let at = |file: &str| directory.join(file);
        let uri = |file: &str| DocumentUri::of_path(&at(file)).expect("the path is a URI");
        let span = |start: usize| {
            ByteSpan::new(
                ByteOffset::from(start),
                ByteOffset::from(start.saturating_add(1)),
            )
            .expect("the span is ordered")
        };
        let import = |start: usize, address: &str| PathImport {
            addressed: span(start),
            address: String::from(address),
        };
        let renamed = |from: &str, to: &str| {
            Moves::of(&[FileRename {
                old_uri: uri(from),
                new_uri: uri(to),
            }])
        };
        let file_moved = renamed("base.gandr", "deeper/base.gandr");
        assert_eq!(
            file_moved.readdressed(&at("deeper/mid.gandr"), &[
                import(0, "../base.gandr"),
                import(10, "./beside.gandr"),
            ]),
            [Readdressed {
                addressed: span(0),
                written: String::from("./base.gandr"),
            }],
            "an import of the moved file follows it; one of a file that stays does not move"
        );
        let source_moved = renamed("deeper/mid.gandr", "mid.gandr");
        assert_eq!(
            source_moved.readdressed(&at("deeper/mid.gandr"), &[
                import(0, "../base.gandr"),
                import(10, "./beside.gandr"),
            ]),
            [
                Readdressed {
                    addressed: span(0),
                    written: String::from("./base.gandr"),
                },
                Readdressed {
                    addressed: span(10),
                    written: String::from("./deeper/beside.gandr"),
                },
            ],
            "a source moving to another directory rewrites every import it writes"
        );
        let folder_moved = renamed("deeper", "renamed");
        assert_eq!(
            folder_moved.moved(&at("deeper/mid.gandr")),
            Some(at("renamed/mid.gandr")),
            "a file under a moved folder moves with it"
        );
        assert_eq!(
            folder_moved.readdressed(&at("deeper/mid.gandr"), &[
                import(0, "../base.gandr"),
                import(10, "./beside.gandr"),
            ]),
            Vec::<Readdressed>::new(),
            "an import of a file moving with its importer reads as it did"
        );
        assert_eq!(
            folder_moved.readdressed(&at("stays.gandr"), &[import(0, "./deeper/mid.gandr")]),
            [Readdressed {
                addressed: span(0),
                written: String::from("./renamed/mid.gandr"),
            }],
            "an import of a file under a moved folder follows the folder"
        );
        assert_eq!(
            renamed("base.gandr", "odd\"name.gandr")
                .readdressed(&at("stays.gandr"), &[import(0, "base.gandr")]),
            [Readdressed {
                addressed: span(0),
                written: String::from("odd\\\"name.gandr"),
            }],
            "an address is written undotted as it was, its quote escaped"
        );
        assert_eq!(
            renamed("base.gandr", "elsewhere.gandr").moved(&at("stays.gandr")),
            None,
            "a file beside a moved one stays"
        );
        let _cleared = std::fs::remove_dir_all(&directory);
    }
}
