//! The parse cache: each passage's parse, kept by the digest of its text.
//!
//! A passage that a host parsed once is never parsed again where the cache
//! stands. The cache's directory names the model and the parse script, so a
//! new model or a changed script starts a new cache. A rule that changes reads
//! the kept parse again, and no passage parses for it.
//!
//! A read that fails is a miss, and the passage parses again. A write that
//! fails leaves the entry out, and the next run parses the passage again. So a
//! missing or a damaged cache costs a parse and never a refusal. An entry is
//! written beside its place and then renamed onto it, so a reader sees a whole
//! entry or none.

use std::fs;
use std::path::Path;
use std::path::PathBuf;

use quenchant_shape::shape::Maybe;

use crate::digest::Digest;

/// The name of the model whose parses a cache keeps: the parser's version and
/// the model's.
///
/// # Specification
/// - provides: half of the cache directory's name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Model<'name>(pub &'name str);

/// The text of the parse script, whose digest names the cache beside the
/// model.
///
/// # Specification
/// - provides: the other half of the cache directory's name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Script<'text>(pub &'text [u8]);

/// One passage's parse as the script prints it: JSON text.
///
/// # Specification
/// - provides: what an entry holds.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Kept(pub String);

/// Why the cache gives no parse for a digest.
///
/// # Specification
/// - provides: the miss a read answers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Missed
{
    /// No entry stands for the digest, or its file cannot be read.
    Absent,
}

/// What a write did.
///
/// # Specification
/// - provides: the count of parses a run could not keep.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Keeping
{
    /// The entry stands.
    Kept,
    /// The directory or the file could not be written; the next run parses
    /// the passage again.
    Unwritten,
    /// The run named no cache, so nothing is kept.
    Unasked,
}

/// The parses of one model and one parse script, by passage digest.
///
/// # Specification
/// - provides: the parse a run reads in place of a parse, and the place it
///   keeps a new one.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cache
{
    /// The directory of this model's and this script's entries; none for a
    /// run that names no cache.
    dir: Option<PathBuf>,
}

impl Cache
{
    /// The cache under `root` for the parses of `model` by `script`.
    ///
    /// # Specification
    /// - requires: nothing; the directory need not exist.
    /// - ensures: the directory is `root`, then the model's name with each
    ///   character outside letters, digits, `.`, `-`, `+` and `_` written as
    ///   `_`, then the first sixteen hexadecimal digits of the script's digest.
    /// - provides: one cache for each model and script.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — a path, no predicate compares.
    ///
    /// # Cost
    /// - allocation: the directory's name and path, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two scripts give two caches, and a parse kept under
    ///   one is a miss under the other; a name that drops the script shares a
    ///   stale parse.
    /// - witness: `cache::tests::a_kept_parse_is_read_back_and_another_script_misses_it`
    #[inline]
    #[must_use]
    pub fn under(
        root: &Path,
        model: Model<'_>,
        script: Script<'_>,
    ) -> Self
    {
        let named: String = model
            .0
            .chars()
            .map(|character| {
                if character.is_ascii_alphanumeric() || matches!(character, '.' | '-' | '+' | '_') {
                    character
                }
                else {
                    '_'
                }
            })
            .collect();
        let script = blake3::hash(script.0).to_hex();
        Self {
            dir: Some(
                root.join(named)
                    .join(script.as_str().get(.. 16).unwrap_or_default()),
            ),
        }
    }

    /// The cache of a run that names none: every read misses, and nothing is
    /// kept.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run with no cache parses every passage; a kept
    ///   parse read back changes the marks of the fake interpreter.
    /// - witness: `tests::cli::a_second_run_reads_every_parse_from_the_cache`
    #[inline]
    #[must_use]
    pub const fn none() -> Self
    {
        Self { dir: None }
    }

    /// The file of the entry for `digest`: a directory for its first two
    /// digits, then the digest.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the entry's name and path, growth within the digest
    fn entry(
        &self,
        digest: Digest,
    ) -> Option<PathBuf>
    {
        let name = digest.to_string();
        self.dir
            .as_ref()
            .map(|dir| dir.join(name.get(.. 2).unwrap_or_default()).join(&name))
    }

    /// The parse kept for `digest`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the text of the entry for `digest` when its file reads;
    ///   [`Missed::Absent`] otherwise, and for a run that names no cache.
    /// - provides: the read that saves a parse.
    /// - fails: never; a failed read is a miss.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Cost
    /// - allocation: the entry's path and text, growth within the kept parse
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Cache::under`].
    /// - witness: `cache::tests::a_kept_parse_is_read_back_and_another_script_misses_it`
    #[inline]
    pub fn read(
        &self,
        digest: Digest,
    ) -> Maybe<Kept, Missed>
    {
        self.entry(digest)
            .and_then(|path| fs::read_to_string(path).ok())
            .map_or(Maybe::Absent(Missed::Absent), |text| {
                Maybe::Present(Kept(text))
            })
    }

    /// Keep `parse` for `digest`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on [`Keeping::Kept`], the entry for `digest` holds `parse`
    ///   whole; the file is written beside its place and renamed onto it. A run
    ///   that names no cache keeps nothing and answers [`Keeping::Unasked`].
    /// - provides: the write a later run reads in place of a parse.
    /// - fails: never; a failed write is [`Keeping::Unwritten`].
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Cost
    /// - allocation: the entry's path and the partial file's name, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Cache::under`]; a write under a file that blocks
    ///   the directory is unwritten and reads back as a miss.
    /// - witness: `cache::tests::a_kept_parse_is_read_back_and_another_script_misses_it`
    /// - witness: `cache::tests::an_unwritable_cache_misses_and_refuses_nothing`
    #[inline]
    pub fn keep(
        &self,
        digest: Digest,
        parse: &Kept,
    ) -> Keeping
    {
        let Some(path) = self.entry(digest)
        else {
            return Keeping::Unasked;
        };
        let partial = path.with_extension(format!("part{}", std::process::id()));
        let written = path
            .parent()
            .map_or(Ok(()), fs::create_dir_all)
            .and_then(|()| fs::write(&partial, parse.0.as_bytes()))
            .and_then(|()| fs::rename(&partial, &path));
        if written.is_ok() {
            Keeping::Kept
        }
        else {
            drop(fs::remove_file(&partial));
            Keeping::Unwritten
        }
    }
}

#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::Cache;
    use super::Keeping;
    use super::Kept;
    use super::Missed;
    use super::Model;
    use super::Script;
    use crate::digest::Digest;
    use crate::passage::Text;

    #[test]
    fn a_kept_parse_is_read_back_and_another_script_misses_it()
    {
        let root = std::env::temp_dir().join(format!("prose-cache-{}", std::process::id()));
        let cache = Cache::under(&root, Model("spacy 3/model"), Script(b"parse"));
        let other = Cache::under(&root, Model("spacy 3/model"), Script(b"parse again"));
        let digest = Digest::of(Text("The check reads what a change wrote."));
        assert_eq!(cache.read(digest), Maybe::Absent(Missed::Absent));
        let parse = Kept(String::from("[[[\"The\"]]]"));
        assert_eq!(cache.keep(digest, &parse), Keeping::Kept);
        assert_eq!(cache.read(digest), Maybe::Present(parse));
        assert_eq!(other.read(digest), Maybe::Absent(Missed::Absent));
        assert!(root.join("spacy_3_model").is_dir());
        drop(std::fs::remove_dir_all(&root));
    }

    #[test]
    fn an_unwritable_cache_misses_and_refuses_nothing()
    {
        let blocker = std::env::temp_dir().join(format!("prose-cache-file-{}", std::process::id()));
        std::fs::write(&blocker, b"a file where the cache's directory stands")
            .expect("the scratch file writes");
        let cache = Cache::under(&blocker, Model("model"), Script(b"parse"));
        let digest = Digest::of(Text("A sentence."));
        assert_eq!(
            cache.keep(digest, &Kept(String::from("[]"))),
            Keeping::Unwritten
        );
        assert_eq!(cache.read(digest), Maybe::Absent(Missed::Absent));
        drop(std::fs::remove_file(&blocker));
    }
}
