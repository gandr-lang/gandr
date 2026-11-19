//! The staged THIR that each `thir` mark of a source names, read before the
//! lowering runs.
//!
//! A `thir` mark gives a signature the body of a Rust function as its value.
//! The lowering runs no process. So the dispatcher reads each mark of a
//! source as it reads the source's imports, and it asks the record cache for
//! the function's body. A source holds the answer for each mark, and the
//! lowering reads the answer by the mark's file and path.
//!
//! The crate is one file beside the source, under the fixed command line
//! `--crate-type lib --edition 2024`. A process with no reader installed
//! stages nothing, and each mark is refused by name.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use std::ffi::OsString;
use std::path::Path;
use std::path::PathBuf;
use std::sync::OnceLock;

use gandr_runtime_rust_record::Answer;
use gandr_runtime_rust_record::Cache;
use gandr_runtime_rust_record::Function;
use gandr_runtime_rust_record::FunctionPath;
use gandr_runtime_rust_record::Identity;
use gandr_runtime_rust_record::Outcome;
use gandr_runtime_rust_record::Program;
use gandr_runtime_rust_record::Record;
use gandr_runtime_rust_record::Request;
use gandr_runtime_rust_record::Staging;
use gandr_surface_lowering::Staged;
use gandr_surface_lowering::Unstaged;
use gandr_surface_syntax::SourceText;

use crate::verdicts::AlreadyInstalled;

/// The stager this process installed.
// economy: one reader and one cache per process, read where each source's
// marks are read, as the hydration is read where each import resolves.
static INSTALLED: OnceLock<Stager> = OnceLock::new();

/// The text that opens a `thir` mark, before its tuple of two texts.
const MARK: &str = "@[thir((";

/// The command line of a crate of one file, before the file.
const COMMAND: [&str; 4] = ["--crate-type", "lib", "--edition", "2024"];

/// The reader of a Rust crate and the cache of its records.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Stager
{
    /// The cache, which a miss fills.
    cache: Cache,
    /// The reader, on the pinned toolchain's own libraries.
    program: Program,
}

impl Stager
{
    /// The stager that reads with the reader at `reader` and keeps each
    /// record in the directory `records`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        records: PathBuf,
        reader: PathBuf,
    ) -> Self
    {
        Self {
            cache: Cache::at(records),
            program: Program(reader),
        }
    }
}

/// Install `stager` for each source that this process reads after, unless
/// one is installed already, which stays.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`AlreadyInstalled`].
///
/// # Cost
/// - allocation: the installed stager, setup
#[inline]
pub fn install_stager(stager: Stager) -> Result<(), AlreadyInstalled>
{
    INSTALLED.set(stager).map_err(|_refused| AlreadyInstalled)
}

/// One `thir` mark as the text writes it: the Rust file and the path of the
/// function in that file.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Mark
{
    /// The Rust file, beside the source.
    file: Arc<str>,
    /// The function's path inside its crate.
    function: FunctionPath,
}

/// The answer for each `thir` mark that `text` writes, its file read beside
/// `directory`, in the order that `text` writes the marks.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one answer for each mark whose two texts hold no escape. The
///   marks of one file make one request, which holds each function that they
///   name, so a body may call another marked function of its file. With no
///   stager installed, each answer is [`Unstaged::NoReader`].
/// - panics: none.
/// - executable: none — each answer comes from a process and a cache, which no
///   predicate reads.
///
/// # Adequacy
/// - hypothesis: L3 — with no stager installed, each mark with no escape is
///   answered in written order, across two files, and a mark with an escape
///   takes no answer.
/// - witness: `thir::tests::with_no_stager_each_mark_is_answered_in_order`
///
/// # Cost
/// - allocation: each mark's texts and its answer, growth within the marks of
///   the source
/// - allocation: each file's request and record, growth within the files of the
///   source
pub fn staged(
    text: SourceText<'_>,
    directory: &Path,
) -> Vec<Staged>
{
    let written = marks(text);
    let mut requests: BTreeMap<&str, (&Mark, BTreeSet<FunctionPath>)> = BTreeMap::new();
    for mark in &written {
        let _new = requests
            .entry(mark.file.as_ref())
            .or_insert_with(|| (mark, BTreeSet::new()))
            .1
            .insert(mark.function.clone());
    }
    let reads: BTreeMap<&str, Result<BTreeMap<FunctionPath, Staging>, Unstaged>> = requests
        .into_iter()
        .map(|(file, (mark, functions))| {
            let bodies = read(directory, mark, functions.into_iter().collect())
                .map(|read| read.into_iter().map(|one| (one.path, one.body)).collect());
            (file, bodies)
        })
        .collect();
    written
        .iter()
        .map(|mark| {
            let staging = match reads.get(mark.file.as_ref()) {
                Some(&Ok(ref bodies)) => bodies.get(&mark.function).cloned().ok_or_else(|| {
                    Unstaged::Unread(Arc::from("the record holds no such function"))
                }),
                Some(&Err(ref unstaged)) => Err(unstaged.clone()),
                None => Err(Unstaged::NoReader),
            };
            Staged {
                file: Arc::clone(&mark.file),
                function: mark.function.clone(),
                staging,
            }
        })
        .collect()
}

/// Each mark's file and function, in the order that `text` writes them. A
/// mark whose texts hold an escape is left out.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: each mark's two texts, growth within the marks of the source
// economy: a scan of the text, as `paths_formed` reads the import forms. A
// mark inside a comment stages too, and the lowering reads only the marks
// that it collects.
fn marks(text: SourceText<'_>) -> Vec<Mark>
{
    // The text of the string literal at the start of `rest`, past its
    // whitespace, and the bytes after it; none for a literal with an escape.
    let quoted: fn(&str) -> Option<(&str, &str)> = |rest| {
        let open = rest.trim_start().strip_prefix('"')?;
        let (inner, after) = open.split_once('"')?;
        (!inner.contains('\\')).then_some((inner, after))
    };
    let source = text.as_ref();
    source
        .match_indices(MARK)
        .filter_map(|(at, _)| {
            let rest = source.get(at.saturating_add(MARK.len()) ..)?;
            let (file, rest) = quoted(rest)?;
            let rest = rest.trim_start().strip_prefix(',')?;
            let (function, rest) = quoted(rest)?;
            rest.trim_start().strip_prefix(')')?;
            Some(Mark {
                file: Arc::from(file),
                function: FunctionPath::from(function),
            })
        })
        .collect()
}

/// The functions `functions` of the file of `mark`, read beside `directory`
/// in one request.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Unstaged::NoReader`] with no stager installed, and the cause that the
/// cache or the record states otherwise.
///
/// # Cost
/// - allocation: the request and the record, growth within the files of the
///   source
fn read(
    directory: &Path,
    mark: &Mark,
    functions: Vec<FunctionPath>,
) -> Result<Vec<Function>, Unstaged>
{
    let Some(stager) = INSTALLED.get()
    else {
        return Err(Unstaged::NoReader);
    };
    let mut arguments: Vec<OsString> = COMMAND.iter().map(OsString::from).collect();
    arguments.push(directory.join(&*mark.file).into_os_string());
    let request = Request {
        arguments,
        functions,
    };
    match stager
        .cache
        .read(&stager.program, &request, &Identity::of_build())
    {
        Err(unread) => Err(Unstaged::Unread(Arc::from(unread.to_string()))),
        Ok(Answer {
            record:
                Record {
                    outcome: Outcome::Read(read),
                    ..
                },
            ..
        }) => Ok(read),
        Ok(Answer {
            record:
                Record {
                    outcome: Outcome::Refused(refusals),
                    ..
                },
            ..
        }) => Err(Unstaged::Refused(Arc::from(
            refusals
                .first()
                .map_or_else(String::new, |refusal| alloc::format!("{refusal:?}")),
        ))),
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;
    use std::path::Path;

    use gandr_surface_lowering::Unstaged;
    use gandr_surface_syntax::SourceText;

    use super::staged;

    #[test]
    fn with_no_stager_each_mark_is_answered_in_order()
    {
        let text = SourceText::from(include_str!(
            "thir/unformatted/with-no-stager-each-mark-is-answered-in-order.gandr"
        ));
        let answers = staged(text, Path::new("."));
        let read: Vec<_> = answers
            .iter()
            .map(|one| {
                (
                    one.file.as_ref(),
                    one.function.as_ref(),
                    one.staging.clone(),
                )
            })
            .collect();
        assert_eq!(
            read,
            Vec::from([
                ("a.rs", "f", Err(Unstaged::NoReader)),
                ("b.rs", "h", Err(Unstaged::NoReader)),
                ("a.rs", "k", Err(Unstaged::NoReader)),
            ])
        );
    }
}
