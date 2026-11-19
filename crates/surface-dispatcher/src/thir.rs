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

use alloc::sync::Arc;
use std::ffi::OsString;
use std::path::Path;
use std::sync::OnceLock;

use gandr_runtime_rust_record::Answer;
use gandr_runtime_rust_record::Cache;
use gandr_runtime_rust_record::FunctionPath;
use gandr_runtime_rust_record::Identity;
use gandr_runtime_rust_record::Outcome;
use gandr_runtime_rust_record::Program;
use gandr_runtime_rust_record::Record;
use gandr_runtime_rust_record::Request;
use gandr_surface_lowering::Staged;
use gandr_surface_lowering::Unstaged;
use gandr_surface_syntax::SourceText;

use crate::verdicts::AlreadyInstalled;

/// The stager this process installed.
// economy: one reader and one cache per process, read where each source's
// marks are read, as the hydration is read where each import resolves.
static INSTALLED: OnceLock<Stager> = OnceLock::new();

/// The text that opens a `thir` mark, before its two texts.
const MARK: &str = "@[thir(";

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
    /// The stager that reads with `program` and keeps each record in `cache`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        cache: Cache,
        program: Program,
    ) -> Self
    {
        Self { cache, program }
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
#[inline]
pub fn install_stager(stager: Stager) -> Result<(), AlreadyInstalled>
{
    INSTALLED.set(stager).map_err(|_refused| AlreadyInstalled)
}

/// The answer for each `thir` mark that `text` writes, its file read beside
/// `directory`, in the order that `text` writes the marks.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one answer for each mark whose two texts hold no escape. With no
///   stager installed, each answer is [`Unstaged::NoReader`].
/// - panics: none.
///
/// # Cost
/// - allocation: each mark's texts and its answer, growth within the marks of
///   the source
pub(crate) fn staged(
    text: SourceText<'_>,
    directory: &Path,
) -> Vec<Staged>
{
    marks(text)
        .into_iter()
        .map(|(file, function)| stage(directory, file, function))
        .collect()
}

/// Each mark's file and function, in the order that `text` writes them.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: each mark's two texts, growth within the marks of the source
// economy: a scan of the text, as `paths_formed` reads the import forms. A
// mark inside a comment stages too, and the lowering reads only the marks
// that it collects.
fn marks(text: SourceText<'_>) -> Vec<(Arc<str>, FunctionPath)>
{
    let source = text.as_ref();
    source
        .match_indices(MARK)
        .filter_map(|(at, _)| {
            let rest = source.get(at.saturating_add(MARK.len()) ..)?;
            let (file, rest) = quoted(rest)?;
            let rest = rest.trim_start().strip_prefix(',')?;
            let (function, rest) = quoted(rest)?;
            rest.trim_start().strip_prefix(')')?;
            Some((Arc::from(file), FunctionPath::from(function)))
        })
        .collect()
}

/// The text of the string literal at the start of `rest`, past its
/// whitespace, and the bytes after it; none for a literal with an escape.
///
/// # Specification
/// trivial.
fn quoted(rest: &str) -> Option<(&str, &str)>
{
    let open = rest.trim_start().strip_prefix('"')?;
    let (inner, after) = open.split_once('"')?;
    if inner.contains('\\') {
        return None;
    }
    Some((inner, after))
}

/// The answer for the mark that names `function` of `file`.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the request and the answer, growth within the marks of the
///   source
fn stage(
    directory: &Path,
    file: Arc<str>,
    function: FunctionPath,
) -> Staged
{
    let staging = match INSTALLED.get() {
        None => Err(Unstaged::NoReader),
        Some(stager) => {
            let mut arguments: Vec<OsString> = COMMAND.iter().map(OsString::from).collect();
            arguments.push(directory.join(&*file).into_os_string());
            let request = Request {
                arguments,
                functions: Vec::from([function.clone()]),
            };
            match stager
                .cache
                .read(&stager.program, &request, &Identity::of_build())
            {
                Err(unread) => Err(Unstaged::Unread(Arc::from(unread.to_string()))),
                Ok(Answer {
                    record:
                        Record {
                            outcome: Outcome::Read(functions),
                            ..
                        },
                    ..
                }) => functions
                    .into_iter()
                    .next()
                    .map(|read| read.body)
                    .ok_or_else(|| Unstaged::Unread(Arc::from("the record holds no function"))),
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
        },
    };
    Staged {
        file,
        function,
        staging,
    }
}
