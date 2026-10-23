//! The format verb: a verb's paths, read, laid out and rewritten in order.
//!
//! # The walk's paths, the formatter's layout
//!
//! [`Formatting`] reaches its sources exactly as the walk does — each path in
//! order, a directory depth-first in byte order, every path answering with a
//! source or a fault — and hands each source to `gandr-surface-format`. A
//! source the formatter refuses is a fault and stays as written; the
//! formatting continues past it, so one run reports every source it could
//! not lay out.
//!
//! # A source is written only when its layout changes
//!
//! Under [`Rewrite::InPlace`] a source whose formatted text differs from its
//! own is written back over it; a source already in the formatter's layout is
//! not touched. Under [`Rewrite::Check`] nothing is written.
//!
//! # Sources fork; steps keep walk order
//!
//! [`Formatting::visit`] at a width above one lays the sources out on a pool,
//! largest first, and hands the steps over in walk order once every source
//! is laid out, so every step is the serial formatting's at every width.
//!
//! # The format verb lays out what a walk reaches
//!
//! `Formatting::step` reaches the paths it was given through the walk's own
//! traversal — the same order, the same skipped links, the same fault for a
//! path naming no source — so `gandr fmt` and `gandr check` over the same paths
//! visit the same sources. Each source is read, parsed, and laid out by
//! `gandr-surface-format` at the invocation's page; a source whose formatted
//! text is its own is `FormatStep::Unchanged` and is never written, and one
//! whose text differs is `FormatStep::Changed`, written back over the source
//! first under `Rewrite::InPlace` and left untouched under `Rewrite::Check`. A
//! source the formatter refuses, or the parse cannot commit, is a `FormatFault`
//! and stays as written; the formatting continues past it.
//!
//! `Formatting::visit` forks by source on the driver's [`Pool`], as
//! `Walk::visit` does: at a width above one it reaches every path first, then
//! lays the sources out on the pool's threads and the calling thread, largest
//! first, and hands the steps over in walk order, so every byte the driver
//! prints, every source rewritten and the exit are the serial formatting's. A
//! source's text lives only on the thread laying it out; what
//! the calling thread holds is each path and whether its layout changed. The
//! serial formatting costs a parse, a layout and the formatter's own reparse
//! per source; forked, `fmt --check` takes what `check` takes at the default
//! width. The alternative was the stepped formatting alone, which streams but
//! leaves the formatter several times slower than the checker on the same tree;
//! it reverses if a caller needs a source's line printed before the next is
//! laid out. The formatted text is written through the formatting's
//! [`Reader`], as it was read: a source below the reader's crossover is
//! rewritten in place, keeping its permissions and hard links, and a write
//! interrupted midway leaves it truncated; one the reader may map is written
//! beside the mapping and renamed over it ([`Reader::write`]).

use core::cmp::Reverse;
use core::num::NonZeroUsize;
use core::ops::ControlFlow;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::path::Path;
use std::path::PathBuf;
use std::sync::OnceLock;

use anodized::spec;
use gandr_surface_format::Beside;
use gandr_surface_format::FormatError;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::Withdrawal;
use gandr_surface_format::format_beside;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::MeldError;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::component;
use crate::pool::Pool;
use crate::reader::Reader;
use crate::root;
use crate::walk::Reached;
use crate::walk::Traversal;
use crate::walk::walk_step;
use crate::width::Width;

/// What the format verb does with a source whose layout changes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rewrite
{
    /// Write the formatted text back over the source.
    InPlace,
    /// Write nothing; report the source alone.
    Check,
}

/// Why a path could not be laid out.
#[derive(Debug)]
pub enum FormatFault<'formatting>
{
    /// The path could not be listed or read, or its text is not UTF-8.
    Unreadable(std::io::Error),
    /// The path names no source: a directory holding no `.gandr` file.
    NoSource,
    /// The built-in grammar did not build, so no source can be parsed.
    Grammar(&'formatting PbgError),
    /// The parse could not commit a tree.
    Parse(MeldError),
    /// The formatter refused the source; it stays as written.
    Refused(FormatError),
    /// The formatted text could not be written back.
    Unwritable(std::io::Error),
}

impl core::fmt::Display for FormatFault<'_>
{
    /// Writes the fault and what it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Unreadable(ref error) => write!(f, "unreadable: {error}"),
            Self::NoSource => f.write_str("names no `.gandr` source"),
            Self::Grammar(error) => write!(f, "the built-in grammar did not build: {error}"),
            Self::Parse(ref error) => write!(f, "the parse did not commit: {error}"),
            Self::Refused(ref error) => write!(f, "not formatted: {error}"),
            Self::Unwritable(ref error) => write!(f, "cannot write the formatted text: {error}"),
        }
    }
}

/// One step of a formatting.
#[derive(Debug)]
pub enum FormatStep<'formatting>
{
    /// A source already in the formatter's layout.
    Unchanged
    {
        /// The source's path, as the formatting reached it.
        path: &'formatting Path,
        /// Each declaration that kept the source's spelling, and why.
        withdrawn: Vec<Kept>,
    },
    /// A source whose layout the formatter changes: written back under
    /// [`Rewrite::InPlace`], reported alone under [`Rewrite::Check`].
    Changed
    {
        /// The source's path, as the formatting reached it.
        path: &'formatting Path,
        /// Each declaration that kept the source's spelling, and why.
        withdrawn: Vec<Kept>,
    },
    /// A path the formatting could not lay out.
    Fault
    {
        /// The path, as the formatting reached it.
        path: &'formatting Path,
        /// Why.
        fault: FormatFault<'formatting>,
    },
}

/// A declaration the formatter left in the source's spelling because a
/// rewrite would have changed what it lowers to, where the source writes it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Kept
{
    /// The declaration, its span and the reason.
    pub withdrawal: Withdrawal,
    /// The one-based line its introducing form starts on.
    pub line: usize,
    /// The one-based column, in characters, its introducing form starts at.
    pub column: usize,
}

impl Kept
{
    /// `withdrawal`, located in `text`, the source it was found in.
    ///
    /// # Specification
    /// trivial.
    fn located(
        withdrawal: Withdrawal,
        text: SourceText<'_>,
    ) -> Self
    {
        let before = text
            .as_ref()
            .get(.. usize::from(withdrawal.span.start()))
            .unwrap_or_default();
        let line_start = before.rfind('\n').map_or(0, |at| at.saturating_add(1));
        Self {
            line: before.matches('\n').count().saturating_add(1),
            column: before
                .get(line_start ..)
                .unwrap_or_default()
                .chars()
                .count()
                .saturating_add(1),
            withdrawal,
        }
    }
}

impl core::fmt::Display for Kept
{
    /// The line and column, the declaration's name in backticks, then
    /// `keeps its spelling: ` and the reason.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(
            f,
            "{}:{}: `{}` keeps its spelling: {}",
            self.line, self.column, self.withdrawal.declaration, self.withdrawal.reason
        )
    }
}

/// The format verb over the paths it was given, laying out its sources in
/// order.
#[derive(Debug)]
pub struct Formatting
{
    /// The grammar every source is parsed under, built once per formatting.
    grammar: Result<Pbg, PbgError>,
    /// Where the formatting is among the paths it was given.
    traversal: Traversal,
    /// The page every source is laid out at.
    options: FormatOptions,
    /// What a changed source becomes.
    rewrite: Rewrite,
    /// The threads [`Formatting::visit`] lays sources out on.
    width: Width,
    /// What every source is read and written back through.
    reader: Reader,
}

impl Formatting
{
    /// A formatting of `paths`, in the order given, at `options` and
    /// `width`, nothing yet read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        paths: Vec<PathBuf>,
        options: FormatOptions,
        rewrite: Rewrite,
        width: Width,
    ) -> Self
    {
        Self {
            grammar: built_in(),
            traversal: Traversal::new(paths),
            options,
            rewrite,
            width,
            reader: Reader::new(),
        }
    }

    /// The threads [`Formatting::visit`] lays sources out on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn width(&self) -> Width
    {
        self.width
    }

    /// What a changed source becomes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rewrite(&self) -> Rewrite
    {
        self.rewrite
    }

    /// The page every source is laid out at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn options(&self) -> FormatOptions
    {
        self.options
    }

    /// The next source or fault of the formatting.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each path given is reached in order, as [`crate::Walk`]
    ///   reaches it. Each source is read, parsed and formatted at the
    ///   formatting's page; a source whose formatted text is its own is
    ///   [`FormatStep::Unchanged`], and one whose text differs is
    ///   [`FormatStep::Changed`], written back over the source under
    ///   [`Rewrite::InPlace`] first and left untouched under
    ///   [`Rewrite::Check`]. A path that cannot be listed or read, names no
    ///   source, fails to parse, is refused by the formatter or cannot be
    ///   written back is a [`FormatStep::Fault`], and its source stays as
    ///   written. Under [`Rewrite::Check`] no step is
    ///   [`FormatFault::Unwritable`]. Exhaustion is stable.
    /// - provides: the one pass `gandr fmt` renders.
    /// - fails: never; every fault is a step, and the formatting continues past
    ///   it.
    /// - panics: none.
    /// - intension: lays out one source's text and its formatted text at a
    ///   time; the reader holds the text of each source left unchanged until
    ///   the formatting is dropped.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree holding a source out of layout, one in it, a
    ///   nested source, an empty directory and a missing path yields exact
    ///   ordered rows under both rewrites; the files' bytes after each pass
    ///   distinguish writing under check, writing an unchanged source and a
    ///   lost write. A second in-place pass is all unchanged. Formatter
    ///   refusals and unwritable files are outside these fixtures.
    /// - witness: `format::tests::a_tree_is_formatted_in_place_once`
    /// - witness: `format::tests::checking_writes_nothing`
    #[inline]
    #[spec(
        captures: [checking = self.rewrite == Rewrite::Check],
        ensures: |ref ret| !(checking && matches!(*ret,
            Maybe::Present(FormatStep::Fault { fault: FormatFault::Unwritable(_), .. }))),
    )]
    pub fn step(&mut self) -> Maybe<FormatStep<'_>, walk_step::Absent>
    {
        let reached = match self.traversal.reach() {
            Maybe::Absent(absent) => return Maybe::Absent(absent),
            Maybe::Present(reached) => reached,
        };
        let path = self.traversal.path();
        let (grammar, options, rewrite) = (self.grammar.as_ref(), self.options, self.rewrite);
        Maybe::Present(step_of(path, reached, || {
            lay_out(&self.reader, path, grammar, options, rewrite)
        }))
    }

    /// Hand every step of the formatting to `visitor`, in walk order, laying
    /// the sources out on `pool`, and answer the first `Break` `visitor`
    /// returns.
    ///
    /// # Specification
    /// - requires: `pool` is the driver's, at the formatting's width.
    /// - ensures: `visitor` receives exactly the steps [`Formatting::step`]
    ///   yields, in its order, and every source is read, laid out and written
    ///   as [`Formatting::step`] does. [`Width::SERIAL`], or a grammar that did
    ///   not build, steps the formatting itself, so a `Break` stops it before
    ///   the next source is read. Any other width first reaches every path;
    ///   then the calling thread and the helpers [`Pool`] gives the fork, never
    ///   more than the sources, lay the sources out, each taking the largest
    ///   source by bytes none has taken, and only then are the steps handed
    ///   over in walk order, so a `Break` stops the handing over and every
    ///   source has already been laid out. A pool the host refused lays every
    ///   source out on the calling thread.
    /// - provides: the pass `gandr fmt` runs, at the width the driver chose.
    /// - fails: never; every fault is a step.
    /// - panics: only by propagating a panic of `visitor` or of a pool thread,
    ///   once every helper has stopped.
    /// - executable: none — the steps are handed to an opaque visitor and the
    ///   effect is on files; the witnesses compare both against the serial
    ///   formatting.
    /// - intension: the serial formatting lays out one source at a time; a
    ///   wider one holds every path reached and each source's outcome. The
    ///   reader holds the text of each source left unchanged until the
    ///   formatting is dropped, and of no source it wrote.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree holding sources in and out of layout, nested
    ///   sources, an empty directory and a missing path yields the same rows
    ///   and the same bytes on disk at widths one and three, under both
    ///   rewrites. Thread interleavings beyond those runs are outside the
    ///   witnesses.
    /// - witness: `format::tests::a_tree_is_formatted_in_place_once`
    /// - witness: `format::tests::checking_writes_nothing`
    #[inline]
    pub fn visit<Stop, Visitor>(
        mut self,
        pool: &Pool,
        mut visitor: Visitor,
    ) -> ControlFlow<Stop>
    where
        Visitor: FnMut(FormatStep<'_>) -> ControlFlow<Stop>,
    {
        let grammar = match self.grammar {
            Ok(ref grammar) if self.width != Width::SERIAL => grammar,
            Ok(_) | Err(_) => {
                while let Maybe::Present(step) = self.step() {
                    visitor(step)?;
                }
                return ControlFlow::Continue(());
            },
        };
        let mut paths = Vec::new();
        let mut found = Vec::new();
        while let Maybe::Present(reached) = self.traversal.reach() {
            paths.push(self.traversal.take_path());
            found.push(reached);
        }
        let laid: Vec<OnceLock<Result<Laid, FormatFault<'_>>>> =
            paths.iter().map(|_| OnceLock::new()).collect();
        let mut order: Vec<(Reverse<u64>, usize)> = paths
            .iter()
            .zip(&found)
            .enumerate()
            .filter(|&(_, (_, reached))| matches!(*reached, Reached::Source))
            .map(|(position, (path, _))| {
                let bytes = std::fs::metadata(path).map_or(0, |metadata| metadata.len());
                (Reverse(bytes), position)
            })
            .collect();
        order.sort_unstable();
        let cursor = AtomicUsize::new(0);
        let (options, rewrite) = (self.options, self.rewrite);
        // Lay out the largest source no thread has taken, until none is left.
        let work = || {
            while let Some(&(_, position)) = order.get(cursor.fetch_add(1, Ordering::Relaxed)) {
                if let (Some(path), Some(slot)) = (paths.get(position), laid.get(position)) {
                    let _first =
                        slot.set(lay_out(&self.reader, path, Ok(grammar), options, rewrite));
                }
            }
        };
        match pool.helpers(&order) {
            Maybe::Present((threads, helpers)) => threads.in_place_scope(|scope| {
                for _ in 0 .. NonZeroUsize::from(helpers).get() {
                    scope.spawn(|_| work());
                }
                work();
            }),
            Maybe::Absent(_) => work(),
        }
        for ((path, reached), slot) in paths.iter().zip(found).zip(laid) {
            let step = step_of(path, reached, || {
                slot.into_inner()
                    .unwrap_or_else(|| lay_out(&self.reader, path, Ok(grammar), options, rewrite))
            });
            visitor(step)?;
        }
        ControlFlow::Continue(())
    }
}

/// The step a path the traversal reached as `reached` makes, a source being
/// what `lay` makes of it.
///
/// # Specification
/// trivial.
fn step_of<'step, Lay>(
    path: &'step Path,
    reached: Reached,
    lay: Lay,
) -> FormatStep<'step>
where
    Lay: FnOnce() -> Result<Laid, FormatFault<'step>>,
{
    let fault = match reached {
        Reached::Source => match lay() {
            Ok(Laid::Unchanged(withdrawn)) => return FormatStep::Unchanged { path, withdrawn },
            Ok(Laid::Changed(withdrawn)) => return FormatStep::Changed { path, withdrawn },
            Err(fault) => fault,
        },
        Reached::Unreadable(error) => FormatFault::Unreadable(error),
        Reached::NoSource => FormatFault::NoSource,
    };
    FormatStep::Fault { path, fault }
}

/// Whether a source's layout changed, beside the declarations that kept
/// their spelling.
#[derive(Debug, Eq, PartialEq)]
enum Laid
{
    /// The formatted text is the source's own.
    Unchanged(Vec<Kept>),
    /// The formatted text differs from the source's.
    Changed(Vec<Kept>),
}

/// Read the source at `path` through `reader`, format it under `grammar` at
/// `options`, and under [`Rewrite::InPlace`] write a changed layout back
/// through `reader`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the answer is whether the source's formatted text differs from
///   its own. Only a changed layout under [`Rewrite::InPlace`] writes, only to
///   `path`, and through [`Reader::write`], so no mapping of the source faults.
/// - fails: a read, grammar, parse, formatter or write fault.
/// - panics: none.
///
/// # Errors
/// The [`FormatFault`] that stopped the source.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Formatting::step`]: changed and unchanged sources
///   under both rewrites, observed by their bytes after the pass, and a mapped
///   source rewritten while its mapping is held.
/// - witness: `format::tests::a_tree_is_formatted_in_place_once`
/// - witness: `format::tests::checking_writes_nothing`
/// - witness: `format::tests::a_mapped_source_is_formatted_in_place`
#[spec(ensures: |ref ret| !(rewrite == Rewrite::Check
    && matches!(*ret, Err(FormatFault::Unwritable(_)))))]
fn lay_out<'formatting>(
    reader: &Reader,
    path: &Path,
    grammar: Result<&'formatting Pbg, &'formatting PbgError>,
    options: FormatOptions,
    rewrite: Rewrite,
) -> Result<Laid, FormatFault<'formatting>>
{
    let read = reader.read(path).map_err(FormatFault::Unreadable)?;
    let text = read.text();
    let grammar = grammar.map_err(FormatFault::Grammar)?;
    let parsed = parse(grammar, text).map_err(FormatFault::Parse)?;
    let closure = component::lay_out(grammar, path, root::classify(path), text);
    let beside = match closure {
        Maybe::Present(ref laid) => Beside::Imports {
            before: SourceText::from(laid.text.get(.. usize::from(laid.base)).unwrap_or_default()),
            unit: &laid.unit,
        },
        Maybe::Absent(_) => Beside::Alone,
    };
    let formatted = format_beside(
        grammar,
        &parsed,
        options,
        (beside, Some(&crate::compose::Elaborating)),
    )
    .map_err(FormatFault::Refused)?;
    let withdrawn = formatted
        .withdrawn()
        .iter()
        .map(|withdrawal| Kept::located(withdrawal.clone(), text))
        .collect();
    let laid = <&str>::from(formatted.text());
    if laid == text.as_ref() {
        return Ok(Laid::Unchanged(withdrawn));
    }
    if rewrite == Rewrite::InPlace {
        reader
            .write(path, SourceText::from(laid))
            .map_err(FormatFault::Unwritable)?;
    }
    Ok(Laid::Changed(withdrawn))
}

#[cfg(test)]
mod tests
{
    use core::convert::Infallible;
    use core::num::NonZeroUsize;
    use core::ops::ControlFlow;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_format::FormatOptions;
    use gandr_surface_syntax::SourceText;

    use super::FormatFault;
    use super::FormatStep;
    use super::Formatting;
    use super::Rewrite;
    use crate::pool::Pool;
    use crate::reader::Reader;
    use crate::walk::tests::Scratch;
    use crate::width::Threads;
    use crate::width::Width;

    /// Three threads: wider than one, narrower than the fixtures' sources.
    ///
    /// # Specification
    /// trivial.
    fn three() -> Width
    {
        Width::Threads(Threads::from(NonZeroUsize::MIN.saturating_add(2)))
    }

    /// What a test row records of one step.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Seen
    {
        /// Already in layout.
        Unchanged,
        /// Laid out anew.
        Changed,
        /// A path that names no source.
        NoSource,
        /// A path that could not be read.
        Unreadable,
        /// Any other fault.
        Fault,
    }

    /// Every step of a formatting of `paths` under `rewrite` at `width`, each
    /// path relative to `base`.
    ///
    /// # Specification
    /// trivial.
    fn steps(
        base: &Path,
        paths: Vec<PathBuf>,
        rewrite: Rewrite,
        width: Width,
    ) -> Vec<(PathBuf, Seen)>
    {
        let formatting = Formatting::new(paths, FormatOptions::default(), rewrite, width);
        let mut seen = Vec::new();
        let visited = formatting.visit(&Pool::new(width), |step| {
            let (path, row) = match step {
                FormatStep::Unchanged { path, .. } => (path, Seen::Unchanged),
                FormatStep::Changed { path, .. } => (path, Seen::Changed),
                FormatStep::Fault {
                    path,
                    fault: FormatFault::NoSource,
                } => (path, Seen::NoSource),
                FormatStep::Fault {
                    path,
                    fault: FormatFault::Unreadable(_),
                } => (path, Seen::Unreadable),
                FormatStep::Fault { path, .. } => (path, Seen::Fault),
            };
            let relative = path.strip_prefix(base).unwrap_or(path).to_path_buf();
            seen.push((relative, row));
            ControlFlow::<Infallible>::Continue(())
        });
        assert_eq!(visited, ControlFlow::Continue(()));
        seen
    }

    /// The text of the file at `path`.
    ///
    /// # Specification
    /// trivial.
    fn read(path: &Path) -> String
    {
        std::fs::read_to_string(path).expect("the source is readable")
    }

    #[test]
    fn a_tree_is_formatted_in_place_once()
    {
        for (name, width) in [("format-serial", Width::SERIAL), ("format-wide", three())] {
            let scratch = Scratch::new(Path::new(name));
            scratch.file(
                Path::new("tree/a.gandr"),
                SourceText::from("def  a =  1 ;\n"),
            );
            scratch.file(Path::new("tree/b.gandr"), SourceText::from("def b = 2 ;\n"));
            scratch.file(
                Path::new("tree/nested/c.gandr"),
                SourceText::from("def c   = 3 ;\n"),
            );
            scratch.file(
                Path::new("tree/nested/d.gandr"),
                SourceText::from("def d = (1 ;\n"),
            );
            let root = scratch.root();
            std::fs::create_dir_all(root.join("empty")).expect("the directory is created");
            let paths = vec![
                root.join("tree"),
                root.join("empty"),
                root.join("missing.gandr"),
            ];
            assert_eq!(
                steps(root, paths, Rewrite::InPlace, width),
                vec![
                    (PathBuf::from("tree/a.gandr"), Seen::Changed),
                    (PathBuf::from("tree/b.gandr"), Seen::Unchanged),
                    (PathBuf::from("tree/nested/c.gandr"), Seen::Changed),
                    (PathBuf::from("tree/nested/d.gandr"), Seen::Unchanged),
                    (PathBuf::from("empty"), Seen::NoSource),
                    (PathBuf::from("missing.gandr"), Seen::Unreadable),
                ],
                "{name}: every path answers in order, and only sources out of layout change"
            );
            assert_eq!(read(&root.join("tree/a.gandr")), "def a = 1 ;\n", "{name}");
            assert_eq!(read(&root.join("tree/b.gandr")), "def b = 2 ;\n", "{name}");
            assert_eq!(
                read(&root.join("tree/nested/c.gandr")),
                "def c = 3 ;\n",
                "{name}"
            );
            assert_eq!(
                read(&root.join("tree/nested/d.gandr")),
                "def d = (1 ;\n",
                "{name}: a repaired form stays as written"
            );
            assert_eq!(
                steps(root, vec![root.join("tree")], Rewrite::InPlace, width),
                vec![
                    (PathBuf::from("tree/a.gandr"), Seen::Unchanged),
                    (PathBuf::from("tree/b.gandr"), Seen::Unchanged),
                    (PathBuf::from("tree/nested/c.gandr"), Seen::Unchanged),
                    (PathBuf::from("tree/nested/d.gandr"), Seen::Unchanged),
                ],
                "{name}: a formatted tree formats unchanged"
            );
        }
    }

    #[test]
    fn checking_writes_nothing()
    {
        let scratch = Scratch::new(Path::new("format-check"));
        scratch.file(Path::new("a.gandr"), SourceText::from("def  a =  1 ;\n"));
        scratch.file(Path::new("b.gandr"), SourceText::from("def b = 2 ;\n"));
        let root = scratch.root();
        for width in [Width::SERIAL, three()] {
            assert_eq!(
                steps(root, vec![root.to_path_buf()], Rewrite::Check, width),
                vec![
                    (PathBuf::from("a.gandr"), Seen::Changed),
                    (PathBuf::from("b.gandr"), Seen::Unchanged),
                ],
                "the check reports the source out of layout"
            );
            assert_eq!(
                read(&root.join("a.gandr")),
                "def  a =  1 ;\n",
                "the check writes nothing"
            );
        }
    }

    #[test]
    fn a_mapped_source_is_formatted_in_place()
    {
        let scratch = Scratch::new(Path::new("format-mapped"));
        scratch.file(Path::new("a.gandr"), SourceText::from("def  a =  1 ;\n"));
        scratch.file(Path::new("b.gandr"), SourceText::from("def b   = 2 ;\n"));
        scratch.file(Path::new("c.gandr"), SourceText::from("def c = 3 ;\n"));
        let root = scratch.root();
        let mut formatting = Formatting::new(
            vec![root.to_path_buf()],
            FormatOptions::default(),
            Rewrite::InPlace,
            three(),
        );
        formatting.reader = Reader::mapping_every_file();
        let held = formatting
            .reader
            .read(&root.join("a.gandr"))
            .expect("the source maps");
        let mut seen = Vec::new();
        let visited = formatting.visit(&Pool::new(three()), |step| {
            seen.push(matches!(step, FormatStep::Changed { .. }));
            ControlFlow::<Infallible>::Continue(())
        });
        assert_eq!(visited, ControlFlow::Continue(()));
        assert_eq!(seen, [true, true, false], "every source answers, in order");
        assert_eq!(
            held.text().as_ref(),
            "def  a =  1 ;\n",
            "a mapping held across the rewrite keeps the text it mapped"
        );
        assert_eq!(read(&root.join("a.gandr")), "def a = 1 ;\n");
        assert_eq!(read(&root.join("b.gandr")), "def b = 2 ;\n");
        assert_eq!(read(&root.join("c.gandr")), "def c = 3 ;\n");
    }

    #[test]
    fn a_linear_run_is_written_away_beside_a_checker()
    {
        let grammar = gandr_surface_grammar::built_in().expect("the built-in grammar builds");
        let source = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
                      \n\
                      def twice(n : Nat) -> -F Nat { Succ(Succ(n)) }\n\
                      \n\
                      def second(a : Nat, b : Nat) -> -F Nat { b }\n\
                      \n\
                      def make(n : Nat) -> -F (() => Nat) { thunk { twice(n) } }\n\
                      \n\
                      def apply(t : () => Nat) -> -F Nat { force t }\n\
                      \n\
                      def field(n : Nat) -> -F Nat {\n  run m <- twice(n) ;\n  Succ(m)\n}\n\
                      \n\
                      def paired(n : Nat) -> -F Nat {\n  run p <- twice(n) ;\n  run q <- twice(Zero) ;\n  second(p, q)\n}\n\
                      \n\
                      def chained(n : Nat) -> -F Nat {\n  run a <- twice(n) ;\n  run b <- twice(a) ;\n  become twice(b)\n}\n\
                      \n\
                      def suspended(n : Nat) -> -F Nat {\n  run t <- make(n) ;\n  apply(t)\n}\n";
        let sugared = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
                       \n\
                       def twice(n : Nat) -> -F Nat { Succ(Succ(n)) }\n\
                       \n\
                       def second(a : Nat, b : Nat) -> -F Nat { b }\n\
                       \n\
                       def make(n : Nat) -> -F (() => Nat) { thunk { twice(n) } }\n\
                       \n\
                       def apply(t : () => Nat) -> -F Nat { force t }\n\
                       \n\
                       def field(n : Nat) -> -F Nat {\n  Succ(twice(n))\n}\n\
                       \n\
                       def paired(n : Nat) -> -F Nat {\n  second(twice(n), twice(Zero))\n}\n\
                       \n\
                       def chained(n : Nat) -> -F Nat {\n  run a <- twice(n) ;\n  become twice(twice(a))\n}\n\
                       \n\
                       def suspended(n : Nat) -> -F Nat {\n  run t <- make(n) ;\n  apply(t)\n}\n";
        let options = FormatOptions {
            form: gandr_surface_format::Form::Sugared,
            ..FormatOptions::default()
        };
        let format = |text: &str, checker: Option<&dyn gandr_surface_format::Elaborate>| {
            let parsed = gandr_surface_parser::parse(&grammar, SourceText::from(text))
                .expect("the source parses");
            let formatted = gandr_surface_format::format_beside(
                &grammar,
                &parsed,
                options,
                (gandr_surface_format::Beside::Alone, checker),
            )
            .expect("the source formats");
            let withdrawn: Vec<(String, gandr_surface_format::Withdrawn)> = formatted
                .withdrawn()
                .iter()
                .map(|withdrawal| (withdrawal.declaration.clone(), withdrawal.reason.clone()))
                .collect();
            (formatted.into_text(), withdrawn)
        };
        let suspended = || {
            vec![(
                String::from("suspended"),
                gandr_surface_format::Withdrawn::Lowered,
            )]
        };
        assert_eq!(
            format(source, Some(&crate::compose::Elaborating)),
            (String::from(sugared), suspended()),
            "beside the checker the runs ending a block whose binders its tail reads once each, \
             first and in order, are written at their reads, a pair at once and a chain shedding \
             its last link; one whose call the checker would suspend at a thunk-typed parameter \
             rather than run elaborates otherwise, and keeps its spelling"
        );
        assert_eq!(
            format(sugared, Some(&crate::compose::Elaborating)),
            (String::from(sugared), suspended()),
            "a second pass writes away nothing more"
        );
        assert_eq!(
            format(source, None),
            (String::from(source), Vec::new()),
            "without a checker no run statement is written away"
        );
    }

    #[test]
    fn a_thunk_the_checker_inserts_is_left_to_it_1327()
    {
        let grammar = gandr_surface_grammar::built_in().expect("the built-in grammar builds");
        let source = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
                      \n\
                      def twice(n : Nat) -> -F Nat { Succ(Succ(n)) }\n\
                      \n\
                      def make(n : Nat) -> -F (() => Nat) { thunk { twice(n) } }\n\
                      \n\
                      def bump : Nat => Nat ;\n\
                      def bump = thunk { fn (n) { Succ(n) } } ;\n\
                      \n\
                      def counted : () => Nat ;\n\
                      def counted = thunk { twice(Zero) } ;\n\
                      \n\
                      def tailed : () => Nat ;\n\
                      def tailed = thunk { become twice(Zero) } ;\n\
                      \n\
                      def none : () => Nat ;\n\
                      def none = thunk { Zero } ;\n";
        let sugared = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
                       \n\
                       def twice(n : Nat) -> -F Nat { Succ(Succ(n)) }\n\
                       \n\
                       def make(n : Nat) -> -F (() => Nat) { thunk { twice(n) } }\n\
                       \n\
                       def bump : Nat => Nat ;\n\
                       def bump = fn (n) { Succ(n) } ;\n\
                       \n\
                       def counted : () => Nat ;\n\
                       def counted = twice(Zero) ;\n\
                       \n\
                       def tailed : () => Nat ;\n\
                       def tailed = thunk { become twice(Zero) } ;\n\
                       \n\
                       def none : () => Nat ;\n\
                       def none = thunk { Zero } ;\n";
        // The thunk rewrite alone: the function form would merge each signed
        // thunk, which a witness of its own pins.
        let options = FormatOptions {
            form: gandr_surface_format::Form::Sugared,
            rewrites: gandr_surface_format::Selection::Only(&[
                gandr_surface_format::RewriteName::InsertedThunk,
            ]),
            ..FormatOptions::default()
        };
        let format = |text: &str, checker: Option<&dyn gandr_surface_format::Elaborate>| {
            let parsed = gandr_surface_parser::parse(&grammar, SourceText::from(text))
                .expect("the source parses");
            let formatted = gandr_surface_format::format_beside(
                &grammar,
                &parsed,
                options,
                (gandr_surface_format::Beside::Alone, checker),
            )
            .expect("the source formats");
            let withdrawn: Vec<String> = formatted
                .withdrawn()
                .iter()
                .map(|withdrawal| withdrawal.declaration.clone())
                .collect();
            (formatted.into_text(), withdrawn)
        };
        assert_eq!(
            format(source, Some(&crate::compose::Elaborating)),
            (String::from(sugared), Vec::new()),
            "beside the checker a thunk of one computation checked against a thunk type is left \
             for the checker to insert; a `become` keeps its thunk, and so do a returned thunk \
             and one around a value, which the checker would not insert, with nothing withdrawn"
        );
        assert_eq!(
            format(sugared, Some(&crate::compose::Elaborating)),
            (String::from(sugared), Vec::new()),
            "a second pass leaves out nothing more"
        );
        assert_eq!(
            format(source, None),
            (String::from(source), Vec::new()),
            "without a checker every thunk is kept"
        );
    }

    #[test]
    fn a_reduct_the_checker_applies_is_written_in_the_explicit_form_and_left_out_in_the_sugared()
    {
        let grammar = gandr_surface_grammar::built_in().expect("the built-in grammar builds");
        let base = include_str!("../../../corpus/model/include/monoid.gandr");
        let (_, uses) = include_str!("../../../corpus/model/include/reduct.gandr")
            .split_once("import \"./monoid.gandr\" ;\n")
            .expect("the exemplar imports its base");
        let written = format!("{base}{uses}");
        let format = |text: &str, form, checker: Option<&dyn gandr_surface_format::Elaborate>| {
            let parsed = gandr_surface_parser::parse(&grammar, SourceText::from(text))
                .expect("the source parses");
            let options = FormatOptions {
                form,
                rewrites: gandr_surface_format::Selection::Only(&[
                    gandr_surface_format::RewriteName::InsertedReduct,
                ]),
                ..FormatOptions::default()
            };
            let formatted = gandr_surface_format::format_beside(
                &grammar,
                &parsed,
                options,
                (gandr_surface_format::Beside::Alone, checker),
            )
            .expect("the source formats");
            let withdrawn: Vec<String> = formatted
                .withdrawn()
                .iter()
                .map(|withdrawal| withdrawal.declaration.clone())
                .collect();
            (formatted.into_text(), withdrawn)
        };
        let elaborating: &dyn gandr_surface_format::Elaborate = &crate::compose::Elaborating;
        let checker = Some(elaborating);
        let (source, _) = format(&written, gandr_surface_format::Form::Source, None);
        let (explicit, withdrawn) = format(&source, gandr_surface_format::Form::Explicit, checker);
        let tokens = |text: &str| text.split_whitespace().collect::<String>();
        assert_eq!(
            (tokens(&explicit), withdrawn),
            (
                tokens(&source)
                    .replace(
                        "multiplies(endoMonoid)",
                        "multiplies(Monoid.Semigroup(endoMonoid))"
                    )
                    .replace("multiplies(m)", "multiplies(UnitAndZero.Semigroup(m))"),
                Vec::new()
            ),
            "the explicit form writes the reduct the checker applies, the diamond's by the \
             reduct its model's theory names, and leaves the one a type names as written"
        );
        assert_eq!(
            format(&explicit, gandr_surface_format::Form::Sugared, checker),
            (source.clone(), Vec::new()),
            "the sugared form leaves each to the checker again, and keeps the reduct a type names"
        );
        assert_eq!(
            format(&source, gandr_surface_format::Form::Explicit, None),
            (source.clone(), Vec::new()),
            "without a checker no reduct is written"
        );
    }

    /// #2130: beside the checker the explicit form writes the forgetting map
    /// it applies at a manifest carrier, and the sugared form leaves it to the
    /// checker again; the map at a sort selected off a binder is left to the
    /// checker in both.
    #[test]
    fn a_forgetting_map_the_checker_applies_is_written_out_only_in_the_explicit_form_2130()
    {
        let grammar = gandr_surface_grammar::built_in().expect("the built-in grammar builds");
        let base = include_str!("../../../corpus/model/identity/model-counter.gandr");
        let (_, uses) = include_str!("../../../corpus/model/identity/model-counter-manifest.gandr")
            .split_once("import \"./model-counter.gandr\" ;\n")
            .expect("the exemplar imports its base");
        let written = format!("{base}{uses}");
        let format = |text: &str, form, checker: Option<&dyn gandr_surface_format::Elaborate>| {
            let parsed = gandr_surface_parser::parse(&grammar, SourceText::from(text))
                .expect("the source parses");
            let options = FormatOptions {
                form,
                rewrites: gandr_surface_format::Selection::Only(&[
                    gandr_surface_format::RewriteName::InsertedForget,
                ]),
                ..FormatOptions::default()
            };
            let formatted = gandr_surface_format::format_beside(
                &grammar,
                &parsed,
                options,
                (gandr_surface_format::Beside::Alone, checker),
            )
            .expect("the source formats");
            let withdrawn: Vec<String> = formatted
                .withdrawn()
                .iter()
                .map(|withdrawal| withdrawal.declaration.clone())
                .collect();
            (formatted.into_text(), withdrawn)
        };
        let elaborating: &dyn gandr_surface_format::Elaborate = &crate::compose::Elaborating;
        let checker = Some(elaborating);
        let (source, _) = format(&written, gandr_surface_format::Form::Source, None);
        let (explicit, withdrawn) = format(&source, gandr_surface_format::Form::Explicit, checker);
        let tokens = |text: &str| text.split_whitespace().collect::<String>();
        let mut expected = tokens(&source);
        for (written, applied) in [
            (
                "observe(upManifest)",
                "observe(forget[sort C = +{Unit, Bool}](upManifest) at Model(Counter))",
            ),
            (
                "(upManifest : Model(Counter))",
                "(forget[sort C = +{Unit, Bool}](upManifest) at Model(Counter) : Model(Counter))",
            ),
            (
                "observe(negatedManifest)",
                "observe(forget[sort C = +{Unit, Bool}](negatedManifest) at Model(Counter))",
            ),
            (
                "observeShown(upReadings)",
                "observeShown(forget[sort R = Integer](upReadings) at Model(ReadCounter))",
            ),
            (
                "observeShown(upBoth)",
                "observeShown(forget[sort C = +{Unit, Bool}, sort R = Integer](upBoth) at \
                 Model(ReadCounter))",
            ),
            (
                "observeShown(negatedBoth)",
                "observeShown(forget[sort C = +{Unit, Bool}, sort R = Integer](negatedBoth) at \
                 Model(ReadCounter))",
            ),
        ] {
            assert!(
                expected.contains(&tokens(written)),
                "the source writes `{written}`"
            );
            expected = expected.replace(&tokens(written), &tokens(applied));
        }
        assert_eq!(
            (tokens(&explicit), withdrawn),
            (expected, Vec::new()),
            "the explicit form writes each forgetting map at a quoted carrier, and leaves the \
             one at a sort selected off a binder to the checker"
        );
        // The explicit form breaks the bodies its maps lengthen, and a body
        // keeps the lines it is written on, so the round trip is read by its
        // tokens.
        let (sugared, withdrawn) = format(&explicit, gandr_surface_format::Form::Sugared, checker);
        assert_eq!(
            (tokens(&sugared), withdrawn),
            (tokens(&source), Vec::new()),
            "the sugared form leaves each forgetting map to the checker again"
        );
        assert_eq!(
            format(&source, gandr_surface_format::Form::Explicit, None),
            (source.clone(), Vec::new()),
            "without a checker no forgetting map is written"
        );
    }

    /// A path that names no source, one that cannot be read and one whose
    /// formatted text cannot be written read apart, and the two input-output
    /// faults carry the error they met.
    #[test]
    fn each_format_fault_reads_apart_and_carries_its_cause()
    {
        let unreadable = FormatFault::Unreadable(std::io::Error::other("the disk is gone"));
        let unwritable = FormatFault::Unwritable(std::io::Error::other("the file is locked"));
        let written = [&FormatFault::NoSource, &unreadable, &unwritable].map(ToString::to_string);
        assert_eq!(
            written
                .iter()
                .collect::<alloc::collections::BTreeSet<_>>()
                .len(),
            3,
            "{written:?}"
        );
        assert!(written[1].ends_with("the disk is gone"), "{}", written[1]);
        assert!(written[2].ends_with("the file is locked"), "{}", written[2]);
    }
}
