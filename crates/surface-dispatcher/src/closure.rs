//! A source's import closure, laid out as the unit it is lowered in.
//!
//! # One unit per importer
//!
//! A source that imports a sibling by path is lowered, checked and admitted
//! together with every source it imports, directly or not: the closure's texts
//! are laid end to end, one newline apart, each source after every source it
//! imports and the importer last, parsed as one tree and lowered into one
//! arena. The siblings' declarations are therefore the prefix of the
//! importer's constants, admitted and readmitted first, and the checker and
//! the kernel see one environment. What the walk settles and reports is the
//! importer's own declarations: the composition is projected onto the
//! importer's bytes ([`Laid::base`] onward), and each sibling is settled when
//! the walk reaches it in its own right.
//!
//! **The unit is the importer's closure**, read from disk beside it; a source
//! that imports nothing stays the unit of one source and is lowered exactly as
//! before. Why the closure and not the import-connected component, what it
//! costs and when it reverses: [`compose`](mod@crate::compose) § An importer is
//! composed over its siblings.
//!
//! **A path stays in its root.** An address with no scheme is a path relative
//! to the importer's directory. It resolves when it names a readable source
//! classified under the importer's root; anything else — nothing at the path,
//! a directory, a source under another root — leaves the import unresolved,
//! and the lowering refuses every declaration of the importer
//! `ImportUnresolved` at the import. An import that is an edge of a cycle is
//! `ImportCycle` the same way, so each source of a cycle is refused whole,
//! naming the edge it leaves by. A sibling that does not parse is unresolved
//! too; a sibling the lowering refuses as a whole refuses the importer whole
//! with its refusal.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::Address;
use gandr_surface_lowering::ImportTarget;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::UnitSource;
use gandr_surface_lowering::written_imports;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::root::SourceRoot;
use crate::walk::read_source;

/// The keyword every import is written with: a source whose text never
/// spells it imports nothing, and is not parsed to find out.
const IMPORT: &str = "import";

/// A source's import closure laid out as one unit.
///
/// # Specification
/// - requires: constructed by [`lay_out`].
/// - ensures: `text` is the closure's sources in dependency order, one newline
///   apart, the importer last and starting at `base`; `unit` says where each
///   starts and what each path import resolved to; `paths` holds each source's
///   canonical path by its position in the unit.
/// - panics: none.
/// - executable: none — a data type; [`lay_out`] carries the clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a two-source closure, a cycle and an unresolved path are
///   each laid out exactly.
/// - witness: `closure::tests::an_importer_is_laid_after_what_it_imports`
/// - witness: `closure::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Laid
{
    /// The unit's text.
    pub text: String,
    /// Where each source starts and what its path imports resolved to.
    pub unit: Unit,
    /// Where the importer's own text starts in `text`.
    pub base: ByteOffset,
    /// Each source's canonical path, by its position in the unit.
    pub paths: Vec<PathBuf>,
}

quenchant_shape::reason_enum! {
    /// Why a source is lowered alone.
    pub mod laid {
        /// The reason no closure is laid out.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source writes no path import, or does not parse, which its
            /// own composition reports.
            Alone,
        }
    }
}

/// One source of a closure, as read.
#[derive(Debug)]
struct Read
{
    /// Its canonical path.
    path: PathBuf,
    /// Its text.
    text: String,
    /// What each of its path imports, in source order, came to.
    edges: Vec<Edge>,
    /// Whether it parsed.
    parsed: bool,
}

/// A source's position in the closure: the order it was first read in, the
/// importer first.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Position(usize);

/// What one path import came to while the closure was read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Edge
{
    /// The closure's source at this position.
    To(Position),
    /// No source the root holds.
    Unresolved,
}

/// How far the ordering walk has come at one source.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Visit
{
    /// Not reached.
    New,
    /// Reached; its imports are being ordered.
    Open,
    /// Ordered.
    Done,
}

/// The import closure of the source at `path`, read as `text` under `root`,
/// laid out as one unit.
///
/// # Specification
/// - requires: `text` is the source at `path`, classified under `root`.
/// - ensures: a source that writes a path import is laid out with every source
///   it reaches through path imports: each import's path is joined to its
///   importer's directory and resolves when it names a readable source
///   classified under `root` that parses; an import that is an edge of a cycle
///   resolves to [`ImportTarget::Cycle`] and any other import that does not
///   resolve to [`ImportTarget::Unresolved`]. The sources stand in dependency
///   order, each after every source it imports, the importer last at
///   [`Laid::base`], one newline apart; a source no resolved import reaches is
///   not laid out.
/// - provides: the unit the walk lowers a source in.
/// - fails: never; a source that writes no path import, or does not parse, is
///   [`laid::Absent::Alone`].
/// - panics: none.
/// - intension: a source whose text does not spell `import` is not parsed; each
///   source of the closure is read and parsed once; recursion-free.
///
/// # Adequacy
/// - hypothesis: L3 — a two-source closure, a cycle, a missing path and a
///   source importing nothing, each laid out exactly.
/// - witness: `closure::tests::an_importer_is_laid_after_what_it_imports`
/// - witness: `closure::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
/// - witness: `closure::tests::a_source_importing_nothing_is_alone`
#[spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref laid) => laid.text.get(usize::from(laid.base) ..) == Some(text.as_ref())
        && laid.paths.len() == laid.unit.sources().len(),
    Maybe::Absent(_) => true,
})]
#[inline]
pub fn lay_out(
    grammar: &Pbg,
    path: &Path,
    root: SourceRoot,
    text: SourceText<'_>,
) -> Maybe<Laid, laid::Absent>
{
    if !text.as_ref().contains(IMPORT) {
        return Maybe::Absent(laid::Absent::Alone);
    }
    let Ok(canonical) = std::fs::canonicalize(path)
    else {
        return Maybe::Absent(laid::Absent::Alone);
    };
    let mut read = Vec::from([Read {
        path: canonical.clone(),
        text: String::from(text.as_ref()),
        edges: Vec::new(),
        parsed: true,
    }]);
    let mut index = BTreeMap::from([(canonical, Position(0_usize))]);
    let mut next = 0_usize;
    while let Some(source) = read.get(next) {
        let directory = source
            .path
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_default();
        let Maybe::Present(written) =
            paths_written(grammar, SourceText::from(source.text.as_str()))
        else {
            if let Some(unparsed) = read.get_mut(next) {
                unparsed.parsed = false;
            }
            next = next.saturating_add(1);
            continue;
        };
        let mut edges = Vec::with_capacity(written.len());
        for address in written {
            edges.push(resolve(
                &directory.join(address),
                root,
                &mut read,
                &mut index,
            ));
        }
        if let Some(reading) = read.get_mut(next) {
            reading.edges = edges;
        }
        next = next.saturating_add(1);
    }
    match read.first() {
        Some(importer) if importer.parsed && !importer.edges.is_empty() => {},
        Some(_) | None => return Maybe::Absent(laid::Absent::Alone),
    }

    laid_out(&read)
}

/// The path addresses `text`'s imports write, in source order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each import whose address has no scheme, its address as written
///   with escapes decoded; a source whose imports do not read is taken to write
///   none, its own lowering refusing it; a source that does not parse is
///   unparsed.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the closure witnesses read a path import and a scheme
///   import beside it.
/// - witness: `closure::tests::an_importer_is_laid_after_what_it_imports`
#[spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref written) => written.len() <= text.as_ref().matches(IMPORT).count(),
    Maybe::Absent(_) => true,
})]
fn paths_written(
    grammar: &Pbg,
    text: SourceText<'_>,
) -> Maybe<Vec<String>, laid::Absent>
{
    let Ok(parsed) = parse(grammar, text)
    else {
        return Maybe::Absent(laid::Absent::Alone);
    };
    let tree = parsed.into_tree();
    let written = written_imports(grammar, &tree).unwrap_or_default();
    Maybe::Present(
        written
            .into_iter()
            .filter(|import| import.address == Address::Path)
            .map(|import| String::from(import.uri.as_ref()))
            .collect(),
    )
}

/// What the path `target` an import names comes to, reading the source it
/// names into the closure the first time it is named.
///
/// # Specification
/// - requires: `index` maps each canonical path in `read` to its position.
/// - ensures: the position of the source at `target`'s canonical path, read and
///   appended when new; [`Edge::Unresolved`] when the path cannot be
///   canonicalised or read, or names a source under a root other than `root`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a sibling, a second import of it, and a missing path.
/// - witness: `closure::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
#[spec(ensures: |ret| match ret {
    Edge::To(position) => position.0 < read.len(),
    Edge::Unresolved => true,
})]
fn resolve(
    target: &Path,
    root: SourceRoot,
    read: &mut Vec<Read>,
    index: &mut BTreeMap<PathBuf, Position>,
) -> Edge
{
    let Ok(canonical) = std::fs::canonicalize(target)
    else {
        return Edge::Unresolved;
    };
    if let Some(&known) = index.get(&canonical) {
        return Edge::To(known);
    }
    let mut text = String::new();
    match read_source(&canonical, &mut text) {
        Ok(found) if found == root => {
            let position = Position(read.len());
            let _fresh = index.insert(canonical.clone(), position);
            read.push(Read {
                path: canonical,
                text,
                edges: Vec::new(),
                parsed: true,
            });
            Edge::To(position)
        },
        Ok(_) | Err(_) => Edge::Unresolved,
    }
}

/// The unit the closure `read` lays out, its importer at position zero.
///
/// # Specification
/// - requires: `read` is a closure [`lay_out`] read, every edge naming a
///   position it holds.
/// - ensures: as [`lay_out`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses of [`lay_out`].
/// - witness: `closure::tests::an_importer_is_laid_after_what_it_imports`
#[spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref laid) => laid.paths.len() == laid.unit.sources().len() && laid.paths.len() <= read.len(),
    Maybe::Absent(_) => true,
})]
fn laid_out(read: &[Read]) -> Maybe<Laid, laid::Absent>
{
    let reaches = reaches(read);
    let cyclic = |from: usize, to: Position| {
        from == to.0
            || reaches
                .get(to.0)
                .is_some_and(|reached| reached.contains(&Position(from)))
    };
    let usable = |from: usize, edge: Edge| match edge {
        Edge::To(to) => !cyclic(from, to) && read.get(to.0).is_some_and(|source| source.parsed),
        Edge::Unresolved => false,
    };
    let mut visits: Vec<Visit> = read.iter().map(|_| Visit::New).collect();
    let mut order: Vec<usize> = Vec::new();
    let mut stack: Vec<(usize, usize)> = Vec::from([(0_usize, 0_usize)]);
    if let Some(visit) = visits.get_mut(0) {
        *visit = Visit::Open;
    }
    while let Some(&mut (source, ref mut at)) = stack.last_mut() {
        let edge = read
            .get(source)
            .and_then(|reading| reading.edges.get(*at))
            .copied();
        let Some(edge) = edge
        else {
            if let Some(visit) = visits.get_mut(source) {
                *visit = Visit::Done;
            }
            order.push(source);
            let _done = stack.pop();
            continue;
        };
        *at = at.saturating_add(1);
        if let Edge::To(to) = edge
            && usable(source, edge)
            && let Some(visit) = visits.get_mut(to.0)
            && *visit == Visit::New
        {
            *visit = Visit::Open;
            stack.push((to.0, 0_usize));
        }
    }
    let positions: BTreeMap<usize, SourceIndex> = order
        .iter()
        .enumerate()
        .map(|(position, &source)| (source, SourceIndex::from(position)))
        .collect();
    let mut text = String::new();
    let mut sources = Vec::with_capacity(order.len());
    let mut paths = Vec::with_capacity(order.len());
    let mut base = ByteOffset::from(0_usize);
    for &source in &order {
        let Some(reading) = read.get(source)
        else {
            continue;
        };
        if !text.is_empty() {
            text.push('\n');
        }
        base = ByteOffset::from(text.len());
        let targets = reading
            .edges
            .iter()
            .map(|&edge| match edge {
                Edge::To(to) if cyclic(source, to) => ImportTarget::Cycle,
                Edge::To(to) if usable(source, edge) => positions
                    .get(&to.0)
                    .map_or(ImportTarget::Unresolved, |&position| {
                        ImportTarget::Source(position)
                    }),
                Edge::To(_) | Edge::Unresolved => ImportTarget::Unresolved,
            })
            .collect();
        sources.push(UnitSource::new(base, targets));
        paths.push(reading.path.clone());
        text.push_str(&reading.text);
    }
    Unit::new(sources).map_or(Maybe::Absent(laid::Absent::Alone), |unit| {
        Maybe::Present(Laid {
            text,
            unit,
            base,
            paths,
        })
    })
}

/// Every source each source of `read` reaches through its imports.
///
/// # Specification
/// - requires: every edge of `read` names a position it holds.
/// - ensures: one set per source, by position, holding each source reached
///   through one or more resolved imports, itself only when a cycle leads back
///   to it.
/// - fails: never.
/// - panics: none.
/// - intension: one breadth-first walk per source; recursion-free.
///
/// # Adequacy
/// - hypothesis: L3 — a cycle and a chain.
/// - witness: `closure::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
#[spec(ensures: |ref ret| ret.len() == read.len())]
fn reaches(read: &[Read]) -> Vec<BTreeSet<Position>>
{
    read.iter()
        .map(|start| {
            let mut reached = BTreeSet::new();
            let mut queue: VecDeque<&Read> = VecDeque::from([start]);
            while let Some(source) = queue.pop_front() {
                for &edge in &source.edges {
                    if let Edge::To(to) = edge
                        && reached.insert(to)
                        && let Some(next) = read.get(to.0)
                    {
                        queue.push_back(next);
                    }
                }
            }
            reached
        })
        .collect()
}

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::ImportTarget;
    use gandr_surface_lowering::PathImportOrdinal;
    use gandr_surface_lowering::SourceIndex;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::lay_out;
    use crate::root::SourceRoot;

    /// A scratch directory, removed when dropped.
    #[repr(transparent)]
    struct Scratch(PathBuf);

    impl Scratch
    {
        /// A fresh scratch directory named for `name`, holding `files`.
        ///
        /// # Specification
        /// trivial.
        fn new(
            name: &Path,
            files: &[(&Path, SourceText<'_>)],
        ) -> Self
        {
            let directory = std::env::temp_dir().join(format!(
                "gandr-closure-{}-{}",
                name.display(),
                std::process::id()
            ));
            let _cleared = std::fs::remove_dir_all(&directory);
            std::fs::create_dir_all(&directory).expect("the scratch directory is created");
            for &(file, text) in files {
                std::fs::write(directory.join(file), <&str>::from(text))
                    .expect("the scratch source is written");
            }
            Self(directory)
        }
    }

    impl Drop for Scratch
    {
        /// Removes the directory.
        ///
        /// # Specification
        /// trivial.
        fn drop(&mut self)
        {
            let _removed = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn an_importer_is_laid_after_what_it_imports()
    {
        let grammar = built_in().expect("the grammar builds");
        let importer = SourceText::from(
            "import \"./base.gandr\" ;\nimport \"file:///far.gandr\" as far ;\ndef two : \
             Integer ;\ndef two = one ;",
        );
        let tree = Scratch::new(Path::new("laid"), &[
            (
                Path::new("base.gandr"),
                SourceText::from("def one : Integer ;\ndef one = 1 ;"),
            ),
            (Path::new("main.gandr"), importer),
        ]);
        let Maybe::Present(laid) = lay_out(
            &grammar,
            &tree.0.join("main.gandr"),
            SourceRoot::Strict,
            importer,
        )
        else {
            panic!("an importer of a sibling is laid out");
        };

        assert_eq!(
            laid.text,
            format!(
                "def one : Integer ;\ndef one = 1 ;\n{}",
                <&str>::from(importer)
            ),
            "the sibling stands first, one newline before the importer"
        );
        assert_eq!(laid.base, ByteOffset::from(34_usize));
        assert_eq!(
            laid.unit
                .target(SourceIndex::from(1_usize), PathImportOrdinal::from(0_usize)),
            ImportTarget::Source(SourceIndex::from(0_usize)),
            "the path import names the sibling; the scheme import is no path import"
        );
        assert_eq!(laid.paths.len(), 2_usize);
    }

    #[test]
    fn a_cycle_and_a_missing_path_leave_their_imports_unresolved()
    {
        let grammar = built_in().expect("the grammar builds");
        let first = SourceText::from(
            "import \"./second.gandr\" ;\nimport \"./missing.gandr\" ;\ndef one : Integer ;\ndef \
             one = 1 ;",
        );
        let tree = Scratch::new(Path::new("cycle"), &[
            (Path::new("first.gandr"), first),
            (
                Path::new("second.gandr"),
                SourceText::from("import \"./first.gandr\" ;\ndef two : Integer ;\ndef two = 2 ;"),
            ),
        ]);
        let Maybe::Present(laid) = lay_out(
            &grammar,
            &tree.0.join("first.gandr"),
            SourceRoot::Strict,
            first,
        )
        else {
            panic!("an importer is laid out, whatever its imports came to");
        };

        assert_eq!(
            laid.text,
            <&str>::from(first),
            "a source reached only through a cycle is not laid out"
        );
        assert_eq!(
            (
                laid.unit
                    .target(SourceIndex::from(0_usize), PathImportOrdinal::from(0_usize)),
                laid.unit
                    .target(SourceIndex::from(0_usize), PathImportOrdinal::from(1_usize)),
            ),
            (ImportTarget::Cycle, ImportTarget::Unresolved),
            "the edge of the cycle and the missing path"
        );
    }

    #[test]
    fn a_source_importing_nothing_is_alone()
    {
        let grammar = built_in().expect("the grammar builds");
        let text = SourceText::from("def one : Integer ;\ndef one = 1 ;");

        assert!(matches!(
            lay_out(
                &grammar,
                &PathBuf::from("alone.gandr"),
                SourceRoot::Strict,
                text
            ),
            Maybe::Absent(_)
        ));
    }
}
