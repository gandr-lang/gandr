//! Import-connected components: the sources one lowering reads together.
//!
//! # A component is judged once
//!
//! The sources a walk is given, with every source they reach through path
//! imports, form a graph whose edges are the imports that resolve. Each
//! connected part of it holding a given source is a component, and a component
//! is one unit: its sources laid end to end, one newline apart, each after
//! every source it imports, parsed as one tree, lowered into one arena,
//! checked against one environment and admitted once. Every source of the
//! component is therefore lowered and checked exactly once, however many of
//! its siblings import it, and what the walk reports at a source is the
//! component's verdict projected onto that source's own bytes
//! ([`Component::members`]). A source that imports nothing and that no given
//! source imports is a component of one, lowered exactly as a source always
//! has been.
//!
//! - Recorded design: one arena and one kernel environment per import-connected
//!   component, its members in topological order of the import graph, level by
//!   level with the members of one level in parallel, each lowered and checked
//!   once, and the verdict projected onto each member.
//! - Change: one tree per component, its members in the depth-first order
//!   [`lay_out`] gives one source's closure, which is a topological order. The
//!   lowering reads one tree into one arena, so the members of one level lower
//!   one after another; components with no import between them lower in
//!   parallel on the walk's pool, as single sources did.
//! - Reversal: when the lowering reads a forest — one tree per source into one
//!   arena — each level's members lower on the pool.
//!
//! A source given alone — a document an editor holds, `gandr check` of one
//! path — makes the component its import closure makes: [`lay_out`] lays that
//! closure out with the source last, the unit the session judges a document
//! over.
//!
//! **A path stays in its root.** An address with no scheme is a path relative
//! to the importer's directory. It resolves when it names a readable source
//! classified under the importer's root; anything else — nothing at the path,
//! a directory, a source under another root — leaves the import unresolved,
//! and the lowering refuses every declaration of the importer
//! `ImportUnresolved` at the import. An import that is an edge of a cycle is
//! `ImportCycle` the same way, so each source of a cycle is refused whole,
//! naming the edge it leaves by, and lowered apart from the sources of the
//! cycle. A sibling that does not parse is unresolved too, and lowered apart;
//! a sibling the lowering refuses as a whole refuses its component whole with
//! its refusal.
//!
//! # A walk parses each importer once
//!
//! **Choice.** [`group`] under [`Reading::ImportForms`] reads an importer's
//! path imports from its import forms alone: each `import` that opens a line
//! is taken through the `;` after it, and those forms are parsed together and
//! read as [`paths_written`] reads a whole parse. The component is then parsed
//! once, whole, for its lowering, and that parse confirms the reading
//! ([`Component::confirms`]): its root reads, and the import forms in each
//! source's own bytes write exactly the paths read for it. A component its
//! parse does not confirm — a root the parse repaired, an import inside a
//! module, an import form that does not open its line — is grouped again
//! under [`Reading::Whole`], each importer parsed alone as [`lay_out`] parses
//! it, and its sources lowered as that grouping lays them out. A sibling an
//! import names is still parsed alone, to find whether it parses. [`lay_out`],
//! which the session calls on every edit of a document, reads whole: it
//! parses the document once already.
//!
//! **Why.** Under [`Reading::Whole`] every importer is parsed twice, alone to
//! read its imports and again inside its component, and that second parse was
//! the whole of what an import cost its importer (#617). On a 7 KB source
//! importing a one-declaration sibling, the import reading cost 23 M of the
//! importer's 152 M instructions, while the lowering, the check, the settle and
//! the kernel admission each stayed within 1 % of the flat source's: the
//! admission placed 3907 contents where the flat source placed 3906, and
//! offered 44 declarations where it offered 43. Read from its forms, the
//! importer costs 129 M against the flat source's 127 M, and the model corpus
//! 8 % less.
//!
//! **Alternatives.** Parking the forms the import reading molds and taking
//! them up in the component's parse keeps every importer's parse exact, but
//! labels and commits each importer twice and parks and resumes every form;
//! measured, it saved 9 M of the 23 M on the source above and 0.2 % of the
//! model corpus. Labeling the importer to find its `import` keywords, rather
//! than scanning its lines, reads the same forms for 2 M more. Lowering a
//! forest — one tree per source into one arena — would take each source's own
//! parse up whole; the lowering reads one tree.
//!
//! **Reversal.** A lowering that reads a forest drops the second parse
//! without a prediction: each source is parsed once, alone, and lowered from
//! that tree.
//!
//! # A source read whole is read once per process
//!
//! **Choice.** A source [`lay_out`] reads whole — the document to find its
//! imports, each sibling for its imports or to find whether it parses — is
//! read through one store per process, keyed by the source's text and the
//! grammar's fingerprint, the text compared byte for byte: a text read before
//! answers what its parse found. An editor lays a document's closure out at
//! every recheck, and a language server hovering it and a second connection
//! opening it lay it out again, while only the document's own text changed;
//! on the λ-calculus closure of #776, every sibling parsed again cost 35 ms of
//! each lay-out with specifications enforced. The store holds a few hundred
//! readings and lets the one asked for longest ago go, so an edited
//! document's earlier revisions leave it.
//!
//! **Alternatives.** A store per session keeps nothing a second connection
//! or the hover's lay-out can reuse. A key of the source's path and its
//! modification time answers a stale reading when a file changes within the
//! clock's resolution; the text itself is the key that cannot. A digest of
//! the text as the key would still compare the bytes on a hit, which is the
//! whole cost of comparing them.
//!
//! **Reversal.** Parsing each source once into a forest, the reversal of the
//! one-tree component above, keeps each source's tree; the lay-out then reads
//! its imports there, and the store goes.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::PoisonError;

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
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::root::SourceRoot;
use crate::root::classify;
use crate::walk::read_source;

/// The keyword every import is written with: a source whose text never
/// spells it imports nothing, and is not parsed to find out.
const IMPORT: &str = "import";

/// The punctuation that ends an import form.
const END: &str = ";";

/// How [`group`] reads the path imports a source writes.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Reading
{
    /// The source parsed whole, its root's import forms read, as [`lay_out`]
    /// reads them.
    #[default]
    Whole,
    /// The source's import forms alone, parsed together, for its
    /// component's parse to confirm.
    ImportForms,
}

/// Whether a component's parse reads its sources' imports as [`group`] read
/// them.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Confirmation
{
    /// The parse reads them so: the component is lowered from it.
    Confirmed,
    /// It does not: the component is grouped again under [`Reading::Whole`].
    Unconfirmed,
}

/// How many bytes of source text a run has parsed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParsedBytes(usize);

impl From<usize> for ParsedBytes
{
    /// The count of `bytes` bytes parsed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: usize) -> Self
    {
        Self(bytes)
    }
}

impl From<ParsedBytes> for usize
{
    /// The number of bytes `parsed` records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(parsed: ParsedBytes) -> Self
    {
        parsed.0
    }
}

impl ParsedBytes
{
    /// Count `other`'s bytes into these, saturating.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the sum of both counts, saturated at the maximum count.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a walk over an importer and its sibling parses the
    ///   importer's bytes once, within 2 % of the same source flat; a lost or
    ///   doubled count moves that ratio.
    /// - witness: `walk::tests::an_import_parses_its_importer_once_617`
    #[inline]
    #[spec(captures: [before = self.0], ensures: |_| self.0 == before.saturating_add(other.0))]
    pub(crate) fn absorb(
        &mut self,
        other: Self,
    )
    {
        self.0 = self.0.saturating_add(other.0);
    }
}

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
/// - witness: `component::tests::an_importer_is_laid_after_what_it_imports`
/// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
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
    /// Every path an import of a source the closure read names, resolved or
    /// not, sorted, as [`lay_out`] states.
    pub named: Vec<PathBuf>,
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

/// One source handed to [`group`]: read and classified by the walk.
#[derive(Debug)]
pub struct Given
{
    /// Its canonical path.
    pub path: PathBuf,
    /// The root its canonical path sits under.
    pub root: SourceRoot,
    /// Its text.
    pub text: String,
}

/// One component, laid out as the unit it is lowered in.
///
/// # Specification
/// - requires: constructed by [`group`].
/// - ensures: `text` is the component's sources in admission order, one newline
///   apart, each after every source it imports; `unit` says where each starts
///   and what each of its path imports resolved to; `members` holds the bytes
///   each source's own text covers in `text`, and `sources` each source's path,
///   root and the path imports read for it, by its position in the unit;
///   `reading` is how those imports were read.
/// - panics: none.
/// - executable: none — a data type; [`group`] carries the clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a diamond and a source beside it are laid out as two
///   components, the diamond's base once.
/// - witness: `component::tests::a_component_lays_each_source_once`
#[derive(Debug)]
pub struct Component
{
    /// The unit's text.
    pub text: String,
    /// Where each source starts and what its path imports resolved to.
    pub unit: Unit,
    /// Each source's own bytes in `text`, in admission order.
    pub members: Vec<Member>,
    /// Each source's path, root and imports read, in admission order.
    pub sources: Vec<MemberSource>,
    /// How the sources' imports were read.
    pub reading: Reading,
}

/// Where one source of a component was read from, and what it was read to
/// import.
///
/// # Specification
/// - requires: constructed by [`group`].
/// - ensures: `path` and `root` are the source's own; `written` holds the path
///   imports its reading found, in source order, each address as written with
///   escapes decoded — none for a source never read for its imports.
/// - panics: none.
/// - executable: none — a data type; [`group`] carries the clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`group`].
/// - witness: `component::tests::an_importer_s_forms_are_read_as_its_parse_reads_them`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MemberSource
{
    /// Its canonical path.
    pub path: PathBuf,
    /// The root its canonical path sits under.
    pub root: SourceRoot,
    /// The path imports its reading found.
    pub written: Vec<String>,
}

/// The bytes one source's own text covers in its unit's text.
///
/// # Specification
/// - requires: `start` is at or before `end`.
/// - ensures: the source's text is the unit's from `start` up to `end`.
/// - panics: none.
/// - executable: none — a data type; [`group`] and [`lay_out`] carry the
///   clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`group`].
/// - witness: `component::tests::a_component_lays_each_source_once`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Member
{
    /// Where the source's own text starts.
    pub start: ByteOffset,
    /// Where it ends.
    pub end: ByteOffset,
}

/// Where one given source stands among the components.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Placed
{
    /// Its component, by position in [`Grouped::components`].
    pub component: usize,
    /// Its position among the component's members.
    pub member: usize,
}

/// The sources a walk was given, grouped into components.
///
/// # Specification
/// - requires: constructed by [`group`].
/// - ensures: `placed` holds, for each source given in order, its component and
///   its position among that component's members; every component holds a given
///   source.
/// - panics: none.
/// - executable: none — a data type; [`group`] carries the clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`group`].
/// - witness: `component::tests::a_component_lays_each_source_once`
#[derive(Debug)]
pub struct Grouped
{
    /// The components, in the order their first given source was given.
    pub components: Vec<Component>,
    /// Where each given source stands, in the order the sources were given.
    pub placed: Vec<Placed>,
    /// The bytes parsed to group the sources: each source read whole for its
    /// imports or to find whether it parses, and the import forms read alone.
    pub parsed: ParsedBytes,
}

/// One source read into the import graph.
#[derive(Debug)]
struct Read
{
    /// Its canonical path.
    path: PathBuf,
    /// The root its canonical path sits under.
    root: SourceRoot,
    /// Its text, taken when its component is laid out.
    text: String,
    /// What each of its path imports, in source order, came to.
    edges: Vec<Edge>,
    /// The path imports its reading found, in source order.
    written: Vec<String>,
    /// Whether it parses.
    parse: Parse,
}

/// A source's position in the graph: the order it was first read in, the
/// given sources first.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Position(usize);

/// What one path import came to while the graph was read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Edge
{
    /// The graph's source at this position.
    To(Position),
    /// No source the importer's root holds.
    Unresolved,
}

/// Whether a source read into the graph parses.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Parse
{
    /// Not parsed: it writes no import and no import names it.
    Unchecked,
    /// It parses.
    Parsed,
    /// It does not parse.
    Unparsed,
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

/// The import graph over the sources given and every source they reach.
#[derive(Debug, Default)]
struct Graph
{
    /// Every source read, by position.
    read: Vec<Read>,
    /// The position of each canonical path read.
    index: BTreeMap<PathBuf, Position>,
    /// Every path an import of a source read names, whether it resolved or
    /// not, as [`Graph::resolve`] names it.
    named: BTreeSet<PathBuf>,
    /// How each source's imports are read.
    reading: Reading,
    /// The bytes parsed reading the graph.
    parsed: ParsedBytes,
}

/// The path `target` will have once a file is written there: its directory's
/// canonical path joined with its file name, or `target` itself when its
/// directory has none.
///
/// # Specification
/// trivial.
fn missing(target: &Path) -> PathBuf
{
    match (
        target.parent().map(std::fs::canonicalize),
        target.file_name(),
    ) {
        (Some(Ok(directory)), Some(name)) => directory.join(name),
        (Some(Err(_)) | None, _) | (Some(Ok(_)), None) => target.to_path_buf(),
    }
}

/// The path a laid-out closure names the file at `path` by: its canonical
/// path when it exists, else the path a file written there will have, as
/// [`lay_out`] states for [`Laid::named`].
///
/// # Specification
/// - requires: nothing.
/// - ensures: `path` canonicalised when it canonicalises; else its directory's
///   canonical path joined with its file name; else `path` as given.
/// - provides: the key a consumer looks a changed file up by in
///   [`Laid::named`].
/// - fails: never.
/// - panics: none.
/// - executable: none — the answer reads the file system.
///
/// # Adequacy
/// - hypothesis: L3 — a file that exists and one that does not are each named
///   as the closure that imports them names them.
/// - witness: `component::tests::a_closure_names_every_path_its_imports_name_844`
#[inline]
#[must_use]
pub fn named_path(path: &Path) -> PathBuf
{
    std::fs::canonicalize(path).unwrap_or_else(|_| missing(path))
}

/// The text an editor holds for a source, which an import of that source reads
/// in place of the file at its path.
pub trait Shadows
{
    /// The text held for the source at `named`, a path as [`named_path`]
    /// names it; `None` when the file at the path is read instead.
    ///
    /// # Specification
    /// trivial.
    fn shadowed(
        &self,
        named: &Path,
    ) -> Option<SourceText<'_>>;
}

/// No source shadowed: every import reads the file at its path.
#[derive(Clone, Copy, Debug, Default)]
pub struct Unshadowed;

impl Shadows for Unshadowed
{
    /// Nothing held: the file at every path is read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn shadowed(
        &self,
        _named: &Path,
    ) -> Option<SourceText<'_>>
    {
        None
    }
}

/// One component's sources, by position in the graph, in admission order.
#[repr(transparent)]
#[derive(Debug)]
struct Laying(Vec<Position>);

/// The import closure of the source at `path`, read as `text` under `root`,
/// laid out as one unit, every import read from its file.
///
/// # Specification
/// - requires: `text` is the source at `path`, classified under `root`.
/// - ensures: [`lay_out_shadowed`] with [`Unshadowed`].
/// - provides: the unit a batch tool judges a source in.
/// - fails: never.
/// - panics: none.
/// - executable: none — the result is [`lay_out_shadowed`]'s under
///   [`Unshadowed`], whose own predicate checks it; restating it here would lay
///   the closure out twice.
///
/// # Adequacy
/// - hypothesis: L3 — as [`lay_out_shadowed`].
/// - witness: `component::tests::an_importer_is_laid_after_what_it_imports`
/// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
/// - witness: `component::tests::a_closure_names_every_path_its_imports_name_844`
/// - witness: `component::tests::a_source_importing_nothing_is_alone`
#[inline]
pub fn lay_out(
    grammar: &Pbg,
    path: &Path,
    root: SourceRoot,
    text: SourceText<'_>,
) -> Maybe<Laid, laid::Absent>
{
    lay_out_shadowed(grammar, path, root, text, &Unshadowed)
}

/// The import closure of the source at `path`, read as `text` under `root`,
/// laid out as one unit, each import read as `shadows` holds it.
///
/// # Specification
/// - requires: `text` is the source at `path`, classified under `root`.
/// - ensures: a source that writes a path import is laid out with every source
///   it reaches through path imports: each import's path is joined to its
///   importer's directory and resolves when it names a source classified under
///   `root` that parses, read as `shadows` holds it, else from the file at the
///   path; an import that is an edge of a cycle resolves to
///   [`ImportTarget::Cycle`] and any other import that does not resolve to
///   [`ImportTarget::Unresolved`]. The sources stand in dependency order, each
///   after every source it imports, the importer last at [`Laid::base`], one
///   newline apart; a source no resolved import reaches is not laid out. With
///   [`Unshadowed`], this is the component [`group`] lays out for the source
///   given alone. [`Laid::named`] holds, sorted and once each, every path an
///   import of a source the closure read names, resolved or not, as
///   [`named_path`] names it.
/// - provides: the unit the session judges a document in.
/// - fails: never; a source that writes no path import, or does not parse, is
///   [`laid::Absent::Alone`].
/// - panics: none.
/// - intension: a source whose text does not spell `import` is not parsed; each
///   source of the closure is read and parsed once; recursion-free.
///
/// # Adequacy
/// - hypothesis: L3 — a two-source closure, a cycle, a missing path, a sibling
///   that does not parse, a source importing nothing, and a sibling an editor
///   holds, each laid out exactly.
/// - witness: `component::tests::an_importer_is_laid_after_what_it_imports`
/// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
/// - witness: `component::tests::a_closure_names_every_path_its_imports_name_844`
/// - witness: `component::tests::a_source_importing_nothing_is_alone`
/// - witness: `component::tests::a_shadowed_import_is_read_as_its_editor_holds_it`
#[spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref laid) => laid.text.get(usize::from(laid.base) ..) == Some(text.as_ref())
        && laid.paths.len() == laid.unit.sources().len()
        && laid.named.windows(2).all(|pair| matches!(*pair, [ref first, ref second] if first < second)),
    Maybe::Absent(_) => true,
})]
#[inline]
pub fn lay_out_shadowed(
    grammar: &Pbg,
    path: &Path,
    root: SourceRoot,
    text: SourceText<'_>,
    shadows: &dyn Shadows,
) -> Maybe<Laid, laid::Absent>
{
    if !text.as_ref().contains(IMPORT) {
        return Maybe::Absent(laid::Absent::Alone);
    }
    let Ok(canonical) = std::fs::canonicalize(path)
    else {
        return Maybe::Absent(laid::Absent::Alone);
    };
    let mut graph = Graph::default();
    let importer = graph.admit(canonical, root, String::from(text.as_ref()));
    graph.expand(grammar, shadows);
    match graph.read.get(importer.0) {
        Some(read) if read.parse == Parse::Parsed && !read.edges.is_empty() => {},
        Some(_) | None => return Maybe::Absent(laid::Absent::Alone),
    }
    let mut layings = graph.layings(&[importer]);
    let Some(laying) = layings.pop()
    else {
        return Maybe::Absent(laid::Absent::Alone);
    };
    let paths = laying
        .0
        .iter()
        .filter_map(|position| graph.read.get(position.0).map(|read| read.path.clone()))
        .collect();
    let named = core::mem::take(&mut graph.named).into_iter().collect();
    match graph.lay(&laying) {
        Maybe::Present(component) => {
            let base = component
                .members
                .last()
                .map_or_else(|| ByteOffset::from(0_usize), |member| member.start);
            Maybe::Present(Laid {
                text: component.text,
                unit: component.unit,
                base,
                paths,
                named,
            })
        },
        Maybe::Absent(absent) => Maybe::Absent(absent),
    }
}

/// The sources `given`, in the order given, grouped into the import-connected
/// components they and the sources they reach make, each source's imports
/// read as `reading` says.
///
/// # Specification
/// - requires: each source's path is canonical and its root is that path's.
/// - ensures: every source a given source reaches through path imports is read
///   once, each import resolved as [`lay_out`] resolves it; two given sources
///   at one canonical path stand for one source. Two sources share a component
///   exactly when a chain of resolved imports joins them, whichever way each
///   import points; a source reached only through an import that does not
///   resolve stands in no component. Each component is laid out as [`lay_out`]
///   lays a closure out — its sources in dependency order, one newline apart,
///   each import's target recorded — the depth-first walk starting at its
///   sources in the order they were given; a component of one source keeps that
///   source's text as it was read. Under [`Reading::Whole`] each importer's
///   imports are those [`lay_out`] reads; under [`Reading::ImportForms`] they
///   are those its import forms alone write, an importer whose forms write a
///   path import taken to parse, which [`Component::confirms`] checks.
/// - provides: the units a walk lowers, each once.
/// - fails: never.
/// - panics: none.
/// - intension: a source whose text does not spell `import` and that no import
///   names is not parsed here; under [`Reading::Whole`] every other source is
///   parsed once here, to read its imports or to find whether it parses; under
///   [`Reading::ImportForms`] an importer is scanned once and only its import
///   forms parsed; recursion-free.
///
/// # Adequacy
/// - hypothesis: L3 — a diamond and a source beside it make two components, the
///   diamond's base laid out once, before every source that imports it, under
///   either reading.
/// - witness: `component::tests::a_component_lays_each_source_once`
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
#[spec(
    captures: [offered = given.len()],
    ensures: |ref ret| ret.placed.len() == offered
        && ret.placed.iter().all(|placed| ret.components.get(placed.component)
            .is_some_and(|component| placed.member < component.members.len()
                && component.sources.len() == component.members.len()
                && component.reading == reading)),
)]
pub fn group(
    grammar: &Pbg,
    given: Vec<Given>,
    reading: Reading,
) -> Grouped
{
    let mut graph = Graph {
        reading,
        ..Graph::default()
    };
    let positions: Vec<Position> = given
        .into_iter()
        .map(|source| graph.admit(source.path, source.root, source.text))
        .collect();
    graph.expand(grammar, &Unshadowed);
    let layings = graph.layings(&positions);
    let mut where_laid: BTreeMap<Position, Placed> = BTreeMap::new();
    let mut components = Vec::with_capacity(layings.len());
    for laying in layings {
        let laid = match graph.lay(&laying) {
            Maybe::Present(component) => Vec::from([(component, laying)]),
            // Never for a laying the graph made; each source then stands
            // alone, its imports unresolved.
            Maybe::Absent(_) => laying
                .0
                .iter()
                .map(|&position| (graph.alone(position), Laying(Vec::from([position]))))
                .collect(),
        };
        for (component, laying) in laid {
            for (member, &position) in laying.0.iter().enumerate() {
                let _placed = where_laid.insert(position, Placed {
                    component: components.len(),
                    member,
                });
            }
            components.push(component);
        }
    }
    let placed = positions
        .iter()
        .map(|position| {
            where_laid.get(position).copied().unwrap_or(Placed {
                component: 0_usize,
                member: 0_usize,
            })
        })
        .collect();
    Grouped {
        components,
        placed,
        parsed: graph.parsed,
    }
}

impl Graph
{
    /// Admit the source at canonical `path`, read as `text` under `root`, or
    /// find it admitted already.
    ///
    /// # Specification
    /// - requires: `path` is canonical and `root` is its root.
    /// - ensures: the position of the source at `path`: appended with `text`
    ///   when new, the earlier one's when `path` was admitted before.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a diamond's base, named by two importers, is read
    ///   once.
    /// - witness: `component::tests::a_component_lays_each_source_once`
    #[spec(ensures: |ret| ret.0 < self.read.len())]
    fn admit(
        &mut self,
        path: PathBuf,
        root: SourceRoot,
        text: String,
    ) -> Position
    {
        if let Some(&known) = self.index.get(&path) {
            return known;
        }
        let position = Position(self.read.len());
        let _fresh = self.index.insert(path.clone(), position);
        self.read.push(Read {
            path,
            root,
            text,
            edges: Vec::new(),
            written: Vec::new(),
            parse: Parse::Unchecked,
        });
        position
    }

    /// Read every source the admitted sources reach through path imports,
    /// each once, recording what each import came to; then find whether each
    /// source an import names parses.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each source whose text spells `import` is read for its path
    ///   imports as the graph's [`Reading`] says and its imports resolved in
    ///   the order it writes them, each read as [`Graph::resolve`] reads it
    ///   under `shadows`. Read whole, it is [`Parse::Parsed`] with its edges,
    ///   or [`Parse::Unparsed`] with none; read by its import forms, it is
    ///   [`Parse::Parsed`] with its edges when they write a path import and
    ///   stays [`Parse::Unchecked`] otherwise. Each source an edge names is
    ///   [`Parse::Parsed`] or [`Parse::Unparsed`]; every other source stays
    ///   [`Parse::Unchecked`].
    /// - fails: never.
    /// - panics: none.
    /// - intension: one breadth-first pass over the sources as they are read;
    ///   each source parsed whole at most once; recursion-free.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closure read through two imports of one sibling, a
    ///   cycle and a missing path.
    /// - witness: `component::tests::an_importer_is_laid_after_what_it_imports`
    /// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
    /// - witness: `component::tests::an_importer_s_forms_are_read_as_its_parse_reads_them`
    /// - witness: `component::tests::a_shadowed_import_is_read_as_its_editor_holds_it`
    #[spec(captures: [admitted = self.read.len()], ensures: self.read.len() >= admitted)]
    fn expand(
        &mut self,
        grammar: &Pbg,
        shadows: &dyn Shadows,
    )
    {
        let mut next = 0_usize;
        while let Some(source) = self.read.get(next) {
            if !source.text.contains(IMPORT) {
                next = next.saturating_add(1);
                continue;
            }
            let directory = source
                .path
                .parent()
                .map(Path::to_path_buf)
                .unwrap_or_default();
            let root = source.root;
            let text = SourceText::from(source.text.as_str());
            let mut parsed = ParsedBytes::default();
            let (parse, written) = match self.reading {
                Reading::Whole => match read_whole(grammar, text, &mut parsed) {
                    Maybe::Present(written) => (Parse::Parsed, written),
                    Maybe::Absent(_) => (Parse::Unparsed, Vec::new()),
                },
                Reading::ImportForms => {
                    let written = paths_formed(grammar, text, &mut parsed);
                    let parse = if written.is_empty() {
                        Parse::Unchecked
                    }
                    else {
                        Parse::Parsed
                    };
                    (parse, written)
                },
            };
            self.parsed.absorb(parsed);
            let edges: Vec<Edge> = written
                .iter()
                .map(|address| self.resolve(&directory.join(address), root, shadows))
                .collect();
            if let Some(reading) = self.read.get_mut(next) {
                reading.parse = parse;
                reading.edges = edges;
                reading.written = written;
            }
            next = next.saturating_add(1);
        }
        let named: BTreeSet<Position> = self
            .read
            .iter()
            .flat_map(|read| read.edges.iter())
            .filter_map(|&edge| match edge {
                Edge::To(to) => Some(to),
                Edge::Unresolved => None,
            })
            .collect();
        for to in named {
            if let Some(reading) = self.read.get_mut(to.0)
                && reading.parse == Parse::Unchecked
            {
                let text = SourceText::from(reading.text.as_str());
                let parses = match self.reading {
                    Reading::Whole => matches!(
                        read_whole(grammar, text, &mut self.parsed),
                        Maybe::Present(_)
                    ),
                    Reading::ImportForms => {
                        self.parsed.absorb(ParsedBytes::from(reading.text.len()));
                        parse(grammar, text).is_ok()
                    },
                };
                reading.parse = if parses {
                    Parse::Parsed
                }
                else {
                    Parse::Unparsed
                };
            }
        }
    }

    /// What the path `target` an import of a source under `root` names comes
    /// to, reading the source it names into the graph the first time it is
    /// named.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the graph names `target` as [`named_path`] names it. The
    ///   position of the source at that path, appended when new: read as
    ///   `shadows` holds it when it holds it, else from the file there;
    ///   [`Edge::Unresolved`] when neither `shadows` nor a readable file holds
    ///   it, or it is classified under a root other than `root`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sibling, a second import of it, a missing path, and
    ///   a sibling an editor holds, on disk and not yet written.
    /// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
    /// - witness: `component::tests::a_component_lays_each_source_once`
    /// - witness: `component::tests::a_shadowed_import_is_read_as_its_editor_holds_it`
    #[spec(ensures: |ret| match ret {
        Edge::To(position) => position.0 < self.read.len(),
        Edge::Unresolved => true,
    })]
    fn resolve(
        &mut self,
        target: &Path,
        root: SourceRoot,
        shadows: &dyn Shadows,
    ) -> Edge
    {
        let canonical = std::fs::canonicalize(target);
        let exists = canonical.is_ok();
        let named = canonical.unwrap_or_else(|_| missing(target));
        let _named = self.named.insert(named.clone());
        if let Some(&known) = self.index.get(&named) {
            return if self.read.get(known.0).is_some_and(|read| read.root == root) {
                Edge::To(known)
            }
            else {
                Edge::Unresolved
            };
        }
        let mut text = String::new();
        let found = if let Some(held) = shadows.shadowed(&named) {
            text.push_str(held.as_ref());
            classify(&named)
        }
        else if exists {
            match read_source(&named, &mut text) {
                Ok(found) => found,
                Err(_) => return Edge::Unresolved,
            }
        }
        else {
            return Edge::Unresolved;
        };
        if found == root {
            Edge::To(self.admit(named, root, text))
        }
        else {
            Edge::Unresolved
        }
    }

    /// The components the sources at `given` stand in, each its sources in
    /// admission order.
    ///
    /// # Specification
    /// - requires: every edge of the graph names a position it holds.
    /// - ensures: an edge is usable when it resolved, is no edge of a cycle and
    ///   names a source that parses. The sources laid out are those a chain of
    ///   usable edges reaches from a source of `given`, `given` among them; two
    ///   share a component when a chain of usable edges between them joins
    ///   them, whichever way each points. The components stand in the order of
    ///   their first source in `given`; each holds its sources in the
    ///   post-order of a depth-first walk over usable edges, in the order each
    ///   source writes them, started at each of its sources by position: every
    ///   source after each source it imports.
    /// - fails: never.
    /// - panics: none.
    /// - intension: linear in the sources and edges, beside one reachability
    ///   set per source to tell a cycle; recursion-free.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a diamond and a source beside it, a cycle and a
    ///   chain.
    /// - witness: `component::tests::a_component_lays_each_source_once`
    /// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
    #[spec(ensures: |ref ret| ret.iter().all(|laying| !laying.0.is_empty()))]
    fn layings(
        &self,
        given: &[Position],
    ) -> Vec<Laying>
    {
        let usable = self.usable();
        // Every source a chain of usable edges reaches from a given one.
        let mut needed = vec![false; self.read.len()];
        let mut queue: VecDeque<Position> = given.iter().copied().collect();
        while let Some(at) = queue.pop_front() {
            match needed.get_mut(at.0) {
                Some(seen) if !*seen => *seen = true,
                Some(_) | None => continue,
            }
            if let Some(targets) = usable.get(at.0) {
                queue.extend(targets.iter().copied());
            }
        }
        // The edges joining needed sources, either way.
        let mut joined: Vec<Vec<Position>> = vec![Vec::new(); self.read.len()];
        for (from, targets) in usable.iter().enumerate() {
            if !needed.get(from).copied().unwrap_or(false) {
                continue;
            }
            for &to in targets {
                if let Some(out) = joined.get_mut(from) {
                    out.push(to);
                }
                if let Some(back) = joined.get_mut(to.0) {
                    back.push(Position(from));
                }
            }
        }
        // Each component's sources, numbered in the order given.
        let mut owner: Vec<Option<usize>> = vec![None; self.read.len()];
        let mut owned: Vec<Vec<Position>> = Vec::new();
        for &start in given {
            if owner.get(start.0).copied().flatten().is_some() {
                continue;
            }
            let component = owned.len();
            let mut members = Vec::new();
            let mut queue = VecDeque::from([start]);
            while let Some(at) = queue.pop_front() {
                match owner.get_mut(at.0) {
                    Some(slot) if slot.is_none() => *slot = Some(component),
                    Some(_) | None => continue,
                }
                members.push(at);
                if let Some(next) = joined.get(at.0) {
                    queue.extend(next.iter().copied());
                }
            }
            members.sort_unstable();
            owned.push(members);
        }
        // Each component's sources in dependency order.
        let mut visits = vec![Visit::New; self.read.len()];
        owned
            .into_iter()
            .map(|members| {
                let mut order = Vec::with_capacity(members.len());
                for start in members {
                    if visits.get(start.0) != Some(&Visit::New) {
                        continue;
                    }
                    let mut stack: Vec<(Position, usize)> = Vec::from([(start, 0_usize)]);
                    if let Some(visit) = visits.get_mut(start.0) {
                        *visit = Visit::Open;
                    }
                    while let Some(&mut (source, ref mut at)) = stack.last_mut() {
                        let Some(&to) = usable.get(source.0).and_then(|targets| targets.get(*at))
                        else {
                            if let Some(visit) = visits.get_mut(source.0) {
                                *visit = Visit::Done;
                            }
                            order.push(source);
                            let _done = stack.pop();
                            continue;
                        };
                        *at = at.saturating_add(1);
                        if let Some(visit) = visits.get_mut(to.0)
                            && *visit == Visit::New
                        {
                            *visit = Visit::Open;
                            stack.push((to, 0_usize));
                        }
                    }
                }
                Laying(order)
            })
            .collect()
    }

    /// Each source's usable edges' targets, in the order it writes them.
    ///
    /// # Specification
    /// - requires: every edge of the graph names a position it holds.
    /// - ensures: one list per source, by position: the target of each edge
    ///   that resolved, is no edge of a cycle and names a source that parses.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a cycle's edges and an edge to a missing path are not
    ///   usable; a sibling's is.
    /// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
    /// - witness: `component::tests::a_component_lays_each_source_once`
    #[spec(ensures: |ref ret| ret.len() == self.read.len())]
    fn usable(&self) -> Vec<Vec<Position>>
    {
        let reaches = reaches(&self.read);
        self.read
            .iter()
            .enumerate()
            .map(|(from, read)| {
                read.edges
                    .iter()
                    .filter_map(|&edge| match self.target(&reaches, Position(from), edge) {
                        ImportTarget::Source(to) => Some(Position(usize::from(to))),
                        ImportTarget::Unresolved | ImportTarget::Cycle => None,
                    })
                    .collect()
            })
            .collect()
    }

    /// What the edge `edge` of the source at `from` resolves to, its target
    /// named by graph position.
    ///
    /// # Specification
    /// - requires: `reaches` is [`reaches`] of the graph.
    /// - ensures: [`ImportTarget::Cycle`] for an edge whose target leads back
    ///   to `from`; [`ImportTarget::Source`] holding the target's graph
    ///   position for a resolved edge whose target parses;
    ///   [`ImportTarget::Unresolved`] otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a cycle's edge, a missing path and a sibling.
    /// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
    #[spec(ensures: |ret| match ret {
        ImportTarget::Source(to) => usize::from(to) < self.read.len(),
        ImportTarget::Unresolved | ImportTarget::Cycle => true,
    })]
    fn target(
        &self,
        reaches: &[BTreeSet<Position>],
        from: Position,
        edge: Edge,
    ) -> ImportTarget
    {
        match edge {
            Edge::To(to)
                if from == to
                    || reaches
                        .get(to.0)
                        .is_some_and(|reached| reached.contains(&from)) =>
            {
                ImportTarget::Cycle
            },
            Edge::To(to)
                if self
                    .read
                    .get(to.0)
                    .is_some_and(|read| read.parse == Parse::Parsed) =>
            {
                ImportTarget::Source(SourceIndex::from(to.0))
            },
            Edge::To(_) | Edge::Unresolved => ImportTarget::Unresolved,
        }
    }

    /// Lay the sources of `laying` out as one unit, taking their texts.
    ///
    /// # Specification
    /// - requires: `laying` is one of [`Graph::layings`], whose texts have not
    ///   been taken.
    /// - ensures: the sources' texts in order, one newline apart, each source's
    ///   own bytes recorded as its member and each of its imports' targets by
    ///   position in the unit; a laying of one source keeps its text without
    ///   copying it.
    /// - fails: never; [`laid::Absent::Alone`] only for a laying the unit
    ///   refuses, which [`Graph::layings`] never makes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses of [`lay_out`] and [`group`].
    /// - witness: `component::tests::an_importer_is_laid_after_what_it_imports`
    /// - witness: `component::tests::a_component_lays_each_source_once`
    #[spec(ensures: |ref ret| match *ret {
        Maybe::Present(ref component) => component.members.len() == laying.0.len()
            && component.unit.sources().len() == laying.0.len(),
        Maybe::Absent(_) => true,
    })]
    fn lay(
        &mut self,
        laying: &Laying,
    ) -> Maybe<Component, laid::Absent>
    {
        let reaches = reaches(&self.read);
        let in_unit: BTreeMap<usize, SourceIndex> = laying
            .0
            .iter()
            .enumerate()
            .map(|(index, &position)| (position.0, SourceIndex::from(index)))
            .collect();
        let mut sources = Vec::with_capacity(laying.0.len());
        let mut members = Vec::with_capacity(laying.0.len());
        let mut origins = Vec::with_capacity(laying.0.len());
        let mut text = String::new();
        for &position in &laying.0 {
            let targets = self.read.get(position.0).map_or_else(Vec::new, |read| {
                read.edges
                    .iter()
                    .map(|&edge| match self.target(&reaches, position, edge) {
                        ImportTarget::Source(to) => in_unit
                            .get(&usize::from(to))
                            .map_or(ImportTarget::Unresolved, |&index| {
                                ImportTarget::Source(index)
                            }),
                        held @ (ImportTarget::Unresolved | ImportTarget::Cycle) => held,
                    })
                    .collect()
            });
            let Some(read) = self.read.get_mut(position.0)
            else {
                continue;
            };
            if !sources.is_empty() {
                text.push('\n');
            }
            let start = ByteOffset::from(text.len());
            if laying.0.len() == 1_usize {
                text = core::mem::take(&mut read.text);
            }
            else {
                text.push_str(&read.text);
                read.text = String::new();
            }
            members.push(Member {
                start,
                end: ByteOffset::from(text.len()),
            });
            origins.push(MemberSource {
                path: read.path.clone(),
                root: read.root,
                written: core::mem::take(&mut read.written),
            });
            sources.push(UnitSource::new(start, targets));
        }
        let reading = self.reading;
        Unit::new(sources).map_or(Maybe::Absent(laid::Absent::Alone), |unit| {
            Maybe::Present(Component {
                text,
                unit,
                members,
                sources: origins,
                reading,
            })
        })
    }

    /// The source at `position` laid out alone, its imports unresolved.
    ///
    /// # Specification
    /// - requires: `position`'s text has not been taken.
    /// - ensures: a unit of the one source, starting at zero, each of its path
    ///   imports unresolved; its text taken.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reached only for a laying the unit refuses, which
    ///   [`Graph::layings`] never makes; the shape is [`Unit::single`]'s with
    ///   its imports kept unresolved.
    /// - witness: `component::tests::a_component_lays_each_source_once`
    #[spec(ensures: |ref ret| ret.members.len() == 1_usize && ret.unit.sources().len() == 1_usize)]
    fn alone(
        &mut self,
        position: Position,
    ) -> Component
    {
        let (text, imports, origin) = self.read.get_mut(position.0).map_or_else(
            || (String::new(), Vec::new(), Vec::new()),
            |read| {
                (
                    core::mem::take(&mut read.text),
                    read.edges
                        .iter()
                        .map(|_| ImportTarget::Unresolved)
                        .collect(),
                    Vec::from([MemberSource {
                        path: read.path.clone(),
                        root: read.root,
                        written: core::mem::take(&mut read.written),
                    }]),
                )
            },
        );
        let start = ByteOffset::from(0_usize);
        let end = ByteOffset::from(text.len());
        Component {
            unit: Unit::new(Vec::from([UnitSource::new(start, imports)])).unwrap_or_default(),
            members: Vec::from([Member { start, end }]),
            text,
            sources: origin,
            reading: self.reading,
        }
    }
}

impl Component
{
    /// Whether `tree`, the component's text parsed whole, reads each source's
    /// path imports as [`group`] read them.
    ///
    /// # Specification
    /// - requires: `tree` is [`Component::text`] parsed under `grammar`.
    /// - ensures: [`Confirmation::Confirmed`] under [`Reading::Whole`], whose
    ///   reading is each source's own parse, and for a text that never spells
    ///   `import`, which writes no import under either reading; otherwise
    ///   confirmed exactly when the tree's root reads and the path imports it
    ///   writes within each member's bytes are, in order, the paths read for
    ///   that member.
    /// - provides: the check that lets a walk parse each importer once.
    /// - fails: never; a root the parse repaired, or an import form that does
    ///   not read, is [`Confirmation::Unconfirmed`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a component of an importer and its sibling confirms;
    ///   a source whose import sits inside a module, laid beside the base the
    ///   import names, does not.
    /// - witness: `component::tests::an_importer_s_forms_are_read_as_its_parse_reads_them`
    #[must_use]
    #[inline]
    #[spec(ensures: |ret| ret == Confirmation::Confirmed || self.reading == Reading::ImportForms)]
    pub fn confirms(
        &self,
        grammar: &Pbg,
        tree: &SyntaxTree<'_>,
    ) -> Confirmation
    {
        if self.reading == Reading::Whole || !self.text.contains(IMPORT) {
            return Confirmation::Confirmed;
        }
        let Ok(written) = written_imports(grammar, tree)
        else {
            return Confirmation::Unconfirmed;
        };
        let mut found: Vec<Vec<String>> = vec![Vec::new(); self.members.len()];
        for import in written {
            if import.address != Address::Path {
                continue;
            }
            let at = import.span.start();
            let Some(member) = self
                .members
                .iter()
                .position(|member| member.start <= at && at < member.end)
                .and_then(|position| found.get_mut(position))
            else {
                return Confirmation::Unconfirmed;
            };
            member.push(String::from(import.uri.as_ref()));
        }
        let confirmed = found
            .iter()
            .zip(&self.sources)
            .all(|(paths, source)| *paths == source.written);
        if confirmed {
            Confirmation::Confirmed
        }
        else {
            Confirmation::Unconfirmed
        }
    }
}

/// The path addresses `text`'s import forms write, read from those forms
/// alone, in source order, the bytes parsed counted into `parsed`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each `import` that opens a line, past its indentation, and is
///   followed by a space or a quote is taken through the first `;` after it, or
///   through the text's end; the forms taken are parsed together, one per line,
///   and read as [`paths_written`] reads a whole parse: each import whose
///   address has no scheme, its address as written with escapes decoded. Forms
///   that do not parse, or whose root does not read, write none. `parsed` grows
///   by the bytes of the forms parsed.
/// - provides: the reading [`Reading::ImportForms`] names: for a source whose
///   root reads and whose root imports each open a line, it is
///   [`paths_written`]'s; any other reading its component's parse refuses to
///   confirm ([`Component::confirms`]).
/// - fails: never.
/// - panics: none.
/// - intension: one scan of the text; only its import forms parsed.
///
/// # Adequacy
/// - hypothesis: L3 — an importer's forms read the paths its parse reads, a
///   scheme import and a documentation line naming imports beside them read as
///   none; an import inside a module is read, and its component's parse refuses
///   to confirm it.
/// - witness: `component::tests::an_importer_s_forms_are_read_as_its_parse_reads_them`
#[spec(ensures: |ref ret| ret.len() <= text.as_ref().matches(IMPORT).count())]
fn paths_formed(
    grammar: &Pbg,
    text: SourceText<'_>,
    parsed: &mut ParsedBytes,
) -> Vec<String>
{
    let source = text.as_ref();
    let mut forms = String::new();
    for form in source
        .match_indices(IMPORT)
        .filter_map(|(at, _)| import_form(text, ByteOffset::from(at)))
    {
        forms.push_str(form.as_ref());
        forms.push('\n');
    }
    parsed.absorb(ParsedBytes::from(forms.len()));
    let Ok(read) = parse(grammar, SourceText::from(forms.as_str()))
    else {
        return Vec::new();
    };
    written_imports(grammar, read.tree()).map_or_else(
        |_| Vec::new(),
        |written| {
            written
                .into_iter()
                .filter(|import| import.address == Address::Path)
                .map(|import| String::from(import.uri.as_ref()))
                .collect()
        },
    )
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
/// - witness: `component::tests::an_importer_is_laid_after_what_it_imports`
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

/// The import form the `import` at byte `at` of `source` opens: the text from
/// it through the first `;` after it, or through the text's end, when it opens
/// a line past its indentation and a space or a quote follows it.
///
/// # Specification
/// trivial.
fn import_form(
    text: SourceText<'_>,
    at: ByteOffset,
) -> Option<SourceText<'_>>
{
    let source = <&str>::from(text);
    let at = usize::from(at);
    let before = source.get(.. at)?;
    let indent = before.rsplit('\n').next().unwrap_or_default();
    let after = source.get(at ..)?;
    let spaced = after
        .get(IMPORT.len() ..)
        .and_then(|rest| rest.chars().next())
        .is_some_and(|next| next.is_whitespace() || next == '"');
    if !indent.trim().is_empty() || !spaced {
        return None;
    }
    let end = after
        .find(END)
        .map_or(after.len(), |end| end.saturating_add(END.len()));
    after.get(.. end).map(SourceText::from)
}

/// The files `text`, the source at `path`, imports by path: each path address
/// its imports write, joined to `path`'s directory and named as
/// [`named_path`] names it, in source order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a text that never spells `import` imports nothing and is not
///   parsed; one each of whose `import`s opens an import form is read from its
///   forms alone, as [`Reading::ImportForms`] reads it; any other is read
///   whole, as [`Reading::Whole`] reads it, a text this process read whole
///   before answering what that reading found. A source whose imports do not
///   read, or that does not parse, imports nothing.
/// - provides: an importer's edges, read without judging it: what a table of
///   every source under a root keeps to answer a file's importers.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause would read the text again.
///
/// # Adequacy
/// - hypothesis: L3 — imports read from their forms and an import written after
///   a declaration on its line each name their file, a scheme import names
///   none, and a source that never spells `import` names none.
/// - witness: `component::tests::a_source_names_the_files_it_imports`
#[inline]
#[must_use]
pub fn imports_named(
    grammar: &Pbg,
    path: &Path,
    text: SourceText<'_>,
) -> Vec<PathBuf>
{
    let source = text.as_ref();
    if !source.contains(IMPORT) {
        return Vec::new();
    }
    let mut parsed = ParsedBytes::default();
    let formed = source
        .match_indices(IMPORT)
        .all(|(at, _)| import_form(text, ByteOffset::from(at)).is_some());
    let written = if formed {
        paths_formed(grammar, text, &mut parsed)
    }
    else {
        match read_whole(grammar, text, &mut parsed) {
            Maybe::Present(written) => written,
            Maybe::Absent(_) => Vec::new(),
        }
    };
    let directory = path.parent().unwrap_or(path);
    written
        .iter()
        .map(|address| named_path(&directory.join(address)))
        .collect()
}

/// The most sources [`READINGS`] holds before it lets the one read longest
/// ago go: a closure of a few hundred sources, beside the revisions of the
/// documents an editor has open.
const READINGS_HELD: usize = 512;

/// What reading one source whole found, for each grammar it was read under,
/// and when it was last asked for.
#[derive(Debug)]
struct Held
{
    /// The grammar the source was parsed under.
    grammar: GrammarFingerprint,
    /// The path imports its parse writes, or that it does not parse.
    written: Maybe<Vec<String>, laid::Absent>,
    /// The tick of the store's clock it was last asked for at.
    used: u64,
}

/// Every source this process has read whole, by its text.
#[derive(Debug)]
struct Readings
{
    /// What each text's reading found, under each grammar it was read under.
    held: BTreeMap<String, Vec<Held>>,
    /// How many readings the store holds.
    count: usize,
    /// Ticks once per question.
    clock: u64,
}

impl Readings
{
    /// Keep `fresh`, what reading `text` found, unless the store holds a
    /// reading of `text` under its grammar already, then let the readings
    /// asked for longest ago go until at most [`READINGS_HELD`] remain.
    ///
    /// # Specification
    /// - requires: `count` is the number of readings `held` holds.
    /// - ensures: `count` is still that number, and at most [`READINGS_HELD`];
    ///   `fresh` is held unless it was the one asked for longest ago.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closure laid out twice parses its sources once, and
    ///   a sibling whose text changed is read again and laid out as it now
    ///   reads.
    /// - witness: `component::tests::a_source_read_whole_is_parsed_once_per_text_776`
    #[spec(ensures: self.count <= READINGS_HELD)]
    fn keep(
        &mut self,
        text: String,
        fresh: Held,
    )
    {
        let held = self.held.entry(text).or_default();
        if held.iter().all(|held| held.grammar != fresh.grammar) {
            held.push(fresh);
            self.count = self.count.saturating_add(1);
        }
        while self.count > READINGS_HELD {
            let oldest = self
                .held
                .iter()
                .flat_map(|(text, held)| held.iter().map(move |held| (held.used, text)))
                .min()
                .map(|(_, text)| text.clone());
            let Some(oldest) = oldest
            else {
                break;
            };
            if let Some(held) = self.held.get_mut(&oldest) {
                let before = held.len();
                let least = held.iter().map(|held| held.used).min();
                held.retain(|held| Some(held.used) != least);
                let gone = before.saturating_sub(held.len());
                if held.is_empty() {
                    let _gone = self.held.remove(&oldest);
                }
                self.count = self.count.saturating_sub(gone);
            }
        }
    }
}

/// The process's readings, shared by every lay-out and every grouping that
/// reads its sources whole.
static READINGS: Mutex<Readings> = Mutex::new(Readings {
    held: BTreeMap::new(),
    count: 0_usize,
    clock: 0_u64,
});

/// The path imports `text` writes, read whole under `grammar`: what
/// [`paths_written`] answers, parsed once per process for each text and
/// grammar, `parsed` counting the bytes of a text parsed now.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`paths_written`] of `text` under `grammar`. A text and grammar
///   this process read before answer what that reading found, the text compared
///   byte for byte, and `parsed` is unchanged; any other is parsed, `parsed`
///   absorbs its length, and the store keeps its reading, letting the one asked
///   for longest ago go past [`READINGS_HELD`].
/// - provides: the sibling reading every keystroke's lay-out repeats: an
///   editor's recheck reads each source of the document's closure again, and
///   only the document's own text changes.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause would parse the text again, the work the
///   store saves; the witness reads a held text and a changed one.
///
/// # Adequacy
/// - hypothesis: L3 — a closure laid out twice parses its sources once, and a
///   sibling whose text changed is read again and laid out as it now reads.
/// - witness: `component::tests::a_source_read_whole_is_parsed_once_per_text_776`
fn read_whole(
    grammar: &Pbg,
    text: SourceText<'_>,
    parsed: &mut ParsedBytes,
) -> Maybe<Vec<String>, laid::Absent>
{
    let fingerprint = grammar.fingerprint();
    {
        let mut readings = READINGS.lock().unwrap_or_else(PoisonError::into_inner);
        readings.clock = readings.clock.saturating_add(1);
        let now = readings.clock;
        if let Some(held) = readings
            .held
            .get_mut(text.as_ref())
            .and_then(|held| held.iter_mut().find(|held| held.grammar == fingerprint))
        {
            held.used = now;
            return held.written.clone();
        }
    }
    parsed.absorb(ParsedBytes::from(text.as_ref().len()));
    let written = paths_written(grammar, text);
    let mut readings = READINGS.lock().unwrap_or_else(PoisonError::into_inner);
    let used = readings.clock;
    readings.keep(String::from(text.as_ref()), Held {
        grammar: fingerprint,
        written: written.clone(),
        used,
    });
    drop(readings);
    written
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
/// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
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
    use alloc::collections::BTreeMap;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::ImportTarget;
    use gandr_surface_lowering::PathImportOrdinal;
    use gandr_surface_lowering::SourceIndex;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Confirmation;
    use super::Given;
    use super::ParsedBytes;
    use super::Placed;
    use super::Reading;
    use super::Shadows;
    use super::group;
    use super::imports_named;
    use super::lay_out;
    use super::lay_out_shadowed;
    use super::named_path;
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
                "gandr-component-{}-{}",
                name.display(),
                std::process::id()
            ));
            let _cleared = std::fs::remove_dir_all(&directory);
            std::fs::create_dir_all(&directory).expect("the scratch directory is created");
            for &(file, text) in files {
                std::fs::write(directory.join(file), <&str>::from(text))
                    .expect("the scratch source is written");
            }
            Self(
                std::fs::canonicalize(&directory)
                    .expect("the scratch directory has a canonical path"),
            )
        }

        /// The source `file` in the directory, given as the walk gives it.
        ///
        /// # Specification
        /// trivial.
        fn given(
            &self,
            file: &Path,
        ) -> Given
        {
            let path = self.0.join(file);
            let text = std::fs::read_to_string(&path).expect("the scratch source reads");
            Given {
                path,
                root: SourceRoot::Strict,
                text,
            }
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

    /// The sources an editor holds, by the path a closure names each by.
    #[repr(transparent)]
    struct Held(BTreeMap<PathBuf, String>);

    impl Shadows for Held
    {
        /// The text held at `named`, if any.
        ///
        /// # Specification
        /// trivial.
        fn shadowed(
            &self,
            named: &Path,
        ) -> Option<SourceText<'_>>
        {
            self.0
                .get(named)
                .map(|text| SourceText::from(text.as_str()))
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
        for reading in [Reading::Whole, Reading::ImportForms] {
            let grouped = group(
                &grammar,
                Vec::from([
                    tree.given(Path::new("first.gandr")),
                    tree.given(Path::new("second.gandr")),
                ]),
                reading,
            );
            assert_eq!(
                grouped.components.len(),
                2_usize,
                "{reading:?}: each source of a cycle is lowered apart"
            );
        }
    }

    /// #844: a closure names every path its imports name, though only the
    /// importer is laid out: the edge of a cycle and a missing path.
    #[test]
    fn a_closure_names_every_path_its_imports_name_844()
    {
        let grammar = built_in().expect("the grammar builds");
        let first = SourceText::from(
            "import \"./second.gandr\" ;\nimport \"./missing.gandr\" ;\ndef one : Integer ;\ndef \
             one = 1 ;",
        );
        let tree = Scratch::new(Path::new("named-844"), &[
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
            laid.paths,
            [tree.0.join("first.gandr")],
            "the importer alone is laid out"
        );
        assert_eq!(
            laid.named,
            ["first.gandr", "missing.gandr", "second.gandr"].map(|file| tree.0.join(file)),
            "each path an import names, the missing one where it would be written"
        );
        assert_eq!(
            ["missing.gandr", "second.gandr"].map(|file| named_path(&tree.0.join(".").join(file))),
            ["missing.gandr", "second.gandr"].map(|file| tree.0.join(file)),
            "a file is looked up by the path the closure names it by, written or not"
        );
    }

    /// #776: a source read whole is parsed once per text in a process. A
    /// second grouping of the same sources parses nothing and lays them out
    /// alike; a sibling whose text changed is parsed again and laid out as it
    /// now reads.
    #[test]
    fn a_source_read_whole_is_parsed_once_per_text_776()
    {
        let grammar = built_in().expect("the grammar builds");
        let floor = "/// #776: the floor.\ndef six : Integer ;\ndef six = 6 ;";
        let base = "/// #776: the base.\ndef seven : Integer ;\ndef seven = 7 ;";
        let importer = "import \"./base.gandr\" ;\n/// #776: the importer.\ndef eight : Integer \
                        ;\ndef eight = 8 ;";
        let tree = Scratch::new(Path::new("read-once"), &[
            (Path::new("floor.gandr"), SourceText::from(floor)),
            (Path::new("base.gandr"), SourceText::from(base)),
            (Path::new("importer.gandr"), SourceText::from(importer)),
        ]);
        let grouped = || {
            group(
                &grammar,
                Vec::from([tree.given(Path::new("importer.gandr"))]),
                Reading::Whole,
            )
        };
        let first = grouped();
        assert_eq!(
            usize::from(first.parsed),
            base.len().saturating_add(importer.len()),
            "the first grouping parses the importer and its sibling"
        );
        let again = grouped();
        assert_eq!(
            usize::from(again.parsed),
            0_usize,
            "a second grouping parses neither"
        );
        let texts = |grouped: &super::Grouped| {
            grouped
                .components
                .iter()
                .map(|component| component.text.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(texts(&again), texts(&first), "and lays them out alike");
        let rewritten = format!("import \"./floor.gandr\" ;\n{base}");
        std::fs::write(tree.0.join("base.gandr"), &rewritten).expect("the sibling is rewritten");
        let changed = grouped();
        assert_eq!(
            usize::from(changed.parsed),
            rewritten.len().saturating_add(floor.len()),
            "the changed sibling is read again, and the source it now imports"
        );
        assert_eq!(
            texts(&changed),
            [format!("{floor}\n{rewritten}\n{importer}")],
            "the closure is laid out as the sibling now reads"
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

    #[test]
    fn a_shadowed_import_is_read_as_its_editor_holds_it()
    {
        let grammar = built_in().expect("the grammar builds");
        let importer = SourceText::from(
            "import \"./base.gandr\" ;\nimport \"./draft.gandr\" ;\ndef four : Integer ;\ndef \
             four = one ;",
        );
        let tree = Scratch::new(Path::new("shadowed"), &[
            (
                Path::new("base.gandr"),
                SourceText::from("def one : Integer ;\ndef one = 1 ;"),
            ),
            (Path::new("main.gandr"), importer),
        ]);
        let main = tree.0.join("main.gandr");
        let held = Held(BTreeMap::from([
            (
                named_path(&tree.0.join("base.gandr")),
                String::from("def one : Integer ;\ndef one = 2 ;"),
            ),
            (
                named_path(&tree.0.join("draft.gandr")),
                String::from("def three : Integer ;\ndef three = 3 ;"),
            ),
        ]));
        let Maybe::Present(shadowed) =
            lay_out_shadowed(&grammar, &main, SourceRoot::Strict, importer, &held)
        else {
            panic!("an importer of held siblings is laid out");
        };
        assert!(
            shadowed.text.contains("def one = 2 ;") && !shadowed.text.contains("def one = 1 ;"),
            "the sibling on disk is read as the editor holds it: {}",
            shadowed.text
        );
        assert!(
            shadowed.text.contains("def three = 3 ;"),
            "a sibling only the editor holds is laid out: {}",
            shadowed.text
        );
        assert_eq!(shadowed.paths.len(), 3_usize);
        let Maybe::Present(unshadowed) = lay_out(&grammar, &main, SourceRoot::Strict, importer)
        else {
            panic!("an importer of a sibling on disk is laid out");
        };
        assert!(
            unshadowed.text.contains("def one = 1 ;") && !unshadowed.text.contains("def three"),
            "unshadowed, the file is read and the unwritten sibling is unresolved: {}",
            unshadowed.text
        );
        assert_eq!(unshadowed.paths.len(), 2_usize);
    }

    #[test]
    fn a_component_lays_each_source_once()
    {
        let grammar = built_in().expect("the grammar builds");
        let base = "def one : Integer ;\ndef one = 1 ;";
        let left = "import \"./base.gandr\" ;\ndef two : Integer ;\ndef two = one ;";
        let right = "import \"./base.gandr\" ;\ndef three : Integer ;\ndef three = one ;";
        let top = "import \"./left.gandr\" ;\nimport \"./right.gandr\" ;\ndef four : Integer \
                   ;\ndef four = two ;";
        let apart = "def five : Integer ;\ndef five = 5 ;";
        let tree = Scratch::new(Path::new("diamond"), &[
            (Path::new("apart.gandr"), SourceText::from(apart)),
            (Path::new("base.gandr"), SourceText::from(base)),
            (Path::new("left.gandr"), SourceText::from(left)),
            (Path::new("right.gandr"), SourceText::from(right)),
            (Path::new("top.gandr"), SourceText::from(top)),
        ]);
        for reading in [Reading::Whole, Reading::ImportForms] {
            // The walk's order, the base given twice: once by name, once
            // again through a second path to it.
            let grouped = group(
                &grammar,
                Vec::from([
                    tree.given(Path::new("apart.gandr")),
                    tree.given(Path::new("left.gandr")),
                    tree.given(Path::new("base.gandr")),
                    tree.given(Path::new("top.gandr")),
                    tree.given(Path::new("right.gandr")),
                    tree.given(Path::new("base.gandr")),
                ]),
                reading,
            );

            let [ref alone, ref diamond] = *grouped.components.as_slice()
            else {
                panic!("{reading:?}: two components: {:?}", grouped.components);
            };
            assert_eq!(alone.text, apart, "a source no import joins stands alone");
            assert_eq!(
                diamond.text,
                format!("{base}\n{left}\n{right}\n{top}"),
                "{reading:?}: the base laid once, before both sides, the top after both"
            );
            let own: Vec<&str> = diamond
                .members
                .iter()
                .map(|member| {
                    diamond
                        .text
                        .get(usize::from(member.start) .. usize::from(member.end))
                        .unwrap_or_default()
                })
                .collect();
            assert_eq!(own, [base, left, right, top], "each member's own bytes");
            let place = |component: usize, member: usize| Placed { component, member };
            assert_eq!(grouped.placed, [
                place(0, 0),
                place(1, 1),
                place(1, 0),
                place(1, 3),
                place(1, 2),
                place(1, 0),
            ]);
            assert_eq!(
                diamond
                    .unit
                    .target(SourceIndex::from(3_usize), PathImportOrdinal::from(1_usize)),
                ImportTarget::Source(SourceIndex::from(2_usize)),
                "{reading:?}: the top's second import names the right side's place"
            );
        }
    }

    #[test]
    fn an_importer_s_forms_are_read_as_its_parse_reads_them()
    {
        let grammar = built_in().expect("the grammar builds");
        let base = "def one : Integer ;\ndef one = 1 ;";
        let importer = "/// Imports the base.\nimport \"./base.gandr\" ;\nimport \
                        \"file:///far.gandr\" as far ;\ndef two : Integer ;\ndef two = one ;";
        // An import inside a module is no import of the source's root: read
        // from its forms alone it names the base, and the source's parse
        // does not.
        let nested = "module inner {\n  import \"./base.gandr\" ;\n}\ndef three : Integer ;\ndef \
                      three = 3 ;";
        let tree = Scratch::new(Path::new("formed"), &[
            (Path::new("base.gandr"), SourceText::from(base)),
            (Path::new("importer.gandr"), SourceText::from(importer)),
            (Path::new("nested.gandr"), SourceText::from(nested)),
        ]);
        assert_eq!(
            super::paths_formed(
                &grammar,
                SourceText::from(importer),
                &mut ParsedBytes::default()
            ),
            ["./base.gandr"],
            "the path import, the scheme import read as none"
        );
        assert_eq!(
            super::paths_written(&grammar, SourceText::from(importer)),
            Maybe::Present(Vec::from([String::from("./base.gandr")])),
            "as the importer's own parse reads it"
        );
        let confirmation = |given: &str| {
            let grouped = group(
                &grammar,
                Vec::from([tree.given(Path::new(given))]),
                Reading::ImportForms,
            );
            let [ref component] = *grouped.components.as_slice()
            else {
                panic!("one component: {:?}", grouped.components);
            };
            assert_eq!(
                component.members.len(),
                2_usize,
                "{given} is laid after the base"
            );
            let parsed = parse(&grammar, SourceText::from(component.text.as_str()))
                .expect("the component parses");
            component.confirms(&grammar, parsed.tree())
        };
        assert_eq!(confirmation("importer.gandr"), Confirmation::Confirmed);
        assert_eq!(
            confirmation("nested.gandr"),
            Confirmation::Unconfirmed,
            "the component's root imports nothing in the nested source's bytes"
        );
        let whole = group(
            &grammar,
            Vec::from([tree.given(Path::new("nested.gandr"))]),
            Reading::Whole,
        );
        assert_eq!(
            whole
                .components
                .iter()
                .map(|component| component.text.as_str())
                .collect::<Vec<_>>(),
            [nested],
            "read whole, the nested source imports nothing and stands alone"
        );
    }

    #[test]
    fn a_source_names_the_files_it_imports()
    {
        let grammar = built_in().expect("the grammar builds");
        let base = "def one : Integer ;\ndef one = 1 ;";
        let importer = "/// Imports the base.\nimport \"./base.gandr\" ;\nimport \
                        \"file:///far.gandr\" as far ;\ndef two : Integer ;\ndef two = one ;";
        // The second import does not open its line, so the source is read
        // whole, and both are named, the file not yet written among them.
        let crowded = "import \"./base.gandr\" ; import \"./later.gandr\" ;\ndef three : Integer \
                       ;\ndef three = 3 ;";
        let tree = Scratch::new(Path::new("named"), &[(
            Path::new("base.gandr"),
            SourceText::from(base),
        )]);
        let named = |file: &str, text: &str| {
            imports_named(&grammar, &tree.0.join(file), SourceText::from(text))
        };
        assert_eq!(
            named("importer.gandr", importer),
            [tree.0.join("base.gandr")],
            "the path import names its file; the scheme import names none"
        );
        assert_eq!(
            named("crowded.gandr", crowded),
            ["base.gandr", "later.gandr"].map(|file| tree.0.join(file)),
            "an import past the start of its line is read from the whole source"
        );
        assert_eq!(
            named("base.gandr", base),
            Vec::<PathBuf>::new(),
            "a source that never spells `import` names nothing"
        );
    }
}
