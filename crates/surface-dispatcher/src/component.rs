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
///   each source's own text covers in `text`, by its position in the unit.
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
}

/// One component's sources, by position in the graph, in admission order.
#[repr(transparent)]
#[derive(Debug)]
struct Laying(Vec<Position>);

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
///   not laid out. This is the component [`group`] lays out for the source
///   given alone.
/// - provides: the unit the session judges a document in.
/// - fails: never; a source that writes no path import, or does not parse, is
///   [`laid::Absent::Alone`].
/// - panics: none.
/// - intension: a source whose text does not spell `import` is not parsed; each
///   source of the closure is read and parsed once; recursion-free.
///
/// # Adequacy
/// - hypothesis: L3 — a two-source closure, a cycle, a missing path and a
///   source importing nothing, each laid out exactly.
/// - witness: `component::tests::an_importer_is_laid_after_what_it_imports`
/// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
/// - witness: `component::tests::a_source_importing_nothing_is_alone`
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
    let mut graph = Graph::default();
    let importer = graph.admit(canonical, root, String::from(text.as_ref()));
    graph.expand(grammar);
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
            })
        },
        Maybe::Absent(absent) => Maybe::Absent(absent),
    }
}

/// The sources `given`, in the order given, grouped into the import-connected
/// components they and the sources they reach make.
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
///   source's text as it was read.
/// - provides: the units a walk lowers, each once.
/// - fails: never.
/// - panics: none.
/// - intension: a source whose text does not spell `import` and that no import
///   names is not parsed here; every other source is parsed once here, to read
///   its imports or to find whether it parses; recursion-free.
///
/// # Adequacy
/// - hypothesis: L3 — a diamond and a source beside it make two components, the
///   diamond's base laid out once, before every source that imports it.
/// - witness: `component::tests::a_component_lays_each_source_once`
/// - witness: `walk::tests::an_importer_is_judged_over_its_sibling`
#[spec(
    captures: [offered = given.len()],
    ensures: |ref ret| ret.placed.len() == offered
        && ret.placed.iter().all(|placed| ret.components.get(placed.component)
            .is_some_and(|component| placed.member < component.members.len())),
)]
pub fn group(
    grammar: &Pbg,
    given: Vec<Given>,
) -> Grouped
{
    let mut graph = Graph::default();
    let positions: Vec<Position> = given
        .into_iter()
        .map(|source| graph.admit(source.path, source.root, source.text))
        .collect();
    graph.expand(grammar);
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
    Grouped { components, placed }
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
    /// - ensures: each source whose text spells `import` is parsed and its path
    ///   imports resolved in the order it writes them, [`Parse::Parsed`] with
    ///   its edges, or [`Parse::Unparsed`] with none; each source an edge names
    ///   is [`Parse::Parsed`] or [`Parse::Unparsed`]; every other source stays
    ///   [`Parse::Unchecked`].
    /// - fails: never.
    /// - panics: none.
    /// - intension: one breadth-first pass over the sources as they are read;
    ///   each source parsed at most once; recursion-free.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closure read through two imports of one sibling, a
    ///   cycle and a missing path.
    /// - witness: `component::tests::an_importer_is_laid_after_what_it_imports`
    /// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
    #[spec(captures: [admitted = self.read.len()], ensures: self.read.len() >= admitted)]
    fn expand(
        &mut self,
        grammar: &Pbg,
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
            let (parse, written) =
                match paths_written(grammar, SourceText::from(source.text.as_str())) {
                    Maybe::Present(written) => (Parse::Parsed, written),
                    Maybe::Absent(_) => (Parse::Unparsed, Vec::new()),
                };
            let edges: Vec<Edge> = written
                .iter()
                .map(|address| self.resolve(&directory.join(address), root))
                .collect();
            if let Some(reading) = self.read.get_mut(next) {
                reading.parse = parse;
                reading.edges = edges;
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
                reading.parse = if parse(grammar, SourceText::from(reading.text.as_str())).is_ok() {
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
    /// - ensures: the position of the source at `target`'s canonical path, read
    ///   and appended when new; [`Edge::Unresolved`] when the path cannot be
    ///   canonicalised or read, or names a source under a root other than
    ///   `root`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sibling, a second import of it, and a missing path.
    /// - witness: `component::tests::a_cycle_and_a_missing_path_leave_their_imports_unresolved`
    /// - witness: `component::tests::a_component_lays_each_source_once`
    #[spec(ensures: |ret| match ret {
        Edge::To(position) => position.0 < self.read.len(),
        Edge::Unresolved => true,
    })]
    fn resolve(
        &mut self,
        target: &Path,
        root: SourceRoot,
    ) -> Edge
    {
        let Ok(canonical) = std::fs::canonicalize(target)
        else {
            return Edge::Unresolved;
        };
        if let Some(&known) = self.index.get(&canonical) {
            return if self.read.get(known.0).is_some_and(|read| read.root == root) {
                Edge::To(known)
            }
            else {
                Edge::Unresolved
            };
        }
        let mut text = String::new();
        match read_source(&canonical, &mut text) {
            Ok(found) if found == root => Edge::To(self.admit(canonical, root, text)),
            Ok(_) | Err(_) => Edge::Unresolved,
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
            sources.push(UnitSource::new(start, targets));
        }
        Unit::new(sources).map_or(Maybe::Absent(laid::Absent::Alone), |unit| {
            Maybe::Present(Component {
                text,
                unit,
                members,
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
        let (text, imports) = self.read.get_mut(position.0).map_or_else(
            || (String::new(), Vec::new()),
            |read| {
                (
                    core::mem::take(&mut read.text),
                    read.edges
                        .iter()
                        .map(|_| ImportTarget::Unresolved)
                        .collect(),
                )
            },
        );
        let start = ByteOffset::from(0_usize);
        let end = ByteOffset::from(text.len());
        Component {
            unit: Unit::new(Vec::from([UnitSource::new(start, imports)])).unwrap_or_default(),
            members: Vec::from([Member { start, end }]),
            text,
        }
    }
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
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::ImportTarget;
    use gandr_surface_lowering::PathImportOrdinal;
    use gandr_surface_lowering::SourceIndex;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Given;
    use super::Placed;
    use super::group;
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
        let grouped = group(
            &grammar,
            Vec::from([
                tree.given(Path::new("first.gandr")),
                tree.given(Path::new("second.gandr")),
            ]),
        );
        assert_eq!(
            grouped.components.len(),
            2_usize,
            "each source of a cycle is lowered apart"
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
        // The walk's order, the base given twice: once by name, once again
        // through a second path to it.
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
        );

        let [ref alone, ref diamond] = *grouped.components.as_slice()
        else {
            panic!("two components: {:?}", grouped.components);
        };
        assert_eq!(alone.text, apart, "a source no import joins stands alone");
        assert_eq!(
            diamond.text,
            format!("{base}\n{left}\n{right}\n{top}"),
            "the base laid once, before both sides, the top after both"
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
            "the top's second import names the right side's place in the unit"
        );
    }
}
