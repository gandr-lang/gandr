//! The cells verb: the rewriting cells each source's declarations elaborate
//! to, each read hole by hole with how many times its right-hand side writes
//! the hole.
//!
//! # A hole's count is its Lipschitz constant
//!
//! A cell whose right-hand side writes a hole `n` times stretches a distance
//! between two instances of the hole by at most `n` in one step, when every
//! symbol is non-expansive: zero for a dropped hole, one for a kept one. The
//! census reads the count each cell's metadata already holds
//! ([`CellContractumUse::occurrences`](gandr_theory_cell_complexes::CellContractumUse::occurrences));
//! it walks no term of its own. The kernel's reading of a cell is unchanged:
//! the count is reported, not trusted.
//!
//! # The walk's paths, the lowering's cells
//!
//! [`Census`] reaches its sources exactly as the walk does, and lays each out
//! after the prelude and the sources it imports, as `check` lowers it. A
//! source's rows are the cells of the declarations it writes itself, in the
//! lowering's order, each declaration's cells in its store's order. Nothing is
//! checked: a census reads the cells the lowering elaborates, whether or not
//! the declarations settle. The census steps one source at a time; a census
//! of a tree costs a parse and a lowering per source, and no checking.
//!
//! # References
//!
//! - `Gavazzo-2022-quantitative_metric_rewriting_abstract_nonexpansive_graded_systems`
//!   — exemplar: § 8.2's Lemma 9 bounds how far one step stretches the distance
//!   between two instances of a hole by the number of times the contractum
//!   writes it, over non-expansive symbols: the count a row reports.
//! - `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — background: each cell's
//!   counts are reported over the sources as they lower, the kernel unchanged
//!   (§ quant-try-first).

use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::EtaKind;
use gandr_theory_cell_complexes::HoleName;
use gandr_theory_cell_complexes::Multiplicity;
use gandr_theory_cell_complexes::StepGrowth;
use quenchant_shape::shape::Maybe;

use crate::component;
use crate::compose::ComposeFault;
use crate::compose::Lowered;
use crate::compose::LoweringCount;
use crate::compose::lower_unit_source;
use crate::format::LineColumn;
use crate::reader::Reader;
use crate::root;
use crate::walk::Reached;
use crate::walk::Traversal;
use crate::walk::walk_step;

/// Why a path's cells could not be read.
#[derive(Debug)]
pub enum CensusFault<'census>
{
    /// The path could not be listed or read, or its text is not UTF-8.
    Unreadable(std::io::Error),
    /// The path names no source: a directory holding no `.gandr` file.
    NoSource,
    /// The built-in grammar did not build, so no source can be parsed.
    Grammar(&'census PbgError),
    /// The parse could not commit a tree, or the lowering faulted.
    Composed(ComposeFault<'census>),
    /// The lowering refused the source as a whole.
    Refused(LoweringRefusal<'census>),
}

impl core::fmt::Display for CensusFault<'_>
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
            Self::Composed(ref fault) => write!(f, "not lowered: {fault}"),
            Self::Refused(ref refusal) => write!(f, "the lowering refused the source: {refusal}"),
        }
    }
}

/// One cell of a declaration a source writes, with each hole's count.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CellRow
{
    /// The one-based line the cell is written on: its rule's arrow, for a
    /// written rule's cell, and its declaration's start otherwise.
    pub line: usize,
    /// The one-based column, in characters, of the same place.
    pub column: usize,
    /// The cell, by its place in its declaration's store.
    pub cell: CellId,
    /// Where the cell came from.
    pub provenance: CellProvenance,
    /// The join of its holes' uses.
    pub growth: StepGrowth,
    /// Each hole, in first-occurrence order over the left-hand side then the
    /// right, with how many times the right-hand side writes it.
    pub holes: Vec<(HoleName, Multiplicity)>,
}

impl core::fmt::Display for CellRow
{
    /// The line and column, `cell` and the cell's place, its provenance and
    /// growth, then each hole and its count.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes ``<line>:<column>: cell <id> <provenance>, <growth>:``
    ///   and then each hole as ` <hole> <count>`, separated by commas, or ` no
    ///   holes` for a cell without one, and no line terminator. The provenance
    ///   is `rule`, `μ/μ̃`, `frame`, `data η`, `codata η` or `completion`; the
    ///   growth `strictly linear`, `erasing`, or `duplicating` and the largest
    ///   count.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes write status, not the text
    ///   written, so the rendering is read off the census's witness rows.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — rule cells of every growth, a frame cell, and holes
    ///   counted zero to three times render exactly; the provenances no
    ///   description declaration mints are outside the fixture.
    /// - witness: `cells::tests::a_census_reads_each_hole_s_count_in_the_source_s_own_declarations`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        let provenance = match self.provenance {
            CellProvenance::SurfaceRule => "rule",
            CellProvenance::MuMuTilde => "μ/μ̃",
            CellProvenance::FrameDefining => "frame",
            CellProvenance::Eta(EtaKind::Data) => "data η",
            CellProvenance::Eta(EtaKind::Codata) => "codata η",
            CellProvenance::DerivedByCompletion => "completion",
        };
        write!(
            f,
            "{}:{}: cell {} {provenance}, ",
            self.line,
            self.column,
            usize::from(self.cell)
        )?;
        match self.growth {
            StepGrowth::StrictlyLinear => f.write_str("strictly linear:")?,
            StepGrowth::Erasing => f.write_str("erasing:")?,
            StepGrowth::Duplicating { count } => write!(f, "duplicating {}:", u64::from(count))?,
        }
        if self.holes.is_empty() {
            return f.write_str(" no holes");
        }
        let mut separator = " ";
        for &(ref hole, count) in &self.holes {
            write!(f, "{separator}{hole} {}", u64::from(count))?;
            separator = ", ";
        }
        Ok(())
    }
}

/// One step of a census.
#[derive(Debug)]
pub enum CensusStep<'census>
{
    /// A source, and the cells of the declarations it writes.
    Source
    {
        /// The source's path, as the census reached it.
        path: &'census Path,
        /// The cells, as [`Census::step`] orders them.
        cells: Vec<CellRow>,
    },
    /// A path the census could not read cells from.
    Fault
    {
        /// The path, as the census reached it.
        path: &'census Path,
        /// Why.
        fault: CensusFault<'census>,
    },
}

/// The cells verb over the paths it was given, reading its sources in order.
#[derive(Debug)]
pub struct Census
{
    /// The grammar every source is parsed under, built once per census.
    grammar: Result<Pbg, PbgError>,
    /// Where the census is among the paths it was given.
    traversal: Traversal,
    /// What every source is read through.
    reader: Reader,
    /// The last source reached, laid out after the prelude and its imports:
    /// the text a step's fault borrows.
    laid: String,
}

impl Census
{
    /// A census of `paths`, in the order given, nothing yet read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(paths: Vec<PathBuf>) -> Self
    {
        Self {
            grammar: built_in(),
            traversal: Traversal::new(paths),
            reader: Reader::new(),
            laid: String::new(),
        }
    }

    /// The next source or fault of the census.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each path given is reached in order, as [`crate::Walk`]
    ///   reaches it. Each source is read, laid out after the prelude and the
    ///   sources it imports, parsed and lowered; its step holds one row per
    ///   cell of each declaration the source writes itself — none from the
    ///   prelude or an import — in the lowering's order and each declaration's
    ///   store order. A row carries the cell's line and column in the source —
    ///   its rule's arrow when it is a written rule's and the declaration's
    ///   rules oriented, its declaration's start otherwise — the cell, its
    ///   provenance, its step growth, and each hole with how many times the
    ///   cell's right-hand side writes it. A path that cannot be listed or
    ///   read, names no source, fails to parse or lower, or whose source the
    ///   lowering refuses whole is a [`CensusStep::Fault`]. Exhaustion is
    ///   stable.
    /// - provides: the pass `gandr cells` renders.
    /// - fails: never; every fault is a step, and the census continues past it.
    /// - panics: none.
    /// - intension: holds one laid-out source at a time.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree holding a source whose rules write a hole
    ///   once, not at all, twice and three times, a source importing it, and a
    ///   missing path yields exact ordered rows: every hole's count, the
    ///   imported declaration's cells absent from the importer's step, each
    ///   rule cell at its own rule's line in the source's own text and each
    ///   frame cell at its declaration's, and the missing path's fault.
    ///   Lowering faults, whole-source refusals and an unoriented block are
    ///   outside the fixture.
    /// - witness: `cells::tests::a_census_reads_each_hole_s_count_in_the_source_s_own_declarations`
    #[inline]
    #[spec(
        captures: [built = self.grammar.is_ok()],
        ensures: |ref ret| !(built && matches!(*ret,
            Maybe::Present(CensusStep::Fault { fault: CensusFault::Grammar(_), .. }))),
    )]
    pub fn step(&mut self) -> Maybe<CensusStep<'_>, walk_step::Absent>
    {
        let reached = match self.traversal.reach() {
            Maybe::Absent(absent) => return Maybe::Absent(absent),
            Maybe::Present(reached) => reached,
        };
        let path = self.traversal.path();
        let fault = match reached {
            Reached::Source => {
                match read_cells(&self.reader, path, self.grammar.as_ref(), &mut self.laid) {
                    Ok(cells) => return Maybe::Present(CensusStep::Source { path, cells }),
                    Err(fault) => fault,
                }
            },
            Reached::Unreadable(error) => CensusFault::Unreadable(error),
            Reached::NoSource => CensusFault::NoSource,
        };
        Maybe::Present(CensusStep::Fault { path, fault })
    }
}

/// Read the source at `path` through `reader`, lay it out into `laid` under
/// `grammar`, lower it, and read the cells of the declarations it writes.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`CensusFault`] that stopped the source.
fn read_cells<'census>(
    reader: &Reader,
    path: &Path,
    grammar: Result<&'census Pbg, &'census PbgError>,
    laid: &'census mut String,
) -> Result<Vec<CellRow>, CensusFault<'census>>
{
    let read = reader.read(path).map_err(CensusFault::Unreadable)?;
    let grammar = grammar.map_err(CensusFault::Grammar)?;
    let unit = component::lay_out(grammar, path, root::classify(path), read.text());
    *laid = unit.text;
    let laid: &'census str = laid;
    let lowered = lower_unit_source(
        grammar,
        SourceText::from(laid),
        &unit.unit,
        &mut LoweringCount::default(),
    )
    .map_err(CensusFault::Composed)?
    .into_lowered();
    let module = match lowered {
        Lowered::Module { module, .. } => module,
        Lowered::Refused(refusal) => return Err(CensusFault::Refused(refusal)),
    };
    let base = usize::from(unit.base);
    let own = SourceText::from(laid.get(base ..).unwrap_or_default());
    let mut rows = Vec::new();
    // Each written rule's arrow, by the cell its face became: one
    // declaration's at a time.
    let mut arrows: Vec<Option<ByteOffset>> = Vec::new();
    for declaration in &module.cells().declarations {
        let start = declaration.at.span.start();
        if usize::from(start) < base {
            continue;
        }
        arrows.clear();
        for &(face, cell) in &declaration.faces {
            if let Some(&Maybe::Present(arrow)) = declaration.rule_spans.get(usize::from(face)) {
                let slot = usize::from(cell);
                if arrows.len() <= slot {
                    arrows.resize(slot.saturating_add(1), None);
                }
                if let Some(entry) = arrows.get_mut(slot) {
                    *entry = Some(arrow.start());
                }
            }
        }
        for (cell, held) in declaration.store.iter() {
            let at = arrows
                .get(usize::from(cell))
                .copied()
                .flatten()
                .unwrap_or(start);
            let LineColumn { line, column } =
                LineColumn::of(own, ByteOffset::from(usize::from(at).saturating_sub(base)));
            rows.push(CellRow {
                line,
                column,
                cell,
                provenance: held.provenance(),
                growth: held.meta().step_growth(),
                holes: held
                    .meta()
                    .vars()
                    .iter()
                    .map(|var| (var.var().hole().clone(), var.contractum().occurrences()))
                    .collect(),
            });
        }
    }
    Ok(rows)
}

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Census;
    use super::CensusFault;
    use super::CensusStep;
    use crate::walk::tests::Scratch;

    #[test]
    fn a_census_reads_each_hole_s_count_in_the_source_s_own_declarations()
    {
        let scratch = Scratch::new(Path::new("census"));
        // `left` keeps `l` and drops `r`; `twice` and `thrice` write `t` two
        // and three times.
        scratch.file(
            Path::new("tree/a-tree.gandr"),
            SourceText::from(
                "pub data Tree : Type {\n  Leaf : Tree;\n  Node : (l : Tree, r : Tree) --> Tree;\n  \
                 oper left(t : Tree) -> Tree;\n  oper twice(t : Tree) -> Tree;\n  oper thrice(t \
                 : Tree) -> Tree;\n  rule left(Leaf) ==> Leaf;\n  rule left(Node(l, r)) ==> \
                 l;\n  rule twice(t) ==> Node(t, t);\n  rule thrice(t) ==> Node(t, Node(t, \
                 t));\n}\n",
            ),
        );
        // The importer lowers over `Tree`, whose cells are the other step's.
        scratch.file(
            Path::new("tree/b-importer.gandr"),
            SourceText::from(
                "import \"./a-tree.gandr\" ;\n\npub data Flag : Type {\n  Off : Flag;\n  On : \
                 Flag;\n  oper flip(f : Flag) -> Flag;\n  rule flip(Off) ==> On;\n  rule \
                 flip(On) ==> Off;\n}\n",
            ),
        );
        let root = scratch.root();
        let missing = root.join("missing.gandr");
        let mut census = Census::new(vec![root.join("tree"), missing.clone()]);
        let mut steps: Vec<(PathBuf, Result<Vec<String>, bool>)> = Vec::new();
        while let Maybe::Present(step) = census.step() {
            steps.push(match step {
                CensusStep::Source { path, cells } => (
                    path.to_path_buf(),
                    Ok(cells.iter().map(ToString::to_string).collect()),
                ),
                CensusStep::Fault { path, fault } => (
                    path.to_path_buf(),
                    Err(matches!(fault, CensusFault::Unreadable(_))),
                ),
            });
        }
        let rows = |lines: &[&str]| Ok(lines.iter().map(ToString::to_string).collect());
        assert_eq!(steps, vec![
            (
                root.join("tree/a-tree.gandr"),
                rows(&[
                    "1:5: cell 0 frame, strictly linear: v 1, beta 1",
                    "1:5: cell 1 frame, strictly linear: v 1, beta 1",
                    "7:19: cell 2 rule, strictly linear: $ret 1",
                    "8:25: cell 3 rule, erasing: l 1, r 0, $ret 1",
                    "9:17: cell 4 rule, duplicating 2: t 2, $ret 1",
                    "10:18: cell 5 rule, duplicating 3: t 3, $ret 1",
                ])
            ),
            (
                root.join("tree/b-importer.gandr"),
                rows(&[
                    "3:5: cell 0 frame, strictly linear: v 1, beta 1",
                    "3:5: cell 1 frame, strictly linear: v 1, beta 1",
                    "7:18: cell 2 rule, strictly linear: $ret 1",
                    "8:17: cell 3 rule, strictly linear: $ret 1",
                ])
            ),
            (missing, Err(true)),
        ]);
        assert!(
            matches!(census.step(), Maybe::Absent(_)),
            "exhaustion is stable"
        );
    }
}
