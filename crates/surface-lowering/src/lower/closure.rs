//! A closure's lowering held for the documents laid after it.
//!
//! A document that imports its siblings is lowered as one unit: the sources
//! it reaches, its closure, laid end to end before it. A source lowers alike
//! whatever follows it, so the closure's share of that lowering is the same
//! for every revision of the document. [`ClosureLowering`] parses and lowers
//! the closure once and keeps the lowering suspended at the closure's end;
//! [`ClosureLowering::resume`] lowers a document's tree laid after the
//! closure's on a copy of that state, and answers what [`super::lower_unit`]
//! answers over the same tree and unit.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::sync::Arc;
use core::fmt;

use gandr_core_term::CoreArena;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use gandr_theory_levitation::NominalSerial;

use self::cells::Lowered;
use self::cells::Parsed;
use super::Fuel;
use super::Lowerer;
use super::LoweringBudget;
use super::Rooted;
use super::Sink;
use super::SinkTables;
use super::empty_module;
use super::lower_unit;
use super::rooted;
use crate::description::DescriptionReport;
use crate::description::elaborate_roots;
use crate::error::LoweringRefusal;
use crate::module::LoweredModule;
use crate::module::begin_collection;
use crate::module::pieces_under;
use crate::module::root_pieces;
use crate::module::source_pieces;
use crate::namespace::Recognition;
use crate::origin::OriginTable;
use crate::unit::SourceIndex;
use crate::unit::Unit;

/// What a closure's lowering is built over.
///
/// # Specification
/// trivial.
struct Held
{
    /// The grammar the closure's text is parsed under.
    grammar: Arc<Pbg>,
    /// The closure's text: its sources laid end to end.
    text: String,
    /// The closure's sources, in the order the unit admits them.
    unit: Unit,
    /// The allowance the lowering is bounded by.
    budget: LoweringBudget,
    /// The outermost scope the lowering declares its names over.
    outermost: Recognition,
}

/// The phase of a closure's lowering a refusal stopped.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stage
{
    /// Reading the descriptions.
    Collection,
    /// Reading the roots' top-level forms.
    Pieces,
    /// Lowering a source.
    Lowering,
}

/// A closure's lowering stopped at the closure's end: everything a later
/// source's lowering continues from.
///
/// # Specification
/// trivial.
#[derive(Clone)]
struct Suspended<'closure>
{
    /// The lowering's state.
    lowerer: Lowerer<'closure, 'closure>,
    /// The arena the closure's sources minted into.
    arena: CoreArena,
    /// Where each node they minted came from.
    origins: OriginTable,
    /// The mint sweep's tables beside the arena.
    tables: SinkTables,
}

/// What lowering a closure came to.
///
/// # Specification
/// trivial.
enum Prefix<'closure>
{
    /// A root of the closure is not a module's; the unit is refused by it,
    /// whatever follows.
    Misshapen(LoweringRefusal<'closure>),
    /// The closure's roots read, and its lowering refused at `stage`.
    Halted
    {
        /// Whether a root of the closure reads as a module's.
        rooted: Rooted,
        /// The phase the refusal stopped.
        stage: Stage,
        /// The refusal.
        refusal: LoweringRefusal<'closure>,
    },
    /// The closure's sources lowered.
    Suspended
    {
        /// Whether a root of the closure reads as a module's.
        rooted: Rooted,
        /// The lowering, stopped at the closure's end.
        state: Box<Suspended<'closure>>,
    },
}

/// The self-referential cells a closure's lowering is held in: the closure's
/// text with its parse, and that parse with its lowering.
#[expect(
    clippy::mem_forget,
    reason = "the cells self_cell generates forget their construction guard once the dependent \
              is built: the guard frees the joint allocation only when building unwinds"
)]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        recursive_owned_pointer,
        reason = "self_cell names each cell as a marker type parameter of the cell it holds, not \
                  an owning link: the cell owns one joint allocation of the owner and the \
                  dependent, and its drop frees that allocation once without recursing"
    )
)]
mod cells
{
    use gandr_surface_syntax::SyntaxTree;
    use self_cell::self_cell;

    use super::Held;
    use super::Prefix;

    self_cell!(
        /// The closure's text with its parse.
        ///
        /// # Specification
        /// trivial.
        pub(super) struct Parsed
        {
            owner: Held,

            #[covariant]
            dependent: SyntaxTree,
        }
    );

    self_cell!(
        /// The closure's parse with its lowering.
        ///
        /// # Specification
        /// trivial.
        pub(super) struct Lowered
        {
            owner: Parsed,

            #[covariant]
            dependent: Prefix,
        }
    );
}

/// A closure's lowering, held for the documents laid after it: the closure's
/// text, its parse, and its sources lowered, the lowering stopped at the
/// closure's end.
///
/// # Specification
/// - requires: the closure's text lays its unit's sources end to end.
/// - ensures: [`Self::resume`] answers what [`super::lower_unit`] answers over
///   the tree and unit it is given.
/// - provides: a document's lowering beside the siblings it imports, at the
///   cost of the document's own sources.
/// - executable: none — a data type; [`Self::resume`] states the comparison.
///
/// # Adequacy
/// - hypothesis: L3 — a document laid after its closure, resumed on one closure
///   lowering twice and lowered whole, answers one module and one arena each
///   time.
/// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
#[repr(transparent)]
pub struct ClosureLowering(Lowered);

impl ClosureLowering
{
    /// The closure `text` lays out as `unit`, parsed by `parse` under
    /// `grammar` and lowered within `budget` over `outermost`.
    ///
    /// # Specification
    /// - requires: `parse` answers the tree of the text it is given under the
    ///   grammar it is given.
    /// - ensures: the closure's tree is `parse`'s, and its sources are lowered
    ///   as [`super::lower_unit`] lowers them before any source after them.
    /// - provides: the state [`Self::resume`] continues from.
    /// - fails: `parse`'s refusal; a lowering refusal is held for
    ///   [`Self::resume`] to answer.
    /// - panics: none.
    /// - executable: none — the clauses compare the lowering with
    ///   [`super::lower_unit`] over a tree no argument carries; the witness
    ///   resumes it and compares.
    ///
    /// # Errors
    /// The refusal `parse` returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type.
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[inline]
    pub fn new<E, Parse>(
        grammar: Arc<Pbg>,
        text: String,
        unit: Unit,
        budget: LoweringBudget,
        outermost: Recognition,
        parse: Parse,
    ) -> Result<Self, E>
    where
        Parse: for<'text> FnOnce(&'text Pbg, SourceText<'text>) -> Result<SyntaxTree<'text>, E>,
    {
        let held = Held {
            grammar,
            text,
            unit,
            budget,
            outermost,
        };
        let parsed = Parsed::try_new(held, |held| {
            parse(&held.grammar, SourceText::from(held.text.as_str()))
        })?;

        Ok(Self(Lowered::new(parsed, |parsed| {
            suspend(parsed.borrow_owner(), parsed.borrow_dependent())
        })))
    }

    /// The closure's tree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn tree(&self) -> &SyntaxTree<'_>
    {
        self.0.borrow_owner().borrow_dependent()
    }

    /// The closure's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn text(&self) -> SourceText<'_>
    {
        SourceText::from(self.0.borrow_owner().borrow_owner().text.as_str())
    }

    /// The closure's sources.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unit(&self) -> &Unit
    {
        &self.0.borrow_owner().borrow_owner().unit
    }

    /// The grammar the closure is parsed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn grammar(&self) -> &Pbg
    {
        &self.0.borrow_owner().borrow_owner().grammar
    }

    /// Lower `tree`, the closure's tree with a document's laid after it, as
    /// `unit` lays it out, into `arena`: the closure's lowering resumed on a
    /// copy, only the sources after the closure's lowered.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`super::lower_unit`] over `tree` and `unit` into `arena`,
    ///   within the closure's budget over its outermost scope. When `tree`'s
    ///   first nodes are the closure's tree's, over its text, `unit`'s first
    ///   sources the closure's with one more after them, and `arena` empty, the
    ///   closure's sources are not lowered again: `arena` becomes a copy of the
    ///   closure's with the later sources minted after it; otherwise `tree` is
    ///   lowered whole.
    /// - provides: a document's lowering at the cost of its own source.
    /// - fails: as [`super::lower_unit`].
    /// - panics: none.
    /// - executable: none — the answer is [`super::lower_unit`]'s, which the
    ///   witness compares; computing that here would undo the saving.
    ///
    /// # Errors
    /// As [`super::lower_unit`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document resumed twice on one closure lowering and
    ///   lowered whole answers one module and one arena, a tree that does not
    ///   extend the closure's is lowered whole, and a document that refuses the
    ///   unit answers the whole lowering's refusal.
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[inline]
    pub fn resume<'held>(
        &'held self,
        tree: &SyntaxTree<'held>,
        unit: &Unit,
        arena: &mut CoreArena,
    ) -> Result<LoweredModule<'held>, LoweringRefusal<'held>>
    {
        let held = self.0.borrow_owner().borrow_owner();
        let closure = self.tree();
        let pbg: &Pbg = &held.grammar;
        let lowered = held.unit.sources().len();
        let read = usize::from(closure.node_count());
        let extends = tree.grammar() == pbg.fingerprint()
            && tree.source().as_ref().starts_with(held.text.as_str())
            && tree.roots().len() > closure.roots().len()
            && tree.roots().starts_with(closure.roots())
            && unit.sources().get(.. lowered) == Some(held.unit.sources())
            && unit.sources().len() > lowered
            && arena.watermark() == CoreArena::new().watermark()
            && closure
                .positions()
                .all(|position| tree.node(position) == closure.node(position))
            && usize::from(tree.node_count()) > read;
        if !extends {
            return lower_unit(pbg, tree, unit, arena, held.budget, held.outermost.clone());
        }
        let added = tree
            .roots()
            .get(closure.roots().len() ..)
            .unwrap_or_default();
        let prefix = self.0.borrow_dependent();
        // The order the whole lowering refuses in: every root's shape, then
        // every root's descriptions, then every root's forms, then each
        // source; the closure's first at each phase.
        let closure_rooted = match *prefix {
            Prefix::Misshapen(refusal) => return Err(refusal),
            Prefix::Halted { rooted, .. } | Prefix::Suspended { rooted, .. } => rooted,
        };
        if (closure_rooted, rooted(pbg, tree, added)?) == (Rooted(false), Rooted(false)) {
            return Ok(empty_module(held.outermost.clone()));
        }
        let halted = |at: Stage| match *prefix {
            Prefix::Halted { stage, refusal, .. } if stage == at => Err(refusal),
            Prefix::Misshapen(_) | Prefix::Halted { .. } | Prefix::Suspended { .. } => Ok(()),
        };
        halted(Stage::Collection)?;
        let first = match *prefix {
            Prefix::Suspended { ref state, .. } => NominalSerial::from(
                u64::try_from(state.lowerer.collected.descriptions.len()).unwrap_or(u64::MAX),
            ),
            // A refused closure answers its refusal below, however the
            // document's descriptions are numbered.
            Prefix::Misshapen(_) | Prefix::Halted { .. } => NominalSerial::from(0_u64),
        };
        let mut described = DescriptionReport::default();
        elaborate_roots(pbg, tree, added, first, &mut described)?;
        halted(Stage::Pieces)?;
        let pieces = pieces_under(pbg, tree, added)?;
        halted(Stage::Lowering)?;
        let Prefix::Suspended { ref state, .. } = *prefix
        else {
            // Every other prefix answered above.
            return lower_unit(pbg, tree, unit, arena, held.budget, held.outermost.clone());
        };
        let Suspended {
            lowerer,
            arena: minted,
            mut origins,
            tables,
        } = Suspended::clone(state);
        let mut lowerer: Lowerer<'_, 'held> = lowerer;
        lowerer.widen(tree, unit, described);
        *arena = minted;
        let mut sink = Sink::new(arena, &mut origins, tables);
        for (source, own) in source_pieces(unit, pieces)
            .into_iter()
            .enumerate()
            .skip(lowered)
        {
            lowerer.lower_source(SourceIndex::from(source), own, &mut sink)?;
        }

        lowerer.finish(arena, origins)
    }
}

impl fmt::Debug for ClosureLowering
{
    /// The closure's length and sources.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_struct("ClosureLowering")
            .field("text", &<&str>::from(self.text()).len())
            .field("unit", self.unit())
            .finish_non_exhaustive()
    }
}

/// Lower the closure `tree` parses `held`'s text to, stopping at its end.
///
/// # Specification
/// - requires: `tree` is the parse of `held`'s text under its grammar.
/// - ensures: the closure's roots misshapen, its lowering halted at the phase
///   that refused, or its sources lowered as [`super::lower_unit`] lowers them,
///   in the unit's order.
/// - fails: never; a refusal is held in the prefix.
/// - panics: none.
/// - executable: none — the clauses compare the prefix with
///   [`super::lower_unit`] over the same tree, which the type's witness does.
///
/// # Adequacy
/// - hypothesis: L3 — as [`ClosureLowering`].
/// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
fn suspend<'closure>(
    held: &'closure Held,
    tree: &'closure SyntaxTree<'closure>,
) -> Prefix<'closure>
{
    let pbg: &Pbg = &held.grammar;
    if tree.grammar() != pbg.fingerprint() {
        return Prefix::Misshapen(LoweringRefusal::GrammarMismatch {
            tree: tree.grammar(),
            grammar: pbg.fingerprint(),
        });
    }
    let rooted = match rooted(pbg, tree, tree.roots()) {
        Ok(rooted) => rooted,
        Err(refusal) => return Prefix::Misshapen(refusal),
    };
    let halted = |stage, refusal| Prefix::Halted {
        rooted,
        stage,
        refusal,
    };
    let collected = match begin_collection(pbg, tree, &held.unit) {
        Ok(collected) => collected,
        Err(refusal) => return halted(Stage::Collection, refusal),
    };
    let pieces = match root_pieces(pbg, tree) {
        Ok(pieces) => pieces,
        Err(refusal) => return halted(Stage::Pieces, refusal),
    };
    let mut lowerer = Lowerer::new(
        pbg,
        tree,
        collected,
        Fuel::new(held.budget),
        held.outermost.clone(),
    );
    let mut arena = CoreArena::new();
    let mut origins = OriginTable::new();
    let mut sink = Sink::new(&mut arena, &mut origins, SinkTables::new());
    for (source, own) in source_pieces(&held.unit, pieces).into_iter().enumerate() {
        if let Err(refusal) = lowerer.lower_source(SourceIndex::from(source), own, &mut sink) {
            return halted(Stage::Lowering, refusal);
        }
    }
    let tables = sink.into_tables();

    Prefix::Suspended {
        rooted,
        state: Box::new(Suspended {
            lowerer,
            arena,
            origins,
            tables,
        }),
    }
}
