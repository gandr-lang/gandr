//! A closure's lowering held for the documents laid after it.
//!
//! A document that imports its siblings is lowered as one unit: the sources
//! it reaches, its closure, laid end to end before it. A source lowers alike
//! whatever follows it, so the closure's share of that lowering is the same
//! for every revision of the document. [`ClosureLowering`] parses and lowers
//! the closure once and keeps the lowering suspended at the closure's end;
//! [`ClosureLowering::resume`] lowers a document's tree laid after the
//! closure's on a copy of that state, and answers what [`super::lower_unit`]
//! answers over the same tree and unit. [`ClosureLowering::alone`] answers the
//! closure's own module, which a checker can judge once, and
//! [`ClosureLowering::resume_onto`] lowers a document after the arena that
//! judgement minted into, so the document's nodes follow the checker's, on
//! the closure's origin table carrying the checker's nodes once
//! ([`ClosureLowering::carrying`]).

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_term::Carried;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
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
use crate::description::Sight;
use crate::description::elaborate_roots;
use crate::error::LoweringRefusal;
use crate::form::Piece;
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

/// How a document's tree continues a closure's lowering.
///
/// # Specification
/// trivial.
enum Route<'held>
{
    /// The tree is lowered whole: it does not extend the closure's, or the
    /// lowering it continues would not be the closure's suspended one.
    Whole,
    /// Neither the closure's roots nor the document's read as a module's.
    Empty,
    /// The closure's suspended lowering continues over the added sources.
    Continue
    {
        /// The lowering stopped at the closure's end.
        state: &'held Suspended<'held>,
        /// The description reading of the roots the tree adds.
        described: DescriptionReport,
        /// The top-level forms of the roots the tree adds.
        pieces: Vec<Piece>,
    },
}

/// The arena a document's lowering after a closure mints into.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Base
{
    /// An empty arena: the closure's arena is copied into it first.
    Empty,
    /// The closure's arena with more nodes minted after them.
    Closure,
}

/// What lowering a document onto its closure's arena came to.
///
/// # Specification
/// trivial.
#[expect(
    clippy::large_enum_variant,
    reason = "one per document lowered after a closure, matched at once; the resumed module is \
              the common variant, and boxing it would allocate per keystroke to shrink the rare \
              whole one"
)]
#[derive(Clone, Debug)]
pub enum Onto<'held>
{
    /// The document's sources lowered after the arena's nodes, the closure's
    /// sources not lowered again.
    Resumed(LoweredModule<'held>),
    /// The tree is not one the closure's suspended lowering continues over:
    /// it is lowered whole ([`ClosureLowering::resume`]), into an arena of its
    /// own.
    Whole,
}

/// A closure lowering's origin table, carrying a judgement's nodes.
///
/// The nodes a judgement of the closure's declarations minted are located
/// once ([`ClosureLowering::carrying`]), and every document lowered onto that
/// judgement's arena starts from the table ([`ClosureLowering::resume_onto`]).
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct CarriedOrigins(OriginTable);

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
        let base = if arena.watermark() == CoreArena::new().watermark() {
            Base::Empty
        }
        else {
            // A filled arena is lowered into whole: only an empty one is
            // known to take the closure's copy.
            return lower_unit(
                &held.grammar,
                tree,
                unit,
                arena,
                held.budget,
                held.outermost.clone(),
            );
        };
        match self.route(tree, unit, base)? {
            Route::Whole => lower_unit(
                &held.grammar,
                tree,
                unit,
                arena,
                held.budget,
                held.outermost.clone(),
            ),
            Route::Empty => Ok(empty_module(held.outermost.clone())),
            Route::Continue {
                state,
                described,
                pieces,
            } => {
                arena.clone_from(&state.arena);
                continue_from(
                    (&held.unit, state),
                    (tree, unit),
                    (described, pieces),
                    arena,
                    &state.origins,
                )
            },
        }
    }

    /// The closure's own module and the arena it was lowered into: what the
    /// closure's lowering answers with no source after it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `None` when the closure's lowering stopped before its end, or
    ///   finishing it refuses; otherwise the closure's declarations as
    ///   [`super::lower_unit`] lowers them ahead of any source after them, ids
    ///   included, over a copy of the closure's arena.
    /// - provides: the declarations a checker judges once for every document
    ///   laid after the closure, and the arena it judges them over.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses compare with [`super::lower_unit`] over
    ///   a tree no argument carries; the witness compares.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closure's own module lowers to the leading
    ///   declarations of a document lowered onto its arena, ids included.
    /// - witness: `tests::namespace::a_document_lowered_onto_its_closure_s_arena_follows_its_nodes_776`
    #[inline]
    #[must_use]
    pub fn alone(&self) -> Option<(LoweredModule<'_>, CoreArena)>
    {
        let Prefix::Suspended { ref state, .. } = *self.0.borrow_dependent()
        else {
            return None;
        };
        let arena = state.arena.clone();
        let lowerer = state.lowerer.clone();
        lowerer
            .finish(&arena, state.origins.clone())
            .ok()
            .map(|module| (module, arena))
    }

    /// The closure lowering's origin table carrying `carried` and `binds`,
    /// the nodes a judgement of the closure's declarations minted after its
    /// arena's: built once per judgement, and read by every
    /// [`Self::resume_onto`] after it.
    ///
    /// # Specification
    /// - requires: every node `carried` and `binds` name as minted follows the
    ///   nodes of the closure's arena ([`Self::alone`]), as
    ///   [`OriginTable::carry`] requires of the closure's table.
    /// - ensures: the closure's suspended table with `carried` and `binds`
    ///   recorded as [`OriginTable::carry`] records them; an empty table when
    ///   the closure's lowering stopped before its end, which
    ///   [`Self::resume_onto`] never reads.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses compare with a carry over a copy of a
    ///   table no argument carries; the witness locates a carried node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::resume_onto`].
    /// - witness: `tests::namespace::a_document_lowered_onto_its_closure_s_arena_follows_its_nodes_776`
    #[inline]
    #[must_use]
    pub fn carrying(
        &self,
        carried: &[Carried],
        binds: &[(ValueId, ComputationId)],
    ) -> CarriedOrigins
    {
        let Prefix::Suspended { ref state, .. } = *self.0.borrow_dependent()
        else {
            return CarriedOrigins(OriginTable::new());
        };
        let mut origins = state.origins.clone();
        origins.carry(carried, binds);
        CarriedOrigins(origins)
    }

    /// Lower `tree`, the closure's tree with a document's laid after it, as
    /// `unit` lays it out, after the nodes of `arena`, which holds the
    /// closure's arena with more nodes minted after it: the closure's
    /// lowering resumed on a copy of `origins`, which locates those nodes
    /// ([`Self::carrying`]), only the sources after the closure's lowered.
    ///
    /// # Specification
    /// - requires: `arena` is [`Self::alone`]'s arena with any nodes minted
    ///   after its own; `origins` is [`Self::carrying`]'s table of the nodes
    ///   minted after them.
    /// - ensures: [`Onto::Whole`], `arena` untouched, when `tree` is not one
    ///   [`Self::resume`] would continue the closure's lowering over; otherwise
    ///   the module [`Self::resume`] answers, the closure's declarations and
    ///   its arena rows unchanged, its origin table a copy of `origins` with
    ///   the later sources' nodes, which are minted after `arena`'s; or the
    ///   refusal it answers.
    /// - provides: a document's lowering that a judgement of the closure's
    ///   declarations over `arena` continues, the nodes that judgement's
    ///   elaborations minted located where their sources are written, without
    ///   locating them again.
    /// - fails: as [`Self::resume`].
    /// - panics: none.
    /// - executable: none — as [`Self::resume`].
    ///
    /// # Errors
    /// As [`Self::resume`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document lowered onto its closure's arena after
    ///   more nodes keeps the closure's declarations and arena rows, locates a
    ///   node minted after them where its source is written, and reads as the
    ///   whole lowering does once its own ids are set aside.
    /// - witness: `tests::namespace::a_document_lowered_onto_its_closure_s_arena_follows_its_nodes_776`
    #[inline]
    pub fn resume_onto<'held>(
        &'held self,
        tree: &SyntaxTree<'held>,
        unit: &Unit,
        arena: &mut CoreArena,
        origins: &CarriedOrigins,
    ) -> Result<Onto<'held>, LoweringRefusal<'held>>
    {
        match self.route(tree, unit, Base::Closure)? {
            Route::Whole | Route::Empty => Ok(Onto::Whole),
            Route::Continue {
                state,
                described,
                pieces,
            } => continue_from(
                (self.unit(), state),
                (tree, unit),
                (described, pieces),
                arena,
                &origins.0,
            )
            .map(Onto::Resumed),
        }
    }

    /// How `tree`, laid out as `unit`, continues the closure's lowering into
    /// an arena that is `base`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Route::Whole`] when `tree` does not extend the closure's
    ///   tree over its text with `unit` laying its sources out first and more
    ///   after them, or, onto the closure's arena, when the closure's lowering
    ///   stopped before its end; otherwise the refusal the whole lowering
    ///   answers first, [`Route::Empty`] when no root reads as a module's, or
    ///   the suspended lowering with the added roots' descriptions and forms.
    /// - fails: the refusal the whole lowering answers before any source after
    ///   the closure's is lowered: the closure's, then the added roots', phase
    ///   by phase.
    /// - panics: none.
    /// - executable: none — the clauses compare the route with the whole
    ///   lowering over a tree no argument carries; the witness resumes it and
    ///   compares.
    ///
    /// # Errors
    /// As the specification's fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::resume`].
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    fn route<'held>(
        &'held self,
        tree: &SyntaxTree<'held>,
        unit: &Unit,
        base: Base,
    ) -> Result<Route<'held>, LoweringRefusal<'held>>
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
            && closure
                .positions()
                .all(|position| tree.node(position) == closure.node(position))
            && usize::from(tree.node_count()) > read;
        let prefix = self.0.borrow_dependent();
        let suspended = matches!(*prefix, Prefix::Suspended { .. });
        if !extends || (base == Base::Closure && !suspended) {
            return Ok(Route::Whole);
        }
        let added = tree
            .roots()
            .get(closure.roots().len() ..)
            .unwrap_or_default();
        // The order the whole lowering refuses in: every root's shape, then
        // every root's descriptions, then every root's forms, then each
        // source; the closure's first at each phase.
        let closure_rooted = match *prefix {
            Prefix::Misshapen(refusal) => return Err(refusal),
            Prefix::Halted { rooted, .. } | Prefix::Suspended { rooted, .. } => rooted,
        };
        if (closure_rooted, rooted(pbg, tree, added)?) == (Rooted(false), Rooted(false)) {
            return Ok(Route::Empty);
        }
        let halted = |at: Stage| match *prefix {
            Prefix::Halted { stage, refusal, .. } if stage == at => Err(refusal),
            Prefix::Misshapen(_) | Prefix::Halted { .. } | Prefix::Suspended { .. } => Ok(()),
        };
        halted(Stage::Collection)?;
        let (first, prior) = match *prefix {
            Prefix::Suspended { ref state, .. } => (
                NominalSerial::from(
                    u64::try_from(state.lowerer.collected.descriptions.len()).unwrap_or(u64::MAX),
                ),
                Some(&state.lowerer.collected.descriptions),
            ),
            // A refused closure answers its refusal below, however the
            // document's descriptions are numbered and whatever it includes.
            Prefix::Misshapen(_) | Prefix::Halted { .. } => (NominalSerial::from(0_u64), None),
        };
        let none = BTreeMap::new();
        let mut described = DescriptionReport::default();
        elaborate_roots(pbg, tree, added, first, &mut described, Sight {
            unit,
            prior: prior.unwrap_or(&none),
        })?;
        halted(Stage::Pieces)?;
        let pieces = pieces_under(pbg, tree, added)?;
        halted(Stage::Lowering)?;
        let Prefix::Suspended { ref state, .. } = *prefix
        else {
            // Every other prefix answered above.
            return Ok(Route::Whole);
        };
        Ok(Route::Continue {
            state,
            described,
            pieces,
        })
    }
}

/// Continue `state`, the suspended lowering of the closure whose sources
/// `closure` lays out, over `tree` laid out as `unit`, the added roots read as
/// `described` and `pieces`, minting after `arena`'s nodes on a copy of
/// `origins`.
///
/// # Specification
/// - requires: `arena` holds `state`'s arena with any nodes minted after its
///   own, and `origins` is `state`'s table locating them
///   ([`ClosureLowering::carrying`]), or `state`'s own when none were; `tree`
///   and `unit` extend the closure's, and `described` and `pieces` are the
///   added roots' readings ([`ClosureLowering::route`]).
/// - ensures: on a copy of the lowering's state and of `origins`, the sources
///   after the closure's lowered into `arena` after its nodes, and the module
///   finished.
/// - fails: as [`super::lower_unit`], raised by a source after the closure's.
/// - panics: none.
/// - executable: none — the clauses compare the module with the whole
///   lowering's over a tree no argument carries; the witnesses resume it and
///   compare.
///
/// # Errors
/// As the specification's fails clause.
///
/// # Adequacy
/// - hypothesis: L3 — as [`ClosureLowering::resume`].
/// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
/// - witness: `tests::namespace::a_document_lowered_onto_its_closure_s_arena_follows_its_nodes_776`
fn continue_from<'held>(
    (closure, state): (&Unit, &'held Suspended<'held>),
    (tree, unit): (&SyntaxTree<'held>, &Unit),
    (described, pieces): (DescriptionReport, Vec<Piece>),
    arena: &mut CoreArena,
    origins: &OriginTable,
) -> Result<LoweredModule<'held>, LoweringRefusal<'held>>
{
    let lowered = closure.sources().len();
    let mut lowerer: Lowerer<'_, 'held> = state.lowerer.clone();
    let mut origins = origins.clone();
    lowerer.widen(tree, unit, described);
    let mut sink = Sink::new(arena, &mut origins, state.tables.clone());
    for (source, own) in source_pieces(unit, pieces)
        .into_iter()
        .enumerate()
        .skip(lowered)
    {
        lowerer.lower_source(SourceIndex::from(source), own, &mut sink)?;
    }

    lowerer.finish(arena, origins)
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
    lowerer.plans.share();

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
