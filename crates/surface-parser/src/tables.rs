//! The molder's tables: admission by tile sets, push classes and window
//! classes, read off the grammar's tile automaton.
//!
//! The molder weighs every candidate of a token by dry runs: it pushes the
//! candidate, reads the obligations the push flags, and rolls back; a tie
//! the push leaves open it weighs by the window of tokens after it, molding
//! each tied opener's window greedily. The verdicts are the dry runs'. What
//! the tables decide is which dry runs are the same dry run.
//!
//! # Admission
//!
//! [`Admission`] is [`MeldState::admits_at`] composed from the grammar's tile
//! sets: the words of the sets a context admits from — what fills the
//! expected sort, what an operand head admits, the first mids where no form
//! is open — are united once per word of the menu, and each candidate is one
//! bit test, a continuation also one adjacency search against the open
//! frontier. The answer is `admits_at`'s for every mold. Composing the
//! context reads a tile set per admitting context, which a menu of a few
//! molds does not repay, so the molder composes it only for a menu wider
//! than [`ADMISSION_MENU`] and admits a narrower one by `admits_at` itself.
//!
//! # Push classes
//!
//! A push reads of the incoming tile its observation class (the grammar's
//! [`Observation`]) and whether it continues each open frontier the push
//! consults: the nearest, and below it every frontier the push may close on
//! the way, the completable ones and the whole required tails. Two
//! candidates with the same observation and the same continuation bits over
//! that [`SettleChain`] flag the same obligations when pushed, and leave the
//! same completion obligations; the [`PushKey`] names the pair, and the
//! molder dry-runs one candidate per key. The chain is read only for a
//! decision two of whose candidates share an observation class; otherwise
//! every candidate keys alone.
//!
//! # Window classes
//!
//! A tied opener's window depends on the opener only through what the window
//! reads of it and of the tiles it continues with: its push key, and, at
//! each later token of the window, which of its same-form successors the
//! token's labels admit — each read, recursively, the same way. That is a
//! derivative of the opener in the grammar's tile automaton, driven by the
//! window's tokens, with every position a successor may be skipped to: the
//! [`WindowClasses`] signature. Openers whose signatures and push keys
//! agree mold their windows alike, so the window of the least decides for
//! all of them, and the molder molds one window per class. Openers share a
//! window only when their push keys agree, so the signatures are computed
//! only for a tie two of whose openers' keys do.
//!
//! Two facts of a successor's identity, not just its class, can reach a
//! window, and both are accounted. A successor that can open its form is
//! also in the token's fresh menu, where every opener's world meets it, so
//! the signature names it by identity. A token none of whose fresh molds
//! and none of whose open frontier's successors carries its label is
//! gathered from its whole declared menu, where every successor of every
//! open frontier meets every opener's; a window that gathers so is exposed,
//! and the openers of its class mold their own windows.
//!
//! The signatures are canonical numbers: the window's nodes, one per
//! successor and position reached, are numbered level by level from the
//! window's end, each by its encoding — its observation and the numbered
//! successors at each later position — so two nodes share a number exactly
//! when their encodings agree. No hash decides equality.
//!
//! # Correctness
//!
//! The molder's verdicts with the tables are the dry runs' verdicts: a push
//! class's members flag what its representative flags, a window class's
//! members mold windows whose obligations the representative's equal, and
//! the window order, least mold first with a later window winning only by
//! fewer obligations, keeps the least of a class ahead of the rest. The
//! argument rests on the observation classes holding everything the melder
//! reads of a pushed tile; [`MoldVerdicts::Differential`] checks it at every
//! decision, and the differential witness runs it over the corpus, the drop
//! matrix and the editor scenario.
//!
//! # Decision
//!
//! The tables decide which dry runs and which windows are one, and the
//! melder still reaches every verdict, once per class: the shape is exact by
//! construction wherever the observation classes hold everything the melder
//! reads, and the witness checks that they do. One-token-drop recovery is
//! therefore the dry runs' exactly — the floor; repairs competing with the
//! opener windows, which would improve some four thousand drop variants, are
//! not built here.
//!
//! - Alternatives: the dry runs kept, one per candidate and one window per tied
//!   opener, which is the procedure the tables replace and stays in the tree as
//!   their oracle ([`MoldVerdicts::DryRuns`]); the repair of a stray against
//!   the open form's expectation set (skip it, or insert one expected tile),
//!   held because the declared menu's partial-form readings are what recover a
//!   dropped opener and the repair loses them on thousands of drop variants;
//!   verdicts computed by the automaton alone — a transition table advancing
//!   every opener's window at once, and an edit-distance automaton (Schulz and
//!   Mihov's Levenshtein automata, or Myers' bit-parallel matching) scoring the
//!   one-edit repairs — which cannot equal the dry runs' verdicts, because a
//!   window's verdict is the obligation count the melder leaves after molding
//!   it greedily, and that reads precedence, closing and completion no distance
//!   over tile sequences carries. Here the derivative names which windows
//!   agree, and its reach to every later position is the one-error closure: a
//!   skipped token, or a stray mid between two tiles, still lands its
//!   successors in the same nodes.
//! - Reversal: a fact the melder reads of a pushed tile that the observation
//!   classes do not carry shows as a disagreement in the witness and becomes a
//!   component of the reading; a grammar whose openers stop collapsing into few
//!   window classes makes a verdict table worth its build. The expectation-set
//!   repair stays held, and a table-backed window cheap enough that context
//!   direction buys nothing retires it as a cost measure; as a competitor of
//!   the opener windows it is the ceiling's open step.
//!
//! [`MoldVerdicts::DryRuns`]: crate::MoldVerdicts::DryRuns
//! [`MoldVerdicts::Differential`]: crate::MoldVerdicts::Differential
//! [`ADMISSION_MENU`]: crate::mold::ADMISSION_MENU

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::MoldSet;
use gandr_surface_grammar::MoldWord;
use gandr_surface_grammar::MoldWordIndex;
use gandr_surface_grammar::Observation;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::TileSet;
use gandr_surface_syntax::MoldId;

use crate::meld::Frontier;
use crate::meld::MeldState;
use crate::meld::MoldAdmissibility;
use crate::mold::CandidateLabel;
use crate::mold::TokenLabels;

/// The most frontiers a [`SettleChain`] names; a longer chain leaves every
/// candidate its own push class.
const CHAIN_CAPACITY: usize = 64;

/// The admission context of one token: [`MeldState::admits_at`] read off the
/// grammar's tile sets.
///
/// # Specification
/// - requires: built from the [`Frontier`] of the state its candidates are
///   admitted against, before any mutation.
/// - ensures: [`admits`](Self::admits) answers as `admits_at` does for that
///   frontier.
/// - panics: none.
/// - executable: none — a context value; [`admits`](Self::admits) carries the
///   executable clause.
///
/// # Adequacy
/// - hypothesis: L3 — the differential witness compares the admitted menu with
///   `admits_at`'s at every decision of the corpus, the drop matrix and the
///   editor scenario; a set missing from the union or a continuation read
///   against the wrong frontier shows as a disagreement.
/// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
#[derive(Clone, Debug)]
pub struct Admission<'pbg>
{
    /// The grammar whose tile sets admit.
    pbg: &'pbg Pbg,
    /// How many molds the grammar's table holds; an id at or past it is
    /// admitted unfiltered.
    molds: usize,
    /// The nearest open frontier, which a mid or an end continues.
    open: Option<MoldId>,
    /// The sets every candidate is admitted from by its kind and sort; an
    /// unselected set is empty.
    sets: [MoldSet<'pbg>; 7],
    /// The mids and ends, which the open frontier admits by adjacency.
    continuations: MoldSet<'pbg>,
    /// Whether an item-sort `(` is refused: an operand head at an
    /// expression slot.
    refuses_item_paren: bool,
    /// The last word composed, with its index.
    cached: Option<(MoldWordIndex, MoldWord)>,
}

impl<'pbg> Admission<'pbg>
{
    /// The admission context of `frontier` over `pbg`.
    ///
    /// # Specification
    /// - requires: `frontier` is the state's admissibility frontier.
    /// - ensures: admits from the fills of the expected sort and of items and
    ///   the prefix operators; with an operand head, also from the operators
    ///   that extend it and the absorbing starts of its sort and of items; with
    ///   no open form, also from the first mids; refuses an item `(` after an
    ///   operand head at an expression slot.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Admission`].
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[spec(ensures: |ret| ret.open == frontier.open && ret.refuses_item_paren == (bool::from(frontier.head_operand) && frontier.expected == Sort::Expression))]
    pub(crate) fn new(
        pbg: &'pbg Pbg,
        frontier: &Frontier,
    ) -> Self
    {
        let head_operand = bool::from(frontier.head_operand);
        let selected = |set: TileSet, held: bool| {
            if held {
                pbg.tile_set(set)
            }
            else {
                MoldSet::default()
            }
        };
        Self {
            pbg,
            molds: pbg.mold_count().0,
            open: frontier.open,
            sets: [
                pbg.tile_set(TileSet::Fills(frontier.expected)),
                pbg.tile_set(TileSet::Fills(Sort::Item)),
                pbg.tile_set(TileSet::Prefixes),
                selected(TileSet::LeftOperators, head_operand),
                frontier.head_sort.map_or_else(MoldSet::default, |sort| {
                    selected(TileSet::Absorbs(sort), head_operand)
                }),
                selected(TileSet::Absorbs(Sort::Item), head_operand),
                selected(TileSet::FirstMids, frontier.open.is_none()),
            ],
            continuations: pbg.tile_set(TileSet::Continuations),
            refuses_item_paren: head_operand && frontier.expected == Sort::Expression,
            cached: None,
        }
    }

    /// Whether `mold` is admissible in this context.
    ///
    /// # Specification
    /// - requires: the context was built from the state's frontier.
    /// - ensures: true for an id past the table; false for a refused item `(`;
    ///   otherwise true exactly when the mold is in a selected set or is a mid
    ///   or end the open frontier continues.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Admission`].
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[spec(ensures: |ret| self.pbg.mold(mold).is_ok() || bool::from(ret))]
    pub(crate) fn admits(
        &mut self,
        mold: MoldId,
    ) -> MoldAdmissibility
    {
        let at = MoldWordIndex::of(mold);
        let word = match self.cached {
            Some((cached, word)) if cached == at => word,
            Some(_) | None => {
                let word = self
                    .sets
                    .iter()
                    .fold(MoldWord::default(), |word, set| word | set.word(at));
                self.cached = Some((at, word));
                word
            },
        };
        let admitted = bool::from(word.contains(mold))
            || self.open.is_some_and(|open| {
                bool::from(self.continuations.word(at).contains(mold))
                    && bool::from(self.pbg.molds_adjacent(open, mold))
            });
        if admitted {
            let refused = self.refuses_item_paren
                && self
                    .pbg
                    .mold(mold)
                    .is_ok_and(|def| def.sort == Sort::Item && def.label == "(");
            return MoldAdmissibility::from(!refused);
        }
        // An id past the table is in no set; push routes it to the unmolded
        // path, so it is never filtered.
        MoldAdmissibility::from(
            usize::try_from(u32::from(mold)).map_or(true, |index| index >= self.molds),
        )
    }
}

/// The open frontiers a push may consult, nearest first: the nearest, and
/// below it every frontier a push can close before meeting the next — the
/// completable ones and the required tails — down to and including the
/// first that is neither.
///
/// # Specification
/// - requires: [`read`](Self::read) from the state whose candidates are keyed,
///   before any mutation, or [`unkey`](Self::unkey).
/// - ensures: names at most [`CHAIN_CAPACITY`] frontiers; a longer chain, or
///   one unkeyed, keys every candidate by itself.
/// - panics: none.
/// - executable: none — a reused buffer; [`read`](Self::read) and
///   [`key`](Self::key) carry the clauses.
///
/// # Adequacy
/// - hypothesis: L3 — the differential witness compares the verdicts the push
///   classes reach with the dry runs' at every decision; a chain cut short
///   merges candidates a deeper frontier tells apart.
/// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
#[derive(Clone, Debug, Default)]
pub struct SettleChain
{
    /// The chain's frontier molds, nearest first.
    molds: Vec<MoldId>,
    /// Whether keys name classes: the chain was read whole.
    keyed: bool,
}

/// Whether a candidate continues each frontier of a [`SettleChain`]: bit `i`
/// for the chain's `i`th frontier.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ChainAdjacency(u64);

/// What a push reads of its candidate: its observation class and its
/// continuation bits over the settle chain, or the candidate itself when the
/// chain overflowed or the mold is past the table.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PushKey
{
    /// A class of candidates that push alike.
    Class
    {
        /// The candidate's observation class.
        observation: Observation,
        /// The candidate's continuation bits.
        adjacency: ChainAdjacency,
    },
    /// A candidate keyed by itself.
    Alone(MoldId),
}

impl SettleChain
{
    /// Read the chain of `state` over `pbg`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the chain holds the open frontiers from the nearest down to
    ///   and including the first that is neither completable nor a required
    ///   tail, and keys by class; or, when the walk reaches past the first
    ///   [`CHAIN_CAPACITY`] of them, keys every candidate by itself.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`SettleChain`].
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[spec(ensures: |()| self.molds.len() <= CHAIN_CAPACITY)]
    pub(crate) fn read(
        &mut self,
        pbg: &Pbg,
        state: &MeldState<'_>,
    )
    {
        self.molds.clear();
        self.keyed = true;
        for mold in state.open_frontier_molds() {
            if self.molds.len() == CHAIN_CAPACITY {
                self.keyed = false;
                break;
            }
            self.molds.push(mold);
            let passes = bool::from(pbg.mold_is_form_last(mold))
                || bool::from(pbg.mold_has_required_tail(mold));
            if !passes {
                break;
            }
        }
    }

    /// Key every candidate by itself until the next [`read`](Self::read):
    /// for a decision where no two candidates can share a class.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the chain is empty and keys no class.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`SettleChain`]; a stale chain left keyed would
    ///   key a later decision's candidates against frontiers the state no
    ///   longer holds.
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[spec(ensures: |()| self.molds.is_empty() && !self.keyed)]
    pub(crate) fn unkey(&mut self)
    {
        self.molds.clear();
        self.keyed = false;
    }

    /// The push key of `mold` over this chain.
    ///
    /// # Specification
    /// - requires: the chain was read from the state `mold` is weighed on, or
    ///   unkeyed.
    /// - ensures: the mold itself when the chain keys no class or the mold is
    ///   past the table; otherwise its observation class and, for each chain
    ///   frontier, whether the mold continues it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`SettleChain`].
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[spec(ensures: |ret| (!self.keyed || pbg.observation(mold).is_err()) == (ret == PushKey::Alone(mold)))]
    pub(crate) fn key(
        &self,
        pbg: &Pbg,
        mold: MoldId,
    ) -> PushKey
    {
        if !self.keyed {
            return PushKey::Alone(mold);
        }
        let Ok(observation) = pbg.observation(mold)
        else {
            return PushKey::Alone(mold);
        };
        let mut bits = 0_u64;
        // A mold with no predecessor continues no frontier.
        if bool::from(pbg.mold_has_predecessor(mold)) {
            for (position, &frontier) in (0_u32 ..).zip(&self.molds) {
                if bool::from(pbg.molds_adjacent(frontier, mold)) {
                    bits |= 1_u64.checked_shl(position).unwrap_or(0);
                }
            }
        }
        PushKey::Class {
            observation,
            adjacency: ChainAdjacency(bits),
        }
    }
}

/// The canonical window signatures of a tie's openers, and the buffers that
/// number them.
///
/// # Specification
/// - requires: [`classify`](Self::classify) is given the openers in ascending
///   order and the labels of the tokens after the tie.
/// - ensures: two openers share a signature exactly when their observation
///   classes agree and, at each later position, their same-form successors the
///   position's labels admit agree in order, label, identity where the
///   successor can open its form, and signature.
/// - panics: none.
/// - executable: none — reused buffers; [`classify`](Self::classify) carries
///   the clause.
///
/// # Adequacy
/// - hypothesis: L3 — the differential witness compares the window verdicts the
///   classes reach with the dry runs' over every windowed tie of the corpus,
///   the drop matrix and the editor scenario; a signature that drops a
///   position, a label or an identity merges openers whose windows differ.
/// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
#[derive(Clone, Debug, Default)]
pub struct WindowClasses
{
    /// The nodes reached at each level, ascending: level `j` holds the molds
    /// whose signature reads the positions from `j` on.
    levels: Vec<Vec<MoldId>>,
    /// Each level's nodes' canonical numbers, beside `levels`.
    numbers: Vec<Vec<u32>>,
    /// Every node's edges, node after node, in the order reach expands them.
    edges: Vec<WindowEdge>,
    /// Each level's nodes' edges as a start and an end in `edges`, beside
    /// `levels`.
    edge_spans: Vec<Vec<(usize, usize)>>,
    /// The encodings of the level being numbered, back to back.
    arena: Vec<u32>,
    /// Each node's encoding as a start and an end in `arena`.
    spans: Vec<(usize, usize)>,
    /// The level's nodes in encoding order.
    order: Vec<usize>,
}

/// A successor a window position's labels admit, read once when its node is
/// reached and again when the node is numbered.
#[derive(Clone, Copy, Debug)]
struct WindowEdge
{
    /// The window position whose token the successor is.
    position: usize,
    /// Which of the token's labels the successor carries.
    label: u32,
    /// The successor's identity when it can open its form, else
    /// [`UNNAMED`].
    named: u32,
    /// The successor.
    successor: MoldId,
}

/// The sentinel an encoding writes for a successor named by its class alone.
const UNNAMED: u32 = u32::MAX;

/// An opener's canonical window signature number.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WindowClass(u32);

impl WindowClasses
{
    /// Number each of `openers` by its window signature over `labels`, into
    /// `classes`.
    ///
    /// # Specification
    /// - requires: `openers` ascending; `labels` the labels of the significant
    ///   tokens after the tie, the window's and the one after it.
    /// - ensures: `classes` holds one number per opener, in order; two openers'
    ///   numbers agree exactly when their signatures do.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`WindowClasses`].
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    ///
    /// # Termination
    /// Each level's nodes reach only later levels, of which there are at most
    /// `labels.len()`; each node is expanded once.
    #[spec(ensures: |()| classes.len() == openers.len())]
    pub(crate) fn classify(
        &mut self,
        pbg: &Pbg,
        openers: &[MoldId],
        labels: &[TokenLabels<'_>],
        classes: &mut Vec<WindowClass>,
    )
    {
        let &mut Self {
            ref mut levels,
            ref mut numbers,
            ref mut edges,
            ref mut edge_spans,
            ref mut arena,
            ref mut spans,
            ref mut order,
        } = self;
        let positions = labels.len();
        let depth = positions.saturating_add(1);
        if levels.len() < depth {
            levels.resize_with(depth, Vec::new);
            numbers.resize_with(depth, Vec::new);
            edge_spans.resize_with(depth, Vec::new);
        }
        for nodes in levels.iter_mut() {
            nodes.clear();
        }
        for level_spans in edge_spans.iter_mut() {
            level_spans.clear();
        }
        edges.clear();
        classes.clear();
        if let Some(first) = levels.first_mut() {
            first.extend_from_slice(openers);
        }
        // Reach: each node's successors the labels at a later position admit
        // are nodes of the level after that position, and the node's edges.
        // Every expansion lands on a later level, so a level is whole before
        // its nodes are expanded and their indices are final. The melder
        // matches a successor to a token by its label's spelling, so each
        // successor's label is read once and matched at every position.
        for level in 0 .. depth {
            let mut at = 0_usize;
            while let Some(&mold) = levels.get(level).and_then(|nodes| nodes.get(at)) {
                at = at.saturating_add(1);
                let start = edges.len();
                for &(_, successor) in pbg.mold_successors(mold) {
                    let Ok(def) = pbg.mold(successor)
                    else {
                        continue;
                    };
                    let label = CandidateLabel::from(def.label);
                    let named = if bool::from(pbg.mold_is_form_first(successor)) {
                        u32::from(successor)
                    }
                    else {
                        UNNAMED
                    };
                    for (position, token) in labels.iter().enumerate().skip(level) {
                        let Some(carried) = token.iter().position(|&held| held == label)
                        else {
                            continue;
                        };
                        edges.push(WindowEdge {
                            position,
                            label: u32::try_from(carried).unwrap_or(UNNAMED),
                            named,
                            successor,
                        });
                        if let Some(next) = levels.get_mut(position.saturating_add(1))
                            && let Err(slot) = next.binary_search(&successor)
                        {
                            next.insert(slot, successor);
                        }
                    }
                }
                if let Some(level_spans) = edge_spans.get_mut(level) {
                    level_spans.push((start, edges.len()));
                }
            }
        }
        // Number: from the last level down, each node by its encoding — its
        // observation, then each edge's position, label, identity when the
        // successor can open its form, and the successor's number. Edges are
        // listed alike for every node, so equal encodings are equal
        // signatures.
        for level in (0 .. depth).rev() {
            arena.clear();
            spans.clear();
            let count = levels.get(level).map_or(0, Vec::len);
            for at in 0 .. count {
                let Some(&mold) = levels.get(level).and_then(|nodes| nodes.get(at))
                else {
                    break;
                };
                let start = arena.len();
                arena.push(pbg.observation(mold).map_or(UNNAMED, u32::from));
                let (from, to) = edge_spans
                    .get(level)
                    .and_then(|level_spans| level_spans.get(at))
                    .copied()
                    .unwrap_or((0, 0));
                for edge in edges.get(from .. to).unwrap_or(&[]) {
                    let after = edge.position.saturating_add(1);
                    let number = levels
                        .get(after)
                        .and_then(|nodes| nodes.binary_search(&edge.successor).ok())
                        .and_then(|slot| numbers.get(after)?.get(slot))
                        .copied()
                        .unwrap_or(UNNAMED);
                    arena.extend([
                        u32::try_from(edge.position).unwrap_or(UNNAMED),
                        edge.label,
                        edge.named,
                        number,
                    ]);
                }
                spans.push((start, arena.len()));
            }
            let encoding = |node: usize| {
                spans
                    .get(node)
                    .and_then(|&(start, end)| arena.get(start .. end))
                    .unwrap_or(&[])
            };
            order.clear();
            order.extend(0 .. count);
            order.sort_unstable_by(|&left, &right| encoding(left).cmp(encoding(right)));
            let Some(numbered) = numbers.get_mut(level)
            else {
                continue;
            };
            numbered.clear();
            numbered.resize(count, 0);
            let mut current = 0_u32;
            let mut previous: Option<usize> = None;
            for &node in order.iter() {
                if previous.is_some_and(|before| encoding(before) != encoding(node)) {
                    current = current.saturating_add(1);
                }
                if let Some(slot) = numbered.get_mut(node) {
                    *slot = current;
                }
                previous = Some(node);
            }
        }
        let first = levels.first();
        let numbered = numbers.first();
        classes.extend(openers.iter().map(|opener| {
            WindowClass(
                first
                    .and_then(|nodes| nodes.binary_search(opener).ok())
                    .and_then(|slot| numbered?.get(slot))
                    .copied()
                    .unwrap_or(UNNAMED),
            )
        }));
    }
}
