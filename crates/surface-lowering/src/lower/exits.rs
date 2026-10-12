//! Early exits: a `return` or a `become` wherever a path through a body
//! passes, lowered so that every exit stands where its body ends.
//!
//! # Three passes, one per sweep
//!
//! A **survey**, descending before the classification, records what every
//! node's paths do with the body it stands in: never leave it, sometimes, or
//! always. A function, a lambda and a thunk never do, since an exit inside one
//! leaves it and not the body around it.
//!
//! The **classification** reads the survey at each block a path runs through.
//! A statement whose computation sometimes leaves distributes the rest of the
//! block: its computation joins the block, answers what the block answers, and
//! every position in tail position of it joins too. A statement whose
//! computation always leaves makes the rest of the block unreachable, which is
//! refused. An exit standing where no path passes — a call's head, outside any
//! body — is refused as not in tail.
//!
//! The **mint** sweep commutes each body once, when the function, the lambda
//! or the thunk that owns it is minted: a bind whose rest is distributed
//! disappears into its computation, whose every local end binds a copy of the
//! rest, carried under the binders between the statement and the end, and
//! every exit is left where it stands, which is then where the body ends. A
//! match leaf's copy of an arm body carries the exits and the distributed
//! binds of the arm with it.
//!
//! The decision, the alternatives and what reverses it are the crate's: see
//! the crate documentation's section on exits.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ArenaWatermark;
use gandr_core_term::Binders;
use gandr_core_term::Carried;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Lowerer;
use super::Sink;
use super::lowered;
use super::native::Answer;
use super::native::answered;
use crate::error::LoweringRefusal;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::origin::Origin;

#[cfg(test)]
mod tests;

/// What the paths through a node do with the body it stands in.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the variants are ordered never, sometimes, always, so the greater
///   of two children's is what a form holding both does at least.
/// - provides: the survey's answer, which the classification reads at every
///   statement of a block a path runs through.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a computation with no exit, one with an exit in one arm
///   and one with an exit in every arm, each at one and two depths.
/// - witness: `lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Leaves
{
    /// No path leaves: the node holds no exit outside a body of its own.
    #[default]
    Never,
    /// Some path leaves and some ends where the node stands.
    Sometimes,
    /// Every path leaves.
    Always,
}

/// Where the rest of a block goes after one of its statements.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a bound rest is bound once, after the statement's computation
///   returns; a distributed rest continues every local end of it.
/// - provides: the statement half of the commuting.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a statement whose computation holds no exit binds its
///   rest once, and one whose match exits in one arm continues the other.
/// - witness: `lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Rest
{
    /// The rest is bound once over the statement's computation.
    Bound,
    /// The rest continues every local end of the statement's computation,
    /// which holds an exit.
    Distributed,
}

quenchant_shape::reason_enum! {
    /// Why a rest continues no rest of its own.
    pub mod enclosing {
        /// The statement's computation is where its body's own path runs.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No local end of another statement holds the statement.
            Outermost,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a rest has no commuted form yet.
    pub mod settled {
        /// The commuting has not reached it.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No local end has asked for it.
            Pending,
        }
    }
}

/// A rest of a block the commuting holds, by its position in its list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct RestAt(usize);

/// A distributed rest: what continues each local end of its statement.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the rest is read under the statement's binder, `depth` binders
///   below the body's root.
/// - executable: none — the record holds no arena to check the depth against.
///
/// # Adequacy
/// - hypothesis: L3 — a rest continuing the local ends of a match nested in
///   another match's arm continues the outer rest in turn.
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Pending
{
    /// The rest, under the statement's one binder.
    rest: ComputationId,
    /// The binders between the body's root and the statement.
    depth: Binders,
    /// The statement's origin, which every bind of the rest carries.
    origin: Origin,
    /// The rest the statement's own local end continues, when the statement
    /// stands at a local end of another.
    outer: Maybe<RestAt, enclosing::Absent>,
}

/// One unit of the commuting's work.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Step
{
    /// Commute a computation at a depth, under the rests it continues.
    Open(ComputationId, Maybe<RestAt, enclosing::Absent>, Binders),
    /// Rebuild a computation over its children's commuted forms.
    Close(ComputationId),
    /// Keep the result on top as a rest's commuted form.
    Settle(RestAt),
    /// Bind a local end at a depth over a rest's commuted form.
    Continue(ComputationId, RestAt, Binders),
}

impl<'source> Lowerer<'_, 'source>
{
    /// Survey what every node's paths do with the body it stands in.
    ///
    /// # Specification
    /// - requires: nothing; the survey reads the tree alone.
    /// - ensures: every node holds its [`Leaves`], children before parents:
    ///   `return` and `become` always leave; a function, a lambda and a thunk
    ///   never do, since an exit inside one leaves it; a form holding no exit
    ///   outside such a body never does; a block or a grouping does what the
    ///   child that leaves most does; a match always leaves when every arm
    ///   does; every other form holding an exit sometimes does.
    /// - provides: what the classification of a block reads to decide where the
    ///   rest of the block goes, before any statement in it is classified.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the sweep outruns the
    ///   allowance, a step per node.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a computation with no exit, one with an exit in one
    ///   arm and one with an exit in every arm, each at one and two depths, and
    ///   an exit inside a thunk, each asserted as its exact survey.
    /// - witness: `lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
    #[spec(
        captures: before = (self.fuel.remaining, self.leaves.len()),
        ensures: |ret| {
            self.leaves.len() == before.1
                && (ret.is_err()
                    || self.fuel.remaining
                        <= before.0.saturating_sub(usize::from(self.tree.node_count())))
        },
    )]
    pub(super) fn survey(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        let mut pieces = core::mem::take(&mut self.pieces);
        let mut remaining = usize::from(self.tree.node_count());
        let mut outcome = Ok(());
        while let Some(next) = remaining.checked_sub(1_usize) {
            remaining = next;
            if let Err(refusal) = self.fuel.spend() {
                outcome = Err(refusal);
                break;
            }
            let leaves = self.leaves_of(NodeIndex::from(next), &mut pieces);
            if let Some(held) = self.leaves.get_mut(next) {
                *held = leaves;
            }
        }
        self.pieces = pieces;

        outcome
    }

    /// What the paths of the node at `position` do, its children surveyed.
    ///
    /// # Specification
    /// - requires: every child of `position` is surveyed.
    /// - ensures: as [`Self::survey`] states it, for one node; a node that is
    ///   no form sometimes leaves when a child does and never otherwise.
    /// - provides: the per-node half of [`Self::survey`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::survey`].
    /// - witness: `lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
    #[spec(ensures: |ret| ret != Leaves::Sometimes || self.tree.children(position).any(|child| self.leaves_at(child) != Leaves::Never))]
    fn leaves_of(
        &self,
        position: NodeIndex,
        pieces: &mut Pieces,
    ) -> Leaves
    {
        let held = self
            .tree
            .children(position)
            .map(|child| self.leaves_at(child))
            .max()
            .unwrap_or_default();
        let Some(node) = self.tree.node(position)
        else {
            return Leaves::Never;
        };
        let Ok(Shape::Form { former, .. }) = shape_of(self.pbg, node)
        else {
            return held.min(Leaves::Sometimes);
        };
        match former {
            | Former::Exit | Former::Become => Leaves::Always,
            | Former::Thunk | Former::Lambda | Former::Declaration | Former::Module => {
                Leaves::Never
            },
            | _ if held == Leaves::Never => Leaves::Never,
            | Former::Block | Former::Parenthesized => held,
            | Former::Case => self.arms_leave(position, pieces),
            | _ => Leaves::Sometimes,
        }
    }

    /// What the paths of the match at `position`, which holds an exit, do:
    /// always leave when every arm always does.
    ///
    /// # Specification
    /// - requires: every arm body of the match is surveyed, and one of its
    ///   children holds an exit.
    /// - ensures: always when the match has an arm and every arm body always
    ///   leaves; sometimes otherwise, a match whose pieces do not read
    ///   included.
    /// - provides: the match half of [`Self::leaves_of`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::survey`].
    /// - witness: `lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
    #[spec(ensures: |ret| ret != Leaves::Never)]
    fn arms_leave(
        &self,
        position: NodeIndex,
        pieces: &mut Pieces,
    ) -> Leaves
    {
        if read_pieces(self.pbg, self.tree, position, pieces).is_err() {
            return Leaves::Sometimes;
        }
        let mut arrow = false;
        let mut leaves = Leaves::Sometimes;
        let mut every = Leaves::Always;
        for piece in &pieces.pieces {
            match *piece {
                | Piece::Tile { label, .. } => arrow = label == TileName::FAT_ARROW,
                | Piece::Operand(body) if arrow => {
                    arrow = false;
                    every = every.min(self.leaves_at(body.node));
                    leaves = every.max(Leaves::Sometimes);
                },
                | Piece::Operand(_) => {},
            }
        }

        leaves
    }

    /// What the paths of the node at `position` do, as surveyed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the surveyed answer of a node the tree holds; never for a
    ///   position past the tree.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::survey`].
    /// - witness: `lower::exits::tests::the_paths_of_a_computation_are_surveyed_through_nesting`
    #[spec(ensures: |ret| ret == self.leaves.get(usize::from(position)).copied().unwrap_or_default())]
    pub(super) fn leaves_at(
        &self,
        position: NodeIndex,
    ) -> Leaves
    {
        self.leaves
            .get(usize::from(position))
            .copied()
            .unwrap_or_default()
    }

    /// Mark `inner`, standing in tail position of `outer`, with the paths
    /// through `outer`: where a path ends, where an exit may stand, and where a
    /// local end continues a block.
    ///
    /// # Specification
    /// - requires: `inner` stands in tail position of `outer`: a block's last
    ///   computation, a match's arm, a grouping's operand.
    /// - ensures: `inner` carries each mark `outer` carries, and keeps its own.
    /// - provides: the one way a path is passed down the classification.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path through a grouping, a block and a match
    ///   reaches an exit in each, an exit under none is refused, and a path
    ///   through nested matches missing its exit is refused where it ends.
    /// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
    /// - witness: `lower::exits::tests::a_path_missing_its_exit_is_refused_where_it_ends`
    #[spec(
        captures: before = (
            self.exits.contains(&inner) || self.exits.contains(&outer),
            self.exitable.contains(&inner) || self.exitable.contains(&outer),
            self.joined.contains(&inner) || self.joined.contains(&outer),
        ),
        ensures: self.exits.contains(&inner) == before.0
            && self.exitable.contains(&inner) == before.1
            && self.joined.contains(&inner) == before.2,
    )]
    pub(super) fn pass_paths(
        &mut self,
        outer: NodeIndex,
        inner: NodeIndex,
    )
    {
        for marks in [&mut self.exits, &mut self.exitable, &mut self.joined] {
            if marks.contains(&outer) {
                let _marked = marks.insert(inner);
            }
        }
    }

    /// Read `body`, the block of a function's, a lambda's or a thunk's body,
    /// as one a path runs through, its last computation where the body ends.
    ///
    /// # Specification
    /// - requires: `body` is the block just read for the body at `site`, and
    ///   `answer` the type the body states, when it states one.
    /// - ensures: the block's last computation is where a path ends, and the
    ///   block's statements as [`Self::paths_through`] marks them.
    /// - provides: the one opening of a body every function, lambda and thunk
    ///   shares.
    /// - fails: [`LoweringRefusal::Unreachable`], as [`Self::paths_through`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::Unreachable`] for statements no path reaches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::paths_through`].
    /// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
    /// - witness: `lower::exits::tests::code_no_path_reaches_is_refused`
    #[spec(ensures: |ret| ret.is_err() || (self.exits.contains(&body.last) && self.exitable.contains(&body.last)))]
    pub(super) fn open_body(
        &mut self,
        site: super::Site,
        body: Block,
        answer: Maybe<Answer, answered::Absent>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _tail = self.exits.insert(body.last);
        self.paths_through(site, body, answer)
    }

    /// Run the paths through `block` on to its statements.
    ///
    /// # Specification
    /// - requires: `block` is the block just read at `site`, a path passes it,
    ///   and `answer` is the type the block answers, when one is stated.
    /// - ensures: the last computation and every statement's computation are
    ///   where an exit may stand; a statement whose computation sometimes
    ///   leaves distributes the rest of the block, its computation joining the
    ///   block and answering `answer`; a statement whose computation never
    ///   leaves keeps its rest bound.
    /// - provides: the statement half of the classification of exits.
    /// - fails: [`LoweringRefusal::Unreachable`] for a statement whose
    ///   computation always leaves, at the bytes from the next statement to the
    ///   block's last computation.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::Unreachable`] for statements no path reaches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a statement leaving in one arm distributes its rest,
    ///   one leaving in every arm refuses what follows, and one never leaving
    ///   keeps its rest bound.
    /// - witness: `lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
    /// - witness: `lower::exits::tests::code_no_path_reaches_is_refused`
    #[spec(ensures: |ret| ret.is_err() || (self.exitable.contains(&block.last)
        && super::stretch(&self.statements, block.statements).iter().all(|statement| {
            self.exitable.contains(&statement.bound)
                && (statement.rest == Rest::Distributed) == (self.leaves_at(statement.bound) == Leaves::Sometimes)
                && (statement.rest == Rest::Bound || self.joined.contains(&statement.bound))
        })))]
    pub(super) fn paths_through(
        &mut self,
        site: super::Site,
        block: Block,
        answer: Maybe<Answer, answered::Absent>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _last = self.exitable.insert(block.last);
        for position in block.statements.start .. block.statements.end {
            let Some(&statement) = self.statements.get(position)
            else {
                continue;
            };
            let _path = self.exitable.insert(statement.bound);
            match self.leaves_at(statement.bound) {
                | Leaves::Never => {},
                | Leaves::Sometimes => {
                    if let Some(held) = self.statements.get_mut(position) {
                        held.rest = Rest::Distributed;
                    }
                    let _joined = self.joined.insert(statement.bound);
                    if let Maybe::Present(stated) = answer {
                        let _first = self.answers.insert(statement.bound, stated);
                    }
                },
                | Leaves::Always => {
                    let after = super::Stretch {
                        start: position.saturating_add(1_usize),
                        end: block.statements.end,
                    };
                    return Err(LoweringRefusal::Unreachable {
                        span: self.unreached(site, block, after),
                    });
                },
            }
        }

        Ok(())
    }

    /// The bytes no path reaches in `block` once a statement always leaves:
    /// from the first statement of `after`, or the last computation, to the
    /// last computation.
    ///
    /// # Specification
    /// - requires: `after` is the stretch of `block`'s statements that follow
    ///   the leaving one, `block` read at `site`.
    /// - ensures: the span from the first node after the statement to the
    ///   block's last computation; the site's span when the tree holds neither.
    /// - provides: the locus of [`LoweringRefusal::Unreachable`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused rest of one statement and of none before
    ///   the last computation, each at its exact bytes.
    /// - witness: `lower::exits::tests::code_no_path_reaches_is_refused`
    #[spec(ensures: |ret| self.tree.node(block.last).is_none_or(|node| ret.end() >= node.span().end()))]
    fn unreached(
        &self,
        site: super::Site,
        block: Block,
        after: super::Stretch,
    ) -> ByteSpan
    {
        let first = if after.start < after.end {
            self.statements
                .get(after.start)
                .map_or(block.last, |statement| statement.origin)
        }
        else {
            block.last
        };
        let span_of = |node: NodeIndex| self.tree.node(node).map(gandr_surface_syntax::Node::span);
        match (span_of(first), span_of(block.last)) {
            | (Some(start), Some(end)) => start.join(end),
            | (Some(only), None) | (None, Some(only)) => only,
            | (None, None) => site.at.span,
        }
    }

    /// Mint `body`, the block of a function's, a lambda's or a thunk's body,
    /// with every exit put where the body ends.
    ///
    /// # Specification
    /// - requires: every node the block names is already minted or absent;
    ///   `origin` is the body's owner's.
    /// - ensures: the block [`Self::mint_block`] mints, commuted by [`commute`]
    ///   once any bind with a distributed rest is minted; nothing when the
    ///   block did not lower.
    /// - provides: the body half of thunks, lambdas and function tails.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body with no early exit is the block itself, and
    ///   one with an exit two matches deep leaves from where it stands.
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.computation(id).is_some()))]
    pub(super) fn mint_body(
        &self,
        body: Block,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        self.mint_block(body, sink).map(|minted| {
            if sink.distributed.is_empty() {
                minted
            }
            else {
                commute(sink, minted, origin)
            }
        })
    }
}

/// Record, for every copy a rewrite made of an exit or of a bind whose rest
/// is distributed, that the copy is one too.
///
/// # Specification
/// - requires: `carried` is what one rewrite reported.
/// - ensures: every computation `carried` maps an exit to is an exit; every one
///   it maps a distributed bind to is distributed, at the original's origin.
/// - provides: what keeps a match leaf's copy of an arm body commutable.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an exit in an arm that binds a field leaves from the
///   leaf's copy of the arm.
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
#[spec(ensures: carried.iter().all(|pair| match *pair {
    Carried::Computation(held, written) => (!sink.exits.contains(&held) || sink.exits.contains(&written))
        && (!sink.distributed.contains_key(&held) || sink.distributed.contains_key(&written)),
    _ => true,
}))]
pub(super) fn mark_copies(
    sink: &mut Sink<'_>,
    carried: &[Carried],
)
{
    for pair in carried {
        if let Carried::Computation(held, written) = *pair {
            if sink.exits.contains(&held) {
                let _first = sink.exits.insert(written);
            }
            if let Some(&origin) = sink.distributed.get(&held) {
                let _first = sink.distributed.insert(written, origin);
            }
        }
    }
}

/// `body` with every bind whose rest is distributed commuted into its
/// computation.
///
/// # Specification
/// - requires: `body` is the computation of one function's, lambda's or thunk's
///   body, every body nested in it already commuted; `fallback` is the body's
///   owner's origin.
/// - ensures: the body with each distributed bind `x ← M; N`, depth `d` below
///   the root, replaced by `M` with every local end of `M`, `d'` below the
///   root, continuing `N'`, where `N'` is `N`, itself commuted, with every
///   index past its binder raised by `d' - d`: a returner `return v` is
///   replaced by `N'[v/x]`, the beta step of the returner, so no producer the
///   checker cannot synthesise is bound; any other end `e` by `x ← e; N'`. A
///   local end is a node the walk through binds' rests, case branches, a data
///   case's field functions and a split's body reaches that is none of those
///   and no exit; an exit resets the rests it continues to none, so it stays
///   where it stands. The rest is copied once per depth it is carried to. Every
///   rebuilt node takes its original's origin and match record, every bind of a
///   rest its statement's origin, and every copied node its source's; `body`
///   itself when nothing was distributed in it.
/// - provides: the mint half of early exits: every exit focuses as the cut of
///   its value against the body's own return continuation.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// Each step opens a node of the finite body or a rest, which is settled
/// once, or closes one opened before.
///
/// # Adequacy
/// - hypothesis: L2 — the commuted body of a return two matches deep agrees
///   with the body written with the rest in each arm by hand. L3 — the checker
///   accepts it, its exit is the body's own tail, and every node has an origin.
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
/// - witness: `lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
/// - witness: `lower::tests::every_minted_node_has_an_origin`
#[spec(ensures: |ret| sink.arena.computation(ret).is_some() || ret == body)]
pub(super) fn commute(
    sink: &mut Sink<'_>,
    body: ComputationId,
    fallback: Origin,
) -> ComputationId
{
    let mut pending: Vec<Pending> = Vec::new();
    let mut settled: Vec<Maybe<ComputationId, settled::Absent>> = Vec::new();
    // economy: a rest is copied once per depth a local end continues it at,
    // so the commuted body grows with the rest times its distinct end depths;
    // a join point would share it, at the cost of a typed binder the core
    // does not have.
    let mut copies: BTreeMap<(RestAt, Binders), ComputationId> = BTreeMap::new();
    let mut carried: Vec<Carried> = Vec::new();
    let mut results: Vec<ComputationId> = Vec::new();
    let mut steps = Vec::from([Step::Open(
        body,
        Maybe::Absent(enclosing::Absent::Outermost),
        Binders::NONE,
    )]);
    while let Some(step) = steps.pop() {
        match step {
            | Step::Open(node, rests, depth) => {
                let rests = if sink.exits.contains(&node) {
                    Maybe::Absent(enclosing::Absent::Outermost)
                }
                else {
                    rests
                };
                let held = sink.arena.computation(node).cloned();
                match held {
                    | Some(Computation::Bind(bound, rest)) => {
                        if let Some(&origin) = sink.distributed.get(&node) {
                            let at = RestAt(pending.len());
                            pending.push(Pending {
                                rest,
                                depth,
                                origin,
                                outer: rests,
                            });
                            settled.push(Maybe::Absent(settled::Absent::Pending));
                            steps.push(Step::Open(bound, Maybe::Present(at), depth));
                        }
                        else {
                            steps.push(Step::Close(node));
                            steps.push(Step::Open(rest, rests, depth.deeper()));
                        }
                    },
                    | Some(Computation::Case { ref branches, .. }) => {
                        steps.push(Step::Close(node));
                        for &branch in branches.iter().rev() {
                            steps.push(Step::Open(branch, rests, depth.deeper()));
                        }
                    },
                    | Some(Computation::DataCase { ref branches, .. }) => {
                        steps.push(Step::Close(node));
                        for &branch in branches.iter().rev() {
                            steps.push(Step::Open(branch, rests, depth));
                        }
                    },
                    | Some(Computation::Split {
                        arity, body: under, ..
                    }) => {
                        steps.push(Step::Close(node));
                        steps.push(Step::Open(under, rests, depth.deeper_by(arity)));
                    },
                    | Some(Computation::Lambda(under)) => {
                        steps.push(Step::Close(node));
                        steps.push(Step::Open(under, rests, depth.deeper()));
                    },
                    | _ => match rests {
                        | Maybe::Absent(_) => results.push(node),
                        | Maybe::Present(at) => match settled.get(at.0) {
                            | Some(&Maybe::Present(rest)) => {
                                let Some(&continued) = pending.get(at.0)
                                else {
                                    results.push(node);
                                    continue;
                                };
                                results.push(continue_end(
                                    sink,
                                    (node, depth),
                                    (at, rest, continued),
                                    &mut copies,
                                    &mut carried,
                                ));
                            },
                            | Some(&Maybe::Absent(_)) | None => {
                                let Some(&continued) = pending.get(at.0)
                                else {
                                    results.push(node);
                                    continue;
                                };
                                steps.push(Step::Continue(node, at, depth));
                                steps.push(Step::Settle(at));
                                steps.push(Step::Open(
                                    continued.rest,
                                    continued.outer,
                                    continued.depth.deeper(),
                                ));
                            },
                        },
                    },
                }
            },
            | Step::Close(node) => {
                let rebuilt = rebuild(sink, node, &mut results, fallback);
                results.push(rebuilt);
            },
            | Step::Settle(at) => {
                if let Some(commuted) = results.pop()
                    && let Some(slot) = settled.get_mut(at.0)
                {
                    *slot = Maybe::Present(commuted);
                }
            },
            | Step::Continue(node, at, depth) => {
                let (Some(&Maybe::Present(rest)), Some(&continued)) =
                    (settled.get(at.0), pending.get(at.0))
                else {
                    results.push(node);
                    continue;
                };
                results.push(continue_end(
                    sink,
                    (node, depth),
                    (at, rest, continued),
                    &mut copies,
                    &mut carried,
                ));
            },
        }
    }

    results.pop().unwrap_or(body)
}

/// Continue the local end `end`, `depth` below the body's root, with the
/// commuted rest `rest` of the statement `continued`, carried down to it.
///
/// # Specification
/// - requires: `rest` is the commuted rest of `continued`, held at `at`, and
///   `depth` is at least the statement's.
/// - ensures: with `rest'` the rest with every index past its binder raised by
///   the depth between the statement and the end, one copy per depth kept in
///   `copies`: `rest'` instantiated at `v` for an end `return v`, its nodes at
///   their sources' origins; `x ← end; rest'` at the statement's origin for any
///   other end.
/// - provides: the continuation half of [`commute`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`commute`].
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
/// - witness: `lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
#[spec(captures: returned = matches!(sink.arena.computation(end.0), Some(&Computation::Return(_))),
    ensures: |ret| returned || matches!(sink.arena.computation(ret), Some(&Computation::Bind(bound, _)) if bound == end.0))]
fn continue_end(
    sink: &mut Sink<'_>,
    end: (ComputationId, Binders),
    continued: (RestAt, ComputationId, Pending),
    copies: &mut BTreeMap<(RestAt, Binders), ComputationId>,
    carried: &mut Vec<Carried>,
) -> ComputationId
{
    let (node, depth) = end;
    let (at, rest, statement) = continued;
    // reason: a binder count uses u32::MAX as its conservative ceiling, and an
    // end stands at least as deep as its statement.
    let amount = Binders::from(u32::from(depth).saturating_sub(u32::from(statement.depth)));
    let copy = match copies.get(&(at, amount)) {
        | Some(&copy) => copy,
        | None => {
            let copy = carry(sink, rest, amount, statement.origin, carried);
            let _first = copies.insert((at, amount), copy);
            copy
        },
    };
    if let Some(&Computation::Return(value)) = sink.arena.computation(node) {
        let mark = sink.arena.watermark();
        carried.clear();
        let instantiated =
            gandr_core_term::instantiate_computation_traced(sink.arena, copy, value, carried);
        record_copies(sink, mark, carried, statement.origin);
        return instantiated;
    }
    let bound = sink.arena.computation_bind(node, copy);
    sink.origins.record_computation(bound, statement.origin);

    bound
}

/// `rest`, under one binder, with every index past that binder raised by
/// `amount`, every node it mints recorded at its source's origin.
///
/// # Specification
/// - requires: every node of `rest` has an origin, or `fallback` stands for it.
/// - ensures: the shifted rest; `rest` itself, minting nothing, when `amount`
///   is none; every node minted carries the origin and the match record of the
///   node it was rewritten from, or `fallback`.
/// - provides: the copy half of [`commute`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a rest carried under a match's field binder reads the
///   function's parameter past it, and keeps its origins.
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
/// - witness: `lower::tests::every_minted_node_has_an_origin`
#[spec(ensures: |ret| amount != Binders::NONE || ret == rest)]
fn carry(
    sink: &mut Sink<'_>,
    rest: ComputationId,
    amount: Binders,
    fallback: Origin,
    carried: &mut Vec<Carried>,
) -> ComputationId
{
    let mark = sink.arena.watermark();
    carried.clear();
    let copy = gandr_core_term::shift_computation_under_traced(
        sink.arena,
        rest,
        Binders::ONE,
        amount,
        carried,
    );
    record_copies(sink, mark, carried, fallback);

    copy
}

/// Record the origin of every node minted since `mark`, each its source's in
/// `carried`.
///
/// # Specification
/// - requires: nothing has been recorded for a node minted since `mark`, and
///   `carried` reports the rewrite that minted them.
/// - ensures: every node minted since `mark` carries the origin of the first
///   node `carried` reports it rewritten from, or `fallback`; every computation
///   rewritten from a match's root carries the match's record.
/// - provides: the origin half of [`carry`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`carry`].
/// - witness: `lower::tests::every_minted_node_has_an_origin`
#[spec(ensures: sink.arena.computations_since(mark).all(|id| matches!(sink.origins.computation(id), Maybe::Present(_)))
    && sink.arena.values_since(mark).all(|id| matches!(sink.origins.value(id), Maybe::Present(_))))]
fn record_copies(
    sink: &mut Sink<'_>,
    mark: ArenaWatermark,
    carried: &[Carried],
    fallback: Origin,
)
{
    let mut values = BTreeMap::new();
    let mut computations = BTreeMap::new();
    let mut value_types = BTreeMap::new();
    let mut comp_types = BTreeMap::new();
    for pair in carried {
        match *pair {
            | Carried::Value(held, written) => {
                let _first = values.entry(written).or_insert(held);
            },
            | Carried::Computation(held, written) => {
                let _first = computations.entry(written).or_insert(held);
            },
            | Carried::ValueType(held, written) => {
                let _first = value_types.entry(written).or_insert(held);
            },
            | Carried::CompType(held, written) => {
                let _first = comp_types.entry(written).or_insert(held);
            },
        }
    }
    for id in sink.arena.values_since(mark) {
        let origin = match values.get(&id) {
            | Some(&held) => found_or(sink.origins.value(held), fallback),
            | None => fallback,
        };
        sink.origins.record_value(id, origin);
    }
    for id in sink.arena.computations_since(mark) {
        let source = computations.get(&id).copied();
        let origin = match source {
            | Some(held) => found_or(sink.origins.computation(held), fallback),
            | None => fallback,
        };
        sink.origins.record_computation(id, origin);
        if let Some(held) = source
            && let Maybe::Present(case) = sink.origins.case(held)
        {
            let kept = case.clone();
            sink.origins.record_case(id, kept);
        }
    }
    for id in sink.arena.value_types_since(mark) {
        let origin = match value_types.get(&id) {
            | Some(&held) => found_or(sink.origins.value_type(held), fallback),
            | None => fallback,
        };
        sink.origins.record_value_type(id, origin);
    }
    for id in sink.arena.comp_types_since(mark) {
        let origin = match comp_types.get(&id) {
            | Some(&held) => found_or(sink.origins.comp_type(held), fallback),
            | None => fallback,
        };
        sink.origins.record_comp_type(id, origin);
    }
}

/// Rebuild `node` over its children's commuted forms, the last of `results`.
///
/// # Specification
/// - requires: `node` is a bind, a case, a data case, a split or a lambda whose
///   every commuted child stands on top of `results`, in order.
/// - ensures: those results popped; `node` itself when each is the child it
///   stands for; else a node of the same former over them, recorded at `node`'s
///   origin, or `fallback`, and its match record.
/// - provides: the close half of [`commute`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`commute`].
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
#[spec(ensures: |ret| ret == node || sink.arena.computation(ret).is_some())]
fn rebuild(
    sink: &mut Sink<'_>,
    node: ComputationId,
    results: &mut Vec<ComputationId>,
    fallback: Origin,
) -> ComputationId
{
    let Some(held) = sink.arena.computation(node).cloned()
    else {
        return node;
    };
    let count = match held {
        | Computation::Case { ref branches, .. } => branches.len(),
        | Computation::DataCase { ref branches, .. } => branches.len(),
        | Computation::Bind(..) | Computation::Split { .. } | Computation::Lambda(_) => 1_usize,
        | _ => 0_usize,
    };
    let commuted = results.split_off(results.len().saturating_sub(count));
    let rebuilt = match (held, commuted.as_slice()) {
        | (Computation::Bind(bound, rest), &[commuted]) if commuted != rest => {
            sink.arena.computation_bind(bound, commuted)
        },
        | (Computation::Lambda(under), &[commuted]) if commuted != under => {
            sink.arena.computation_lambda(commuted)
        },
        | (
            Computation::Split {
                scrutinee,
                arity,
                body,
            },
            &[commuted],
        ) if commuted != body => sink.arena.computation_split(scrutinee, arity, commuted),
        | (
            Computation::Case {
                scrutinee,
                ref branches,
            },
            branched,
        ) if **branches != *branched => sink.arena.computation_case(scrutinee, branched),
        | (
            Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
            },
            branched,
        ) if branches.as_slice() != branched => {
            sink.arena
                .computation_data_case(scrutinee, motive, branched.to_vec())
        },
        | _ => return node,
    };
    let origin = found_or(sink.origins.computation(node), fallback);
    sink.origins.record_computation(rebuilt, origin);
    if let Maybe::Present(case) = sink.origins.case(node) {
        let kept = case.clone();
        sink.origins.record_case(rebuilt, kept);
    }

    rebuilt
}

/// The origin `found` holds, or `fallback`.
///
/// # Specification
/// trivial.
const fn found_or<Reason>(
    found: Maybe<Origin, Reason>,
    fallback: Origin,
) -> Origin
where
    Reason: Copy,
{
    match found {
        | Maybe::Present(origin) => origin,
        | Maybe::Absent(_) => fallback,
    }
}
