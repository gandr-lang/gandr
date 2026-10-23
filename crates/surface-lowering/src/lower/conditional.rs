//! The conditional `if c { t } else { e }`, lowered as the match of its
//! condition over the two booleans: `x ← c; case x { inl _ => t', inr _ =>
//! e' }`. The condition is read where a computation is, as a `while`'s is: a
//! value written there is returned, and the bind of a returner is written as
//! its beta step. Each branch is a block read under two nameless binders, the
//! bound condition and the case's unit payload, so no written name resolves to
//! either. A conditional whose false branch is one more conditional, `if c {
//! t } else if d { u } else { e }`, nests that one in its false branch. An
//! answer written after the condition, `-> T`, is the answer every branch's
//! last computation is read at, as a match's written answer is its arms'.

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::Value;
use gandr_core_term::Zone;
use gandr_core_term::instantiate_computation_traced;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Sink;
use super::Site;
use super::exits::mark_copies;
use super::exits::record_copies;
use super::lowered;
use super::native::Answer;
use super::native::Over;
use super::native::answered;
use crate::error::FormFault;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Piece;
use crate::form::TileName;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::SurfaceName;
use crate::resolve::TypeAtom;
use crate::resolve::binder_site;

#[cfg(test)]
mod tests;

/// A conditional as the minting reads it: the computation it tests, the block
/// it runs when that holds, and what it runs when it does not.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each node and block was read by [`Lowerer::conditional`].
/// - executable: none — the plan holds no source.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::conditional`].
/// - witness: `lower::conditional::tests::a_conditional_runs_the_branch_its_condition_selects`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Conditional
{
    /// The tested computation.
    condition: NodeIndex,
    /// The block run when the condition holds.
    then: Block,
    /// What runs when it does not.
    otherwise: Otherwise,
}

/// What a conditional runs when its condition does not hold.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one variant per false branch the grammar writes.
/// - executable: none — the plan holds no source.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::conditional`].
/// - witness: `lower::conditional::tests::an_else_if_tests_its_own_condition_in_the_false_branch`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Otherwise
{
    /// The block after `else`.
    Block(Block),
    /// One more conditional after `else`, its false branch a block.
    If
    {
        /// Its tested computation, read inside the outer false branch.
        condition: NodeIndex,
        /// The block it runs when that holds.
        then: Block,
        /// The block it runs when it does not.
        otherwise: Block,
    },
}

impl<'source> Lowerer<'_, 'source>
{
    /// Classify a conditional, `if c -> T? { … } else { … }` or `… else if d
    /// -> U? { … } else { … }`.
    ///
    /// # Specification
    /// - requires: `site` is an `if` in term position.
    /// - ensures: a conditional standing as a computation reads its condition
    ///   as a tested computation under its frame, and each branch as a block
    ///   under two more nameless binders; an `else if` reads its own condition
    ///   under the outer false branch's frame and its branches under two more.
    ///   Each branch's last computation is read at the answer written after the
    ///   condition that heads it, else at the answer the conditional's position
    ///   states, and carries the paths through the conditional; the form is
    ///   planned over the condition and the branches.
    /// - provides: the conditional.
    /// - fails: yields the wrong-sort refusal outside computation position; a
    ///   misplaced tile for a form out of shape; each block's own refusal and
    ///   the unreachable refusal for statements after one every path of which
    ///   exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The conditional's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a conditional over a value and one over a comparison
    ///   each run the branch the condition selects, one under a written answer
    ///   checks, and an `else if` tests its own condition only when the first
    ///   does not hold.
    /// - witness: `lower::conditional::tests::a_conditional_runs_the_branch_its_condition_selects`
    /// - witness: `lower::conditional::tests::an_else_if_tests_its_own_condition_in_the_false_branch`
    #[spec(
        ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::If(_))),
    )]
    pub(super) fn conditional(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let (condition, then, inner, answer) = self.branch(site, &mut cursor, frame)?;
        let otherwise = if let Maybe::Present(_) = cursor.tile(TileName::IF) {
            let (condition, then, below, own) = self.branch(site, &mut cursor, inner)?;
            let otherwise = self.block(site, &mut cursor, below)?;
            self.ends(site, otherwise, own)?;
            Otherwise::If {
                condition,
                then,
                otherwise,
            }
        }
        else {
            let otherwise = self.block(site, &mut cursor, inner)?;
            self.ends(site, otherwise, answer)?;
            Otherwise::Block(otherwise)
        };
        self.plan(
            site,
            Plan::If(Conditional {
                condition,
                then,
                otherwise,
            }),
        );

        Ok(())
    }

    /// Read one head of a conditional, `if c -> T? { … } else`, from its
    /// condition to its `else`, the `if` read already or next.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the head's `if` or past it, inside the
    ///   conditional at `site` read under `frame`.
    /// - ensures: the condition is read as a tested computation under `frame`,
    ///   the written answer as a result under `frame`, and the block before the
    ///   `else` under `frame` extended by two nameless binders, its last
    ///   computation at the written answer and carrying the paths through the
    ///   conditional; the condition, the block, the extended frame and the
    ///   written answer are returned, with the cursor past the `else`.
    /// - fails: a misplaced tile at a head out of shape; the block's own
    ///   refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The head's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::conditional`].
    /// - witness: `lower::conditional::tests::a_conditional_runs_the_branch_its_condition_selects`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(condition, ..)| self.tested.contains(&condition)))]
    fn branch(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
        frame: Frame,
    ) -> Result<(NodeIndex, Block, Frame, Maybe<Answer, answered::Absent>), LoweringRefusal<'source>>
    {
        let _if = cursor.tile(TileName::IF);
        let condition = site.one(cursor.operands())?;
        let written = match cursor.tile(TileName::ARROW) {
            Maybe::Present(_) => Maybe::Present(site.one(cursor.operands())?),
            Maybe::Absent(_) => Maybe::Absent(answered::Absent::Unstated),
        };
        let _tested = self.tested.insert(condition.node);
        self.read(condition.node, Reading::Computation(frame));
        let mut inner = frame;
        for _binder in 0_u8 .. 2_u8 {
            inner = Frame::Inner(self.scope.extend(
                inner,
                SurfaceName::from(""),
                Maybe::Absent(binder_site::Absent::Unwritten),
            ));
        }
        // The block runs to the `else`, which the block reader takes as the
        // end of its pieces: it reads the block alone.
        let rest = cursor.remaining();
        let length = rest
            .iter()
            .position(
                |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::ELSE),
            )
            .ok_or_else(|| site.fault(cursor.here(), FormFault::MisplacedTile))?;
        let mut braced = Cursor::new(rest.get(.. length).unwrap_or_default(), cursor.here());
        let answer = match written {
            Maybe::Present(stated) => {
                self.read(stated.node, Reading::Result(frame));
                Maybe::Present(Answer {
                    node: stated.node,
                    frame,
                    over: Over::Written,
                })
            },
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        let then = self.block(site, &mut braced, inner)?;
        while let Maybe::Absent(_) = cursor.tile(TileName::ELSE) {
            if let Maybe::Absent(_) = cursor.read() {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            }
        }
        self.ends(site, then, answer)?;
        Ok((condition.node, then, inner, answer))
    }

    /// Make `block`, a branch of the conditional at `site`, end where the
    /// conditional does.
    ///
    /// # Specification
    /// - requires: `block` was just read as a branch of the conditional at
    ///   `site`.
    /// - ensures: the block's last computation is read at `answer` when one is
    ///   written, else at the answer the conditional's position states, and
    ///   carries the paths through the conditional; a path that passes the
    ///   conditional runs on to the block's statements.
    /// - provides: a branch's end, as a match's arm ends where the match does.
    /// - fails: [`LoweringRefusal::Unreachable`] for statements after one every
    ///   path of which exits.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::Unreachable`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a conditional ending a function whose branches both
    ///   return checks, as one whose branches end in values does.
    /// - witness: `lower::conditional::tests::a_conditional_runs_the_branch_its_condition_selects`
    #[spec(ensures: |ret| ret.is_err() || !self.exitable.contains(&site.at.node) || self.exitable.contains(&block.last))]
    fn ends(
        &mut self,
        site: Site,
        block: Block,
        answer: Maybe<Answer, answered::Absent>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let answer = match answer {
            Maybe::Present(written) => Maybe::Present(written),
            Maybe::Absent(reason) => self
                .answers
                .get(&site.at.node)
                .copied()
                .map_or(Maybe::Absent(reason), Maybe::Present),
        };
        if let Maybe::Present(stated) = answer {
            let _first = self.answers.insert(block.last, stated);
        }
        self.pass_paths(site.at.node, block.last);
        if self.exitable.contains(&site.at.node) {
            self.paths_through(site, block, answer)?;
        }
        Ok(())
    }

    /// Mint the conditional `conditional`.
    ///
    /// # Specification
    /// - requires: the condition and every node of the branches are already
    ///   minted or absent.
    /// - ensures: `x ← c; case x { inl _ => t, inr _ => e }`, the false branch
    ///   `e` the minted block or the nested conditional minted the same way; a
    ///   condition that is a returner `return v` takes the beta step instead,
    ///   the case instantiated at `v` with every copy it makes marked as its
    ///   source is; every node at `origin`; nothing when a condition or a
    ///   branch did not lower.
    /// - provides: the minting half of [`Self::conditional`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::conditional`].
    /// - witness: `lower::conditional::tests::a_conditional_runs_the_branch_its_condition_selects`
    /// - witness: `lower::conditional::tests::an_else_if_tests_its_own_condition_in_the_false_branch`
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(Lowered::Computation(_)) | Maybe::Absent(_)))]
    pub(super) fn mint_conditional(
        &self,
        conditional: Conditional,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let then = match self.mint_block(conditional.then, sink) {
            Maybe::Present(then) => then,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let otherwise = match conditional.otherwise {
            Otherwise::Block(block) => self.mint_block(block, sink),
            Otherwise::If {
                condition,
                then,
                otherwise,
            } => match (
                self.mint_block(then, sink),
                self.mint_block(otherwise, sink),
            ) {
                (Maybe::Present(then), Maybe::Present(otherwise)) => {
                    self.tested(condition, [then, otherwise], sink, origin)
                },
                (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => Maybe::Absent(reason),
            },
        };
        let Maybe::Present(otherwise) = otherwise
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        // `tested` records every node it mints, the case's root among them.
        match self.tested(conditional.condition, [then, otherwise], sink, origin) {
            Maybe::Present(id) => Maybe::Present(Lowered::Computation(id)),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The case of the computation `condition` over `branches`, the true
    /// branch first, bound to it: `x ← c; case x { inl _ => t, inr _ => e }`.
    ///
    /// # Specification
    /// - requires: `branches` are minted under two binders more than the
    ///   condition.
    /// - ensures: the bind of the condition over the case of its bound value;
    ///   for a condition that is the return of a variable, `return x`, the case
    ///   instantiated at `x`, every copy marked as its source is; for the
    ///   return of any other value, `return v`, whose type the case cannot
    ///   synthesise, the bind of that return ascribed `-F Bool`; the case, the
    ///   bind and the ascription at `origin`; nothing when the condition did
    ///   not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::conditional`].
    /// - witness: `lower::conditional::tests::a_conditional_runs_the_branch_its_condition_selects`
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(_)) == matches!(self.computation_at(condition), Maybe::Present(_)))]
    fn tested(
        &self,
        condition: NodeIndex,
        branches: [ComputationId; 2],
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        let tested = match self.computation_at(condition) {
            Maybe::Present(tested) => tested,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let bound = sink
            .arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        sink.origins.record_value(bound, origin);
        let case = sink.arena.computation_case(bound, &branches);
        sink.origins.record_computation(case, origin);
        let mut tested = tested;
        if let Some(&Computation::Return(value)) = sink.arena.computation(tested) {
            if let Some(&Value::Variable { .. }) = sink.arena.value(value) {
                let mark = sink.arena.watermark();
                let mut carried = alloc::vec::Vec::new();
                let instantiated =
                    instantiate_computation_traced(sink.arena, case, value, &mut carried);
                record_copies(sink, mark, &carried, origin);
                mark_copies(sink, &carried);
                return Maybe::Present(instantiated);
            }
            let Lowered::ValueType(boolean) = sink.atom(TypeAtom::Boolean, origin)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let returner = sink.arena.comp_type_returner(boolean);
            sink.origins.record_comp_type(returner, origin);
            tested = sink.arena.computation_ascribe(tested, returner);
            sink.origins.record_computation(tested, origin);
        }
        let bind = sink.arena.computation_bind(tested, case);
        sink.origins.record_computation(bind, origin);
        Maybe::Present(bind)
    }
}
