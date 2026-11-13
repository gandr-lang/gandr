//! The conditional `if c { t } else { e }`, lowered as the match of its
//! condition over the two booleans: `x ← c; case x { inl _ => t', inr _ =>
//! e' }`. The condition is read where a computation is, as a `while`'s is: a
//! value written there is returned, and the bind of a returner is written as
//! its beta step. Each branch is a block read under two nameless binders, the
//! bound condition and the case's unit payload, so no written name resolves to
//! either. A conditional whose false branch is an else-if chain nests each
//! branch in its false branch. An
//! answer written after the condition, `-> T`, is the answer every branch's
//! last computation is read at, as a match's written answer is its arms', and
//! the type the case is ascribed, so the conditional answers it wherever it
//! stands: `x ← c; (case x { … } : T)`. An `else if` that writes its own
//! answer ascribes its own case; one that writes none is checked at the
//! answer of the conditional it stands in.

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::Value;
use gandr_core_term::Zone;
use gandr_core_term::instantiate_computation_traced;
use gandr_kernel_term::DeBruijnIndex;
pub(super) use gandr_surface_lowering_base::lower::conditional::Conditional;
use gandr_surface_lowering_base::lower::conditional::Otherwise;
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
use super::native::passed;
use crate::error::FormFault;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Piece;
use crate::form::TileName;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::SurfaceName;
use crate::resolve::Telescope;
use crate::resolve::TypeAtom;
use crate::resolve::binder_site;

#[cfg(test)]
mod tests;

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
        ensures: |ret| ret.is_err() || matches!(self.cx.plans.get(site.at.node), Some(&Plan::If(_))),
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
            let start = self.cx.else_ifs.mark();
            let (condition, then, mut below, answer) = self.branch(site, &mut cursor, inner)?;
            let mut last_answer = answer;
            while let Maybe::Present(_) = cursor.tile(TileName::IF) {
                let (condition, then, next, answer) = self.branch(site, &mut cursor, below)?;
                self.cx.else_ifs.push((condition, then, answer));
                below = next;
                last_answer = answer;
            }
            let otherwise = self.block(site, &mut cursor, below)?;
            self.ends(site, otherwise, last_answer)?;
            Otherwise::If {
                condition,
                then,
                rest: self.cx.else_ifs.since(start),
                otherwise,
                answer,
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
                answer,
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
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(condition, ..)| self.cx.tested.contains(&condition)))]
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
        let _tested = self.cx.tested.insert(condition.node);
        self.read(condition.node, Reading::Computation(frame));
        let mut inner = frame;
        for _binder in 0_u8 .. 2_u8 {
            inner = Frame::Inner(self.cx.scope.extend(
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
                    arm: Maybe::Absent(passed::Absent::Unpassed),
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
    #[spec(ensures: |ret| ret.is_err() || !self.cx.exitable.contains(&site.at.node) || self.cx.exitable.contains(&block.last))]
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
                .cx
                .answers
                .get(&site.at.node)
                .copied()
                .map_or(Maybe::Absent(reason), Maybe::Present),
        };
        if let Maybe::Present(stated) = answer {
            let _first = self.cx.answers.insert(block.last, stated);
        }
        self.pass_paths(site.at.node, block.last);
        if self.cx.exitable.contains(&site.at.node) {
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
    ///   `e` the minted block or the nested conditional minted the same way,
    ///   each case ascribed the answer written after its own condition; a
    ///   condition that is a returner `return v` takes the beta step instead,
    ///   the case instantiated at `v` with every copy it makes marked as its
    ///   source is; every node at `origin`; nothing when a condition, a branch
    ///   or a written answer did not lower.
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
                rest,
                otherwise,
                answer,
            } => {
                let mut otherwise = self.mint_block(otherwise, sink);
                for &(condition, then, answer) in self.cx.else_ifs.read(rest).iter().rev() {
                    otherwise = match (self.mint_block(then, sink), otherwise) {
                        (Maybe::Present(then), Maybe::Present(otherwise)) => {
                            self.tested((condition, answer), [then, otherwise], sink, origin)
                        },
                        (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => {
                            Maybe::Absent(reason)
                        },
                    };
                }
                match (self.mint_block(then, sink), otherwise) {
                    (Maybe::Present(then), Maybe::Present(otherwise)) => {
                        self.tested((condition, answer), [then, otherwise], sink, origin)
                    },
                    (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => {
                        Maybe::Absent(reason)
                    },
                }
            },
        };
        let Maybe::Present(otherwise) = otherwise
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        // `tested` records every node it mints, the case's root among them.
        match self.tested(
            (conditional.condition, conditional.answer),
            [then, otherwise],
            sink,
            origin,
        ) {
            Maybe::Present(id) => Maybe::Present(Lowered::Computation(id)),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The case of the computation `condition` over `branches`, the true
    /// branch first, bound to it and ascribed `answer` when one is written: `x
    /// ← c; (case x { inl _ => t, inr _ => e } : T)`.
    ///
    /// # Specification
    /// - requires: `branches` are minted under two binders more than the
    ///   condition, and `answer` was read under the condition's frame.
    /// - ensures: the bind of the condition over the case of its bound value,
    ///   ascribed the written answer carried under the bind's binder; for a
    ///   condition that is the return of a variable, `return x`, the case
    ///   instantiated at `x`, every copy marked as its source is; for the
    ///   return of any other value, `return v`, whose type the case cannot
    ///   synthesise, the bind of that return ascribed `-F Bool`; the case, the
    ///   bind and the ascriptions at `origin`, a copy of the answer at what it
    ///   copies; nothing when the condition or the written answer did not
    ///   lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::conditional`]; a conditional with a
    ///   written answer synthesises it where its position states none.
    /// - witness: `lower::conditional::tests::a_conditional_runs_the_branch_its_condition_selects`
    /// - witness: `lower::conditional::tests::a_written_answer_ascribes_the_conditional_2089`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(self.computation_at(condition), Maybe::Present(_)))]
    fn tested(
        &self,
        (condition, answer): (NodeIndex, Maybe<Answer, answered::Absent>),
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
        let case = match answer {
            Maybe::Present(answer) => {
                let mark = sink.arena.watermark();
                let Maybe::Present(written) = self.answered_type(answer, sink)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                // The answer is read under the condition's frame, and the case
                // stands under the condition's binder.
                let mut carried = alloc::vec::Vec::new();
                let answered = self.relocate(
                    sink.arena,
                    written,
                    answer.frame,
                    Telescope::Signature,
                    Binders::ONE,
                    Some(&mut carried),
                );
                let ascribed = sink.arena.computation_ascribe(case, answered);
                record_copies(sink, mark, &carried, origin);
                ascribed
            },
            Maybe::Absent(_) => case,
        };
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
