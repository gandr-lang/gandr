//! The composite criterion on the terms of a presented reading.
//!
//! A critical pair whose peak holds a redex strictly below its seam is
//! composite: when the rewriting terminates, its join follows from the joins
//! of the other pairs (Kapur, Musser and Narendran). [`CompositeCriterion`]
//! walks the peak below the seam breadth first, in the order of
//! [`CellAlphabet::command_positions`](gandr_theory_cell_complexes::CellAlphabet::command_positions),
//! and asks each cell of the store, in store order, whether its left side
//! matches there. The first match is the pair's witness.
//!
//! The walk reads the peak's table in place. A match binds each variable to a
//! range of the table, compares a repeated variable's two ranges, and reads a
//! scoped variable's range through [`Depths`](super::Depths). The criterion
//! keeps its tables from one pair to the next, so a pair costs no allocation
//! once the tables hold the largest peak. Only a witness builds its position.

use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes::SubstitutionDecision;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::CompositePair;
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::PairClass;
use gandr_theory_coherent_resolutions::PairScheme;
use gandr_theory_coherent_resolutions::rewrite_at;
use quenchant_shape::shape::Maybe;

use super::Count;
use super::Head;
use super::OpenApplications;
use super::Term;
use super::TermAlphabet;
use super::TermPos;
use super::TermSubst;

/// The composite criterion on the terms of a presented reading, with the
/// working memory that its walk keeps from one pair to the next.
///
/// # Specification
/// - ensures: [`PairScheme::class`] gives a pair the first step below its seam
///   at which a cell of the store fires, or none.
/// - executable: none — a datum; [`PairScheme::class`] carries the predicate.
///
/// # Adequacy
/// - hypothesis: L3 — as its [`PairScheme::class`].
/// - witness: `term::tests::the_criterion_finds_the_listings_first_redex_below_each_position`
#[derive(Clone, Debug, Default)]
pub struct CompositeCriterion
{
    /// Each node of the walk below the seam: its start in the peak, the place
    /// of its parent in this table, and the step from its parent.
    visited: Vec<(Count, usize, PositionStep)>,
    /// Each variable that the match binds: the place of its first occurrence
    /// in the pattern, and the range of its image in the peak.
    bound: Vec<(Count, Count, Count)>,
    /// The applications still owed arguments, as a scope reads an image.
    open: OpenApplications,
    /// The steps of a witness's position below the seam, deepest first.
    steps: Vec<PositionStep>,
}

impl CompositeCriterion
{
    /// A criterion that has walked no peak.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Whether `pattern` matches the subterm of `target` that starts at
    /// `start`, as [`TermAlphabet`]'s `match_cmd` decides against that subterm
    /// read whole.
    ///
    /// # Specification
    /// - ensures: positive exactly when `match_cmd` of `pattern` against the
    ///   subterm, from an empty substitution, is positive.
    /// - panics: none.
    /// - intension: one lockstep pass over the pattern and the subterm's range,
    ///   with no node copied.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`PairScheme::class`].
    /// - witness: `term::tests::the_criterion_finds_the_listings_first_redex_below_each_position`
    #[spec(ensures: |output| bool::from(output)
        == bool::from(TermAlphabet::match_cmd(pattern, &target.slice(start, target.end_of(start)), &mut TermSubst::default())))]
    fn matches(
        &mut self,
        pattern: &Term,
        target: &Term,
        start: Count,
    ) -> SubstitutionDecision
    {
        let &mut Self {
            ref mut bound,
            ref mut open,
            ..
        } = self;
        bound.clear();
        let end = target.end_of(start);
        let mut at = start;
        for (place, head) in pattern.0.iter().enumerate() {
            let Some(target_head) = target.0.get(at.0).filter(|_| at < end)
            else {
                return SubstitutionDecision::from(false);
            };
            let (var, scope) = match *head {
                Head::Var(ref var) => (var, None),
                Head::Scoped(ref var, ref scope) => (var, Some(scope)),
                Head::Konst(_)
                | Head::Ctor(..)
                | Head::Op(..)
                | Head::Results(_)
                | Head::Inst(..)
                | Head::Abs(_)
                | Head::Occ(..)
                | Head::Free(..) => {
                    if head != target_head {
                        return SubstitutionDecision::from(false);
                    }
                    at = at.next();
                    continue;
                },
            };
            let image_end = target.end_of(at);
            let Some(image) = target.0.get(at.0 .. image_end.0)
            else {
                return SubstitutionDecision::from(false);
            };
            if scope.is_some_and(|scope| !bool::from(scope.admits(image, open))) {
                return SubstitutionDecision::from(false);
            }
            let earlier = bound.iter().find(|&&(first, ..)| {
                matches!(
                    pattern.0.get(first.0),
                    Some(&(Head::Var(ref name) | Head::Scoped(ref name, _))) if name == var
                )
            });
            match earlier {
                Some(&(_, from, to)) => {
                    if target.0.get(from.0 .. to.0) != Some(image) {
                        return SubstitutionDecision::from(false);
                    }
                },
                None => bound.push((Count(place), at, image_end)),
            }
            at = image_end;
        }
        SubstitutionDecision::from(at == end)
    }

    /// The position of the node at `node` of the walk, below `above`.
    ///
    /// # Specification
    /// - ensures: `above`'s steps, then the step of each node from the walk's
    ///   root down to `node`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`PairScheme::class`].
    /// - witness: `term::tests::the_criterion_finds_the_listings_first_redex_below_each_position`
    #[spec(ensures: |output| output.0.starts_with(&above.0))]
    fn position(
        &mut self,
        above: &TermPos,
        node: Count,
    ) -> TermPos
    {
        let &mut Self {
            ref visited,
            ref mut steps,
            ..
        } = self;
        steps.clear();
        let mut at = node.0;
        while at != 0 {
            let Some(&(_, parent, step)) = visited.get(at)
            else {
                break;
            };
            steps.push(step);
            at = parent;
        }
        TermPos(
            above
                .0
                .iter()
                .copied()
                .chain(steps.iter().rev().copied())
                .collect(),
        )
    }
}

impl PairScheme<TermAlphabet> for CompositeCriterion
{
    /// The first step strictly below the seam of `overlap` at which a cell of
    /// `store` fires, or none.
    ///
    /// # Specification
    /// - ensures: [`PairClass::Composite`] with the first position of
    ///   [`CellAlphabet::command_positions`](gandr_theory_cell_complexes::CellAlphabet::command_positions),
    ///   in its order, that the seam strictly encloses and at which a cell
    ///   fires, and the first such cell in store order; its
    ///   [`CompositePair::replay`] holds. [`PairClass::Unclassed`] when no cell
    ///   fires at any such position, or when the seam leaves the peak.
    /// - panics: none.
    /// - intension: one breadth-first walk of the peak's range below the seam,
    ///   and one lockstep match of each cell at each node until the first that
    ///   holds; the tables of the walk and the match keep their capacity from
    ///   one pair to the next, and only a witness builds a position.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over each position of a nested term, and over a
    ///   linear, a nonlinear and a scoped rule, the criterion answers the
    ///   listing's first position below and the first cell that fires there. A
    ///   position at the seam, a position beside it, a repeated variable bound
    ///   to two different images, or an image that a scope does not admit
    ///   changes the answer.
    /// - witness: `term::tests::the_criterion_finds_the_listings_first_redex_below_each_position`
    #[inline]
    #[spec(ensures: |output| match output {
        PairClass::Composite(ref step) => (CompositePair { overlap: overlap.clone(), below: step.clone() }).replay(store).is_ok()
            && TermAlphabet::command_positions(&overlap.peak).iter().take_while(|at| **at != step.at).all(|at|
                TermAlphabet::position_order(&overlap.seam, at) != PositionOrder::Encloses
                    || store.iter().all(|(_, cell)| matches!(rewrite_at(cell, &overlap.peak, at), Maybe::Absent(_)))),
        PairClass::Unclassed => TermAlphabet::command_positions(&overlap.peak).iter().all(|at|
            TermAlphabet::position_order(&overlap.seam, at) != PositionOrder::Encloses
                || store.iter().all(|(_, cell)| matches!(rewrite_at(cell, &overlap.peak, at), Maybe::Absent(_)))),
    })]
    fn class(
        &mut self,
        store: &CellStore<TermAlphabet>,
        overlap: &Overlap<TermAlphabet>,
    ) -> PairClass<TermAlphabet>
    {
        let peak = &overlap.peak;
        let Maybe::Present((root, _)) = peak.range_at(&overlap.seam.0)
        else {
            return PairClass::Unclassed;
        };
        self.visited.clear();
        self.visited.push((root, 0, PositionStep::from(0_usize)));
        let mut cursor = 0_usize;
        while let Some(&(start, ..)) = self.visited.get(cursor) {
            let Some(head) = peak.0.get(start.0)
            else {
                break;
            };
            let mut child = start.next();
            for index in 0 .. head.arity().0 {
                self.visited
                    .push((child, cursor, PositionStep::from(index)));
                child = peak.end_of(child);
            }
            if cursor != 0 {
                for (cell, rule) in store.iter() {
                    if bool::from(self.matches(rule.lhs(), peak, start)) {
                        return PairClass::Composite(CellApp {
                            cell,
                            at: self.position(&overlap.seam, Count(cursor)),
                        });
                    }
                }
            }
            cursor = cursor.saturating_add(1);
        }
        PairClass::Unclassed
    }
}
