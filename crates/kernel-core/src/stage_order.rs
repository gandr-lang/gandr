//! The order on a structural fixpoint's stages: the forest the recursion
//! typing grows while it checks one declaration.
//!
//! A fixpoint mints a root stage `ι` for the parameter it recurses on, and a
//! case on a value at an exact stage mints one child below that stage. A
//! stage's parent lies strictly above it, so a path up the forest is a chain
//! of strict steps, and every comparison reads a path's length as a lower
//! bound on how far apart two stages lie, never as an exact distance. There is
//! no stage arithmetic and no `∞` stage: the order is decided by walking up
//! one path, and a binder a call reads off several arguments stands at the
//! stage their bounds agree on ([`StageOrder::solve`]).
//!
//! The checker and the kernel each grow their own order and decide with this
//! one type, so the two judgements share one notion of "below".

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageDepth;
use gandr_kernel_term::StageId;
use quenchant_shape::shape::Maybe;

/// What an exact stage lies directly below.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Parent
{
    /// A fixpoint minted it: it lies below nothing.
    Root,
    /// A case minted it, one step below the stage its scrutinee stood at.
    Stage(StageId),
}

/// Whether every value at one stage stands at another.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Fit
{
    /// It does: the found stage lies at or below the wanted one.
    Within,
    /// It does not, or the order cannot tell.
    NotBelow,
}

/// Why a stage could not be minted below another.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unminted
{
    /// The parent names no stage of this order.
    Parent(StageId),
}

/// Which way a reading bounds the binder it was read for.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Side
{
    /// The binder stands at or above it: read where an argument's own value
    /// stands, which fits the binder's place by subsumption.
    Lower,
    /// The binder stands at or below it: read under a function argument's
    /// domain, which takes the binder's place by subsumption.
    Upper,
    /// The binder stands at it: read inside a data type's argument, whose
    /// variance the call does not read.
    Exact,
}

impl Side
{
    /// The side a reading one domain deeper takes.
    ///
    /// # Specification
    /// - ensures: lower and upper swap; exact stays.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`StageOrder::solve`].
    /// - witness: `stage_order::tests::readings_solve_at_the_least_stage_they_allow`
    #[spec(ensures: |ret| matches!((self, ret), (Self::Lower, Self::Upper) | (Self::Upper, Self::Lower) | (Self::Exact, Self::Exact)))]
    #[inline]
    #[must_use]
    pub const fn flipped(self) -> Self
    {
        match self {
            Self::Lower => Self::Upper,
            Self::Upper => Self::Lower,
            Self::Exact => Self::Exact,
        }
    }
}

/// One argument's reading of a binder: the stage it shows, and which way
/// that stage bounds the binder.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Reading
{
    /// The stage the argument's type holds where the binder is marked.
    pub stage: Stage,
    /// Which way it bounds the binder.
    pub side: Side,
}

/// Two readings of one binder no stage satisfies together.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Disagreement
{
    /// The stage the other readings settle on.
    pub first: Stage,
    /// The stage of the reading it does not satisfy.
    pub second: Stage,
}

/// Why a side of a binder's readings holds no stage yet.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Unread
{
    /// No reading of that side has been read.
    Unbounded,
}

/// How many strict steps up the forest one stage lies below another.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Steps(u32);

/// Why no path joins two stages.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Unjoined
{
    /// The upper stage is not on the lower one's path to its root.
    Apart,
    /// A stage the walk met names no stage of this order.
    Unminted,
}

/// The stages one judgement minted, each with the stage it lies directly
/// below.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct StageOrder
{
    /// Each stage's parent, indexed by [`StageId`].
    parents: Vec<Parent>,
}

impl StageOrder
{
    /// Mint a fixpoint's own stage, below nothing.
    ///
    /// # Specification
    /// - ensures: a stage not minted before, whose parent is [`Parent::Root`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two roots are apart in both directions, and a root is
    ///   within itself.
    /// - witness: `stage_order::tests::roots_are_apart`
    #[spec(
        captures: before = self.parents.len(),
        ensures: |ret| usize::from(ret) == before && self.parents.len() == before.saturating_add(1)
            && self.parents.last() == Some(&Parent::Root),
    )]
    #[inline]
    pub fn mint_root(&mut self) -> StageId
    {
        let stage = StageId::from(self.parents.len());
        self.parents.push(Parent::Root);
        stage
    }

    /// Mint a stage one step below `parent`.
    ///
    /// # Specification
    /// - ensures: a stage not minted before, whose parent is `parent`.
    /// - fails: [`Unminted::Parent`] when `parent` names no stage of this
    ///   order; nothing is minted.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child is strictly below its parent and its
    ///   grandparent, and a parent the order never minted is refused.
    /// - witness: `stage_order::tests::a_chain_is_within_each_ancestor`
    /// - witness: `stage_order::tests::an_unminted_parent_is_refused`
    #[spec(
        captures: before = self.parents.len(),
        ensures: |ret| match ret {
            Ok(stage) => usize::from(stage) == before && self.parents.last() == Some(&Parent::Stage(parent)),
            Err(Unminted::Parent(named)) => named == parent && self.parents.len() == before,
        },
    )]
    #[inline]
    pub fn mint_below(
        &mut self,
        parent: StageId,
    ) -> Result<StageId, Unminted>
    {
        if usize::from(parent) >= self.parents.len() {
            return Err(Unminted::Parent(parent));
        }
        let stage = StageId::from(self.parents.len());
        self.parents.push(Parent::Stage(parent));
        Ok(stage)
    }

    /// Whether every value at `found` stands at `wanted`: the order's
    /// subsumption.
    ///
    /// # Specification
    /// - ensures: [`Fit::Within`] exactly when an exact stage lies on its own
    ///   path to an exact `wanted`; when an exact stage lies at least `depth`
    ///   steps below a bound's anchor; when a bound's anchor lies on its path
    ///   to an exact `wanted`; and when a bound's depth, added to the steps
    ///   from its anchor up to the wanted bound's anchor, covers the wanted
    ///   depth. A stage this order never minted fits nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each of the four pairings is separated at its edge: a
    ///   child within its parent and its bound, a parent not within its own
    ///   bound, a bound within its anchor's ancestors, and a depth that falls
    ///   one step short.
    /// - witness: `stage_order::tests::a_chain_is_within_each_ancestor`
    /// - witness: `stage_order::tests::a_stage_is_not_within_its_own_bound`
    /// - witness: `stage_order::tests::bounds_compare_by_their_depth_and_anchors`
    /// - witness: `stage_order::tests::roots_are_apart`
    #[spec(ensures: |ret| match (found, wanted) {
        (Stage::At(lower), Stage::At(upper)) =>
            (ret == Fit::Within) == matches!(self.steps(lower, upper), Maybe::Present(_)),
        (Stage::At(lower), Stage::Below { anchor, depth }) =>
            (ret == Fit::Within) == matches!(self.steps(lower, anchor), Maybe::Present(Steps(steps)) if steps >= u32::from(depth)),
        (Stage::Below { anchor, .. }, Stage::At(upper)) =>
            (ret == Fit::Within) == matches!(self.steps(anchor, upper), Maybe::Present(_)),
        (Stage::Below { anchor: from, depth: below }, Stage::Below { anchor: to, depth: needed }) =>
            (ret == Fit::Within) == matches!(self.steps(from, to), Maybe::Present(Steps(steps)) if u32::from(below).saturating_add(steps) >= u32::from(needed)),
    })]
    #[inline]
    #[must_use]
    pub fn fit(
        &self,
        found: Stage,
        wanted: Stage,
    ) -> Fit
    {
        let within = match (found, wanted) {
            (Stage::At(lower), Stage::At(upper)) => {
                matches!(self.steps(lower, upper), Maybe::Present(_))
            },
            (Stage::At(lower), Stage::Below { anchor, depth }) => {
                matches!(self.steps(lower, anchor), Maybe::Present(Steps(steps)) if steps >= u32::from(depth))
            },
            (Stage::Below { anchor, .. }, Stage::At(upper)) => {
                matches!(self.steps(anchor, upper), Maybe::Present(_))
            },
            (
                Stage::Below {
                    anchor: from,
                    depth: below,
                },
                Stage::Below {
                    anchor: to,
                    depth: needed,
                },
            ) => matches!(
                self.steps(from, to),
                Maybe::Present(Steps(steps))
                    if u32::from(below).saturating_add(steps) >= u32::from(needed)
            ),
        };
        if within { Fit::Within } else { Fit::NotBelow }
    }

    /// The stage a binder stands at that every one of its readings bounds: the
    /// least the lower readings allow, and the one the exact readings name.
    ///
    /// # Specification
    /// - ensures: the exact readings' stage when there are any, else the
    ///   greatest lower reading when there is one, else the least upper one;
    ///   that stage satisfies every reading — a lower one fits within it, it
    ///   fits within an upper one, and an exact one fits both ways.
    /// - fails: [`Disagreement`] naming the first two readings no stage of the
    ///   order satisfies together: two lower or two upper readings neither of
    ///   which fits within the other, two exact readings that differ, or the
    ///   chosen stage beside a reading it does not satisfy.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of lower readings solves at its top, a lower
    ///   reading above an upper one and two apart lower readings are refused,
    ///   and an exact reading wins over a lower one it fits above.
    /// - witness: `stage_order::tests::readings_solve_at_the_least_stage_they_allow`
    /// - witness: `stage_order::tests::readings_no_stage_satisfies_disagree`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&solved| core::iter::once(&first)
        .chain(rest)
        .all(|&reading| self.bounded(solved, reading) == Fit::Within)))]
    #[inline]
    pub fn solve(
        &self,
        first: Reading,
        rest: &[Reading],
    ) -> Result<Stage, Disagreement>
    {
        let mut lower: Maybe<Stage, Unread> = Maybe::Absent(Unread::Unbounded);
        let mut upper: Maybe<Stage, Unread> = Maybe::Absent(Unread::Unbounded);
        let mut exact: Maybe<Stage, Unread> = Maybe::Absent(Unread::Unbounded);
        for &reading in core::iter::once(&first).chain(rest) {
            let held = match reading.side {
                Side::Lower => &mut lower,
                Side::Upper => &mut upper,
                Side::Exact => &mut exact,
            };
            *held = Maybe::Present(match *held {
                Maybe::Present(stage) => match reading.side {
                    Side::Lower => self.greater(stage, reading.stage)?,
                    Side::Upper => self.lesser(stage, reading.stage)?,
                    Side::Exact => self.same(stage, reading.stage)?,
                },
                Maybe::Absent(_) => reading.stage,
            });
        }
        let solved = match (exact, lower, upper) {
            (Maybe::Present(stage), ..)
            | (Maybe::Absent(_), Maybe::Present(stage), _)
            | (Maybe::Absent(_), Maybe::Absent(_), Maybe::Present(stage)) => stage,
            (Maybe::Absent(_), Maybe::Absent(_), Maybe::Absent(_)) => first.stage,
        };
        for (bound, side) in [(lower, Side::Lower), (upper, Side::Upper)] {
            if let Maybe::Present(stage) = bound
                && self.bounded(solved, Reading { stage, side }) == Fit::NotBelow
            {
                return Err(Disagreement {
                    first: solved,
                    second: stage,
                });
            }
        }
        Ok(solved)
    }

    /// Whether `solved` satisfies `reading`: [`Fit::Within`] when it lies
    /// where the reading's side bounds it.
    ///
    /// # Specification
    /// trivial.
    fn bounded(
        &self,
        solved: Stage,
        reading: Reading,
    ) -> Fit
    {
        let below = self.fit(reading.stage, solved);
        let above = self.fit(solved, reading.stage);
        match (reading.side, below, above) {
            (Side::Lower, fit, _) | (Side::Upper, _, fit) => fit,
            (Side::Exact, Fit::Within, Fit::Within) => Fit::Within,
            (Side::Exact, Fit::NotBelow, _) | (Side::Exact, _, Fit::NotBelow) => Fit::NotBelow,
        }
    }

    /// The greater of two lower readings.
    ///
    /// # Specification
    /// trivial.
    fn greater(
        &self,
        held: Stage,
        read: Stage,
    ) -> Result<Stage, Disagreement>
    {
        if self.fit(held, read) == Fit::Within {
            Ok(read)
        }
        else if self.fit(read, held) == Fit::Within {
            Ok(held)
        }
        else {
            Err(Disagreement {
                first: held,
                second: read,
            })
        }
    }

    /// The lesser of two upper readings.
    ///
    /// # Specification
    /// trivial.
    fn lesser(
        &self,
        held: Stage,
        read: Stage,
    ) -> Result<Stage, Disagreement>
    {
        self.greater(held, read)
            .map(|greater| if greater == read { held } else { read })
    }

    /// Two exact readings, which must name one stage.
    ///
    /// # Specification
    /// trivial.
    fn same(
        &self,
        held: Stage,
        read: Stage,
    ) -> Result<Stage, Disagreement>
    {
        if self.fit(held, read) == Fit::Within && self.fit(read, held) == Fit::Within {
            Ok(held)
        }
        else {
            Err(Disagreement {
                first: held,
                second: read,
            })
        }
    }

    /// The steps from the exact stage `from` up to its ancestor `to`.
    ///
    /// # Specification
    /// - ensures: zero steps exactly when `from == to`; otherwise one more than
    ///   the steps from `from`'s parent; [`Unjoined::Apart`] when the walk
    ///   reaches a root before `to`, and [`Unjoined::Unminted`] when it meets a
    ///   stage this order never minted.
    /// - panics: none.
    /// - intension: a loop up the parent chain, finite because a parent is
    ///   always minted before its child, so each step lowers the index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — read through [`Self::fit`], whose witnesses separate
    ///   an ancestor, a sibling and an unminted stage.
    /// - witness: `stage_order::tests::a_chain_is_within_each_ancestor`
    /// - witness: `stage_order::tests::siblings_are_apart`
    /// - witness: `stage_order::tests::an_unminted_parent_is_refused`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(Steps(count)) => (count == 0) == (from == to),
        Maybe::Absent(_) => true,
    })]
    fn steps(
        &self,
        from: StageId,
        to: StageId,
    ) -> Maybe<Steps, Unjoined>
    {
        let mut at = from;
        let mut steps = 0_u32;
        loop {
            if at == to {
                return if usize::from(at) < self.parents.len() {
                    Maybe::Present(Steps(steps))
                }
                else {
                    Maybe::Absent(Unjoined::Unminted)
                };
            }
            match self.parents.get(usize::from(at)) {
                Some(&Parent::Stage(parent)) => {
                    at = parent;
                    steps = steps.saturating_add(1);
                },
                Some(&Parent::Root) => return Maybe::Absent(Unjoined::Apart),
                None => return Maybe::Absent(Unjoined::Unminted),
            }
        }
    }
}

/// The bound one step below `stage`: every stage strictly below it.
///
/// # Specification
/// - ensures: `<s` for an exact `s`, and the same anchor one step deeper for a
///   bound.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an exact stage and a bound each move one step, so a lost
///   step or a reset anchor differs.
/// - witness: `stage_order::tests::below_moves_one_step`
#[spec(ensures: |ret| match stage {
    Stage::At(anchor) => ret == Stage::Below { anchor, depth: StageDepth::ONE },
    Stage::Below { anchor, depth } => ret == Stage::Below { anchor, depth: depth.deeper() },
})]
#[inline]
#[must_use]
pub fn below(stage: Stage) -> Stage
{
    match stage {
        Stage::At(anchor) => Stage::Below {
            anchor,
            depth: StageDepth::ONE,
        },
        Stage::Below { anchor, depth } => Stage::Below {
            anchor,
            depth: depth.deeper(),
        },
    }
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageDepth;
    use gandr_kernel_term::StageId;

    use super::Disagreement;
    use super::Fit;
    use super::Reading;
    use super::Side;
    use super::StageOrder;
    use super::Unminted;
    use super::below;

    /// # Specification
    /// trivial.
    #[test]
    fn roots_are_apart()
    {
        let mut order = StageOrder::default();
        let first = order.mint_root();
        let second = order.mint_root();
        assert_eq!(order.fit(Stage::At(first), Stage::At(first)), Fit::Within);
        assert_eq!(
            order.fit(Stage::At(first), Stage::At(second)),
            Fit::NotBelow
        );
        assert_eq!(
            order.fit(Stage::At(second), Stage::At(first)),
            Fit::NotBelow
        );
    }

    /// # Specification
    /// trivial.
    #[test]
    fn a_chain_is_within_each_ancestor()
    {
        let mut order = StageOrder::default();
        let root = order.mint_root();
        let child = order.mint_below(root).expect("the root is minted");
        let grandchild = order.mint_below(child).expect("the child is minted");
        assert_eq!(
            order.fit(Stage::At(grandchild), Stage::At(root)),
            Fit::Within
        );
        assert_eq!(
            order.fit(Stage::At(grandchild), below(Stage::At(root))),
            Fit::Within
        );
        assert_eq!(
            order.fit(Stage::At(grandchild), below(below(Stage::At(root)))),
            Fit::Within
        );
        assert_eq!(
            order.fit(Stage::At(grandchild), below(below(below(Stage::At(root))))),
            Fit::NotBelow,
            "two steps cover no third"
        );
        assert_eq!(order.fit(Stage::At(root), Stage::At(child)), Fit::NotBelow);
    }

    /// # Specification
    /// trivial.
    #[test]
    fn a_stage_is_not_within_its_own_bound()
    {
        let mut order = StageOrder::default();
        let root = order.mint_root();
        assert_eq!(
            order.fit(Stage::At(root), below(Stage::At(root))),
            Fit::NotBelow
        );
        assert_eq!(
            order.fit(below(Stage::At(root)), Stage::At(root)),
            Fit::Within
        );
    }

    /// # Specification
    /// trivial.
    #[test]
    fn bounds_compare_by_their_depth_and_anchors()
    {
        let mut order = StageOrder::default();
        let root = order.mint_root();
        let child = order.mint_below(root).expect("the root is minted");
        let under_child = below(Stage::At(child));
        assert_eq!(
            order.fit(under_child, below(below(Stage::At(root)))),
            Fit::Within
        );
        assert_eq!(
            order.fit(under_child, below(below(below(Stage::At(root))))),
            Fit::NotBelow,
            "one step and one edge cover no third"
        );
        assert_eq!(
            order.fit(below(Stage::At(root)), under_child),
            Fit::NotBelow
        );
    }

    /// # Specification
    /// trivial.
    #[test]
    fn siblings_are_apart()
    {
        let mut order = StageOrder::default();
        let root = order.mint_root();
        let left = order.mint_below(root).expect("the root is minted");
        let right = order.mint_below(root).expect("the root is minted");
        assert_eq!(order.fit(Stage::At(left), Stage::At(right)), Fit::NotBelow);
        assert_eq!(
            order.fit(Stage::At(left), below(Stage::At(root))),
            Fit::Within
        );
        assert_eq!(
            order.fit(Stage::At(right), below(Stage::At(root))),
            Fit::Within
        );
    }

    /// # Specification
    /// trivial.
    #[test]
    fn an_unminted_parent_is_refused()
    {
        let mut order = StageOrder::default();
        let stray = StageId::from(3_usize);
        assert_eq!(order.mint_below(stray), Err(Unminted::Parent(stray)));
        assert_eq!(order.fit(Stage::At(stray), Stage::At(stray)), Fit::NotBelow);
        let root = order.mint_root();
        let next = StageId::from(usize::from(root) + 1);
        assert_eq!(
            order.fit(Stage::At(next), Stage::At(next)),
            Fit::NotBelow,
            "the stage one past the last minted is unminted"
        );
    }

    /// # Specification
    /// trivial.
    #[test]
    fn below_moves_one_step()
    {
        let anchor = StageId::from(0_usize);
        assert_eq!(below(Stage::At(anchor)), Stage::Below {
            anchor,
            depth: StageDepth::ONE
        });
        assert_eq!(below(below(Stage::At(anchor))), Stage::Below {
            anchor,
            depth: StageDepth::ONE.deeper()
        });
    }

    /// # Specification
    /// trivial.
    #[test]
    fn readings_solve_at_the_least_stage_they_allow()
    {
        let mut order = StageOrder::default();
        let root = Stage::At(order.mint_root());
        let child = Stage::At(
            order
                .mint_below(StageId::from(0_usize))
                .expect("the root is minted"),
        );
        let read = |stage, side| Reading { stage, side };
        assert_eq!(
            order.solve(read(child, Side::Lower), &[read(root, Side::Lower)]),
            Ok(root),
            "a chain of lower readings solves at its top"
        );
        assert_eq!(
            order.solve(read(root, Side::Upper), &[read(child, Side::Lower)]),
            Ok(child),
            "the least stage the lower reading allows, under the upper one"
        );
        assert_eq!(
            order.solve(read(child, Side::Upper), &[read(root, Side::Upper)]),
            Ok(child),
            "upper readings alone solve at their least"
        );
        assert_eq!(
            order.solve(read(child, Side::Lower), &[read(root, Side::Exact)]),
            Ok(root),
            "an exact reading wins over a lower one it fits above"
        );
        assert_eq!(Side::Lower.flipped(), Side::Upper);
        assert_eq!(Side::Exact.flipped(), Side::Exact);
    }

    /// # Specification
    /// trivial.
    #[test]
    fn readings_no_stage_satisfies_disagree()
    {
        let mut order = StageOrder::default();
        let root = Stage::At(order.mint_root());
        let child = Stage::At(
            order
                .mint_below(StageId::from(0_usize))
                .expect("the root is minted"),
        );
        let apart = Stage::At(order.mint_root());
        let read = |stage, side| Reading { stage, side };
        assert_eq!(
            order.solve(read(root, Side::Lower), &[read(child, Side::Upper)]),
            Err(Disagreement {
                first: root,
                second: child,
            }),
            "a lower reading above an upper one"
        );
        assert_eq!(
            order.solve(read(root, Side::Lower), &[read(apart, Side::Lower)]),
            Err(Disagreement {
                first: root,
                second: apart,
            }),
            "two lower readings on apart roots"
        );
        assert_eq!(
            order.solve(read(root, Side::Exact), &[read(child, Side::Exact)]),
            Err(Disagreement {
                first: root,
                second: child,
            }),
            "two exact readings that differ"
        );
    }
}
