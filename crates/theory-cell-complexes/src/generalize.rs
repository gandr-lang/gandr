//! Anti-unification of command patterns: the least general generalization of
//! a family, the dual of [`crate::subst::unify_cmd`]'s most general unifier.
//!
//! Where unification finds the most general pattern two patterns both
//! instantiate to, anti-unification finds the most specific pattern tuple
//! every member of a family instantiates. The walk keeps a head every member
//! shares and descends below it; where the members differ it stands a fresh
//! metavariable, a point, whose arms are the members' subterms there. Two
//! positions whose subterms agree member by member stand one point, which is
//! what makes the result least general rather than merely general.
//!
//! Producers and consumer spines are generalized by different walks, both
//! explicit: a producer column by a worklist of columns and constructor
//! builds, a spine from the cut outward, one shared frame at a time, until
//! the members' remaining spines differ or end. Neither recurses, and a
//! consumer's operation arguments are producer columns, so the consumer walk
//! calls the producer walk and never the reverse.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use crate::alphabet::Generalization;
use crate::alphabet::GeneralizationArm;
use crate::alphabet::GeneralizationPoint;
use crate::alphabet::anti_unification;
use crate::pattern::ArgumentCount;
use crate::pattern::CmdPat;
use crate::pattern::ConsPat;
use crate::pattern::ConsRef;
use crate::pattern::ConsView;
use crate::pattern::HoleName;
use crate::pattern::MetaVar;
use crate::pattern::ProdPat;
use crate::pattern::ProdRef;
use crate::pattern::ProdView;
use crate::pattern::SpineEnd;
use crate::pattern::SpineFrame;
use crate::pattern::Sym;
use crate::sequent::SequentAlphabet;
use crate::subst::substitution_from;

/// One subterm per member at one position of the walk, in family order.
///
/// A family has a first member, so a column is never empty.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Column<T>
{
    /// The first member's subterm.
    first: T,
    /// Every other member's subterm, in family order.
    rest: Vec<T>,
}

impl<T: Copy> Column<T>
{
    /// Every member's subterm, in family order.
    ///
    /// # Specification
    /// trivial.
    fn iter(&self) -> impl Iterator<Item = T> + '_
    {
        core::iter::once(self.first).chain(self.rest.iter().copied())
    }

    /// The column with `part` taken of every member's subterm.
    ///
    /// # Specification
    /// trivial.
    fn map<U, F>(
        &self,
        part: F,
    ) -> Column<U>
    where
        F: Fn(T) -> U,
    {
        Column {
            first: part(self.first),
            rest: self.rest.iter().copied().map(&part).collect(),
        }
    }
}

/// The member subterms one point stands for.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Disagreement<'term>
{
    /// A producer column whose heads differ.
    Prod(Column<ProdRef<'term>>),
    /// A consumer column whose outermost frames or ends differ.
    Cons(Column<ConsRef<'term>>),
}

/// The points stood so far, each with what it stands for, and the names a
/// new point may not take.
#[derive(Debug)]
struct Points<'term>
{
    /// Every hole name a member wears.
    taken: BTreeSet<HoleName>,
    /// The suffix the next fresh name is tried with.
    next: usize,
    /// The points, in the order the walk stood them.
    stood: Vec<(MetaVar, Disagreement<'term>)>,
}

impl<'term> Points<'term>
{
    /// The point standing for `disagreement`: the one already stood for an
    /// equal column, or a new one under a fresh name.
    ///
    /// # Specification
    /// - ensures: one metavariable per distinct column, of the column's
    ///   category, its name worn by no member and by no other point.
    /// - panics: none.
    fn stand(
        &mut self,
        disagreement: Disagreement<'term>,
    ) -> MetaVar
    {
        if let Some(stood) = self.stood.iter().find(|stood| stood.1 == disagreement) {
            return stood.0.clone();
        }
        let name = self.fresh();
        let var = match disagreement {
            | Disagreement::Prod(_) => MetaVar::producer(name),
            | Disagreement::Cons(_) => MetaVar::consumer(name),
        };
        self.stood.push((var.clone(), disagreement));
        var
    }

    /// A hole name no member wears and no point has taken.
    ///
    /// # Specification
    /// - ensures: `$g$` followed by the least suffix not yet tried whose name
    ///   is not taken; the name is taken from then on.
    /// - panics: none.
    /// - intension: the taken set is finite, so the search ends; a counter held
    ///   in memory never reaches the saturation bound.
    fn fresh(&mut self) -> HoleName
    {
        loop {
            let suffix = self.next;
            self.next = self.next.saturating_add(1);
            let name = HoleName::from(format!("$g${suffix}"));
            if self.taken.insert(name.clone()) {
                return name;
            }
        }
    }

    /// The points, each with one arm per member.
    ///
    /// # Specification
    /// - ensures: one point per stood metavariable, in standing order, whose
    ///   arms bind it alone to each member's subterm, in family order, with
    ///   that subterm's node count.
    /// - panics: none.
    fn into_points(self) -> Vec<GeneralizationPoint<SequentAlphabet>>
    {
        self.stood
            .into_iter()
            .map(|(var, disagreement)| {
                let arms = match disagreement {
                    | Disagreement::Prod(column) => column
                        .iter()
                        .map(|subterm| GeneralizationArm {
                            binding: substitution_from(
                                BTreeMap::from([(var.clone(), subterm.to_pattern())]),
                                BTreeMap::new(),
                            ),
                            size: subterm.size(),
                        })
                        .collect(),
                    | Disagreement::Cons(column) => column
                        .iter()
                        .map(|subterm| GeneralizationArm {
                            binding: substitution_from(
                                BTreeMap::new(),
                                BTreeMap::from([(var.clone(), subterm.to_pattern())]),
                            ),
                            size: subterm.size(),
                        })
                        .collect(),
                };
                GeneralizationPoint { var, arms }
            })
            .collect()
    }
}

/// What a producer column shares at its root.
enum ProdShape<'term>
{
    /// Every member is one metavariable.
    Meta(&'term MetaVar),
    /// Every member applies one constructor at one arity: its argument
    /// columns, left to right.
    Ctor(&'term Sym, Vec<Column<ProdRef<'term>>>),
    /// The members' heads differ.
    Differ,
}

/// What a consumer column shares at its outermost frame or end.
enum ConsShape<'term>
{
    /// Every member ends in `★`.
    Top,
    /// Every member is one consumer metavariable.
    Meta(&'term MetaVar),
    /// Every member's outermost frame is one operation at one arity.
    Op
    {
        /// The shared operation symbol.
        op: &'term Sym,
        /// The argument columns, left to right.
        args: Vec<Column<ProdRef<'term>>>,
        /// The continuation column, one frame in.
        ret: Column<ConsRef<'term>>,
    },
    /// Every member's outermost frame re-wraps with one constructor.
    Frame
    {
        /// The shared constructor symbol.
        ctor: &'term Sym,
        /// The continuation column, one frame in.
        ret: Column<ConsRef<'term>>,
    },
    /// The members' outermost frames or ends differ.
    Differ,
}

/// The columns of `first`'s children beside the other members' children, one
/// column per child.
///
/// # Specification
/// - requires: every iterator of `rest` yields as many children as `first`,
///   which equal heads guarantee, since a head carries its arity.
/// - ensures: one column per child of `first`, left to right, holding each
///   member's child at that index in family order.
/// - panics: none.
fn child_columns<'term, I>(
    first: I,
    rest: Vec<I>,
) -> Vec<Column<ProdRef<'term>>>
where
    I: Iterator<Item = ProdRef<'term>>,
{
    let mut rest = rest;
    first
        .map(|child| Column {
            first: child,
            rest: rest.iter_mut().filter_map(Iterator::next).collect(),
        })
        .collect()
}

/// What a producer column shares at its root.
///
/// # Specification
/// - ensures: [`ProdShape::Differ`] when two members' heads differ, in symbol,
///   arity or metavariable; otherwise the shared metavariable or the shared
///   constructor with its argument columns.
/// - panics: none.
fn prod_shape<'term>(column: &Column<ProdRef<'term>>) -> ProdShape<'term>
{
    let head = column.first.head();
    if column.rest.iter().any(|member| member.head() != head) {
        return ProdShape::Differ;
    }
    match column.first.view() {
        | ProdView::Meta(var) => ProdShape::Meta(var),
        | ProdView::Ctor { ctor, args } => ProdShape::Ctor(
            ctor,
            child_columns(
                args,
                column.rest.iter().map(|member| member.children()).collect(),
            ),
        ),
    }
}

/// What a consumer column shares at its outermost frame or end.
///
/// # Specification
/// - ensures: the shared end, or the shared outermost frame with its argument
///   columns and its continuation column, when every member agrees on it;
///   [`ConsShape::Differ`] otherwise, including when one member's spine ends
///   where another's carries a frame.
/// - panics: none.
fn cons_shape<'term>(column: &Column<ConsRef<'term>>) -> ConsShape<'term>
{
    match column.first.view() {
        | ConsView::Top => {
            if column
                .rest
                .iter()
                .all(|member| matches!(member.view(), ConsView::Top))
            {
                ConsShape::Top
            }
            else {
                ConsShape::Differ
            }
        },
        | ConsView::Meta(var) => {
            if column
                .rest
                .iter()
                .all(|member| matches!(member.view(), ConsView::Meta(other) if other == var))
            {
                ConsShape::Meta(var)
            }
            else {
                ConsShape::Differ
            }
        },
        | ConsView::Frame { ctor, ret } => {
            let mut rets = Vec::with_capacity(column.rest.len());
            for member in &column.rest {
                match member.view() {
                    | ConsView::Frame {
                        ctor: other,
                        ret: theirs,
                    } if other == ctor => rets.push(theirs),
                    | ConsView::Frame { .. }
                    | ConsView::Op { .. }
                    | ConsView::Meta(_)
                    | ConsView::Top => {
                        return ConsShape::Differ;
                    },
                }
            }
            ConsShape::Frame {
                ctor,
                ret: Column {
                    first: ret,
                    rest: rets,
                },
            }
        },
        | ConsView::Op { op, args, ret } => {
            let arity = args.len();
            let mut rest_args = Vec::with_capacity(column.rest.len());
            let mut rets = Vec::with_capacity(column.rest.len());
            for member in &column.rest {
                match member.view() {
                    | ConsView::Op {
                        op: other,
                        args: theirs,
                        ret: their_ret,
                    } if other == op && theirs.len() == arity => {
                        rest_args.push(theirs);
                        rets.push(their_ret);
                    },
                    | ConsView::Op { .. }
                    | ConsView::Frame { .. }
                    | ConsView::Meta(_)
                    | ConsView::Top => {
                        return ConsShape::Differ;
                    },
                }
            }
            ConsShape::Op {
                op,
                args: child_columns(args, rest_args),
                ret: Column {
                    first: ret,
                    rest: rets,
                },
            }
        },
    }
}

/// One pending task of the producer walk.
enum ProdTask<'term>
{
    /// Generalize one column, leaving its pattern on the built stack.
    Visit(Column<ProdRef<'term>>),
    /// Apply a shared constructor to the last patterns built, one per
    /// argument.
    Build(&'term Sym, ArgumentCount),
}

/// The least general generalization of one producer column.
///
/// # Specification
/// - ensures: a pattern every member instantiates under its point arms; a
///   shared metavariable or constructor is kept, and a column whose heads
///   differ is the metavariable of the point standing for it, stood in `points`
///   if new.
/// - panics: none.
/// - intension: one task per column and one build per shared constructor below
///   the root, on a heap worklist; argument columns are visited left to right,
///   so points are stood in the members' pre-order.
fn generalize_prod<'term>(
    column: Column<ProdRef<'term>>,
    points: &mut Points<'term>,
) -> ProdPat
{
    let (ctor, children) = match prod_shape(&column) {
        | ProdShape::Meta(var) => return ProdPat::meta(var.hole().clone()),
        | ProdShape::Differ => {
            return ProdPat::meta(points.stand(Disagreement::Prod(column)).hole().clone());
        },
        | ProdShape::Ctor(ctor, children) => (ctor, children),
    };
    let mut built: Vec<ProdPat> = Vec::with_capacity(children.len());
    let mut tasks: Vec<ProdTask<'term>> = children.into_iter().rev().map(ProdTask::Visit).collect();
    while let Some(task) = tasks.pop() {
        match task {
            | ProdTask::Visit(column) => match prod_shape(&column) {
                | ProdShape::Meta(var) => built.push(ProdPat::meta(var.hole().clone())),
                | ProdShape::Differ => {
                    let var = points.stand(Disagreement::Prod(column));
                    built.push(ProdPat::meta(var.hole().clone()));
                },
                | ProdShape::Ctor(ctor, children) => {
                    tasks.push(ProdTask::Build(ctor, ArgumentCount::from(children.len())));
                    tasks.extend(children.into_iter().rev().map(ProdTask::Visit));
                },
            },
            | ProdTask::Build(ctor, arity) => {
                let first = built.len().saturating_sub(usize::from(arity));
                let args = built.split_off(first);
                built.push(ProdPat::ctor(ctor.clone(), args));
            },
        }
    }
    ProdPat::ctor(ctor.clone(), built)
}

/// The least general generalization of one consumer column.
///
/// # Specification
/// - ensures: a spine every member instantiates under its point arms: the
///   frames every member shares from the cut outward are kept, their argument
///   columns generalized as producers, and the first column that differs is the
///   consumer metavariable of the point standing for the members' remaining
///   spines.
/// - panics: none.
/// - intension: one step per shared frame; each step strips one frame from
///   every member, so the walk ends within the shortest spine.
fn generalize_cons<'term>(
    column: Column<ConsRef<'term>>,
    points: &mut Points<'term>,
) -> ConsPat
{
    // Outermost first while walking; a spine lists them innermost first.
    let mut frames: Vec<SpineFrame> = Vec::new();
    let mut current = column;
    let end = loop {
        match cons_shape(&current) {
            | ConsShape::Top => break SpineEnd::Top,
            | ConsShape::Meta(var) => break SpineEnd::Meta(var.clone()),
            | ConsShape::Differ => break SpineEnd::Meta(points.stand(Disagreement::Cons(current))),
            | ConsShape::Frame { ctor, ret } => {
                frames.push(SpineFrame::Frame(ctor.clone()));
                current = ret;
            },
            | ConsShape::Op { op, args, ret } => {
                let args = args
                    .into_iter()
                    .map(|arg| generalize_prod(arg, points))
                    .collect();
                frames.push(SpineFrame::Op {
                    op: op.clone(),
                    args,
                });
                current = ret;
            },
        }
    };
    frames.reverse();
    ConsPat::from_parts(frames, end)
}

/// The least general generalization of a family of command-pattern tuples.
///
/// # Specification
/// - requires: none; a member may carry metavariables of its own, which an arm
///   binds like any other subterm.
/// - ensures: one cut per component, of the members' shared polarity; for every
///   member, applying its arm at every point to each cut gives the member's
///   component back; a shared head is kept and descended into, so a point
///   stands only where two members differ; two positions whose subterms agree
///   member by member stand one point; every point's name is `$g$` and a
///   suffix, worn by no member; the points are listed in the order the walk
///   first meets them — component by component, the producer before the
///   consumer, left to right, a spine from the cut outward.
/// - provides: [`anti_unification::Absent::EmptyFamily`] for a family with no
///   member; [`anti_unification::Absent::RaggedFamily`] when two members have
///   different lengths; [`anti_unification::Absent::Ungeneralizable`] when two
///   members' cuts differ in polarity, where the grammar has no command
///   metavariable to stand.
/// - panics: none.
/// - intension: one walk over the members in lockstep, linear in the
///   generalization's size times the family's; a new point is compared with
///   every point already stood, so the walk is quadratic in the number of
///   points.
///
/// # Adequacy
/// - hypothesis: L3 — a shared constructor is kept above a point, a repeated
///   disagreement stands one point while two different ones stand two, a spine
///   is shared from the cut outward until it differs, a point's name avoids
///   every member's, a joint tuple shares a point across components, and each
///   refusal is reached by its own family. L1 — every generated family is
///   reproduced from its generalization by each member's arms, no point's arms
///   all bind one image, no two points stand for one column, and a pattern
///   every member instantiates matches the generalization.
/// - witness: `generalize::tests::a_shared_constructor_is_kept_above_the_point`
/// - witness: `generalize::tests::positions_agreeing_member_by_member_stand_one_point`
/// - witness: `generalize::tests::a_spine_is_shared_from_the_cut_outward`
/// - witness: `generalize::tests::a_point_takes_a_name_no_member_wears`
/// - witness: `generalize::tests::a_tuple_shares_its_points_across_components`
/// - witness: `generalize::tests::a_family_without_a_generalization_is_refused_by_name`
/// - witness: `tests::generalize::every_member_is_its_generalization_under_its_arms`
/// - witness: `tests::generalize::a_shared_pattern_matches_the_generalization`
#[inline]
pub fn anti_unify_cmd(
    family: &[&[CmdPat]]
) -> Maybe<Generalization<SequentAlphabet>, anti_unification::Absent>
{
    let Some((first, rest)) = family.split_first()
    else {
        return Maybe::Absent(anti_unification::Absent::EmptyFamily);
    };
    if rest.iter().any(|member| member.len() != first.len()) {
        return Maybe::Absent(anti_unification::Absent::RaggedFamily);
    }
    let mut points = Points {
        taken: family
            .iter()
            .flat_map(|member| member.iter())
            .flat_map(CmdPat::metavars)
            .map(|var| var.hole().clone())
            .collect(),
        next: 0,
        stood: Vec::new(),
    };
    let mut patterns = Vec::with_capacity(first.len());
    for (component, cut) in first.iter().enumerate() {
        let cuts = Column {
            first: cut,
            rest: rest
                .iter()
                .filter_map(|member| member.get(component))
                .collect(),
        };
        if cuts
            .rest
            .iter()
            .any(|other| other.polarity() != cut.polarity())
        {
            return Maybe::Absent(anti_unification::Absent::Ungeneralizable);
        }
        let prod = generalize_prod(cuts.map(|member| member.producer().to_ref()), &mut points);
        let cons = generalize_cons(cuts.map(|member| member.consumer().to_ref()), &mut points);
        patterns.push(CmdPat::cut(cut.polarity(), prod, cons));
    }
    Maybe::Present(Generalization {
        patterns,
        points: points.into_points(),
    })
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::alphabet::CellAlphabet as _;
    use crate::polarity::Polarity;

    /// A count of `Succ` constructors.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Successors(usize);

    /// The index of one member in a test family.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Member(usize);

    /// `n` successors of `Zero`.
    ///
    /// # Specification
    /// trivial.
    fn numeral(n: Successors) -> ProdPat
    {
        (0 .. n.0).fold(ProdPat::ctor("Zero", []), |inner, _| {
            ProdPat::ctor("Succ", [inner])
        })
    }

    /// The positive cut `⟨prod | cons⟩`.
    ///
    /// # Specification
    /// trivial.
    fn cut(
        prod: ProdPat,
        cons: ConsPat,
    ) -> CmdPat
    {
        CmdPat::cut(Polarity::Positive, prod, cons)
    }

    /// The generalization of `family`, or the test fails.
    ///
    /// # Specification
    /// - panics: when the family has no generalization, which the calling test
    ///   rules out.
    fn generalized(family: &[&[CmdPat]]) -> Generalization<SequentAlphabet>
    {
        let Maybe::Present(generalization) = anti_unify_cmd(family)
        else {
            panic!("the family generalizes");
        };
        generalization
    }

    /// Every component of member `member`, rebuilt from the generalization by
    /// applying each point's arm in turn.
    ///
    /// # Specification
    /// - panics: when the member index is out of range, a test defect.
    fn rebuilt(
        generalization: &Generalization<SequentAlphabet>,
        member: Member,
    ) -> Vec<CmdPat>
    {
        generalization
            .patterns
            .iter()
            .map(|pattern| {
                generalization
                    .points
                    .iter()
                    .fold(pattern.clone(), |term, point| {
                        point.arms[member.0].binding.apply_cmd(&term)
                    })
            })
            .collect()
    }

    #[test]
    fn a_shared_constructor_is_kept_above_the_point()
    {
        let spine = || ConsPat::op("add", [numeral(Successors(0))], ConsPat::top());
        let one = cut(numeral(Successors(1)), spine());
        let two = cut(numeral(Successors(2)), spine());
        let generalization =
            generalized(&[core::slice::from_ref(&one), core::slice::from_ref(&two)]);
        assert_eq!(
            1,
            generalization.points.len(),
            "the numerals differ below one Succ"
        );
        let point = &generalization.points[0];
        assert_eq!(
            cut(
                ProdPat::ctor("Succ", [ProdPat::meta(point.var.hole().clone())]),
                spine(),
            ),
            generalization.patterns[0],
            "the shared Succ and the shared spine are kept"
        );
        assert_eq!(
            [1_usize, 2_usize],
            [0_usize, 1_usize].map(|member| usize::from(point.arms[member].size)),
            "each arm is the member's subterm under the shared Succ"
        );
        assert_eq!(
            (alloc::vec![one], alloc::vec![two]),
            (
                rebuilt(&generalization, Member(0)),
                rebuilt(&generalization, Member(1))
            ),
            "each member is rebuilt"
        );
    }

    #[test]
    fn positions_agreeing_member_by_member_stand_one_point()
    {
        let pair = |left: Successors, right: Successors| {
            cut(
                ProdPat::ctor("Pair", [numeral(left), numeral(right)]),
                ConsPat::top(),
            )
        };
        let (zero, one) = (Successors(0), Successors(1));
        let repeated = generalized(&[&[pair(zero, zero)], &[pair(one, one)]]);
        assert_eq!(
            1,
            repeated.points.len(),
            "one disagreement, met twice, stands one point"
        );
        let var = repeated.points[0].var.hole().clone();
        assert_eq!(
            cut(
                ProdPat::ctor("Pair", [ProdPat::meta(var.clone()), ProdPat::meta(var)]),
                ConsPat::top(),
            ),
            repeated.patterns[0],
            "and both positions carry it"
        );
        let crossed = generalized(&[&[pair(zero, one)], &[pair(one, zero)]]);
        assert_eq!(
            2,
            crossed.points.len(),
            "two disagreements that differ member by member stand two points"
        );
    }

    #[test]
    fn a_spine_is_shared_from_the_cut_outward()
    {
        let (zero, one) = (Successors(0), Successors(1));
        let framed = cut(
            numeral(zero),
            ConsPat::op(
                "add",
                [numeral(zero)],
                ConsPat::frame("Succ", ConsPat::top()),
            ),
        );
        let bare = cut(
            numeral(zero),
            ConsPat::op("add", [numeral(one)], ConsPat::top()),
        );
        let generalization =
            generalized(&[core::slice::from_ref(&framed), core::slice::from_ref(&bare)]);
        assert_eq!(
            2,
            generalization.points.len(),
            "the operation's argument and the rest of the spine differ"
        );
        let [argument, rest] = [0, 1].map(|index| generalization.points[index].var.clone());
        assert_eq!(
            crate::pattern::Cat::Producer,
            argument.cat(),
            "the argument point stands for producers"
        );
        assert_eq!(
            crate::pattern::Cat::Consumer,
            rest.cat(),
            "the spine point stands for the remaining spines"
        );
        assert_eq!(
            cut(
                numeral(zero),
                ConsPat::op(
                    "add",
                    [ProdPat::meta(argument.hole().clone())],
                    ConsPat::meta(rest.hole().clone()),
                ),
            ),
            generalization.patterns[0],
            "the shared operation frame is kept outside the point"
        );
        assert_eq!(
            (alloc::vec![framed], alloc::vec![bare]),
            (
                rebuilt(&generalization, Member(0)),
                rebuilt(&generalization, Member(1))
            ),
            "the framed member and the bare one are rebuilt"
        );
    }

    #[test]
    fn a_point_takes_a_name_no_member_wears()
    {
        let wearing = cut(ProdPat::meta("$g$0"), ConsPat::top());
        let ground = cut(numeral(Successors(0)), ConsPat::top());
        let generalization = generalized(&[
            core::slice::from_ref(&wearing),
            core::slice::from_ref(&ground),
        ]);
        assert_eq!(
            HoleName::new("$g$1"),
            *generalization.points[0].var.hole(),
            "the first fresh name is worn by a member, so the next is taken"
        );
        assert_eq!(
            (alloc::vec![wearing], alloc::vec![ground]),
            (
                rebuilt(&generalization, Member(0)),
                rebuilt(&generalization, Member(1))
            ),
            "the member's own hole is an arm, beside the ground one"
        );
    }

    #[test]
    fn a_tuple_shares_its_points_across_components()
    {
        let member = |n: Successors| {
            alloc::vec![
                cut(numeral(n), ConsPat::top()),
                cut(
                    ProdPat::ctor("Pair", [numeral(n), numeral(Successors(0))]),
                    ConsPat::top(),
                ),
            ]
        };
        let (one, two) = (member(Successors(1)), member(Successors(2)));
        let generalization = generalized(&[&one, &two]);
        assert_eq!(
            1,
            generalization.points.len(),
            "the peak's disagreement recurs in the join and stands one point"
        );
        assert_eq!(
            (one, two),
            (
                rebuilt(&generalization, Member(0)),
                rebuilt(&generalization, Member(1))
            ),
            "every component of each member is rebuilt"
        );
    }

    #[test]
    fn a_family_without_a_generalization_is_refused_by_name()
    {
        let positive = cut(numeral(Successors(0)), ConsPat::top());
        let negative = CmdPat::cut(Polarity::Negative, numeral(Successors(0)), ConsPat::top());
        assert_eq!(
            Maybe::Absent(anti_unification::Absent::EmptyFamily),
            anti_unify_cmd(&[]),
            "a family with no member"
        );
        let lone = core::slice::from_ref(&positive);
        assert_eq!(
            Maybe::Absent(anti_unification::Absent::RaggedFamily),
            anti_unify_cmd(&[lone, &[positive.clone(), positive.clone()]]),
            "members of two lengths"
        );
        assert_eq!(
            Maybe::Absent(anti_unification::Absent::Ungeneralizable),
            anti_unify_cmd(&[lone, &[negative]]),
            "two polarities, where no command metavariable can stand"
        );
        let Maybe::Present(single) = SequentAlphabet::anti_unify_cmd(&[lone])
        else {
            panic!("one member generalizes to itself");
        };
        assert_eq!(
            (lone.to_vec(), 0),
            (single.patterns, single.points.len()),
            "a lone member is its own generalization, with no point"
        );
    }
}
