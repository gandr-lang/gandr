//! The reduction order completion orients critical pairs by: a size
//! comparison guarded by hole occurrence, with a lexicographic path order
//! deciding the ties.
//!
//! Completion turns a divergent critical pair into a derived cell by putting
//! the larger side on the left, and reads [`Ordering::Equal`] as an honest
//! obstruction rather than a guessed orientation. What counts as larger is
//! this module's whole subject.
//!
//! # Why size alone leaves an obstruction, and why it also needs a guard
//!
//! A node-count order cannot orient a pair whose two sides have the same
//! size, which is the common shape at a cut: both faces of a rule are one cut
//! with a producer half and a consumer half, so moving where the work sits
//! moves nodes around without adding any.
//!
//! Size is also not, by itself, stable under substitution, and a reduction
//! order must be: if `l ≻ r` then `lσ ≻ rσ` for every `σ`, or orienting
//! `l → r` proves nothing about the instances that actually rewrite. A side
//! that is smaller today grows faster under substitution when it repeats a
//! hole the other side does not — `f(x, a, a)` outsizes `g(x, x)` until `x` is
//! instantiated by anything of size three. So the size comparison is admitted
//! only when the larger side dominates the smaller one hole by hole, which is
//! exactly the condition under which substitution cannot reverse it. Cell
//! patterns are linear on the left but not on the right, so the shape this
//! guard excludes is reachable from a written rule.
//!
//! # The path order that decides the ties
//!
//! The tie-break is the lexicographic path order over the uniform node view of
//! the pattern grammar, taken with respect to a total, well-founded precedence
//! on head symbols. It is a simplification order, hence stable under
//! substitution, monotone under contexts, and well-founded.
//!
//! The precedence is `cut > K⁻ > f > K > ★`, and its middle is chosen rather
//! than arbitrary. Ranking a return-side constructor frame above an operation
//! frame orients the worked fusion cell in the direction it is written:
//!
//! ```text
//! ⟨v | Succ⁻(add(n; α))⟩  ~>  ⟨v | add(n; Succ⁻(α))⟩
//! ```
//!
//! That is deforestation — the intermediate `Succ` allocation is gone — and it
//! is a same-size pair, so the size comparison alone leaves it unoriented.
//! Under the ranking above the `K⁻`-headed side is the larger, so the derived
//! cell pushes the constructor frame inward; the opposite ranking orients it
//! backwards.
//!
//! The remaining tiers are ordinary: a cut is the frame every other head sits
//! inside, and a constructor is the value form nothing rewrites away. Within
//! one head kind the precedence is the symbol's own order, then the arity; a
//! cut orders by polarity. Those are arbitrary but total and deterministic,
//! which is all a path order asks of a precedence, and determinism keeps
//! orientations reproducible.
//!
//! # What this order does not orient
//!
//! A simplification order cannot orient a rule whose right-hand side buries
//! the left's hole under new structure. The frame-defining cell
//! ([`crate::sequent::frame_defining_cell`]) is exactly that shape —
//! `⟨v | K⁻(β)⟩ ~> ⟨K(v) | β⟩` puts `v` under `K` — so no precedence orients
//! it in the shipped direction. That costs nothing here: a polarity-derived
//! cell's orientation is fixed by the calculus and never passes through this
//! order, which orients critical pairs and nothing else. It does mean this
//! order alone is not a termination proof for a store holding
//! polarity-derived cells, and it is not offered as one.
//!
//! # Implementation shape
//!
//! Both commands are laid out in one node table each, every node's children at
//! strictly smaller indices and the root last. The layout reads the producer
//! tables in place and gives each consumer spine its end first and its
//! outermost frame last. The relation is then filled by two nested loops over
//! `(left index, right index)` in increasing order, because the path order at
//! one pair reads only pairs with a smaller left index, a smaller right index,
//! or both. Nothing recurses.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::cmp::Ordering;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::pattern::CmdPat;
use crate::pattern::MetaVar;
use crate::pattern::ProdHead;
use crate::pattern::ProdRef;
use crate::pattern::SpineEnd;
use crate::pattern::SpineFrame;
use crate::pattern::Sym;
use crate::polarity::Polarity;

/// The reduction order: the orientation completion reads.
///
/// # Specification
/// - ensures: [`Ordering::Greater`] or [`Ordering::Less`] only for a pair the
///   order can orient stably — the named side is larger by node count and
///   carries every hole of the other at least as often, or the two are equal by
///   node count with equal hole counts and separated by the lexicographic path
///   order. [`Ordering::Equal`] everywhere else, which completion reads as an
///   honest obstruction.
/// - provides: a well-founded, substitution-stable, context-monotone
///   orientation of critical pairs.
/// - panics: none.
/// - intension: the path order is consulted only on a size tie, so every
///   orientation the size comparison decides is left to it.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are separated pointwise: a
///   size-decided pair with hole domination, an equal-size pair the path order
///   orients, and the two obstruction routes (a size difference the hole counts
///   do not license, an equal-size pair the path order cannot separate). L2 —
///   over generated pairs the relation is irreflexive and antisymmetric, and a
///   strict verdict survives a uniform instantiation.
/// - witness: `order::tests::a_size_difference_orients_when_the_larger_side_dominates`
/// - witness: `order::tests::a_size_difference_that_substitution_could_reverse_is_an_obstruction`
/// - witness: `order::tests::an_equal_size_pair_is_oriented_by_the_path_order`
/// - witness: `order::tests::an_equal_size_pair_the_path_order_cannot_separate_stays_an_obstruction`
/// - witness: `order::tests::the_frame_defining_shape_is_not_oriented_forwards_and_that_is_stated`
/// - witness: `tests::order::the_order_is_a_strict_order_over_generated_patterns`
/// - witness: `tests::order::the_path_order_survives_a_uniform_hole_instantiation`
#[inline]
#[must_use]
#[spec(ensures: |output| (lhs != rhs || output == Ordering::Equal) && match output {
    Ordering::Greater => lhs.size() >= rhs.size() && dominates(&hole_counts(lhs), &hole_counts(rhs)).0,
    Ordering::Less => rhs.size() >= lhs.size() && dominates(&hole_counts(rhs), &hole_counts(lhs)).0,
    Ordering::Equal => true,
})]
pub fn reduction_cmp(
    lhs: &CmdPat,
    rhs: &CmdPat,
) -> Ordering
{
    let left_holes = hole_counts(lhs);
    let right_holes = hole_counts(rhs);
    match lhs.size().cmp(&rhs.size()) {
        | Ordering::Greater if dominates(&left_holes, &right_holes).0 => Ordering::Greater,
        | Ordering::Less if dominates(&right_holes, &left_holes).0 => Ordering::Less,
        | Ordering::Equal if left_holes == right_holes => path_order_cmp(lhs, rhs),
        | Ordering::Greater | Ordering::Less | Ordering::Equal => Ordering::Equal,
    }
}

/// The lexicographic path order on two command patterns.
///
/// # Specification
/// - ensures: [`Ordering::Greater`] when the left strictly exceeds the right in
///   the path order, [`Ordering::Less`] in the mirror case, and
///   [`Ordering::Equal`] when neither does — syntactic equality and genuine
///   incomparability alike, which completion treats the same way.
/// - provides: a simplification order, so stable under substitution, monotone
///   under contexts, and well-founded.
/// - panics: none.
/// - intension: time and space are the product of the two node counts;
///   `economy:` each relation table keeps every row, where a fill could release
///   a row once no pending parent reads it.
///
/// # Adequacy
/// - hypothesis: L3 — the fusion pair is separated both ways, and the
///   deep-pattern witness compares a pattern many thousands of nodes deep
///   against a small one, both ways, on a small stack.
/// - witness: `order::tests::an_equal_size_pair_is_oriented_by_the_path_order`
/// - witness: `tests::depth::a_deep_pattern_is_matched_ordered_and_dropped_on_a_small_stack`
#[inline]
#[must_use]
#[spec(ensures: |output| (lhs != rhs || output == Ordering::Equal) && match output {
    Ordering::Greater => rhs.metavars().all(|var| lhs.metavars().any(|held| held == var)),
    Ordering::Less => lhs.metavars().all(|var| rhs.metavars().any(|held| held == var)),
    Ordering::Equal => true,
})]
pub fn path_order_cmp(
    lhs: &CmdPat,
    rhs: &CmdPat,
) -> Ordering
{
    let left = FlatTerm::lay_out(lhs);
    let right = FlatTerm::lay_out(rhs);
    if strictly_greater(&left, &right).0 {
        return Ordering::Greater;
    }
    if strictly_greater(&right, &left).0 {
        return Ordering::Less;
    }
    Ordering::Equal
}

/// An occurrence count for one metavariable.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct HoleOccurrences(usize);

/// How many times each metavariable occurs in a pattern.
///
/// Occurrence is counted per [`MetaVar`] — the `(name, category)` pair a
/// substitution binds — rather than per hole name, because a name worn at two
/// polarities is two independent substitution targets.
///
/// # Specification
/// - ensures: one entry per distinct metavariable, mapped to its occurrence
///   count.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, repeated and cross-category occurrences have exact
///   keyed multiplicities. Dropped repeats, category conflation and extra keys
///   change the counts and orientation guard.
/// - witness: `order::tests::hole_domination_counts_occurrences_and_categories`
#[spec(ensures: |output| output.values().fold(0_usize, |sum, count| sum.saturating_add(count.0)) == cmd.metavars().count()
    && output.iter().all(|(var, count)| count.0 > 0 && count.0 == cmd.metavars().filter(|held| held == var).count()))]
fn hole_counts(cmd: &CmdPat) -> BTreeMap<&MetaVar, HoleOccurrences>
{
    let mut counts: BTreeMap<&MetaVar, HoleOccurrences> = BTreeMap::new();
    for var in cmd.metavars() {
        let entry = counts.entry(var).or_default();
        entry.0 = entry.0.saturating_add(1);
    }
    counts
}

/// Whether one side carries every hole of the other at least as often — the
/// condition that makes a node-count comparison survive substitution.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct HoleDomination(bool);

/// Whether `larger` carries every metavariable of `smaller` at least as
/// often.
///
/// Instantiating a metavariable adds its image's size once per occurrence, so
/// a side that never repeats a hole less often than the other cannot be
/// overtaken.
///
/// # Specification
/// - ensures: positive exactly when every entry of `smaller` has an entry in
///   `larger` with a count at least as high.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — absent, lower, equal and higher per-hole counts separate
///   domination from obstruction. Vacuous empty maps are included;
///   strict-versus-nonstrict bounds and missing-key defaults change the
///   verdict.
/// - witness: `order::tests::hole_domination_counts_occurrences_and_categories`
#[spec(ensures: |output| output.0 == smaller.iter().all(|(var, count)| larger.get(var).is_some_and(|held| held >= count)))]
fn dominates(
    larger: &BTreeMap<&MetaVar, HoleOccurrences>,
    smaller: &BTreeMap<&MetaVar, HoleOccurrences>,
) -> HoleDomination
{
    HoleDomination(
        smaller
            .iter()
            .all(|(var, count)| larger.get(var).is_some_and(|held| held >= count)),
    )
}

/// A verdict of the path order's strict relation, or of syntactic equality,
/// at one pair of nodes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct PathVerdict(bool);

/// A dense index into a [`FlatTerm`]'s node table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct FlatIndex(usize);

/// The rank of a head symbol's kind in the precedence.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct HeadRank(u8);

/// A node's number of immediate children.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ChildCount(usize);

/// The head of a laid-out node: a function symbol, or a metavariable.
///
/// A path order treats the two differently: a metavariable exceeds nothing,
/// and is exceeded only by a term that properly contains it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Head<'term>
{
    /// A cut `⟨p |ε c⟩`, carrying its polarity.
    Cut(Polarity),
    /// An operation frame `f(p̄; c)`.
    Op(&'term Sym),
    /// A return-side constructor frame `K⁻(c)`.
    Frame(&'term Sym),
    /// A constructor application `K(p̄)`.
    Ctor(&'term Sym),
    /// The terminal consumer `★`.
    Top,
    /// A metavariable leaf.
    Var(&'term MetaVar),
}

/// One node of a [`FlatTerm`].
#[derive(Clone, Copy, Debug)]
struct FlatNode<'term>
{
    /// The node's head.
    head: Head<'term>,
    /// Where the node's children begin in [`FlatTerm::children`].
    first_child: FlatIndex,
    /// How many children the node has.
    child_count: ChildCount,
}

/// A command laid out in one node table: every node's children at strictly
/// smaller indices, the root last.
#[derive(Debug, Default)]
struct FlatTerm<'term>
{
    /// The nodes.
    nodes: Vec<FlatNode<'term>>,
    /// Every node's children, left to right, each node's run contiguous.
    children: Vec<FlatIndex>,
}

impl<'term> FlatTerm<'term>
{
    /// Lays a command out in one node table.
    ///
    /// # Specification
    /// - ensures: every node appears after all of its children; the last node
    ///   is the cut. The children of each node are in the uniform node view's
    ///   left-to-right order.
    /// - panics: none.
    /// - intension: one pass over the consumer spine and one over each producer
    ///   table, never recursion; the producer tables are read in their own
    ///   index order, which already puts children first.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — leaf and nested cuts exercise producer, operation and
    ///   continuation children through equal and strict path comparisons.
    ///   Child-order loss, missing nodes and forward edges change the relation;
    ///   boundary table probes cover empty ranges.
    /// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
    #[spec(ensures: |output| output.nodes.len() == usize::from(cmd.size())
        && output.nodes.last().is_some_and(|node| node.head == Head::Cut(cmd.polarity()))
        && output.nodes.iter().enumerate().all(|(index, node)| output.children_of(node).len() == node.child_count.0
            && output.children_of(node).iter().all(|child| child.0 < index)))]
    fn lay_out(cmd: &'term CmdPat) -> Self
    {
        let mut term = Self::default();
        let cons = cmd.consumer().to_ref();
        let mut ret = term.push(
            match *cons.end() {
                | SpineEnd::Top => Head::Top,
                | SpineEnd::Meta(ref var) => Head::Var(var),
            },
            &[],
        );
        for frame in cons.frames() {
            ret = match *frame {
                | SpineFrame::Op { ref op, ref args } => {
                    let mut roots: Vec<FlatIndex> =
                        Vec::with_capacity(args.len().saturating_add(1));
                    for arg in args {
                        roots.push(term.push_prod(arg.to_ref()));
                    }
                    roots.push(ret);
                    term.push(Head::Op(op), &roots)
                },
                | SpineFrame::Frame(ref ctor) => term.push(Head::Frame(ctor), &[ret]),
            };
        }
        let prod = term.push_prod(cmd.producer().to_ref());
        term.push(Head::Cut(cmd.polarity()), &[prod, ret]);
        term
    }

    /// Lays one producer table out and returns its root's index.
    ///
    /// # Specification
    /// - ensures: the table's nodes appended in table order, each constructor's
    ///   children being the most recently completed subtrees, its first child
    ///   the most recent; the index of the table's root.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nullary and multi-argument producers appear below
    ///   distinct heads in both comparison directions. Exact strict and equal
    ///   observations reject a wrong root or reordered arguments.
    /// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
    #[spec(captures: before = self.nodes.len(), ensures: |output|
        self.nodes.len() == before.saturating_add(usize::from(prod.size())) && output.0.saturating_add(1) == self.nodes.len())]
    fn push_prod(
        &mut self,
        prod: ProdRef<'term>,
    ) -> FlatIndex
    {
        // The roots of the completed subtrees not yet claimed by a parent, the
        // most recent last.
        let mut completed: Vec<FlatIndex> = Vec::new();
        let mut children: Vec<FlatIndex> = Vec::new();
        let mut root = FlatIndex(self.nodes.len());
        for entry in prod.entries() {
            let head = match *entry.head() {
                | ProdHead::Meta(ref var) => Head::Var(var),
                | ProdHead::Ctor(ref ctor, _) => Head::Ctor(ctor),
            };
            let first = completed
                .len()
                .saturating_sub(usize::from(entry.head().arity()));
            children.clear();
            children.extend(completed.drain(first ..).rev());
            root = self.push(head, &children);
            completed.push(root);
        }
        root
    }

    /// Appends one node over already-appended children.
    ///
    /// # Specification
    /// - requires: every index of `children` is already appended.
    /// - ensures: the new node's index.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — heads over zero, one and multiple existing children
    ///   are compared through the resulting terms. Wrong arity, head or child
    ///   order changes equality or strict order.
    /// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
    #[spec(requires: children.iter().all(|child| child.0 < self.nodes.len()),
        captures: before = self.nodes.len(), ensures: |output| output.0 == before && self.nodes.len() == before.saturating_add(1)
            && self.nodes.get(output.0).is_some_and(|node| node.head == head && self.children_of(node) == children))]
    fn push(
        &mut self,
        head: Head<'term>,
        children: &[FlatIndex],
    ) -> FlatIndex
    {
        let index = FlatIndex(self.nodes.len());
        self.nodes.push(FlatNode {
            head,
            first_child: FlatIndex(self.children.len()),
            child_count: ChildCount(children.len()),
        });
        self.children.extend_from_slice(children);
        index
    }

    /// The children of `node`, left to right.
    ///
    /// # Specification
    /// - ensures: the run [`FlatTerm::push`] recorded for the node; an empty
    ///   run for a node this table did not lay out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero and multiple children and a range beyond the
    ///   child table return exact runs. Wrong offsets, dropped children and a
    ///   weakened range bound change the observation.
    /// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
    #[spec(ensures: |output| if node.first_child.0.saturating_add(node.child_count.0) <= self.children.len() {
        output.len() == node.child_count.0
    } else { output.is_empty() })]
    fn children_of(
        &self,
        node: &FlatNode<'term>,
    ) -> &[FlatIndex]
    {
        let end = node.first_child.0.saturating_add(node.child_count.0);
        self.children.get(node.first_child.0 .. end).unwrap_or(&[])
    }
}

/// The precedence rank of a head's kind; a metavariable takes none.
///
/// # Specification
/// - ensures: cuts above constructor frames above operation frames above
///   constructors above `★`; [`precedence::Absent::Metavariable`] for a
///   metavariable. The frame-above-operation tier is what orients the worked
///   fusion cell forwards.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — all five function-head tiers and unranked metavariables
///   have exact comparisons both ways. Reversed tiers or ranking a variable
///   changes the precedence.
/// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
#[spec(ensures: |output| match (head, output) {
    (Head::Var(_), Maybe::Absent(precedence::Absent::Metavariable)) => true,
    (Head::Cut(_), Maybe::Present(rank)) => rank.0 == 4,
    (Head::Frame(_), Maybe::Present(rank)) => rank.0 == 3,
    (Head::Op(_), Maybe::Present(rank)) => rank.0 == 2,
    (Head::Ctor(_), Maybe::Present(rank)) => rank.0 == 1,
    (Head::Top, Maybe::Present(rank)) => rank.0 == 0,
    _ => false,
})]
fn head_rank(head: Head<'_>) -> Maybe<HeadRank, precedence::Absent>
{
    Maybe::Present(match head {
        | Head::Cut(_) => HeadRank(4),
        | Head::Frame(_) => HeadRank(3),
        | Head::Op(_) => HeadRank(2),
        | Head::Ctor(_) => HeadRank(1),
        | Head::Top => HeadRank(0),
        | Head::Var(_) => {
            return Maybe::Absent(precedence::Absent::Metavariable);
        },
    })
}

quenchant_shape::reason_enum! {
    /// Why a head takes no place in the precedence.
    mod precedence {
        /// The reason the head is unranked.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A metavariable is not a function symbol.
            Metavariable,
        }
    }
}

/// The polarity's rank inside the cut kind: arbitrary, total, deterministic.
///
/// # Specification
/// trivial.
const fn polarity_rank(polarity: Polarity) -> HeadRank
{
    match polarity {
        | Polarity::Positive => HeadRank(0),
        | Polarity::Negative => HeadRank(1),
    }
}

/// The precedence comparison of two heads at their arities.
///
/// # Specification
/// - ensures: kind rank first, then the kind's own payload (a symbol's order, a
///   cut's polarity rank), then the arity: a total order on function symbols.
/// - provides: [`precedence::Absent::Metavariable`] when either head is a
///   metavariable.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — kind, symbol, polarity and arity ties are varied
///   separately, with variables on either side. Exact comparisons reject
///   reversed precedence, skipped tie-breaks and ranked variables.
/// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
#[spec(ensures: |output| match output {
    Maybe::Absent(_) => matches!(left, Head::Var(_)) || matches!(right, Head::Var(_)),
    Maybe::Present(order) => !matches!(left, Head::Var(_)) && !matches!(right, Head::Var(_))
        && (left != right || order == left_arity.cmp(&right_arity)),
})]
fn precedence_cmp(
    left: Head<'_>,
    left_arity: ChildCount,
    right: Head<'_>,
    right_arity: ChildCount,
) -> Maybe<Ordering, precedence::Absent>
{
    let (Maybe::Present(left_rank), Maybe::Present(right_rank)) =
        (head_rank(left), head_rank(right))
    else {
        return Maybe::Absent(precedence::Absent::Metavariable);
    };
    let by_payload = match (left, right) {
        | (Head::Cut(left_polarity), Head::Cut(right_polarity)) => {
            polarity_rank(left_polarity).cmp(&polarity_rank(right_polarity))
        },
        | (Head::Op(left_sym), Head::Op(right_sym))
        | (Head::Frame(left_sym), Head::Frame(right_sym))
        | (Head::Ctor(left_sym), Head::Ctor(right_sym)) => left_sym.cmp(right_sym),
        | (
            Head::Cut(_) | Head::Op(_) | Head::Frame(_) | Head::Ctor(_) | Head::Top | Head::Var(_),
            _,
        ) => Ordering::Equal,
    };
    Maybe::Present(
        left_rank
            .cmp(&right_rank)
            .then(by_payload)
            .then(left_arity.cmp(&right_arity)),
    )
}

/// Whether `left`'s root strictly exceeds `right`'s root in the path order.
///
/// The relation is filled by two nested loops over `(left index, right index)`
/// in increasing order. That is sound because the path order at one pair
/// reads only pairs with a strictly smaller left index (the subterm case), a
/// strictly smaller right index (the "greater than every argument" side
/// condition), or both (the lexicographic comparison of arguments), and every
/// child's index is strictly smaller than its parent's.
///
/// # Specification
/// - ensures: positive exactly when the two roots stand in the strict
///   lexicographic path order induced by [`precedence_cmp`].
/// - panics: none.
/// - intension: no recursion; time is the product of the two node counts times
///   the arity.
///
/// # Adequacy
/// - hypothesis: L3 — identical, proper-subterm, precedence-separated and
///   lexicographically separated terms are compared both ways; empty tables are
///   negative. False reflexivity, ignored side conditions and reversed argument
///   order change the relation.
/// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
#[spec(ensures: |output| !output.0 || (!left.nodes.is_empty() && !right.nodes.is_empty()
    && left.nodes.last().is_some_and(|node| !matches!(node.head, Head::Var(_)))
    && (left.nodes.len() != right.nodes.len() || left.children != right.children
        || left.nodes.iter().zip(&right.nodes).any(|(l, r)| l.head != r.head || l.first_child != r.first_child || l.child_count != r.child_count))))]
fn strictly_greater(
    left: &FlatTerm<'_>,
    right: &FlatTerm<'_>,
) -> PathVerdict
{
    let right_count = right.nodes.len();
    let mut equal = RelationTable::default();
    let mut greater = RelationTable::default();
    for left_node in &left.nodes {
        let left_children = left.children_of(left_node);
        let mut equal_row: Vec<PathVerdict> = Vec::with_capacity(right_count);
        let mut greater_row: Vec<PathVerdict> = Vec::with_capacity(right_count);
        for right_node in &right.nodes {
            let right_children = right.children_of(right_node);
            let same = left_node.head == right_node.head
                && left_children.len() == right_children.len()
                && left_children
                    .iter()
                    .zip(right_children)
                    .all(|(&child, &other)| equal.at(child, other).0);
            equal_row.push(PathVerdict(same));
            let pair = NodePair {
                left: left_node,
                left_children,
                right: right_node,
                right_children,
            };
            greater_row.push(exceeds(pair, &equal, &greater, &greater_row));
        }
        equal.rows.push(equal_row);
        greater.rows.push(greater_row);
    }
    greater.roots()
}

/// One pair of nodes being compared, with their children.
#[derive(Clone, Copy, Debug)]
struct NodePair<'pair, 'term>
{
    /// The left node.
    left: &'pair FlatNode<'term>,
    /// The left node's children.
    left_children: &'pair [FlatIndex],
    /// The right node.
    right: &'pair FlatNode<'term>,
    /// The right node's children.
    right_children: &'pair [FlatIndex],
}

/// A filled half of the path-order relation over one pair of laid-out
/// terms: `rows[left index][right index]`.
#[repr(transparent)]
#[derive(Debug, Default)]
struct RelationTable
{
    /// One row per left node, each holding one answer per right node.
    rows: Vec<Vec<PathVerdict>>,
}

impl RelationTable
{
    /// The answer at `(left, right)`, negative outside the filled region.
    ///
    /// # Specification
    /// - ensures: the recorded answer when both indices are inside the filled
    ///   region, and a negative answer otherwise — a default an increasing fill
    ///   never reaches.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, ragged and filled relations expose recorded
    ///   true and false entries and negative out-of-range answers. Shifted
    ///   indices and a positive missing-cell default change the result.
    /// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
    #[spec(ensures: |output| output.0 == self.rows.get(left.0).and_then(|row| row.get(right.0))
        .is_some_and(|answer| answer.0))]
    fn at(
        &self,
        left: FlatIndex,
        right: FlatIndex,
    ) -> PathVerdict
    {
        self.rows
            .get(left.0)
            .and_then(|row| row.get(right.0))
            .copied()
            .unwrap_or_default()
    }

    /// The last entry of the last row: the two roots' answer once the fill is
    /// complete.
    ///
    /// # Specification
    /// - ensures: the root pair's answer for a filled table, and a negative
    ///   answer for an empty one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty rows and filled relations whose last entry is
    ///   true or false expose opposite root answers. Using a first entry or a
    ///   positive empty default changes the result.
    /// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
    #[spec(ensures: |output| output.0 == self.rows.last().is_some_and(|row| row.last().is_some_and(|answer| answer.0)))]
    fn roots(&self) -> PathVerdict
    {
        self.rows
            .last()
            .and_then(|row| row.last())
            .copied()
            .unwrap_or_default()
    }
}

/// Whether the left node exceeds the right node, reading the filled rows.
///
/// `current_row` holds the greater-than answers for the left node against
/// every right node already visited in this row, which is exactly the set the
/// "and it exceeds each of the right's arguments" side condition reads.
///
/// # Specification
/// - requires: `equal` and `greater` hold every row with a strictly smaller
///   left index, and `current_row` every column with a strictly smaller right
///   index.
/// - ensures: the strict path-order answer for this pair.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid filled relation prefixes compare function heads,
///   variable heads and a larger child against the other root. Exact path
///   comparisons reject ranked variables, a lost subterm case and skipped
///   argument domination.
/// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
#[spec(
    requires: pair.left_children.iter().all(|child| equal.rows.get(child.0).is_some_and(|row| current_row.len() < row.len())
        && greater.rows.get(child.0).is_some_and(|row| current_row.len() < row.len()))
        && pair.right_children.iter().all(|child| child.0 < current_row.len()),
    ensures: |output| !matches!(pair.left.head, Head::Var(_)) || !output.0,
)]
fn exceeds(
    pair: NodePair<'_, '_>,
    equal: &RelationTable,
    greater: &RelationTable,
    current_row: &[PathVerdict],
) -> PathVerdict
{
    // A metavariable exceeds nothing.
    if matches!(pair.left.head, Head::Var(_)) {
        return PathVerdict(false);
    }
    let right_index = FlatIndex(current_row.len());
    // The subterm case: some argument of the left already reaches the right.
    let subterm = pair
        .left_children
        .iter()
        .any(|&child| greater.at(child, right_index).0 || equal.at(child, right_index).0);
    if subterm {
        return PathVerdict(true);
    }
    // Both remaining cases need the left to exceed every argument of the
    // right.
    let over_arguments = pair
        .right_children
        .iter()
        .all(|&arg| current_row.get(arg.0).copied().unwrap_or_default().0);
    if !over_arguments {
        return PathVerdict(false);
    }
    let precedence = precedence_cmp(
        pair.left.head,
        pair.left.child_count,
        pair.right.head,
        pair.right.child_count,
    );
    match precedence {
        | Maybe::Present(Ordering::Greater) => PathVerdict(true),
        | Maybe::Present(Ordering::Equal) => {
            lexicographically_greater(pair.left_children, pair.right_children, equal, greater)
        },
        | Maybe::Present(Ordering::Less) | Maybe::Absent(_) => PathVerdict(false),
    }
}

/// Whether the left argument list exceeds the right one lexicographically.
///
/// # Specification
/// - requires: `equal` and `greater` hold every row the two lists index.
/// - ensures: positive when the first position at which the two are not equal
///   has the left argument strictly greater; negative when the lists agree
///   throughout or the first difference goes the other way.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — filled relations compare equal argument lists and first
///   differences in either direction. Prefix equality is negative; skipping the
///   first difference or choosing the wrong column changes the answer.
/// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
#[spec(
    requires: left.iter().zip(right).all(|(left, right)| equal.rows.get(left.0).is_some_and(|row| right.0 < row.len())
        && greater.rows.get(left.0).is_some_and(|row| right.0 < row.len())),
    ensures: |output| left.iter().zip(right).find(|&(left, right)| !equal.at(*left, *right).0)
        .map_or(!output.0, |(left, right)| output == greater.at(*left, *right)),
)]
fn lexicographically_greater(
    left: &[FlatIndex],
    right: &[FlatIndex],
    equal: &RelationTable,
    greater: &RelationTable,
) -> PathVerdict
{
    for (&left_arg, &right_arg) in left.iter().zip(right) {
        if equal.at(left_arg, right_arg).0 {
            continue;
        }
        return greater.at(left_arg, right_arg);
    }
    PathVerdict(false)
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::pattern::ConsPat;
    use crate::pattern::ProdPat;

    #[test]
    fn hole_domination_counts_occurrences_and_categories()
    {
        let producer = MetaVar::producer("x");
        let consumer = MetaVar::consumer("x");
        let missing = MetaVar::producer("absent");
        let term = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("x")]),
            ConsPat::meta("x"),
        );
        let counts = hole_counts(&term);
        assert_eq!(
            BTreeMap::from([
                (&producer, HoleOccurrences(2)),
                (&consumer, HoleOccurrences(1))
            ]),
            counts
        );
        let ground = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        assert!(hole_counts(&ground).is_empty());
        assert!(dominates(&counts, &BTreeMap::new()).0);
        assert!(dominates(&counts, &counts).0);
        for (key, amount, expected) in [
            (&producer, 1, true),
            (&producer, 2, true),
            (&producer, 3, false),
            (&consumer, 1, true),
            (&consumer, 2, false),
            (&missing, 1, false),
        ] {
            assert_eq!(
                expected,
                dominates(&counts, &BTreeMap::from([(key, HoleOccurrences(amount))])).0
            );
        }
        assert!(!dominates(&BTreeMap::new(), &counts).0);
    }

    #[test]
    fn precedence_and_relation_boundaries_preserve_strictness()
    {
        let a = Sym::new("A");
        let z = Sym::new("Z");
        let variable = MetaVar::producer("x");
        let ranked = [
            Head::Top,
            Head::Ctor(&a),
            Head::Op(&a),
            Head::Frame(&a),
            Head::Cut(Polarity::Positive),
        ];
        for (left_index, &left) in ranked.iter().enumerate() {
            for (right_index, &right) in ranked.iter().enumerate() {
                assert_eq!(
                    Maybe::Present(left_index.cmp(&right_index)),
                    precedence_cmp(left, ChildCount(2), right, ChildCount(2))
                );
            }
            assert_eq!(
                Maybe::Absent(precedence::Absent::Metavariable),
                precedence_cmp(left, ChildCount(0), Head::Var(&variable), ChildCount(0))
            );
            assert_eq!(
                Maybe::Absent(precedence::Absent::Metavariable),
                precedence_cmp(Head::Var(&variable), ChildCount(0), left, ChildCount(0))
            );
            assert_eq!(
                Maybe::Present(Ordering::Less),
                precedence_cmp(left, ChildCount(0), left, ChildCount(1))
            );
            assert_eq!(
                Maybe::Present(Ordering::Greater),
                precedence_cmp(left, ChildCount(2), left, ChildCount(1))
            );
        }
        for (left, right) in [
            (Head::Ctor(&a), Head::Ctor(&z)),
            (Head::Op(&a), Head::Op(&z)),
            (Head::Frame(&a), Head::Frame(&z)),
            (Head::Cut(Polarity::Positive), Head::Cut(Polarity::Negative)),
        ] {
            assert_eq!(
                Maybe::Present(Ordering::Less),
                precedence_cmp(left, ChildCount(9), right, ChildCount(0))
            );
            assert_eq!(
                Maybe::Present(Ordering::Greater),
                precedence_cmp(right, ChildCount(0), left, ChildCount(9))
            );
        }
        let term = |prod| CmdPat::cut(Polarity::Positive, prod, ConsPat::top());
        let low = ProdPat::ctor("A", []);
        let high = ProdPat::ctor("Z", []);
        for (smaller, larger) in [
            (low.clone(), high.clone()),
            (low.clone(), ProdPat::ctor("A", [low.clone()])),
            (
                ProdPat::ctor("Pair", [low.clone(), high.clone()]),
                ProdPat::ctor("Pair", [high.clone(), low.clone()]),
            ),
            (
                ProdPat::ctor("Pair", [low.clone(), low.clone()]),
                ProdPat::ctor("Pair", [low.clone(), high]),
            ),
        ] {
            let smaller = term(smaller);
            let larger = term(larger);
            assert_eq!(Ordering::Less, path_order_cmp(&smaller, &larger));
            assert_eq!(Ordering::Greater, path_order_cmp(&larger, &smaller));
            assert_eq!(Ordering::Equal, path_order_cmp(&larger, &larger));
        }
        let laid_out_term = term(ProdPat::ctor("Pair", [low.clone(), ProdPat::meta("x")]));
        let layout = FlatTerm::lay_out(&laid_out_term);
        let invalid = FlatNode {
            head: Head::Top,
            first_child: FlatIndex(usize::MAX),
            child_count: ChildCount(1),
        };
        assert!(layout.children_of(&invalid).is_empty());
        assert!(!strictly_greater(&FlatTerm::default(), &layout).0);
        assert!(!strictly_greater(&layout, &FlatTerm::default()).0);
        let variable_term = term(ProdPat::meta("x"));
        let ground_term = term(low);
        assert_eq!(
            Ordering::Equal,
            path_order_cmp(&variable_term, &ground_term)
        );
        assert_eq!(
            Ordering::Equal,
            path_order_cmp(&ground_term, &variable_term)
        );
        let empty = RelationTable::default();
        assert!(!empty.roots().0);
        assert!(!empty.at(FlatIndex(0), FlatIndex(0)).0);
        let table = RelationTable {
            rows: alloc::vec![
                alloc::vec![PathVerdict(false), PathVerdict(true)],
                alloc::vec![],
                alloc::vec![PathVerdict(true), PathVerdict(false)]
            ],
        };
        for (left, right, expected) in [
            (0, 0, false),
            (0, 1, true),
            (1, 0, false),
            (2, 0, true),
            (2, 1, false),
            (2, 2, false),
            (3, 0, false),
            (usize::MAX, usize::MAX, false),
        ] {
            assert_eq!(expected, table.at(FlatIndex(left), FlatIndex(right)).0);
        }
        assert!(!table.roots().0);
        assert!(
            !RelationTable {
                rows: alloc::vec![alloc::vec![]]
            }
            .roots()
            .0
        );
        assert!(
            RelationTable {
                rows: alloc::vec![alloc::vec![PathVerdict(false), PathVerdict(true)]]
            }
            .roots()
            .0
        );
        let equal = RelationTable {
            rows: alloc::vec![
                alloc::vec![PathVerdict(true), PathVerdict(false)],
                alloc::vec![PathVerdict(false), PathVerdict(true)]
            ],
        };
        let greater = RelationTable {
            rows: alloc::vec![
                alloc::vec![PathVerdict(false), PathVerdict(false)],
                alloc::vec![PathVerdict(true), PathVerdict(false)]
            ],
        };
        for (left, right, expected) in [
            (alloc::vec![], alloc::vec![], false),
            (alloc::vec![FlatIndex(1)], alloc::vec![FlatIndex(1)], false),
            (alloc::vec![FlatIndex(1)], alloc::vec![FlatIndex(0)], true),
            (
                alloc::vec![FlatIndex(0), FlatIndex(1)],
                alloc::vec![FlatIndex(1), FlatIndex(0)],
                false,
            ),
            (
                alloc::vec![FlatIndex(0), FlatIndex(1)],
                alloc::vec![FlatIndex(0), FlatIndex(0)],
                true,
            ),
            (
                alloc::vec![FlatIndex(0)],
                alloc::vec![FlatIndex(0), FlatIndex(1)],
                false,
            ),
        ] {
            assert_eq!(
                expected,
                lexicographically_greater(&left, &right, &equal, &greater).0
            );
        }
    }

    /// The worked fusion cell, left face: the intermediate `Succ` allocation
    /// is still there.
    ///
    /// # Specification
    /// trivial.
    fn fusion_before() -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("v"),
            ConsPat::frame(
                "Succ",
                ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("a")),
            ),
        )
    }

    /// The worked fusion cell, right face: the constructor frame has been
    /// pushed inside the operation frame and the allocation is gone.
    ///
    /// # Specification
    /// trivial.
    fn fusion_after() -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("v"),
            ConsPat::op(
                "add",
                [ProdPat::meta("n")],
                ConsPat::frame("Succ", ConsPat::meta("a")),
            ),
        )
    }

    #[test]
    fn an_equal_size_pair_is_oriented_by_the_path_order()
    {
        // The fusion cell's two faces have the same node count because fusing
        // moves a frame rather than removing one, so the size comparison
        // alone leaves an obstruction.
        let (before, after) = (fusion_before(), fusion_after());
        assert_eq!(
            before.size(),
            after.size(),
            "the hypothesis: the fusion cell's two faces are the same size"
        );
        assert_eq!(
            Ordering::Greater,
            reduction_cmp(&before, &after),
            "so the order puts the unfused face on the left, which is the cell as written"
        );
        assert_eq!(
            Ordering::Less,
            reduction_cmp(&after, &before),
            "and the relation is antisymmetric on it"
        );
    }

    #[test]
    fn a_size_difference_orients_when_the_larger_side_dominates()
    {
        // Where the node counts differ and the larger side carries every hole
        // of the smaller at least as often, the size comparison decides.
        let larger = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("n")]),
            ConsPat::op("add", [ProdPat::meta("m")], ConsPat::meta("a")),
        );
        let smaller = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("n"),
            ConsPat::op("add", [ProdPat::meta("m")], ConsPat::meta("a")),
        );
        assert!(
            larger.size() > smaller.size(),
            "the hypothesis: the two differ in node count"
        );
        assert_eq!(
            Ordering::Greater,
            reduction_cmp(&larger, &smaller),
            "the larger, dominating side is greater"
        );
        assert_eq!(
            Ordering::Less,
            reduction_cmp(&smaller, &larger),
            "and the mirror is less"
        );
    }

    #[test]
    fn a_size_difference_that_substitution_could_reverse_is_an_obstruction()
    {
        // The guard. The left is larger by node count today and smaller under
        // any substitution sending `x` to something of size three or more,
        // because the right repeats `x` and the left does not.
        let larger_now = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Pair", [
                ProdPat::meta("x"),
                ProdPat::ctor("Zero", []),
                ProdPat::ctor("Zero", []),
            ]),
            ConsPat::top(),
        );
        let grows_faster = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("x")]),
            ConsPat::top(),
        );
        assert!(
            larger_now.size() > grows_faster.size(),
            "the hypothesis: the guarded side is the one a size order would pick"
        );
        assert_eq!(
            Ordering::Equal,
            reduction_cmp(&larger_now, &grows_faster),
            "the hole counts do not license the size comparison, so it is an honest obstruction"
        );
        assert_eq!(
            Ordering::Equal,
            reduction_cmp(&grows_faster, &larger_now),
            "in either direction"
        );
    }

    #[test]
    fn an_equal_size_pair_the_path_order_cannot_separate_stays_an_obstruction()
    {
        // Two cuts differing only in which of two holes sits where are the
        // same size with the same hole counts, and the path order reaches the
        // metavariable leaves without a precedence to separate them.
        let left = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("x"),
            ConsPat::op("f", [ProdPat::meta("y")], ConsPat::meta("a")),
        );
        let right = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("y"),
            ConsPat::op("f", [ProdPat::meta("x")], ConsPat::meta("a")),
        );
        assert_eq!(left.size(), right.size(), "the hypothesis: equal size");
        assert_eq!(
            Ordering::Equal,
            reduction_cmp(&left, &right),
            "a path order does not order metavariables, so this pair is left to the engine"
        );
    }

    #[test]
    fn the_frame_defining_shape_is_not_oriented_forwards_and_that_is_stated()
    {
        // The documented limit. A simplification order cannot orient a rule
        // whose right side buries the left's hole under new structure, which
        // is what the frame-defining cell does; its orientation comes from the
        // calculus and never passes through this order.
        let before = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("v"),
            ConsPat::frame("Succ", ConsPat::meta("b")),
        );
        let after = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("v")]),
            ConsPat::meta("b"),
        );
        assert_eq!(
            before.size(),
            after.size(),
            "the two faces are the same size"
        );
        assert_eq!(
            Ordering::Less,
            reduction_cmp(&before, &after),
            "the order reads the constructor-building side as larger, the reverse of the \
             calculus's own orientation"
        );
    }
}
