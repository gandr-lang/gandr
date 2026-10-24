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
//! Both commands are laid out in one node table each, every node's children
//! at strictly smaller indices and the root last. The layout reads the
//! producer and consumer tables in place, each in its own index order, which
//! already puts every node after its children. The tie-break is the
//! lexicographic path order of `gandr_theory_path_orders::lpo`, reading each
//! table from its root and ranking every head at its arity by the precedence
//! above. Nothing recurses.
//!
//! # Reduction order
//!
//! `reduction_cmp` compares node counts, admitted only when the larger side
//! carries every hole of the smaller at least as often: without that guard a
//! repeated hole lets substitution reverse the verdict, and an order that
//! substitution can reverse proves nothing about the instances that rewrite.
//! Equal sizes are decided by the lexicographic path order over a uniform node
//! view, with the precedence `cut > K⁻ > f > K > ★` (a cut, a return-side
//! constructor frame, an operation frame, a constructor, the terminal), then
//! the symbol's own order, then the arity. Ranking the constructor frame above
//! the operation frame orients the fusion cell `⟨v | Succ⁻(add(n; α))⟩ ~> ⟨v |
//! add(n; Succ⁻(α))⟩` in the direction it is written, the direction that
//! removes the intermediate constructor. `Ordering::Equal` means unorientable,
//! an honest obstruction completion reports, never a guess.
//!
//! The path order is a simplification order, so it cannot orient a rule whose
//! right-hand side embeds its left: the frame-defining cell `⟨v | K⁻(β)⟩ ~>
//! ⟨K(v) | β⟩` is that shape, and no precedence orients it forwards. That
//! cell's orientation comes from the calculus and never passes through this
//! order, which orients critical pairs only; the order is therefore not a
//! termination proof for a store holding polarity-derived cells.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::convert::Infallible;

use anodized::spec;
use gandr_theory_path_orders::Former;
use gandr_theory_path_orders::Node;
use gandr_theory_path_orders::Place;
use gandr_theory_path_orders::Precedence;
use gandr_theory_path_orders::Rank;
use gandr_theory_path_orders::Status;
use gandr_theory_path_orders::Term;
use gandr_theory_path_orders::Valuation;
use gandr_theory_path_orders::Valued;
use gandr_theory_path_orders::lpo;
use gandr_theory_path_orders::lpo::Buffers;
use gandr_theory_path_orders::lpo::Orientation;
use gandr_theory_spec_combinators::Mark;
use gandr_theory_spec_combinators::appended;
use quenchant_shape::shape::Maybe;

use crate::pattern::CmdPat;
use crate::pattern::ConsHead;
use crate::pattern::ConsRef;
use crate::pattern::MetaVar;
use crate::pattern::ProdHead;
use crate::pattern::ProdRef;
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
/// - witness: `order::tests::an_equal_size_pair_with_different_holes_stays_an_obstruction`
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
        Ordering::Greater if dominates(&left_holes, &right_holes).0 => Ordering::Greater,
        Ordering::Less if dominates(&right_holes, &left_holes).0 => Ordering::Less,
        Ordering::Equal if left_holes == right_holes => path_order_cmp(lhs, rhs),
        Ordering::Greater | Ordering::Less | Ordering::Equal => Ordering::Equal,
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
    /// - intension: one pass over each consumer and producer table, never
    ///   recursion; the tables are read in their own index order, which already
    ///   puts children first.
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
        let cons = term.push_cons(cmd.consumer().to_ref());
        let prod = term.push_prod(cmd.producer().to_ref());
        term.push(Head::Cut(cmd.polarity()), &[prod, cons]);
        term
    }

    /// Lays one consumer table out and returns its root's index.
    ///
    /// # Specification
    /// - ensures: the table's nodes appended in table order, each frame's
    ///   children being its producer arguments, laid out just before it, then
    ///   its continuations, the most recently completed subtrees, its first
    ///   continuation the most recent; the index of the table's root.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a framed operation and a two-continuation frame
    ///   appear below distinct heads in both comparison directions. Exact
    ///   strict and equal observations reject a wrong root or reordered
    ///   continuations.
    /// - witness: `order::tests::precedence_and_relation_boundaries_preserve_strictness`
    #[spec(captures: before = self.nodes.len(), ensures: |output|
        self.nodes.len() == before.saturating_add(usize::from(cons.size())) && output.0.saturating_add(1) == self.nodes.len())]
    fn push_cons(
        &mut self,
        cons: ConsRef<'term>,
    ) -> FlatIndex
    {
        // The roots of the completed subtrees not yet claimed by a frame, the
        // most recent last.
        let mut completed: Vec<FlatIndex> = Vec::new();
        let mut children: Vec<FlatIndex> = Vec::new();
        let mut root = FlatIndex(self.nodes.len());
        for head in cons.heads() {
            let first = completed
                .len()
                .saturating_sub(usize::from(head.continuations()));
            let rets: Vec<FlatIndex> = completed.drain(first ..).rev().collect();
            children.clear();
            for arg in head.args() {
                children.push(self.push_prod(arg.to_ref()));
            }
            children.extend(rets);
            root = self.push(
                match *head {
                    ConsHead::Op { ref op, .. } => Head::Op(op),
                    ConsHead::Frame(ref ctor) => Head::Frame(ctor),
                    ConsHead::Top => Head::Top,
                    ConsHead::Meta(ref var) => Head::Var(var),
                },
                &children,
            );
            completed.push(root);
        }
        root
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
                ProdHead::Meta(ref var) => Head::Var(var),
                ProdHead::Ctor(ref ctor, _) => Head::Ctor(ctor),
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
        captures: [before = self.nodes.len(), mark = Mark::of(&self.children)],
        ensures: |output| output.0 == before && self.nodes.len() == before.saturating_add(1)
            && self.nodes.get(output.0).is_some_and(|node| node.head == head
                && node.first_child.0 == usize::from(mark) && node.child_count.0 == children.len())
            && appended(&self.children, mark) == children)]
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
        Head::Cut(_) => HeadRank(4),
        Head::Frame(_) => HeadRank(3),
        Head::Op(_) => HeadRank(2),
        Head::Ctor(_) => HeadRank(1),
        Head::Top => HeadRank(0),
        Head::Var(_) => {
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
        Polarity::Positive => HeadRank(0),
        Polarity::Negative => HeadRank(1),
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
        (Head::Cut(left_polarity), Head::Cut(right_polarity)) => {
            polarity_rank(left_polarity).cmp(&polarity_rank(right_polarity))
        },
        (Head::Op(left_sym), Head::Op(right_sym))
        | (Head::Frame(left_sym), Head::Frame(right_sym))
        | (Head::Ctor(left_sym), Head::Ctor(right_sym)) => left_sym.cmp(right_sym),
        (
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

/// Whether `left`'s root strictly exceeds `right`'s root in the path order:
/// the lexicographic path order of [`gandr_theory_path_orders::lpo`] over the
/// two laid-out commands, every head at its arity ranked by
/// [`precedence_cmp`].
///
/// # Specification
/// - ensures: positive exactly when the two roots stand in the strict
///   lexicographic path order induced by [`precedence_cmp`].
/// - panics: none.
/// - intension: no recursion; one table over the two node counts.
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
    let heads = Heads::of(left, right);
    PathVerdict(matches!(
        lpo::orient(&Side(left), &Side(right), &heads, &mut Buffers::default()),
        Orientation::Oriented(_)
    ))
}

/// A head at its arity: the symbol the path order compares.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Applied<'term>
{
    /// The head.
    head: Head<'term>,
    /// Its child count.
    arity: ChildCount,
}

/// The order of two heads at their arities by [`precedence_cmp`], a
/// metavariable beside everything.
///
/// # Specification
/// trivial.
fn ranked(
    one: Applied<'_>,
    two: Applied<'_>,
) -> Ordering
{
    match precedence_cmp(one.head, one.arity, two.head, two.arity) {
        Maybe::Present(order) => order,
        Maybe::Absent(_) => Ordering::Equal,
    }
}

/// A laid-out command as the path order reads it: from its root, so the
/// order's position `n` is the table's node `n` places from its end.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Side<'flat, 'term>(&'flat FlatTerm<'term>);

impl<'term> Side<'_, 'term>
{
    /// The table's node at the order's position `node`.
    ///
    /// # Specification
    /// trivial.
    fn at(
        &self,
        node: Node,
    ) -> Option<&FlatNode<'term>>
    {
        let last = self.0.nodes.len().checked_sub(1)?;
        self.0.nodes.get(last.checked_sub(usize::from(node))?)
    }
}

impl<'term> Term for Side<'_, 'term>
{
    type Bound = Infallible;
    type Symbol = Applied<'term>;
    type Variable = &'term MetaVar;

    /// The command's node count.
    ///
    /// # Specification
    /// trivial.
    fn end(&self) -> Node
    {
        Node::from(self.0.nodes.len())
    }

    /// A metavariable leaf as a variable, every other head at its arity as a
    /// symbol; a position past the command reads as `★`, which is above
    /// nothing.
    ///
    /// # Specification
    /// trivial.
    fn former(
        &self,
        node: Node,
    ) -> Former<Applied<'term>, &'term MetaVar, Infallible>
    {
        match self.at(node) {
            Some(&FlatNode {
                head: Head::Var(variable),
                ..
            }) => Former::Variable(variable),
            Some(found) => Former::Symbol(Applied {
                head: found.head,
                arity: found.child_count,
            }),
            None => Former::Symbol(Applied {
                head: Head::Top,
                arity: ChildCount(0),
            }),
        }
    }

    /// The node's children, left to right, at the order's positions.
    ///
    /// # Specification
    /// trivial.
    fn arguments(
        &self,
        node: Node,
    ) -> impl Iterator<Item = Node> + Clone
    {
        let last = self.0.nodes.len().saturating_sub(1);
        self.at(node)
            .map_or(&[][..], |found| self.0.children_of(found))
            .iter()
            .map(move |&FlatIndex(child)| Node::from(last.saturating_sub(child)))
    }
}

impl Valued for Side<'_, '_>
{
    /// No metavariable of a command pattern is a value.
    ///
    /// # Specification
    /// trivial.
    fn valuation(
        &self,
        _variable: &MetaVar,
    ) -> Valuation
    {
        Valuation::Term
    }
}

/// Every function head of two laid-out commands at its arity, once each, in
/// [`precedence_cmp`] order: a head's place is its position.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Debug)]
struct Heads<'term>(Vec<Applied<'term>>);

impl<'term> Heads<'term>
{
    /// The function heads of `left` and `right`, ordered and without repeats.
    ///
    /// # Specification
    /// trivial.
    fn of(
        left: &FlatTerm<'term>,
        right: &FlatTerm<'term>,
    ) -> Self
    {
        let mut heads: Vec<Applied<'term>> = left
            .nodes
            .iter()
            .chain(&right.nodes)
            .filter(|node| !matches!(node.head, Head::Var(_)))
            .map(|node| Applied {
                head: node.head,
                arity: node.child_count,
            })
            .collect();
        heads.sort_by(|&one, &two| ranked(one, two));
        heads.dedup();
        Self(heads)
    }
}

impl<'term> Precedence for Heads<'term>
{
    type Symbol = Applied<'term>;

    /// The head's position among the ordered heads; ground for a head neither
    /// command holds.
    ///
    /// # Specification
    /// trivial.
    fn place(
        &self,
        symbol: Applied<'term>,
    ) -> Place
    {
        self.0
            .binary_search_by(|&probe| ranked(probe, symbol))
            .map_or(Place::Ground, |at| {
                Place::Ranked(Rank::from(u64::try_from(at).unwrap_or(u64::MAX)))
            })
    }

    /// Lexicographic, for every head.
    ///
    /// # Specification
    /// trivial.
    fn status(
        &self,
        _symbol: Applied<'term>,
    ) -> Status
    {
        Status::Lexicographic
    }
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
        let split = |first: &str, second: &str| {
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("A", []),
                ConsPat::operation("f", [], [
                    ConsPat::frame(first, ConsPat::top()),
                    ConsPat::frame(second, ConsPat::top()),
                ]),
            )
        };
        assert_eq!(
            Ordering::Less,
            path_order_cmp(&split("A", "Z"), &split("Z", "A")),
            "continuations are compared in port order"
        );
        assert_eq!(
            Ordering::Greater,
            path_order_cmp(&split("Z", "A"), &split("A", "Z"))
        );
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
    fn an_equal_size_pair_with_different_holes_stays_an_obstruction()
    {
        // A hole against a constructor of the same size: the path order would
        // separate them, but a substitution could grow the hole past it.
        let hole = CmdPat::cut(Polarity::Positive, ProdPat::meta("x"), ConsPat::meta("a"));
        let ground = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::meta("a"),
        );
        assert_eq!(hole.size(), ground.size(), "the hypothesis: equal size");
        assert_eq!(Ordering::Equal, reduction_cmp(&hole, &ground));
        assert_eq!(Ordering::Equal, reduction_cmp(&ground, &hole));
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
