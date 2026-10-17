//! The term alphabet: a description's rules read as first-order rewrites over
//! terms, every subterm a position a rule may fire at.
//!
//! # Why a second alphabet
//!
//! The sequent alphabet rewrites a command at its root: an operation call is
//! the cut its rules match, and every rewrite the call takes stays at that
//! cut. A rule whose left-hand side is a constructor application —
//! `Loop(Unloop(x)) ==> x`, a presented type's rule — rewrites a value
//! wherever in a term it stands: `Loop(Loop(Unloop(Base)))` holds its redex
//! below the root. No root cut reaches it, and the frame-defining cell that
//! moves a constructor from the consumer into the producer moves it past the
//! rule before the rule can see it, so the two cells' critical pair never
//! joins. A description with a constructor-headed rule is therefore also read
//! here, where a term is a tree of constructor, operation and results nodes
//! and every node is a position, so a rule fires below the root and two rules
//! overlap inside a left-hand side ([`elaborate_data_desc`] builds the store).
//!
//! - **Choice.** A second inhabitant of [`CellAlphabet`] over the description's
//!   own free terms, so normalization, replay and the critical-pair check are
//!   the generic engines, with one more alphabet beside the sequent one.
//! - **Alternatives.** Constructor-headed cells in the sequent store, a rule
//!   `K(p) ==> r` cutting `p` against the return-side frame `K⁻`: the
//!   frame-defining cell overlaps it at that cut, folds the constructor into
//!   the producer, and the folded term holds a redex no cell at the root reads,
//!   so the pair diverges for every presented type. Guarding the frame cell by
//!   the constructors its argument may not start with leaves open terms split
//!   between producer and frames in more than one way, so equal terms compare
//!   unequal. A bespoke term rewriter beside the engines would be a second
//!   normalizer and a second certificate format.
//! - **Reversal.** A sequent alphabet with command positions inside a producer
//!   would hold both readings in one store.
//!
//! A term is one table in prefix order, every node followed by its children,
//! so no term routes ownership through itself and no walk over one recurses;
//! a node's children are found by skipping subterm ends. The reduction order
//! is size guarded by hole domination, the order completion orients by; the
//! description's termination is the path order's question, decided over the
//! written faces before any store is read. Every cell may fire anywhere: the
//! alphabet has one polarity. Renaming apart primes a name until it is fresh
//! against the anchor and the other fresh names, so a cell already apart
//! comes back unchanged.
//!
//! [`elaborate_data_desc`]: crate::elaborate_data_desc

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellInvertibility;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CommandSpliceRefusal;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::FiringPermission;
use gandr_theory_cell_complexes::Generalization;
use gandr_theory_cell_complexes::GeneralizationArm;
use gandr_theory_cell_complexes::GeneralizationPoint;
use gandr_theory_cell_complexes::PatternSize;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes::SeamRole;
use gandr_theory_cell_complexes::SubstitutionDecision;
use gandr_theory_cell_complexes::anti_unification;
use gandr_theory_cell_complexes::command_subterm;
use gandr_theory_cell_complexes::path_order;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

/// The term alphabet marker.
///
/// # Specification
/// - ensures: the implementation keeps the inhabitant laws an engine spends:
///   substituting a match into its pattern reproduces the matched term, a
///   successful match binds every metavariable the pattern names, and splicing
///   at a position agrees with reading there.
/// - provides: terms whose every subterm is a command position, so a rule fires
///   below the root and two rules overlap inside a left-hand side.
/// - panics: none.
/// - executable: none — this stateless marker owns no terms or substitutions;
///   its laws relate the operations its witnesses exercise.
///
/// # Adequacy
/// - hypothesis: L3 — each law is asserted pointwise on terms that bind
///   distinct, repeated and target-carried metavariables, at every position of
///   a term nesting constructors, operations and results two deep.
/// - witness: `term::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
/// - witness: `term::tests::substitution_walks_are_transactional_and_bounded`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TermAlphabet;

/// A count or an index within one term table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Count(usize);

impl Count
{
    /// The next index.
    ///
    /// # Specification
    /// - ensures: one more than `self`, saturating at `usize::MAX`; a table
    ///   held in memory never reaches that bound.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, ordinary, last-in-range and saturated indices
    ///   have exact successors. Wrapping or skipping the increment changes the
    ///   boundary observations.
    /// - witness: `term::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[spec(ensures: |ret| if self.0 == usize::MAX { ret.0 == usize::MAX }
        else { matches!(ret.0.checked_sub(self.0), Some(1)) })]
    const fn next(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

/// One node of a term.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Head
{
    /// A metavariable leaf: a rule's pattern variable.
    Var(Name),
    /// A skolem constant leaf, the replay's stand-in for a metavariable: no
    /// pattern but a metavariable matches it.
    Konst(Name),
    /// A constructor application over its argument count.
    Ctor(Name, Count),
    /// An operation application over its argument count.
    Op(Name, Count),
    /// A results tuple over its component count.
    Results(Count),
}

impl Head
{
    /// The node's number of children.
    ///
    /// # Specification
    /// trivial.
    const fn arity(&self) -> Count
    {
        match *self {
            Self::Var(_) | Self::Konst(_) => Count(0),
            Self::Ctor(_, arity) | Self::Op(_, arity) | Self::Results(arity) => arity,
        }
    }
}

/// A term of the alphabet: its nodes in prefix order.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Term(Vec<Head>);

quenchant_shape::reason_enum! {
    /// Why a term reads back as no free term.
    pub mod term_reading {
        /// The reason the term writes no free term.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The term holds a skolem constant, which only a replay writes and
            /// no free term spells.
            Skolem,
        }
    }
}

impl From<&FreeTerm> for Term
{
    /// The free term's nodes in prefix order, each head kept.
    ///
    /// # Specification
    /// - ensures: one node per free-term node in prefix order, a variable a
    ///   metavariable, a constructor, an operation and a results tuple each
    ///   their own head over their argument count.
    /// - panics: none.
    /// - intension: one pass with an explicit stack of the subterms still to
    ///   visit, so nesting costs no call stack.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a term nesting a constructor, an operation and a
    ///   results tuple reads back as itself, and its positions are the free
    ///   term's; a child order reversed or a head kind merged changes the read.
    /// - witness: `term::tests::a_free_term_reads_back_through_the_alphabet`
    #[inline]
    #[spec(ensures: |ret| ret.read() == Maybe::Present(term.clone()))]
    fn from(term: &FreeTerm) -> Self
    {
        let mut nodes = Vec::new();
        let mut pending = alloc::vec![term.to_node()];
        while let Some(node) = pending.pop() {
            let (head, args) = match node.view() {
                TermView::Var(name) => {
                    nodes.push(Head::Var(name.clone()));
                    continue;
                },
                TermView::Ctor { name, args } => {
                    (Head::Ctor(name.clone(), Count(args.len())), args)
                },
                TermView::Op { name, args } => (Head::Op(name.clone(), Count(args.len())), args),
                TermView::Results { args } => (Head::Results(Count(args.len())), args),
            };
            nodes.push(head);
            let mark = pending.len();
            pending.extend(args);
            if let Some(children) = pending.get_mut(mark ..) {
                children.reverse();
            }
        }
        Self(nodes)
    }
}

impl Term
{
    /// The free term this term spells.
    ///
    /// # Specification
    /// - ensures: one free-term node per node, in the same order.
    /// - provides: [`term_reading::Absent::Skolem`] when a node is a skolem
    ///   constant.
    /// - panics: none.
    /// - intension: one pass over the table in reverse prefix order, each
    ///   application taking its arguments off a stack.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the conversion from a free term, and a skolemized
    ///   term reads as none; reading a constructor's arguments in reverse
    ///   changes a witnessed term.
    /// - witness: `term::tests::a_free_term_reads_back_through_the_alphabet`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every node once; the check scans them once more for a skolem constant"
        )
    )]
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) == self.0.iter().any(|head| matches!(*head, Head::Konst(_))))]
    pub fn read(&self) -> Maybe<FreeTerm, term_reading::Absent>
    {
        let mut built: Vec<FreeTerm> = Vec::new();
        for head in self.0.iter().rev() {
            let take = |built: &mut Vec<FreeTerm>, arity: Count| {
                let split = built.len().saturating_sub(arity.0);
                built.drain(split ..).rev().collect::<Vec<FreeTerm>>()
            };
            let node = match *head {
                Head::Var(ref name) => FreeTerm::var(name),
                Head::Konst(_) => return Maybe::Absent(term_reading::Absent::Skolem),
                Head::Ctor(ref name, arity) => FreeTerm::ctor(name, take(&mut built, arity)),
                Head::Op(ref name, arity) => FreeTerm::op(name, take(&mut built, arity)),
                Head::Results(arity) => FreeTerm::results(take(&mut built, arity)),
            };
            built.push(node);
        }
        built
            .pop()
            .map_or_else(|| Maybe::Present(FreeTerm::results([])), Maybe::Present)
    }

    /// The end of the subterm starting at `start`: one past its last node.
    ///
    /// # Specification
    /// - ensures: the index after the subterm rooted at `start`; the table's
    ///   length when the table is cut short.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — leaf, nested, truncated and exhausted ranges have
    ///   exact ends. Incorrect pending arity, a skipped child or an off-by-one
    ///   end changes the selected subterm.
    /// - witness: `term::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[spec(ensures: |output| output >= start && (start.0 > self.0.len() || output.0 <= self.0.len())
        && (start.0 != 0 || output.0 == self.0.len() || self.0.is_empty()))]
    fn end_of(
        &self,
        start: Count,
    ) -> Count
    {
        let mut pending = Count(1);
        let mut index = start;
        while pending > Count(0) {
            let Some(head) = self.0.get(index.0)
            else {
                break;
            };
            pending = Count(pending.0.saturating_sub(1).saturating_add(head.arity().0));
            index = index.next();
        }
        index
    }

    /// The range of the subterm reached by following `steps` from the root.
    ///
    /// # Specification
    /// - ensures: the start and end of the subterm `steps` reaches.
    /// - provides: [`command_subterm::Absent::OffTerm`] when a step indexes
    ///   past a node's children.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every node of a nested tree reads its exact subterm;
    ///   out-of-arity and below-leaf paths refuse. Shifted offsets or a missed
    ///   boundary changes those reads.
    /// - witness: `term::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[spec(ensures: |output| match output {
        Maybe::Present((start, end)) => start <= end && end.0 <= self.0.len()
            && (!steps.is_empty() || start.0 == 0),
        Maybe::Absent(command_subterm::Absent::OffTerm) => !steps.is_empty(),
        Maybe::Absent(command_subterm::Absent::NotACommand) => false,
    })]
    fn range_at(
        &self,
        steps: &[PositionStep],
    ) -> Maybe<(Count, Count), command_subterm::Absent>
    {
        let mut start = Count(0);
        for &step in steps {
            let Some(head) = self.0.get(start.0)
            else {
                return Maybe::Absent(command_subterm::Absent::OffTerm);
            };
            let step = Count(usize::from(step));
            if step >= head.arity() {
                return Maybe::Absent(command_subterm::Absent::OffTerm);
            }
            let mut child = start.next();
            for _ in 0 .. step.0 {
                child = self.end_of(child);
            }
            start = child;
        }
        Maybe::Present((start, self.end_of(start)))
    }

    /// The subterm occupying `[start, end)`, owned.
    ///
    /// # Specification
    /// - requires: ordered bounds within the node table.
    /// - ensures: exactly the selected node range, in its original order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — valid leaf and nested ranges reconstruct exact
    ///   subterms. Reversed bounds or an extra node changes read and splice
    ///   round trips.
    /// - witness: `term::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[spec(requires: start <= end && end.0 <= self.0.len(), ensures: |output| self.0.get(start.0 .. end.0) == Some(output.0.as_slice()))]
    fn slice(
        &self,
        start: Count,
        end: Count,
    ) -> Self
    {
        Self(self.0.iter().take(end.0).skip(start.0).cloned().collect())
    }

    /// The term's metavariables, left to right with repeats.
    ///
    /// # Specification
    /// - ensures: every metavariable occurrence in prefix order, with repeats.
    /// - panics: none.
    /// - executable: none — the wrapper closure receives an impl-Trait return
    ///   type that Rust rejects for closures.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty occurrence lists and repeated names are
    ///   observed through exact metadata and multiplicities. Dropped repeats,
    ///   invented variables and reversal change those observations.
    /// - witness: `term::tests::metadata_names_and_orders_observe_boundaries`
    fn vars(&self) -> impl Iterator<Item = &Name>
    {
        self.0.iter().filter_map(|head| match *head {
            Head::Var(ref var) => Some(var),
            Head::Konst(_) | Head::Ctor(..) | Head::Op(..) | Head::Results(_) => None,
        })
    }

    /// The term with every metavariable relabelled by `relabel`, which keeps
    /// every leaf a leaf.
    ///
    /// # Specification
    /// - requires: the relabeller returns a leaf for every variable it sees.
    /// - ensures: relabelled variables with all other heads and node arities
    ///   kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — leaf-preserving freshening and skolemization keep
    ///   exact application structure and repeated-name identity. Relabelling
    ///   other heads or changing arity changes the terms.
    /// - witness: `term::tests::metadata_names_and_orders_observe_boundaries`
    #[spec(ensures: |output| output.0.len() == self.0.len()
        && output.0.iter().zip(&self.0).all(|(after, before)| after.arity() == before.arity()))]
    fn relabel<R>(
        &self,
        relabel: R,
    ) -> Self
    where
        R: Fn(&Name) -> Head,
    {
        Self(
            self.0
                .iter()
                .map(|head| match *head {
                    Head::Var(ref var) => relabel(var),
                    Head::Konst(_) | Head::Ctor(..) | Head::Op(..) | Head::Results(_) => {
                        head.clone()
                    },
                })
                .collect(),
        )
    }
}

/// A position: a path of child indices from the root.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct TermPos(Box<[PositionStep]>);

impl TermPos
{
    /// The child indices from the root outward.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn steps(&self) -> &[PositionStep]
    {
        &self.0
    }
}

/// A substitution: an ordered map from metavariables to terms.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct TermSubst(BTreeMap<Name, Term>);

impl TermSubst
{
    /// The term with every bound metavariable replaced by its image, once.
    ///
    /// # Specification
    /// - ensures: each bound variable is replaced by its image once, without
    ///   visiting that image; unbound variables and other heads are kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a triangular map separates one-pass replacement from
    ///   full application; empty maps and absent names stay unchanged.
    ///   Re-entering an image or dropping a binding changes the resulting term.
    /// - witness: `term::tests::substitution_walks_are_transactional_and_bounded`
    #[spec(ensures: |output| output.0.len() == term.0.iter().fold(0_usize, |size, head| size.saturating_add(match *head {
        Head::Var(ref var) => self.0.get(var).map_or(1, |image| image.0.len()), Head::Konst(_) | Head::Ctor(..) | Head::Op(..) | Head::Results(_) => 1,
    })) && (term.vars().any(|var| self.0.contains_key(var)) || output == *term))]
    fn apply_once(
        &self,
        term: &Term,
    ) -> Term
    {
        let mut nodes = Vec::with_capacity(term.0.len());
        for head in &term.0 {
            if let Head::Var(ref var) = *head
                && let Some(image) = self.0.get(var)
            {
                nodes.extend(image.0.iter().cloned());
                continue;
            }
            nodes.push(head.clone());
        }
        Term(nodes)
    }

    /// The term with the substitution applied to its fixpoint.
    ///
    /// # Specification
    /// - ensures: no bound metavariable remains when the bindings are acyclic;
    ///   at most one pass per binding plus one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ground images, triangular chains and a self-cycle
    ///   have exact final terms. Missing a triangular pass, substituting a
    ///   wrong image or changing an unbound term changes the result.
    /// - witness: `term::tests::substitution_walks_are_transactional_and_bounded`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "the check reads each image's metavariables once, over the few bindings one rule's match or one overlap's unifier holds"
        )
    )]
    #[spec(ensures: |output| (term.vars().any(|var| self.0.contains_key(var)) || output == *term)
        && (!self.0.values().all(|image| image.vars().all(|var| !self.0.contains_key(var)))
            || output.vars().all(|var| !self.0.contains_key(var))))]
    fn apply_fully(
        &self,
        term: &Term,
    ) -> Term
    {
        let mut current = term.clone();
        for _ in 0 ..= self.0.len() {
            let next = self.apply_once(&current);
            if next == current {
                break;
            }
            current = next;
        }
        current
    }

    /// `term` followed through the bindings while it is a bare bound
    /// metavariable.
    ///
    /// # Specification
    /// - ensures: the first term on the binding chain that is not a bound
    ///   metavariable, or the term reached after one step per binding.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bound and free leaves, compound terms and a
    ///   self-cycle separate head walking from full substitution. Losing a
    ///   chain link or descending into compound arguments changes the result.
    /// - witness: `term::tests::substitution_walks_are_transactional_and_bounded`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "the check compares the result with each image once, over the few bindings one unifier holds"
        )
    )]
    #[spec(captures: original = term.clone(), ensures: |output| output == original || self.0.values().any(|image| image == &output))]
    fn walk(
        &self,
        term: Term,
    ) -> Term
    {
        let mut current = term;
        for _ in 0 ..= self.0.len() {
            let image = match current.0.as_slice() {
                &[Head::Var(ref var)] => self.0.get(var),
                _ => None,
            };
            let Some(image) = image
            else {
                break;
            };
            current = image.clone();
        }
        current
    }
}

/// How a cell's orientation was fixed.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TermOrient
{
    /// As the rule is written: left to right.
    Written,
    /// Chosen by the reduction order.
    Derived,
}

/// Where a cell came from.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TermProv
{
    /// A rule the description writes.
    SurfaceRule,
    /// Derived by completion or fusion.
    Derived,
}

/// A cell's metadata: the metavariables of both faces, in first-occurrence
/// order, and the invertibility the cell was built with.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TermMeta
{
    /// The distinct metavariables of both faces.
    vars: Vec<Name>,
    /// Whether the cell is an invertible certificate.
    invertible: CellInvertibility,
}

/// A count of one metavariable's occurrences.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Occurrences(usize);

/// How often each metavariable occurs in a term.
///
/// # Specification
/// - ensures: each occurring variable has its exact positive multiplicity.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, single and repeated variable sets have exact keyed
///   counts. Deduplication, extra keys and a lost occurrence change the
///   domination decision.
/// - witness: `term::tests::metadata_names_and_orders_observe_boundaries`
#[spec(ensures: |output| output.values().fold(0_usize, |sum, count| sum.saturating_add(count.0)) == term.vars().count()
    && output.iter().all(|(var, count)| count.0 > 0 && count.0 == term.vars().filter(|held| held == var).count()))]
fn occurrences(term: &Term) -> BTreeMap<&Name, Occurrences>
{
    let mut counts: BTreeMap<&Name, Occurrences> = BTreeMap::new();
    for var in term.vars() {
        let count = counts.entry(var).or_default();
        count.0 = count.0.saturating_add(1);
    }
    counts
}

/// Whether one side carries every metavariable of the other at least as often.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HoleDomination
{
    /// Every hole of the smaller side occurs at least as often on the larger.
    Dominates,
    /// Some hole of the smaller side occurs more often than on the larger.
    FallsShort,
}

/// Whether `larger` dominates `smaller` hole by hole.
///
/// # Specification
/// - ensures: domination exactly when every smaller-side count is present on
///   the larger side with at least the same multiplicity.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, missing, equal and smaller multiplicities separate
///   domination from refusal. Strict comparison at equality or a permissive
///   missing-key default changes the result.
/// - witness: `term::tests::metadata_names_and_orders_observe_boundaries`
#[spec(ensures: |output| (output == HoleDomination::Dominates) == smaller.iter().all(|(var, count)| larger.get(var).is_some_and(|held| held >= count)))]
fn dominates(
    larger: &BTreeMap<&Name, Occurrences>,
    smaller: &BTreeMap<&Name, Occurrences>,
) -> HoleDomination
{
    if smaller
        .iter()
        .all(|(var, count)| larger.get(var).is_some_and(|held| held >= count))
    {
        return HoleDomination::Dominates;
    }
    HoleDomination::FallsShort
}

/// The least general generalization of a family of term tuples.
///
/// # Specification
/// - ensures: one pattern per component; every member's component is its
///   pattern with each point's arm applied; a head every member holds at a
///   position is kept and descended into, so a point stands only where two
///   members differ; two positions whose subterms agree member by member stand
///   one point; every point's name is `$g$` and a suffix, worn by no member;
///   the points are listed in the order the walk meets them, component by
///   component, in prefix order.
/// - provides: [`anti_unification::Absent::EmptyFamily`] for a family with no
///   member; [`anti_unification::Absent::RaggedFamily`] when two members have
///   different lengths. Every node may be a metavariable, so every family that
///   is neither generalizes.
/// - panics: none.
/// - intension: one lockstep walk emitting the pattern in prefix order, the
///   pending child columns on a heap stack; a new point is compared with every
///   point already stood.
///
/// # Adequacy
/// - hypothesis: L3 — a shared constructor is kept above a point, a repeated
///   disagreement stands one point, a point's name avoids every member's, and
///   each refusal is reached by its own family; each member is its
///   generalization under its arms.
/// - witness: `term::tests::a_family_generalizes_to_its_least_general_pattern`
#[spec(ensures: |output| match output {
    Maybe::Absent(anti_unification::Absent::EmptyFamily) => family.is_empty(),
    Maybe::Absent(anti_unification::Absent::RaggedFamily) => family.first().is_some_and(|first| family.iter().any(|member| member.len() != first.len())),
    Maybe::Absent(anti_unification::Absent::Ungeneralizable) => false,
    Maybe::Present(ref generalized) => family.first().is_some_and(|first| generalized.patterns.len() == first.len())
        && family.iter().all(|member| member.len() == generalized.patterns.len())
        && generalized.points.iter().all(|point| point.arms.len() == family.len()
            && family.iter().flat_map(|member| member.iter()).flat_map(Term::vars).all(|var| var != &point.var)),
})]
fn anti_unify_terms(
    family: &[&[Term]]
) -> Maybe<Generalization<TermAlphabet>, anti_unification::Absent>
{
    let Some((first, rest)) = family.split_first()
    else {
        return Maybe::Absent(anti_unification::Absent::EmptyFamily);
    };
    if rest.iter().any(|member| member.len() != first.len()) {
        return Maybe::Absent(anti_unification::Absent::RaggedFamily);
    }
    let mut taken: BTreeSet<Name> = family
        .iter()
        .flat_map(|member| member.iter())
        .flat_map(Term::vars)
        .cloned()
        .collect();
    let mut suffix = Count(0);
    let mut stood: Vec<(Name, Vec<&[Head]>)> = Vec::new();
    let mut patterns = Vec::with_capacity(first.len());
    for (component, term) in first.iter().enumerate() {
        let members: Vec<&Term> = core::iter::once(term)
            .chain(rest.iter().filter_map(|member| member.get(component)))
            .collect();
        let mut nodes: Vec<Head> = Vec::new();
        let mut visits: Vec<Vec<Count>> = alloc::vec![alloc::vec![Count(0); members.len()]];
        while let Some(starts) = visits.pop() {
            let mut heads = members
                .iter()
                .zip(&starts)
                .map(|(member, start)| member.0.get(start.0));
            let shared = match heads.next() {
                Some(Some(head)) if heads.all(|other| other == Some(head)) => Some(head),
                Some(_) | None => None,
            };
            if let Some(head) = shared {
                nodes.push(head.clone());
                let mut cursor: Vec<Count> = starts.iter().map(|start| start.next()).collect();
                let mut children: Vec<Vec<Count>> = Vec::with_capacity(head.arity().0);
                for _ in 0 .. head.arity().0 {
                    let next: Vec<Count> = members
                        .iter()
                        .zip(&cursor)
                        .map(|(member, child)| member.end_of(*child))
                        .collect();
                    children.push(core::mem::replace(&mut cursor, next));
                }
                visits.extend(children.into_iter().rev());
                continue;
            }
            let column: Vec<&[Head]> = members
                .iter()
                .zip(&starts)
                .map(|(member, start)| {
                    member
                        .0
                        .get(start.0 .. member.end_of(*start).0)
                        .unwrap_or_default()
                })
                .collect();
            if let Some(seen) = stood.iter().find(|seen| seen.1 == column) {
                nodes.push(Head::Var(seen.0.clone()));
                continue;
            }
            let fresh = loop {
                let name = Name::from(alloc::format!("$g${}", suffix.0));
                suffix = suffix.next();
                if taken.insert(name.clone()) {
                    break name;
                }
            };
            stood.push((fresh.clone(), column));
            nodes.push(Head::Var(fresh));
        }
        patterns.push(Term(nodes));
    }
    let points = stood
        .into_iter()
        .map(|(var, column)| {
            let arms = column
                .iter()
                .map(|subterm| GeneralizationArm {
                    binding: TermSubst(BTreeMap::from([(var.clone(), Term(subterm.to_vec()))])),
                    size: PatternSize::from(subterm.len()),
                })
                .collect();
            GeneralizationPoint { var, arms }
        })
        .collect();
    Maybe::Present(Generalization { patterns, points })
}

impl CellAlphabet for TermAlphabet
{
    type Cmd = Term;
    type Hole = Name;
    type Meta = TermMeta;
    type Orientation = TermOrient;
    type Pos = TermPos;
    type Provenance = TermProv;
    type Subst = TermSubst;
    type Var = Name;

    /// Matching by one lockstep pass over the two prefix tables.
    ///
    /// # Specification
    /// - ensures: each pattern metavariable binds the target subterm at its
    ///   place, a bound one only an equal subterm; every other node must equal
    ///   the target's, so a pattern node never matches a skolem constant.
    ///   `subst` is extended only on success.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ground and schematic matches reconstruct targets in
    ///   one pass; incompatible heads and repeated-hole conflicts preserve an
    ///   existing map. Wrong binding and partial commitment change the
    ///   observations.
    /// - witness: `term::tests::substitution_walks_are_transactional_and_bounded`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body clones `subst` into its staging map and compares each bound image it meets"
        )
    )]
    #[spec(captures: before = subst.clone(), ensures: |output| if bool::from(output) { subst.apply_once(pattern) == *target } else { *subst == before })]
    fn match_cmd(
        pattern: &Self::Cmd,
        target: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision
    {
        let mut found = subst.clone();
        let mut at = Count(0);
        for head in &pattern.0 {
            let Some(target_head) = target.0.get(at.0)
            else {
                return SubstitutionDecision::from(false);
            };
            if let Head::Var(ref var) = *head {
                let end = target.end_of(at);
                let image = target.slice(at, end);
                if found.0.get(var).is_some_and(|bound| *bound != image) {
                    return SubstitutionDecision::from(false);
                }
                found.0.insert(var.clone(), image);
                at = end;
                continue;
            }
            if head != target_head {
                return SubstitutionDecision::from(false);
            }
            at = at.next();
        }
        if at != Count(target.0.len()) {
            return SubstitutionDecision::from(false);
        }
        *subst = found;
        SubstitutionDecision::from(true)
    }

    /// Robinson unification over owned subterm pairs.
    ///
    /// # Specification
    /// - ensures: a most general unifier extending `subst` on success, with the
    ///   occurs check, resolved so no image holds a bound metavariable: one
    ///   pass of it is its fixpoint, which is what [`Self::apply_subst`]
    ///   applies (#654). `subst` is extended only on success.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — compatible distinct holes and triangular images
    ///   equate both faces; a head clash and an occurs cycle preserve prior
    ///   bindings. Eager commits, skipped occurs checks and an unresolved chain
    ///   change the result.
    /// - witness: `term::tests::substitution_walks_are_transactional_and_bounded`
    /// - witness: `term::tests::a_substitution_replaces_each_variable_once_all_at_once_654`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body clones `subst` into its staging map, walks each goal through it and resolves each image once"
        )
    )]
    #[spec(captures: before = subst.clone(), ensures: |output| if bool::from(output) {
        subst.apply_once(lhs) == subst.apply_once(rhs)
            && subst.0.values().all(|image| image.vars().all(|var| !subst.0.contains_key(var)))
    } else { *subst == before })]
    fn unify_cmd(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision
    {
        let mut found = subst.clone();
        let mut goals = alloc::vec![(lhs.clone(), rhs.clone())];
        while let Some((left, right)) = goals.pop() {
            let left = found.walk(left);
            let right = found.walk(right);
            let (var, image) = match (left.0.as_slice(), right.0.as_slice()) {
                (&[Head::Var(ref x)], &[Head::Var(ref y)]) if x == y => continue,
                (&[Head::Var(ref var)], _) => (var.clone(), right.clone()),
                (_, &[Head::Var(ref var)]) => (var.clone(), left.clone()),
                (&[ref left_head, ..], &[ref right_head, ..]) if left_head == right_head => {
                    let mut left_child = Count(1);
                    let mut right_child = Count(1);
                    for _ in 0 .. left_head.arity().0 {
                        let left_end = left.end_of(left_child);
                        let right_end = right.end_of(right_child);
                        goals.push((
                            left.slice(left_child, left_end),
                            right.slice(right_child, right_end),
                        ));
                        left_child = left_end;
                        right_child = right_end;
                    }
                    continue;
                },
                _ => return SubstitutionDecision::from(false),
            };
            if found
                .apply_fully(&image)
                .vars()
                .any(|occurring| *occurring == var)
            {
                return SubstitutionDecision::from(false);
            }
            found.0.insert(var, image);
        }
        let resolved = found
            .0
            .iter()
            .map(|(var, image)| (var.clone(), found.apply_fully(image)))
            .collect();
        *subst = TermSubst(resolved);
        SubstitutionDecision::from(true)
    }

    /// The least general generalization of a family of term tuples.
    ///
    /// # Specification
    /// - ensures: as [`anti_unify_terms`].
    /// - provides: as [`anti_unify_terms`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nesting families reconstruct every member under their
    ///   arms, while empty and ragged families return distinct refusals. Lost
    ///   components or wrong arms change the observations.
    /// - witness: `term::tests::a_family_generalizes_to_its_least_general_pattern`
    #[inline]
    #[spec(ensures: |output| match output {
        Maybe::Present(ref generalized) => family.first().is_some_and(|first| generalized.patterns.len() == first.len()) && generalized.points.iter().all(|point| point.arms.len() == family.len()),
        Maybe::Absent(anti_unification::Absent::EmptyFamily) => family.is_empty(),
        Maybe::Absent(anti_unification::Absent::RaggedFamily) => family.first().is_some_and(|first| family.iter().any(|member| member.len() != first.len())),
        Maybe::Absent(anti_unification::Absent::Ungeneralizable) => false,
    })]
    fn anti_unify_cmd(
        family: &[&[Self::Cmd]]
    ) -> Maybe<Generalization<Self>, anti_unification::Absent>
    {
        anti_unify_terms(family)
    }

    /// The term with every bound metavariable replaced by its image, once and
    /// all at once: an image is never read again, so a variable of the term a
    /// match was taken from stays that term's whatever the pattern named its
    /// own (#654), and a unifier, resolved by [`Self::unify_cmd`], needs no
    /// second pass.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn apply_subst(
        subst: &Self::Subst,
        cmd: &Self::Cmd,
    ) -> Self::Cmd
    {
        subst.apply_once(cmd)
    }

    /// The bindings of `vars` alone.
    ///
    /// # Specification
    /// - ensures: exactly the existing bindings whose keys occur in vars.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — none, one, duplicate and absent requested keys expose
    ///   exact restricted maps. Extra bindings and missing retained images
    ///   change the result.
    /// - witness: `term::tests::substitution_walks_are_transactional_and_bounded`
    #[inline]
    #[spec(ensures: |output| output.0.len() == subst.0.keys().filter(|var| vars.contains(var)).count()
        && output.0.iter().all(|(var, image)| vars.contains(var) && subst.0.get(var) == Some(image)))]
    fn restrict_subst(
        subst: &Self::Subst,
        vars: &[Self::Var],
    ) -> Self::Subst
    {
        TermSubst(
            subst
                .0
                .iter()
                .filter(|&(var, _)| vars.contains(var))
                .map(|(var, image)| (var.clone(), image.clone()))
                .collect(),
        )
    }

    /// The term's metavariables, left to right with repeats.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn metavariables(cmd: &Self::Cmd) -> Vec<Self::Var>
    {
        cmd.vars().cloned().collect()
    }

    /// The table's length: one node per entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cmd_size(cmd: &Self::Cmd) -> PatternSize
    {
        PatternSize::from(cmd.0.len())
    }

    /// Every position of the term, breadth first: every subterm is a command.
    ///
    /// # Specification
    /// - ensures: one position per node, the root first and no position before
    ///   one enclosing it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a leaf and a nested tree expose their complete
    ///   breadth-first position list. Duplicates, omitted nodes and a child
    ///   before its parent change the list.
    /// - witness: `term::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[inline]
    #[spec(ensures: |output| output.len() == cmd.0.len() && (cmd.0.is_empty() || output.first().is_some_and(|pos| pos.0.is_empty()))
        && output.iter().enumerate().all(|(index, pos)| !output.iter().take(index).any(|earlier| earlier == pos)
            && (pos.0.is_empty() || output.iter().take(index).any(|parent| pos.0.split_last().is_some_and(|(_, prefix)| parent.0.as_ref() == prefix)))))]
    fn command_positions(cmd: &Self::Cmd) -> Vec<Self::Pos>
    {
        let mut positions = Vec::with_capacity(cmd.0.len());
        let mut queue: VecDeque<(Vec<PositionStep>, Count)> = VecDeque::new();
        queue.push_back((Vec::new(), Count(0)));
        while let Some((path, start)) = queue.pop_front() {
            let Some(head) = cmd.0.get(start.0)
            else {
                continue;
            };
            let mut child = start.next();
            for index in 0 .. head.arity().0 {
                let mut child_path = path.clone();
                child_path.push(PositionStep::from(index));
                queue.push_back((child_path, child));
                child = cmd.end_of(child);
            }
            positions.push(TermPos(path.into_boxed_slice()));
        }
        positions
    }

    /// The empty path.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn root_position() -> Self::Pos
    {
        TermPos::default()
    }

    /// The position of `path`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn position_at_path(path: &[PositionStep]) -> Self::Pos
    {
        TermPos(path.into())
    }

    /// The path order of the two paths.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn position_order(
        left: &Self::Pos,
        right: &Self::Pos,
    ) -> PositionOrder
    {
        path_order(left.0.iter().copied(), right.0.iter().copied())
    }

    /// Discharged: left-hand sides are trees rooted at one node and targets are
    /// trees.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn convexity_discharge(_store: &CellStore<Self>) -> ConvexityDischarge
    {
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget
    }

    /// The subterm at `pos`, owned.
    ///
    /// # Specification
    /// - ensures: the subterm `pos` addresses; every subterm is a command.
    /// - provides: [`command_subterm::Absent::OffTerm`] when a step of `pos`
    ///   indexes past a node's children.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — root and nested nodes return exact terms;
    ///   out-of-arity and below-leaf paths return `OffTerm`. A wrong range or a
    ///   merged absence changes the observation.
    /// - witness: `term::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[inline]
    #[spec(ensures: |output| match output {
        Maybe::Present(ref subterm) => subterm.0.len() <= cmd.0.len() && (!pos.0.is_empty() || subterm == cmd),
        Maybe::Absent(command_subterm::Absent::OffTerm) => matches!(cmd.range_at(&pos.0), Maybe::Absent(command_subterm::Absent::OffTerm)),
        Maybe::Absent(command_subterm::Absent::NotACommand) => false,
    })]
    fn subterm_cmd_at(
        cmd: &Self::Cmd,
        pos: &Self::Pos,
    ) -> Maybe<Self::Cmd, command_subterm::Absent>
    {
        cmd.range_at(&pos.0)
            .map(|(start, end)| cmd.slice(start, end))
    }

    /// `cmd` with the subterm at `pos` replaced.
    ///
    /// # Specification
    /// - ensures: the term equal to `cmd` except at `pos`, which holds
    ///   `replacement`.
    /// - fails: [`CommandSpliceRefusal::OffTerm`] when a step of `pos` indexes
    ///   past a node's children.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — root, shrinking and growing replacements preserve
    ///   exact siblings, and invalid paths refuse. Dropped context, shifted
    ///   bounds and incorrect replacement change the term.
    /// - witness: `term::tests::positions_preserve_prefix_boundaries_and_splice_siblings`
    #[inline]
    #[spec(captures: expected = replacement.clone(), ensures: |output| match output {
        Ok(ref term) => matches!(Self::subterm_cmd_at(term, pos), Maybe::Present(ref found) if found == &expected),
        Err(CommandSpliceRefusal::OffTerm) => matches!(cmd.range_at(&pos.0), Maybe::Absent(command_subterm::Absent::OffTerm)),
        Err(CommandSpliceRefusal::NotACommand) => false,
    })]
    fn splice_cmd_at(
        cmd: &Self::Cmd,
        pos: &Self::Pos,
        replacement: Self::Cmd,
    ) -> Result<Self::Cmd, CommandSpliceRefusal>
    {
        let (start, end) = match cmd.range_at(&pos.0) {
            Maybe::Present(range) => range,
            Maybe::Absent(command_subterm::Absent::OffTerm) => {
                return Err(CommandSpliceRefusal::OffTerm);
            },
            Maybe::Absent(command_subterm::Absent::NotACommand) => {
                return Err(CommandSpliceRefusal::NotACommand);
            },
        };
        let mut nodes: Vec<Head> = Vec::with_capacity(
            cmd.0
                .len()
                .saturating_sub(end.0.saturating_sub(start.0))
                .saturating_add(replacement.0.len()),
        );
        nodes.extend(cmd.0.iter().take(start.0).cloned());
        nodes.extend(replacement.0);
        nodes.extend(cmd.0.iter().skip(end.0).cloned());
        Ok(Term(nodes))
    }

    /// Size guarded by hole domination; a tie or an unlicensed difference is
    /// an obstruction.
    ///
    /// # Specification
    /// - ensures: the larger table wins when it carries every hole of the
    ///   smaller at least as often; every other pair is
    ///   [`core::cmp::Ordering::Equal`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — increasing sizes with adequate, missing or
    ///   insufficient hole counts separate strict order from obstruction; equal
    ///   sizes remain equal. Reversed signs and a skipped guard change the
    ///   verdict.
    /// - witness: `term::tests::metadata_names_and_orders_observe_boundaries`
    #[inline]
    #[spec(ensures: |output| match output {
        core::cmp::Ordering::Greater => lhs.0.len() > rhs.0.len() && dominates(&occurrences(lhs), &occurrences(rhs)) == HoleDomination::Dominates,
        core::cmp::Ordering::Less => lhs.0.len() < rhs.0.len() && dominates(&occurrences(rhs), &occurrences(lhs)) == HoleDomination::Dominates,
        core::cmp::Ordering::Equal => lhs.0.len() == rhs.0.len() || if lhs.0.len() > rhs.0.len() {
            dominates(&occurrences(lhs), &occurrences(rhs)) == HoleDomination::FallsShort
        } else { dominates(&occurrences(rhs), &occurrences(lhs)) == HoleDomination::FallsShort },
    })]
    fn reduction_cmp(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
    ) -> core::cmp::Ordering
    {
        let (left, right) = (occurrences(lhs), occurrences(rhs));
        match lhs.0.len().cmp(&rhs.0.len()) {
            core::cmp::Ordering::Greater
                if dominates(&left, &right) == HoleDomination::Dominates =>
            {
                core::cmp::Ordering::Greater
            },
            core::cmp::Ordering::Less if dominates(&right, &left) == HoleDomination::Dominates => {
                core::cmp::Ordering::Less
            },
            core::cmp::Ordering::Greater
            | core::cmp::Ordering::Less
            | core::cmp::Ordering::Equal => core::cmp::Ordering::Equal,
        }
    }

    /// The renamed faces with each name primed apart from the anchor's.
    ///
    /// # Specification
    /// - ensures: every metavariable of `renamed` replaced by itself primed
    ///   until it is absent from `anchor` and from the other fresh names;
    ///   shapes kept, and a cell already apart returned unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated names, colliding prime chains and
    ///   already-disjoint terms reconstruct exact renamed faces. Splitting a
    ///   shared name, reusing a taken name or changing a constructor changes
    ///   the result.
    /// - witness: `term::tests::metadata_names_and_orders_observe_boundaries`
    #[inline]
    #[spec(ensures: |output| output.0.0.len() == renamed.0.0.len() && output.1.0.len() == renamed.1.0.len()
        && output.0.vars().chain(output.1.vars()).all(|var| anchor.0.vars().chain(anchor.1.vars()).all(|held| held != var)))]
    fn rename_apart(
        anchor: (&Self::Cmd, &Self::Cmd),
        renamed: (&Self::Cmd, &Self::Cmd),
    ) -> (Self::Cmd, Self::Cmd)
    {
        let mut taken: BTreeSet<Name> = anchor.0.vars().chain(anchor.1.vars()).cloned().collect();
        let mut fresh: BTreeMap<Name, Name> = BTreeMap::new();
        for var in renamed.0.vars().chain(renamed.1.vars()) {
            if fresh.contains_key(var) {
                continue;
            }
            let mut name = var.clone();
            while taken.contains(&name) {
                name = Name::from(alloc::format!("{name}'"));
            }
            taken.insert(name.clone());
            fresh.insert(var.clone(), name);
        }
        // Every metavariable of both renamed faces was given a fresh name
        // above, so the fallback to the original name is never taken.
        let relabel =
            |var: &Name| Head::Var(fresh.get(var).cloned().unwrap_or_else(|| var.clone()));
        (renamed.0.relabel(relabel), renamed.1.relabel(relabel))
    }

    /// Every metavariable replaced by its constant.
    ///
    /// # Specification
    /// - ensures: every variable becomes the constant with the same name; all
    ///   other heads and the node count are unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated variables become name-stable constants while
    ///   a ground term is unchanged. Missed grounding, merged names or changed
    ///   constructors alters the exact term.
    /// - witness: `term::tests::metadata_names_and_orders_observe_boundaries`
    #[inline]
    #[spec(ensures: |output| output.vars().next().is_none() && output.0.len() == cmd.0.len()
        && output.0.iter().zip(&cmd.0).all(|(after, before)| match *before { Head::Var(ref var) => matches!(*after, Head::Konst(ref constant) if constant == var), Head::Konst(_) | Head::Ctor(..) | Head::Op(..) | Head::Results(_) => after == before }))]
    fn skolemize(cmd: &Self::Cmd) -> Self::Cmd
    {
        cmd.relabel(|var| Head::Konst(var.clone()))
    }

    /// A metavariable is its own hole.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hole_of(var: &Self::Var) -> Self::Hole
    {
        var.clone()
    }

    /// Positive for the derived provenance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn completion_certificate(provenance: &Self::Provenance) -> CellInvertibility
    {
        CellInvertibility::from(matches!(*provenance, TermProv::Derived))
    }

    /// The distinct metavariables of both faces.
    ///
    /// # Specification
    /// - ensures: one variable per distinct name, in first-occurrence order
    ///   over lhs then rhs, with the supplied invertibility flag.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, repeated and right-only names expose ordered
    ///   unique entries with both invertibility values. Deduplication by the
    ///   wrong key, reordering and a lost flag change the metadata.
    /// - witness: `term::tests::metadata_names_and_orders_observe_boundaries`
    #[inline]
    #[spec(ensures: |output| output.invertible == invertible
        && lhs.vars().chain(rhs.vars()).all(|var| output.vars.iter().filter(|held| *held == var).count() == 1)
        && output.vars.iter().all(|var| lhs.vars().chain(rhs.vars()).any(|held| held == var)))]
    fn derive_meta(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        invertible: CellInvertibility,
    ) -> Self::Meta
    {
        let mut vars: Vec<Name> = Vec::new();
        for var in lhs.vars().chain(rhs.vars()) {
            if !vars.contains(var) {
                vars.push(var.clone());
            }
        }
        TermMeta { vars, invertible }
    }

    /// One forward endpoint for the hole when it occurs: a one-polarity
    /// language has no backward flow.
    ///
    /// # Specification
    /// - ensures: a forward endpoint for each matching metadata variable, and
    ///   no endpoint when the requested hole is absent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — present and absent holes expose one forward endpoint
    ///   or none. Wrong filtering, extra endpoints and a backward role change
    ///   the observation.
    /// - witness: `term::tests::metadata_names_and_orders_observe_boundaries`
    #[inline]
    #[spec(ensures: |output| output.len() == meta.vars.iter().filter(|var| *var == hole).count()
        && output.iter().all(|endpoint| endpoint.0 == *hole && endpoint.1 == SeamRole::Forward))]
    fn hole_flow(
        meta: &Self::Meta,
        hole: &Self::Hole,
    ) -> Vec<(Self::Var, SeamRole)>
    {
        meta.vars
            .iter()
            .filter(|var| *var == hole)
            .map(|var| (var.clone(), SeamRole::Forward))
            .collect()
    }

    /// Every cell fires anywhere.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn may_fire(
        _provenance: &Self::Provenance,
        _target: &Self::Cmd,
    ) -> FiringPermission
    {
        FiringPermission::from(true)
    }

    /// The derived orientation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn derived_orientation() -> Self::Orientation
    {
        TermOrient::Derived
    }

    /// The derived provenance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn derived_provenance() -> Self::Provenance
    {
        TermProv::Derived
    }
}

/// A written face as a cell of the term alphabet: its two sides as terms,
/// oriented as written.
///
/// # Specification
/// - ensures: the cell `Term::from(lhs) ~> Term::from(rhs)`, oriented
///   [`TermOrient::Written`] with provenance [`TermProv::SurfaceRule`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's two cancellations read back as the written
///   faces and fire below the root; swapping a side or the orientation changes
///   the normal forms the presentation's suite observes.
/// - witness: `term::tests::the_circles_rules_fire_below_the_root`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.lhs().read() == Maybe::Present(face.lhs.clone())
    && ret.rhs().read() == Maybe::Present(face.rhs.clone())
    && ret.orient() == TermOrient::Written && ret.provenance() == TermProv::SurfaceRule)]
pub fn face_cell(face: &RuleFace) -> Cell<TermAlphabet>
{
    Cell::new(
        Term::from(&face.lhs),
        Term::from(&face.rhs),
        TermOrient::Written,
        TermProv::SurfaceRule,
    )
}

#[cfg(test)]
mod tests;
