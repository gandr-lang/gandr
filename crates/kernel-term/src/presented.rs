//! A presented type's rules: the constructor-headed rewrite rules a data
//! declaration carries beside its constructor table.
//!
//! # The generative reading
//!
//! A `data` block whose `rule` members rewrite its own constructor terms
//! presents a type: the constructors generate its terms, the rules orient an
//! equational theory on them, and its elements are the normal forms. Two terms
//! of the type convert exactly when their normal forms agree. A rule is part of
//! the type's definition, read by every conversion of its terms, never a step
//! a producer chooses; that is why it travels on the declaration and not in a
//! dialogue. A declaration with no rule is a free type, and its bytes are what
//! they were before rules existed.
//!
//! # Representation
//!
//! A side is a pre-order sequence of [`RuleNode`]s: a constructor tag, whose
//! children are the next subterms its arity in the declaration's constructor
//! table counts, or a pattern variable. Variables are numbered by first
//! occurrence on the left side, so a left side is linear exactly when its
//! variables read `0, 1, 2, …` in order; the kernel checks that, the arities,
//! that every constructor stands where the declaration's own type does, and
//! that the right side reuses each variable at its left side's field type.
//! Flat sequences keep a side free of owning recursion, and its bytes are its
//! nodes in order.
//!
//! **Alternatives.** A side as kernel terms — constructor values over de
//! Bruijn variables in the arena — would carry a classifier at every
//! constructor and an arena context for every variable, where a rule is first
//! order over one constructor table and tags say all of it. **Reversal.** A
//! rule over another type's constructors, or a non-linear left side, needs a
//! classifier per node.
//!
//! # Free cells and their words
//!
//! A `data` block may declare a cell between two closed terms of its sort,
//! `loop : Base <-> Base;`. The cells looping at one point mint a second
//! presented type, the words over them ([`FreeCells`]): the free group on the
//! cells presented as a polygraph, a letter and an inverse per cell as its
//! constructors and the two cancellations per cell as its rules. The words
//! travel as an ordinary presented declaration that also carries its cells, so
//! conversion modulo rules, the respect check and the replay read them as they
//! read any presented type, one stratum up; the cells are what lets the
//! checker and the kernel read `Path[.A = T](a, a)` as the words at `a`, and
//! what the kernel re-mints the table and the rules from. Above dimension one
//! the cells are spherical, so their words commute: both conversions read them
//! as the free abelian group on the cells, by one normal form.
//!
//! **Alternatives.** A primitive word node with its own conversion would
//! duplicate the rewriting presented types already have; the cells on the
//! sort's own declaration would leave the words no admission position of
//! their own. **Reversal.** A cell between distinct terms takes words indexed
//! by their endpoints, a family over pairs of points rather than one type per
//! point.
//!
//! # Convergence and apartness
//!
//! Conversion reads normal forms by one fixed strategy, sound whether or not
//! the rules are confluent. Telling two terms apart is the converse claim and
//! needs more: [`Presentation::converges`] joins every critical pair, so with
//! the termination admission establishes, each term has one normal form, and
//! [`Presentation::apart`] then separates two terms whose normal forms, holding
//! no unknown subterm of the type, first differ at two distinct constructors.
//! A free type has no rule to rewrite a leaf, so it separates two terms whose
//! first difference is two distinct constructors whatever leaves they hold.
//! Both checkers call the one decision with the same fuel, each reading its
//! own arena through a [`TermReading`] callback, so they refuse alike.
//!
//! **Alternatives.** Joining the critical pairs once at admission, which would
//! put the cost on every presented type rather than on each use of apartness.
//! **Reversal.** A presented type cased absurdly often enough that the joins
//! show in profiles caches the verdict on the admitted declaration.
//!
//! # References
//!
//! - `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — anchor: the presented type
//!   and its loop space as normal forms. Above dimension one the words of the
//!   spherical cells at a point are abelian, so [`Presentation::normalize`]
//!   sorts and counts them.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: the rules of a
//!   presented type give each term one normal form. A symmetry
//!   ([`RuleReading::Symmetry`]) is a rule that no reader rewrites by.

use alloc::alloc::Global;
use alloc::boxed::Box;

use anodized::spec;
use gandr_kernel_data::Count;
use gandr_kernel_data::Shared;
use gandr_kernel_data::SmallVec;
use gandr_kernel_data::ThinShared;

use crate::term::ConstructorTag;

/// A rule's pattern variable, numbered by its first occurrence in the left
/// side's pre-order.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RuleVariable(u32);

impl From<u32> for RuleVariable
{
    /// The variable at `ordinal`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(ordinal: u32) -> Self
    {
        Self(ordinal)
    }
}

impl From<RuleVariable> for u32
{
    /// The variable's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(variable: RuleVariable) -> Self
    {
        variable.0
    }
}

/// How many pattern variables a rule binds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct VariableCount(u32);

impl From<VariableCount> for u32
{
    /// The count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: VariableCount) -> Self
    {
        count.0
    }
}

/// One node of a rule side, in pre-order.
///
/// # Specification
/// - provides: a constructor of the declaration's own table, whose children
///   follow it, or a pattern variable.
/// - panics: none.
/// - executable: none — data declaration; arity and typing are the kernel's
///   admission obligations.
///
/// # Adequacy
/// - hypothesis: L3 — a presented declaration round-trips through the wire with
///   every node of both sides in order.
/// - witness: `encode::tests::a_presented_data_declaration_closes_its_segment_with_its_rules`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RuleNode
{
    /// A constructor of the declaration's own table, applied to the next
    /// subterms its arity counts.
    Constructor(ConstructorTag),
    /// A pattern variable.
    Variable(RuleVariable),
}

/// One oriented rule `left ==> right` over a declaration's constructors.
///
/// # Specification
/// - provides: the producer's two sides, unchecked; admission owns their
///   well-formedness.
/// - panics: none.
/// - executable: none — data declaration; the kernel's admission checks the
///   sides against the constructor table.
///
/// # Adequacy
/// - hypothesis: L3 — as [`RuleNode`].
/// - witness: `encode::tests::a_presented_data_declaration_closes_its_segment_with_its_rules`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct PresentedRule
{
    /// The left side, in pre-order: the redex pattern.
    left: Box<[RuleNode]>,
    /// The right side, in pre-order: the contractum.
    right: Box<[RuleNode]>,
}

/// How the readers of a rule table read one rule.
///
/// # Specification
/// - provides: the two readings of [`PresentedRule::reading`].
/// - panics: none.
/// - executable: none — closed classification.
///
/// # Adequacy
/// - hypothesis: L3 — as [`PresentedRule::reading`].
/// - witness: `presented::tests::a_rule_that_swaps_two_fields_is_a_symmetry`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RuleReading
{
    /// The rule rewrites its left side to its right side.
    Step,
    /// The rule swaps the two fields of this constructor. No reader rewrites
    /// by it.
    Symmetry(ConstructorTag),
}

impl PresentedRule
{
    /// The rule rewriting `left` to `right`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        left: Box<[RuleNode]>,
        right: Box<[RuleNode]>,
    ) -> Self
    {
        Self { left, right }
    }

    /// The left side, in pre-order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn left(&self) -> &[RuleNode]
    {
        &self.left
    }

    /// The right side, in pre-order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn right(&self) -> &[RuleNode]
    {
        &self.right
    }

    /// How many pattern variables the rule binds: its left side's variable
    /// nodes, each written once.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the number of [`RuleNode::Variable`] nodes on the left side,
    ///   saturating at the ordinal ceiling.
    /// - provides: how many fresh binders the rule's sides stand under when
    ///   they are built as terms. A rule [`Presentation::validate`] admits
    ///   numbers its left side's variables `0, 1, 2, …` and reuses only those
    ///   on its right, so every ordinal on either side lies below the count.
    ///   The clause checks the count against the side's length; the exact count
    ///   is the witness's, since a clause may not walk the receiver.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a cancellation over one variable binds one, a rule
    ///   between ground words binds none.
    /// - witness: `presented::tests::a_rule_side_builds_bottom_up_over_its_variables`
    #[spec(ensures: |ret| usize::try_from(ret.0).is_ok_and(|count| count <= self.left.len()))]
    #[inline]
    #[must_use]
    pub fn variables(&self) -> VariableCount
    {
        let count = self
            .left
            .iter()
            .filter(|node| matches!(node, RuleNode::Variable(_)))
            .count();
        VariableCount(u32::try_from(count).unwrap_or(u32::MAX))
    }

    /// Where each of the left side's variables stands, in variable order: the
    /// declaration's own type or the classifier of the field it fills, as
    /// `table` lists them.
    ///
    /// # Specification
    /// - requires: nothing — the side may be unvalidated.
    /// - ensures: `Ok` with one slot per variable node of the left side, in
    ///   pre-order, exactly when the side is one term by `table`'s arities with
    ///   every constructor at the own type; for a rule
    ///   [`Presentation::validate`] admits, pre-order is variable order.
    /// - provides: what a fold instantiates a law at: the fold of a variable
    ///   standing at the own type, the variable itself anywhere else.
    /// - fails: as [`Presentation::validate`] reading the left side:
    ///   [`RuleFault::UnknownConstructor`], [`RuleFault::NotOwnPosition`] or
    ///   [`RuleFault::Arity`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Cost
    /// - allocation: the slots of the left side's variables, growth within the
    ///   left side's nodes
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's cancellation reads its one variable at
    ///   the own type, and a constructor with a field of another type reads its
    ///   variable at that classifier.
    /// - witness: `presented::tests::a_rule_side_builds_bottom_up_over_its_variables`
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|slots| slots.len() <= self.left.len())
        || matches!(ret, Err(RuleFault::UnknownConstructor | RuleFault::NotOwnPosition | RuleFault::Arity)))]
    #[inline]
    pub fn slots<T>(
        &self,
        table: &[SmallVec<RuleSlot<T>, 0, Global>],
    ) -> Result<SmallVec<RuleSlot<T>, 0, Global>, RuleFault>
    where
        T: Copy + Eq,
    {
        read_side(&self.left, table).map(|reading| {
            reading
                .variables
                .into_iter()
                .map(|(_, slot)| slot)
                .collect()
        })
    }

    /// How the readers of the table read this rule: as a step, or as a
    /// symmetry of one constructor.
    ///
    /// # Specification
    /// - requires: nothing — the rule may be unvalidated.
    /// - ensures: [`RuleReading::Symmetry`] with the constructor exactly when
    ///   the left side is that constructor over the variables `0` and `1` and
    ///   the right side is it over `1` and `0`; [`RuleReading::Step`] for every
    ///   other rule.
    /// - provides: the one test of the form [`Presentation::validate`],
    ///   [`Presentation::normalize`] and [`Presentation::converges`] share. A
    ///   symmetry states that its constructor's two fields commute. No reader
    ///   rewrites by it, so the constructor count that bounds the rewriting of
    ///   the steps still falls at each rewrite.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `[c, 0, 1] ==> [c, 1, 0]` is a symmetry of `c`; the
    ///   same sides over two constructors, over one variable twice, or with the
    ///   right side in the written order are steps.
    /// - witness: `presented::tests::a_rule_that_swaps_two_fields_is_a_symmetry`
    #[spec(ensures: |ret| match ret {
        RuleReading::Symmetry(tag) => self.left.first() == Some(&RuleNode::Constructor(tag)),
        RuleReading::Step => true,
    })]
    #[inline]
    #[must_use]
    pub fn reading(&self) -> RuleReading
    {
        let (first, second) = (
            RuleNode::Variable(RuleVariable(0)),
            RuleNode::Variable(RuleVariable(1)),
        );
        match (&*self.left, &*self.right) {
            (
                &[RuleNode::Constructor(tag), left_first, left_second],
                &[head, right_first, right_second],
            ) if head == RuleNode::Constructor(tag)
                && left_first == first
                && left_second == second
                && right_first == second
                && right_second == first =>
            {
                RuleReading::Symmetry(tag)
            },
            _ => RuleReading::Step,
        }
    }
}

/// A declaration's rules, in the order the producer wrote them, shared, and
/// for a type of words the free cells it is minted over.
///
/// Empty for a free type and for every declaration that is not a data
/// declaration.
///
/// # Specification
/// - provides: the rule table one presented type reads, cheap to clone into
///   every conversion that needs it.
/// - panics: none.
/// - executable: none — data declaration.
///
/// # Adequacy
/// - hypothesis: L3 — as [`RuleNode`].
/// - witness: `encode::tests::a_presented_data_declaration_closes_its_segment_with_its_rules`
/// - witness: `encode::tests::a_type_of_words_closes_its_segment_with_its_cells`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Presentation
{
    /// The rules, in written order.
    rules: ThinShared<(), PresentedRule, Global>,
    /// The free cells a type of words is minted over; absent for every other
    /// presentation.
    cells: Option<Shared<FreeCells, Global>>,
}

impl Presentation
{
    /// The presentation of `rules`, in written order; the free presentation
    /// when it is empty.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the shared list of the presentation's rules, growth within
    ///   the given rules
    #[inline]
    #[must_use]
    pub fn new(rules: SmallVec<PresentedRule, 0, Global>) -> Self
    {
        Self {
            rules: ThinShared::from_header_and_iter((), rules),
            cells: None,
        }
    }

    /// The type of words over `cells`: the presentation the lowering mints,
    /// whose rules are the two cancellations of every cell.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the rules are [`FreeCells::cancellations`] of `cells`, in
    ///   order, and the cells are `cells`.
    /// - provides: the one way a producer states a type of words, so the
    ///   kernel's comparison with the mint is against this very function.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the shared rules of the two cancellations of every cell,
    ///   and the shared cells, growth within the cells
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's one cell mints its two cancellations.
    /// - witness: `presented::tests::a_cell_mints_its_words_and_its_cancellations`
    #[spec(captures: count = cells.cells().len(), ensures: |ret| ret.rules().len() == count.saturating_mul(2))]
    #[inline]
    #[must_use]
    pub fn words(cells: FreeCells) -> Self
    {
        Self {
            rules: ThinShared::from_header_and_iter((), cells.cancellations()),
            cells: Some(Shared::new(cells)),
        }
    }

    /// This presentation carrying `cells`, its rules as they were: a decoded
    /// type of words, whose rules the kernel compares with the mint.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the shared handle on the carried cells, setup
    #[inline]
    #[must_use]
    pub fn carrying(
        self,
        cells: FreeCells,
    ) -> Self
    {
        Self {
            cells: Some(Shared::new(cells)),
            ..self
        }
    }

    /// The rules, in written order: none for a free type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rules(&self) -> &[PresentedRule]
    {
        &self.rules
    }

    /// The free cells a type of words is minted over; none for every other
    /// presentation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cells(&self) -> Option<&FreeCells>
    {
        self.cells.as_deref()
    }

    /// Check every rule against the constructor table it presents, in written
    /// order, stopping at the first that does not present the type.
    ///
    /// `table` lists each constructor's fields, in tag order, as the slots a
    /// side reads: [`RuleSlot::Own`] where the declaration's own type stands,
    /// [`RuleSlot::Dependent`] where an open classifier stands after the
    /// constructor's first field, [`RuleSlot::Other`] with the field's
    /// classifier anywhere else.
    ///
    /// # Specification
    /// - requires: nothing — a rule may be arbitrary producer bytes.
    /// - ensures: `Ok(())` exactly when every rule's left side is headed by a
    ///   constructor, each side's constructors exist in `table` and consume
    ///   exactly the side's nodes by their arities, every constructor stands at
    ///   the root or at an [`RuleSlot::Own`] field, no variable stands at a
    ///   [`RuleSlot::Dependent`] one, the left side's variables read in
    ///   pre-order as `0, 1, 2, …`, every right-side variable occurs on the
    ///   left at the same slot and at most once on the right, and the right
    ///   side holds fewer constructors than the left. Otherwise the first
    ///   failing rule and its first fault.
    /// - provides: the admission check the kernel and the checker share, and
    ///   with it termination of [`Self::normalize`]: a linear, non-duplicating
    ///   rule with fewer constructors on its right removes at least one
    ///   constructor from any term it rewrites, so a term of `n` constructors
    ///   admits at most `n` rewrites.
    /// - fails: [`RuleRefusal`] naming the rule and its [`RuleFault`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Cost
    /// - allocation: the binding table and use mask of each rule's variables,
    ///   growth within the rule's sides
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's two rules pass, and one rule per fault
    ///   is refused by that fault and no other.
    /// - witness: `presented::tests::validation_names_each_fault`
    #[spec(ensures: |ret| ret.as_ref().err().is_none_or(|refusal| usize::from(refusal.rule) < self.rules().len()))]
    #[inline]
    pub fn validate<T>(
        &self,
        table: &[SmallVec<RuleSlot<T>, 0, Global>],
    ) -> Result<(), RuleRefusal>
    where
        T: Copy + Eq,
    {
        // One binding table and one use mask, refilled per rule.
        let (mut bound, mut used): (SmallVec<RuleSlot<T>, 0, Global>, SmallVec<bool, 0, Global>) = (
            SmallVec::<_, 0, Global>::new(),
            SmallVec::<_, 0, Global>::new(),
        );
        for (index, rule) in self.rules().iter().enumerate() {
            let refuse = |fault| RuleRefusal {
                rule: RuleIndex(index),
                fault,
            };
            if !matches!(rule.left().first(), Some(&RuleNode::Constructor(_))) {
                return Err(refuse(RuleFault::VariableHeaded));
            }
            let left = read_side(rule.left(), table).map_err(refuse)?;
            bound.clear();
            for &(variable, slot) in &left.variables {
                if usize::try_from(u32::from(variable)).ok() != Some(bound.len()) {
                    return Err(refuse(RuleFault::NonLinear));
                }
                bound.push(slot);
            }
            let right = read_side(rule.right(), table).map_err(refuse)?;
            used.clear();
            used.resize(Count::from(bound.len()), false);
            for &(variable, slot) in &right.variables {
                let ordinal = usize::try_from(u32::from(variable)).unwrap_or(usize::MAX);
                let (Some(&written), Some(seen)) = (bound.get(ordinal), used.get_mut(ordinal))
                else {
                    return Err(refuse(RuleFault::Unbound));
                };
                if *seen {
                    return Err(refuse(RuleFault::Duplicated));
                }
                *seen = true;
                if written != slot {
                    return Err(refuse(RuleFault::SlotMismatch));
                }
            }
            if right.constructors >= left.constructors
                && !matches!(rule.reading(), RuleReading::Symmetry(_))
            {
                return Err(refuse(RuleFault::NotDecreasing));
            }
        }
        Ok(())
    }

    /// Rewrite `term` to its normal form under these rules.
    ///
    /// `term` is a constructor term flattened in pre-order: a constructor
    /// node's children are the next subterms its arity counts, and a leaf is
    /// whatever the caller does not rewrite through — a variable, a neutral, a
    /// field of another type. A node a rewrite builds carries the payload
    /// `fresh` makes of the redex root's.
    ///
    /// # The strategy
    ///
    /// The redex rewritten next is the innermost one starting last in
    /// pre-order, and at one position the first rule in written order fires.
    /// The kernel and the checker both rewrite here, so they reach one normal
    /// form even for rules that are not confluent; for confluent rules every
    /// strategy reaches it. After a rewrite at `p` only the nodes it built and
    /// the positions before `p` can hold a new redex — every position after
    /// the rewritten span was found normal and is unchanged, and a variable's
    /// subterm is copied normal — so the scan resumes at the end of what the
    /// rewrite built.
    ///
    /// A type of words takes that strategy in one pass ([`Self::cancelled`]):
    /// each rule cancels two letters, and a word is one chain of letters, so
    /// the redex at a letter is that letter and the first letter of the
    /// normal suffix after it. Over cells above dimension one the words are
    /// abelian, and the pass also sorts the letters by their cells
    /// ([`Self::counted`]): no rule commutes two letters, so that normal form
    /// is one the rules alone do not reach.
    ///
    /// # Specification
    /// - requires: `self` passed [`Self::validate`] against the table `arities`
    ///   counts; `term` is one well-formed pre-order term.
    /// - ensures: [`Normalized::Unchanged`] with `term` untouched when no rule
    ///   matches anywhere; otherwise [`Normalized::Rewritten`] with `term`
    ///   rewritten until no rule matches at any position. A rule matches in
    ///   each order of the two fields of a constructor that a symmetry
    ///   ([`RuleReading::Symmetry`]) of the table names, at each such node of
    ///   its left side, and no rewrite is by a symmetry. A word of cells above
    ///   dimension one is also unchanged only when its letters stand in the
    ///   order of their cells, and is otherwise rewritten to that order. Each
    ///   node compared or copied costs one unit of `fuel`; in the pass over a
    ///   word, each letter costs one.
    /// - provides: the normal form both conversions compare a presented type's
    ///   terms by.
    /// - fails: [`Exhausted`] when `fuel` runs out first; `term` then holds
    ///   some intermediate term of the rewriting.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a circle word with nested inverse pairs normalizes to
    ///   its reduced word, a reduced word comes back unchanged, a leaf standing
    ///   for a variable is carried through a rewrite, and a starved fuel is
    ///   exhausted. Over a type of words over loops, the pass and the rewriting
    ///   give one term and one outcome for every word of up to six letters over
    ///   two loops. Over cells above dimension one, two words that differ by
    ///   the order of their letters give one normal form.
    /// - witness: `presented::tests::normalization_reduces_circle_words`
    /// - witness: `presented::tests::the_pass_over_a_word_rewrites_as_the_rules_do`
    /// - witness: `presented::tests::a_word_of_cells_above_dimension_one_sorts_and_counts_its_letters_6740`
    /// - witness: `presented::tests::a_left_side_matches_in_each_order_under_a_symmetry_8299`
    #[spec(captures: before = fuel.0, ensures: |ret| fuel.0 <= before
        && (!matches!(ret, Err(Exhausted)) || fuel.0 == 0))]
    #[inline]
    pub fn normalize<C, L, F>(
        &self,
        arities: &[FieldCount],
        term: &mut SmallVec<RuleTerm<C, L>, 0, Global>,
        fresh: F,
        fuel: &mut RewriteFuel,
    ) -> Result<Normalized, Exhausted>
    where
        C: Copy,
        L: Copy,
        F: Fn(&C) -> C,
    {
        if let Some(outcome) = self.cancelled(term, fuel)? {
            return Ok(outcome);
        }
        self.rewritten(arities, term, fresh, fuel)
    }

    /// Rewrite `term` to its normal form by the strategy [`Self::normalize`]
    /// states, one redex at a time.
    ///
    /// # Specification
    /// - requires: as [`Self::normalize`].
    /// - ensures: as [`Self::normalize`], each node compared or copied costing
    ///   one unit of `fuel`.
    /// - fails: as [`Self::normalize`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: the outer `loop`, which rewrites once per turn, and the scans
    ///   and copies inside it, each over a finite slice.
    /// - measure: the term's constructor count, which every rewrite of a
    ///   validated presentation lowers; and `fuel`, which every node charges.
    ///
    /// # Cost
    /// - allocation: the built right side of each rewrite, the rewritten term,
    ///   the constructors under a symmetry and each order of a left side that
    ///   the match tries, growth within the rule's sides and the term's nodes
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::normalize`].
    /// - witness: `presented::tests::normalization_reduces_circle_words`
    #[spec(captures: before = fuel.0, ensures: |ret| fuel.0 <= before
        && (!matches!(ret, Err(Exhausted)) || fuel.0 == 0))]
    fn rewritten<C, L, F>(
        &self,
        arities: &[FieldCount],
        term: &mut SmallVec<RuleTerm<C, L>, 0, Global>,
        fresh: F,
        fuel: &mut RewriteFuel,
    ) -> Result<Normalized, Exhausted>
    where
        C: Copy,
        L: Copy,
        F: Fn(&C) -> C,
    {
        let symmetric: SmallVec<ConstructorTag, 0, Global> = self
            .rules()
            .iter()
            .filter_map(|rule| match rule.reading() {
                RuleReading::Symmetry(tag) => Some(tag),
                RuleReading::Step => None,
            })
            .collect();
        let mut outcome = Normalized::Unchanged;
        let mut cursor = term.len();
        'rewrite: loop {
            while let Some(start) = cursor.checked_sub(1) {
                cursor = start;
                let Some(&RuleTerm::Constructor { payload, .. }) = term.get(start)
                else {
                    continue;
                };
                for rule in self.rules() {
                    if matches!(rule.reading(), RuleReading::Symmetry(_)) {
                        continue;
                    }
                    let Matched::At { end, bindings } = matched_under(
                        &symmetric,
                        term,
                        TermPosition(start),
                        rule.left(),
                        arities,
                        fuel,
                    )?
                    else {
                        continue;
                    };
                    let mut built = SmallVec::<_, 0, Global>::new();
                    for &node in rule.right() {
                        fuel.charge()?;
                        match node {
                            RuleNode::Constructor(tag) => built.push(RuleTerm::Constructor {
                                tag,
                                arity: arities.get(usize::from(tag)).copied().unwrap_or_default(),
                                payload: fresh(&payload),
                            }),
                            RuleNode::Variable(variable) => {
                                let ordinal =
                                    usize::try_from(u32::from(variable)).unwrap_or(usize::MAX);
                                let Some(&(from, to)) = bindings.get(ordinal)
                                else {
                                    continue;
                                };
                                for copied in term.get(from .. to).unwrap_or(&[]) {
                                    fuel.charge()?;
                                    built.push(*copied);
                                }
                            },
                        }
                    }
                    cursor = start.saturating_add(built.len());
                    term.replace_range(start .. end, built);
                    outcome = Normalized::Rewritten;
                    continue 'rewrite;
                }
            }
            return Ok(outcome);
        }
    }

    /// The normal form of a word in one pass, when this presentation is a
    /// type of words whose every rule cancels two letters.
    ///
    /// Over loops, the pass reads from the last letter and keeps the normal
    /// suffix as a stack, its first letter on top. Each letter, read from the
    /// last to the first, cancels with the top when a rule's left side is the
    /// two letters over a variable, and goes on top otherwise.
    /// [`Self::rewritten`] rewrites in that order: its next redex starts last,
    /// and the suffix after it is normal. So the pass removes the pairs that
    /// the rewriting removes, and keeps each other letter as written.
    ///
    /// Over cells above dimension one, the words are abelian, and the pass is
    /// [`Self::counted`].
    ///
    /// # Specification
    /// - requires: `self` passed [`Self::validate`] against the arities that
    ///   the nodes of `term` carry.
    /// - ensures: `Ok(None)` with `term` untouched unless `self` carries cells,
    ///   each rule is `[a, b, x] ==> [x]` over two constructors and a variable,
    ///   and `term` is letters of one field each over a last node of no field
    ///   or a leaf. Otherwise, over cells above dimension one, the outcome of
    ///   [`Self::counted`]. Over loops, [`Normalized::Unchanged`] with `term`
    ///   untouched when no two neighbouring letters cancel, and
    ///   [`Normalized::Rewritten`] with `term` the letters that no pair
    ///   removes, in order, over the last node: the term and the outcome
    ///   [`Self::rewritten`] gives. Each letter costs one unit of `fuel`.
    /// - fails: [`Exhausted`] when `fuel` runs out first; `term` is then
    ///   untouched.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: one `for` loop over the letters, from the last to the first.
    /// - measure: the letters still to read.
    ///
    /// # Cost
    /// - allocation: the stack of kept positions and the normal word, growth
    ///   within the term's letters
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::normalize`]: every word of up to six
    ///   letters over two loops, over a leaf or the empty word, gives the
    ///   rewriting's term and outcome; a presentation without cells is left to
    ///   the rewriting.
    /// - witness: `presented::tests::the_pass_over_a_word_rewrites_as_the_rules_do`
    /// - witness: `presented::tests::a_word_of_cells_above_dimension_one_sorts_and_counts_its_letters_6740`
    #[spec(captures: before = fuel.0, ensures: |ret| fuel.0 <= before
        && (!matches!(ret, Err(Exhausted)) || fuel.0 == 0))]
    fn cancelled<C, L>(
        &self,
        term: &mut SmallVec<RuleTerm<C, L>, 0, Global>,
        fuel: &mut RewriteFuel,
    ) -> Result<Option<Normalized>, Exhausted>
    where
        C: Copy,
        L: Copy,
    {
        let one = FieldCount::from(1_usize);
        let pair = |rule: &PresentedRule| match (rule.left(), rule.right()) {
            (
                &[
                    RuleNode::Constructor(first),
                    RuleNode::Constructor(second),
                    RuleNode::Variable(rest),
                ],
                &[RuleNode::Variable(kept)],
            ) if rest == kept => Some((first, second)),
            _ => None,
        };
        if self.cells.is_none() || !self.rules().iter().all(|rule| pair(rule).is_some()) {
            return Ok(None);
        }
        let Some((&last, letters)) = term.split_last()
        else {
            return Ok(None);
        };
        let ends = match last {
            RuleTerm::Leaf(_) => true,
            RuleTerm::Constructor { arity, .. } => arity == FieldCount::default(),
        };
        let tag_at = |at: usize| match letters.get(at) {
            Some(&RuleTerm::Constructor { tag, arity, .. }) if arity == one => Some(tag),
            _ => None,
        };
        if !ends || (0 .. letters.len()).any(|at| tag_at(at).is_none()) {
            return Ok(None);
        }
        if self
            .cells()
            .is_some_and(|cells| cells.reflexivities() != Reflexivities::NONE)
        {
            return Self::counted(term, fuel).map(Some);
        }
        let cancels = |first, second| {
            self.rules()
                .iter()
                .any(|rule| pair(rule) == Some((first, second)))
        };
        // The positions of the normal suffix, its first letter last.
        let mut kept: SmallVec<usize, 0, Global> =
            SmallVec::<_, 0, Global>::with_capacity(Count::from(letters.len()));
        for at in (0 .. letters.len()).rev() {
            fuel.charge()?;
            let matched = match (tag_at(at), kept.last().and_then(|&top| tag_at(top))) {
                (Some(first), Some(second)) => cancels(first, second),
                _ => false,
            };
            if matched {
                let _cancelled = kept.pop();
            }
            else {
                kept.push(at);
            }
        }
        if kept.len() == letters.len() {
            return Ok(Some(Normalized::Unchanged));
        }
        let mut normal: SmallVec<RuleTerm<C, L>, 0, Global> =
            SmallVec::<_, 0, Global>::with_capacity(Count::from(kept.len().saturating_add(1)));
        normal.extend(kept.iter().rev().filter_map(|&at| letters.get(at).copied()));
        normal.push(last);
        *term = normal;
        Ok(Some(Normalized::Rewritten))
    }

    /// The normal form of a word of cells above dimension one: its letters
    /// sorted by their cells, and each cell's letters and inverses cancelling
    /// at any distance.
    ///
    /// A cell above dimension one is spherical, and a spherical cell is
    /// central. The Peiffer identity gives `∂c ⋆ c' = c · c' · c⁻¹`, and `∂c`
    /// is empty. So any two letters commute, and the words are the free
    /// abelian group on the cells. Its normal form is a sum: the cells in
    /// order, each written as often as its count, as a letter or an inverse
    /// by the count's sign. Within a cell, the pass keeps the first letters of
    /// the count's sign, in written order.
    ///
    /// # Specification
    /// - requires: `term` is letters of one field each, every letter a letter
    ///   or an inverse of a cell, over a last node of no field or a leaf.
    /// - ensures: [`Normalized::Unchanged`] with `term` untouched when its
    ///   letters stand in the order of their cells, with one sign for each
    ///   cell. Otherwise [`Normalized::Rewritten`] with `term` that normal form
    ///   over the last node. Each letter costs one unit of `fuel`.
    /// - fails: [`Exhausted`] when `fuel` runs out first; `term` is then
    ///   untouched.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: one charge per letter, one stable sort and one walk of the
    ///   sorted letters, each over a finite slice.
    /// - measure: the letters still to read.
    ///
    /// # Cost
    /// - allocation: the sorted order of the letters and the counted word,
    ///   growth within the term's letters
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two words of two cells that differ by the order of
    ///   their letters give one normal form; two that differ by a count give
    ///   two; a letter cancels its inverse at any distance; a normal word comes
    ///   back unchanged.
    /// - witness: `presented::tests::a_word_of_cells_above_dimension_one_sorts_and_counts_its_letters_6740`
    #[spec(captures: before = fuel.0, ensures: |ret| fuel.0 <= before
        && (!matches!(ret, Err(Exhausted)) || fuel.0 == 0))]
    fn counted<C, L>(
        term: &mut SmallVec<RuleTerm<C, L>, 0, Global>,
        fuel: &mut RewriteFuel,
    ) -> Result<Normalized, Exhausted>
    where
        C: Copy,
        L: Copy,
    {
        let Some((&last, letters)) = term.split_last()
        else {
            return Ok(Normalized::Unchanged);
        };
        let tag_at = |at: usize| match letters.get(at) {
            Some(&RuleTerm::Constructor { tag, .. }) => Some(tag),
            Some(&RuleTerm::Leaf(_)) | None => None,
        };
        let cell_at = |at: usize| tag_at(at).and_then(FreeCells::generator);
        for _letter in letters {
            fuel.charge()?;
        }
        let normal = (1 .. letters.len()).all(|after| {
            let before = after.saturating_sub(1);
            tag_at(before) == tag_at(after) || cell_at(before) < cell_at(after)
        });
        if normal {
            return Ok(Normalized::Unchanged);
        }
        let mut order: SmallVec<usize, 0, Global> = (0 .. letters.len()).collect();
        order.sort_by_key(|&at| cell_at(at));
        let mut counted: SmallVec<RuleTerm<C, L>, 0, Global> =
            SmallVec::<_, 0, Global>::with_capacity(Count::from(term.len()));
        for group in order.chunk_by(|&first, &second| cell_at(first) == cell_at(second)) {
            let Some(cell) = group.first().and_then(|&at| cell_at(at))
            else {
                continue;
            };
            let letter = FreeCells::letter(cell);
            let letters_of = group
                .iter()
                .filter(|&&at| tag_at(at) == Some(letter))
                .count();
            let inverses_of = group.len().saturating_sub(letters_of);
            let sign = if letters_of >= inverses_of {
                letter
            }
            else {
                FreeCells::inverse(cell)
            };
            counted.extend(
                group
                    .iter()
                    .filter(|&&at| tag_at(at) == Some(sign))
                    .take(letters_of.abs_diff(inverses_of))
                    .filter_map(|&at| letters.get(at).copied()),
            );
        }
        counted.push(last);
        *term = counted;
        Ok(Normalized::Rewritten)
    }

    /// Decide whether these rules give every term one normal form, by joining
    /// every critical pair.
    ///
    /// A critical pair is where two rules overlap: the left side of `inner`
    /// unifies with the subterm of `outer`'s left side at a constructor
    /// position, the root excepted when the two rules are one. Rewriting the
    /// overlap by `outer` at its root and by `inner` at that position gives
    /// the pair's two sides, each normalized by [`Self::normalize`]. Both left
    /// sides are linear and their variables are kept apart, so unification is
    /// one walk of the two sides that fails only where two constructors
    /// differ.
    ///
    /// # Specification
    /// - requires: `self` passed [`Self::validate`] against the table `arities`
    ///   counts.
    /// - ensures: [`Convergence::Diverges`] naming the first symmetry
    ///   ([`RuleReading::Symmetry`]) as both rules, when the table holds one:
    ///   its two orders are two normal forms, because no reader rewrites by it.
    ///   Otherwise [`Convergence::Converges`] exactly when every critical
    ///   pair's two sides normalize to one term; otherwise
    ///   [`Convergence::Diverges`] naming the first pair that does not, in
    ///   written order of the overlapped rule, the position and the overlapping
    ///   rule. Each node unified, built, compared or copied costs one unit of
    ///   `fuel`.
    /// - provides: the convergence a decision over normal forms rests on: an
    ///   admitted presentation terminates, so joining every critical pair makes
    ///   it confluent (the critical pair lemma with Newman's lemma), and two
    ///   terms are then equal exactly when their normal forms are.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// - reason: three `for` loops over the finite rules and the overlapped
    ///   rule's left side, each pair built by bounded walks and normalized by
    ///   [`Self::normalize`], which terminates.
    /// - measure: the (rule, position, rule) triples left; `fuel`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's two cancellations and the integers'
    ///   converge; two rules rewriting one redex to two normal forms diverge,
    ///   named in order; a rule overlapping itself below its root is checked; a
    ///   table that holds a symmetry diverges at the symmetry.
    /// - witness: `presented::tests::critical_pairs_decide_convergence`
    /// - witness: `presented::tests::a_rule_that_swaps_two_fields_is_a_symmetry`
    #[spec(captures: before = fuel.0, ensures: |ret| fuel.0 <= before
        && match ret {
            Ok(Convergence::Diverges { outer, inner }) => outer.0 < self.rules().len() && inner.0 < self.rules().len(),
            Ok(Convergence::Converges) => true,
            Err(Exhausted) => fuel.0 == 0,
        })]
    #[inline]
    pub fn converges(
        &self,
        arities: &[FieldCount],
        fuel: &mut RewriteFuel,
    ) -> Result<Convergence, Exhausted>
    {
        if let Some(symmetry) = self
            .rules()
            .iter()
            .position(|rule| matches!(rule.reading(), RuleReading::Symmetry(_)))
        {
            return Ok(Convergence::Diverges {
                outer: RuleIndex(symmetry),
                inner: RuleIndex(symmetry),
            });
        }
        for (outer_index, outer) in self.rules().iter().enumerate() {
            for (position, &node) in outer.left().iter().enumerate() {
                if !matches!(node, RuleNode::Constructor(_)) {
                    continue;
                }
                for (inner_index, inner) in self.rules().iter().enumerate() {
                    if position == 0 && inner_index == outer_index {
                        continue;
                    }
                    let Overlap::Pair {
                        outer: mut by_outer,
                        inner: mut by_inner,
                    } = overlap((outer, TermPosition(position)), inner, arities, fuel)?
                    else {
                        continue;
                    };
                    let _outer = self.normalize(arities, &mut by_outer, |&()| (), fuel)?;
                    let _inner = self.normalize(arities, &mut by_inner, |&()| (), fuel)?;
                    if by_outer != by_inner {
                        return Ok(Convergence::Diverges {
                            outer: RuleIndex(outer_index),
                            inner: RuleIndex(inner_index),
                        });
                    }
                }
            }
        }
        Ok(Convergence::Converges)
    }

    /// Decide whether two terms of the presented type are apart: no path at
    /// the type joins them.
    ///
    /// `table` is the type's constructor table as [`Self::validate`] reads it;
    /// `read` reads one node of a term where the type stands: a constructor of
    /// the type, its fields appended in order to the vector it is handed; a
    /// reference whose definition is a closed term, unfolded; anything else, a
    /// leaf, two leaves equal exactly when their ids are. Read side by side in
    /// pre-order, every node before the first difference agrees, so the two
    /// nodes there stand at one position of both terms. Two constructors with
    /// distinct tags at that position make the terms apart: no path joins two
    /// terms whose subterms at one position have distinct heads. A presented
    /// type asks first that the rules converge and that the normal forms hold
    /// no subterm of the type that is not a constructor, since a rule may
    /// rewrite such a subterm into the other term. A free type has no rule to
    /// rewrite by, so its terms may hold any leaves: the decision is the
    /// unifier's conflict rule, disjointness under injectivity.
    ///
    /// # Specification
    /// - requires: `self` passed [`Self::validate`] against `table`; `read`
    ///   reads the terms as well-typed by `table`.
    /// - ensures: [`Apartness::Diverges`] when the rules do not converge, as
    ///   [`Self::converges`] names them; else both terms flattened in pre-order
    ///   — where the type's own family stands, a constructor a node and a
    ///   definition its body, and elsewhere every subterm a leaf — and
    ///   normalized. A presented type is [`Apartness::Open`] when either normal
    ///   form holds a leaf where the type's own family stands, the root
    ///   included. Otherwise, read in pre-order side by side,
    ///   [`Apartness::Apart`] when the first nodes to differ are two
    ///   constructors; when they are anything else, [`Apartness::Open`] if a
    ///   term holds a leaf where the family stands and [`Apartness::Leaf`] if
    ///   not; and [`Apartness::Agree`] when no node differs.
    ///   [`Apartness::Undecided`] when the decision's fuel runs out first: one
    ///   unit per node read, rewritten, compared or copied, the same fuel at
    ///   every caller, so two checkers decide alike.
    /// - provides: the apartness rule both checkers admit the empty case over a
    ///   path type by.
    /// - fails: never — an exhausted decision is [`Apartness::Undecided`].
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the flattening is a `while let` loop over a stack charged one
    ///   unit of fuel per node; [`Self::converges`] and [`Self::normalize`]
    ///   terminate; the scans are `for` loops over the two finite terms.
    /// - measure: the decision's fuel; the nodes left to scan.
    ///
    /// # Cost
    /// - allocation: the constructors' arities and the two flattened terms,
    ///   growth within the constructor table and the two terms' nodes
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `S(Z)` and `Z` over the integers are apart, `S(P(Z))`
    ///   and `Z` agree, `S(x)` and `Z` over a leaf of the type are open, a
    ///   reference to `S(Z)` is apart from `Z`, two marks over distinct leaves
    ///   differ at a leaf, two distinct words are apart, a self-referring
    ///   definition runs out of fuel, and divergent rules are named; over a
    ///   free type, `S(x)` and `Z` are apart, `S(Z)` and `S(S(x))` are apart
    ///   below their shared head, and `x` and `S(Z)` are open.
    /// - witness: `presented::tests::apartness_is_decided_by_normal_forms`
    #[spec(ensures: |ret| !self.rules().is_empty() || !matches!(ret, Apartness::Diverges { .. }))]
    #[inline]
    #[must_use]
    pub fn apart<T, V, R>(
        &self,
        table: &[SmallVec<RuleSlot<T>, 0, Global>],
        (left, right): (V, V),
        mut read: R,
    ) -> Apartness
    where
        T: Copy + Eq,
        V: Copy + Eq,
        R: FnMut(V, &mut SmallVec<V, 0, Global>) -> TermReading<V>,
    {
        let arities: SmallVec<FieldCount, 0, Global> = table
            .iter()
            .map(|fields| FieldCount(fields.len()))
            .collect();
        let mut fuel = RewriteFuel(DECISION_FUEL);
        let decided = flatten(table, left, &mut read, &mut fuel).and_then(|mut left| {
            let mut right = flatten(table, right, &mut read, &mut fuel)?;
            decide_apart(self, (table, &arities), (&mut left, &mut right), &mut fuel)
        });
        decided.unwrap_or(Apartness::Undecided)
    }
}

/// The fuel [`Presentation::apart`] spends, the same at every caller.
const DECISION_FUEL: u64 = 0x0010_0000;

/// One node of a term as the caller of [`Presentation::apart`] reads it.
///
/// # Specification
/// - provides: the caller's whole contribution to the decision: which nodes are
///   the type's constructors and which references unfold.
/// - panics: none.
/// - executable: none — closed classification.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::apart`].
/// - witness: `presented::tests::apartness_is_decided_by_normal_forms`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TermReading<V>
{
    /// A constructor of the type with this tag, its fields appended in order.
    Constructor(ConstructorTag),
    /// A reference whose definition is this closed term.
    Defined(V),
    /// Any other node: a leaf.
    Other,
}

/// `root` flattened in pre-order as a term of the type `table` describes:
/// where the type's own family stands, a constructor a node and a definition
/// its body; every other subterm a leaf.
///
/// # Specification
/// - requires: nothing — a constructor whose tag `table` lacks is a leaf.
/// - ensures: the term, each node read costing one unit of `fuel`.
/// - fails: [`Exhausted`] when `fuel` runs out, a definition that refers to
///   itself included.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: a `while let` loop over a stack, each round charged one unit of
///   `fuel`.
/// - measure: `fuel`.
///
/// # Cost
/// - allocation: the flattened term, its pending stack and the read fields,
///   growth within `fuel`
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::apart`].
/// - witness: `presented::tests::apartness_is_decided_by_normal_forms`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |term| !term.is_empty()))]
fn flatten<T, V, R>(
    table: &[SmallVec<RuleSlot<T>, 0, Global>],
    root: V,
    read: &mut R,
    fuel: &mut RewriteFuel,
) -> Result<FlatTerm<V>, Exhausted>
where
    T: Copy + Eq,
    V: Copy + Eq,
    R: FnMut(V, &mut SmallVec<V, 0, Global>) -> TermReading<V>,
{
    let mut term = SmallVec::<_, 0, Global>::new();
    let mut fields = SmallVec::<_, 0, Global>::new();
    let mut pending = SmallVec::<_, 0, Global>::from_iter([(root, RuleSlot::<T>::Own)]);
    while let Some((at, slot)) = pending.pop() {
        fuel.charge()?;
        fields.clear();
        let reading = read(at, &mut fields);
        match (slot, reading) {
            (RuleSlot::Own, TermReading::Constructor(tag)) => {
                let Some(row) = table.get(usize::from(tag))
                else {
                    term.push(RuleTerm::Leaf(at));
                    continue;
                };
                term.push(RuleTerm::Constructor {
                    tag,
                    arity: FieldCount(fields.len()),
                    payload: (),
                });
                for (index, &field) in fields.iter().enumerate().rev() {
                    pending.push((field, row.get(index).copied().unwrap_or(RuleSlot::Own)));
                }
            },
            (RuleSlot::Own, TermReading::Defined(body)) => pending.push((body, RuleSlot::Own)),
            (RuleSlot::Own, TermReading::Other) | (RuleSlot::Other(_) | RuleSlot::Dependent, _) => {
                term.push(RuleTerm::Leaf(at));
            },
        }
    }
    Ok(term)
}

/// Whether a presentation's rules give every term one normal form.
///
/// # Specification
/// - provides: the verdict [`Presentation::converges`] reaches.
/// - panics: none.
/// - executable: none — closed classification.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::converges`].
/// - witness: `presented::tests::critical_pairs_decide_convergence`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Convergence
{
    /// Every critical pair joins: every term has one normal form.
    Converges,
    /// The overlap of rule `outer` by rule `inner` rewrites one term to two
    /// normal forms.
    Diverges
    {
        /// The rule overlapped, rewritten at the overlap's root.
        outer: RuleIndex,
        /// The rule overlapping it, rewritten where its left side stands.
        inner: RuleIndex,
    },
}

/// How two terms of a presented type stand, as [`Presentation::apart`]
/// decides.
///
/// # Specification
/// - provides: apartness, and otherwise the one reason it was not decided.
/// - panics: none.
/// - executable: none — closed classification.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::apart`].
/// - witness: `presented::tests::apartness_is_decided_by_normal_forms`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Apartness
{
    /// The normal forms first differ at two constructors with distinct tags:
    /// no path joins the terms.
    Apart,
    /// The normal forms agree: the terms are one element.
    Agree,
    /// A normal form holds a subterm of the type that is no constructor — a
    /// variable or a stuck term — which the rules might rewrite once it is
    /// known.
    Open,
    /// The normal forms first differ at a subterm of another type, which the
    /// rules do not read.
    Leaf,
    /// The rules do not converge, so distinct normal forms need not be
    /// distinct elements.
    Diverges
    {
        /// The rule overlapped.
        outer: RuleIndex,
        /// The rule overlapping it.
        inner: RuleIndex,
    },
    /// The decision's fuel ran out first.
    Undecided,
}

/// [`Presentation::apart`]'s decision within `fuel`.
///
/// # Specification
/// - requires: as [`Presentation::apart`]; `arities` counts `table`.
/// - ensures: as [`Presentation::apart`], the terms normalized in place.
/// - fails: [`Exhausted`] when `fuel` runs out.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: as [`Presentation::apart`].
/// - measure: `fuel`; the nodes left to scan.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::apart`].
/// - witness: `presented::tests::apartness_is_decided_by_normal_forms`
#[spec(ensures: |ret| ret != Ok(Apartness::Undecided))]
fn decide_apart<T, L>(
    presentation: &Presentation,
    (table, arities): (&[SmallVec<RuleSlot<T>, 0, Global>], &[FieldCount]),
    (left, right): (&mut FlatTerm<L>, &mut FlatTerm<L>),
    fuel: &mut RewriteFuel,
) -> Result<Apartness, Exhausted>
where
    T: Copy + Eq,
    L: Copy + Eq,
{
    if !presentation.rules().is_empty() {
        if let Convergence::Diverges { outer, inner } = presentation.converges(arities, fuel)? {
            return Ok(Apartness::Diverges { outer, inner });
        }
        let _left = presentation.normalize(arities, left, |&()| (), fuel)?;
        let _right = presentation.normalize(arities, right, |&()| (), fuel)?;
        // A rule may rewrite a leaf of the type into the other term.
        if closure(table, left) == Closure::Open || closure(table, right) == Closure::Open {
            return Ok(Apartness::Open);
        }
    }
    for (one, other) in left.iter().zip(right.iter()) {
        fuel.charge()?;
        match (*one, *other) {
            (
                RuleTerm::Constructor { tag: first, .. },
                RuleTerm::Constructor { tag: second, .. },
            ) => {
                if first != second {
                    return Ok(Apartness::Apart);
                }
            },
            (RuleTerm::Leaf(first), RuleTerm::Leaf(second)) if first == second => {},
            (RuleTerm::Constructor { .. } | RuleTerm::Leaf(_), _) => {
                return Ok(unsettled(table, left, right));
            },
        }
    }
    if left.len() == right.len() {
        Ok(Apartness::Agree)
    }
    else {
        Ok(unsettled(table, left, right))
    }
}

/// Why two terms that differ short of two distinct constructors are not shown
/// apart.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Apartness::Open`] exactly when either term holds a leaf where
///   the type's own family stands, or is not one term by `table`;
///   [`Apartness::Leaf`] otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::apart`].
/// - witness: `presented::tests::apartness_is_decided_by_normal_forms`
#[spec(ensures: |ret| matches!(ret, Apartness::Open | Apartness::Leaf))]
fn unsettled<T, L>(
    table: &[SmallVec<RuleSlot<T>, 0, Global>],
    left: &[RuleTerm<(), L>],
    right: &[RuleTerm<(), L>],
) -> Apartness
where
    T: Copy + Eq,
{
    if closure(table, left) == Closure::Open || closure(table, right) == Closure::Open {
        Apartness::Open
    }
    else {
        Apartness::Leaf
    }
}

/// Whether a flattened term of a presented type is closed where its own
/// family stands.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Closure
{
    /// No leaf stands where the family does.
    Closed,
    /// A leaf stands where the family does, or the term is not one term.
    Open,
}

/// Whether a flattened term of a presented type holds a leaf where its own
/// family stands.
///
/// # Specification
/// - requires: nothing — a term that is not one well-formed pre-order term by
///   `table` reads as open.
/// - ensures: [`Closure::Open`] exactly when some leaf of `term` stands at the
///   root or at a [`RuleSlot::Own`] field of the constructor above it, or the
///   term is not one term by `table`.
/// - provides: the closedness [`Presentation::apart`] asks of a normal form.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` loop over the term.
/// - measure: the nodes left.
///
/// # Cost
/// - allocation: the stack of field slots that the walk expects, growth within
///   the term's nodes
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::apart`].
/// - witness: `presented::tests::apartness_is_decided_by_normal_forms`
#[spec(ensures: |ret| !term.is_empty() || ret == Closure::Open)]
fn closure<T, C, L>(
    table: &[SmallVec<RuleSlot<T>, 0, Global>],
    term: &[RuleTerm<C, L>],
) -> Closure
where
    T: Copy + Eq,
{
    let mut expected = SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own]);
    for node in term {
        let Some(slot) = expected.pop()
        else {
            return Closure::Open;
        };
        match *node {
            RuleTerm::Constructor { tag, .. } => {
                let Some(fields) = table.get(usize::from(tag))
                else {
                    return Closure::Open;
                };
                expected.extend(fields.iter().rev().copied());
            },
            RuleTerm::Leaf(_) => {
                if slot == RuleSlot::Own {
                    return Closure::Open;
                }
            },
        }
    }
    if expected.is_empty() {
        Closure::Closed
    }
    else {
        Closure::Open
    }
}

/// A variable of a critical pair: the overlapped rule's or the overlapping
/// rule's, kept apart.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PairVariable
{
    /// A variable of the overlapped rule.
    Outer(RuleVariable),
    /// A variable of the overlapping rule.
    Inner(RuleVariable),
}

/// A term flattened in pre-order with no payload on its constructors: what
/// the apartness decision and the critical pairs compare.
type FlatTerm<L> = SmallVec<RuleTerm<(), L>, 0, Global>;

/// One side of a critical pair, flattened in pre-order.
type PairTerm = FlatTerm<PairVariable>;

/// What overlapping one rule's left side by another's at a position found.
///
/// # Specification
/// trivial.
enum Overlap
{
    /// The two left sides do not unify there.
    Disjoint,
    /// They unify; the overlap rewritten by each rule.
    Pair
    {
        /// The overlap rewritten at its root by the overlapped rule.
        outer: PairTerm,
        /// The overlap rewritten at the position by the overlapping rule.
        inner: PairTerm,
    },
}

/// The critical pair of `outer` overlapped at `position` of its left side by
/// `inner`'s left side.
///
/// # Specification
/// - requires: both rules passed [`Presentation::validate`] against the table
///   `arities` counts; `position` holds a constructor of `outer`'s left side.
/// - ensures: [`Overlap::Disjoint`] when the subterm at `position` and
///   `inner`'s left side meet two constructors with distinct tags; otherwise
///   [`Overlap::Pair`] with the most general unifier `σ` — each variable of
///   either side bound to the other side's subterm standing where it does —
///   applied to `outer`'s right side, and to `outer`'s left side with `inner`'s
///   right side in place at `position`. Each node walked or copied costs one
///   unit of `fuel`.
/// - fails: [`Exhausted`] when `fuel` runs out.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `while let` loop advances a cursor over the subterm at
///   `position` every round; the builds are `for` loops over finite sides.
/// - measure: the subterm's nodes left.
///
/// # Cost
/// - allocation: the unifier's bindings and the two sides of the critical pair,
///   growth within the two rules' sides
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::converges`].
/// - witness: `presented::tests::critical_pairs_decide_convergence`
#[spec(ensures: |ret| ret.is_ok() || fuel.0 == 0)]
fn overlap(
    (outer, position): (&PresentedRule, TermPosition),
    inner: &PresentedRule,
    arities: &[FieldCount],
    fuel: &mut RewriteFuel,
) -> Result<Overlap, Exhausted>
{
    let left = outer.left();
    let TermPosition(end) = subterm_end(left, position, arities, fuel)?;
    let (Some(before), Some(at), Some(after)) = (
        left.get(.. position.0),
        left.get(position.0 .. end),
        left.get(end ..),
    )
    else {
        return Ok(Overlap::Disjoint);
    };
    let overlapping = inner.left();
    let mut outer_bound: SmallVec<(RuleVariable, PairTerm), 0, Global> =
        SmallVec::<_, 0, Global>::new();
    let mut inner_bound: SmallVec<(RuleVariable, PairTerm), 0, Global> =
        SmallVec::<_, 0, Global>::new();
    let (mut a, mut b) = (0_usize, 0_usize);
    while let Some(&node) = at.get(a) {
        fuel.charge()?;
        match (node, overlapping.get(b)) {
            (RuleNode::Constructor(one), Some(&RuleNode::Constructor(other))) => {
                if one != other {
                    return Ok(Overlap::Disjoint);
                }
                a = a.saturating_add(1);
                b = b.saturating_add(1);
            },
            (RuleNode::Variable(variable), Some(_)) => {
                let TermPosition(to) = subterm_end(overlapping, TermPosition(b), arities, fuel)?;
                let span = overlapping.get(b .. to).unwrap_or(&[]);
                outer_bound.push((variable, flattened(span, PairVariable::Inner, arities)));
                a = a.saturating_add(1);
                b = to;
            },
            (RuleNode::Constructor(_), Some(&RuleNode::Variable(variable))) => {
                let TermPosition(to) = subterm_end(at, TermPosition(a), arities, fuel)?;
                let span = at.get(a .. to).unwrap_or(&[]);
                inner_bound.push((variable, flattened(span, PairVariable::Outer, arities)));
                a = to;
                b = b.saturating_add(1);
            },
            (RuleNode::Constructor(_) | RuleNode::Variable(_), None) => {
                return Ok(Overlap::Disjoint);
            },
        }
    }
    // Stable, so a variable bound twice keeps its first binding first, which
    // is the one `substituted` reads.
    outer_bound.sort_by_key(|&(variable, _)| variable);
    inner_bound.sort_by_key(|&(variable, _)| variable);
    let by_outer = substituted(outer.right(), PairVariable::Outer, &outer_bound, arities);
    let mut by_inner = flattened(before, PairVariable::Outer, arities);
    by_inner.extend(substituted(
        inner.right(),
        PairVariable::Inner,
        &inner_bound,
        arities,
    ));
    by_inner.extend(flattened(after, PairVariable::Outer, arities));
    Ok(Overlap::Pair {
        outer: by_outer,
        inner: by_inner,
    })
}

/// One past the last node of the subterm of `side` starting at `start`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the end of the pre-order subterm at `start` by `arities`; the
///   side's length when the side ends first.
/// - fails: [`Exhausted`] when `fuel` runs out; one unit per node.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `while let` loop reads one node per round and stops at the
///   side's end.
/// - measure: the side's nodes after `start`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::converges`].
/// - witness: `presented::tests::critical_pairs_decide_convergence`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&TermPosition(end)| end <= side.len().max(start.0)))]
fn subterm_end(
    side: &[RuleNode],
    start: TermPosition,
    arities: &[FieldCount],
    fuel: &mut RewriteFuel,
) -> Result<TermPosition, Exhausted>
{
    let TermPosition(mut at) = start;
    let mut owed = 1_usize;
    while let Some(next) = owed.checked_sub(1) {
        fuel.charge()?;
        owed = match side.get(at) {
            Some(&RuleNode::Constructor(tag)) => {
                next.saturating_add(arities.get(usize::from(tag)).map_or(0, |count| count.0))
            },
            Some(&RuleNode::Variable(_)) => next,
            None => return Ok(TermPosition(side.len().max(start.0))),
        };
        at = at.saturating_add(1);
    }
    Ok(TermPosition(at))
}

/// `nodes` as a pair's term, each variable read as `side` names it.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the pair's term, one entry for each node, growth within the
///   given nodes
fn flattened(
    nodes: &[RuleNode],
    side: fn(RuleVariable) -> PairVariable,
    arities: &[FieldCount],
) -> PairTerm
{
    nodes
        .iter()
        .map(|&node| match node {
            RuleNode::Constructor(tag) => RuleTerm::Constructor {
                tag,
                arity: arities.get(usize::from(tag)).copied().unwrap_or_default(),
                payload: (),
            },
            RuleNode::Variable(variable) => RuleTerm::Leaf(side(variable)),
        })
        .collect()
}

/// The rule side `nodes` under a unifier: each variable `bound` names read
/// as its term, every other as `side` names it.
///
/// # Specification
/// - requires: `bound` is sorted by variable.
/// - ensures: each variable node replaced by the first term `bound` holds for
///   it, or by its leaf under `side` when `bound` holds none; each constructor
///   node kept with its arity under `arities`.
/// - panics: none.
/// - executable: none — sortedness of `bound` would rescan it on every call,
///   and the substituted term is the body's own construction.
///
/// # Cost
/// - allocation: the substituted term, growth within the rule side's nodes and
///   the unifier's terms
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::converges`].
/// - witness: `presented::tests::critical_pairs_decide_convergence`
fn substituted(
    nodes: &[RuleNode],
    side: fn(RuleVariable) -> PairVariable,
    bound: &[(RuleVariable, PairTerm)],
    arities: &[FieldCount],
) -> PairTerm
{
    let mut term = SmallVec::<_, 0, Global>::with_capacity(Count::from(nodes.len()));
    for &node in nodes {
        match node {
            RuleNode::Constructor(tag) => term.push(RuleTerm::Constructor {
                tag,
                arity: arities.get(usize::from(tag)).copied().unwrap_or_default(),
                payload: (),
            }),
            RuleNode::Variable(variable) => {
                let first = bound.partition_point(|&(named, _)| named < variable);
                match bound.get(first) {
                    Some(&(named, ref value)) if named == variable => {
                        term.extend_from_slice(value);
                    },
                    Some(_) | None => term.push(RuleTerm::Leaf(side(variable))),
                }
            },
        }
    }
    term
}

/// A free invertible 1-cell of a presented type's sort: a generator between
/// two closed terms of the sort, each a side over the sort's own constructor
/// table holding no variable.
///
/// Each end is a shared list of nodes. The cells of one presentation share
/// their ends: the loops of a type of words hold its point by a count, one
/// block for any count of loops. The equality and the hash read the nodes, so
/// two cells with the same ends are equal whether or not they share a block.
///
/// # Specification
/// - provides: the producer's two endpoints, unchecked; admission owns their
///   well-formedness.
/// - panics: none.
/// - executable: none — data declaration; [`FreeCells::validate`] checks the
///   endpoints against the sort's table.
///
/// # Adequacy
/// - hypothesis: L3 — as [`FreeCells::validate`].
/// - witness: `presented::tests::cell_validation_names_each_fault`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FreeCell
{
    /// The cell's source, in pre-order.
    source: ThinShared<(), RuleNode, Global>,
    /// The cell's target, in pre-order.
    target: ThinShared<(), RuleNode, Global>,
}

impl FreeCell
{
    /// The cell from `source` to `target`. A loop passes one end twice.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        source: ThinShared<(), RuleNode, Global>,
        target: ThinShared<(), RuleNode, Global>,
    ) -> Self
    {
        Self { source, target }
    }

    /// The source, in pre-order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn source(&self) -> &[RuleNode]
    {
        self.source.slice()
    }

    /// The target, in pre-order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn target(&self) -> &[RuleNode]
    {
        self.target.slice()
    }
}

/// The free cells a type of words is minted over.
///
/// The cells name the sort whose closed terms they join, by its admission
/// position, and how many times the point is wrapped in its reflexivity. They
/// hold the cells, one generator each, in written order.
///
/// # The words
///
/// The type of words over loops at one point is the free group on the cells
/// presented as a polygraph: the empty word, then per generator a letter and
/// its inverse, each taking the rest of the word as its one field, and per
/// generator the two cancellations `g ∷ back(g) ∷ p ==> p` and `back(g) ∷ g ∷
/// p ==> p` as rules. Tag `0` is the empty word, tag `1 + 2i` generator `i`'s
/// letter and tag `2 + 2i` its inverse. The table and the rules follow from
/// the cells alone, so a producer states the cells and the kernel compares
/// what the declaration carries with this mint.
///
/// # Cells above dimension one
///
/// A cell may stand at the reflexivity of the point, `surf : Path.here Base
/// <-> Path.here Base`, a cell of dimension two. The cells then loop at the
/// point wrapped [`Self::reflexivities`] times in its reflexivity, and the
/// path type at that wrapped point reads as their words. The endpoints stay
/// closed terms of the sort, so the table, the rules and the validation are
/// the ones at dimension one. The words commute there: each cell is spherical,
/// so [`Presentation::normalize`] sorts and counts them. **Alternatives.** The
/// 2-cells over the words of the point's loops, a type of words with no cell
/// at dimension one; that needs a type of words with the empty word alone.
/// **Reversal.** A cell between two distinct words of the dimension below, the
/// torus's square, needs the cells' endpoints as words, not as wrapped points.
///
/// # Specification
/// - provides: the cells and the words they mint.
/// - panics: none.
/// - executable: none — data declaration.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::words`].
/// - witness: `presented::tests::a_cell_mints_its_words_and_its_cancellations`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FreeCells
{
    /// The sort's admission position.
    sort: crate::term::ConstantIndex,
    /// How many times the cells' point is wrapped in its reflexivity: none
    /// for loops, one for cells of dimension two.
    reflexivities: Reflexivities,
    /// The cells, in written order.
    cells: Box<[FreeCell]>,
}

impl FreeCells
{
    /// The cells `cells` of the sort admitted at `sort`, loops at their point.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the boxed slice of the sort's cells, growth within the
    ///   given cells
    #[inline]
    #[must_use]
    pub fn new(
        sort: crate::term::ConstantIndex,
        cells: SmallVec<FreeCell, 0, Global>,
    ) -> Self
    {
        Self {
            sort,
            reflexivities: Reflexivities::NONE,
            cells: cells.into_boxed_slice(),
        }
    }

    /// These cells at their point wrapped `reflexivities` times in its
    /// reflexivity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn wrapped(
        self,
        reflexivities: Reflexivities,
    ) -> Self
    {
        Self {
            reflexivities,
            ..self
        }
    }

    /// The sort's admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sort(&self) -> crate::term::ConstantIndex
    {
        self.sort
    }

    /// How many times the cells' point is wrapped in its reflexivity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reflexivities(&self) -> Reflexivities
    {
        self.reflexivities
    }

    /// The cells, in written order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cells(&self) -> &[FreeCell]
    {
        &self.cells
    }

    /// The point the words loop at: the first cell's source, empty when there
    /// is no cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn point(&self) -> &[RuleNode]
    {
        self.cells.first().map_or(&[], FreeCell::source)
    }

    /// The empty word's tag.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nil() -> ConstructorTag
    {
        ConstructorTag::from(0_usize)
    }

    /// The tag of generator `generator`'s letter.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn letter(generator: CellIndex) -> ConstructorTag
    {
        ConstructorTag::from(generator.0.saturating_mul(2).saturating_add(1))
    }

    /// The tag of generator `generator`'s inverse.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn inverse(generator: CellIndex) -> ConstructorTag
    {
        ConstructorTag::from(generator.0.saturating_mul(2).saturating_add(2))
    }

    /// The generator whose letter or inverse is tagged `tag`, `None` for the
    /// empty word: the inverse of [`Self::letter`] and [`Self::inverse`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn generator(tag: ConstructorTag) -> Option<CellIndex>
    {
        usize::from(tag)
            .checked_sub(1)
            .map(|offset| CellIndex(offset.div_euclid(2)))
    }

    /// How many constructors the words take: the empty word and a letter and
    /// an inverse per cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn constructors(&self) -> ConstructorCount
    {
        ConstructorCount(self.cells.len().saturating_mul(2).saturating_add(1))
    }

    /// The words' rules: per cell, in order, a letter then its inverse
    /// cancelling, and an inverse then its letter.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: two rules per cell, each `[a, b, x] ==> [x]` over the cell's
    ///   letter and inverse tags, the letter first in the first.
    /// - provides: the mint [`Presentation::words`] and the kernel's admission
    ///   both read.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the cancellation rules and their sides, growth within the
    ///   presentation's cells
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's one cell mints the landed circle's two
    ///   rules over tags 1 and 2.
    /// - witness: `presented::tests::a_cell_mints_its_words_and_its_cancellations`
    #[spec(ensures: |ret| ret.len() == self.cells.len().saturating_mul(2))]
    #[inline]
    #[must_use]
    pub fn cancellations(&self) -> SmallVec<PresentedRule, 0, Global>
    {
        let rest = RuleNode::Variable(RuleVariable(0));
        let mut rules = SmallVec::<_, 0, Global>::with_capacity(Count::from(
            self.cells.len().saturating_mul(2),
        ));
        for generator in (0 .. self.cells.len()).map(CellIndex) {
            let letter = RuleNode::Constructor(Self::letter(generator));
            let inverse = RuleNode::Constructor(Self::inverse(generator));
            rules.push(PresentedRule::new(
                [letter, inverse, rest].into(),
                [rest].into(),
            ));
            rules.push(PresentedRule::new(
                [inverse, letter, rest].into(),
                [rest].into(),
            ));
        }
        rules
    }

    /// Check the cells against the sort's constructor table: at least one,
    /// every endpoint a closed term of the sort, and every cell a loop at the
    /// first cell's source.
    ///
    /// `table` lists the sort's constructors as [`Presentation::validate`]
    /// reads them.
    ///
    /// # Specification
    /// - requires: nothing — the cells may be arbitrary producer bytes.
    /// - ensures: `Ok(())` exactly when there is a cell, every endpoint is one
    ///   term by the table's arities with every constructor at the sort and no
    ///   variable, and every cell's source and target are the first cell's
    ///   source; otherwise the first fault in cell order, an endpoint's before
    ///   its loop's.
    /// - provides: the endpoint half of a type of words' admission; the
    ///   distinct-endpoint and directed cells are later readings.
    /// - fails: [`CellFault::Empty`], [`CellFault::Endpoint`],
    ///   [`CellFault::Open`], [`CellFault::NotALoop`] or [`CellFault::Apart`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's loop passes, and one cell per fault is
    ///   refused by that fault and no other.
    /// - witness: `presented::tests::cell_validation_names_each_fault`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CellFault::Empty | CellFault::Endpoint(_) | CellFault::Open | CellFault::NotALoop | CellFault::Apart)))]
    #[inline]
    pub fn validate<T>(
        &self,
        table: &[SmallVec<RuleSlot<T>, 0, Global>],
    ) -> Result<(), CellFault>
    where
        T: Copy + Eq,
    {
        if self.cells.is_empty() {
            return Err(CellFault::Empty);
        }
        for cell in &self.cells {
            for endpoint in [cell.source(), cell.target()] {
                let reading = read_side(endpoint, table).map_err(CellFault::Endpoint)?;
                if !reading.variables.is_empty() {
                    return Err(CellFault::Open);
                }
            }
            if cell.source() != cell.target() {
                return Err(CellFault::NotALoop);
            }
            if cell.source() != self.point() {
                return Err(CellFault::Apart);
            }
        }
        Ok(())
    }
}

/// A cell's position among a type of words' cells, its generator.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CellIndex(usize);

/// How many times a point is wrapped in its reflexivity: none for the point,
/// one for `Path.here a`, two for `Path.here (Path.here a)`.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Reflexivities(usize);

impl Reflexivities
{
    /// The point itself.
    pub const NONE: Self = Self(0);
}

impl From<usize> for Reflexivities
{
    /// `count` wrappings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<Reflexivities> for usize
{
    /// The count of wrappings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: Reflexivities) -> Self
    {
        count.0
    }
}

impl From<usize> for CellIndex
{
    /// The cell at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<CellIndex> for usize
{
    /// The cell's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: CellIndex) -> Self
    {
        index.0
    }
}

/// How many constructors a declaration takes: a type of words, or the sort
/// its words loop at.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstructorCount(usize);

impl From<usize> for ConstructorCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<ConstructorCount> for usize
{
    /// The count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ConstructorCount) -> Self
    {
        count.0
    }
}

/// Why free cells do not mint a type of words.
///
/// # Specification
/// - provides: one variant per clause of [`FreeCells::validate`], and the
///   kernel's admission clauses beside it.
/// - panics: none.
/// - executable: none — closed classification.
///
/// # Adequacy
/// - hypothesis: L3 — as [`FreeCells::validate`].
/// - witness: `presented::tests::cell_validation_names_each_fault`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CellFault
{
    /// No cell: the words would be the empty word alone.
    Empty,
    /// An endpoint is not one term over the sort's table.
    Endpoint(RuleFault),
    /// An endpoint holds a variable: a cell joins closed terms.
    Open,
    /// A cell joins two distinct terms: endpoint-indexed words are a later
    /// reading.
    NotALoop,
    /// A cell loops at another point than the first cell's.
    Apart,
    /// The sort is not a data declaration admitted earlier with no parameter.
    Sort,
    /// The declaration's table or rules are not the words the cells mint.
    NotMinted,
    /// An earlier type of words loops at the same point of the same sort.
    Twice,
}

/// Build a rule side as a term, bottom up: `node` receives each node of the
/// side with the terms already built for its fields, in field order.
///
/// # Specification
/// - requires: nothing — the side may be unvalidated.
/// - ensures: `Ok` with what `node` built at the side's root exactly when every
///   constructor's tag lies in `arities` and the nodes form exactly one
///   pre-order term under those arities; `node` is called once per node read, a
///   variable with no fields, every child before its parent.
/// - provides: a rule's two sides as terms over whatever the caller binds for
///   the pattern's variables, for a conversion to compare under a case's arms.
/// - fails: [`RuleFault::UnknownConstructor`] for a tag past `arities`;
///   [`RuleFault::Arity`] when the nodes do not form exactly one term.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: one `for` loop over the side, not recursion.
/// - measure: the nodes left to read.
///
/// # Cost
/// - allocation: the stack of built terms and each node's fields, growth within
///   the side's nodes
///
/// # Adequacy
/// - hypothesis: L3 — the circle's `loop(unloop(x))` builds `unloop` over the
///   variable and `loop` over that; a side one field short and a tag past the
///   table are refused by their own faults.
/// - witness: `presented::tests::a_rule_side_builds_bottom_up_over_its_variables`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(RuleFault::UnknownConstructor | RuleFault::Arity)))]
#[inline]
pub fn build_side<T, F>(
    side: &[RuleNode],
    arities: &[FieldCount],
    mut node: F,
) -> Result<T, RuleFault>
where
    F: FnMut(RuleNode, SmallVec<T, 0, Global>) -> T,
{
    let mut built: SmallVec<T, 0, Global> = SmallVec::<_, 0, Global>::new();
    for &written in side.iter().rev() {
        let fields = match written {
            RuleNode::Variable(_) => SmallVec::<_, 0, Global>::new(),
            RuleNode::Constructor(tag) => {
                let arity = arities
                    .get(usize::from(tag))
                    .copied()
                    .ok_or(RuleFault::UnknownConstructor)?;
                let start = built
                    .len()
                    .checked_sub(usize::from(arity))
                    .ok_or(RuleFault::Arity)?;
                built.drain(start ..).rev().collect()
            },
        };
        built.push(node(written, fields));
    }
    match (built.pop(), built.is_empty()) {
        (Some(root), true) => Ok(root),
        (Some(_) | None, _) => Err(RuleFault::Arity),
    }
}

/// Where a constructor field stands, as a rule side reads it.
///
/// # Specification
/// - provides: the declaration's own type, where a constructor of the table may
///   stand; another classifier, where only a variable may, compared by
///   identity; or a classifier read only in its constructor's telescope, where
///   neither may.
/// - panics: none.
/// - executable: none — data declaration; [`Presentation::validate`] reads it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::validate`].
/// - witness: `presented::tests::validation_names_each_fault`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RuleSlot<T>
{
    /// The declaration's own type.
    Own,
    /// Another classifier, read under the declaration's parameters alone.
    Other(T),
    /// A field after its constructor's first whose classifier is open: it is
    /// formed under the fields before it as well as the parameters, so a rule
    /// variable standing there would have no classifier of its own.
    Dependent,
}

/// A rule's position in its declaration's written order.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RuleIndex(usize);

impl From<usize> for RuleIndex
{
    /// The rule at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<RuleIndex> for usize
{
    /// The rule's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: RuleIndex) -> Self
    {
        index.0
    }
}

/// Why a rule does not present its type.
///
/// # Specification
/// - provides: one variant per clause of [`Presentation::validate`].
/// - panics: none.
/// - executable: none — closed classification.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::validate`].
/// - witness: `presented::tests::validation_names_each_fault`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RuleFault
{
    /// The left side is a bare variable, which would rewrite every term.
    VariableHeaded,
    /// A side names a constructor past the table.
    UnknownConstructor,
    /// A side's nodes do not form one term by the table's arities.
    Arity,
    /// A constructor stands at a field of another type than the
    /// declaration's own.
    NotOwnPosition,
    /// The left side repeats a variable or skips one in pre-order.
    NonLinear,
    /// The right side names a variable the left side does not bind.
    Unbound,
    /// The right side names one variable twice, which would copy its term.
    Duplicated,
    /// The right side places a variable at a field of another type than the
    /// one it stands at on the left.
    SlotMismatch,
    /// The right side holds as many constructors as the left or more, so the
    /// rule is not seen to terminate.
    NotDecreasing,
    /// A variable stands at a [`RuleSlot::Dependent`] field, whose classifier
    /// is read only in its constructor's telescope.
    DependentSlot,
}

/// The first rule of a presentation that does not present its type, and why.
///
/// # Specification
/// - provides: the rule's written position and its first fault.
/// - panics: none.
/// - executable: none — data declaration.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::validate`].
/// - witness: `presented::tests::validation_names_each_fault`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RuleRefusal
{
    /// The rule, by written position.
    pub rule: RuleIndex,
    /// Its first fault.
    pub fault: RuleFault,
}

/// One node of a constructor term flattened in pre-order for rewriting.
///
/// # Specification
/// - provides: a constructor of the presented type with its arity and the
///   caller's payload, or a leaf the rewriting moves but never reads.
/// - panics: none.
/// - executable: none — data declaration; [`Presentation::normalize`] reads it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::normalize`].
/// - witness: `presented::tests::normalization_reduces_circle_words`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RuleTerm<C, L>
{
    /// A constructor, applied to the next subterms its arity counts.
    Constructor
    {
        /// Its tag in the declaration's table.
        tag: ConstructorTag,
        /// How many subterms follow it as its fields.
        arity: FieldCount,
        /// What the caller carries with it.
        payload: C,
    },
    /// A subterm the rules do not inspect.
    Leaf(L),
}

/// How many fields a constructor has, as rewriting counts its subterms.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FieldCount(usize);

impl From<usize> for FieldCount
{
    /// A constructor of `fields` fields.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fields: usize) -> Self
    {
        Self(fields)
    }
}

impl From<FieldCount> for usize
{
    /// The field count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: FieldCount) -> Self
    {
        count.0
    }
}

/// Whether a normalization rewrote anything.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Normalized
{
    /// No rule matched anywhere: the term was normal.
    Unchanged,
    /// At least one rewrite fired.
    Rewritten,
}

/// A normalization ran out of fuel.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Exhausted;

/// The nodes a normalization may still compare or copy.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RewriteFuel(u64);

impl From<u64> for RewriteFuel
{
    /// Fuel for `nodes` nodes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(nodes: u64) -> Self
    {
        Self(nodes)
    }
}

impl From<RewriteFuel> for u64
{
    /// The nodes still to spend.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fuel: RewriteFuel) -> Self
    {
        fuel.0
    }
}

impl RewriteFuel
{
    /// Spend one node, or report the fuel exhausted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one unit spent when any remained; [`Exhausted`] with nothing
    ///   spent when none did.
    /// - provides: the charge every rewriting step pays.
    /// - fails: [`Exhausted`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Presentation::normalize`].
    /// - witness: `presented::tests::normalization_reduces_circle_words`
    #[spec(captures: before = self.0, ensures: |ret| match ret {
        Ok(()) => before > 0 && self.0 == before.saturating_sub(1),
        Err(Exhausted) => before == 0 && self.0 == 0,
    })]
    pub(crate) fn charge(&mut self) -> Result<(), Exhausted>
    {
        self.0 = self.0.checked_sub(1).ok_or(Exhausted)?;
        Ok(())
    }
}

/// What reading one side against the table found.
///
/// # Specification
/// trivial.
struct SideReading<T>
{
    /// Each variable in pre-order with the slot it stands at.
    variables: SmallVec<(RuleVariable, RuleSlot<T>), 0, Global>,
    /// How many constructors the side holds.
    constructors: usize,
}

/// Read one side against `table`, the root standing at the own type.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the side's variables with their slots and its constructor count
///   when the side is one term by the table's arities, every constructor at the
///   own type and no variable at a [`RuleSlot::Dependent`] field.
/// - provides: the per-side half of [`Presentation::validate`].
/// - fails: [`RuleFault::UnknownConstructor`], [`RuleFault::NotOwnPosition`],
///   [`RuleFault::DependentSlot`] or [`RuleFault::Arity`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop over the side's nodes, not recursion.
/// - measure: the nodes left.
///
/// # Cost
/// - allocation: the expected slots and the side's variables with their slots,
///   growth within the side's nodes
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::validate`].
/// - witness: `presented::tests::validation_names_each_fault`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|reading| reading.constructors.saturating_add(reading.variables.len()) == side.len())
    || matches!(ret, Err(RuleFault::UnknownConstructor | RuleFault::NotOwnPosition | RuleFault::DependentSlot | RuleFault::Arity)))]
fn read_side<T>(
    side: &[RuleNode],
    table: &[SmallVec<RuleSlot<T>, 0, Global>],
) -> Result<SideReading<T>, RuleFault>
where
    T: Copy + Eq,
{
    let mut expected = SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own]);
    let mut reading = SideReading {
        variables: SmallVec::<_, 0, Global>::new(),
        constructors: 0,
    };
    for &node in side {
        let slot = expected.pop().ok_or(RuleFault::Arity)?;
        match node {
            RuleNode::Constructor(tag) => {
                let fields = table
                    .get(usize::from(tag))
                    .ok_or(RuleFault::UnknownConstructor)?;
                if slot != RuleSlot::Own {
                    return Err(RuleFault::NotOwnPosition);
                }
                expected.extend(fields.iter().rev().copied());
                reading.constructors = reading.constructors.saturating_add(1);
            },
            RuleNode::Variable(_) if slot == RuleSlot::Dependent => {
                return Err(RuleFault::DependentSlot);
            },
            RuleNode::Variable(variable) => reading.variables.push((variable, slot)),
        }
    }
    if !expected.is_empty() {
        return Err(RuleFault::Arity);
    }
    Ok(reading)
}

/// A position in a flattened term.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TermPosition(usize);

/// Whether a left side matched at a position.
///
/// # Specification
/// trivial.
enum Matched
{
    /// It did not.
    No,
    /// It did, the redex ending before `end`, each variable bound to the span
    /// of its subterm.
    At
    {
        /// One past the redex's last node.
        end: usize,
        /// Each variable's span, at the number of the variable.
        bindings: SmallVec<(usize, usize), 0, Global>,
    },
}

/// Match the linear pattern `left` at `start` in `term`.
///
/// # Specification
/// - requires: `left` is a validated left side, so its variables are the
///   numbers below their count, each one time. The variables stand in any
///   order.
/// - ensures: [`Matched::At`] when every constructor of `left` meets a
///   constructor of `term` with its tag and its table arity, each variable
///   binding the subterm standing where it does, at the number of the variable;
///   [`Matched::No`] otherwise. Each pattern node and each node a variable's
///   span walks costs one unit.
/// - provides: the matching half of [`Presentation::normalize`].
/// - fails: [`Exhausted`] when `fuel` runs out.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop over the pattern and the `while` loop over one
///   subterm's nodes, not recursion.
/// - measure: the pattern nodes left; the subterm nodes still owed.
///
/// # Cost
/// - allocation: the bindings of the pattern's variables, growth within the
///   left side's variables
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::normalize`].
/// - witness: `presented::tests::normalization_reduces_circle_words`
#[spec(ensures: |ret| match ret {
    Ok(Matched::At { end, ref bindings }) => end <= term.len() && bindings.iter().all(|&(from, to)| start.0 <= from && from < to && to <= end),
    Ok(Matched::No) | Err(Exhausted) => true,
})]
fn matched<C, L>(
    term: &[RuleTerm<C, L>],
    start: TermPosition,
    left: &[RuleNode],
    arities: &[FieldCount],
    fuel: &mut RewriteFuel,
) -> Result<Matched, Exhausted>
{
    let mut at = start.0;
    let mut bindings = SmallVec::<_, 0, Global>::new();
    for &node in left {
        fuel.charge()?;
        match (node, term.get(at)) {
            (RuleNode::Constructor(wanted), Some(&RuleTerm::Constructor { tag, arity, .. }))
                if wanted == tag && arities.get(usize::from(tag)) == Some(&arity) =>
            {
                at = at.saturating_add(1);
            },
            (RuleNode::Variable(variable), Some(_)) => {
                let from = at;
                let mut owed = 1_usize;
                while let Some(next) = owed.checked_sub(1) {
                    fuel.charge()?;
                    owed = match term.get(at) {
                        Some(&RuleTerm::Constructor { arity, .. }) => {
                            next.saturating_add(usize::from(arity))
                        },
                        Some(&RuleTerm::Leaf(_)) => next,
                        None => return Ok(Matched::No),
                    };
                    at = at.saturating_add(1);
                }
                let ordinal = usize::try_from(u32::from(variable)).unwrap_or(usize::MAX);
                if ordinal >= left.len() {
                    return Ok(Matched::No);
                }
                if bindings.len() <= ordinal {
                    bindings.resize(Count::from(ordinal.saturating_add(1)), (from, at));
                }
                if let Some(span) = bindings.get_mut(ordinal) {
                    *span = (from, at);
                }
            },
            (RuleNode::Constructor(_) | RuleNode::Variable(_), _) => return Ok(Matched::No),
        }
    }
    Ok(Matched::At { end: at, bindings })
}

/// Which nodes under a symmetry of a left side take their two arguments in
/// the other order: bit `i` selects the `i`th such node, in pre-order.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Swaps(usize);

/// Match `left` at `start` in `term` in some order of the two arguments of
/// each of its nodes whose constructor `symmetric` holds.
///
/// # Specification
/// - requires: `left` is a validated left side; each tag of `symmetric` is the
///   constructor of a validated symmetry, so it has two fields.
/// - ensures: the outcome of [`matched`] on `left` as written when that
///   matches, when `symmetric` is empty, or when the root of `left` does not
///   meet the node at `start`. Otherwise the outcome of [`matched`] on the
///   first order of `left` that matches, by [`reordered`] over each [`Swaps`]
///   in ascending order, and [`Matched::No`] when no order matches.
/// - provides: the match of a left side under the symmetries of its
///   presentation, so a rule fires in each order of the two arguments of a
///   commutative constructor. Each binding stands at the number of its
///   variable, so the right side builds as for the written order.
/// - fails: [`Exhausted`] when `fuel` runs out.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop over the orders, at most two to the count of the
///   nodes of `left` under a symmetry.
/// - measure: the orders left; `fuel`, which each match charges.
///
/// # Cost
/// - allocation: the positions of the nodes under a symmetry and each order of
///   the left side, growth within the left side's nodes
///
/// # Adequacy
/// - hypothesis: L3 — a rule with a constant on the left of a commutative
///   constructor fires on a term that holds the constant on the right, at the
///   root and below a second such constructor; a term that holds the constant
///   on neither side stays as written; a table with no symmetry matches the
///   written order alone.
/// - witness: `presented::tests::a_left_side_matches_in_each_order_under_a_symmetry_8299`
#[spec(ensures: |ret| match ret {
    Ok(Matched::At { end, ref bindings }) => end <= term.len() && bindings.iter().all(|&(from, to)| start.0 <= from && from < to && to <= end),
    Ok(Matched::No) | Err(Exhausted) => true,
})]
fn matched_under<C, L>(
    symmetric: &[ConstructorTag],
    term: &[RuleTerm<C, L>],
    start: TermPosition,
    left: &[RuleNode],
    arities: &[FieldCount],
    fuel: &mut RewriteFuel,
) -> Result<Matched, Exhausted>
{
    let written = matched(term, start, left, arities, fuel)?;
    let rooted = matches!(
        (left.first(), term.get(start.0)),
        (Some(&RuleNode::Constructor(wanted)), Some(&RuleTerm::Constructor { tag, .. }))
            if wanted == tag
    );
    if symmetric.is_empty() || !rooted || matches!(written, Matched::At { .. }) {
        return Ok(written);
    }
    let sites: SmallVec<TermPosition, 0, Global> = left
        .iter()
        .enumerate()
        .filter(
            |&(_, &node)| matches!(node, RuleNode::Constructor(tag) if symmetric.contains(&tag)),
        )
        .map(|(at, _)| TermPosition(at))
        .collect();
    let orders = u32::try_from(sites.len())
        .ok()
        .and_then(|nodes| 1_usize.checked_shl(nodes))
        .unwrap_or(usize::MAX);
    for swaps in 1 .. orders {
        let order = reordered(left, &sites, Swaps(swaps), arities, fuel)?;
        let found = matched(term, start, &order, arities, fuel)?;
        if matches!(found, Matched::At { .. }) {
            return Ok(found);
        }
    }
    Ok(Matched::No)
}

/// `left` with the two arguments in the other order at each node of `sites`
/// that `swaps` selects.
///
/// # Specification
/// - requires: `left` is one term by `arities`; `sites` are positions of
///   `left`, in ascending order.
/// - ensures: the pre-order of `left` where each node of two fields that stands
///   at `sites[i]`, with bit `i` of `swaps` set, holds its second subterm
///   before its first. Each other node holds its subterms as written. The
///   result has the nodes of `left`, so it has its length.
/// - fails: [`Exhausted`] when `fuel` runs out; one unit per node and per node
///   of each subterm that the walk measures.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `while let` loop over a stack of the subterms still to write,
///   not recursion.
/// - measure: the nodes of `left` not yet written.
///
/// # Cost
/// - allocation: the reordered side and the stack of its subterms, growth
///   within the left side's nodes
///
/// # Adequacy
/// - hypothesis: L3 — as [`matched_under`].
/// - witness: `presented::tests::a_left_side_matches_in_each_order_under_a_symmetry_8299`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |order| order.len() <= left.len()))]
fn reordered(
    left: &[RuleNode],
    sites: &[TermPosition],
    Swaps(swaps): Swaps,
    arities: &[FieldCount],
    fuel: &mut RewriteFuel,
) -> Result<SmallVec<RuleNode, 0, Global>, Exhausted>
{
    let mut order = SmallVec::<_, 0, Global>::with_capacity(Count::from(left.len()));
    let mut pending: SmallVec<TermPosition, 0, Global> =
        SmallVec::<_, 0, Global>::from_iter([TermPosition(0)]);
    while let Some(TermPosition(at)) = pending.pop() {
        fuel.charge()?;
        let Some(&node) = left.get(at)
        else {
            continue;
        };
        order.push(node);
        let RuleNode::Constructor(tag) = node
        else {
            continue;
        };
        let fields = arities.get(usize::from(tag)).map_or(0, |count| count.0);
        let first = pending.len();
        let mut child = TermPosition(at.saturating_add(1));
        for _field in 0 .. fields {
            pending.push(child);
            child = subterm_end(left, child, arities, fuel)?;
        }
        let swapped = fields == 2
            && sites
                .iter()
                .position(|&TermPosition(site)| site == at)
                .and_then(|site| u32::try_from(site).ok())
                .and_then(|bit| swaps.checked_shr(bit))
                .is_some_and(|rest| rest & 1 == 1);
        if !swapped && let Some(children) = pending.get_mut(first ..) {
            children.reverse();
        }
    }
    Ok(order)
}

#[cfg(test)]
mod tests
{
    use alloc::alloc::Global;
    use alloc::string::String;

    use gandr_kernel_data::Count;
    use gandr_kernel_data::SmallVec;
    use gandr_kernel_data::ThinShared;

    use super::Apartness;
    use super::CellFault;
    use super::Convergence;
    use super::Exhausted;
    use super::FieldCount;
    use super::FreeCell;
    use super::FreeCells;
    use super::Normalized;
    use super::Presentation;
    use super::PresentedRule;
    use super::Reflexivities;
    use super::RewriteFuel;
    use super::RuleFault;
    use super::RuleIndex;
    use super::RuleNode;
    use super::RuleReading;
    use super::RuleRefusal;
    use super::RuleSlot;
    use super::RuleTerm;
    use super::RuleVariable;
    use super::TermReading;
    use crate::term::ConstructorTag;

    /// The classifier of `mark`'s field, another type than the circle.
    ///
    /// # Specification
    /// trivial.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Classifier
    {
        /// The integers.
        Integer,
    }

    /// A letter of a circle word: its position in the word as written.
    ///
    /// # Specification
    /// trivial.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Letter(usize);

    /// The word's innermost subterm, which the rules never read.
    ///
    /// # Specification
    /// trivial.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Point;

    /// `base`, `loop(x)`, `unloop(x)`, a constructor `mark(n)` over another
    /// type, and `pair(x, d)` whose second field is open in its telescope, as
    /// validation reads their fields.
    ///
    /// # Specification
    /// trivial.
    fn table() -> SmallVec<SmallVec<RuleSlot<Classifier>, 0, Global>, 0, Global>
    {
        SmallVec::<_, 0, Global>::from_iter([
            SmallVec::<_, 0, Global>::new(),
            SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own]),
            SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own]),
            SmallVec::<_, 0, Global>::from_iter([RuleSlot::Other(Classifier::Integer)]),
            SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own, RuleSlot::Dependent]),
        ])
    }

    /// The one-rule presentation `left ==> right`.
    ///
    /// # Specification
    /// trivial.
    fn one(
        left: &[RuleNode],
        right: &[RuleNode],
    ) -> Presentation
    {
        Presentation::new(SmallVec::<_, 0, Global>::from_iter([PresentedRule::new(
            left.into(),
            right.into(),
        )]))
    }

    /// The circle's two rules.
    ///
    /// # Specification
    /// trivial.
    fn circle() -> Presentation
    {
        let looped = RuleNode::Constructor(ConstructorTag::from(1_usize));
        let unlooped = RuleNode::Constructor(ConstructorTag::from(2_usize));
        let x = RuleNode::Variable(RuleVariable::from(0_u32));
        Presentation::new(SmallVec::<_, 0, Global>::from_iter([
            PresentedRule::new([looped, unlooped, x].into(), [x].into()),
            PresentedRule::new([unlooped, looped, x].into(), [x].into()),
        ]))
    }

    #[test]
    fn validation_names_each_fault()
    {
        let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let v = |ordinal: u32| RuleNode::Variable(RuleVariable::from(ordinal));
        let table = table();
        assert_eq!(circle().validate(&table), Ok(()));
        let refused = |fault| {
            Err(RuleRefusal {
                rule: RuleIndex::from(0_usize),
                fault,
            })
        };
        for (left, right, fault) in [
            (&[v(0)][..], &[c(0)][..], RuleFault::VariableHeaded),
            (&[c(9)], &[c(0)], RuleFault::UnknownConstructor),
            (&[c(1)], &[c(0)], RuleFault::Arity),
            (&[c(1), c(0), c(0)], &[c(0)], RuleFault::Arity),
            (&[c(3), c(0)], &[], RuleFault::NotOwnPosition),
            (&[c(1), v(1)], &[v(1)], RuleFault::NonLinear),
            (&[c(1), c(2), v(0)], &[c(1), v(1)], RuleFault::Unbound),
            (
                &[c(1), c(2), v(0)],
                &[c(1), c(1), v(0)],
                RuleFault::NotDecreasing,
            ),
            (&[c(3), v(0)], &[v(0)], RuleFault::SlotMismatch),
            (&[c(4), v(0), v(1)], &[v(0)], RuleFault::DependentSlot),
        ] {
            assert_eq!(
                one(left, right).validate(&table),
                refused(fault),
                "{fault:?}"
            );
        }
        let doubled = Presentation::new(SmallVec::<_, 0, Global>::from_iter([PresentedRule::new(
            [c(1), c(2), c(1), v(0)].into(),
            [c(1), v(0)].into(),
        )]));
        assert_eq!(doubled.validate(&table), Ok(()));
        let duplicated = Presentation::new(SmallVec::<_, 0, Global>::from_iter([
            PresentedRule::new([c(1), c(2), v(0)].into(), [v(0)].into()),
            PresentedRule::new([c(1), c(1), c(1), v(0)].into(), [c(2), v(0), v(0)].into()),
        ]));
        assert_eq!(
            duplicated.validate(&table),
            Err(RuleRefusal {
                rule: RuleIndex::from(1_usize),
                fault: RuleFault::Arity,
            }),
            "the second rule's right side is two terms, and it is named by position"
        );
    }

    #[test]
    fn a_cell_mints_its_words_and_its_cancellations()
    {
        let base = || ThinShared::from_iter([RuleNode::Constructor(ConstructorTag::from(0_usize))]);
        let sort = crate::term::ConstantIndex::from(3_usize);
        let cells = FreeCells::new(
            sort,
            SmallVec::<_, 0, Global>::from_iter([FreeCell::new(base(), base())]),
        );
        assert_eq!(
            (
                usize::from(cells.constructors()),
                FreeCells::letter(super::CellIndex::from(0_usize)),
                FreeCells::inverse(super::CellIndex::from(0_usize))
            ),
            (
                3_usize,
                ConstructorTag::from(1_usize),
                ConstructorTag::from(2_usize)
            ),
            "the empty word, then the loop's letter and its inverse"
        );
        let words = Presentation::words(cells.clone());
        assert_eq!(
            words.rules(),
            circle().rules(),
            "one loop mints the landed circle's two cancellations, over tags 1 and 2"
        );
        assert_eq!(words.cells(), Some(&cells));
        assert_eq!(
            Presentation::new(SmallVec::<_, 0, Global>::from_iter(
                circle().rules().iter().cloned()
            ))
            .carrying(cells),
            words,
            "the decoder's rules and cells are the mint's"
        );
        let twice = FreeCells::new(
            sort,
            SmallVec::<_, 0, Global>::from_iter([
                FreeCell::new(base(), base()),
                FreeCell::new(base(), base()),
            ]),
        );
        let second = twice.cancellations();
        assert_eq!(
            second.get(2).map(PresentedRule::left),
            Some(
                &[
                    RuleNode::Constructor(ConstructorTag::from(3_usize)),
                    RuleNode::Constructor(ConstructorTag::from(4_usize)),
                    RuleNode::Variable(RuleVariable::from(0_u32))
                ][..]
            ),
            "the second cell cancels over its own letter and inverse"
        );
    }

    #[test]
    fn the_loops_of_a_decoded_type_of_words_share_their_point_8290()
    {
        use gandr_kernel_data::Identity;

        let node = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let mut arena = crate::arena::TermArena::new();
        let mut builder = crate::decl::DeclarationBuilder::new(&mut arena);
        let kind = builder.arena().value_type_universe(
            crate::types::GroundSort::Value,
            gandr_kernel_strata::Level::zero(),
        );
        let own = builder.arena().value_type_data(
            crate::term::ConstantIndex::from(0_usize),
            SmallVec::<_, 0, Global>::new(),
        );
        // Each written end is a block of its own, so only the decoder shares.
        let base = || ThinShared::from_iter([node(0)]);
        let other = || ThinShared::from_iter([node(1), node(0)]);
        let cells = FreeCells::new(
            crate::term::ConstantIndex::from(0_usize),
            SmallVec::<_, 0, Global>::from_iter([
                FreeCell::new(base(), base()),
                FreeCell::new(base(), base()),
                FreeCell::new(base(), other()),
            ]),
        );
        let constructors = core::iter::once(SmallVec::<_, 0, Global>::new())
            .chain(core::iter::repeat_with(|| SmallVec::<_, 0, Global>::from_iter([own])).take(6))
            .collect();
        let data = builder
            .data(
                crate::decl::LevelSignature::monomorphic(),
                SmallVec::<_, 0, Global>::new(),
                constructors,
                kind,
            )
            .presented(Presentation::words(cells.clone()));
        let declarations = [crate::decl::MarkedDeclaration::new(
            crate::decl::AdmissionMark::Checked,
            data,
        )];
        let bytes = crate::encode::encode(&arena, &declarations);
        let decoded =
            crate::decode::decode(bytes.as_image()).expect("the encoded artifact decodes");
        let read = decoded
            .declarations()
            .first()
            .expect("one data declaration")
            .declaration()
            .presentation()
            .cells();
        assert_eq!(read, Some(&cells), "the decoded cells are the written ones");
        let identities = read.and_then(|read| {
            let point = &read.cells.first()?.source;
            Some(
                read.cells
                    .iter()
                    .flat_map(|cell| [&cell.source, &cell.target])
                    .map(|end| ThinShared::ptr_eq(point, end))
                    .collect::<alloc::vec::Vec<_>>(),
            )
        });
        assert_eq!(
            identities,
            Some(alloc::vec![
                Identity::Same,
                Identity::Same,
                Identity::Same,
                Identity::Same,
                Identity::Same,
                Identity::Distinct
            ]),
            "the five ends at the point share one block, and the end that differs holds its own"
        );
    }

    #[test]
    fn cell_validation_names_each_fault()
    {
        let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let v = |ordinal: u32| RuleNode::Variable(RuleVariable::from(ordinal));
        let table = table();
        let sort = crate::term::ConstantIndex::from(0_usize);
        let cells = |pairs: &[(&[RuleNode], &[RuleNode])]| {
            FreeCells::new(
                sort,
                pairs
                    .iter()
                    .map(|&(source, target)| {
                        FreeCell::new(
                            source.iter().copied().collect(),
                            target.iter().copied().collect(),
                        )
                    })
                    .collect(),
            )
        };
        assert_eq!(cells(&[(&[c(0)], &[c(0)])]).validate(&table), Ok(()));
        assert_eq!(
            cells(&[
                (&[c(1), c(0)], &[c(1), c(0)]),
                (&[c(1), c(0)], &[c(1), c(0)])
            ])
            .validate(&table),
            Ok(()),
            "two loops at one compound point"
        );
        for (pairs, fault) in [
            (&[][..], CellFault::Empty),
            (
                &[(&[c(9)][..], &[c(9)][..])][..],
                CellFault::Endpoint(RuleFault::UnknownConstructor),
            ),
            (
                &[(&[c(1)][..], &[c(1)][..])],
                CellFault::Endpoint(RuleFault::Arity),
            ),
            (
                &[(&[c(3), c(0)][..], &[c(3), c(0)][..])],
                CellFault::Endpoint(RuleFault::NotOwnPosition),
            ),
            (&[(&[c(1), v(0)][..], &[c(1), v(0)][..])], CellFault::Open),
            (&[(&[c(0)][..], &[c(1), c(0)][..])], CellFault::NotALoop),
            (
                &[
                    (&[c(0)][..], &[c(0)][..]),
                    (&[c(1), c(0)][..], &[c(1), c(0)][..]),
                ],
                CellFault::Apart,
            ),
        ] {
            assert_eq!(cells(pairs).validate(&table), Err(fault), "{fault:?}");
        }
    }

    #[test]
    fn normalization_reduces_circle_words()
    {
        let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let x = RuleNode::Variable(RuleVariable::from(0_u32));
        // `word` over the point, each letter `1` a `loop` and `2` an `unloop`,
        // each carrying its position as written.
        let word = |letters: &[usize]| {
            let mut term: SmallVec<RuleTerm<Letter, Point>, 0, Global> = letters
                .iter()
                .enumerate()
                .map(|(position, &letter)| RuleTerm::Constructor {
                    tag: ConstructorTag::from(letter),
                    arity: FieldCount::from(1_usize),
                    payload: Letter(position),
                })
                .collect();
            term.push(RuleTerm::Leaf(Point));
            term
        };
        let shifted = |&Letter(position): &Letter| Letter(position + 100);
        let kept = |&letter: &Letter| letter;
        let arities = [0_usize, 1, 1, 1].map(FieldCount::from);
        let circle = circle();
        let mut fuel = RewriteFuel::from(1_000_u64);
        let mut term = word(&[1, 2, 1]);
        assert_eq!(
            circle.normalize(&arities, &mut term, shifted, &mut fuel),
            Ok(Normalized::Rewritten)
        );
        assert_eq!(
            term,
            word(&[1]),
            "the innermost pair, `unloop(loop(x))` from the second letter, goes first, keeping \
             the outer `loop` as written"
        );
        let built = Presentation::new(SmallVec::<_, 0, Global>::from_iter([PresentedRule::new(
            [c(1), c(2), c(1), x].into(),
            [c(1), x].into(),
        )]));
        let mut term = word(&[1, 2, 1]);
        assert_eq!(
            built.normalize(&arities, &mut term, shifted, &mut fuel),
            Ok(Normalized::Rewritten)
        );
        assert_eq!(
            term,
            [
                RuleTerm::Constructor {
                    tag: ConstructorTag::from(1_usize),
                    arity: FieldCount::from(1_usize),
                    payload: Letter(100),
                },
                RuleTerm::Leaf(Point),
            ],
            "a constructor the right side builds carries what `fresh` makes of the redex root's \
             payload"
        );
        let mut nested = word(&[1, 1, 2, 2, 2, 1, 1]);
        assert_eq!(
            circle.normalize(&arities, &mut nested, kept, &mut fuel),
            Ok(Normalized::Rewritten)
        );
        assert_eq!(nested.len(), 2, "{nested:?}");
        assert!(matches!(nested.last(), Some(&RuleTerm::Leaf(Point))));
        let mut reduced = word(&[1, 1, 1]);
        let before = reduced.clone();
        assert_eq!(
            circle.normalize(&arities, &mut reduced, kept, &mut fuel),
            Ok(Normalized::Unchanged)
        );
        assert_eq!(reduced, before);
        let mut starved = RewriteFuel::from(3_u64);
        assert_eq!(
            circle.normalize(&arities, &mut word(&[1, 2, 1, 2]), kept, &mut starved),
            Err(Exhausted)
        );
        assert_eq!(u64::from(starved), 0);
    }

    /// The words over two loops at one point: tags 1 and 2 the first loop's
    /// letter and inverse, 3 and 4 the second's.
    ///
    /// # Specification
    /// trivial.
    fn two_loops() -> Presentation
    {
        let base = || ThinShared::from_iter([RuleNode::Constructor(ConstructorTag::from(0_usize))]);
        Presentation::words(FreeCells::new(
            crate::term::ConstantIndex::from(3_usize),
            SmallVec::<_, 0, Global>::from_iter([
                FreeCell::new(base(), base()),
                FreeCell::new(base(), base()),
            ]),
        ))
    }

    /// `letters` over `end`, each letter carrying its position as written.
    ///
    /// # Specification
    /// trivial.
    fn spelled(
        letters: &[ConstructorTag],
        end: RuleTerm<Letter, Point>,
    ) -> SmallVec<RuleTerm<Letter, Point>, 0, Global>
    {
        let mut term: SmallVec<RuleTerm<Letter, Point>, 0, Global> = letters
            .iter()
            .enumerate()
            .map(|(position, &tag)| RuleTerm::Constructor {
                tag,
                arity: FieldCount::from(1_usize),
                payload: Letter(position),
            })
            .collect();
        term.push(end);
        term
    }

    #[test]
    fn the_pass_over_a_word_rewrites_as_the_rules_do()
    {
        let words = two_loops();
        let arities = [0_usize, 1, 1, 1, 1].map(FieldCount::from);
        let kept = |&letter: &Letter| letter;
        let empty = RuleTerm::Constructor {
            tag: ConstructorTag::from(0_usize),
            arity: FieldCount::from(0_usize),
            payload: Letter(usize::MAX),
        };
        let mut compared = 0_usize;
        let mut letters: SmallVec<ConstructorTag, 0, Global> =
            SmallVec::<_, 0, Global>::with_capacity(Count::from(6));
        let mut rewritten: SmallVec<RuleTerm<Letter, Point>, 0, Global> =
            SmallVec::<_, 0, Global>::with_capacity(Count::from(7));
        for length in 0 ..= 6_u32 {
            for code in 0 .. 4_usize.pow(length) {
                letters.clear();
                letters.extend((0 .. length).map(|place| {
                    ConstructorTag::from(code.div_euclid(4_usize.pow(place)) % 4 + 1)
                }));
                for end in [RuleTerm::Leaf(Point), empty] {
                    let mut passed = spelled(&letters, end);
                    rewritten.clear();
                    rewritten.extend_from_slice(&passed);
                    let mut fuel = RewriteFuel::from(10_000_u64);
                    let by_pass = words.normalize(&arities, &mut passed, kept, &mut fuel);
                    let by_rules = words.rewritten(
                        &arities,
                        &mut rewritten,
                        kept,
                        &mut RewriteFuel::from(10_000_u64),
                    );
                    assert_eq!(
                        (by_pass, &passed),
                        (by_rules, &rewritten),
                        "the pass removes the pairs the rules remove, and keeps each other \
                         letter as written: {letters:?}"
                    );
                    assert_eq!(
                        u64::from(fuel),
                        10_000 - u64::from(length),
                        "the pass reads each letter once: {letters:?}"
                    );
                    compared += 1;
                }
            }
        }
        assert_eq!(
            compared,
            2 * 5_461,
            "every word of up to six letters, over both ends"
        );
        let mut unpresented = spelled(
            &[1_usize, 2].map(ConstructorTag::from),
            RuleTerm::Leaf(Point),
        );
        assert_eq!(
            circle().cancelled(&mut unpresented, &mut RewriteFuel::from(10_u64)),
            Ok(None),
            "the same rules without cells are the rewriting's"
        );
    }

    #[test]
    fn a_word_keeps_its_critical_letters_and_matches_the_rest()
    {
        // The words the timings read: `loop` written `n` times, which `Path.ap`
        // of the identity maps to itself, and `loop` then `back loop`, each
        // `n / 2` times.
        let words = two_loops();
        let arities = [0_usize, 1, 1, 1, 1].map(FieldCount::from);
        let kept = |&letter: &Letter| letter;
        let (forward, back) = (ConstructorTag::from(1_usize), ConstructorTag::from(2_usize));
        for letters in [100_usize, 589, 10_000] {
            let mut fuel = RewriteFuel::from(u64::MAX);
            let mut looped = spelled(
                &SmallVec::<_, 0, Global>::from_iter(core::iter::repeat_n(forward, letters)),
                RuleTerm::Leaf(Point),
            );
            assert_eq!(
                words.normalize(&arities, &mut looped, kept, &mut fuel),
                Ok(Normalized::Unchanged)
            );
            assert_eq!(
                looped.len(),
                letters + 1,
                "each of the {letters} letters is critical, and no pair matches"
            );
            let half = letters.div_euclid(2);
            let mut cancelling = spelled(
                &[
                    SmallVec::<_, 0, Global>::from_iter(core::iter::repeat_n(forward, half)),
                    SmallVec::<_, 0, Global>::from_iter(core::iter::repeat_n(back, half)),
                ]
                .concat(),
                RuleTerm::Leaf(Point),
            );
            assert_eq!(
                words.normalize(&arities, &mut cancelling, kept, &mut fuel),
                Ok(Normalized::Rewritten)
            );
            assert_eq!(
                cancelling,
                [RuleTerm::Leaf(Point)],
                "the {half} pairs match, and no letter is critical"
            );
            assert_eq!(
                u64::MAX - u64::from(fuel),
                u64::try_from(letters + 2 * half).unwrap_or(u64::MAX),
                "each word costs one unit of fuel per letter"
            );
        }
    }

    /// #6740: over cells above dimension one the words are abelian. Two words
    /// that differ by the order of their letters read as one normal form, and
    /// two that differ by a count read apart. A letter cancels its inverse at
    /// any distance. Over two loops, the order still tells two words apart.
    #[test]
    fn a_word_of_cells_above_dimension_one_sorts_and_counts_its_letters_6740()
    {
        use Node::C;
        let base = || ThinShared::from_iter([RuleNode::Constructor(ConstructorTag::from(0_usize))]);
        let spheres = Presentation::words(
            FreeCells::new(
                crate::term::ConstantIndex::from(3_usize),
                SmallVec::<_, 0, Global>::from_iter([
                    FreeCell::new(base(), base()),
                    FreeCell::new(base(), base()),
                ]),
            )
            .wrapped(Reflexivities::from(1_usize)),
        );
        let arities = [0_usize, 1, 1, 1, 1].map(FieldCount::from);
        let kept = |&letter: &Letter| letter;
        // A word's outcome and its tags, the leaf written as `0`, and the fuel
        // it spends.
        let normal = |words: &Presentation, letters: &[usize]| {
            let tags: SmallVec<ConstructorTag, 0, Global> =
                letters.iter().copied().map(ConstructorTag::from).collect();
            let mut term = spelled(&tags, RuleTerm::Leaf(Point));
            let mut fuel = RewriteFuel::from(100_u64);
            let outcome = words.normalize(&arities, &mut term, kept, &mut fuel);
            let read: SmallVec<usize, 0, Global> = term
                .iter()
                .map(|node| match *node {
                    RuleTerm::Constructor { tag, .. } => usize::from(tag),
                    RuleTerm::Leaf(Point) => 0,
                })
                .collect();
            (outcome, read, 100 - u64::from(fuel))
        };
        assert_eq!(
            normal(&spheres, &[3, 1]),
            (
                Ok(Normalized::Rewritten),
                SmallVec::<_, 0, Global>::from_iter([1, 3, 0]),
                2
            ),
            "the second cell's letter moves after the first's"
        );
        assert_eq!(
            normal(&spheres, &[1, 3]),
            (
                Ok(Normalized::Unchanged),
                SmallVec::<_, 0, Global>::from_iter([1, 3, 0]),
                2
            ),
            "a word in the order of its cells is normal"
        );
        assert_eq!(
            normal(&spheres, &[1, 3, 2]),
            (
                Ok(Normalized::Rewritten),
                SmallVec::<_, 0, Global>::from_iter([3, 0]),
                3
            ),
            "the first cell's letter cancels its inverse across the second cell"
        );
        assert_eq!(
            normal(&spheres, &[4, 1, 4, 2, 2]),
            (
                Ok(Normalized::Rewritten),
                SmallVec::<_, 0, Global>::from_iter([2, 4, 4, 0]),
                5
            ),
            "each cell keeps its count, as a letter or an inverse by its sign"
        );
        assert_eq!(
            normal(&two_loops(), &[3, 1]),
            (
                Ok(Normalized::Unchanged),
                SmallVec::<_, 0, Global>::from_iter([3, 1, 0]),
                2
            ),
            "two loops do not commute"
        );
        let table: SmallVec<SmallVec<RuleSlot<Classifier>, 0, Global>, 0, Global> =
            SmallVec::<_, 0, Global>::from_iter([
                SmallVec::<_, 0, Global>::new(),
                SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own]),
                SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own]),
                SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own]),
                SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own]),
            ]);
        let mut terms = Terms::default();
        let mut apart = |words: &Presentation, left: &[Node], right: &[Node]| {
            let (left, right) = (terms.build(left, &arities), terms.build(right, &arities));
            words.apart(&table, (left, right), |at, fields| terms.read(at, fields))
        };
        assert_eq!(
            apart(&spheres, &[C(3), C(1), C(0)], &[C(1), C(3), C(0)]),
            Apartness::Agree,
            "two words that differ by the order of their letters are one word"
        );
        assert_eq!(
            apart(&spheres, &[C(1), C(1), C(0)], &[C(1), C(0)]),
            Apartness::Apart,
            "two words that differ by a count are apart"
        );
        assert_eq!(
            apart(&two_loops(), &[C(3), C(1), C(0)], &[C(1), C(3), C(0)]),
            Apartness::Apart,
            "two words of loops that differ by the order of their letters are apart"
        );
    }

    #[test]
    fn a_rule_side_builds_bottom_up_over_its_variables()
    {
        let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let v = |ordinal: u32| RuleNode::Variable(RuleVariable::from(ordinal));
        let shown = |node: RuleNode, fields: SmallVec<String, 0, Global>| match node {
            RuleNode::Variable(variable) => alloc::format!("x{}", u32::from(variable)),
            RuleNode::Constructor(tag) => {
                alloc::format!("c{}({})", usize::from(tag), fields.join(","))
            },
        };
        let arities = [0_usize, 1, 1, 1].map(FieldCount::from);
        let circle = circle();
        let cancellation = &circle.rules()[0];
        assert_eq!(u32::from(cancellation.variables()), 1);
        assert_eq!(
            super::build_side(cancellation.left(), &arities, shown),
            Ok(String::from("c1(c2(x0))")),
            "`unloop` is built over the variable, `loop` over that"
        );
        assert_eq!(
            super::build_side(cancellation.right(), &arities, shown),
            Ok(String::from("x0"))
        );
        let own = SmallVec::<_, 0, Global>::from_iter([RuleSlot::<u8>::Own]);
        let table = [
            SmallVec::<_, 0, Global>::new(),
            own.clone(),
            own.clone(),
            SmallVec::<_, 0, Global>::from_iter([RuleSlot::Other(7_u8)]),
        ];
        assert_eq!(cancellation.slots(&table), Ok(own));
        let marked = PresentedRule::new([c(1), c(3), v(0)].into(), [c(0)].into());
        assert_eq!(
            marked.slots(&table),
            Ok(SmallVec::<_, 0, Global>::from_iter([RuleSlot::Other(7_u8)])),
            "a variable under a constructor's field of another type reads that classifier"
        );
        assert_eq!(
            PresentedRule::new([c(1), v(0), v(1)].into(), [v(0)].into()).slots(&table),
            Err(RuleFault::Arity),
            "a variable past the side's one term"
        );
        let pair = [0_usize, 2].map(FieldCount::from);
        assert_eq!(
            super::build_side(&[c(1), v(0), v(1)], &pair, shown),
            Ok(String::from("c1(x0,x1)")),
            "fields reach their constructor in field order"
        );
        let ground = PresentedRule::new([c(1), c(0)].into(), [c(0)].into());
        assert_eq!(u32::from(ground.variables()), 0);
        assert_eq!(
            super::build_side(&[c(1)], &arities, shown),
            Err(RuleFault::Arity),
            "a loop missing its field"
        );
        assert_eq!(
            super::build_side(&[c(0), c(0)], &arities, shown),
            Err(RuleFault::Arity),
            "two terms where one is owed"
        );
        assert_eq!(
            super::build_side(&[c(9)], &arities, shown),
            Err(RuleFault::UnknownConstructor)
        );
    }

    /// A node of a test term written in pre-order: a constructor by its tag, a
    /// leaf by its id, or a reference to a term already built.
    ///
    /// # Specification
    /// trivial.
    #[derive(Clone, Copy, Debug)]
    enum Node
    {
        /// A constructor of the table.
        C(usize),
        /// A leaf.
        L(u8),
        /// A reference defined as the term at this id.
        R(Id),
    }

    /// The id of a test term.
    ///
    /// # Specification
    /// trivial.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Id(usize);

    /// A node of a test term as stored.
    ///
    /// # Specification
    /// trivial.
    #[derive(Clone, Debug)]
    enum Stored
    {
        /// A constructor and its fields' ids.
        Constructor(usize, SmallVec<Id, 0, Global>),
        /// A reference and the id of its definition.
        Defined(Id),
        /// A leaf.
        Leaf(u8),
    }

    /// The terms a test decides over, by id.
    ///
    /// # Specification
    /// trivial.
    #[repr(transparent)]
    #[derive(Debug, Default)]
    struct Terms(SmallVec<Stored, 0, Global>);

    impl Terms
    {
        /// The term `nodes` writes over a table of `arities`, its id; one leaf
        /// per leaf id.
        ///
        /// # Specification
        /// trivial.
        fn build(
            &mut self,
            nodes: &[Node],
            arities: &[FieldCount],
        ) -> Id
        {
            let mut built: SmallVec<Id, 0, Global> = SmallVec::<_, 0, Global>::new();
            for &node in nodes.iter().rev() {
                let stored =
                    match node {
                        Node::C(tag) => {
                            let mut fields = SmallVec::<_, 0, Global>::new();
                            for _ in 0 .. arities[tag].0 {
                                fields.push(built.pop().expect("a field is written"));
                            }
                            Stored::Constructor(tag, fields)
                        },
                        Node::L(id) => {
                            if let Some(found) = self.0.iter().position(
                                |stored| matches!(*stored, Stored::Leaf(held) if held == id),
                            ) {
                                built.push(Id(found));
                                continue;
                            }
                            Stored::Leaf(id)
                        },
                        Node::R(target) => Stored::Defined(target),
                    };
                built.push(Id(self.0.len()));
                self.0.push(stored);
            }
            built.pop().expect("one term is written")
        }

        /// The node at `at` as [`Presentation::apart`] reads it.
        ///
        /// # Specification
        /// trivial.
        fn read(
            &self,
            at: Id,
            fields: &mut SmallVec<Id, 0, Global>,
        ) -> TermReading<Id>
        {
            match self.0[at.0] {
                Stored::Constructor(tag, ref written) => {
                    fields.extend_from_slice(written);
                    TermReading::Constructor(ConstructorTag::from(tag))
                },
                Stored::Defined(body) => TermReading::Defined(body),
                Stored::Leaf(_) => TermReading::Other,
            }
        }
    }

    /// The integers' table, `Z`, `S(x)` and `P(x)`, and their two
    /// cancellations.
    ///
    /// # Specification
    /// trivial.
    fn integers() -> (
        SmallVec<SmallVec<RuleSlot<Classifier>, 0, Global>, 0, Global>,
        Presentation,
    )
    {
        let successor = RuleNode::Constructor(ConstructorTag::from(1_usize));
        let predecessor = RuleNode::Constructor(ConstructorTag::from(2_usize));
        let x = RuleNode::Variable(RuleVariable::from(0_u32));
        (
            SmallVec::<_, 0, Global>::from_iter([
                SmallVec::<_, 0, Global>::new(),
                SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own]),
                SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own]),
            ]),
            Presentation::new(SmallVec::<_, 0, Global>::from_iter([
                PresentedRule::new([successor, predecessor, x].into(), [x].into()),
                PresentedRule::new([predecessor, successor, x].into(), [x].into()),
            ])),
        )
    }

    #[test]
    fn critical_pairs_decide_convergence()
    {
        let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let v = |ordinal: u32| RuleNode::Variable(RuleVariable::from(ordinal));
        let arities = [0_usize, 1, 1, 1].map(FieldCount::from);
        let table = table();
        let mut fuel = RewriteFuel::from(10_000_u64);
        assert_eq!(
            circle().converges(&arities, &mut fuel),
            Ok(Convergence::Converges),
            "each cancellation overlaps the other below its root, and the overlaps join"
        );
        let (integers_table, integers) = integers();
        assert_eq!(integers.validate(&integers_table), Ok(()));
        assert_eq!(
            integers.converges(&arities, &mut fuel),
            Ok(Convergence::Converges)
        );
        let forked = Presentation::new(SmallVec::<_, 0, Global>::from_iter([
            PresentedRule::new([c(1), c(2), v(0)].into(), [v(0)].into()),
            PresentedRule::new([c(1), c(2), v(0)].into(), [c(0)].into()),
        ]));
        assert_eq!(forked.validate(&table), Ok(()));
        assert_eq!(
            forked.converges(&arities, &mut fuel),
            Ok(Convergence::Diverges {
                outer: RuleIndex::from(0_usize),
                inner: RuleIndex::from(1_usize),
            }),
            "one redex rewritten to its variable and to `base`, the first rule overlapped first"
        );
        let collapsing = one(&[c(1), c(1), v(0)], &[v(0)]);
        assert_eq!(
            collapsing.converges(&arities, &mut fuel),
            Ok(Convergence::Converges),
            "`loop(loop(loop(x)))` reaches `loop(x)` either way"
        );
        let turning = one(&[c(1), c(1), v(0)], &[c(2), v(0)]);
        assert_eq!(turning.validate(&table), Ok(()));
        assert_eq!(
            turning.converges(&arities, &mut fuel),
            Ok(Convergence::Diverges {
                outer: RuleIndex::from(0_usize),
                inner: RuleIndex::from(0_usize),
            }),
            "the rule overlaps itself below its root: `unloop(loop(x))` against `loop(unloop(x))`"
        );
        let mut starved = RewriteFuel::from(2_u64);
        assert_eq!(circle().converges(&arities, &mut starved), Err(Exhausted));
    }

    /// `zero`, `one`, `band(x, y)` and `bor(x, y)` over two fields of the type
    /// itself, and `tagged(x, n)` whose second field is of another type, as
    /// validation reads their fields.
    ///
    /// # Specification
    /// trivial.
    fn bits() -> SmallVec<SmallVec<RuleSlot<Classifier>, 0, Global>, 0, Global>
    {
        SmallVec::<_, 0, Global>::from_iter([
            SmallVec::<_, 0, Global>::new(),
            SmallVec::<_, 0, Global>::new(),
            SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own, RuleSlot::Own]),
            SmallVec::<_, 0, Global>::from_iter([RuleSlot::Own, RuleSlot::Own]),
            SmallVec::<_, 0, Global>::from_iter([
                RuleSlot::Own,
                RuleSlot::Other(Classifier::Integer),
            ]),
        ])
    }

    /// - see: #8291
    #[test]
    fn a_rule_that_swaps_two_fields_is_a_symmetry()
    {
        let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let v = |ordinal: u32| RuleNode::Variable(RuleVariable::from(ordinal));
        let table = bits();
        let arities = [0_usize, 0, 2, 2, 2].map(FieldCount::from);
        let symmetry = || PresentedRule::new([c(2), v(0), v(1)].into(), [c(2), v(1), v(0)].into());
        assert_eq!(
            symmetry().reading(),
            RuleReading::Symmetry(ConstructorTag::from(2_usize))
        );
        for (left, right, fault) in [
            (
                &[c(2), v(0), v(1)][..],
                &[c(2), v(0), v(1)][..],
                RuleFault::NotDecreasing,
            ),
            (
                &[c(2), v(0), v(1)],
                &[c(3), v(1), v(0)],
                RuleFault::NotDecreasing,
            ),
            (
                &[c(2), v(0), v(0)],
                &[c(2), v(0), v(0)],
                RuleFault::NonLinear,
            ),
            (
                &[c(2), c(0), v(0)],
                &[c(2), v(0), c(0)],
                RuleFault::NotDecreasing,
            ),
        ] {
            let step = one(left, right);
            assert_eq!(
                step.rules().first().map(PresentedRule::reading),
                Some(RuleReading::Step),
                "{left:?} to {right:?}"
            );
            assert_eq!(
                step.validate(&table),
                Err(RuleRefusal {
                    rule: RuleIndex::from(0_usize),
                    fault,
                }),
                "a step that removes no constructor stays refused: {left:?} to {right:?}"
            );
        }
        assert_eq!(
            one(&[c(4), v(0), v(1)], &[c(4), v(1), v(0)]).validate(&table),
            Err(RuleRefusal {
                rule: RuleIndex::from(0_usize),
                fault: RuleFault::SlotMismatch,
            }),
            "a symmetry swaps two fields of one type only"
        );
        let steps = || {
            [
                PresentedRule::new([c(2), c(0), v(0)].into(), [c(0)].into()),
                PresentedRule::new([c(2), c(1), v(0)].into(), [v(0)].into()),
            ]
        };
        let band = Presentation::new(
            steps()
                .into_iter()
                .chain(core::iter::once(symmetry()))
                .collect(),
        );
        assert_eq!(band.validate(&table), Ok(()));
        let node = |tag: usize, arity: usize| RuleTerm::Constructor {
            tag: ConstructorTag::from(tag),
            arity: FieldCount::from(arity),
            payload: Letter(tag),
        };
        let kept = |&letter: &Letter| letter;
        let mut fuel = RewriteFuel::from(100_u64);
        let mut absorbed: SmallVec<RuleTerm<Letter, Point>, 0, Global> =
            SmallVec::<_, 0, Global>::from_iter([node(2, 2), node(0, 0), RuleTerm::Leaf(Point)]);
        assert_eq!(
            band.normalize(&arities, &mut absorbed, kept, &mut fuel),
            Ok(Normalized::Rewritten)
        );
        assert_eq!(
            absorbed,
            [RuleTerm::Constructor {
                tag: ConstructorTag::from(0_usize),
                arity: FieldCount::from(0_usize),
                payload: Letter(2),
            }],
            "the step with zero on the left fires beside the symmetry, and its `zero` carries the \
             payload of the redex root"
        );
        let mut swapped: SmallVec<RuleTerm<Letter, Point>, 0, Global> =
            SmallVec::<_, 0, Global>::from_iter([
                node(2, 2),
                RuleTerm::Leaf(Point),
                RuleTerm::Leaf(Point),
            ]);
        let written = swapped.clone();
        assert_eq!(
            band.normalize(&arities, &mut swapped, kept, &mut fuel),
            Ok(Normalized::Unchanged),
            "no reader rewrites by the symmetry, so the rewriting ends within its fuel"
        );
        assert_eq!(swapped, written);
        let mut fuel = RewriteFuel::from(10_000_u64);
        assert_eq!(
            Presentation::new(steps().into_iter().collect()).converges(&arities, &mut fuel),
            Ok(Convergence::Converges)
        );
        assert_eq!(
            band.converges(&arities, &mut fuel),
            Ok(Convergence::Diverges {
                outer: RuleIndex::from(2_usize),
                inner: RuleIndex::from(2_usize),
            }),
            "the two orders of a symmetry are two normal forms, so the table does not converge"
        );
        let mut terms = Terms::default();
        let (one_bit, zero_bit) = (
            terms.build(&[Node::C(1)], &arities),
            terms.build(&[Node::C(0)], &arities),
        );
        assert_eq!(
            band.apart(&table, (one_bit, zero_bit), |at, fields| terms
                .read(at, fields)),
            Apartness::Diverges {
                outer: RuleIndex::from(2_usize),
                inner: RuleIndex::from(2_usize),
            },
            "no two terms are apart by a table that holds a symmetry"
        );
    }

    /// - see: #8299
    #[test]
    fn a_left_side_matches_in_each_order_under_a_symmetry_8299()
    {
        let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let v = |ordinal: u32| RuleNode::Variable(RuleVariable::from(ordinal));
        let table = bits();
        let arities = [0_usize, 0, 2, 2, 2].map(FieldCount::from);
        let node = |tag: usize, arity: usize| RuleTerm::Constructor {
            tag: ConstructorTag::from(tag),
            arity: FieldCount::from(arity),
            payload: Letter(tag),
        };
        let leaf = |name: usize| RuleTerm::Leaf(Letter(name));
        let kept = |&letter: &Letter| letter;
        let symmetry = |tag: usize| {
            PresentedRule::new([c(tag), v(0), v(1)].into(), [c(tag), v(1), v(0)].into())
        };
        let steps = || {
            [
                PresentedRule::new([c(2), c(0), v(0)].into(), [c(0)].into()),
                PresentedRule::new([c(2), c(1), v(0)].into(), [v(0)].into()),
            ]
        };
        let band = Presentation::new(
            steps()
                .into_iter()
                .chain(core::iter::once(symmetry(2)))
                .collect(),
        );
        assert_eq!(band.validate(&table), Ok(()));
        let normal = |presentation: &Presentation, term: &[RuleTerm<Letter, Letter>]| {
            let mut term: SmallVec<RuleTerm<Letter, Letter>, 0, Global> =
                term.iter().copied().collect();
            let mut fuel = RewriteFuel::from(1_000_u64);
            let outcome = presentation.normalize(&arities, &mut term, kept, &mut fuel);
            (outcome, term)
        };
        assert_eq!(
            normal(&band, &[node(2, 2), leaf(7), node(0, 0)]),
            (
                Ok(Normalized::Rewritten),
                SmallVec::<_, 0, Global>::from_iter([RuleTerm::Constructor {
                    tag: ConstructorTag::from(0_usize),
                    arity: FieldCount::from(0_usize),
                    payload: Letter(2),
                }])
            ),
            "the rule with zero on the left fires on zero on the right"
        );
        assert_eq!(
            normal(&band, &[node(2, 2), leaf(7), node(1, 0)]),
            (
                Ok(Normalized::Rewritten),
                SmallVec::<_, 0, Global>::from_iter([leaf(7)])
            ),
            "the rule with one on the left fires on one on the right, and its variable binds the \
             left argument"
        );
        let stuck = [node(2, 2), leaf(7), leaf(8)];
        assert_eq!(
            normal(&band, &stuck),
            (Ok(Normalized::Unchanged), stuck.iter().copied().collect()),
            "a term that holds a constant on neither side stays as written"
        );
        let right_zero = [node(2, 2), leaf(7), node(0, 0)];
        assert_eq!(
            normal(
                &Presentation::new(steps().into_iter().collect()),
                &right_zero
            ),
            (
                Ok(Normalized::Unchanged),
                right_zero.iter().copied().collect()
            ),
            "a table with no symmetry matches the written order alone"
        );
        // `bor(band(one, x), y) ==> y`, with a symmetry of `band` and of `bor`.
        let nested = Presentation::new(SmallVec::<_, 0, Global>::from_iter([
            PresentedRule::new([c(3), c(2), c(1), v(0), v(1)].into(), [v(1)].into()),
            symmetry(2),
            symmetry(3),
        ]));
        assert_eq!(nested.validate(&table), Ok(()));
        for (term, order) in [
            (
                [node(3, 2), node(2, 2), node(1, 0), leaf(8), leaf(7)],
                "the written order",
            ),
            (
                [node(3, 2), node(2, 2), leaf(8), node(1, 0), leaf(7)],
                "the inner arguments in the other order",
            ),
            (
                [node(3, 2), leaf(7), node(2, 2), node(1, 0), leaf(8)],
                "the outer arguments in the other order",
            ),
            (
                [node(3, 2), leaf(7), node(2, 2), leaf(8), node(1, 0)],
                "the two pairs of arguments in the other order",
            ),
        ] {
            assert_eq!(
                normal(&nested, &term),
                (
                    Ok(Normalized::Rewritten),
                    SmallVec::<_, 0, Global>::from_iter([leaf(7)])
                ),
                "{order}"
            );
        }
    }

    #[test]
    fn apartness_is_decided_by_normal_forms()
    {
        use Node::C;
        use Node::L;
        use Node::R;
        let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let v = |ordinal: u32| RuleNode::Variable(RuleVariable::from(ordinal));
        let mut terms = Terms::default();
        let mut apart = |presentation: &Presentation,
                         table: &[SmallVec<RuleSlot<Classifier>, 0, Global>],
                         left: &[Node],
                         right: &[Node]| {
            let arities: SmallVec<FieldCount, 0, Global> = table
                .iter()
                .map(|fields| FieldCount(fields.len()))
                .collect();
            let (left, right) = (terms.build(left, &arities), terms.build(right, &arities));
            presentation.apart(table, (left, right), |at, fields| terms.read(at, fields))
        };
        let (numbers, integers) = integers();
        assert_eq!(
            apart(&integers, &numbers, &[C(1), C(0)], &[C(0)]),
            Apartness::Apart,
            "`S(Z)` and `Z` are normal and differ at their heads"
        );
        assert_eq!(
            apart(&integers, &numbers, &[C(1), C(1), C(0)], &[C(1), C(0)]),
            Apartness::Apart,
            "`S(S(Z))` and `S(Z)` first differ below one shared head"
        );
        assert_eq!(
            apart(&integers, &numbers, &[C(1), C(2), C(0)], &[C(0)]),
            Apartness::Agree,
            "`S(P(Z))` is `Z`"
        );
        assert_eq!(
            apart(&integers, &numbers, &[C(1), L(7)], &[C(0)]),
            Apartness::Open,
            "`S(x)` is `Z` once `x` is `P(Z)`"
        );
        assert_eq!(
            apart(&integers, &numbers, &[C(2), C(1), L(7)], &[C(1), C(0)]),
            Apartness::Open,
            "the leaf survives `P(S(x))`'s rewrite to `x`"
        );
        let erasing = one(&[c(2), c(1), v(0)], &[c(0)]);
        assert_eq!(erasing.validate(&numbers), Ok(()));
        assert_eq!(
            apart(&erasing, &numbers, &[C(2), C(1), L(7)], &[C(1), C(0)]),
            Apartness::Apart,
            "a rule that erases the leaf leaves a closed normal form"
        );
        let forked = Presentation::new(SmallVec::<_, 0, Global>::from_iter([
            PresentedRule::new([c(1), c(2), v(0)].into(), [v(0)].into()),
            PresentedRule::new([c(1), c(2), v(0)].into(), [c(0)].into()),
        ]));
        assert_eq!(
            apart(&forked, &numbers, &[C(1), C(0)], &[C(0)]),
            Apartness::Diverges {
                outer: RuleIndex::from(0_usize),
                inner: RuleIndex::from(1_usize),
            },
            "normal forms of divergent rules are not elements"
        );
        let table = table();
        let marks = [C(3), L(1)];
        assert_eq!(
            apart(&circle(), &table, &marks, &[C(3), L(2)]),
            Apartness::Leaf,
            "two marks first differ at their fields of another type"
        );
        assert_eq!(apart(&circle(), &table, &marks, &marks), Apartness::Agree);
        assert_eq!(
            apart(&circle(), &table, &[C(1), C(1), C(0)], &[C(1), C(0)]),
            Apartness::Apart,
            "two words, the second letter against the empty word"
        );
        assert_eq!(
            apart(&Presentation::default(), &table, &[C(1), C(2), C(0)], &[C(
                0
            )]),
            Apartness::Apart,
            "a free type: constructors are disjoint, and nothing cancels"
        );
        let free = Presentation::default();
        assert_eq!(
            apart(&free, &numbers, &[C(1), L(7)], &[C(0)]),
            Apartness::Apart,
            "over a free type `S(x)` and `Z` differ at their heads whatever `x` is"
        );
        assert_eq!(
            apart(&free, &numbers, &[C(1), C(0)], &[C(1), C(1), L(7)]),
            Apartness::Apart,
            "`S(Z)` and `S(S(x))` differ below their shared head"
        );
        assert_eq!(
            apart(&free, &numbers, &[C(1), L(7)], &[C(1), C(0)]),
            Apartness::Open,
            "`S(x)` is `S(Z)` once `x` is `Z`"
        );
        assert_eq!(
            apart(&free, &numbers, &[L(7)], &[C(1), C(0)]),
            Apartness::Open,
            "a leaf at the root may be any term"
        );
        assert_eq!(
            apart(&free, &table, &marks, &[C(3), L(2)]),
            Apartness::Leaf,
            "a free type's marks first differ at their fields of another type"
        );
        let mut terms = Terms::default();
        let arities = [0_usize, 1, 1].map(FieldCount);
        let successor = terms.build(&[C(1), C(0)], &arities);
        let zero = terms.build(&[C(0)], &arities);
        let named = terms.build(&[R(successor)], &arities);
        let read =
            |terms: &Terms, at: Id, fields: &mut SmallVec<Id, 0, Global>| terms.read(at, fields);
        assert_eq!(
            integers.apart(&numbers, (named, zero), |at, fields| read(
                &terms, at, fields
            )),
            Apartness::Apart,
            "a reference to `S(Z)` unfolds where the type stands"
        );
        let later = Id(terms.0.len());
        terms.0.push(Stored::Defined(later));
        assert_eq!(
            integers.apart(&numbers, (later, zero), |at, fields| read(
                &terms, at, fields
            )),
            Apartness::Undecided,
            "a definition that refers to itself runs out of fuel"
        );
        let mark_table = super::tests::table();
        let marked = terms.build(&[C(3), R(zero)], &[0_usize, 1, 1, 1].map(FieldCount));
        let direct = Id(terms.0.len());
        terms.0.push(Stored::Constructor(
            3,
            SmallVec::<_, 0, Global>::from_iter([zero]),
        ));
        assert_eq!(
            circle().apart(&mark_table, (marked, direct), |at, fields| read(
                &terms, at, fields
            )),
            Apartness::Leaf,
            "a reference at a field of another type is a leaf, not unfolded to the term it names"
        );
    }
}
