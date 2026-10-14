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
//! checker and the kernel read `Path(T, a, a)` as the words at `a`, and what
//! the kernel re-mints the table and the rules from.
//!
//! **Alternatives.** A primitive word node with its own conversion would
//! duplicate the rewriting presented types already have; the cells on the
//! sort's own declaration would leave the words no admission position of
//! their own. **Reversal.** A cell between distinct terms takes words indexed
//! by their endpoints, a family over pairs of points rather than one type per
//! point.

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;

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
        table: &[Vec<RuleSlot<T>>],
    ) -> Result<Vec<RuleSlot<T>>, RuleFault>
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
    rules: Arc<[PresentedRule]>,
    /// The free cells a type of words is minted over; absent for every other
    /// presentation.
    cells: Option<Arc<FreeCells>>,
}

impl Presentation
{
    /// The presentation of `rules`, in written order; the free presentation
    /// when it is empty.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(rules: alloc::vec::Vec<PresentedRule>) -> Self
    {
        Self {
            rules: Arc::from(rules),
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
    /// # Adequacy
    /// - hypothesis: L3 — the circle's one cell mints its two cancellations.
    /// - witness: `presented::tests::a_cell_mints_its_words_and_its_cancellations`
    #[spec(captures: count = cells.cells().len(), ensures: |ret| ret.rules().len() == count.saturating_mul(2))]
    #[inline]
    #[must_use]
    pub fn words(cells: FreeCells) -> Self
    {
        Self {
            rules: Arc::from(cells.cancellations()),
            cells: Some(Arc::new(cells)),
        }
    }

    /// This presentation carrying `cells`, its rules as they were: a decoded
    /// type of words, whose rules the kernel compares with the mint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn carrying(
        self,
        cells: FreeCells,
    ) -> Self
    {
        Self {
            cells: Some(Arc::new(cells)),
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
    /// [`RuleSlot::Other`] with the field's classifier anywhere else.
    ///
    /// # Specification
    /// - requires: nothing — a rule may be arbitrary producer bytes.
    /// - ensures: `Ok(())` exactly when every rule's left side is headed by a
    ///   constructor, each side's constructors exist in `table` and consume
    ///   exactly the side's nodes by their arities, every constructor stands at
    ///   the root or at an [`RuleSlot::Own`] field, the left side's variables
    ///   read `0, 1, 2, …` in pre-order, every right-side variable occurs on
    ///   the left at the same slot and at most once on the right, and the right
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
    /// # Adequacy
    /// - hypothesis: L3 — the circle's two rules pass, and one rule per fault
    ///   is refused by that fault and no other.
    /// - witness: `presented::tests::validation_names_each_fault`
    #[spec(ensures: |ret| ret.as_ref().err().is_none_or(|refusal| usize::from(refusal.rule) < self.rules().len()))]
    #[inline]
    pub fn validate<T>(
        &self,
        table: &[Vec<RuleSlot<T>>],
    ) -> Result<(), RuleRefusal>
    where
        T: Copy + Eq,
    {
        for (index, rule) in self.rules().iter().enumerate() {
            let refuse = |fault| RuleRefusal {
                rule: RuleIndex(index),
                fault,
            };
            if !matches!(rule.left().first(), Some(&RuleNode::Constructor(_))) {
                return Err(refuse(RuleFault::VariableHeaded));
            }
            let left = read_side(rule.left(), table).map_err(refuse)?;
            let mut bound: Vec<RuleSlot<T>> = Vec::new();
            for &(variable, slot) in &left.variables {
                if usize::try_from(u32::from(variable)).ok() != Some(bound.len()) {
                    return Err(refuse(RuleFault::NonLinear));
                }
                bound.push(slot);
            }
            let right = read_side(rule.right(), table).map_err(refuse)?;
            let mut used = alloc::vec![false; bound.len()];
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
            if right.constructors >= left.constructors {
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
    /// # Specification
    /// - requires: `self` passed [`Self::validate`] against the table `arities`
    ///   counts; `term` is one well-formed pre-order term.
    /// - ensures: [`Normalized::Unchanged`] with `term` untouched when no rule
    ///   matches anywhere; otherwise [`Normalized::Rewritten`] with `term`
    ///   rewritten until no rule matches at any position. Each node compared or
    ///   copied costs one unit of `fuel`.
    /// - provides: the normal form both conversions compare a presented type's
    ///   terms by.
    /// - fails: [`Exhausted`] when `fuel` runs out first; `term` then holds
    ///   some intermediate term of the rewriting.
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
    /// # Adequacy
    /// - hypothesis: L3 — a circle word with nested inverse pairs normalizes to
    ///   its reduced word, a reduced word comes back unchanged, a leaf standing
    ///   for a variable is carried through a rewrite, and a starved fuel is
    ///   exhausted.
    /// - witness: `presented::tests::normalization_reduces_circle_words`
    #[spec(captures: before = fuel.0, ensures: |ret| fuel.0 <= before
        && (!matches!(ret, Err(Exhausted)) || fuel.0 == 0))]
    #[inline]
    pub fn normalize<C, L, F>(
        &self,
        arities: &[FieldCount],
        term: &mut Vec<RuleTerm<C, L>>,
        fresh: F,
        fuel: &mut RewriteFuel,
    ) -> Result<Normalized, Exhausted>
    where
        C: Copy,
        L: Copy,
        F: Fn(&C) -> C,
    {
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
                    let Matched::At { end, bindings } =
                        matched(term, TermPosition(start), rule.left(), arities, fuel)?
                    else {
                        continue;
                    };
                    let mut built = Vec::new();
                    for &node in rule.right() {
                        fuel.charge()?;
                        match node {
                            | RuleNode::Constructor(tag) => built.push(RuleTerm::Constructor {
                                tag,
                                arity: arities.get(usize::from(tag)).copied().unwrap_or_default(),
                                payload: fresh(&payload),
                            }),
                            | RuleNode::Variable(variable) => {
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
                    let _replaced = term.splice(start .. end, built);
                    outcome = Normalized::Rewritten;
                    continue 'rewrite;
                }
            }
            return Ok(outcome);
        }
    }
}

/// A free invertible 1-cell of a presented type's sort: a generator between
/// two closed terms of the sort, each a side over the sort's own constructor
/// table holding no variable.
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
    source: Box<[RuleNode]>,
    /// The cell's target, in pre-order.
    target: Box<[RuleNode]>,
}

impl FreeCell
{
    /// The cell from `source` to `target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        source: Box<[RuleNode]>,
        target: Box<[RuleNode]>,
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
    pub const fn source(&self) -> &[RuleNode]
    {
        &self.source
    }

    /// The target, in pre-order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn target(&self) -> &[RuleNode]
    {
        &self.target
    }
}

/// The free cells a type of words is minted over: the sort whose closed terms
/// they join, by its admission position, and the cells, one generator each, in
/// written order.
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
    /// The cells, in written order.
    cells: Box<[FreeCell]>,
}

impl FreeCells
{
    /// The cells `cells` of the sort admitted at `sort`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        sort: crate::term::ConstantIndex,
        cells: Vec<FreeCell>,
    ) -> Self
    {
        Self {
            sort,
            cells: cells.into_boxed_slice(),
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
    /// # Adequacy
    /// - hypothesis: L3 — the circle's one cell mints the landed circle's two
    ///   rules over tags 1 and 2.
    /// - witness: `presented::tests::a_cell_mints_its_words_and_its_cancellations`
    #[spec(ensures: |ret| ret.len() == self.cells.len().saturating_mul(2))]
    #[inline]
    #[must_use]
    pub fn cancellations(&self) -> Vec<PresentedRule>
    {
        let rest = RuleNode::Variable(RuleVariable(0));
        let mut rules = Vec::with_capacity(self.cells.len().saturating_mul(2));
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
        table: &[Vec<RuleSlot<T>>],
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

/// How many constructors a type of words takes.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstructorCount(usize);

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
    F: FnMut(RuleNode, Vec<T>) -> T,
{
    let mut built: Vec<T> = Vec::new();
    for &written in side.iter().rev() {
        let fields = match written {
            | RuleNode::Variable(_) => Vec::new(),
            | RuleNode::Constructor(tag) => {
                let arity = arities
                    .get(usize::from(tag))
                    .copied()
                    .ok_or(RuleFault::UnknownConstructor)?;
                let start = built
                    .len()
                    .checked_sub(usize::from(arity))
                    .ok_or(RuleFault::Arity)?;
                let mut fields = built.split_off(start);
                fields.reverse();
                fields
            },
        };
        built.push(node(written, fields));
    }
    match (built.pop(), built.is_empty()) {
        | (Some(root), true) => Ok(root),
        | (Some(_) | None, _) => Err(RuleFault::Arity),
    }
}

/// Where a constructor field stands, as a rule side reads it.
///
/// # Specification
/// - provides: the declaration's own type, where a constructor of the table may
///   stand, or another classifier, where only a variable may, compared by
///   identity.
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
    /// Another classifier.
    Other(T),
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
    fn charge(&mut self) -> Result<(), Exhausted>
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
    variables: Vec<(RuleVariable, RuleSlot<T>)>,
    /// How many constructors the side holds.
    constructors: usize,
}

/// Read one side against `table`, the root standing at the own type.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the side's variables with their slots and its constructor count
///   when the side is one term by the table's arities, every constructor at the
///   own type.
/// - provides: the per-side half of [`Presentation::validate`].
/// - fails: [`RuleFault::UnknownConstructor`], [`RuleFault::NotOwnPosition`] or
///   [`RuleFault::Arity`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `for` loop over the side's nodes, not recursion.
/// - measure: the nodes left.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::validate`].
/// - witness: `presented::tests::validation_names_each_fault`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|reading| reading.constructors.saturating_add(reading.variables.len()) == side.len())
    || matches!(ret, Err(RuleFault::UnknownConstructor | RuleFault::NotOwnPosition | RuleFault::Arity)))]
fn read_side<T>(
    side: &[RuleNode],
    table: &[Vec<RuleSlot<T>>],
) -> Result<SideReading<T>, RuleFault>
where
    T: Copy + Eq,
{
    let mut expected = Vec::from([RuleSlot::Own]);
    let mut reading = SideReading {
        variables: Vec::new(),
        constructors: 0,
    };
    for &node in side {
        let slot = expected.pop().ok_or(RuleFault::Arity)?;
        match node {
            | RuleNode::Constructor(tag) => {
                let fields = table
                    .get(usize::from(tag))
                    .ok_or(RuleFault::UnknownConstructor)?;
                if slot != RuleSlot::Own {
                    return Err(RuleFault::NotOwnPosition);
                }
                expected.extend(fields.iter().rev().copied());
                reading.constructors = reading.constructors.saturating_add(1);
            },
            | RuleNode::Variable(variable) => reading.variables.push((variable, slot)),
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
        /// Each variable's span, in variable order.
        bindings: Vec<(usize, usize)>,
    },
}

/// Match the linear pattern `left` at `start` in `term`.
///
/// # Specification
/// - requires: `left` is a validated left side, its variables in order.
/// - ensures: [`Matched::At`] when every constructor of `left` meets a
///   constructor of `term` with its tag and its table arity, each variable
///   binding the subterm standing where it does; [`Matched::No`] otherwise.
///   Each pattern node and each node a variable's span walks costs one unit.
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
    let mut bindings = Vec::new();
    for &node in left {
        fuel.charge()?;
        match (node, term.get(at)) {
            | (RuleNode::Constructor(wanted), Some(&RuleTerm::Constructor { tag, arity, .. }))
                if wanted == tag && arities.get(usize::from(tag)) == Some(&arity) =>
            {
                at = at.saturating_add(1);
            },
            | (RuleNode::Variable(_), Some(_)) => {
                let from = at;
                let mut owed = 1_usize;
                while let Some(next) = owed.checked_sub(1) {
                    fuel.charge()?;
                    owed = match term.get(at) {
                        | Some(&RuleTerm::Constructor { arity, .. }) => {
                            next.saturating_add(usize::from(arity))
                        },
                        | Some(&RuleTerm::Leaf(_)) => next,
                        | None => return Ok(Matched::No),
                    };
                    at = at.saturating_add(1);
                }
                bindings.push((from, at));
            },
            | (RuleNode::Constructor(_) | RuleNode::Variable(_), _) => return Ok(Matched::No),
        }
    }
    Ok(Matched::At { end: at, bindings })
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use super::CellFault;
    use super::Exhausted;
    use super::FieldCount;
    use super::FreeCell;
    use super::FreeCells;
    use super::Normalized;
    use super::Presentation;
    use super::PresentedRule;
    use super::RewriteFuel;
    use super::RuleFault;
    use super::RuleIndex;
    use super::RuleNode;
    use super::RuleRefusal;
    use super::RuleSlot;
    use super::RuleTerm;
    use super::RuleVariable;
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

    /// `base`, `loop(x)`, `unloop(x)` and a constructor `mark(n)` over another
    /// type, as validation reads their fields.
    ///
    /// # Specification
    /// trivial.
    fn table() -> Vec<Vec<RuleSlot<Classifier>>>
    {
        alloc::vec![
            alloc::vec![],
            alloc::vec![RuleSlot::Own],
            alloc::vec![RuleSlot::Own],
            alloc::vec![RuleSlot::Other(Classifier::Integer)],
        ]
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
        Presentation::new(alloc::vec![PresentedRule::new(left.into(), right.into())])
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
        Presentation::new(alloc::vec![
            PresentedRule::new([looped, unlooped, x].into(), [x].into()),
            PresentedRule::new([unlooped, looped, x].into(), [x].into()),
        ])
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
        ] {
            assert_eq!(
                one(left, right).validate(&table),
                refused(fault),
                "{fault:?}"
            );
        }
        let doubled = Presentation::new(alloc::vec![PresentedRule::new(
            [c(1), c(2), c(1), v(0)].into(),
            [c(1), v(0)].into(),
        )]);
        assert_eq!(doubled.validate(&table), Ok(()));
        let duplicated = Presentation::new(alloc::vec![
            PresentedRule::new([c(1), c(2), v(0)].into(), [v(0)].into()),
            PresentedRule::new([c(1), c(1), c(1), v(0)].into(), [c(2), v(0), v(0)].into()),
        ]);
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
        let base =
            || alloc::boxed::Box::from([RuleNode::Constructor(ConstructorTag::from(0_usize))]);
        let sort = crate::term::ConstantIndex::from(3_usize);
        let cells = FreeCells::new(sort, alloc::vec![FreeCell::new(base(), base())]);
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
            Presentation::new(circle().rules().to_vec()).carrying(cells),
            words,
            "the decoder's rules and cells are the mint's"
        );
        let twice = FreeCells::new(sort, alloc::vec![
            FreeCell::new(base(), base()),
            FreeCell::new(base(), base())
        ]);
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
                    .map(|&(source, target)| FreeCell::new(source.into(), target.into()))
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
            let mut term: Vec<RuleTerm<Letter, Point>> = letters
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
        let built = Presentation::new(alloc::vec![PresentedRule::new(
            [c(1), c(2), c(1), x].into(),
            [c(1), x].into(),
        )]);
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

    #[test]
    fn a_rule_side_builds_bottom_up_over_its_variables()
    {
        let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let v = |ordinal: u32| RuleNode::Variable(RuleVariable::from(ordinal));
        let shown = |node: RuleNode, fields: Vec<String>| match node {
            | RuleNode::Variable(variable) => alloc::format!("x{}", u32::from(variable)),
            | RuleNode::Constructor(tag) => {
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
        let own = alloc::vec![RuleSlot::<u8>::Own];
        let table = [alloc::vec![], own.clone(), own.clone(), alloc::vec![
            RuleSlot::Other(7_u8)
        ]];
        assert_eq!(cancellation.slots(&table), Ok(own));
        let marked = PresentedRule::new([c(1), c(3), v(0)].into(), [c(0)].into());
        assert_eq!(
            marked.slots(&table),
            Ok(alloc::vec![RuleSlot::Other(7_u8)]),
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
}
