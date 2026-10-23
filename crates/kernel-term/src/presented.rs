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
        // One binding table and one use mask, refilled per rule.
        let (mut bound, mut used): (Vec<RuleSlot<T>>, Vec<bool>) = (Vec::new(), Vec::new());
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
            used.resize(bound.len(), false);
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
                    let _replaced = term.splice(start .. end, built);
                    outcome = Normalized::Rewritten;
                    continue 'rewrite;
                }
            }
            return Ok(outcome);
        }
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
    /// - ensures: [`Convergence::Converges`] exactly when every critical pair's
    ///   two sides normalize to one term; otherwise [`Convergence::Diverges`]
    ///   naming the first pair that does not, in written order of the
    ///   overlapped rule, the position and the overlapping rule. Each node
    ///   unified, built, compared or copied costs one unit of `fuel`.
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
    ///   named in order; a rule overlapping itself below its root is checked.
    /// - witness: `presented::tests::critical_pairs_decide_convergence`
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
        table: &[Vec<RuleSlot<T>>],
        (left, right): (V, V),
        mut read: R,
    ) -> Apartness
    where
        T: Copy + Eq,
        V: Copy + Eq,
        R: FnMut(V, &mut Vec<V>) -> TermReading<V>,
    {
        let arities: Vec<FieldCount> = table
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
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::apart`].
/// - witness: `presented::tests::apartness_is_decided_by_normal_forms`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |term| !term.is_empty()))]
fn flatten<T, V, R>(
    table: &[Vec<RuleSlot<T>>],
    root: V,
    read: &mut R,
    fuel: &mut RewriteFuel,
) -> Result<FlatTerm<V>, Exhausted>
where
    T: Copy + Eq,
    V: Copy + Eq,
    R: FnMut(V, &mut Vec<V>) -> TermReading<V>,
{
    let mut term = Vec::new();
    let mut fields = Vec::new();
    let mut pending = Vec::from([(root, RuleSlot::<T>::Own)]);
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
    (table, arities): (&[Vec<RuleSlot<T>>], &[FieldCount]),
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
    table: &[Vec<RuleSlot<T>>],
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
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::apart`].
/// - witness: `presented::tests::apartness_is_decided_by_normal_forms`
#[spec(ensures: |ret| !term.is_empty() || ret == Closure::Open)]
fn closure<T, C, L>(
    table: &[Vec<RuleSlot<T>>],
    term: &[RuleTerm<C, L>],
) -> Closure
where
    T: Copy + Eq,
{
    let mut expected = Vec::from([RuleSlot::Own]);
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
type FlatTerm<L> = Vec<RuleTerm<(), L>>;

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
    let mut outer_bound: Vec<(RuleVariable, PairTerm)> = Vec::new();
    let mut inner_bound: Vec<(RuleVariable, PairTerm)> = Vec::new();
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
    let mut term = Vec::with_capacity(nodes.len());
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
            RuleNode::Variable(_) => Vec::new(),
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
/// # Adequacy
/// - hypothesis: L3 — as [`Presentation::validate`].
/// - witness: `presented::tests::validation_names_each_fault`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|reading| reading.constructors.saturating_add(reading.variables.len()) == side.len())
    || matches!(ret, Err(RuleFault::UnknownConstructor | RuleFault::NotOwnPosition | RuleFault::DependentSlot | RuleFault::Arity)))]
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
            (RuleNode::Constructor(wanted), Some(&RuleTerm::Constructor { tag, arity, .. }))
                if wanted == tag && arities.get(usize::from(tag)) == Some(&arity) =>
            {
                at = at.saturating_add(1);
            },
            (RuleNode::Variable(_), Some(_)) => {
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
                bindings.push((from, at));
            },
            (RuleNode::Constructor(_) | RuleNode::Variable(_), _) => return Ok(Matched::No),
        }
    }
    Ok(Matched::At { end: at, bindings })
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

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
    use super::RewriteFuel;
    use super::RuleFault;
    use super::RuleIndex;
    use super::RuleNode;
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
    fn table() -> Vec<Vec<RuleSlot<Classifier>>>
    {
        alloc::vec![
            alloc::vec![],
            alloc::vec![RuleSlot::Own],
            alloc::vec![RuleSlot::Own],
            alloc::vec![RuleSlot::Other(Classifier::Integer)],
            alloc::vec![RuleSlot::Own, RuleSlot::Dependent],
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
            (&[c(4), v(0), v(1)], &[v(0)], RuleFault::DependentSlot),
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
        Constructor(usize, Vec<Id>),
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
    struct Terms(Vec<Stored>);

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
            let mut built: Vec<Id> = Vec::new();
            for &node in nodes.iter().rev() {
                let stored =
                    match node {
                        Node::C(tag) => {
                            let mut fields = Vec::new();
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
            fields: &mut Vec<Id>,
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
    fn integers() -> (Vec<Vec<RuleSlot<Classifier>>>, Presentation)
    {
        let successor = RuleNode::Constructor(ConstructorTag::from(1_usize));
        let predecessor = RuleNode::Constructor(ConstructorTag::from(2_usize));
        let x = RuleNode::Variable(RuleVariable::from(0_u32));
        (
            alloc::vec![alloc::vec![], alloc::vec![RuleSlot::Own], alloc::vec![
                RuleSlot::Own
            ],],
            Presentation::new(alloc::vec![
                PresentedRule::new([successor, predecessor, x].into(), [x].into()),
                PresentedRule::new([predecessor, successor, x].into(), [x].into()),
            ]),
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
        let forked = Presentation::new(alloc::vec![
            PresentedRule::new([c(1), c(2), v(0)].into(), [v(0)].into()),
            PresentedRule::new([c(1), c(2), v(0)].into(), [c(0)].into()),
        ]);
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
                         table: &[Vec<RuleSlot<Classifier>>],
                         left: &[Node],
                         right: &[Node]| {
            let arities: Vec<FieldCount> = table
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
        let forked = Presentation::new(alloc::vec![
            PresentedRule::new([c(1), c(2), v(0)].into(), [v(0)].into()),
            PresentedRule::new([c(1), c(2), v(0)].into(), [c(0)].into()),
        ]);
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
        let read = |terms: &Terms, at: Id, fields: &mut Vec<Id>| terms.read(at, fields);
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
        terms.0.push(Stored::Constructor(3, alloc::vec![zero]));
        assert_eq!(
            circle().apart(&mark_table, (marked, direct), |at, fields| read(
                &terms, at, fields
            )),
            Apartness::Leaf,
            "a reference at a field of another type is a leaf, not unfolded to the term it names"
        );
    }
}
