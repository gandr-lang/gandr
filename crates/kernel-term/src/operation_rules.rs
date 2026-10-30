//! An operation's rules: the rewrite rules a definition carries beside the
//! body its operation lowered to, and the decision that they converge.
//!
//! A `data` or `sign` block's operation is written as rules, `add(Zero, n)
//! ==> n`, and lowers to a function whose first matching rule fires. Read as
//! equations, the rules mean one thing whichever rule fires first exactly when
//! they terminate and every critical pair joins: every strategy then reaches
//! the one normal form. The definition the operation lowers to carries its
//! rules ([`OperationRules`]), and the kernel decides that itself
//! ([`OperationRules::converge`]).
//!
//! A side is a pre-order sequence of [`OperationNode`]s, as a presented type's
//! side is: an operation, the admitted definition at its position applied to
//! the next subterms its arity counts; a constructor of an admitted data
//! declaration; the results of a many-output operation; or a pattern variable.
//! A left side is the operation's own call over linear patterns, its
//! variables numbered by first occurrence; a right side reuses them any number
//! of times. A pattern is constructors, variables and calls. A rule whose left
//! side holds a call, `add(add(m, n), k) ==> add(m, add(n, k))`, is a law of
//! the operation: it is never an arm of the first-match function, whose inputs
//! are constructor terms, and convergence makes it hold of that function.
//!
//! The decision has three parts. Termination is the lexicographic path order
//! of [`gandr_theory_path_orders::lpo`] over each rule, its derivation
//! replayed, with an operation above every operation admitted before it and
//! above every constructor and results tuple; an operation calls only itself
//! and operations admitted before it, so the precedence is the admission
//! order. The critical pairs are every two rules whose left sides unify at the
//! root, every rule of a presented type that unifies with a constructor
//! pattern below the root, and every rule of an operation that unifies with a
//! call of it below the root; the kernel enumerates them by unification of
//! linear patterns. Both reducts of each pair normalize under
//! the operation's rules, the rules of every operation they reach and the
//! rules of every presented type their constructors belong to, and their
//! normal forms must be one term. Fuel bounds the work, and a pair the fuel
//! leaves undecided is refused.

use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::convert::Infallible;

use anodized::spec;
use gandr_theory_path_orders::Evidence;
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
use gandr_theory_path_orders::lpo::Replay;

use crate::presented::Exhausted;
use crate::presented::FieldCount;
use crate::presented::Presentation;
use crate::presented::RewriteFuel;
use crate::presented::RuleIndex;
use crate::presented::RuleNode;
use crate::presented::RuleVariable;
use crate::term::ConstantIndex;
use crate::term::ConstructorTag;

/// One node of an operation rule's side, in pre-order.
///
/// # Specification
/// - provides: an operation applied to the next subterms its arity counts, a
///   constructor of a data declaration applied to its fields, a results tuple
///   of a many-output operation, or a pattern variable.
/// - panics: none.
/// - executable: none — data declaration; arity and scope are the kernel's
///   admission obligations.
///
/// # Adequacy
/// - hypothesis: L3 — a definition carrying rules round-trips through the wire
///   with every node of both sides in order.
/// - witness: `encode::tests::a_ruled_definition_closes_its_segment_with_its_rules`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OperationNode
{
    /// The definition admitted at `constant`, or the ruled definition itself,
    /// applied to the next `arity` subterms.
    Operation
    {
        /// The definition's position.
        constant: ConstantIndex,
        /// How many subterms follow it as its arguments.
        arity: FieldCount,
    },
    /// The constructor `tag` of the data declaration at `family`, applied to
    /// the next subterms its field count names.
    Constructor
    {
        /// The data declaration's position.
        family: ConstantIndex,
        /// The constructor's tag in its table.
        tag: ConstructorTag,
    },
    /// The results of a many-output operation, the next subterms in port
    /// order.
    Results(FieldCount),
    /// A pattern variable.
    Variable(RuleVariable),
}

/// One oriented rule `left ==> right` of an operation.
///
/// # Specification
/// - provides: the producer's two sides, unchecked; admission owns their
///   well-formedness.
/// - panics: none.
/// - executable: none — data declaration.
///
/// # Adequacy
/// - hypothesis: L3 — as [`OperationNode`].
/// - witness: `encode::tests::a_ruled_definition_closes_its_segment_with_its_rules`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct OperationRule
{
    /// The left side, in pre-order: the operation's call over patterns.
    left: Box<[OperationNode]>,
    /// The right side, in pre-order: what the call rewrites to.
    right: Box<[OperationNode]>,
}

impl OperationRule
{
    /// The rule rewriting `left` to `right`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        left: Box<[OperationNode]>,
        right: Box<[OperationNode]>,
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
    pub fn left(&self) -> &[OperationNode]
    {
        &self.left
    }

    /// The right side, in pre-order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn right(&self) -> &[OperationNode]
    {
        &self.right
    }
}

/// A definition's rules, in the order the producer wrote them, shared.
///
/// Empty for every definition no operation lowered to, and for every
/// declaration that is not a definition.
///
/// # Specification
/// - provides: the rule table one operation reads, cheap to clone into every
///   admission that calls it.
/// - panics: none.
/// - executable: none — data declaration.
///
/// # Adequacy
/// - hypothesis: L3 — as [`OperationNode`].
/// - witness: `encode::tests::a_ruled_definition_closes_its_segment_with_its_rules`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct OperationRules(Arc<[OperationRule]>);

/// Why an operation's rule is refused.
///
/// # Specification
/// - provides: the first fault of the first refused rule, or the pair that does
///   not join.
/// - panics: none.
/// - executable: none — data declaration.
///
/// # Adequacy
/// - hypothesis: L3 — as [`OperationRules::converge`].
/// - witness: `operation_rules::tests::a_malformed_rule_is_refused_by_its_fault`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OperationRuleFault
{
    /// The left side is not the operation's own call at the arity its first
    /// rule states.
    Head,
    /// The left side's arguments hold a results tuple: a pattern is
    /// constructors, variables and calls.
    NotAPattern,
    /// A results tuple stands below a right side's root.
    Results,
    /// A constructor names no constructor of an admitted data declaration.
    UnknownConstructor,
    /// An operation names neither the ruled definition nor a ruled definition
    /// admitted before it, or calls it at another arity.
    UnknownOperation,
    /// A side is not one term: its nodes run out, or some are left over.
    Arity,
    /// The left side repeats a variable or skips one in pre-order.
    NonLinear,
    /// The right side names a variable the left side does not bind.
    Unbound,
    /// The path order does not put the left side above the right.
    Unoriented,
    /// The rule and the one named rewrite one term to two normal forms.
    Diverges(Overlapped),
    /// A reduct of the rule's pair with the one named reaches no normal form
    /// within the fuel.
    Undecided(Overlapped),
}

/// The other rule of a critical pair.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Overlapped
{
    /// A rule of the same operation: an earlier one overlapping at the root,
    /// or any one overlapping a call of the operation below the root.
    Operation(RuleIndex),
    /// A rule of the presented type at `family`, overlapping a pattern below
    /// the root.
    Presented
    {
        /// The presented type's position.
        family: ConstantIndex,
        /// The rule's position in its presentation.
        rule: RuleIndex,
    },
    /// A rule of the ruled definition at `constant`, admitted before,
    /// overlapping a call of it below the root.
    Called
    {
        /// The called definition's position.
        constant: ConstantIndex,
        /// The rule's position among its rules.
        rule: RuleIndex,
    },
}

/// The first rule an operation's rules are refused at, and why.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OperationRuleRefusal
{
    /// The rule, by written position.
    pub rule: RuleIndex,
    /// Its first fault.
    pub fault: OperationRuleFault,
}

/// What a convergence decision reads of the declarations admitted before the
/// ruled definition.
///
/// # Specification
/// - provides: each data declaration's constructor arities and presentation,
///   and each ruled definition's rules, by position.
/// - panics: none.
/// - executable: none — an interface; the kernel and the tests implement it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`OperationRules::converge`].
/// - witness: `operation_rules::tests::two_overlapping_rules_that_join_converge`
pub trait RuleScope
{
    /// The field count of constructor `tag` of the data declaration at
    /// `family`; none when there is no such constructor.
    ///
    /// # Specification
    /// trivial.
    fn fields(
        &self,
        family: ConstantIndex,
        tag: ConstructorTag,
    ) -> Option<FieldCount>;

    /// The presentation of the data declaration at `family`; none when
    /// `family` is no data declaration.
    ///
    /// # Specification
    /// trivial.
    fn presentation(
        &self,
        family: ConstantIndex,
    ) -> Option<&Presentation>;

    /// The rules of the definition at `constant`; none when it carries none.
    ///
    /// # Specification
    /// trivial.
    fn rules(
        &self,
        constant: ConstantIndex,
    ) -> Option<&OperationRules>;
}

impl OperationRules
{
    /// The rules `rules`, in written order; none for a definition that is no
    /// operation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(rules: Vec<OperationRule>) -> Self
    {
        Self(Arc::from(rules))
    }

    /// The rules, in written order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rules(&self) -> &[OperationRule]
    {
        &self.0
    }

    /// The arity of the operation the rules define: the arity its first
    /// rule's head states; none for no rules or a first rule with no
    /// operation at its head.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arity(&self) -> Option<FieldCount>
    {
        match *self.0.first()?.left.first()? {
            OperationNode::Operation { arity, .. } => Some(arity),
            OperationNode::Constructor { .. }
            | OperationNode::Results(_)
            | OperationNode::Variable(_) => None,
        }
    }

    /// Decide that the rules of the definition admitted at `own` converge
    /// over `scope`: each rule well formed, oriented by the path order, and
    /// every critical pair joined.
    ///
    /// # Specification
    /// - requires: nothing — the rules may be arbitrary producer bytes, and
    ///   `scope` answers for the declarations admitted below `own`.
    /// - ensures: `Ok(())` exactly when every rule's left side is `own`'s call
    ///   at the first rule's arity over linear patterns of constructors,
    ///   variables and calls, every side is one term whose constructors `scope`
    ///   knows and whose operations are `own` at that arity or a ruled
    ///   definition below `own` at its arity, a results tuple stands only at a
    ///   right side's root, every right-side variable is bound on the left, the
    ///   path order puts each left side above its right, and both reducts of
    ///   every critical pair normalize to one term within `fuel`. Otherwise the
    ///   first refused rule, in written order, and its fault; a pair is
    ///   reported at its later rule, or at the rule holding the call it
    ///   overlaps.
    /// - provides: the kernel's own decision that an operation's rules read as
    ///   equations mean what its first-match function computes.
    /// - fails: as `- ensures:`.
    /// - panics: none.
    /// - measure: the rules, then the pairs, each normalization bounded by
    ///   `fuel`.
    ///
    /// # Errors
    /// The first refused rule and its fault.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two overlapping rules that join converge, the same
    ///   pair rewriting apart is refused at the later rule naming the earlier,
    ///   a growing rule is unoriented, an orthogonal recursive operation over
    ///   an earlier one converges, a pattern overlapping a presented type's
    ///   rule is decided against it, a law over a call of its own operation or
    ///   an earlier one converges, a law parting from a rule at its call is
    ///   refused naming that rule, and each malformation is named.
    /// - witness: `operation_rules::tests::two_overlapping_rules_that_join_converge`
    /// - witness: `operation_rules::tests::two_overlapping_rules_that_part_are_refused_at_the_later`
    /// - witness: `operation_rules::tests::a_growing_rule_is_unoriented`
    /// - witness: `operation_rules::tests::an_operation_over_an_earlier_one_converges`
    /// - witness: `operation_rules::tests::a_pattern_below_a_presented_rule_is_decided_against_it`
    /// - witness: `operation_rules::tests::a_malformed_rule_is_refused_by_its_fault`
    /// - witness: `operation_rules::tests::a_law_over_its_own_call_converges_1510`
    /// - witness: `operation_rules::tests::a_law_parting_at_its_call_is_refused_1510`
    /// - witness: `operation_rules::tests::a_law_over_an_earlier_call_is_decided_against_its_rules_1510`
    #[spec(ensures: |ret| ret.as_ref().err().is_none_or(|refusal| usize::from(refusal.rule) < self.0.len()))]
    #[inline]
    pub fn converge<S>(
        &self,
        own: ConstantIndex,
        scope: &S,
        fuel: &mut RewriteFuel,
    ) -> Result<(), OperationRuleRefusal>
    where
        S: RuleScope,
    {
        let Some(arity) = self.arity()
        else {
            return if self.0.is_empty() {
                Ok(())
            }
            else {
                Err(refusal(RuleIndex::from(0_usize), OperationRuleFault::Head))
            };
        };
        let reader = Reader {
            own: (own, arity),
            scope,
        };
        for (index, rule) in self.0.iter().enumerate() {
            reader
                .validate(rule)
                .map_err(|fault| refusal(RuleIndex::from(index), fault))?;
        }
        let mut order = Buffers::default();
        for (index, rule) in self.0.iter().enumerate() {
            if reader.path_greater(&rule.left, &rule.right, &mut order) == Placement::NotAbove {
                return Err(refusal(
                    RuleIndex::from(index),
                    OperationRuleFault::Unoriented,
                ));
            }
        }
        let system = reader.system(self);
        let mut scratch = Scratch::default();
        for (later, rule) in self.0.iter().enumerate() {
            for (earlier, other) in self.0.iter().enumerate().take(later) {
                if reader.root_pair(other, rule, &mut scratch).is_none() {
                    continue;
                }
                reader.join(&system, fuel, &mut scratch).map_err(|joined| {
                    refusal(
                        RuleIndex::from(later),
                        joined.fault(Overlapped::Operation(RuleIndex::from(earlier))),
                    )
                })?;
            }
            for &(family, ref presentation) in &system.presentations {
                for (index, presented) in presentation.iter().enumerate() {
                    for (at, &node) in rule.left.iter().enumerate().skip(1) {
                        let below = matches!(node, OperationNode::Constructor { family: owner, .. } if owner == family);
                        if !below
                            || reader
                                .interior_pair(rule, presented, Position(at), &mut scratch)
                                .is_none()
                        {
                            continue;
                        }
                        reader.join(&system, fuel, &mut scratch).map_err(|joined| {
                            refusal(
                                RuleIndex::from(later),
                                joined.fault(Overlapped::Presented {
                                    family,
                                    rule: RuleIndex::from(index),
                                }),
                            )
                        })?;
                    }
                }
            }
            for (at, &node) in rule.left.iter().enumerate().skip(1) {
                let OperationNode::Operation { constant, .. } = node
                else {
                    continue;
                };
                let called = if constant == own {
                    Some(self)
                }
                else {
                    scope.rules(constant)
                };
                for (index, other) in called
                    .into_iter()
                    .flat_map(|called| called.0.iter())
                    .enumerate()
                {
                    if reader
                        .interior_pair(rule, other, Position(at), &mut scratch)
                        .is_none()
                    {
                        continue;
                    }
                    let overlapped = if constant == own {
                        Overlapped::Operation(RuleIndex::from(index))
                    }
                    else {
                        Overlapped::Called {
                            constant,
                            rule: RuleIndex::from(index),
                        }
                    };
                    reader.join(&system, fuel, &mut scratch).map_err(|joined| {
                        refusal(RuleIndex::from(later), joined.fault(overlapped))
                    })?;
                }
            }
        }
        Ok(())
    }
}

/// The refusal of the rule at `index` for `fault`.
///
/// # Specification
/// trivial.
const fn refusal(
    index: RuleIndex,
    fault: OperationRuleFault,
) -> OperationRuleRefusal
{
    OperationRuleRefusal { rule: index, fault }
}

/// Why a pair did not join.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Unjoined
{
    /// The two normal forms differ.
    Apart,
    /// A normalization ran out of fuel.
    Exhausted,
}

impl Unjoined
{
    /// The fault this is against `other`.
    ///
    /// # Specification
    /// trivial.
    const fn fault(
        self,
        other: Overlapped,
    ) -> OperationRuleFault
    {
        match self {
            Self::Apart => OperationRuleFault::Diverges(other),
            Self::Exhausted => OperationRuleFault::Undecided(other),
        }
    }
}

impl From<Exhausted> for Unjoined
{
    /// A normalization that ran out of fuel.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(_exhausted: Exhausted) -> Self
    {
        Self::Exhausted
    }
}

/// The buffers a decision reuses from pair to pair.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Scratch
{
    /// The left reduct of the pair being decided.
    left: Vec<OperationNode>,
    /// The right reduct of the pair being decided.
    right: Vec<OperationNode>,
    /// A term being rewritten into.
    rewritten: Vec<OperationNode>,
    /// The first side's variable bindings.
    first: Vec<Binding>,
    /// The second side's variable bindings.
    second: Vec<Binding>,
}

/// What a variable of one side of a unification is bound to.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binding
{
    /// Nothing: it stays a variable of the peak.
    Free,
    /// The other side's subterm from the first position to the second.
    Other(Position, Position),
}

/// A node's position in a side or a term, in pre-order.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Position(usize);

impl Position
{
    /// The position after this one; none past the address space.
    ///
    /// # Specification
    /// trivial.
    fn next(self) -> Option<Self>
    {
        self.0.checked_add(1).map(Self)
    }
}

/// A pattern variable's ordinal, a count of variables, or an offset added to
/// ordinals.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Ordinal(usize);

/// Whether one term lies above another in the path order or its precedence.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Placement
{
    /// It lies above.
    Above,
    /// It does not: below, equal or incomparable.
    NotAbove,
}

/// The rules a normalization rewrites by: the operation's own, those of every
/// operation they call, and the presented rules of every family they build.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct System
{
    /// Every operation rule, each as its two sides.
    rules: Vec<OperationRule>,
    /// Every presented family read, with its rules over operation nodes.
    presentations: Vec<(ConstantIndex, Vec<OperationRule>)>,
}

/// One decision's view of the ruled definition and what is admitted below it.
///
/// # Specification
/// trivial.
struct Reader<'scope, S>
{
    /// The ruled definition's position and arity.
    own: (ConstantIndex, FieldCount),
    /// The declarations admitted below it.
    scope: &'scope S,
}

impl<S> Reader<'_, S>
where
    S: RuleScope,
{
    /// How many subterms `node` heads; none for a constructor `scope` does
    /// not know.
    ///
    /// # Specification
    /// trivial.
    fn arity(
        &self,
        node: OperationNode,
    ) -> Option<FieldCount>
    {
        match node {
            OperationNode::Operation { arity, .. } | OperationNode::Results(arity) => Some(arity),
            OperationNode::Constructor { family, tag } => self.scope.fields(family, tag),
            OperationNode::Variable(_) => Some(FieldCount::from(0_usize)),
        }
    }

    /// One past the last node of the subterm at `at`; none when the nodes run
    /// out or a constructor is unknown.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some(end)` with `at < end <= side.len()` exactly when the
    ///   nodes from `at` hold one whole term by their arities.
    /// - panics: none.
    /// - measure: the nodes scanned.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OperationRules::converge`].
    /// - witness: `operation_rules::tests::a_malformed_rule_is_refused_by_its_fault`
    #[spec(ensures: |ret| ret.is_none_or(|end| at < end && end.0 <= side.len()))]
    fn extent(
        &self,
        side: &[OperationNode],
        at: Position,
    ) -> Option<Position>
    {
        let mut next = at;
        let mut owed = 1_usize;
        while let Some(left) = owed.checked_sub(1) {
            let &node = side.get(next.0)?;
            owed = left.checked_add(usize::from(self.arity(node)?))?;
            next = next.next()?;
        }
        Some(next)
    }

    /// Check that `constant` at `stated` arguments names the ruled definition
    /// at its arity, or a ruled definition admitted before it at its own.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`OperationRuleFault::UnknownOperation`] otherwise.
    fn known(
        &self,
        constant: ConstantIndex,
        stated: FieldCount,
    ) -> Result<(), OperationRuleFault>
    {
        let (own, arity) = self.own;
        let known = if constant == own {
            stated == arity
        }
        else {
            constant < own
                && self.scope.rules(constant).and_then(OperationRules::arity) == Some(stated)
        };
        if known {
            Ok(())
        }
        else {
            Err(OperationRuleFault::UnknownOperation)
        }
    }

    /// The first fault of `rule`, or none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`OperationRules::converge`]'s well-formedness clause, for
    ///   one rule.
    /// - panics: none.
    /// - executable: none — the fault is the body's own classification of the
    ///   rule; the witness pins each.
    ///
    /// # Errors
    /// The rule's first fault, in the order the clauses are listed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OperationRules::converge`].
    /// - witness: `operation_rules::tests::a_malformed_rule_is_refused_by_its_fault`
    fn validate(
        &self,
        rule: &OperationRule,
    ) -> Result<(), OperationRuleFault>
    {
        let (own, arity) = self.own;
        match rule.left.first() {
            Some(&OperationNode::Operation {
                constant,
                arity: stated,
            }) if constant == own && stated == arity => {},
            _ => return Err(OperationRuleFault::Head),
        }
        let mut bound = 0_usize;
        for &node in rule.left.iter().skip(1) {
            match node {
                OperationNode::Constructor { family, tag } => {
                    if self.scope.fields(family, tag).is_none() {
                        return Err(OperationRuleFault::UnknownConstructor);
                    }
                },
                OperationNode::Variable(variable) => {
                    if usize::try_from(u32::from(variable)).ok() != Some(bound) {
                        return Err(OperationRuleFault::NonLinear);
                    }
                    bound = bound.saturating_add(1);
                },
                OperationNode::Operation {
                    constant,
                    arity: stated,
                } => self.known(constant, stated)?,
                OperationNode::Results(_) => return Err(OperationRuleFault::NotAPattern),
            }
        }
        if self.extent(&rule.left, Position(0)) != Some(Position(rule.left.len())) {
            return Err(OperationRuleFault::Arity);
        }
        for (position, &node) in rule.right.iter().enumerate() {
            match node {
                OperationNode::Operation {
                    constant,
                    arity: stated,
                } => self.known(constant, stated)?,
                OperationNode::Constructor { family, tag } => {
                    if self.scope.fields(family, tag).is_none() {
                        return Err(OperationRuleFault::UnknownConstructor);
                    }
                },
                OperationNode::Results(_) => {
                    if position != 0 {
                        return Err(OperationRuleFault::Results);
                    }
                },
                OperationNode::Variable(variable) => {
                    if usize::try_from(u32::from(variable)).is_ok_and(|ordinal| ordinal >= bound) {
                        return Err(OperationRuleFault::Unbound);
                    }
                },
            }
        }
        if self.extent(&rule.right, Position(0)) != Some(Position(rule.right.len())) {
            return Err(OperationRuleFault::Arity);
        }
        Ok(())
    }

    /// Whether the path order of [`gandr_theory_path_orders::lpo`] over the
    /// admission order ([`AdmissionOrder`]) puts `left` above `right`, its
    /// derivation replayed.
    ///
    /// # Specification
    /// - requires: both sides are one term each by their arities.
    /// - ensures: above exactly when the order orients the pair and its
    ///   derivation replays: a variable lies below a term that holds it and
    ///   differs from it; a term lies above another when one of its arguments
    ///   equals or lies above it, or when it covers every argument of the other
    ///   and either its head precedes the other's or the heads agree and its
    ///   arguments lie lexicographically above the other's.
    /// - panics: none.
    /// - executable: none — restating the order would recompute the table it
    ///   fills; the witnesses pin both answers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — recursion on a descending argument is oriented, a
    ///   rule rebuilding its own call or growing its argument is not, and a
    ///   call to an earlier operation lies below.
    /// - witness: `operation_rules::tests::a_growing_rule_is_unoriented`
    /// - witness: `operation_rules::tests::an_operation_over_an_earlier_one_converges`
    fn path_greater(
        &self,
        left: &[OperationNode],
        right: &[OperationNode],
        buffers: &mut Buffers,
    ) -> Placement
    {
        let (Some(above), Some(below)) = (self.children(left), self.children(right))
        else {
            return Placement::NotAbove;
        };
        let left = OperationSide {
            side: left,
            children: &above,
        };
        let right = OperationSide {
            side: right,
            children: &below,
        };
        match lpo::orient(&left, &right, &AdmissionOrder, buffers) {
            Orientation::Oriented(Evidence::Path(derivation))
                if lpo::check(&left, &right, &AdmissionOrder, &derivation, buffers)
                    == Replay::Holds =>
            {
                Placement::Above
            },
            Orientation::Oriented(_) | Orientation::Unoriented => Placement::NotAbove,
        }
    }

    /// The positions of each node's arguments; none when the side is not one
    /// term.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some` exactly when every node's arguments are whole terms
    ///   within the side; [`Children::of`] then lists, for each node, the
    ///   positions its arguments start at, in order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::path_greater`].
    /// - witness: `operation_rules::tests::a_growing_rule_is_unoriented`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|children| children.first.len() == side.len().saturating_add(1)))]
    fn children(
        &self,
        side: &[OperationNode],
    ) -> Option<Children>
    {
        let mut children = Children {
            starts: Vec::with_capacity(side.len()),
            first: Vec::with_capacity(side.len().saturating_add(1)),
        };
        for (at, &node) in side.iter().enumerate() {
            children.first.push(Position(children.starts.len()));
            let mut next = Position(at).next()?;
            for _argument in 0 .. usize::from(self.arity(node)?) {
                children.starts.push(next);
                next = self.extent(side, next)?;
            }
        }
        children.first.push(Position(children.starts.len()));
        Some(children)
    }

    /// The rules a normalization of `rules`' pairs rewrites by.
    ///
    /// # Specification
    /// - requires: every rule of `rules` validated.
    /// - ensures: `rules`' own rules, the rules of every ruled definition they
    ///   reach through right-side calls, and the presentation of every family a
    ///   constructor of any of those rules belongs to, each family once.
    /// - panics: none.
    /// - measure: each reached definition once.
    /// - executable: none — the closure is the body's own traversal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OperationRules::converge`].
    /// - witness: `operation_rules::tests::an_operation_over_an_earlier_one_converges`
    fn system(
        &self,
        rules: &OperationRules,
    ) -> System
    {
        let mut reached: BTreeSet<ConstantIndex> = BTreeSet::from([self.own.0]);
        let mut pending: Vec<&OperationRules> = alloc::vec![rules];
        let mut system = System {
            rules: Vec::new(),
            presentations: Vec::new(),
        };
        let mut families: BTreeSet<ConstantIndex> = BTreeSet::new();
        while let Some(next) = pending.pop() {
            for rule in next.rules() {
                system.rules.push(rule.clone());
                for &node in rule.left.iter().chain(rule.right.iter()) {
                    match node {
                        OperationNode::Operation { constant, .. } => {
                            if reached.insert(constant)
                                && let Some(called) = self.scope.rules(constant)
                            {
                                pending.push(called);
                            }
                        },
                        OperationNode::Constructor { family, .. } => {
                            families.insert(family);
                        },
                        OperationNode::Results(_) | OperationNode::Variable(_) => {},
                    }
                }
            }
        }
        for family in families {
            let Some(presentation) = self.scope.presentation(family)
            else {
                continue;
            };
            if presentation.rules().is_empty() {
                continue;
            }
            let read = |side: &[RuleNode]| -> Box<[OperationNode]> {
                side.iter()
                    .map(|&node| match node {
                        RuleNode::Constructor(tag) => OperationNode::Constructor { family, tag },
                        RuleNode::Variable(variable) => OperationNode::Variable(variable),
                    })
                    .collect()
            };
            let rules = presentation
                .rules()
                .iter()
                .map(|rule| OperationRule::new(read(rule.left()), read(rule.right())))
                .collect();
            system.presentations.push((family, rules));
        }
        system
    }

    /// Write the two reducts of the root overlap of `earlier` and `later` to
    /// `scratch`, or report that their left sides do not unify.
    ///
    /// # Specification
    /// - requires: both rules validated.
    /// - ensures: `Some(())` exactly when the two left sides unify;
    ///   `scratch.left` then holds `earlier`'s right side and `scratch.right`
    ///   `later`'s, each under the most general unifier, `later`'s variables
    ///   numbered after `earlier`'s.
    /// - panics: none.
    /// - executable: none — the unifier lives in `scratch`, which the
    ///   postcondition would have to re-derive.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OperationRules::converge`].
    /// - witness: `operation_rules::tests::two_overlapping_rules_that_join_converge`
    fn root_pair(
        &self,
        earlier: &OperationRule,
        later: &OperationRule,
        scratch: &mut Scratch,
    ) -> Option<()>
    {
        let offset = variables(&earlier.left);
        self.unify(
            (&earlier.left, Position(0)),
            (&later.left, Position(0)),
            scratch,
        )?;
        scratch.left.clear();
        scratch.right.clear();
        let unmoved = Ordinal(0);
        instantiate(
            &earlier.right,
            (&scratch.first, unmoved),
            &later.left,
            offset,
            &mut scratch.left,
        );
        instantiate(
            &later.right,
            (&scratch.second, offset),
            &earlier.left,
            unmoved,
            &mut scratch.right,
        );
        Some(())
    }

    /// Write the two reducts of `other`'s left side overlapping `rule`'s left
    /// side at the pattern node `at` to `scratch`, or report that they do not
    /// unify there.
    ///
    /// # Specification
    /// - requires: `rule` validated; `other` a presented rule over operation
    ///   nodes, or an operation's rule.
    /// - ensures: `Some(())` exactly when `other`'s left side unifies with the
    ///   subterm at `at`; `scratch.left` then holds `rule`'s right side under
    ///   the unifier, and `scratch.right` its left side with that subterm
    ///   rewritten by `other`, `other`'s variables numbered after `rule`'s.
    /// - panics: none.
    /// - executable: none — as [`Self::root_pair`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OperationRules::converge`].
    /// - witness: `operation_rules::tests::a_pattern_below_a_presented_rule_is_decided_against_it`
    /// - witness: `operation_rules::tests::a_law_parting_at_its_call_is_refused_1510`
    fn interior_pair(
        &self,
        rule: &OperationRule,
        other: &OperationRule,
        at: Position,
        scratch: &mut Scratch,
    ) -> Option<()>
    {
        let offset = variables(&rule.left);
        let end = self.extent(&rule.left, at)?;
        self.unify((&rule.left, at), (&other.left, Position(0)), scratch)?;
        scratch.left.clear();
        scratch.right.clear();
        let unmoved = Ordinal(0);
        instantiate(
            &rule.right,
            (&scratch.first, unmoved),
            &other.left,
            offset,
            &mut scratch.left,
        );
        let before = rule.left.get(.. at.0)?;
        let after = rule.left.get(end.0 ..)?;
        instantiate(
            before,
            (&scratch.first, unmoved),
            &other.left,
            offset,
            &mut scratch.right,
        );
        instantiate(
            &other.right,
            (&scratch.second, offset),
            &rule.left,
            unmoved,
            &mut scratch.right,
        );
        instantiate(
            after,
            (&scratch.first, unmoved),
            &other.left,
            offset,
            &mut scratch.right,
        );
        Some(())
    }

    /// Unify the subterm of `first` at its position with the subterm of
    /// `second` at its, recording each side's variable bindings in `scratch`.
    ///
    /// # Specification
    /// - requires: each side linear in its own variables, the two variable sets
    ///   disjoint.
    /// - ensures: `Some(())` exactly when the two subterms unify: walked in
    ///   step, every two non-variable nodes met are one symbol; a variable met
    ///   on either side is bound to the other side's subterm there. `scratch`'s
    ///   bindings list one entry per variable of each side.
    /// - panics: none.
    /// - measure: the nodes walked.
    /// - executable: none — as [`Self::root_pair`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OperationRules::converge`].
    /// - witness: `operation_rules::tests::two_overlapping_rules_that_join_converge`
    fn unify(
        &self,
        (first, from): (&[OperationNode], Position),
        (second, onto): (&[OperationNode], Position),
        scratch: &mut Scratch,
    ) -> Option<()>
    {
        scratch.first.clear();
        scratch.first.resize(variables(first).0, Binding::Free);
        scratch.second.clear();
        scratch.second.resize(variables(second).0, Binding::Free);
        let end = self.extent(first, from)?;
        let (mut left, mut right) = (from, onto);
        while left < end {
            let (&one, &other) = (first.get(left.0)?, second.get(right.0)?);
            match (one, other) {
                (OperationNode::Variable(variable), _) => {
                    let close = self.extent(second, right)?;
                    *scratch.first.get_mut(ordinal(variable)?.0)? = Binding::Other(right, close);
                    left = left.next()?;
                    right = close;
                },
                (_, OperationNode::Variable(variable)) => {
                    let close = self.extent(first, left)?;
                    *scratch.second.get_mut(ordinal(variable)?.0)? = Binding::Other(left, close);
                    right = right.next()?;
                    left = close;
                },
                _ if one == other => {
                    left = left.next()?;
                    right = right.next()?;
                },
                _ => return None,
            }
        }
        Some(())
    }

    /// Normalize the two reducts `scratch` holds under `system` and compare
    /// their normal forms.
    ///
    /// # Specification
    /// - requires: `system` terminates.
    /// - ensures: `Ok(())` exactly when both normal forms are one term;
    ///   [`Unjoined::Apart`] when they differ; [`Unjoined::Exhausted`] when
    ///   `fuel` ran out first.
    /// - panics: none.
    /// - measure: `fuel`.
    /// - executable: none — the normal forms are the body's own computation.
    ///
    /// # Errors
    /// As `- ensures:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OperationRules::converge`].
    /// - witness: `operation_rules::tests::two_overlapping_rules_that_part_are_refused_at_the_later`
    fn join(
        &self,
        system: &System,
        fuel: &mut RewriteFuel,
        scratch: &mut Scratch,
    ) -> Result<(), Unjoined>
    {
        let Scratch {
            ref mut left,
            ref mut right,
            ref mut rewritten,
            ref mut first,
            ..
        } = *scratch;
        self.normalize(system, left, fuel, rewritten, first)?;
        self.normalize(system, right, fuel, rewritten, first)?;
        if left == right {
            Ok(())
        }
        else {
            Err(Unjoined::Apart)
        }
    }

    /// Rewrite `term` to normal form under `system`, outermost-leftmost.
    ///
    /// # Specification
    /// - requires: `system` terminates.
    /// - ensures: on success `term` holds a term no rule of `system` matches
    ///   anywhere, reached from the input by rewriting at the first redex in
    ///   pre-order.
    /// - panics: none.
    /// - fails: [`Exhausted`] when `fuel` runs out, one unit per node scanned
    ///   or copied.
    /// - measure: `fuel`.
    /// - executable: none — irreducibility would rescan the term against every
    ///   rule after each call.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OperationRules::converge`].
    /// - witness: `operation_rules::tests::an_operation_over_an_earlier_one_converges`
    fn normalize(
        &self,
        system: &System,
        term: &mut Vec<OperationNode>,
        fuel: &mut RewriteFuel,
        rewritten: &mut Vec<OperationNode>,
        bindings: &mut Vec<Binding>,
    ) -> Result<(), Exhausted>
    {
        'rewrite: loop {
            for at in (0 .. term.len()).map(Position) {
                fuel.charge()?;
                let rules = system.rules.iter().chain(
                    system
                        .presentations
                        .iter()
                        .flat_map(|&(_, ref rules)| rules.iter()),
                );
                for rule in rules {
                    let Some(end) = self.matched(&rule.left, term, at, bindings)
                    else {
                        continue;
                    };
                    rewritten.clear();
                    rewritten.extend(term.iter().take(at.0).copied());
                    for &node in &rule.right {
                        fuel.charge()?;
                        match node {
                            OperationNode::Variable(variable) => {
                                if let Some(&Binding::Other(start, close)) =
                                    ordinal(variable).and_then(|index| bindings.get(index.0))
                                {
                                    rewritten
                                        .extend(term.get(start.0 .. close.0).unwrap_or_default());
                                }
                            },
                            OperationNode::Operation { .. }
                            | OperationNode::Constructor { .. }
                            | OperationNode::Results(_) => rewritten.push(node),
                        }
                    }
                    rewritten.extend(term.get(end.0 ..).unwrap_or_default());
                    core::mem::swap(term, rewritten);
                    continue 'rewrite;
                }
            }
            return Ok(());
        }
    }

    /// Match `pattern` against the subterm of `term` at `at`, binding its
    /// variables in `bindings`.
    ///
    /// # Specification
    /// - requires: `pattern` linear.
    /// - ensures: `Some(end)`, one past the matched subterm, exactly when every
    ///   non-variable node of `pattern` meets the same node of `term` walked in
    ///   step; each pattern variable is bound to the term's subterm it meets.
    /// - panics: none.
    /// - measure: the nodes walked.
    /// - executable: none — the bindings are the body's own record of the walk.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OperationRules::converge`].
    /// - witness: `operation_rules::tests::an_operation_over_an_earlier_one_converges`
    fn matched(
        &self,
        pattern: &[OperationNode],
        term: &[OperationNode],
        at: Position,
        bindings: &mut Vec<Binding>,
    ) -> Option<Position>
    {
        bindings.clear();
        bindings.resize(variables(pattern).0, Binding::Free);
        let mut next = at;
        for &node in pattern {
            match node {
                OperationNode::Variable(variable) => {
                    let close = self.extent(term, next)?;
                    *bindings.get_mut(ordinal(variable)?.0)? = Binding::Other(next, close);
                    next = close;
                },
                OperationNode::Operation { .. }
                | OperationNode::Constructor { .. }
                | OperationNode::Results(_) => {
                    if term.get(next.0) != Some(&node) {
                        return None;
                    }
                    next = next.next()?;
                },
            }
        }
        Some(next)
    }
}

/// One side of an operation rule as the path order reads it: each operation,
/// constructor and results tuple a symbol, each pattern variable a variable.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct OperationSide<'side>
{
    /// The side, in pre-order.
    side: &'side [OperationNode],
    /// Each node's argument positions.
    children: &'side Children,
}

impl Term for OperationSide<'_>
{
    type Bound = Infallible;
    type Symbol = OperationNode;
    type Variable = RuleVariable;

    /// The side's node count.
    ///
    /// # Specification
    /// trivial.
    fn end(&self) -> Node
    {
        Node::from(self.side.len())
    }

    /// The node at `node`: an operation, a constructor or a results tuple as
    /// a symbol, a pattern variable as a variable; a position past the side
    /// reads as a variable no rule binds, which is above nothing.
    ///
    /// # Specification
    /// trivial.
    fn former(
        &self,
        node: Node,
    ) -> Former<OperationNode, RuleVariable, Infallible>
    {
        match self.side.get(usize::from(node)) {
            Some(&OperationNode::Variable(variable)) => Former::Variable(variable),
            Some(
                &symbol @ (OperationNode::Operation { .. }
                | OperationNode::Constructor { .. }
                | OperationNode::Results(_)),
            ) => Former::Symbol(symbol),
            None => Former::Variable(RuleVariable::from(u32::MAX)),
        }
    }

    /// The positions the node's arguments start at.
    ///
    /// # Specification
    /// trivial.
    fn arguments(
        &self,
        node: Node,
    ) -> impl Iterator<Item = Node> + Clone
    {
        self.children
            .of(Position(usize::from(node)))
            .iter()
            .map(|&Position(at)| Node::from(at))
    }
}

impl Valued for OperationSide<'_>
{
    /// No variable of an operation rule is a value.
    ///
    /// # Specification
    /// trivial.
    fn valuation(
        &self,
        _variable: RuleVariable,
    ) -> Valuation
    {
        Valuation::Term
    }
}

/// The admission order as the path order's precedence: an operation ranked
/// by its position, above every operation admitted before it; constructors
/// and results tuples ground; every status lexicographic.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct AdmissionOrder;

impl Precedence for AdmissionOrder
{
    type Symbol = OperationNode;

    /// An operation's position as its rank; every other node ground.
    ///
    /// # Specification
    /// trivial.
    fn place(
        &self,
        symbol: OperationNode,
    ) -> Place
    {
        match symbol {
            OperationNode::Operation { constant, .. } => Place::Ranked(Rank::from(
                u64::try_from(usize::from(constant)).unwrap_or(u64::MAX),
            )),
            OperationNode::Constructor { .. }
            | OperationNode::Results(_)
            | OperationNode::Variable(_) => Place::Ground,
        }
    }

    /// Lexicographic, for every symbol.
    ///
    /// # Specification
    /// trivial.
    fn status(
        &self,
        _symbol: OperationNode,
    ) -> Status
    {
        Status::Lexicographic
    }
}

/// The positions each node of one side's arguments start at, flattened.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Children
{
    /// Every node's argument positions, node after node.
    starts: Vec<Position>,
    /// Where each node's run of `starts` begins, then one past the last run.
    first: Vec<Position>,
}

impl Children
{
    /// The positions the arguments of the node at `node` start at; empty
    /// past the side.
    ///
    /// # Specification
    /// trivial.
    fn of(
        &self,
        node: Position,
    ) -> &[Position]
    {
        let run = |at: Option<usize>| at.and_then(|at| self.first.get(at)).copied();
        match (run(Some(node.0)), run(node.0.checked_add(1))) {
            (Some(start), Some(end)) => self.starts.get(start.0 .. end.0).unwrap_or_default(),
            _ => &[],
        }
    }
}

/// How many variables `side` binds: one past its largest ordinal.
///
/// # Specification
/// trivial.
fn variables(side: &[OperationNode]) -> Ordinal
{
    Ordinal(
        side.iter()
            .filter_map(|&node| match node {
                OperationNode::Variable(variable) => ordinal(variable)?.0.checked_add(1),
                OperationNode::Operation { .. }
                | OperationNode::Constructor { .. }
                | OperationNode::Results(_) => None,
            })
            .max()
            .unwrap_or(0),
    )
}

/// The variable's ordinal as an index into its side's bindings.
///
/// # Specification
/// trivial.
fn ordinal(variable: RuleVariable) -> Option<Ordinal>
{
    usize::try_from(u32::from(variable)).ok().map(Ordinal)
}

/// Append `side` to `out` under one side's bindings: a variable bound to a
/// subterm of `other` is replaced by that subterm with `other`'s variables
/// moved by `moved`, and a free one is moved by its own side's offset.
///
/// # Specification
/// - requires: `bindings` lists one entry per variable of `side`; each bound
///   span lies within `other`.
/// - ensures: `out` gains `side` with every bound variable replaced and every
///   free one renumbered.
/// - panics: none.
/// - executable: none — the substituted side is the body's own construction.
///
/// # Adequacy
/// - hypothesis: L3 — as [`OperationRules::converge`].
/// - witness: `operation_rules::tests::two_overlapping_rules_that_join_converge`
fn instantiate(
    side: &[OperationNode],
    (bindings, own): (&[Binding], Ordinal),
    other: &[OperationNode],
    moved: Ordinal,
    out: &mut Vec<OperationNode>,
)
{
    let shifted = |node: OperationNode, by: Ordinal| match node {
        OperationNode::Variable(variable) => ordinal(variable)
            .and_then(|index| index.0.checked_add(by.0))
            .and_then(|index| u32::try_from(index).ok())
            .map_or(node, |index| {
                OperationNode::Variable(RuleVariable::from(index))
            }),
        OperationNode::Operation { .. }
        | OperationNode::Constructor { .. }
        | OperationNode::Results(_) => node,
    };
    for &node in side {
        let bound = match node {
            OperationNode::Variable(variable) => ordinal(variable)
                .and_then(|index| bindings.get(index.0))
                .copied(),
            OperationNode::Operation { .. }
            | OperationNode::Constructor { .. }
            | OperationNode::Results(_) => None,
        };
        match bound {
            Some(Binding::Other(start, close)) => {
                out.extend(
                    other
                        .get(start.0 .. close.0)
                        .unwrap_or_default()
                        .iter()
                        .map(|&inner| shifted(inner, moved)),
                );
            },
            Some(Binding::Free) | None => out.push(shifted(node, own)),
        }
    }
}

#[cfg(test)]
mod tests;
