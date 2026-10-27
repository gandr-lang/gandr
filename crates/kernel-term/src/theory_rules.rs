//! The rules of a presentation: the kernel's decision that a `Theory` value's
//! rules, completed by the rules it carries derived, are one convergent
//! rewriting system.
//!
//! A `theory` block's core definition is a value of the presentation code,
//! `Theory`. Its rule chain carries, beside each written rule, what the
//! decision replays rather than searches for: the rule's orientation (`Rule`
//! as written, `Turned` right to left), the freshness conditions it states
//! (`Fresh`) and the row it fires under (`Under`, `Open`), the rules a
//! completion derived (`Derived`, each naming the critical pair it joins) and
//! each operation's rank (`Rank`).
//! [`TheoryRules::read`] reads the chain and
//! [`TheoryRules::decide`] decides it in four steps:
//!
//! 1. every side is one term, every left side is headed by an operation and
//!    instantiates a variable only at distinct bound occurrences — a pattern
//!    (Miller) — its variables numbered by first occurrence, and every right
//!    side names and instantiates only variables its left side binds;
//! 2. the lexicographic path order of [`gandr_theory_path_orders::lpo`] over
//!    the stated ranks puts every left side above its right, its derivation
//!    replayed: an operation stands above every operation of a lower rank and
//!    above every constructor and results tuple, and the order is a
//!    simplification order whatever the ranks, so the rules terminate. A
//!    variable a right side instantiates is read at a function type, the order
//!    then the higher-order recursive path order: a left side is above an
//!    instantiation when one of its arguments holds the variable, bare or as a
//!    pattern under the abstractions of the names it is applied to last (read
//!    up to η), and it covers every argument of the instantiation;
//! 3. each derived rule is, up to its variables' names, the two normal forms
//!    under the rules before it of the critical pair it names, so it is an
//!    equation the rules before it prove;
//! 4. every critical pair joins: a pair one of whose rules instantiates a
//!    variable, is conditioned or fires under a row in the second-order reading
//!    of [`higher`], every other first order.
//!
//! By the critical pair lemma and Newman's lemma the rules are then confluent
//! and terminating, and by step 3 they decide exactly the equations the
//! written rules generate. Nothing is searched for: a derived rule the value
//! does not carry, or one whose peak does not replay, leaves its pair to part
//! in step 4 or is refused by name in step 3.
//!
//! Over an indexed sort the written terms do not carry the indices their
//! sorting fixes, so two laws' overlap can part where the typing makes its
//! sides one: a category's `comp(id(a), id(b))`. Steps 3 and 4 then read
//! each rule with its operations' implicit indices first, solved from the
//! sorts their arguments stand at ([`indexed`]), and step 2 orders the rules
//! as written. A presentation that reading does not cover is decided as
//! written.
//!
//! The terms are first order but for instantiations. A symbol is an
//! operation application, a constructor application, a results tuple, an
//! atom's abstraction or an atom named inside one, or a binding field or a
//! variable named inside one, interned by its kind, its name and its argument
//! count; two symbols are one exactly when all three agree. A binder is
//! interned without the name it binds, and an occurrence by the number of
//! binders between it and the innermost of its kind naming it, so both are
//! the canonical re-minting the checker admits them under: a rule that
//! renames a bound name is the same rule. Matching reads a binder as a
//! constructor of one field and an occurrence as a constant; the order reads
//! a binding field and its variable as the abstraction and bound-occurrence
//! formers, and an atom's abstraction and its atom as ground symbols. A
//! pattern instantiates its variable at bound variables alone, and the
//! first-order steps shift no occurrence's number. Where some
//! operation's input port takes an atom, so a term can name one, a rule that
//! states a freshness condition, or whose variable stands under other
//! abstractions at one occurrence than at another, is conditioned: it fires
//! only where its instance names no atom it may not, renumbering the atoms a
//! moved instance names, which is a question about the instance the
//! first-order reading does not ask. For a rule that instantiates a variable
//! only atom abstractions count: its second-order reading substitutes a
//! variable's instance across a binding field without capture. So a
//! conditioned rule fires in no first-order normal form, and its critical
//! pairs are decided in the second-order reading, where each variable
//! occurrence is applied to the atoms it may name ([`TheoryRule::scoped`]):
//! the condition is stated over the hole the variable stands for, pattern
//! unification composes two rules' conditions at their overlap, and an
//! overlap no instance satisfies owes no join. A rule stated under a row of
//! theories fires in the rows it describes alone, so in no first-order normal
//! form either: a pair of two rules is decided in the rows both describe,
//! their meet ([`RuleRow::meet`]), by the rules firing in every one of them,
//! and two rows that share none owe no join.
//! A variable standing under other abstractions at two occurrences on a left
//! side is refused there. Where no port takes an atom no term names one, and
//! a condition holds of every instance. A left side may repeat a variable,
//! so matching compares the subterms a repeated variable binds and the
//! critical pairs come from unification with an occurs check. A rule that
//! instantiates a variable — a second-order rule, `let(u, t) ==> t(u)` —
//! substitutes under a binder no first-order term marks, so it rewrites no
//! term the first-order pairs normalize; a pair either of whose rules
//! instantiates a variable is found and normalized in the second-order
//! reading, where the variable stands for a term over the names it is applied
//! to and its instance substitutes for them, and the critical pair lemma for
//! patterns (Mayr and Nipkow) decides it.
//!
//! # References
//!
//! - Donald E. Knuth and Peter B. Bendix. "Simple Word Problems in Universal
//!   Algebras." _Computational Problems in Abstract Algebra_, Pergamon, 1970 —
//!   completion and the critical pair lemma.
//! - Franz Baader and Tobias Nipkow. _Term Rewriting and All That_. Cambridge
//!   University Press, 1998, §§ 4.6, 5.4 and 6.2 — unification, the
//!   lexicographic path order and critical pairs.
//! - Jean-Pierre Jouannaud and Albert Rubio. "The Higher-Order Recursive Path
//!   Ordering." LICS 1999 — the order on instantiations.
//! - Richard Mayr and Tobias Nipkow. "Higher-Order Rewrite Systems and their
//!   Confluence." _Theoretical Computer Science_ 192(1), 1998 — critical pairs
//!   of pattern rewrite systems.
//! - `vault:01a178aa-a07b-7a23-bbcd-cf3893ccc160` — background: the
//!   effect-modalities design (§ The declaration) — a presentation may declare
//!   a sort classified `Type[-]`, which the presentation code admits under its
//!   own tag.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_path_orders::Evidence;
use gandr_theory_path_orders::Former;
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

use crate::Literal;
use crate::StringLiteral;
use crate::TermArena;
use crate::Value;
use crate::ValueId;
use crate::ValueType;
use crate::ValueTypeId;
use crate::base::BaseType;
use crate::presented::Exhausted;
use crate::presented::FieldCount;
use crate::presented::RewriteFuel;
use crate::presented::RuleIndex;
use crate::presented::RuleVariable;
use crate::term::ConstantIndex;
use crate::term::ConstructorTag;
use crate::theory_rules::higher::Higher;
use crate::theory_rules::higher::Pair;
use crate::theory_rules::row::RowExtent;
use crate::theory_rules::row::RowLabel;
use crate::theory_rules::row::RuleRow;

/// The nodes one presentation's decision may scan or copy, at every caller:
/// a bound on a pathological presentation, far above the few million a
/// completed group's forty-one rules spend.
pub const PRESENTATION_FUEL: u64 = 1 << 26;

/// Each constructor of the presentation code, in tag order: its count of
/// string fields, which come first, and its count of recursive fields after
/// them.
pub const PRESENTATION_CODE: [(usize, usize); 32] = [
    (0, 3),
    (0, 0),
    (1, 2),
    (1, 3),
    (2, 2),
    (1, 3),
    (1, 0),
    (1, 1),
    (1, 1),
    (0, 1),
    (0, 2),
    (1, 2),
    (2, 3),
    (2, 2),
    (2, 1),
    (1, 3),
    (1, 3),
    (3, 3),
    (2, 1),
    (1, 3),
    (1, 3),
    (1, 1),
    (1, 2),
    (2, 4),
    (1, 1),
    (2, 1),
    (1, 0),
    (1, 1),
    (1, 0),
    (1, 1),
    (0, 1),
    (1, 2),
];

/// The presentation code's constructor tags this module reads.
mod tag
{
    /// The presentation: its sort, operation and rule chains.
    pub(super) const PRESENTS: usize = 0;
    /// The end of a chain.
    pub(super) const END: usize = 1;
    /// An ordinary sort.
    pub(super) const SORT: usize = 2;
    /// An operation.
    pub(super) const OPER: usize = 3;
    /// A port that binds nothing.
    pub(super) const PORT: usize = 4;
    /// A rule oriented as written.
    pub(super) const RULE: usize = 5;
    /// A variable.
    pub(super) const VAR: usize = 6;
    /// An operation application.
    pub(super) const APP: usize = 7;
    /// A constructor application.
    pub(super) const CON: usize = 8;
    /// A results tuple.
    pub(super) const TUPLE: usize = 9;
    /// An argument and the rest of the arguments.
    pub(super) const ARG: usize = 10;
    /// A representable sort.
    pub(super) const REPRESENTABLE: usize = 11;
    /// A port under its binders.
    pub(super) const BOUND: usize = 12;
    /// The shape parameter.
    pub(super) const SHAPE: usize = 13;
    /// An observation.
    pub(super) const OBS: usize = 15;
    /// A rule oriented right to left.
    pub(super) const TURNED: usize = 16;
    /// A derived rule and the critical pair it joins.
    pub(super) const DERIVED: usize = 17;
    /// An operation's rank.
    pub(super) const RANK: usize = 18;
    /// A constant operation.
    pub(super) const CONST: usize = 19;
    /// A nested operation.
    pub(super) const NESTED: usize = 20;
    /// A variable's instantiation.
    pub(super) const INST: usize = 21;
    /// An atom sort.
    pub(super) const ATOM: usize = 22;
    /// A port abstracting atoms.
    pub(super) const ABSTRACTED: usize = 23;
    /// An atom's abstraction over its body.
    pub(super) const ABS: usize = 24;
    /// A freshness condition on the written rule before it.
    pub(super) const FRESH: usize = 25;
    /// An atom named inside an abstraction of it.
    pub(super) const OCC: usize = 26;
    /// A binding field over its body.
    pub(super) const BIND: usize = 27;
    /// A variable named inside a binding field of it.
    pub(super) const BVAR: usize = 28;
    /// A theory the row the written rule before it fires under holds.
    pub(super) const UNDER: usize = 29;
    /// The row the written rule before it fires under may hold others.
    pub(super) const OPEN: usize = 30;
    /// A computation sort.
    pub(super) const COMPUTATION: usize = 31;
}

/// Whether a data declaration's constructor table is the presentation code's.
///
/// The code has one constructor per row of [`PRESENTATION_CODE`], each with
/// that row's string fields and then that row's fields of `own` itself.
///
/// # Specification
/// - ensures: positive exactly when `constructors` has as many entries as
///   [`PRESENTATION_CODE`], and each has the row's count of `String` fields
///   followed by the row's count of fields of the unapplied `own`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the code's own table is recognised, and the same table
///   short one constructor, with a string field read as a recursion, or
///   recurring into another declaration, is not.
/// - witness: `theory_rules::tests::the_presentation_code_is_recognised_by_its_table`
#[spec(ensures: |ret| !bool::from(ret) || constructors.len() == PRESENTATION_CODE.len())]
#[inline]
#[must_use]
pub fn presentation_code(
    arena: &TermArena,
    own: ConstantIndex,
    constructors: &[Vec<ValueTypeId>],
) -> CodeRecognition
{
    let field = |id: ValueTypeId, string: bool| match arena.value_type(id) {
        Some(&ValueType::Base(BaseType::String)) => string,
        Some(&ValueType::Data {
            declaration,
            ref arguments,
        }) => !string && declaration == own && arguments.is_empty(),
        Some(_) | None => false,
    };
    CodeRecognition::from(
        constructors.len() == PRESENTATION_CODE.len()
            && constructors
                .iter()
                .zip(PRESENTATION_CODE)
                .all(|(fields, (strings, recursions))| {
                    fields.len() == strings.saturating_add(recursions)
                        && fields
                            .iter()
                            .enumerate()
                            .all(|(index, &id)| field(id, index < strings))
                }),
    )
}

/// Whether a data declaration is the presentation code.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CodeRecognition(bool);

impl From<bool> for CodeRecognition
{
    /// The recognition `recognised` states.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(recognised: bool) -> Self
    {
        Self(recognised)
    }
}

impl From<CodeRecognition> for bool
{
    /// Whether the declaration is the code.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(recognition: CodeRecognition) -> Self
    {
        recognition.0
    }
}

/// One symbol of a presentation's rule terms, by its place in the symbol
/// table.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TheorySymbol(usize);

impl From<usize> for TheorySymbol
{
    /// The symbol at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<TheorySymbol> for usize
{
    /// The symbol's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(symbol: TheorySymbol) -> Self
    {
        symbol.0
    }
}

/// An operation's place in the order: above every operation of a lower rank
/// and beside every operation of its own.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OperationRank(u32);

impl From<u32> for OperationRank
{
    /// The rank `rank`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rank: u32) -> Self
    {
        Self(rank)
    }
}

impl From<OperationRank> for u32
{
    /// The rank's number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rank: OperationRank) -> Self
    {
        rank.0
    }
}

/// The number of binders, of either kind, between an occurrence and the
/// binder naming it: the occurrence's de Bruijn index.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BinderDistance(usize);

impl From<usize> for BinderDistance
{
    /// The distance `binders`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(binders: usize) -> Self
    {
        Self(binders)
    }
}

impl From<BinderDistance> for usize
{
    /// The distance's binder count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(distance: BinderDistance) -> Self
    {
        distance.0
    }
}

/// What a symbol applies, as the order reads it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SymbolKind
{
    /// An operation at its rank.
    Operation(OperationRank),
    /// A constructor or a results tuple: below every operation.
    Constructor,
    /// An atom's abstraction over its body: a ground symbol below every
    /// operation, as a constructor of one field is.
    Abstraction,
    /// An atom named inside an abstraction of it, by the binders between it
    /// and the one binding it: a constant below every operation, as a
    /// constructor is.
    Occurrence(BinderDistance),
    /// A binding field over its body: the order's abstraction former.
    Field,
    /// A variable named inside a binding field of it, by the binders between
    /// it and the one binding it: the order's bound occurrence.
    Bound(BinderDistance),
}

/// One node of a rule side, in pre-order: a symbol applied to the next
/// subterms its arity counts, a variable, or a variable instantiated at the
/// next subterms its count names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TheoryNode
{
    /// A symbol of the table.
    Symbol(TheorySymbol),
    /// A variable, numbered by first occurrence on the rule's left side.
    Variable(RuleVariable),
    /// A right side's instantiation of a variable its left side binds at the
    /// next `FieldCount` subterms, one per variable the binding binds. In the
    /// first-order model the signature generates, the variable stands in the
    /// context its binders extend and the instantiation is the substitution
    /// operator applied to it, `X(u)` read as `$sub(X, $single(u))`; the
    /// calculus is the instantiation's meaning, matched here, never rules the
    /// kernel rewrites by.
    Instance(RuleVariable, FieldCount),
}

/// One node of a closed term's normal form in the second-order reading.
///
/// The nodes stand in pre-order: a symbol applied to the next subterms its
/// arity counts, or an occurrence by the binders of either kind between it
/// and its own.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum NormalNode
{
    /// A symbol of the table: an operation, a constructor, a results tuple,
    /// an atom's abstraction or a binding field.
    Symbol(TheorySymbol),
    /// An atom named inside an abstraction of it.
    Atom(BinderDistance),
    /// A variable named inside a binding field of it.
    Bound(BinderDistance),
}

/// One oriented rule: its left side rewrites to its right.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TheoryRule
{
    /// The left side, in pre-order.
    left: Box<[TheoryNode]>,
    /// The right side, in pre-order.
    right: Box<[TheoryNode]>,
    /// Whether a side instantiates a variable: a second-order rule, which
    /// rewrites no first-order term and whose critical pairs are decided in
    /// the second-order reading.
    instantiates: bool,
    /// Whether the rule states a freshness condition or moves a variable
    /// across an abstraction where a term can name an atom: it fires only
    /// where its instance names no atom it may not, a question about the
    /// instance the first-order reading does not ask, so the rule rewrites
    /// no first-order term and its critical pairs are decided in the
    /// second-order reading.
    conditioned: bool,
    /// The variables every occurrence of which on the left side is an
    /// argument of an operation at an input port of a sort no operation of
    /// the presentation returns: values, which only constructors and
    /// variables build, so instantiating at one calls no operation.
    values: Box<[RuleVariable]>,
    /// The atom abstractions each variable occurrence's instance may name,
    /// as [`Self::scoped`] reads them: what the second-order reading applies
    /// the variable to.
    holes: Holes,
    /// The rows the rule fires in: every row unless it states one, and then
    /// it rewrites no first-order term and its critical pairs are decided in
    /// the second-order reading, under the row they compose.
    row: RuleRow,
}

/// A binder above an occurrence of a rule's variable, as
/// [`TheoryRule::scoped`] reads it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Above<N>
{
    /// An atom's abstraction, by the name of the atom it abstracts.
    Atom(N),
    /// A binding field.
    Field,
}

/// The atom abstractions each variable occurrence of a rule may name, end
/// to end: occurrence `k`'s are `distances[ends[k - 1] .. ends[k]]`.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
struct Holes
{
    /// Every occurrence's abstractions, each by its distance from the
    /// occurrence, in the order the variable is applied to them.
    distances: Box<[BinderDistance]>,
    /// One past each occurrence's last distance, by the occurrence's place:
    /// the left side's in pre-order, then the right side's. Empty where the
    /// rule was read without them, each occurrence then naming none.
    ends: Box<[usize]>,
}

/// A variable occurrence of a rule, by its place among them: the left side's
/// in pre-order, then the right side's.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Occurrence(usize);

/// How a rule's critical pairs are decided.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// The rule rewrites first-order terms; its pairs with another such rule
    /// are decided first-order.
    FirstOrder,
    /// The rule instantiates a variable or is conditioned: it rewrites no
    /// first-order term, and its pairs are decided in the second-order
    /// reading.
    SecondOrder,
}

impl Holes
{
    /// The abstractions occurrence `at` may name; none past the last.
    ///
    /// # Specification
    /// trivial.
    fn at(
        &self,
        Occurrence(at): Occurrence,
    ) -> &[BinderDistance]
    {
        let start = at
            .checked_sub(1)
            .and_then(|before| self.ends.get(before).copied())
            .unwrap_or(0);
        self.ends
            .get(at)
            .and_then(|&end| self.distances.get(start .. end))
            .unwrap_or_default()
    }
}

impl TheoryRule
{
    /// The rule rewriting `left` to `right`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        left: Box<[TheoryNode]>,
        right: Box<[TheoryNode]>,
    ) -> Self
    {
        let instantiates = left
            .iter()
            .chain(right.iter())
            .any(|node| matches!(*node, TheoryNode::Instance(..)));
        Self {
            left,
            right,
            instantiates,
            conditioned: false,
            values: Box::default(),
            holes: Holes::default(),
            row: RuleRow::default(),
        }
    }

    /// The rule, firing in the rows `row` describes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn under(
        self,
        row: RuleRow,
    ) -> Self
    {
        Self { row, ..self }
    }

    /// The rule, stating a freshness condition or moving a variable across an
    /// abstraction where a term can name an atom.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn conditioned(self) -> Self
    {
        Self {
            conditioned: true,
            ..self
        }
    }

    /// The rule, `values` read as its values.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn valued(
        self,
        values: Box<[RuleVariable]>,
    ) -> Self
    {
        Self { values, ..self }
    }

    /// The rule, each variable occurrence's instance reading the atoms it may
    /// name: for a variable, the atom abstractions above its first occurrence
    /// on the left side, outermost first, but those `fresh` states its atom
    /// fresh for and those some occurrence on the right side stands under no
    /// abstraction of; at each occurrence, each found by its atom and its rank
    /// among the abstractions of that atom, innermost first. `above` lists, by
    /// occurrence of a variable, plain or instantiated, the left side's in
    /// pre-order then the right side's, the binders above it, outermost
    /// first.
    ///
    /// The second-order reading applies each occurrence to its atoms before
    /// any argument the rule writes: a freshness condition, written or
    /// implied by a right occurrence standing outside an abstraction, is the
    /// variable not applied to that atom, so it is stated over the hole the
    /// variable stands for. A critical pair then composes two rules'
    /// conditions by pruning in pattern unification, and an instance carries
    /// a moved variable's atoms to their places by substitution.
    ///
    /// # Specification
    /// - ensures: when `above` holds one list per variable occurrence, the rule
    ///   with each occurrence's atoms read as stated; otherwise the rule
    ///   unchanged, each occurrence naming none. Sides, variables, values and
    ///   condition unchanged.
    /// - panics: none.
    /// - executable: none — the holes are private to the rule and read only by
    ///   the second-order reading, whose verdicts the witness observes.
    /// - intension: one pass over the occurrences per variable read, the
    ///   distances kept end to end.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — scope extrusion applies the process it keeps under
    ///   its restriction to the restriction's atom on both sides and the one it
    ///   moves in to none; garbage collection, its atom stated fresh, applies
    ///   its process to none; a law under one abstraction on both sides applies
    ///   its variable to it on both, and one swapping two abstractions of one
    ///   atom swaps the distances.
    /// - witness: `theory_rules::tests::a_variables_atoms_are_read_off_its_abstractions_2448`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `fresh` holds the conditions one rule states, and `occurrences` its variable occurrences"
        )
    )]
    #[inline]
    #[must_use]
    pub fn scoped<N>(
        self,
        above: &[&[Above<N>]],
        fresh: &[(N, RuleVariable)],
    ) -> Self
    where
        N: Copy + PartialEq,
    {
        let variable = |node: &TheoryNode| match *node {
            TheoryNode::Variable(variable) | TheoryNode::Instance(variable, _) => Some(variable),
            TheoryNode::Symbol(_) => None,
        };
        let occurrences: Vec<RuleVariable> = self
            .left
            .iter()
            .chain(self.right.iter())
            .filter_map(variable)
            .collect();
        if occurrences.len() != above.len() {
            return self;
        }
        let lefts = self.left.iter().filter_map(variable).count();
        // The binder at `index` of `from`, found among `at` by its atom and
        // its rank among the abstractions of that atom, innermost first.
        let place = |at: &[Above<N>], from: &[Above<N>], index: usize| {
            let atom = *from.get(index)?;
            let Above::Atom(_) = atom
            else {
                return None;
            };
            let rank = from
                .get(index.saturating_add(1) ..)
                .unwrap_or_default()
                .iter()
                .filter(|&&binder| binder == atom)
                .count();
            at.iter()
                .enumerate()
                .rev()
                .filter(|&(_, &binder)| binder == atom)
                .nth(rank)
                .map(|(place, _)| place)
        };
        let mut distances = Vec::new();
        let mut ends = Vec::with_capacity(occurrences.len());
        for (at, &occurring) in occurrences.iter().enumerate() {
            let first = occurrences
                .get(.. lefts)
                .unwrap_or_default()
                .iter()
                .position(|&other| other == occurring);
            if let (Some(from), Some(&here)) =
                (first.and_then(|first| above.get(first)), above.get(at))
            {
                for (index, &binder) in from.iter().enumerate() {
                    let Above::Atom(atom) = binder
                    else {
                        continue;
                    };
                    let named = !fresh.contains(&(atom, occurring))
                        && occurrences
                            .iter()
                            .zip(above)
                            .skip(lefts)
                            .filter(|&(&other, _)| other == occurring)
                            .all(|(_, right)| place(right, from, index).is_some());
                    if let (true, Some(place)) = (named, place(here, from, index)) {
                        distances.push(BinderDistance(
                            here.len().saturating_sub(place).saturating_sub(1),
                        ));
                    }
                }
            }
            ends.push(distances.len());
        }
        Self {
            holes: Holes {
                distances: distances.into(),
                ends: ends.into(),
            },
            ..self
        }
    }

    /// The atom abstractions occurrence `at` of a variable may name, by
    /// distance.
    ///
    /// # Specification
    /// trivial.
    fn holes(
        &self,
        at: Occurrence,
    ) -> &[BinderDistance]
    {
        self.holes.at(at)
    }

    /// How the rule's critical pairs are decided: second-order when it
    /// instantiates a variable, is conditioned or fires under a row.
    ///
    /// # Specification
    /// trivial.
    fn reading(&self) -> Reading
    {
        if self.instantiates || self.conditioned || self.row != RuleRow::default() {
            Reading::SecondOrder
        }
        else {
            Reading::FirstOrder
        }
    }

    /// The left side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn left(&self) -> &[TheoryNode]
    {
        &self.left
    }

    /// The right side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn right(&self) -> &[TheoryNode]
    {
        &self.right
    }
}

/// A position in a rule side, by its pre-order index.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SidePosition(usize);

impl From<usize> for SidePosition
{
    /// The position `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<SidePosition> for usize
{
    /// The position's index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: SidePosition) -> Self
    {
        position.0
    }
}

/// The critical pair a derived rule joins: `inner`'s left side unified with
/// the subterm of `outer`'s left side at `position`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CriticalPeak
{
    /// The rule overlapped, rewritten at the overlap's root.
    pub outer: RuleIndex,
    /// The operation position of `outer`'s left side the overlap stands at.
    pub position: SidePosition,
    /// The rule overlapping it, rewritten at `position`.
    pub inner: RuleIndex,
}

/// Why a presentation's rules are refused.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TheoryRuleFault
{
    /// The rule chain is not one the presentation code's grammar writes: a
    /// member out of place, a term position holding no term, or a peak or a
    /// rank not in its one numeral spelling.
    Unreadable,
    /// A side is not one term, the left side is not headed by an operation,
    /// numbers its variables out of order or instantiates a variable other
    /// than at distinct bound occurrences.
    Malformed,
    /// The right side names a variable the left side does not bind.
    Unbound,
    /// The path order over the stated ranks does not put the left side above
    /// the right.
    Unoriented,
    /// The derived rule is not the two normal forms of the critical pair it
    /// names under the rules before it.
    NoPeak,
    /// The rule, overlapped by the one named, rewrites one term to two normal
    /// forms.
    Diverges(RuleIndex),
    /// The rule, overlapped by the one named, is one of two overlapping rules
    /// at least one of which instantiates a variable, and unifying their left
    /// sides meets a variable applied to other than distinct bound names,
    /// which pattern unification does not decide.
    Overlaps(RuleIndex),
    /// The decision's fuel ran out at the rule.
    Exhausted,
    /// A variable of the rule stands under other abstractions at one
    /// occurrence on its left side than at another there, where some
    /// operation's input port takes an atom: a match then compares its
    /// instances only up to the atoms they name, which no step decides yet.
    UndecidedCondition,
}

/// The first rule a presentation's rules are refused at, and why. Rules are
/// numbered written first, then derived, each in chain order.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TheoryRuleRefusal
{
    /// The rule.
    pub rule: RuleIndex,
    /// Its fault.
    pub fault: TheoryRuleFault,
}

/// A presentation's rules as the decision reads them.
///
/// The symbol table, the written rules oriented, the derived rules with their
/// peaks, and the same rules in the indexed reading where the presentation
/// has one.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TheoryRules
{
    /// Each symbol's kind and arity, by its position.
    symbols: Vec<(SymbolKind, FieldCount)>,
    /// The written rules, then the derived ones.
    rules: Vec<TheoryRule>,
    /// One peak per derived rule, in order: the last `peaks.len()` rules.
    peaks: Vec<CriticalPeak>,
    /// The rules in the indexed reading ([`indexed`]), in the same order;
    /// empty where the presentation has none, its pairs then decided over
    /// `rules`.
    indexed: Vec<TheoryRule>,
}

impl TheoryRules
{
    /// The written rules `written` over `symbols`, with no derived rule.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        symbols: Vec<(SymbolKind, FieldCount)>,
        written: Vec<TheoryRule>,
    ) -> Self
    {
        Self {
            symbols,
            rules: written,
            peaks: Vec::new(),
            indexed: Vec::new(),
        }
    }

    /// Append `rule`, derived to join `peak`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn derive(
        &mut self,
        rule: TheoryRule,
        peak: CriticalPeak,
    )
    {
        self.rules.push(rule);
        self.peaks.push(peak);
    }

    /// The symbol table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn symbols(&self) -> &[(SymbolKind, FieldCount)]
    {
        &self.symbols
    }

    /// The rules, written first, then derived.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rules(&self) -> &[TheoryRule]
    {
        &self.rules
    }

    /// The peak of each derived rule, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn peaks(&self) -> &[CriticalPeak]
    {
        &self.peaks
    }

    /// The rules whose critical pairs and peaks the decision reads: the
    /// indexed reading where the presentation has one, the rules as read
    /// otherwise.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn decided(&self) -> &[TheoryRule]
    {
        if self.indexed.is_empty() {
            &self.rules
        }
        else {
            &self.indexed
        }
    }

    /// The rules a value of the presentation code carries.
    ///
    /// # Specification
    /// - requires: nothing — the value may be arbitrary producer bytes.
    /// - ensures: the root is `Presents` and its rule chain reads, in order,
    ///   written rules (`Rule` as written, `Turned` with its sides exchanged),
    ///   each followed by its freshness conditions (`Fresh`, an atom's and a
    ///   variable's names), then the theories of the row it fires under
    ///   (`Under`, a theory's name), open when `Open` follows them, then
    ///   derived rules (`Derived`, its peak's three numerals), then ranks
    ///   (`Rank`, an operation's name and a numeral), then `End`. Each term is
    ///   a `Var`, or an `App`, `Con`, `Tuple`, `Inst`, `Abs` or `Bind` over its
    ///   `Arg` chain, or an `Occ` naming an atom an enclosing `Abs` abstracts,
    ///   or a `Bvar` naming a variable an enclosing `Bind` binds; a symbol is
    ///   interned by kind, name and argument count, an `Abs` or a `Bind`
    ///   without its name and an `Occ` or a `Bvar` by the number of binders
    ///   between it and the innermost of its kind naming it, an `App` symbol
    ///   taking the rank its name is given and every other symbol a
    ///   constructor's place. A rule's variables are numbered by first
    ///   occurrence on its left side, then on its right. Where some operation's
    ///   input port is at a sort the sort chain states an atom sort (`Atom`), a
    ///   rule followed by a condition, or whose variable stands under other
    ///   binders at one occurrence than at another — atom abstractions alone
    ///   for a rule with an `Inst` — is conditioned; where none is, no term
    ///   names an atom, a condition holds of every instance, and no rule is. A
    ///   rule followed by `Under` fires in the rows it describes, each theory
    ///   labelled by its first naming in the chain. Where the sort chain states
    ///   an indexed sort, and every rule is first order, unconditioned and
    ///   sorted by the operation chain's ports, each rule is read again with
    ///   every operation application's implicit indices first, the variables
    ///   its ports' sorts name that no input port is, solved by unifying the
    ///   sorts its arguments stand at ([`Self::decided`]); otherwise there is
    ///   no such reading.
    /// - fails: [`TheoryRuleFault::Unreadable`] at the rule the chain stops
    ///   being readable at: a member out of that order, a condition before
    ///   every written rule or after a row, an `Open` after no `Under`, a term
    ///   position holding no term, a field that is no string where a name or
    ///   numeral stands, a numeral not in its one decimal spelling, an `Occ` no
    ///   enclosing `Abs` binds, a `Bvar` no enclosing `Bind` binds, or a second
    ///   rank for one name, and at the first rule when the sort or operation
    ///   chain holds a member the code does not write there;
    ///   [`TheoryRuleFault::UndecidedCondition`] at the first rule whose
    ///   variable stands under other binders at one occurrence on its left side
    ///   than at another there, when some input port is at an atom sort.
    /// - panics: none.
    /// - intension: the chain walked in a loop and each term read from a
    ///   worklist, so no step recurses.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a presentation with a written, a turned and a derived
    ///   rule and two ranks reads as its oriented rules, its peak and its
    ///   ranked operations; a rank before a rule, a derived rule before a
    ///   written one, a padded numeral and a second rank for one name are
    ///   unreadable at the rule they stand at. A rule naming the channel its
    ///   restriction abstracts reads it as one constant whatever the atom's
    ///   name; a condition, or a variable moved out of the abstraction,
    ///   conditions its rule where a port takes the channel and not where none
    ///   does; a variable split across the abstraction on a left side is
    ///   refused undecided; an occurrence no abstraction binds is unreadable. A
    ///   category's left unit law reads with the three objects `id(a)` and `f`
    ///   fix, and laws over no indexed sort have no indexed reading.
    /// - witness: `theory_rules::tests::a_presentation_value_reads_as_its_oriented_rules`
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    /// - witness: `theory_rules::tests::an_occurrence_counts_to_its_abstraction`
    /// - witness: `theory_rules::tests::rules_under_rows_join_under_the_row_their_overlap_composes_2448`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |rules| rules.peaks.len() <= rules.rules.len()))]
    #[inline]
    pub fn read(
        arena: &TermArena,
        presentation: ValueId,
    ) -> Result<Self, TheoryRuleRefusal>
    {
        Reader::new(arena).read(presentation)
    }

    /// Decide the rules: each well formed, each oriented by the path order
    /// over the stated ranks, each derived rule replaying its peak, and every
    /// critical pair joined.
    ///
    /// # Specification
    /// - requires: nothing — the rules may be arbitrary producer bytes.
    /// - ensures: `Ok(())` exactly when, in order: every rule is well formed
    ///   (both sides one term over known symbols, the left side headed by an
    ///   operation and instantiating a variable only at distinct bound
    ///   occurrences, its variables numbered by first occurrence, every right
    ///   variable bound on the left); the path order puts every left side above
    ///   its right; each derived rule's peak names two rules before it and an
    ///   operation position of the outer one's left side, other than the root
    ///   of one rule overlapping itself, whose critical pair's two normal forms
    ///   under the rules before it are the rule's two sides, up to renaming its
    ///   variables; every critical pair one of whose rules instantiates a
    ///   variable or is conditioned joins in the second-order reading
    ///   ([`Self::second_order`]); and every other critical pair normalizes to
    ///   one term under the rules that instantiate nothing and are not
    ///   conditioned. Peaks and first-order pairs are those of
    ///   [`Self::decided`], the rules read with their indices where the
    ///   presentation has that reading, so an overlap a sorting rules out is no
    ///   pair. Otherwise the first failing rule in that order and its fault; a
    ///   divergent or undecided overlap is named at its outer rule.
    /// - provides: the kernel's own decision that a presentation's rules are a
    ///   convergent rewriting system deciding the equations its written rules
    ///   generate, re-derived at every admission and replay.
    /// - fails: as `- ensures:`; [`TheoryRuleFault::Exhausted`] at the rule
    ///   being decided when `fuel` runs out.
    /// - panics: none.
    /// - measure: the rules, then the pairs, each step charged to `fuel`.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a unit law converges and a second rule rewriting the
    ///   same call apart parts naming the pair; a group's inverse law diverges
    ///   alone and converges with the rules a completion derives, each
    ///   replaying its peak, while a derived rule naming the wrong peak, or
    ///   stating a side its peak does not reach, is refused at itself; a rule
    ///   the ranks do not decrease is unoriented and the same rule under a
    ///   higher rank for its head orients; each malformation is named; a `let`
    ///   instantiating its own argument converges, β is unoriented, a second
    ///   `let` rule at a constant joins it and one rewriting the constant apart
    ///   parts from it; get-get joins its own instance through its pattern; a
    ///   relative monad's associativity joins itself and both unit laws; scope
    ///   extrusion and garbage collection where a port takes the channel each
    ///   converge alone and join together, the overlap composing their
    ///   freshness conditions, while a restriction of nothing beside scope
    ///   extrusion parts at their overlap; a category's unit laws join over the
    ///   objects each sorting fixes and part without them.
    /// - witness: `theory_rules::tests::a_unit_law_converges_and_a_second_unit_parts_from_it`
    /// - witness: `theory_rules::tests::a_categorys_laws_join_over_their_objects_1510`
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    /// - witness: `theory_rules::tests::a_rule_the_ranks_do_not_decrease_is_unoriented`
    /// - witness: `theory_rules::tests::a_malformed_rule_is_refused_by_its_fault`
    /// - witness: `theory_rules::tests::a_let_rule_converges_and_beta_is_unoriented`
    /// - witness: `theory_rules::tests::a_pattern_on_the_left_is_read_and_decided_2115`
    /// - witness: `theory_rules::tests::a_relative_monads_laws_join_their_overlaps_2328`
    /// - witness: `theory_rules::tests::conditioned_rules_join_under_the_condition_their_overlap_composes_2448`
    #[spec(ensures: |ret| ret.as_ref().err().is_none_or(|refusal| usize::from(refusal.rule) < self.rules.len()))]
    #[inline]
    pub fn decide(
        &self,
        fuel: &mut RewriteFuel,
    ) -> Result<(), TheoryRuleRefusal>
    {
        let refuse = |index: usize, fault| TheoryRuleRefusal {
            rule: RuleIndex::from(index),
            fault,
        };
        for (index, rule) in self
            .rules
            .iter()
            .enumerate()
            .chain(self.indexed.iter().enumerate())
        {
            self.well_formed(rule)
                .map_err(|fault| refuse(index, fault))?;
        }
        let mut order = OrderBuffers::default();
        for (index, rule) in self.rules.iter().enumerate() {
            if self.path_greater(rule, &mut order) == Verdict::Fails {
                return Err(refuse(index, TheoryRuleFault::Unoriented));
            }
        }
        let decided = self.decided();
        let first = decided.len().saturating_sub(self.peaks.len());
        let mut work = PairBuffers::default();
        for (offset, &peak) in self.peaks.iter().enumerate() {
            let index = first.saturating_add(offset);
            let (Some(before), Some(rule)) = (decided.get(.. index), decided.get(index))
            else {
                return Err(refuse(index, TheoryRuleFault::NoPeak));
            };
            match self.joins(before, peak, rule, &mut work, fuel) {
                Ok(Verdict::Holds) => {},
                Ok(Verdict::Fails) => return Err(refuse(index, TheoryRuleFault::NoPeak)),
                Err(Exhausted) => return Err(refuse(index, TheoryRuleFault::Exhausted)),
            }
        }
        self.second_order(fuel)?;
        for (outer, rule) in decided.iter().enumerate() {
            for (position, &node) in rule.left().iter().enumerate() {
                if !matches!(node, TheoryNode::Symbol(_)) {
                    continue;
                }
                for inner in 0 .. decided.len() {
                    if position == 0 && inner == outer {
                        continue;
                    }
                    let peak = CriticalPeak {
                        outer: RuleIndex::from(outer),
                        position: SidePosition(position),
                        inner: RuleIndex::from(inner),
                    };
                    let other = decided.get(inner);
                    if rule.reading() == Reading::SecondOrder
                        || other.is_some_and(|other| other.reading() == Reading::SecondOrder)
                    {
                        continue;
                    }
                    let joined = self.pair(decided, peak, &mut work, fuel).and_then(|pair| {
                        if pair == Verdict::Fails {
                            return Ok(Verdict::Holds);
                        }
                        self.normalize(
                            decided,
                            &mut work.by_outer,
                            (&mut work.bindings, &mut work.rewritten),
                            fuel,
                        )?;
                        self.normalize(
                            decided,
                            &mut work.by_inner,
                            (&mut work.bindings, &mut work.rewritten),
                            fuel,
                        )?;
                        Ok(Verdict::from(work.by_outer == work.by_inner))
                    });
                    match joined {
                        Ok(Verdict::Holds) => {},
                        Ok(Verdict::Fails) => {
                            return Err(refuse(
                                outer,
                                TheoryRuleFault::Diverges(RuleIndex::from(inner)),
                            ));
                        },
                        Err(Exhausted) => return Err(refuse(outer, TheoryRuleFault::Exhausted)),
                    }
                }
            }
        }
        Ok(())
    }

    /// Decide the critical pairs one of whose rules instantiates a variable
    /// or is conditioned in the second-order reading: each found by pattern
    /// unification, the conditions the two rules state composed by pruning,
    /// and joined by normalizing both reducts under every rule.
    ///
    /// # Specification
    /// - requires: the rules well formed, as [`Self::decide`] checks first.
    /// - ensures: `Ok(())` exactly when every such pair, in order of the outer
    ///   rule, a symbol position of its left side and the inner rule, other
    ///   than the root of one rule overlapping itself, joins. Otherwise the
    ///   first other one at its outer rule: [`TheoryRuleFault::Diverges`] where
    ///   its reducts normalize apart, [`TheoryRuleFault::Overlaps`] where
    ///   unification meets a variable applied to other than distinct bound
    ///   names, [`TheoryRuleFault::Exhausted`] where `fuel` runs out.
    /// - provides: the verdict on second-order pairs a producer reports before
    ///   the kernel replays it in [`Self::decide`].
    /// - fails: as `- ensures:`.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide`]'s second-order cases.
    /// - witness: `theory_rules::tests::a_let_rule_converges_and_beta_is_unoriented`
    /// - witness: `theory_rules::tests::a_pattern_on_the_left_is_read_and_decided_2115`
    /// - witness: `theory_rules::tests::a_relative_monads_laws_join_their_overlaps_2328`
    #[spec(ensures: |ret| ret.as_ref().err().is_none_or(|refusal| usize::from(refusal.rule) < self.rules.len()))]
    #[inline]
    pub fn second_order(
        &self,
        fuel: &mut RewriteFuel,
    ) -> Result<(), TheoryRuleRefusal>
    {
        if !self
            .rules
            .iter()
            .any(|rule| rule.reading() == Reading::SecondOrder)
        {
            return Ok(());
        }
        let higher = Higher::new(self);
        for (outer, rule) in self.rules.iter().enumerate() {
            for (position, &node) in rule.left().iter().enumerate() {
                if !matches!(node, TheoryNode::Symbol(_)) {
                    continue;
                }
                for (inner, other) in self.rules.iter().enumerate() {
                    let apart = (position == 0 && inner == outer)
                        || (rule.reading() == Reading::FirstOrder
                            && other.reading() == Reading::FirstOrder);
                    if apart {
                        continue;
                    }
                    let fault = match higher.pair(
                        RuleIndex::from(outer),
                        Position(position),
                        RuleIndex::from(inner),
                        fuel,
                    ) {
                        Ok(Pair::Joins) => continue,
                        Ok(Pair::Parts) => TheoryRuleFault::Diverges(RuleIndex::from(inner)),
                        Ok(Pair::Undecided) => TheoryRuleFault::Overlaps(RuleIndex::from(inner)),
                        Err(Exhausted) => TheoryRuleFault::Exhausted,
                    };
                    return Err(TheoryRuleRefusal {
                        rule: RuleIndex::from(outer),
                        fault,
                    });
                }
            }
        }
        Ok(())
    }

    /// The normal form of the closed term `term` under these rules read
    /// second-order, in the rows of a program that names no theory: each rule
    /// stated under no row fires, one instantiating a variable by matching
    /// its pattern and substituting its instance.
    ///
    /// # Specification
    /// - requires: these rules well formed, as [`Self::decide`] checks.
    /// - ensures: [`Some`] with an η-short term no rule stated under no row
    ///   matches at any position, reached from `term`, η-contracted, by
    ///   rewriting with those rules, the last redex in pre-order first;
    ///   [`None`] where `term` holds a variable, names a symbol outside the
    ///   table or is no one whole term, or a rule's instance is ill formed.
    /// - fails: [`Exhausted`] when `fuel` runs out first, one unit spent on
    ///   each rule tried at each position.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — β fires at a binding field, substituting its argument
    ///   for the field's variable; a rule instantiating a variable below an
    ///   operation fires there; a rule under a row does not fire; a term
    ///   holding a variable or ending early is no closed term.
    /// - witness: `theory_rules::tests::an_instantiating_rule_fires_by_substitution_2966`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |normal| normal.as_ref().is_none_or(|nodes| !nodes.is_empty())))]
    #[inline]
    pub fn second_order_normal_form(
        &self,
        term: &[TheoryNode],
        fuel: &mut RewriteFuel,
    ) -> Result<Option<Box<[NormalNode]>>, Exhausted>
    {
        Higher::new(self).closed_normal_form(self, term, fuel)
    }

    /// The first critical pair of these rules, as decided ([`Self::decided`]),
    /// whose two normal forms under them are `rule`'s two sides: the peak a
    /// completion that derived `rule` from these rules names for it, sought in
    /// `search`'s buffers.
    ///
    /// # Specification
    /// - requires: these rules are well formed.
    /// - ensures: [`Some`] with the first peak, in order of the outer rule, the
    ///   position and the inner rule, that [`Self::decide`] would replay for
    ///   `rule` appended after these rules; [`None`] when none does. What
    ///   `search` held before is never read, so one search serves every rule a
    ///   caller asks about.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each rule a group's completion derives is found at a
    ///   peak of the rules before it, and the peaks found replay; a rule no
    ///   pair reaches has none.
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |peak| peak.is_none_or(|peak| usize::from(peak.outer) < self.decided().len() && usize::from(peak.inner) < self.decided().len())))]
    #[inline]
    pub fn peak_of(
        &self,
        rule: &TheoryRule,
        search: &mut PeakSearch,
        fuel: &mut RewriteFuel,
    ) -> Result<Option<CriticalPeak>, Exhausted>
    {
        let work = &mut search.0;
        let decided = self.decided();
        for (outer, overlapped) in decided.iter().enumerate() {
            for (position, &node) in overlapped.left().iter().enumerate() {
                if !matches!(node, TheoryNode::Symbol(_)) {
                    continue;
                }
                for inner in 0 .. decided.len() {
                    if position == 0 && inner == outer {
                        continue;
                    }
                    let peak = CriticalPeak {
                        outer: RuleIndex::from(outer),
                        position: SidePosition(position),
                        inner: RuleIndex::from(inner),
                    };
                    if self.joins(decided, peak, rule, work, fuel)? == Verdict::Holds {
                        return Ok(Some(peak));
                    }
                }
            }
        }
        Ok(None)
    }

    /// The arity of `symbol`, none for a symbol outside the table.
    ///
    /// # Specification
    /// trivial.
    fn arity(
        &self,
        symbol: TheorySymbol,
    ) -> Option<FieldCount>
    {
        self.symbols.get(symbol.0).map(|&(_, arity)| arity)
    }

    /// The arity of `symbol` as a count, none outside the table counted as
    /// zero.
    ///
    /// # Specification
    /// trivial.
    fn width(
        &self,
        symbol: TheorySymbol,
    ) -> Position
    {
        Position(self.arity(symbol).map_or(0, usize::from))
    }

    /// Check `rule`'s shape.
    ///
    /// # Specification
    /// - ensures: `Ok(())` exactly when both sides are one term over known
    ///   symbols, the left side is headed by an operation and instantiates a
    ///   variable only at pairwise distinct occurrence symbols, its variables,
    ///   instantiated or not, read in pre-order as first occurrences `0, 1, 2,
    ///   …` with repeats of earlier ones, and every right-side variable and
    ///   instantiated variable is one of them.
    /// - panics: none.
    /// - executable: none — restating the shape is this walk over the sides.
    ///
    /// # Errors
    /// [`TheoryRuleFault::Malformed`] or [`TheoryRuleFault::Unbound`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide`]; a get-get rule instantiating its
    ///   continuation at the two names it abstracts reads, and one
    ///   instantiating it at one name twice, or at a constructor, is malformed.
    /// - witness: `theory_rules::tests::a_malformed_rule_is_refused_by_its_fault`
    /// - witness: `theory_rules::tests::a_pattern_on_the_left_is_read_and_decided_2115`
    fn well_formed(
        &self,
        rule: &TheoryRule,
    ) -> Result<(), TheoryRuleFault>
    {
        let headed = match rule.left().first() {
            Some(&TheoryNode::Symbol(symbol)) => matches!(
                self.symbols.get(symbol.0),
                Some(&(SymbolKind::Operation(_), _))
            ),
            Some(&(TheoryNode::Variable(_) | TheoryNode::Instance(..))) | None => false,
        };
        if !headed
            || self.side_end(rule.left(), Position(0)) != Some(Position(rule.left().len()))
            || self.side_end(rule.right(), Position(0)) != Some(Position(rule.right().len()))
        {
            return Err(TheoryRuleFault::Malformed);
        }
        let mut bound = 0_usize;
        for (at, &node) in rule.left().iter().enumerate() {
            let variable = match node {
                TheoryNode::Variable(variable) => variable,
                TheoryNode::Instance(variable, count) => {
                    // A pattern: the instance's arguments, each one node, are
                    // pairwise distinct occurrences of bound names.
                    let first = at.saturating_add(1);
                    let names = rule
                        .left()
                        .get(first .. first.saturating_add(usize::from(count)))
                        .and_then(|arguments| {
                            arguments
                                .iter()
                                .map(|&argument| match argument {
                                    TheoryNode::Symbol(symbol)
                                        if matches!(
                                            self.symbols.get(symbol.0),
                                            Some(&(SymbolKind::Bound(_), _))
                                        ) =>
                                    {
                                        Some(symbol)
                                    },
                                    TheoryNode::Symbol(_)
                                    | TheoryNode::Variable(_)
                                    | TheoryNode::Instance(..) => None,
                                })
                                .collect::<Option<BTreeSet<TheorySymbol>>>()
                        });
                    if names.is_none_or(|names| names.len() != usize::from(count)) {
                        return Err(TheoryRuleFault::Malformed);
                    }
                    variable
                },
                TheoryNode::Symbol(_) => continue,
            };
            let Ordinal(ordinal) = ordinal(variable);
            if ordinal == bound {
                bound = bound.saturating_add(1);
            }
            else if ordinal > bound {
                return Err(TheoryRuleFault::Malformed);
            }
        }
        if rule.right().iter().any(|&node| {
            matches!(node, TheoryNode::Variable(variable) | TheoryNode::Instance(variable, _) if ordinal(variable).0 >= bound)
        }) {
            return Err(TheoryRuleFault::Unbound);
        }
        Ok(())
    }

    /// One past the end of the subterm of `side` starting at `start`, none
    /// when the side runs out first or names a symbol outside the table.
    ///
    /// # Specification
    /// trivial.
    fn side_end(
        &self,
        side: &[TheoryNode],
        start: Position,
    ) -> Option<Position>
    {
        let (mut at, mut owed) = (start.0, 1_usize);
        while let Some(next) = owed.checked_sub(1) {
            owed = match *side.get(at)? {
                TheoryNode::Symbol(symbol) => next.checked_add(usize::from(self.arity(symbol)?))?,
                TheoryNode::Instance(_, count) => next.checked_add(usize::from(count))?,
                TheoryNode::Variable(_) => next,
            };
            at = at.checked_add(1)?;
        }
        Some(Position(at))
    }

    /// Whether the path order of [`gandr_theory_path_orders::lpo`] over the
    /// stated ranks puts `rule`'s left side above its right, its derivation
    /// replayed: the lexicographic path order, with every variable the right
    /// side instantiates read at a function type.
    ///
    /// # Specification
    /// - requires: both sides are well formed.
    /// - ensures: for `left` and `right` the rule's sides, negative when
    ///   `right` is a variable `right` instantiates somewhere. Otherwise
    ///   positive exactly when `left` applies a symbol some argument of which
    ///   is equal to or above `right`; or `right` is an application every
    ///   argument of which `left` covers, and either `left`'s symbol precedes
    ///   `right`'s — an operation above an operation of a lower rank, and above
    ///   every constructor, results tuple, abstraction and occurrence — or the
    ///   two are one symbol and the first argument pair that differs, left to
    ///   right, is in the order; or `right` instantiates a variable an argument
    ///   of `left` holds, and `left` covers every argument of the instantiation
    ///   but the rule's values. An argument holds a variable it is, or one it
    ///   instantiates under abstractions, as `bind t . k(s, t)` holds `k` read
    ///   up to η. `left` covers a term it is above, or one of its own arguments
    ///   is equal to or above. A variable and an instantiation are above
    ///   nothing and no term above itself.
    /// - panics: none.
    /// - executable: none — the order is the table it fills and the derivation
    ///   it replays; a predicate restating it would be the order again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide`]: associativity, a unit law and an
    ///   inverse law orient, and a rule calling an operation of its head's rank
    ///   does not until the head ranks higher; a `let` instantiating its own
    ///   argument orients and β does not; a get-get rule holding its
    ///   continuation under the abstraction it instantiates it in orients; a
    ///   put-get rule instantiating its continuation at the value the put
    ///   stores orients, and not once an operation returns the value's sort.
    /// - witness: `theory_rules::tests::a_rule_the_ranks_do_not_decrease_is_unoriented`
    /// - witness: `theory_rules::tests::a_let_rule_converges_and_beta_is_unoriented`
    /// - witness: `theory_rules::tests::a_pattern_on_the_left_is_read_and_decided_2115`
    /// - witness: `theory_rules::tests::an_instantiation_at_a_value_selects_a_branch_2272`
    fn path_greater(
        &self,
        rule: &TheoryRule,
        buffers: &mut OrderBuffers,
    ) -> Verdict
    {
        self.ends(rule.left(), &mut buffers.left_ends);
        self.ends(rule.right(), &mut buffers.right_ends);
        let left = RuleSide {
            rules: self,
            side: rule.left(),
            ends: &buffers.left_ends,
            values: &rule.values,
        };
        let right = RuleSide {
            rules: self,
            side: rule.right(),
            ends: &buffers.right_ends,
            values: &[],
        };
        let ranks = StatedRanks(self);
        match lpo::orient(&left, &right, &ranks, &mut buffers.order) {
            Orientation::Oriented(Evidence::Path(derivation)) => Verdict::from(
                lpo::check(&left, &right, &ranks, &derivation, &mut buffers.order) == Replay::Holds,
            ),
            Orientation::Unoriented => Verdict::Fails,
        }
    }

    /// The end of the subterm at every position of a well-formed `side`.
    ///
    /// # Specification
    /// trivial.
    fn ends(
        &self,
        side: &[TheoryNode],
        ends: &mut Vec<Position>,
    )
    {
        ends.clear();
        ends.resize(side.len(), Position(0));
        for (position, &node) in side.iter().enumerate().rev() {
            let mut end = position.saturating_add(1);
            let width = match node {
                TheoryNode::Symbol(symbol) => self.width(symbol).0,
                TheoryNode::Instance(_, count) => usize::from(count),
                TheoryNode::Variable(_) => 0,
            };
            for _ in 0 .. width {
                end = ends.get(end).map_or(end, |next| next.0);
            }
            if let Some(slot) = ends.get_mut(position) {
                *slot = Position(end);
            }
        }
    }

    /// The positions of the arguments of the node at `position` of `side`,
    /// left to right, by `ends`.
    ///
    /// # Specification
    /// trivial.
    fn arguments<'side>(
        &self,
        side: &'side [TheoryNode],
        position: Position,
        ends: &'side [Position],
    ) -> impl Iterator<Item = Position> + Clone + 'side
    {
        let arity = match side.get(position.0) {
            Some(&TheoryNode::Symbol(symbol)) => self.width(symbol).0,
            Some(&TheoryNode::Instance(_, count)) => usize::from(count),
            Some(&TheoryNode::Variable(_)) | None => 0,
        };
        let first = Position(position.0.saturating_add(1));
        core::iter::successors(Some(first), move |at| ends.get(at.0).copied()).take(arity)
    }

    /// Whether `peak`, over `before`, replays as `rule`: the two normal forms
    /// of its critical pair under `before` are `rule`'s sides, in either
    /// order, up to renaming the variables.
    ///
    /// # Specification
    /// - requires: `before` and `rule` are well formed.
    /// - ensures: positive exactly when the peak names two rules of `before`
    ///   and an operation position of the outer one's left side, other than the
    ///   root of one rule overlapping itself, their left sides unify there, and
    ///   the two reducts' normal forms under `before`, read with their
    ///   variables numbered by first occurrence across both, are `rule`'s left
    ///   and right sides so read, or its right and left.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    /// - executable: none — restating it needs the pair and the normal forms
    ///   this computes.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn joins(
        &self,
        before: &[TheoryRule],
        peak: CriticalPeak,
        rule: &TheoryRule,
        work: &mut PairBuffers,
        fuel: &mut RewriteFuel,
    ) -> Result<Verdict, Exhausted>
    {
        if usize::from(peak.outer) >= before.len()
            || usize::from(peak.inner) >= before.len()
            || (peak.position.0 == 0 && peak.outer == peak.inner)
            || self.pair(before, peak, work, fuel)? == Verdict::Fails
        {
            return Ok(Verdict::Fails);
        }
        self.normalize(
            before,
            &mut work.by_outer,
            (&mut work.bindings, &mut work.rewritten),
            fuel,
        )?;
        self.normalize(
            before,
            &mut work.by_inner,
            (&mut work.bindings, &mut work.rewritten),
            fuel,
        )?;
        canonical_flats(
            &work.by_outer,
            &work.by_inner,
            (&mut work.canonical, &mut work.seen_nodes),
        );
        canonical_sides(
            rule.left(),
            rule.right(),
            (&mut work.stated, &mut work.seen_ordinals),
        );
        let split = rule.left().len();
        if (work.by_outer.len(), &work.canonical) == (split, &work.stated) {
            return Ok(Verdict::Holds);
        }
        canonical_flats(
            &work.by_inner,
            &work.by_outer,
            (&mut work.canonical, &mut work.seen_nodes),
        );
        Ok(Verdict::from(
            (work.by_inner.len(), &work.canonical) == (split, &work.stated),
        ))
    }

    /// Whether the overlap `peak` names over `rules` exists, the unifier left
    /// in `work`'s graph.
    ///
    /// # Specification
    /// - requires: the rules `peak` names are well formed.
    /// - ensures: positive exactly when the position holds an operation of the
    ///   outer rule's left side and the inner rule's left side unifies with the
    ///   subterm there, the two rules' variables kept apart and the unifier
    ///   passing the occurs check.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    /// - executable: none — the unifier this builds is the only witness of the
    ///   overlap.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide`]: the inverse law overlapping the
    ///   unit law and itself unify through a repeated variable, an overlap
    ///   whose unifier would be cyclic is none, and a `let` beside a rule that
    ///   rewrites under it overlaps it.
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    /// - witness: `theory_rules::tests::a_let_rule_converges_and_beta_is_unoriented`
    fn overlap(
        &self,
        rules: &[TheoryRule],
        peak: CriticalPeak,
        work: &mut PairBuffers,
        fuel: &mut RewriteFuel,
    ) -> Result<Verdict, Exhausted>
    {
        let (Some(outer), Some(inner)) = (
            rules.get(usize::from(peak.outer)),
            rules.get(usize::from(peak.inner)),
        )
        else {
            return Ok(Verdict::Fails);
        };
        let position = Position(peak.position.0);
        if !matches!(outer.left().get(position.0), Some(&TheoryNode::Symbol(_))) {
            return Ok(Verdict::Fails);
        }
        work.graph.clear();
        work.outer_variables.clear();
        work.inner_variables.clear();
        let Some(root) = work.graph.load(
            self,
            outer.left(),
            &mut work.outer_variables,
            None,
            (&mut work.positions, &mut work.stack),
        )
        else {
            return Ok(Verdict::Fails);
        };
        let Some(&at) = work.positions.get(position.0)
        else {
            return Ok(Verdict::Fails);
        };
        let Some(inner_root) = work.graph.load(
            self,
            inner.left(),
            &mut work.inner_variables,
            None,
            (&mut work.positions, &mut work.stack),
        )
        else {
            return Ok(Verdict::Fails);
        };
        if work.graph.unify(at, inner_root, &mut work.pairs, fuel)? == Verdict::Fails
            || work.graph.acyclic(root, &mut work.marks, &mut work.walk) == Verdict::Fails
        {
            return Ok(Verdict::Fails);
        }
        Ok(Verdict::Holds)
    }

    /// The critical pair `peak` names over `rules`, into `work`'s two terms.
    ///
    /// # Specification
    /// - requires: the rules `peak` names are well formed.
    /// - ensures: positive exactly when neither rule instantiates a variable or
    ///   is conditioned and [`Self::overlap`] is; `work.by_outer` then holds
    ///   the outer rule's right side under the unifier and `work.by_inner` its
    ///   left side with the inner rule's right side in place at the position,
    ///   under the unifier, each variable named by its node in the unifier.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    /// - executable: none — the unifier this builds is the only witness of the
    ///   overlap.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::overlap`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn pair(
        &self,
        rules: &[TheoryRule],
        peak: CriticalPeak,
        work: &mut PairBuffers,
        fuel: &mut RewriteFuel,
    ) -> Result<Verdict, Exhausted>
    {
        let (Some(outer), Some(inner)) = (
            rules.get(usize::from(peak.outer)),
            rules.get(usize::from(peak.inner)),
        )
        else {
            return Ok(Verdict::Fails);
        };
        let position = Position(peak.position.0);
        let Some(end) = self.side_end(outer.left(), position)
        else {
            return Ok(Verdict::Fails);
        };
        if outer.reading() == Reading::SecondOrder
            || inner.reading() == Reading::SecondOrder
            || self.overlap(rules, peak, work, fuel)? == Verdict::Fails
        {
            return Ok(Verdict::Fails);
        }
        let (Some(by_outer), Some(replacement)) = (
            work.graph.load(
                self,
                outer.right(),
                &mut work.outer_variables,
                None,
                (&mut work.positions, &mut work.stack),
            ),
            work.graph.load(
                self,
                inner.right(),
                &mut work.inner_variables,
                None,
                (&mut work.positions, &mut work.stack),
            ),
        )
        else {
            return Ok(Verdict::Fails);
        };
        let graft = Graft {
            span: Span {
                from: position,
                to: end,
            },
            node: replacement,
        };
        let Some(by_inner) = work.graph.load(
            self,
            outer.left(),
            &mut work.outer_variables,
            Some(graft),
            (&mut work.positions, &mut work.stack),
        )
        else {
            return Ok(Verdict::Fails);
        };
        work.graph
            .expand(by_outer, &mut work.by_outer, &mut work.stack, fuel)?;
        work.graph
            .expand(by_inner, &mut work.by_inner, &mut work.stack, fuel)?;
        Ok(Verdict::Holds)
    }

    /// Rewrite `term` to its normal form under the rules of `rules` that
    /// instantiate no variable and are not conditioned.
    ///
    /// # Specification
    /// - requires: `rules` are well formed and oriented; `term` is one term.
    /// - ensures: `term` rewritten until no rule instantiating nothing and not
    ///   conditioned matches at any position: the redex rewritten next is the
    ///   one starting last in pre-order, and at one position the first such
    ///   rule in order fires. A left side's repeated variable matches only
    ///   equal subterms. Each node compared or copied costs one unit of `fuel`.
    ///   A second-order rule fires nowhere: its instantiation substitutes under
    ///   a binder the first-order term does not mark. A conditioned rule fires
    ///   nowhere either: whether its instance names an atom it may not is a
    ///   question about the instance this reading does not ask.
    ///   [`Self::decide`] decides every pair either takes part in by the
    ///   second-order reading, so a first-order pair is decided without them.
    /// - fails: [`Exhausted`] when `fuel` runs out first.
    /// - panics: none.
    /// - executable: none — a normal form is what this computes; checking one
    ///   is another pass of every rule at every position.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::decide`]: a group's critical pairs
    ///   normalize through its inverse law, which matches only a term whose two
    ///   arguments agree.
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn normalize(
        &self,
        rules: &[TheoryRule],
        term: &mut Vec<Flat>,
        (bindings, built): (&mut Vec<Option<Span>>, &mut Vec<Flat>),
        fuel: &mut RewriteFuel,
    ) -> Result<(), Exhausted>
    {
        let mut cursor = term.len();
        'rewrite: loop {
            while let Some(start) = cursor.checked_sub(1) {
                cursor = start;
                if !matches!(term.get(start), Some(&Flat::Symbol(..))) {
                    continue;
                }
                for rule in rules
                    .iter()
                    .filter(|rule| rule.reading() == Reading::FirstOrder)
                {
                    let Some(end) = matched(term, Position(start), rule.left(), bindings, fuel)?
                    else {
                        continue;
                    };
                    built.clear();
                    for &node in rule.right() {
                        fuel.charge()?;
                        match node {
                            TheoryNode::Symbol(symbol) => {
                                built.push(Flat::Symbol(symbol, self.width(symbol).0));
                            },
                            TheoryNode::Variable(variable) => {
                                if let Some(&Some(span)) = bindings.get(ordinal(variable).0) {
                                    for &copied in term.get(span.from.0 .. span.to.0).unwrap_or(&[])
                                    {
                                        fuel.charge()?;
                                        built.push(copied);
                                    }
                                }
                            },
                            // The filter above keeps every rule that
                            // instantiates a variable from firing.
                            TheoryNode::Instance(..) => {},
                        }
                    }
                    cursor = start.saturating_add(built.len());
                    let _replaced = term.splice(start .. end.0, built.iter().copied());
                    continue 'rewrite;
                }
            }
            return Ok(());
        }
    }
}

/// A variable's ordinal.
///
/// # Specification
/// trivial.
fn ordinal(variable: RuleVariable) -> Ordinal
{
    Ordinal(usize::try_from(u32::from(variable)).unwrap_or(usize::MAX))
}

/// A node's position in a side or a flattened term, or a child's place in
/// the unifier's child list or among a node's children.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Position(usize);

/// A node of the unifier's graph, by its place.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Node(usize);

/// A variable's ordinal, or its place among the variables first seen.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Ordinal(usize);

/// A number a peak or a rank spells.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Numeral(usize);

/// The positions a subterm spans: from its first to one past its last.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Span
{
    /// The first position.
    from: Position,
    /// One past the last.
    to: Position,
}

/// A subterm replaced by a node as a side loads.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Graft
{
    /// The positions replaced.
    span: Span,
    /// The node standing in their place.
    node: Node,
}

/// Whether one of the decision's checks holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Verdict
{
    /// It holds.
    Holds,
    /// It does not.
    Fails,
}

impl From<bool> for Verdict
{
    /// The verdict `holds` states.
    ///
    /// # Specification
    /// trivial.
    fn from(holds: bool) -> Self
    {
        if holds { Self::Holds } else { Self::Fails }
    }
}

/// One node of a term the decision computes with: a symbol and its arity, or
/// a variable.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Flat
{
    /// A symbol over its next `arity` subterms.
    Symbol(TheorySymbol, usize),
    /// A variable, by its node in the unifier's graph.
    Variable(Node),
}

/// One past the end of the subterm of `term` starting at `start`, none when
/// the term runs out first.
///
/// # Specification
/// trivial.
fn flat_end(
    term: &[Flat],
    start: Position,
) -> Option<Position>
{
    let (mut at, mut owed) = (start.0, 1_usize);
    while let Some(next) = owed.checked_sub(1) {
        owed = match *term.get(at)? {
            Flat::Symbol(_, arity) => next.checked_add(arity)?,
            Flat::Variable(_) => next,
        };
        at = at.checked_add(1)?;
    }
    Some(Position(at))
}

/// Where `left` matches `term` at `start`: the end of the matched subterm,
/// each variable's binding left in `bindings`.
///
/// # Specification
/// - requires: `left` is well formed and `term` is one term.
/// - ensures: [`Some`] exactly when every symbol of `left` stands at the
///   corresponding position of the subterm at `start` and a variable's every
///   occurrence binds equal subterms; `bindings` then holds each variable's
///   span of `term`, by ordinal.
/// - fails: [`Exhausted`] when `fuel` runs out first; one unit per node read or
///   compared.
/// - panics: none.
/// - executable: none — the bindings left behind are the match's only record.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryRules::decide`]: the inverse law matches a
///   product of an inverse and its own argument and no other.
/// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
fn matched(
    term: &[Flat],
    start: Position,
    left: &[TheoryNode],
    bindings: &mut Vec<Option<Span>>,
    fuel: &mut RewriteFuel,
) -> Result<Option<Position>, Exhausted>
{
    bindings.clear();
    let mut at = start.0;
    for &node in left {
        fuel.charge()?;
        match node {
            TheoryNode::Symbol(symbol) => match term.get(at) {
                Some(&Flat::Symbol(found, _)) if found == symbol => at = at.saturating_add(1),
                Some(&(Flat::Symbol(..) | Flat::Variable(_))) | None => return Ok(None),
            },
            // A pattern instantiating a variable matches nothing: matching
            // one is higher-order, and a rule whose left side holds one
            // instantiates, so it fires in no normal form.
            TheoryNode::Instance(..) => return Ok(None),
            TheoryNode::Variable(variable) => {
                let Some(end) = flat_end(term, Position(at))
                else {
                    return Ok(None);
                };
                let Ordinal(ordinal) = ordinal(variable);
                if let Some(&Some(span)) = bindings.get(ordinal) {
                    let (Some(bound), Some(here)) =
                        (term.get(span.from.0 .. span.to.0), term.get(at .. end.0))
                    else {
                        return Ok(None);
                    };
                    if bound.len() != here.len() {
                        return Ok(None);
                    }
                    for (one, other) in bound.iter().zip(here) {
                        fuel.charge()?;
                        if one != other {
                            return Ok(None);
                        }
                    }
                }
                else {
                    if bindings.len() <= ordinal {
                        bindings.resize(ordinal.saturating_add(1), None);
                    }
                    if let Some(slot) = bindings.get_mut(ordinal) {
                        *slot = Some(Span {
                            from: Position(at),
                            to: end,
                        });
                    }
                }
                at = end.0;
            },
        }
    }
    Ok(Some(Position(at)))
}

/// One node of a term as two terms are compared up to their variables' names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Canonical
{
    /// A symbol.
    Symbol(TheorySymbol),
    /// A variable, by its first occurrence across both terms.
    Variable(Ordinal),
    /// An instantiation of a variable, by its first occurrence across both
    /// terms, over its argument count: no flat term holds one.
    Instance(Ordinal, FieldCount),
}

/// `first` then `second`, each variable renumbered by its first occurrence
/// across both, into `out`; `seen` is scratch.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `out` holds one node per node of `first` then `second`, in order,
///   a symbol as itself and a variable as the ordinal of its first occurrence
///   across both; nothing of a previous call remains.
/// - fails: never.
/// - panics: none.
/// - executable: none — a clause would restate the renumbering node by node.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TheoryRules::joins`]: the derived rule's sides read
///   so are the peak's two normal forms read so.
/// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
fn canonical_flats(
    first: &[Flat],
    second: &[Flat],
    (out, seen): (&mut Vec<Canonical>, &mut Vec<Node>),
)
{
    out.clear();
    seen.clear();
    for &node in first.iter().chain(second) {
        out.push(match node {
            Flat::Symbol(symbol, _) => Canonical::Symbol(symbol),
            Flat::Variable(variable) => Canonical::Variable(first_seen(seen, variable)),
        });
    }
}

/// `left` then `right`, each variable renumbered by its first occurrence
/// across both, into `out`; `seen` is scratch.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `out` holds one node per node of `left` then `right`, in order, a
///   symbol as itself and a variable or an instantiation of one by the ordinal
///   of the variable's first occurrence across both, an instantiation keeping
///   its argument count; nothing of a previous call remains.
/// - fails: never.
/// - panics: none.
/// - executable: none — a clause would restate the renumbering node by node.
///
/// # Adequacy
/// - hypothesis: L3 — as [`canonical_flats`].
/// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
fn canonical_sides(
    left: &[TheoryNode],
    right: &[TheoryNode],
    (out, seen): (&mut Vec<Canonical>, &mut Vec<Ordinal>),
)
{
    out.clear();
    seen.clear();
    for &node in left.iter().chain(right) {
        out.push(match node {
            TheoryNode::Symbol(symbol) => Canonical::Symbol(symbol),
            TheoryNode::Variable(variable) => {
                Canonical::Variable(first_seen(seen, ordinal(variable)))
            },
            TheoryNode::Instance(variable, count) => {
                Canonical::Instance(first_seen(seen, ordinal(variable)), count)
            },
        });
    }
}

/// `key`'s place among the keys `seen` in order, appending it when new.
///
/// # Specification
/// trivial.
fn first_seen<K>(
    seen: &mut Vec<K>,
    key: K,
) -> Ordinal
where
    K: Copy + Eq,
{
    if let Some(place) = seen.iter().position(|&known| known == key) {
        return Ordinal(place);
    }
    seen.push(key);
    Ordinal(seen.len().saturating_sub(1))
}

/// The buffers the path order fills, reused across rules.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct OrderBuffers
{
    /// Each left position's subterm end.
    left_ends: Vec<Position>,
    /// Each right position's subterm end.
    right_ends: Vec<Position>,
    /// The order's tables.
    order: Buffers,
}

/// One side of a rule as the path order reads it: an operation, constructor
/// or results tuple a symbol, an abstraction and an occurrence the binding
/// formers, a variable bare or instantiated.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct RuleSide<'rules>
{
    /// The rules whose symbol table the side reads.
    rules: &'rules TheoryRules,
    /// The side, in pre-order.
    side: &'rules [TheoryNode],
    /// Each position's subterm end.
    ends: &'rules [Position],
    /// The rule's values.
    values: &'rules [RuleVariable],
}

impl Term for RuleSide<'_>
{
    type Bound = TheorySymbol;
    type Symbol = TheorySymbol;
    type Variable = RuleVariable;

    /// The side's node count.
    ///
    /// # Specification
    /// trivial.
    fn end(&self) -> gandr_theory_path_orders::Node
    {
        gandr_theory_path_orders::Node::from(self.side.len())
    }

    /// The node at `node` by its symbol's kind; a position past the side reads
    /// as a variable no rule binds, which is above nothing.
    ///
    /// # Specification
    /// trivial.
    fn former(
        &self,
        node: gandr_theory_path_orders::Node,
    ) -> Former<TheorySymbol, RuleVariable, TheorySymbol>
    {
        match self.side.get(usize::from(node)) {
            Some(&TheoryNode::Symbol(symbol)) => match self.rules.symbols.get(symbol.0) {
                Some(&(SymbolKind::Field, _)) => Former::Abstraction,
                Some(&(SymbolKind::Bound(_), _)) => Former::Bound(symbol),
                Some(&(
                    SymbolKind::Operation(_)
                    | SymbolKind::Constructor
                    | SymbolKind::Abstraction
                    | SymbolKind::Occurrence(_),
                    _,
                ))
                | None => Former::Symbol(symbol),
            },
            Some(&TheoryNode::Variable(variable)) => Former::Variable(variable),
            Some(&TheoryNode::Instance(variable, _)) => Former::Application(variable),
            None => Former::Variable(RuleVariable::from(u32::MAX)),
        }
    }

    /// The positions of the node's arguments, by the side's ends.
    ///
    /// # Specification
    /// trivial.
    fn arguments(
        &self,
        node: gandr_theory_path_orders::Node,
    ) -> impl Iterator<Item = gandr_theory_path_orders::Node> + Clone
    {
        self.rules
            .arguments(self.side, Position(usize::from(node)), self.ends)
            .map(|Position(at)| gandr_theory_path_orders::Node::from(at))
    }
}

impl Valued for RuleSide<'_>
{
    /// A value exactly when the rule lists the variable among its values.
    ///
    /// # Specification
    /// trivial.
    fn valuation(
        &self,
        variable: RuleVariable,
    ) -> Valuation
    {
        if self.values.contains(&variable) {
            Valuation::Value
        }
        else {
            Valuation::Term
        }
    }
}

/// The stated ranks as the path order's precedence: an operation at its rank,
/// every other symbol ground, every status lexicographic.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct StatedRanks<'rules>(&'rules TheoryRules);

impl Precedence for StatedRanks<'_>
{
    type Symbol = TheorySymbol;

    /// An operation's stated rank; every other symbol ground.
    ///
    /// # Specification
    /// trivial.
    fn place(
        &self,
        symbol: TheorySymbol,
    ) -> Place
    {
        match self.0.symbols.get(symbol.0) {
            Some(&(SymbolKind::Operation(rank), _)) => {
                Place::Ranked(Rank::from(u64::from(u32::from(rank))))
            },
            Some(&(
                SymbolKind::Constructor
                | SymbolKind::Abstraction
                | SymbolKind::Occurrence(_)
                | SymbolKind::Field
                | SymbolKind::Bound(_),
                _,
            ))
            | None => Place::Ground,
        }
    }

    /// Lexicographic, for every symbol.
    ///
    /// # Specification
    /// trivial.
    fn status(
        &self,
        _symbol: TheorySymbol,
    ) -> Status
    {
        Status::Lexicographic
    }
}

/// The buffers [`TheoryRules::peak_of`] seeks a peak in, kept by its caller
/// so that a search for each of many rules allocates them once.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Debug, Default)]
pub struct PeakSearch(PairBuffers);

/// The buffers a critical pair is built and normalized in, reused across
/// pairs.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct PairBuffers
{
    /// The unifier's graph.
    graph: Graph,
    /// The outer rule's variables' nodes, by ordinal.
    outer_variables: Vec<Option<Node>>,
    /// The inner rule's variables' nodes, by ordinal.
    inner_variables: Vec<Option<Node>>,
    /// Each position of the side last loaded, by its node.
    positions: Vec<Node>,
    /// The loader's and the expander's stack.
    stack: Vec<Node>,
    /// The unifier's worklist.
    pairs: Vec<(Node, Node)>,
    /// The occurs check's marks.
    marks: Vec<Mark>,
    /// The occurs check's walk: each node open and its next child's place.
    walk: Vec<(Node, Position)>,
    /// The pair's side rewritten by the outer rule.
    by_outer: Vec<Flat>,
    /// The pair's side rewritten by the inner rule.
    by_inner: Vec<Flat>,
    /// A matched left side's bindings.
    bindings: Vec<Option<Span>>,
    /// A firing rule's right side, built before it replaces its redex.
    rewritten: Vec<Flat>,
    /// The pair's normal forms, renumbered.
    canonical: Vec<Canonical>,
    /// A derived rule's sides, renumbered.
    stated: Vec<Canonical>,
    /// The pair's variables, in the order their renumbering first meets them.
    seen_nodes: Vec<Node>,
    /// The derived rule's variables, in the order their renumbering first
    /// meets them.
    seen_ordinals: Vec<Ordinal>,
}

/// One node of the unifier's graph.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum GraphNode
{
    /// A symbol over the `arity` children listed from `first`.
    Symbol
    {
        /// The symbol.
        symbol: TheorySymbol,
        /// Its first child's place in the child list.
        first: Position,
        /// Its child count.
        arity: usize,
    },
    /// A variable, bound to a node or free.
    Variable(Option<Node>),
}

/// A visit mark of the occurs check.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Mark
{
    /// Not reached.
    #[default]
    Unvisited,
    /// On the walk's current path.
    Open,
    /// Every node below it visited.
    Done,
}

/// Terms as a graph whose variables a unifier binds.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Graph
{
    /// The nodes.
    nodes: Vec<GraphNode>,
    /// Every symbol node's children, each run in argument order.
    children: Vec<Node>,
}

impl Graph
{
    /// Empty the graph.
    ///
    /// # Specification
    /// trivial.
    fn clear(&mut self)
    {
        self.nodes.clear();
        self.children.clear();
    }

    /// Load `side` into the graph, its variables shared through
    /// `variables`, with the subterm spanning `graft`'s positions replaced
    /// by its node; the root's node, and each position's in `positions`.
    ///
    /// # Specification
    /// - requires: `side` is well formed under `rules`' table.
    /// - ensures: [`Some`] with the root's node; a variable's node is the one
    ///   `variables` holds for its ordinal, made free and recorded when it
    ///   holds none, and an instantiation's is its variable's, its arguments
    ///   dropped: a pattern unifies with every term its variable may stand for,
    ///   so an overlap through it is found. [`None`] when `side` is not one
    ///   term.
    /// - panics: none.
    /// - executable: none — the nodes made are the graph's own state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::decide`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    /// - witness: `theory_rules::tests::a_pattern_on_the_left_is_read_and_decided_2115`
    fn load(
        &mut self,
        rules: &TheoryRules,
        side: &[TheoryNode],
        variables: &mut Vec<Option<Node>>,
        graft: Option<Graft>,
        (positions, stack): (&mut Vec<Node>, &mut Vec<Node>),
    ) -> Option<Node>
    {
        stack.clear();
        positions.clear();
        positions.resize(side.len(), Node(usize::MAX));
        for (index, &node) in side.iter().enumerate().rev() {
            if let Some(Graft {
                span,
                node: grafted,
            }) = graft
                && index >= span.from.0
                && index < span.to.0
            {
                if index == span.from.0 {
                    stack.push(grafted);
                }
                continue;
            }
            let made = match node {
                TheoryNode::Variable(variable) | TheoryNode::Instance(variable, _) => {
                    if let TheoryNode::Instance(_, count) = node {
                        for _ in 0 .. usize::from(count) {
                            let _argument = stack.pop()?;
                        }
                    }
                    let Ordinal(ordinal) = ordinal(variable);
                    if variables.len() <= ordinal {
                        variables.resize(ordinal.saturating_add(1), None);
                    }
                    let slot = variables.get_mut(ordinal)?;
                    if let Some(made) = *slot {
                        made
                    }
                    else {
                        self.nodes.push(GraphNode::Variable(None));
                        let made = Node(self.nodes.len().saturating_sub(1));
                        *slot = Some(made);
                        made
                    }
                },
                TheoryNode::Symbol(symbol) => {
                    let arity = usize::from(rules.arity(symbol)?);
                    let first = Position(self.children.len());
                    for _ in 0 .. arity {
                        self.children.push(stack.pop()?);
                    }
                    self.nodes.push(GraphNode::Symbol {
                        symbol,
                        first,
                        arity,
                    });
                    Node(self.nodes.len().saturating_sub(1))
                },
            };
            if let Some(slot) = positions.get_mut(index) {
                *slot = made;
            }
            stack.push(made);
        }
        let root = stack.pop()?;
        stack.is_empty().then_some(root)
    }

    /// The node `node` stands for: itself, or what its variable is bound to,
    /// followed through.
    ///
    /// # Specification
    /// trivial.
    fn resolve(
        &self,
        mut node: Node,
    ) -> Node
    {
        while let Some(&GraphNode::Variable(Some(bound))) = self.nodes.get(node.0) {
            node = bound;
        }
        node
    }

    /// The child at `offset` of the run starting at `first`.
    ///
    /// # Specification
    /// trivial.
    fn child(
        &self,
        first: Position,
        offset: Position,
    ) -> Option<Node>
    {
        self.children.get(first.0.checked_add(offset.0)?).copied()
    }

    /// Unify `one` with `other`, binding free variables.
    ///
    /// # Specification
    /// - ensures: positive exactly when no two symbols the walk meets in
    ///   corresponding places differ; each free variable met is then bound to
    ///   what stands opposite it. The occurs check is [`Self::acyclic`]'s.
    /// - fails: [`Exhausted`] when `fuel` runs out first; one unit per pair.
    /// - panics: none.
    /// - executable: none — the bindings made are the graph's own state.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::decide`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn unify(
        &mut self,
        one: Node,
        other: Node,
        pairs: &mut Vec<(Node, Node)>,
        fuel: &mut RewriteFuel,
    ) -> Result<Verdict, Exhausted>
    {
        pairs.clear();
        pairs.push((one, other));
        while let Some((left, right)) = pairs.pop() {
            fuel.charge()?;
            let (left, right) = (self.resolve(left), self.resolve(right));
            if left == right {
                continue;
            }
            match (
                self.nodes.get(left.0).copied(),
                self.nodes.get(right.0).copied(),
            ) {
                (Some(GraphNode::Variable(_)), Some(_)) => {
                    if let Some(slot) = self.nodes.get_mut(left.0) {
                        *slot = GraphNode::Variable(Some(right));
                    }
                },
                (Some(GraphNode::Symbol { .. }), Some(GraphNode::Variable(_))) => {
                    if let Some(slot) = self.nodes.get_mut(right.0) {
                        *slot = GraphNode::Variable(Some(left));
                    }
                },
                (
                    Some(GraphNode::Symbol {
                        symbol,
                        first,
                        arity,
                    }),
                    Some(GraphNode::Symbol {
                        symbol: found,
                        first: other_first,
                        ..
                    }),
                ) => {
                    if symbol != found {
                        return Ok(Verdict::Fails);
                    }
                    for offset in 0 .. arity {
                        let (Some(child), Some(other_child)) = (
                            self.child(first, Position(offset)),
                            self.child(other_first, Position(offset)),
                        )
                        else {
                            return Ok(Verdict::Fails);
                        };
                        pairs.push((child, other_child));
                    }
                },
                (None, _) | (_, None) => return Ok(Verdict::Fails),
            }
        }
        Ok(Verdict::Holds)
    }

    /// Whether the term at `root`, its variables followed through their
    /// bindings, is finite: the occurs check.
    ///
    /// # Specification
    /// - ensures: positive exactly when no node reachable from `root` reaches
    ///   itself.
    /// - panics: none.
    /// - executable: none — restating it is this walk.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::decide`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn acyclic(
        &self,
        root: Node,
        marks: &mut Vec<Mark>,
        walk: &mut Vec<(Node, Position)>,
    ) -> Verdict
    {
        marks.clear();
        marks.resize(self.nodes.len(), Mark::Unvisited);
        walk.clear();
        let start = self.resolve(root);
        if let Some(mark) = marks.get_mut(start.0) {
            *mark = Mark::Open;
        }
        walk.push((start, Position(0)));
        while let Some(&mut (node, ref mut next)) = walk.last_mut() {
            let child = match self.nodes.get(node.0) {
                Some(&GraphNode::Symbol { first, arity, .. }) if next.0 < arity => {
                    let child = self.child(first, *next);
                    *next = Position(next.0.saturating_add(1));
                    child
                },
                Some(&(GraphNode::Symbol { .. } | GraphNode::Variable(_))) | None => {
                    if let Some(mark) = marks.get_mut(node.0) {
                        *mark = Mark::Done;
                    }
                    let _done = walk.pop();
                    continue;
                },
            };
            let Some(child) = child.map(|child| self.resolve(child))
            else {
                continue;
            };
            match marks.get(child.0).copied() {
                Some(Mark::Open) => return Verdict::Fails,
                Some(Mark::Unvisited) => {
                    if let Some(mark) = marks.get_mut(child.0) {
                        *mark = Mark::Open;
                    }
                    walk.push((child, Position(0)));
                },
                Some(Mark::Done) | None => {},
            }
        }
        Verdict::Holds
    }

    /// The term at `root`, its variables followed through their bindings,
    /// flattened in pre-order into `out`.
    ///
    /// # Specification
    /// - requires: [`Self::acyclic`] holds at `root`.
    /// - ensures: one node per node reached; a free variable as its node.
    /// - fails: [`Exhausted`] when `fuel` runs out first; one unit per node.
    /// - panics: none.
    /// - executable: none — the flattening is this walk.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::decide`].
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    fn expand(
        &self,
        root: Node,
        out: &mut Vec<Flat>,
        stack: &mut Vec<Node>,
        fuel: &mut RewriteFuel,
    ) -> Result<(), Exhausted>
    {
        out.clear();
        stack.clear();
        stack.push(root);
        while let Some(node) = stack.pop() {
            fuel.charge()?;
            let node = self.resolve(node);
            match self.nodes.get(node.0) {
                Some(&GraphNode::Symbol {
                    symbol,
                    first,
                    arity,
                }) => {
                    out.push(Flat::Symbol(symbol, arity));
                    for offset in (0 .. arity).rev() {
                        if let Some(child) = self.child(first, Position(offset)) {
                            stack.push(child);
                        }
                    }
                },
                Some(&GraphNode::Variable(_)) | None => out.push(Flat::Variable(node)),
            }
        }
        Ok(())
    }
}

/// What kind of node a symbol is interned from.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Class
{
    /// An operation application.
    Operation,
    /// A constructor application.
    Constructor,
    /// A results tuple.
    Tuple,
    /// An atom's abstraction, its atom's name not part of its key, so two
    /// abstractions that differ only in the atom they name are one symbol.
    Abstraction,
    /// An atom named inside an abstraction of it, keyed by the number of
    /// binders between the two, so it too is one symbol whatever the atom's
    /// name.
    Occurrence(usize),
    /// A binding field, its variable's name not part of its key.
    Field,
    /// A variable named inside a binding field of it, keyed by the number of
    /// binders between the two.
    BoundVariable(usize),
}

/// Which kind of name a binder in scope binds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binds
{
    /// An atom's abstraction binds an atom.
    Atom,
    /// A binding field binds a variable.
    Variable,
}

/// What a term node over an argument chain applies.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Applied<'arena>
{
    /// A symbol, by its interning class and name.
    Symbol(Class, Option<&'arena StringLiteral>),
    /// An instantiation of a variable.
    Instance(RuleVariable),
}

/// Which members of the rule chain may come next.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Stage
{
    /// Written rules, or anything after them.
    Written,
    /// Derived rules, or ranks.
    Derived,
    /// Ranks alone.
    Ranks,
}

/// Whether a term of a presentation can name one of its atoms or a variable
/// one of its binders binds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Naming
{
    /// Some operation's input port stands at an atom sort, or at a sort a
    /// binder binds a variable of.
    Named,
    /// No operation's input port stands at such a sort.
    Unnamed,
}

/// A symbol's interning key: its class, its name, and its argument count.
type SymbolKey<'arena> = (Class, Option<&'arena StringLiteral>, FieldCount);

/// An input port, by its operation's name and its place among the inputs.
type InputPort<'arena> = (&'arena StringLiteral, Ordinal);

/// Where a node of a rule side stands.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stands
{
    /// An argument of an operation on the left side, at an input port of a
    /// sort no operation returns.
    AtValue,
    /// Anywhere else.
    Elsewhere,
}

/// Whether the row of the rule being read has met its tail.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Tail
{
    /// Not yet: the row holds exactly the theories read so far.
    #[default]
    Unseen,
    /// The row stays open through a tail.
    Seen,
}

/// The buffers a rule's terms are read through, reused across rules.
///
/// # Specification
/// trivial.
#[derive(Default)]
struct ReadBuffers<'arena>
{
    /// The rule's variables, each by its place in first-occurrence order.
    variables: BTreeMap<&'arena StringLiteral, Ordinal>,
    /// The nodes still to read, each with the number of abstractions above it
    /// and where it stands.
    stack: Vec<(ValueId, usize, Stands)>,
    /// One node's arguments.
    arguments: Vec<ValueId>,
    /// The binders above the node being read, outermost first: each one's
    /// name and what it binds.
    atoms: Vec<(&'arena StringLiteral, Binds)>,
    /// Each variable's binders at its first occurrence, as a range of `above`.
    scopes: BTreeMap<&'arena StringLiteral, (usize, usize)>,
    /// The binders of every variable's first occurrence, end to end.
    above: Vec<(&'arena StringLiteral, Binds)>,
    /// How far some variable of the rule stands under other abstractions at
    /// one occurrence than at another.
    moved: Moved,
    /// Whether some variable of the rule stands under other abstractions at
    /// one occurrence on the left side than at another there.
    split: bool,
    /// Whether the side being read is the left side.
    left: bool,
    /// The variables with an occurrence on the left side at a value port.
    valued: BTreeSet<RuleVariable>,
    /// The variables with an occurrence on the left side anywhere else.
    served: BTreeSet<RuleVariable>,
    /// The binders above each variable occurrence of the rule read last,
    /// outermost first, end to end, its left side's occurrences in pre-order
    /// first.
    held: Vec<Above<&'arena StringLiteral>>,
    /// One past each of those occurrences' last binder in `held`.
    held_ends: Vec<usize>,
    /// The freshness conditions stated for the rule read last, each an atom's
    /// name and the variable it is fresh for.
    fresh: Vec<(&'arena StringLiteral, RuleVariable)>,
    /// Whether the rule read last still waits for its atoms to be read off.
    pending: bool,
    /// The theories the row of the written rule read last names, each by its
    /// label.
    row: Vec<RowLabel>,
    /// Whether that row has met its tail.
    tail: Tail,
}

/// How far a rule moves a variable: whether some occurrence stands under
/// other binders than its first, and whether an atom abstraction is among
/// those that differ.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
enum Moved
{
    /// Every occurrence stands under the binders of its first.
    #[default]
    Stays,
    /// Some occurrence stands under other binding fields, and the same atom
    /// abstractions.
    AcrossFields,
    /// Some occurrence stands under other atom abstractions.
    AcrossAtoms,
}

/// A reading of a presentation value's rule chain.
///
/// # Specification
/// trivial.
struct Reader<'arena>
{
    /// The arena the value lives in.
    arena: &'arena TermArena,
    /// Each interned symbol's key, in interning order.
    keys: Vec<SymbolKey<'arena>>,
    /// Each interned symbol, by its key.
    interned: BTreeMap<SymbolKey<'arena>, TheorySymbol>,
    /// The rules read so far.
    rules: Vec<TheoryRule>,
    /// The derived rules' peaks.
    peaks: Vec<CriticalPeak>,
    /// Each ranked operation's rank, by its name.
    ranks: BTreeMap<&'arena StringLiteral, OperationRank>,
    /// Whether a term of the presentation can name an atom or a bound
    /// variable.
    naming: Naming,
    /// The first rule whose variable stands under other abstractions at one
    /// occurrence on its left side than at another there, where a term can
    /// name an atom.
    split: Option<RuleIndex>,
    /// The input ports of a sort no operation returns.
    value_ports: BTreeSet<InputPort<'arena>>,
    /// Each theory a row names, by its label: its place in first-naming
    /// order.
    labels: BTreeMap<&'arena StringLiteral, RowLabel>,
}

impl<'arena> Reader<'arena>
{
    /// An empty reading over `arena`.
    ///
    /// # Specification
    /// trivial.
    fn new(arena: &'arena TermArena) -> Self
    {
        Self {
            arena,
            keys: Vec::new(),
            interned: BTreeMap::new(),
            rules: Vec::new(),
            peaks: Vec::new(),
            ranks: BTreeMap::new(),
            naming: Naming::Unnamed,
            split: None,
            value_ports: BTreeSet::new(),
            labels: BTreeMap::new(),
        }
    }

    /// Read the rule chain of `presentation`, as [`TheoryRules::read`].
    ///
    /// # Specification
    /// - ensures: as [`TheoryRules::read`].
    /// - panics: none.
    /// - executable: none — [`TheoryRules::read`] carries the predicate.
    ///
    /// # Errors
    /// As [`TheoryRules::read`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::read`].
    /// - witness: `theory_rules::tests::a_presentation_value_reads_as_its_oriented_rules`
    fn read(
        mut self,
        presentation: ValueId,
    ) -> Result<TheoryRules, TheoryRuleRefusal>
    {
        let tagged = |found: Option<(ConstructorTag, &'arena [ValueId])>| {
            found.map(|(tag, fields)| (usize::from(tag), fields))
        };
        let Some((tag::PRESENTS, &[sorts, operations, rules])) =
            tagged(self.constructor(presentation))
        else {
            return Err(self.unreadable());
        };
        let Some(naming) = self.nameable(sorts, operations)
        else {
            return Err(self.unreadable());
        };
        self.naming = naming;
        let Some(value_ports) = self.value_ports(operations)
        else {
            return Err(self.unreadable());
        };
        self.value_ports = value_ports;
        let mut at = rules;
        let mut stage = Stage::Written;
        let mut buffers = ReadBuffers::default();
        loop {
            let read = match tagged(self.constructor(at)) {
                Some((tag::END, &[])) => break,
                Some((tag::RULE, &[_, left, right, rest])) if stage == Stage::Written => {
                    self.rule(left, right, &mut buffers).map(|()| rest)
                },
                Some((tag::TURNED, &[_, left, right, rest])) if stage == Stage::Written => {
                    self.rule(right, left, &mut buffers).map(|()| rest)
                },
                Some((tag::FRESH, &[atom, term, rest]))
                    if stage == Stage::Written
                        && !self.rules.is_empty()
                        && buffers.row.is_empty() =>
                {
                    if self.naming == Naming::Named
                        && let Some(stated) = self.rules.last_mut()
                    {
                        stated.conditioned = true;
                    }
                    let (atom, term) = (self.text(atom), self.text(term));
                    if let (Some(atom), Some(&Ordinal(place))) =
                        (atom, term.and_then(|term| buffers.variables.get(term)))
                        && let Ok(place) = u32::try_from(place)
                    {
                        buffers.fresh.push((atom, RuleVariable::from(place)));
                    }
                    atom.and(term).map(|_| rest)
                },
                Some((tag::UNDER, &[theory, rest]))
                    if stage == Stage::Written
                        && !self.rules.is_empty()
                        && buffers.tail == Tail::Unseen =>
                {
                    self.text(theory).map(|theory| {
                        let next =
                            RowLabel::from(u32::try_from(self.labels.len()).unwrap_or(u32::MAX));
                        buffers.row.push(*self.labels.entry(theory).or_insert(next));
                        rest
                    })
                },
                Some((tag::OPEN, &[rest]))
                    if stage == Stage::Written
                        && !buffers.row.is_empty()
                        && buffers.tail == Tail::Unseen =>
                {
                    buffers.tail = Tail::Seen;
                    Some(rest)
                },
                Some((tag::DERIVED, &[outer, position, inner, left, right, rest]))
                    if stage <= Stage::Derived =>
                {
                    stage = Stage::Derived;
                    let peak = match (
                        self.numeral(outer),
                        self.numeral(position),
                        self.numeral(inner),
                    ) {
                        (Some(outer), Some(position), Some(inner)) => Some(CriticalPeak {
                            outer: RuleIndex::from(outer.0),
                            position: SidePosition(position.0),
                            inner: RuleIndex::from(inner.0),
                        }),
                        _ => None,
                    };
                    peak.and_then(|peak| {
                        self.rule(left, right, &mut buffers)?;
                        self.peaks.push(peak);
                        Some(rest)
                    })
                },
                Some((tag::RANK, &[name, rank, rest])) => {
                    stage = Stage::Ranks;
                    let name = self.text(name);
                    let rank = self
                        .numeral(rank)
                        .and_then(|rank| u32::try_from(rank.0).ok());
                    match (name, rank) {
                        (Some(name), Some(rank)) => self
                            .ranks
                            .insert(name, OperationRank(rank))
                            .is_none()
                            .then_some(rest),
                        _ => None,
                    }
                },
                Some(_) | None => None,
            };
            at = read.ok_or_else(|| self.unreadable())?;
        }
        self.held(&mut buffers);
        if let Some(rule) = self.split {
            return Err(TheoryRuleRefusal {
                rule,
                fault: TheoryRuleFault::UndecidedCondition,
            });
        }
        let indexed = self
            .signature(sorts, operations)
            .and_then(|signature| self.indexed(&signature))
            .unwrap_or_default();
        let symbols = self
            .keys
            .iter()
            .map(|&(class, name, arity)| {
                let kind = match (class, name) {
                    (Class::Operation, Some(name)) => {
                        SymbolKind::Operation(self.ranks.get(name).copied().unwrap_or_default())
                    },
                    (Class::Operation, None) | (Class::Constructor | Class::Tuple, _) => {
                        SymbolKind::Constructor
                    },
                    (Class::Abstraction, _) => SymbolKind::Abstraction,
                    (Class::Occurrence(between), _) => {
                        SymbolKind::Occurrence(BinderDistance(between))
                    },
                    (Class::Field, _) => SymbolKind::Field,
                    (Class::BoundVariable(between), _) => {
                        SymbolKind::Bound(BinderDistance(between))
                    },
                };
                (kind, arity)
            })
            .collect();
        Ok(TheoryRules {
            symbols,
            rules: self.rules,
            peaks: self.peaks,
            indexed,
        })
    }

    /// Whether a term of the presentation can name an atom or a bound variable:
    /// some operation's input port stands at a sort the sort chain states an
    /// atom sort, or at one a binder binds a variable of.
    ///
    /// # Specification
    /// - ensures: [`Naming::Named`] when an `Oper`, `Obs`, `Const` or `Nested`
    ///   of the chain `operations` has a `Port`, `Bound` or `Abstracted` input
    ///   whose sort an `Atom` of the chain `sorts` names, or a binder of some
    ///   `Bound` or `Abstracted` input binds a variable of, [`Naming::Unnamed`]
    ///   otherwise; [`None`] when either chain, or a port chain, holds a member
    ///   the code does not write there.
    /// - panics: none.
    /// - executable: none — the answer is the walk of the two chains, which a
    ///   predicate would walk again.
    /// - intension: one walk of each chain, the nameable sorts and the sorts
    ///   the inputs stand at kept as they are read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::read`]: one input port taking the
    ///   channel decides a condition refused, and its absence decides it read;
    ///   a monad's unit taking a value at the sort its bind's continuation
    ///   binds names a bound variable.
    /// - witness: `theory_rules::tests::an_occurrence_counts_to_its_abstraction`
    /// - witness: `theory_rules::tests::a_pattern_on_the_left_is_read_and_decided_2115`
    fn nameable(
        &self,
        sorts: ValueId,
        operations: ValueId,
    ) -> Option<Naming>
    {
        let tagged = |id: ValueId| {
            self.constructor(id)
                .map(|(tag, fields)| (usize::from(tag), fields))
        };
        let mut nameable: BTreeSet<&StringLiteral> = BTreeSet::new();
        let mut at = sorts;
        loop {
            at = match tagged(at)? {
                (tag::END, &[]) => break,
                (tag::ATOM, &[name, _, rest]) => {
                    let _new = nameable.insert(self.text(name)?);
                    rest
                },
                (tag::SORT | tag::REPRESENTABLE | tag::COMPUTATION, &[_, _, rest])
                | (tag::SHAPE, &[_, _, _, rest]) => rest,
                _ => return None,
            };
        }
        let mut stood: BTreeSet<&StringLiteral> = BTreeSet::new();
        let mut at = operations;
        loop {
            let (mut port, rest) = match tagged(at)? {
                (tag::END, &[]) => break,
                (tag::OPER | tag::OBS | tag::CONST | tag::NESTED, &[_, inputs, _, rest]) => {
                    (inputs, rest)
                },
                _ => return None,
            };
            loop {
                let (sort, binders, next) = match tagged(port)? {
                    (tag::END, &[]) => break,
                    (tag::PORT, &[_, sort, _, next]) => (sort, None, next),
                    (tag::BOUND, &[_, sort, _, binders, next])
                    | (tag::ABSTRACTED, &[_, sort, _, _, binders, next]) => {
                        (sort, Some(binders), next)
                    },
                    _ => return None,
                };
                let _new = stood.insert(self.text(sort)?);
                let mut binder = binders;
                while let Some(at) = binder {
                    binder = match tagged(at)? {
                        (tag::END, &[]) => None,
                        (tag::PORT, &[_, sort, _, next]) => {
                            let _new = nameable.insert(self.text(sort)?);
                            Some(next)
                        },
                        _ => return None,
                    };
                }
                port = next;
            }
            at = rest;
        }
        Some(if stood.iter().any(|sort| nameable.contains(sort)) {
            Naming::Named
        }
        else {
            Naming::Unnamed
        })
    }

    /// The input ports of the presentation's operations that stand at a sort
    /// no member of the operation chain returns: the ports that take a value.
    ///
    /// # Specification
    /// - ensures: [`Some`] with every input port, by its member's name and its
    ///   place among the inputs, of an `Oper`, `Obs`, `Const` or `Nested` of
    ///   the chain `operations` whose sort no output port of any member names;
    ///   [`None`] when the chain, or a port chain, holds a member the code does
    ///   not write there.
    /// - panics: none.
    /// - executable: none — the answer is the walk of the chain, which a
    ///   predicate would walk again.
    /// - intension: one walk of the chain, each input kept with its sort and
    ///   filtered once every returned sort is known.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::read`]: put-get orients while no
    ///   operation returns the sort `put` stores, and is refused once one does.
    /// - witness: `theory_rules::tests::an_instantiation_at_a_value_selects_a_branch_2272`
    fn value_ports(
        &self,
        operations: ValueId,
    ) -> Option<BTreeSet<InputPort<'arena>>>
    {
        let tagged = |id: ValueId| {
            self.constructor(id)
                .map(|(tag, fields)| (usize::from(tag), fields))
        };
        let mut returned: BTreeSet<&StringLiteral> = BTreeSet::new();
        let mut inputs: Vec<(InputPort<'arena>, &StringLiteral)> = Vec::new();
        let mut at = operations;
        loop {
            let (name, ports, outputs, rest) = match tagged(at)? {
                (tag::END, &[]) => break,
                (
                    tag::OPER | tag::OBS | tag::CONST | tag::NESTED,
                    &[name, ports, outputs, rest],
                ) => (self.text(name)?, ports, outputs, rest),
                _ => return None,
            };
            // The inputs, kept by their operation's name, then the outputs.
            for (chain, input) in [(ports, Some(name)), (outputs, None)] {
                let mut port = chain;
                let mut place = Ordinal(0);
                loop {
                    let (sort, next) = match tagged(port)? {
                        (tag::END, &[]) => break,
                        (tag::PORT, &[_, sort, _, next])
                        | (tag::BOUND, &[_, sort, _, _, next])
                        | (tag::ABSTRACTED, &[_, sort, _, _, _, next]) => (self.text(sort)?, next),
                        _ => return None,
                    };
                    match input {
                        Some(name) => inputs.push(((name, place), sort)),
                        None => {
                            let _new = returned.insert(sort);
                        },
                    }
                    place = Ordinal(place.0.saturating_add(1));
                    port = next;
                }
            }
            at = rest;
        }
        Some(
            inputs
                .into_iter()
                .filter(|&(_, sort)| !returned.contains(sort))
                .map(|(port, _)| port)
                .collect(),
        )
    }

    /// The refusal at the rule the reading has reached.
    ///
    /// # Specification
    /// trivial.
    fn unreadable(&self) -> TheoryRuleRefusal
    {
        TheoryRuleRefusal {
            rule: RuleIndex::from(self.rules.len()),
            fault: TheoryRuleFault::Unreadable,
        }
    }

    /// The tag and fields of the constructor value `id`.
    ///
    /// # Specification
    /// trivial.
    fn constructor(
        &self,
        id: ValueId,
    ) -> Option<(ConstructorTag, &'arena [ValueId])>
    {
        let Value::Constructor {
            tag, ref fields, ..
        } = *self.arena.value(id)?
        else {
            return None;
        };
        Some((tag, fields.as_slice()))
    }

    /// The string value `id`.
    ///
    /// # Specification
    /// trivial.
    fn text(
        &self,
        id: ValueId,
    ) -> Option<&'arena StringLiteral>
    {
        let Value::Literal(Literal::Text(ref text)) = *self.arena.value(id)?
        else {
            return None;
        };
        Some(text)
    }

    /// The number the string value `id` spells in decimal, none for any
    /// other spelling: empty, a non-digit, or a leading zero.
    ///
    /// # Specification
    /// trivial.
    fn numeral(
        &self,
        id: ValueId,
    ) -> Option<Numeral>
    {
        let digits: &str = self.text(id)?.as_ref();
        if digits.is_empty() || (digits.len() > 1 && digits.starts_with('0')) {
            return None;
        }
        digits
            .bytes()
            .try_fold(0_usize, |number, digit| {
                let value = digit.checked_sub(b'0').filter(|&value| value <= 9)?;
                number.checked_mul(10)?.checked_add(usize::from(value))
            })
            .map(Numeral)
    }

    /// Read the rule rewriting the term `left` to the term `right`.
    ///
    /// # Specification
    /// - ensures: [`Some`] with the rule appended, its variables numbered by
    ///   first occurrence on `left`, then on `right`; its values the variables
    ///   every occurrence of which on `left` is an argument of an operation at
    ///   one of the value ports; where a term can name an atom, the rule
    ///   conditioned when a variable stands under other abstractions at one
    ///   occurrence than at its first, counting atom abstractions alone when
    ///   the rule instantiates a variable, and itself recorded as the first
    ///   split rule unless one is when that occurrence is on `left`; [`None`]
    ///   when either term is not one the code writes.
    /// - panics: none.
    /// - executable: none — [`TheoryRules::read`] carries the predicate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::read`].
    /// - witness: `theory_rules::tests::a_presentation_value_reads_as_its_oriented_rules`
    /// - witness: `theory_rules::tests::an_instantiation_at_a_value_selects_a_branch_2272`
    fn rule(
        &mut self,
        left: ValueId,
        right: ValueId,
        buffers: &mut ReadBuffers<'arena>,
    ) -> Option<()>
    {
        self.held(buffers);
        buffers.variables.clear();
        buffers.scopes.clear();
        buffers.above.clear();
        buffers.moved = Moved::Stays;
        buffers.split = false;
        buffers.valued.clear();
        buffers.served.clear();
        let mut sides = (Vec::new(), Vec::new());
        buffers.left = true;
        self.term(left, buffers, &mut sides.0)?;
        buffers.left = false;
        self.term(right, buffers, &mut sides.1)?;
        let values = buffers
            .valued
            .difference(&buffers.served)
            .copied()
            .collect();
        let mut rule = TheoryRule::new(sides.0.into(), sides.1.into()).valued(values);
        if self.naming == Naming::Named {
            rule.conditioned = if rule.instantiates {
                buffers.moved == Moved::AcrossAtoms
            }
            else {
                buffers.moved != Moved::Stays
            };
            if buffers.split {
                let index = RuleIndex::from(self.rules.len());
                let _first = self.split.get_or_insert(index);
            }
        }
        self.rules.push(rule);
        buffers.pending = true;
        Some(())
    }

    /// Read off the atoms each variable occurrence of the rule read last may
    /// name, as [`TheoryRule::scoped`] reads them, where a term can name an
    /// atom and that rule still waits for them, and the row it fires under
    /// where it names one; then clear what its reading kept for it.
    ///
    /// # Specification
    /// trivial.
    fn held(
        &mut self,
        buffers: &mut ReadBuffers<'arena>,
    )
    {
        if buffers.pending
            && let Some(mut rule) = self.rules.pop()
        {
            if self.naming == Naming::Named {
                let mut start = 0;
                let above: Vec<&[Above<&StringLiteral>]> = buffers
                    .held_ends
                    .iter()
                    .map(|&end| {
                        let binders = buffers.held.get(start .. end).unwrap_or_default();
                        start = end;
                        binders
                    })
                    .collect();
                rule = rule.scoped(&above, &buffers.fresh);
            }
            if !buffers.row.is_empty() {
                let extent = match buffers.tail {
                    Tail::Seen => RowExtent::AtLeast,
                    Tail::Unseen => RowExtent::Exactly,
                };
                rule = rule.under(RuleRow::new(buffers.row.drain(..), extent));
            }
            self.rules.push(rule);
        }
        buffers.pending = false;
        buffers.held.clear();
        buffers.held_ends.clear();
        buffers.fresh.clear();
        buffers.row.clear();
        buffers.tail = Tail::Unseen;
    }

    /// Read the term `root` in pre-order into `out`.
    ///
    /// # Specification
    /// - ensures: [`Some`] when every node reached is a `Var`, an `Occ` naming
    ///   an atom some enclosing `Abs` abstracts, a `Bvar` naming a variable
    ///   some enclosing `Bind` binds, or an `App`, `Con`, `Tuple`, `Inst`,
    ///   `Abs` or `Bind` whose arguments are an `Arg` chain ended by `End`; a
    ///   variable, instantiated or not, takes its place among
    ///   `buffers.variables`, appended when new, and the binders above it,
    ///   outermost first, are kept at its first occurrence and compared at
    ///   every other, `buffers.moved` raised when they differ; an `Occ` is the
    ///   occurrence symbol and a `Bvar` the bound symbol of the number of
    ///   binders between it and the innermost of its kind naming it; on the
    ///   left side, a variable an `App` takes at one of the value ports is kept
    ///   in `buffers.valued`, and one anywhere else, instantiated or not, in
    ///   `buffers.served`.
    /// - panics: none.
    /// - executable: none — [`TheoryRules::read`] carries the predicate.
    /// - intension: a worklist of the nodes still to read, each with the number
    ///   of binders above it, so no step recurses; the binders in scope are one
    ///   stack cut back to a node's number as it is read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`TheoryRules::read`].
    /// - witness: `theory_rules::tests::a_presentation_value_reads_as_its_oriented_rules`
    /// - witness: `theory_rules::tests::an_occurrence_counts_to_its_abstraction`
    fn term(
        &mut self,
        root: ValueId,
        buffers: &mut ReadBuffers<'arena>,
        out: &mut Vec<TheoryNode>,
    ) -> Option<()>
    {
        let tagged = |found: Option<(ConstructorTag, &'arena [ValueId])>| {
            found.map(|(tag, fields)| (usize::from(tag), fields))
        };
        buffers.stack.clear();
        buffers.atoms.clear();
        buffers.stack.push((root, 0, Stands::Elsewhere));
        while let Some((node, depth, stands)) = buffers.stack.pop() {
            buffers.atoms.truncate(depth);
            let (applied, chain, below) = match tagged(self.constructor(node))? {
                (tag::VAR, &[name]) => {
                    let name = self.text(name)?;
                    let variable = variable(name, buffers)?;
                    scoped(name, buffers);
                    hold(buffers);
                    if buffers.left {
                        let _new = match stands {
                            Stands::AtValue => buffers.valued.insert(variable),
                            Stands::Elsewhere => buffers.served.insert(variable),
                        };
                    }
                    out.push(TheoryNode::Variable(variable));
                    continue;
                },
                (kind @ (tag::OCC | tag::BVAR), &[name]) => {
                    let name = self.text(name)?;
                    let (binds, class): (Binds, fn(usize) -> Class) = if kind == tag::OCC {
                        (Binds::Atom, Class::Occurrence)
                    }
                    else {
                        (Binds::Variable, Class::BoundVariable)
                    };
                    let between = buffers
                        .atoms
                        .iter()
                        .rev()
                        .position(|&binder| binder == (name, binds))?;
                    let symbol = self.intern((class(between), None, FieldCount::default()));
                    out.push(TheoryNode::Symbol(symbol));
                    continue;
                },
                (tag::APP, &[name, chain]) => (
                    Applied::Symbol(Class::Operation, Some(self.text(name)?)),
                    chain,
                    depth,
                ),
                (tag::CON, &[name, chain]) => (
                    Applied::Symbol(Class::Constructor, Some(self.text(name)?)),
                    chain,
                    depth,
                ),
                (tag::TUPLE, &[chain]) => (Applied::Symbol(Class::Tuple, None), chain, depth),
                (tag::ABS, &[name, chain]) => {
                    buffers.atoms.push((self.text(name)?, Binds::Atom));
                    (
                        Applied::Symbol(Class::Abstraction, None),
                        chain,
                        depth.saturating_add(1),
                    )
                },
                (tag::BIND, &[name, chain]) => {
                    buffers.atoms.push((self.text(name)?, Binds::Variable));
                    (
                        Applied::Symbol(Class::Field, None),
                        chain,
                        depth.saturating_add(1),
                    )
                },
                (tag::INST, &[name, chain]) => {
                    let name = self.text(name)?;
                    let variable = variable(name, buffers)?;
                    scoped(name, buffers);
                    hold(buffers);
                    if buffers.left {
                        let _new = buffers.served.insert(variable);
                    }
                    (Applied::Instance(variable), chain, depth)
                },
                _ => return None,
            };
            buffers.arguments.clear();
            let mut at = chain;
            loop {
                match tagged(self.constructor(at))? {
                    (tag::ARG, &[argument, rest]) => {
                        buffers.arguments.push(argument);
                        at = rest;
                    },
                    (tag::END, &[]) => break,
                    _ => return None,
                }
            }
            // An operation's arguments on the left side stand at its ports.
            let operation = match applied {
                Applied::Symbol(Class::Operation, Some(name)) if buffers.left => Some(name),
                Applied::Symbol(..) | Applied::Instance(_) => None,
            };
            match applied {
                Applied::Symbol(class, name) => {
                    let symbol =
                        self.intern((class, name, FieldCount::from(buffers.arguments.len())));
                    out.push(TheoryNode::Symbol(symbol));
                },
                Applied::Instance(variable) => out.push(TheoryNode::Instance(
                    variable,
                    FieldCount::from(buffers.arguments.len()),
                )),
            }
            let value_ports = &self.value_ports;
            buffers
                .stack
                .extend(
                    buffers
                        .arguments
                        .iter()
                        .enumerate()
                        .rev()
                        .map(|(place, &argument)| {
                            let stands = match operation {
                                Some(name) if value_ports.contains(&(name, Ordinal(place))) => {
                                    Stands::AtValue
                                },
                                Some(_) | None => Stands::Elsewhere,
                            };
                            (argument, below, stands)
                        }),
                );
        }
        Some(())
    }

    /// The symbol of `key`, interned when new.
    ///
    /// # Specification
    /// trivial.
    fn intern(
        &mut self,
        key: SymbolKey<'arena>,
    ) -> TheorySymbol
    {
        let fresh = TheorySymbol(self.keys.len());
        *self.interned.entry(key).or_insert_with(|| {
            self.keys.push(key);
            fresh
        })
    }
}

/// The variable `name` names among `buffers.variables`, appended when new.
///
/// # Specification
/// trivial.
fn variable<'arena>(
    name: &'arena StringLiteral,
    buffers: &mut ReadBuffers<'arena>,
) -> Option<RuleVariable>
{
    let count = Ordinal(buffers.variables.len());
    let Ordinal(place) = *buffers.variables.entry(name).or_insert(count);
    u32::try_from(place).ok().map(RuleVariable::from)
}

/// Keep the binders above the variable occurrence being read, outermost
/// first, as the next occurrence's in `buffers.held`.
///
/// # Specification
/// trivial.
fn hold(buffers: &mut ReadBuffers<'_>)
{
    let ReadBuffers {
        ref atoms,
        ref mut held,
        ref mut held_ends,
        ..
    } = *buffers;
    held.extend(atoms.iter().map(|&(name, binds)| match binds {
        Binds::Atom => Above::Atom(name),
        Binds::Variable => Above::Field,
    }));
    held_ends.push(held.len());
}

/// Keep the atoms in scope at `name`'s first occurrence, or compare them with
/// those at a later one, raising `buffers.moved` to how far they differ, and
/// setting `buffers.split` when the later one is on the left side.
///
/// # Specification
/// trivial.
fn scoped<'arena>(
    name: &'arena StringLiteral,
    buffers: &mut ReadBuffers<'arena>,
)
{
    if let Some(&(start, end)) = buffers.scopes.get(name) {
        let first = buffers.above.get(start .. end).unwrap_or_default();
        if first != buffers.atoms.as_slice() {
            buffers.split |= buffers.left;
            let atom = |binder: &&(&StringLiteral, Binds)| binder.1 == Binds::Atom;
            let across = if first
                .iter()
                .filter(atom)
                .eq(buffers.atoms.iter().filter(atom))
            {
                Moved::AcrossFields
            }
            else {
                Moved::AcrossAtoms
            };
            buffers.moved = buffers.moved.max(across);
        }
        return;
    }
    let start = buffers.above.len();
    buffers.above.extend_from_slice(&buffers.atoms);
    let _new = buffers.scopes.insert(name, (start, buffers.above.len()));
}

mod higher;
mod indexed;
pub mod row;

#[cfg(test)]
mod tests;
