//! The rules of a presentation: the kernel's decision that a `Theory` value's
//! rules, completed by the rules it carries derived, are one convergent
//! rewriting system.
//!
//! A `theory` block's core definition is a value of the presentation code,
//! `Theory`. Its rule chain carries, beside each written rule, what the
//! decision replays rather than searches for: the rule's orientation (`Rule`
//! as written, `Turned` right to left) and the freshness conditions it states
//! (`Fresh`), the rules a completion derived (`Derived`, each naming the
//! critical pair it joins) and each operation's rank (`Rank`).
//! [`TheoryRules::read`] reads the chain and
//! [`TheoryRules::decide`] decides it in four steps:
//!
//! 1. every side is one term, every left side is headed by an operation and
//!    instantiates a variable only at distinct bound occurrences — a pattern
//!    (Miller) — its variables numbered by first occurrence, and every right
//!    side names and instantiates only variables its left side binds;
//! 2. the lexicographic path order over the stated ranks puts every left side
//!    above its right: an operation stands above every operation of a lower
//!    rank and above every constructor and results tuple, and the order is a
//!    simplification order whatever the ranks, so the rules terminate. A
//!    variable a right side instantiates is read at a function type, the order
//!    then the higher-order recursive path order: a left side is above an
//!    instantiation when one of its arguments holds the variable, bare or as a
//!    pattern under the abstractions of the names it is applied to last (read
//!    up to η), and it covers every argument of the instantiation;
//! 3. each derived rule is, up to its variables' names, the two normal forms
//!    under the rules before it of the critical pair it names, so it is an
//!    equation the rules before it prove;
//! 4. no rule that instantiates a variable overlaps or is overlapped by a rule,
//!    and every other critical pair of the rules joins.
//!
//! By the critical pair lemma and Newman's lemma the rules are then confluent
//! and terminating, and by step 3 they decide exactly the equations the
//! written rules generate. Nothing is searched for: a derived rule the value
//! does not carry, or one whose peak does not replay, leaves its pair to part
//! in step 4 or is refused by name in step 3.
//!
//! The terms are first order but for instantiations. A symbol is an
//! operation application, a constructor application, a results tuple, an
//! atom's abstraction or an atom named inside one, interned by its kind, its
//! name and its argument count; two symbols are one exactly when all three
//! agree. An abstraction is interned without the atom it names, and an
//! occurrence by the number of abstractions between it and the one binding
//! it, so both are the canonical re-minting the checker admits them under: a
//! rule that renames the atom is the same rule. The order and matching read an
//! abstraction as a constructor of one field and an occurrence as a constant.
//! No substitution shifts that number in the decision. Where some
//! operation's input port takes an atom, so a term can name one, a rule that
//! states a freshness condition, or whose variable stands under other
//! abstractions at one occurrence than at another, is conditioned: it fires
//! only where its instance names no atom it may not, renumbering the atoms a
//! moved instance names, which is a question about a ground instance. So a
//! conditioned rule takes part in no critical pair, its overlaps refused by
//! name, and fires in no normal form the decision computes; the critical
//! pairs of the other rules join without it, and so join in the whole system.
//! A variable standing under other abstractions at two occurrences on a left
//! side is refused there. Where no port takes an atom no term names one, and
//! a condition holds of every instance. A left side may repeat a variable,
//! so matching compares the subterms a repeated variable binds and the
//! critical pairs come from unification with an occurs check. A rule that
//! instantiates a variable — a second-order rule, `let(u, t) ==> t(u)` —
//! substitutes under a binder no first-order term marks, so it rewrites no
//! term the decision normalizes; the orthogonality step 4 asks of it is what
//! keeps the critical pair lemma in reach for patterns (Mayr and Nipkow).
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

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;

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

/// The nodes one presentation's decision may scan or copy, at every caller:
/// a bound on a pathological presentation, far above the few million a
/// completed group's forty-one rules spend.
pub const PRESENTATION_FUEL: u64 = 1 << 26;

/// Each constructor of the presentation code, in tag order: its count of
/// string fields, which come first, and its count of recursive fields after
/// them.
pub const PRESENTATION_CODE: [(usize, usize); 27] = [
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
    /// An abstraction of one bound name over its body: below every
    /// operation, as a constructor is.
    Abstraction,
    /// An occurrence of a bound name, by the abstractions between it and the
    /// one binding it: a constant below every operation, as a constructor is.
    Occurrence,
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
    /// next `FieldCount` subterms, one per variable the binding binds.
    Instance(RuleVariable, FieldCount),
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
    /// rewrites no term the decision normalizes and overlaps no rule.
    instantiates: bool,
    /// Whether the rule states a freshness condition or moves a variable
    /// across an abstraction where a term can name an atom: it fires only
    /// where its instance names no atom it may not, so it too rewrites no term
    /// the decision normalizes and overlaps no rule.
    conditioned: bool,
    /// The variables every occurrence of which on the left side is an
    /// argument of an operation at an input port of a sort no operation of
    /// the presentation returns: values, which only constructors and
    /// variables build, so instantiating at one calls no operation.
    values: Box<[RuleVariable]>,
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
        }
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
    /// numbers its variables out of order or instantiates a variable.
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
    /// at least one of which instantiates a variable: a second-order rule takes
    /// part in no critical pair.
    Overlaps(RuleIndex),
    /// The decision's fuel ran out at the rule.
    Exhausted,
    /// A variable of the rule stands under other abstractions at one
    /// occurrence on its left side than at another there, where some
    /// operation's input port takes an atom: a match then compares its
    /// instances only up to the atoms they name, which no step decides yet.
    UndecidedCondition,
    /// The rule, overlapped by the one named, is one of two overlapping rules
    /// at least one of which states a freshness condition or moves a variable
    /// across an abstraction where some operation's input port takes an atom:
    /// such a rule takes part in no critical pair yet.
    Conditioned(RuleIndex),
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

/// A presentation's rules as the decision reads them: the symbol table, the
/// written rules oriented, and the derived rules with their peaks.
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

    /// The rules a value of the presentation code carries.
    ///
    /// # Specification
    /// - requires: nothing — the value may be arbitrary producer bytes.
    /// - ensures: the root is `Presents` and its rule chain reads, in order,
    ///   written rules (`Rule` as written, `Turned` with its sides exchanged),
    ///   each followed by its freshness conditions (`Fresh`, an atom's and a
    ///   variable's names), then derived rules (`Derived`, its peak's three
    ///   numerals), then ranks (`Rank`, an operation's name and a numeral),
    ///   then `End`. Each term is a `Var`, or an `App`, `Con`, `Tuple`, `Inst`
    ///   or `Abs` over its `Arg` chain, or an `Occ` naming an atom an enclosing
    ///   `Abs` abstracts; a symbol is interned by kind, name and argument
    ///   count, an `Abs` without its atom's name and an `Occ` by the number of
    ///   `Abs` between it and the innermost naming its atom, an `App` symbol
    ///   taking the rank its name is given and every other symbol a
    ///   constructor's place. A rule's variables are numbered by first
    ///   occurrence on its left side, then on its right. Where some operation's
    ///   input port is at a sort the sort chain states an atom sort (`Atom`), a
    ///   rule followed by a condition, or whose variable stands under other
    ///   `Abs` at one occurrence than at another, is conditioned; where none
    ///   is, no term names an atom, a condition holds of every instance, and no
    ///   rule is.
    /// - fails: [`TheoryRuleFault::Unreadable`] at the rule the chain stops
    ///   being readable at: a member out of that order, a condition before
    ///   every written rule, a term position holding no term, a field that is
    ///   no string where a name or numeral stands, a numeral not in its one
    ///   decimal spelling, an `Occ` no enclosing `Abs` binds, or a second rank
    ///   for one name, and at the first rule when the sort or operation chain
    ///   holds a member the code does not write there;
    ///   [`TheoryRuleFault::UndecidedCondition`] at the first rule whose
    ///   variable stands under other `Abs` at one occurrence on its left side
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
    ///   refused undecided; an occurrence no abstraction binds is unreadable.
    /// - witness: `theory_rules::tests::a_presentation_value_reads_as_its_oriented_rules`
    /// - witness: `theory_rules::tests::an_occurrence_counts_to_its_abstraction`
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
    ///   operation, instantiating nothing, and its variables numbered by first
    ///   occurrence, every right variable bound on the left); the path order
    ///   puts every left side above its right; each derived rule's peak names
    ///   two rules before it and an operation position of the outer one's left
    ///   side, other than the root of one rule overlapping itself, whose
    ///   critical pair's two normal forms under the rules before it are the
    ///   rule's two sides, up to renaming its variables; no rule instantiating
    ///   a variable, and then no conditioned rule, overlaps or is overlapped by
    ///   a rule; and every other critical pair normalizes to one term under the
    ///   rules that instantiate nothing and are not conditioned. Otherwise the
    ///   first failing rule in that order and its fault; a divergent,
    ///   second-order or conditioned overlap is named at its outer rule.
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
    ///   instantiating its own argument converges, β is unoriented, and a
    ///   second-order rule overlapping another is refused at the overlap; scope
    ///   extrusion and garbage collection where a port takes the channel each
    ///   converge alone and are refused together at their overlap.
    /// - witness: `theory_rules::tests::a_unit_law_converges_and_a_second_unit_parts_from_it`
    /// - witness: `theory_rules::tests::a_groups_completion_replays_from_its_peaks`
    /// - witness: `theory_rules::tests::a_rule_the_ranks_do_not_decrease_is_unoriented`
    /// - witness: `theory_rules::tests::a_malformed_rule_is_refused_by_its_fault`
    /// - witness: `theory_rules::tests::a_let_rule_converges_and_beta_is_unoriented`
    /// - witness: `theory_rules::tests::a_conditioned_rule_converges_alone_and_overlaps_nothing`
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
        for (index, rule) in self.rules.iter().enumerate() {
            self.well_formed(rule)
                .map_err(|fault| refuse(index, fault))?;
        }
        let mut order = OrderBuffers::default();
        for (index, rule) in self.rules.iter().enumerate() {
            if self.path_greater(rule, &mut order) == Verdict::Fails {
                return Err(refuse(index, TheoryRuleFault::Unoriented));
            }
        }
        let first = self.rules.len().saturating_sub(self.peaks.len());
        let mut work = PairBuffers::default();
        for (offset, &peak) in self.peaks.iter().enumerate() {
            let index = first.saturating_add(offset);
            let (Some(before), Some(rule)) = (self.rules.get(.. index), self.rules.get(index))
            else {
                return Err(refuse(index, TheoryRuleFault::NoPeak));
            };
            match self.joins(before, peak, rule, &mut work, fuel) {
                Ok(Verdict::Holds) => {},
                Ok(Verdict::Fails) => return Err(refuse(index, TheoryRuleFault::NoPeak)),
                Err(Exhausted) => return Err(refuse(index, TheoryRuleFault::Exhausted)),
            }
        }
        for (outer, rule) in self.rules.iter().enumerate() {
            for (position, &node) in rule.left().iter().enumerate() {
                if !matches!(node, TheoryNode::Symbol(_)) {
                    continue;
                }
                for inner in 0 .. self.rules.len() {
                    if position == 0 && inner == outer {
                        continue;
                    }
                    let peak = CriticalPeak {
                        outer: RuleIndex::from(outer),
                        position: SidePosition(position),
                        inner: RuleIndex::from(inner),
                    };
                    let other = self.rules.get(inner);
                    let apart =
                        if rule.instantiates || other.is_some_and(|other| other.instantiates) {
                            Some(TheoryRuleFault::Overlaps(RuleIndex::from(inner)))
                        }
                        else if rule.conditioned || other.is_some_and(|other| other.conditioned) {
                            Some(TheoryRuleFault::Conditioned(RuleIndex::from(inner)))
                        }
                        else {
                            None
                        };
                    if let Some(fault) = apart {
                        match self.overlap(&self.rules, peak, &mut work, fuel) {
                            Ok(Verdict::Fails) => continue,
                            Ok(Verdict::Holds) => return Err(refuse(outer, fault)),
                            Err(Exhausted) => {
                                return Err(refuse(outer, TheoryRuleFault::Exhausted));
                            },
                        }
                    }
                    let joined = self
                        .pair(&self.rules, peak, &mut work, fuel)
                        .and_then(|pair| {
                            if pair == Verdict::Fails {
                                return Ok(Verdict::Holds);
                            }
                            self.normalize(
                                &self.rules,
                                &mut work.by_outer,
                                (&mut work.bindings, &mut work.rewritten),
                                fuel,
                            )?;
                            self.normalize(
                                &self.rules,
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

    /// The first critical pair of these rules whose two normal forms under
    /// them are `rule`'s two sides: the peak a completion that derived `rule`
    /// from these rules names for it, sought in `search`'s buffers.
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
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |peak| peak.is_none_or(|peak| usize::from(peak.outer) < self.rules.len() && usize::from(peak.inner) < self.rules.len())))]
    #[inline]
    pub fn peak_of(
        &self,
        rule: &TheoryRule,
        search: &mut PeakSearch,
        fuel: &mut RewriteFuel,
    ) -> Result<Option<CriticalPeak>, Exhausted>
    {
        let work = &mut search.0;
        for (outer, overlapped) in self.rules.iter().enumerate() {
            for (position, &node) in overlapped.left().iter().enumerate() {
                if !matches!(node, TheoryNode::Symbol(_)) {
                    continue;
                }
                for inner in 0 .. self.rules.len() {
                    if position == 0 && inner == outer {
                        continue;
                    }
                    let peak = CriticalPeak {
                        outer: RuleIndex::from(outer),
                        position: SidePosition(position),
                        inner: RuleIndex::from(inner),
                    };
                    if self.joins(&self.rules, peak, rule, work, fuel)? == Verdict::Holds {
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
                                            Some(&(SymbolKind::Occurrence, _))
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

    /// Whether the higher-order recursive path order over the stated ranks
    /// puts `rule`'s left side above its right: the lexicographic path order,
    /// with every variable the right side instantiates read at a function type.
    ///
    /// # Specification
    /// - requires: both sides are well formed.
    /// - ensures: for `left` and `right` the rule's sides, negative when
    ///   `right` is a variable `right` instantiates somewhere. Otherwise
    ///   positive exactly when `left` is an application some argument of which
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
    ///   is equal to or above. A variable is above nothing and no term above
    ///   itself.
    /// - panics: none.
    /// - executable: none — the order is the table this fills; a predicate
    ///   restating it would be the function again.
    /// - intension: one table of every pair of positions of the two sides,
    ///   filled from the last positions up, so no comparison recurses.
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
        let (left, right) = (rule.left(), rule.right());
        let columns = right.len();
        self.ends(left, &mut buffers.left_ends);
        self.ends(right, &mut buffers.right_ends);
        buffers.higher.clear();
        for &node in right {
            if let TheoryNode::Instance(variable, _) = node {
                let Ordinal(place) = ordinal(variable);
                if buffers.higher.len() <= place {
                    buffers.higher.resize(place.saturating_add(1), false);
                }
                if let Some(slot) = buffers.higher.get_mut(place) {
                    *slot = true;
                }
            }
        }
        buffers.values.clear();
        for &variable in &rule.values {
            let Ordinal(place) = ordinal(variable);
            if buffers.values.len() <= place {
                buffers.values.resize(place.saturating_add(1), false);
            }
            if let Some(slot) = buffers.values.get_mut(place) {
                *slot = true;
            }
        }
        let higher = &buffers.higher;
        let functional = |node: TheoryNode| matches!(node, TheoryNode::Variable(variable) if higher.get(ordinal(variable).0).copied().unwrap_or(false));
        let values = &buffers.values;
        // A value needs no cover: instantiating at it selects a branch of the
        // abstraction the left side holds and calls no operation.
        let value = |argument: Position| matches!(right.get(argument.0), Some(&TheoryNode::Variable(variable)) if values.get(ordinal(variable).0).copied().unwrap_or(false));
        buffers.table.clear();
        buffers
            .table
            .resize(left.len().saturating_mul(columns), Comparison::default());
        let precedes = |above: TheoryNode, below: TheoryNode| match (above, below) {
            (TheoryNode::Symbol(one), TheoryNode::Symbol(other)) => {
                match (self.symbols.get(one.0), self.symbols.get(other.0)) {
                    (
                        Some(&(SymbolKind::Operation(high), _)),
                        Some(&(SymbolKind::Operation(low), _)),
                    ) => high > low,
                    (
                        Some(&(SymbolKind::Operation(_), _)),
                        Some(&(
                            SymbolKind::Constructor
                            | SymbolKind::Abstraction
                            | SymbolKind::Occurrence,
                            _,
                        )),
                    ) => true,
                    _ => false,
                }
            },
            (TheoryNode::Symbol(_) | TheoryNode::Variable(_) | TheoryNode::Instance(..), _) => {
                false
            },
        };
        // An argument holds a variable it is, or one it instantiates under the
        // abstractions above it: each abstraction's body is the next node.
        let holds = |own: Position, variable: RuleVariable| {
            let mut at = own.0;
            while let Some(&TheoryNode::Symbol(symbol)) = left.get(at)
                && matches!(
                    self.symbols.get(symbol.0),
                    Some(&(SymbolKind::Abstraction, _))
                )
            {
                at = at.saturating_add(1);
            }
            matches!(
                left.get(at),
                Some(&(TheoryNode::Variable(held) | TheoryNode::Instance(held, _))) if held == variable
            )
        };
        for row in (0 .. left.len()).rev() {
            for column in (0 .. columns).rev() {
                let (Some(&node), Some(&other)) = (left.get(row), right.get(column))
                else {
                    continue;
                };
                let rows = self.arguments(left, Position(row), &buffers.left_ends);
                let cols = self.arguments(right, Position(column), &buffers.right_ends);
                let at = |table: &[Comparison], row: Position, column: Position| {
                    row.0
                        .checked_mul(columns)
                        .and_then(|start| start.checked_add(column.0))
                        .and_then(|index| table.get(index).copied())
                        .unwrap_or_default()
                };
                let table = &buffers.table;
                let same = node == other;
                let equal = same
                    && rows
                        .clone()
                        .zip(cols.clone())
                        .all(|(one, two)| at(table, one, two).equal);
                // `node` covers a right argument it is above, or one of its
                // own arguments is equal to or above: the comparison a
                // variable read at a function type takes.
                let covers = |argument: Position| {
                    at(table, Position(row), argument).greater
                        || rows.clone().any(|own| {
                            let pair = at(table, own, argument);
                            pair.equal || pair.greater
                        })
                };
                let greater = matches!(node, TheoryNode::Symbol(_))
                    && !functional(other)
                    && (rows.clone().any(|argument| {
                        let pair = at(table, argument, Position(column));
                        pair.equal || pair.greater
                    }) || match other {
                        TheoryNode::Variable(_) => false,
                        TheoryNode::Instance(variable, _) => {
                            rows.clone().any(|own| holds(own, variable))
                                && cols
                                    .clone()
                                    .all(|argument| value(argument) || covers(argument))
                        },
                        TheoryNode::Symbol(_) => {
                            cols.clone().all(covers)
                                && if same {
                                    rows.clone()
                                        .zip(cols.clone())
                                        .map(|(one, two)| at(table, one, two))
                                        .find(|pair| !pair.equal)
                                        .is_some_and(|pair| pair.greater)
                                }
                                else {
                                    precedes(node, other)
                                }
                        },
                    });
                if let Some(cell) = row
                    .checked_mul(columns)
                    .and_then(|start| start.checked_add(column))
                    .and_then(|index| buffers.table.get_mut(index))
                {
                    *cell = Comparison { equal, greater };
                }
            }
        }
        Verdict::from(buffers.table.first().is_some_and(|pair| pair.greater))
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
        if outer.instantiates
            || inner.instantiates
            || outer.conditioned
            || inner.conditioned
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
    ///   [`Self::decide`] has refused every overlap either takes part in, so no
    ///   critical pair needs one to join.
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
                    .filter(|rule| !rule.instantiates && !rule.conditioned)
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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

/// One entry of the path order's table: whether two subterms are equal, and
/// whether the first is above the second.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default)]
struct Comparison
{
    /// The two subterms are one term.
    equal: bool,
    /// The first is above the second.
    greater: bool,
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
    /// The comparison of every pair of positions, by row.
    table: Vec<Comparison>,
    /// Whether the right side instantiates each variable, by ordinal.
    higher: Vec<bool>,
    /// Whether each variable is one of the rule's values, by ordinal.
    values: Vec<bool>,
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
    /// abstractions between the two, so it too is one symbol whatever the
    /// atom's name.
    Occurrence(usize),
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
    /// The atoms the abstractions above the node being read abstract,
    /// outermost first.
    atoms: Vec<&'arena StringLiteral>,
    /// Each variable's atoms at its first occurrence, as a range of `above`.
    scopes: BTreeMap<&'arena StringLiteral, (usize, usize)>,
    /// The atoms of every variable's first occurrence, end to end.
    above: Vec<&'arena StringLiteral>,
    /// Whether some variable of the rule stands under other abstractions at
    /// one occurrence than at another.
    moved: bool,
    /// Whether some variable of the rule stands under other abstractions at
    /// one occurrence on the left side than at another there.
    split: bool,
    /// Whether the side being read is the left side.
    left: bool,
    /// The variables with an occurrence on the left side at a value port.
    valued: BTreeSet<RuleVariable>,
    /// The variables with an occurrence on the left side anywhere else.
    served: BTreeSet<RuleVariable>,
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
                    if stage == Stage::Written && !self.rules.is_empty() =>
                {
                    if self.naming == Naming::Named
                        && let Some(stated) = self.rules.last_mut()
                    {
                        stated.conditioned = true;
                    }
                    self.text(atom).and_then(|_| self.text(term)).map(|_| rest)
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
        if let Some(rule) = self.split {
            return Err(TheoryRuleRefusal {
                rule,
                fault: TheoryRuleFault::UndecidedCondition,
            });
        }
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
                    (Class::Occurrence(_), _) => SymbolKind::Occurrence,
                };
                (kind, arity)
            })
            .collect();
        Ok(TheoryRules {
            symbols,
            rules: self.rules,
            peaks: self.peaks,
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
                (tag::SORT | tag::REPRESENTABLE, &[_, _, rest])
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
    ///   occurrence than at its first, and itself recorded as the first split
    ///   rule unless one is when that occurrence is on `left`; [`None`] when
    ///   either term is not one the code writes.
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
        buffers.variables.clear();
        buffers.scopes.clear();
        buffers.above.clear();
        buffers.moved = false;
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
            rule.conditioned = buffers.moved;
            if buffers.split {
                let index = RuleIndex::from(self.rules.len());
                let _first = self.split.get_or_insert(index);
            }
        }
        self.rules.push(rule);
        Some(())
    }

    /// Read the term `root` in pre-order into `out`.
    ///
    /// # Specification
    /// - ensures: [`Some`] when every node reached is a `Var`, an `Occ` naming
    ///   an atom some enclosing `Abs` abstracts, or an `App`, `Con`, `Tuple`,
    ///   `Inst` or `Abs` whose arguments are an `Arg` chain ended by `End`; a
    ///   variable, instantiated or not, takes its place among
    ///   `buffers.variables`, appended when new, and the atoms of the `Abs`
    ///   above it, outermost first, are kept at its first occurrence and
    ///   compared at every other, `buffers.moved` set when they differ; an
    ///   `Occ` is the occurrence symbol of the number of `Abs` between it and
    ///   the innermost abstracting its atom; on the left side, a variable an
    ///   `App` takes at one of the value ports is kept in `buffers.valued`, and
    ///   one anywhere else, instantiated or not, in `buffers.served`.
    /// - panics: none.
    /// - executable: none — [`TheoryRules::read`] carries the predicate.
    /// - intension: a worklist of the nodes still to read, each with the number
    ///   of abstractions above it, so no step recurses; the atoms in scope are
    ///   one stack cut back to a node's number as it is read.
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
                    if buffers.left {
                        let _new = match stands {
                            Stands::AtValue => buffers.valued.insert(variable),
                            Stands::Elsewhere => buffers.served.insert(variable),
                        };
                    }
                    out.push(TheoryNode::Variable(variable));
                    continue;
                },
                (tag::OCC, &[name]) => {
                    let name = self.text(name)?;
                    let between = buffers.atoms.iter().rev().position(|&atom| atom == name)?;
                    let symbol =
                        self.intern((Class::Occurrence(between), None, FieldCount::default()));
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
                    buffers.atoms.push(self.text(name)?);
                    (
                        Applied::Symbol(Class::Abstraction, None),
                        chain,
                        depth.saturating_add(1),
                    )
                },
                (tag::INST, &[name, chain]) => {
                    let name = self.text(name)?;
                    let variable = variable(name, buffers)?;
                    scoped(name, buffers);
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

/// Keep the atoms in scope at `name`'s first occurrence, or compare them with
/// those at a later one, setting `buffers.moved` when they differ, and
/// `buffers.split` too when the later one is on the left side.
///
/// # Specification
/// trivial.
fn scoped<'arena>(
    name: &'arena StringLiteral,
    buffers: &mut ReadBuffers<'arena>,
)
{
    if let Some(&(start, end)) = buffers.scopes.get(name) {
        if buffers.above.get(start .. end) != Some(buffers.atoms.as_slice()) {
            buffers.moved = true;
            buffers.split |= buffers.left;
        }
        return;
    }
    let start = buffers.above.len();
    buffers.above.extend_from_slice(&buffers.atoms);
    let _new = buffers.scopes.insert(name, (start, buffers.above.len()));
}

#[cfg(test)]
mod tests;
